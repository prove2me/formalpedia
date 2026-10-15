-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4204
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:52:06.501039+00:00
-- url     : https://prove2.me/submissions/1784427e-fe7c-4fe9-9658-b167d355a9f5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 755935251 ≤ n < 756115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 755936501 1250 755935251 755935261
    0x9040308060d0819020601141c0804180204060e1e040c02240712090b0f040f1703011a030103020307050114040308030f01090f14010e06032d0105070206040b 69
    0x1440d4100588a9074200e80c910b2040000a03148901034589034460800001d14070f5050a002480c3c0001079101c42c5800b4a160504112619010922003144414900e428540070700d9240c601c8481c895580314840395500f054102c0904081c0e90002c0044580c6683c1340145000c4003400c00c48614400241c2d41c1c6001d0803c0c140000d1410103070440f110030042e900580d2000030440b02c041e002d0f1124507503c1a00a0070074401c110704103401100c13031440d55260040401100001c0d9658280003800541f902841541c0c2c10000f9040140d1015608074003a48956121120400302a1a840c03a400a0141138414200e101e0011940744401080c1e9040b260002d00a054203458a001542c00300300044d41c1640c185010080440815030300001103000780340c004244080d540c90682c2120444849280c840201410828a9450410903d81da01d054a006401100309625960300007460562624128505207611203841ca196a0492003901c07032242d001d030000e12442c5e84a4008a07165041100c00905880744ac3c40816 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 755937751 1250 755936501 755936507
    0x70b090606130e010612060507140408100b0621040506060105120408090d08120108160b0a0e040e0a0b0f06040c121814100f0608030d0e0a020612090d020606090403 72
    0x10740803e464600010b1103580351500412150104c1c1801e9440303079111003d000c4115405080000c1c40c1c1204540d640c00e090401c2103d079200c6400b820303858900c1d81c072a003484503581c0c0c80100b2942c240c0503200b0032030a4a440880c242c695401e003280c0590352030246200142080d4000c6003210f08008401213040302595540c0d40308103042e00580c07440c40e04040005840d41c0007a2200c0001c0400b96a4074001c1811580341441e901d1620b05441540400d000d180e210411104540c5d00075a00900014140521242c0d03c05010030018083c4201c031115a04c25145180e05000141c00118041c81c0c80207070020b00b039500c5c2c40601c0240c9052894200004001106500c408103407a40b010091012500141510b002d0584407800399031400c50200c002504241c00e00c149460300340c89504001851078000b8420f15180c4129270343c890254880481400d51248001700781c0c41403d0002061855008100c00d40310106603070403446814049405142510807003542e64205030000070348610650b0010300780c0070590b4856400b1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 755939001 1250 755937751 755937761
    0xa020f04090e010204090905070e06031b040b0d0827040b01170403030209031e0105250c020d0c2d052d0a1502010617060c0703050f030c070b09060613 66
    0x200b201d55800e1101058222141c050300d2401401400140001d60414203c420034180c041c0c0494440d9018085c6840d180714441c0040800031011503000560401176004101c0400104e84010040c01d0006418140780c405030402144000150700000301e42c0d00340809000c2258001145070303010404442c0c900041d0703d008000d640e40940300389400f604244956005ca46407500f013140452019003100c0841042030424810554010301e0881d0020700c0350928000c0e40107c20203014000100002c1c690036000390b4441c52446c0d50760070761000c4d14107881541c0b41e203542074210a40c02c0c80545030500e0200c0c800c07100c001d01303404000d56600030703c54058501d801000c14040006400c454400490990304e02c101c40d906c1c604020014140b0401030307001e80060501c000d00315940e640240c40f800303140ca5500c01e100b00740001d84981c4040050301859a500b0030381800d4581c0d00400c100381c2100744002040004440305900a4540385121790a812900d0701c0b49500e40d52144c004403039103908003120f00e078401a03a503000c0e004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 755940251 1250 755939001 755939021
    0x121a06030f0307050633060904180516060c0c0e0a0603120c060e12030606030a020c061905010603111603030e07031a07020703081801170a0509060a020f0409 69
    0x120381c030948000c20384034250342000e00150f509401401c01c20040b1381c040104900d10b2034a1030712020a0314104142d04804030a83c1e43e255000760000728000c103244e201c80d4891814030500c81c1c4c0c4031904c1401841d100b9a1580152002c025419040c000050f0450150314801000c942c001130b201840ca0809555010a8500410105189468140c00800320b21184c5032403000c0440c5503209007282030305082c60707000e6840d807441d203a002d0f5101e96401c2e150411442d050301e4100100701c40c2ca95490301c85000c0140a030003140e4488400340294010300440d440c0300c3e00c4440114060aa0502003680c3c0c808055088a40741070107041488010001038001e0054060700800c41d074402d050000e0f03400b0050091501c0c1c2140c0e50401c4400b00e280b21405001078102c856110b0b030000c0c05100802c91141076175180e8016000c1d4030310140003134000310a0702d0440c0c2e00071040400c0da007408160061061030002c2e0040c014040544095110340114008210303001071074000c4400412035120000d29061903c0c8516008160440d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 755941501 1250 755940251 755940253
    0xf0d031713060f0c09051507171308072408070813050d09210201050901050319021c050a0c0503011a04090606020f07060201090f0204050601030b091906121a0603 71
    0x20700082ca007481181c0d41e5107100e01e400601484d5401c03000e0411401d40d080940b05811070140c00e60751400140c101e800c4160702c0080884e040140850130380e032034020207000000c01c2050500120b5540400909402258885614400e03c5a01c5040e18203465080c020703070030002011400010201c50007103800a8220203040d1012021600546a040c1400e80c604207610000d60002d008100d040c490300b4404603405425003142c0c40964141d4000707002031060040e464140000440000c0c00400254401f40442c1280c45040d980d034030181e040103c00c01c040c200300a024624040100f640900c0c50b02c1440e0b030050035504d0701403030340e402d1010b60806c0c407034450139040c1c400200b0800404d20308114080c4a0003440c86800512024521203c6603060444075080b02046a1401e903681d404601c2591080c10000d8069800040d103880c2c44004070050110020200d030400c00100602500411203002802100742c540c004116040d04c58120003404c0c0000300c400350203084400b511140706005e0040c40b40c3c0182c0d00030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 755942751 1250 755941501 755941531
    0x60306140f030a14011a0306010b0306040507090b0f03040c12020901090e0f010e03070209011d07180302180414030a0518030f07030305070b100308120a0f1a0f0d0317 73
    0x251355070982041d00080161565120202c101c210075008090354a804004c0307000d04032070340c10b0001d44e0140b0300004000e03d1055413554040780e010b034000e001c0b28000d000b4070b01c405640c80d400070804040c0c030b070b009035000c568100c6400c400140340c0c0d1000380700048260740245400c1d01030b4a841007060141001a4031a05c86015200268469803070074070804158510f560040c0d80c841400e40100700001e80140d00c10a00c10050010038440705a60ba0802544524941001d000100d101e80700241502e4082c1c000a4006016000b0580c1c118100340d03d08d40300d507102e11188014140140344c2c0c2600d038050b030700048010078030a100c4065140d00e00701c030402400340b015040300d283d140750311042480c14081c3c0c2d0050740440c1e030000c0c081c420f100d03020b2107142e40310580ca00494059491643d40784010b00c64201081200d0305d843e000314241d41030760b4000303450700c04007070034284407214000d00c0c815942c08030018a144a84c0d9420400c680500340a80013400407601503d0346030005400e081d40d048207a000404505600c0019 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 755944001 1250 755942751 755942753
    0x20d03091509050109021005090a032a0602010e010f0e1b0f0d15061202060313150608250509010b030a0906020a0c110111030d0e0a0f050313060306140f030a 69
    0x603100e0040b44074003a070004a1081082c0c0140200c0f03180c40740c80c060800004200d01d15035500c407a040c8400301d83c1e01505c0210b0304030310003c0843c0380e6403001c140003c0c12171109400060581d41504010400316614000b0800e22080207054030803101040160301c43c540100d03000c0c1c04a10703065408141104030180c0585424a600c10014500c005181400c6500450f9a22901d601340298070951000c0c104030b04000301c0014407500001c04500000301404a144624684a410400c0d0308021840c1c4020049007805490303100c60110303440300174440d004554a5000c582043d02160a0b1300700c6800c892014044030040d900b007903a003000c164401856814059200c2110000081992006080f8203845980e450f004000710314000ca9498620064030703041103020001c0c20392003600803040701d0b00e03004c07481e0000415644130741c0110700700000301401a2802148100502c144540030008001d000840210041407646030a400c0e000c413081801008020b0080d0080c03840d0030304024101142c40d481c000c0c1154800d08003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 755945251 1250 755944001 755944043
    0x309120b040c0e100b0901120504150f060b0f3121110405100314060711190206130b1c0506010e0306043003020a1e020d0309 55
    0xa5011030310140c0500800c824001c1548030340d03000c1e140803400320115050140c1440395225150055691008000540b9943c507802440c04040100070f0798811f1100e407034507007400f00380220304c08070f882070060514610300000390040c401e020a40b190002030b2410032800c9004000942c0290001c0e03001030449000500c254039504002c030071544040014105900d040801c1d441c02c41a00c1100540c8203000d20400c08000307204040100042142542d0015165442c400c2c00350b0005481c3d80080c044e0b0181089032900d803030001c50801e200382c2c12911620b540c800c91f41100740c0da41058044c00e06158851103078481c01442d240d8020080c900489055440e6980c40708041d080d41e0780a17044040492000121141d0f042d0010b0050b1a03204100b42806542d06441002180d203c400040000b800800c8c0c0000700354640c0600090203040040d1b01e400c1c02110b40790000058025403001141d5804114440c544004110710200070408285035940905411840c0d0501900a0300d4078000c111411030114691440d40c1403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 755946501 1250 755945251 755945279
    0x1303020618070308191404080628060603050a060501092402010b040203130b0a0204120212031608070b090d09031b170d030b0d050a0308040302030c03041508090703050c0105070309 79
    0x841c0181040c02955038068003111b80b810001d403440d0410300080000d40d0000c07801d0b075401901070304558054626005241c0120340317103800045005d4034000300030a0399585a07010500c5141c0444082285e0b6454400554100c001403041125554044071007039940d0168100f4070988051600002c610b801e001300018003a600304603600010041410314580521040044c2103800410001d07003140f6260030321030040d0313508601100280c000c00c00610b48002c4054100b00b107800d40484140035032035034422031070554040e1780410010f039002c56056012504003800815041d82e65038503500c60300511865555510902618082007511411140c1c0e0006120303240481d0080b0790641210150100c080310400103411500c1164549000d107003159214800560002802c05010340c140c100210300c0d60321454220300e14411510003905500000c00c1c001901060001c80551101458480b092144c0c1e4000d0131540e207030749511014000e41e000c4107409980e540100001c0c081e543c02803518212454459030030101c07901e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 755947751 1250 755946501 755946517
    0x3090b01060c0203210313080705030d05060a140f09180a1401060e101e030c080c0906030606031b12060c180d03020d140c0a030f03051303020618070308 67
    0x5140042c48002c5103000d0001d0401503261100140748407943e850100214040180420701402034610350805001003e02503a044c0303580a4102c075034070030140000341c0c041c1c2010341c0c4080c06990407d9001c070310b0900c00c643c050380d00000034290581180340c007010042401c101600414101ea0b15080407092240c4c140040034803140a040516070411144403400d003164801c0d0b114410840d20305d02880b00341641100c4034001c8440b083d010350400c40c02c58054a01c40c14455000407e800e0314880001480e83d004152642009c2088642d110710359648405d02d1b0326003904882056158001080020702c61002180122a8040c090700782500309000301d00007840c04500707454026240e20046040380c20a00f01d0320b01d200381440b0a4600104401a80d076001c0e60349c0340380c0c14086084c081c0e03080c1d142450304505802d41c0c000302421411a481e03001d07107090140070400281262000a03041400081c3c0154a01d002d000040e94198001c1c690b80c2e49040740803071081c04810042c071060281890000100c0d4030034000c1c084030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 755949001 1250 755947751 755947757
    0x60b0d0b030c01030b010903151506020c0306160806100509030a08090a120c0623040605090102060a0e0a0f0503190809060f010608060d0c091505041811010f03090b0106 74
    0x9061000401d4904440d40300d00a0400d4100a4002080e13644011a101100c0c0d0100b03c80340c150b010465035001400e00d5404100402ca0600710001300160700150300da2600c08290b00382d0310f850b168030b82c006010502d5142003001040c0c240012070180c0c01c2503c401e483d00385581c5000e5042c040301d00700007030500c40c071b10348290781302075001c20207140901d04483d0003c028140c1d007016051040165481d044c01e00301c540728001c00d20029030080d4401541480110022171081d680c800c2d551912144068669008403144a006124003070004641184610602402e4544c1d0401001c0c2d16006035913103040c48182c0d00040301c190009000e10201007800d103110340034081c40b6407a004200e08d4213065003031400c00f006000300c6040000000400c002c80d0041c80c2c950300b001040c0c440d034801c189181044844203026a216082042c5400c110302840341d03071440d192042c0d80048a081c001800c1c01d1926141e142c0700d484019143c098070410390805d9600418581d00c45410301e00380814001c4080c0c85404180750240d000e4404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 755950251 1250 755949001 755949011
    0x160e0c031311091e1005010f050307020705090c0a030b0103051b0a02150126010506011205180f0705030d09051813051204060305071b080d0e160305120c0d03020904060b0d 75
    0x1004403a200e44c0c0c0c0d1000f4901320300b120552400000903c48418481018140031001001c564201e10030700044024100252860310b5908200d5407107003440d48203904240000b4079007041c5500961003401000c7c000d80c0c4c4111507005400040103114882d07848951400b05512900d100d04082c02141183c19000702809042200c451000481c0404251603210710713401079900d444100080c0b0303a00815075012580560000013003541d43e40b0701d110101182c1c500445402d00c00c10306c84000840000541509407981a001d850260600000a130b504503068020079074003143c0e64000714401e00502400552208880390542e0904c03d003921240d041051098a0040501c4002014003da81e018001d0355000f00790b034a0071580c9610540140c0011401c04000200381c4c1c00e00003180040500d42d070308841526042402034a00e5060968548020201c803403100b04c2d0240a298482801c41e00a0307420f50b135000b038500c40940100c81c906c0408034000d500a4841c1584550356040210700f80c00d144001d881098843e44000034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 755951501 1250 755950251 755950291
    0x307030315062304030f0f050c0307050901090203060307320604052409211207030207060806010c060f09020f150706090c17160e0c03131109 62
    0x1a544072045100d88072032291400c200956004010401010112030324100000d030303d4248202900c1580d202500d100404c0c400c00b400d2101210400045912690450b03442088242c10706171520310512400c1e030302940d104010445403409800556000310000c0a44002d2038481c02c0c850710440c4600c0c003643c0d2813210349082039103401c94030f060001440d408451060415182000244410b812030903c41d1000205118140c0c1e0070b4111000d652482d84010400c0d9403054041a02d0401541d02c0c0e0700030007503403045c0fa03110b400500300c000444014540540c00340c1640e80c10b056041d01c5100010702603504102041502201040301403281b0759001c00140c030f0108031082e80e401003254044001c03503201d203d400c07560000b16080c1d0150048030091948444089403042c11402c1c4141c2c3d0306d105030b220084e41555018600760499011806401840c1d9007074a4118a41d11809140c040010031a94510b49550400114007080b803030090303150700f052255100000e5401c10b500890203140c401d4856400072007039880542d03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 755952751 1250 755951501 755951507
    0x403090f080c0a051c02040219030b040e0c09191418070f12020d0b010608011a1305060f1b0c0a0b0705060a02070812010b0307080a090308060103020c03040f0305030703 74
    0x100105920341c02003407030b0070361540002c064004921030a44a880035061400d002150b00f000401281d800030011501d42d403804080b0100551824055030002c1c1c40d01040d0701051903c1c0c429110304100d99030091110400e220248400303464080d04401000c80015072010040800380210100e400b00d141c1940c269041c030141c3c01044030042c2c41c00c010281c001d8481030000d03a80c0400c20f2402c5070000548842030800e18004554240c85000000e0510360b000c0b4004912a5049200b642c100c0300303002112145085005585155130242142e51146c0903008107003040640743c1238029043c5529059042807409602c00703000c0315910300e0004c290100342c108101408452601c055004001c0640c071080701d01d88039055035003c1e103460f002803602c2a400d40c00b2a4100901c803600c002c0c1d0b80d4492409240ca4401d584400c1a542c0075042154280300003200b0700001907810540340140341c030040d85611001815240c200042d406074002b2222240c03076100a10000441034070000504004500400c081c607070710b1110741801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 755954001 1250 755952751 755952779
    0x1170a02041508040302121b0123060a1d060f090906010e060105070305041814070909051003050a0f080904091b0b030f01380c1b210114040309 63
    0x102c018004440108804250041503160034540400e9040d50b98500b09140c0320300388055400fa07110035610b0501c2c2061040540319202c041004826403054082d600e500070403803c807925003c0c1490412126410136503490400d40d2003604644018901029041c0c009d01164104000300c852900c29032001004202845803c10100c5e008034080ca800ca10f07041d42920003400b42c0c465032007103400660380b41500c07144c0c102d4650300031030306145d10200281d00d5081100005116058038011503406620b842c020968a1082c002400122030344000a8803a84500c0e80340c08181401159003920b40c031f40100100740b1940e56a101e4188058401c101c041840c0d1000d2004100e060300ca0b40000300c01050400034014600d8111841c0f40c119141e00d031103007c5c0c180c180c41c507180c2490030108080460f445041c0402650000c242c0252056103003410450f07060318104c0a15903a10901d20300e00c82d0f000700e8003a81c001242c948007241890306030301c2600041060440c04101c510313000c400312010707070010703d84800c01d1054000c406c482c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 755955251 1250 755954001 755954039
    0x9070504112d071e020d0b1518010303121b0306080f01140612030d0203012d0b04121b0303080f07080103051c1808010213051e0f01170a0204 62
    0x1081061461408942c40622403020701402c440c103207039043c031810301012403c1d100b11030340600401c0d152410b520382180e0072041038803903041c402d030042c100100c0e6013048842c0d03450002c0090110303229030340782d52030a45031403c601c8540a80c1945405004950910941000200d00b03038554000404a213410354540c10328002041c40c2c03078070740d06003603015505117941038815400031801c0718000b81d0310141109562941c41800500350301a8000b0000040000c03150116900b500c0462120701b1030000841002c43d550543c501904050400c284024404030a130513800c54a03e5200d488194144034600518a040c1e092541c0100c0c0040d50080c1040800144c80076080c0d0440e0301420b10740c0c3d007541155070362500c03180700603103840c540c1c000300c8124865184220401e244041c030701840000c120b0b488801181c040d52143e194035400b07202c1011f00151a04104080c0c02802c021842170044100c110001c019991441e400524100b00d203400c030401d0040064001d8030f0241180c18030060790b070303450502400e00740110568 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 755956501 1250 755955251 755955307
    0xb01090e04031b050a03080103110306070f0e0f0315040201200307060b01050409050708010806010b0a020705060702010302070b0f0105041b0e09040c120605010f050303040b0d050907050411 83
    0x404000c10030348020210740281d81070402c1c0c1c80030305000304603c542500d250300c0a4038520070310000c01c0c2450307040203803607041e6401030302c8982d068201c50084c507580d514143e03403c40c00940000314050140707120f50780e0100c000c00010402c0615100c040f000034580000a41a0011400c0e014140b100715078000b181a203500b08084c480400d0301d101000f0740790301d83c0138a140c042d0001d921401d4915a0b60701c6081214043d00d0f9107041000207081c072600c000c014020902038000e00f8810500003007145e03d030150a60b50b000c10705900a0000c0ba00341000d000c2c6135045044102d051503003d10044002804c00c00329688038405403602c20b0203135031600302040140c0700301150101001c090004110652540082c0d4440320001c1502c1920464440340f40c500f07214603942c1d00192480c07455014031003c104207a00814101c0741403412400380c854450080684034800c0b0f01c18503561020802903111003d5064011541c880f40101c2510b0325541e5510202c1c0940b000400c08000d81200003502201c2000c010380c0a04c40c1b40c00c088 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 755957751 1250 755956501 755956517
    0x61309150509010e10020307030914010f14150d0c0e070507031e05090f031e100b040506030d11070b1605100b06180607080f030403110c0612060102030c070602030d0b01 74
    0x150807522a02c01701008500250000005038229000390415020168068001c0100003e0885036a009040941e8406110360902010f1103401c0036108109000300c0c0d0312420308004482080030010040b405100c1100d00103d203e200007034401100700883e1050465880b440d58030784c041d14000300b082c1c0003182032544000198055a24442d807103000d5440282050394a902542005000246055034940c1d105004401c81e51004140032070106410004544160301032081d0030708141084243d0744121900c030b03003551180011030400b903c100300f02c0800c480c0c0b000640344410340380c1c913082c07449510001600c1c084610380351582c0c04020041100c0c1c020b20080b800100240c1c281c8100252a52188100301242c0c0c0e40c01011000352980da10b0129808141c5c00007a1702da4440030000c1c4605103400494059000c0b0701e903411150350014001c2403007000518001e0140d07190000004104000810140c41c4c24114403080c40b0f00c480c4000f04100031000f81c05141c009540798040300b14403005856048015071304102182c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 755959001 1250 755957751 755957771
    0x12030a020d030504140a06061d0108060708130f030806010f050c060109020a02030f040f031109011208071716061a0f06030417040f0806010611031206130915050901 72
    0x1007800501801640350100700c0307485074101207a60800301300c80c3ea4410b0060710703244810400e16500c5001290f0030080e14081c9101a0784001c14281030074440c29146801180015140c00c1c03141e4213540e44020b42091000b0048031a0303c4081d0300d660b0f0414120045205502400025a041440d014112120b0b10f41a840c1821340d02056131283c0042c840c1805090700816121102c600034000c0d5010b80120007815911241d8901c0d5030b00254645110546c0c0c900d03200e00510146003005074001c0d042e50076188010001c1040c650b201103d03503201c21010b44070b000c415804001d15265500050107103d002034000050703806603080810490300741d00c003065022074920912003002e488400ca00c0400c04801c60784251243c0d41c03410040403500c3d8070044400c03840000a00422910701d2920004152100402241d803240e0300c0d0b090a03503d403018002ca214941c1e005010a680d4818502c000c60f6000d50090000300350b403c0804d80c00000d807045220200c805403046040400c8000aa00ca51640078904a000340003050722 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 755960251 1250 755959001 755959003
    0xf140402180423031e0a050a12110a0315060f0e04091515060906020111040b0d1d0f19022202090a0306090b0f06090a1d0304060e12030a02 61
    0x31540d81c80510081c0064180698508190031a00c4603500040001c00d030042c0703141d00ca0303202e1048200403190254511216030706042c01d99840f0020b544031146011000c50094035807400031801001c01c0c0fa22032200c800342011101c0901110121030b1000b042156038090034101c110450381212003000740c0c2c0c075031a20034980e0186481505d0b2005440020320780201e410070114101e425600c42c0b902d1400e10707885e07603083d14110019030200c442559800c1e04407522508201c0c2a900c48882c461140301d1700744414404515000c0c0204489405483c0020b010300d0700b1507221a0b0003500e0981c10545400000100e0440501840040040000c03100000306116a550020314040048082d0b04c9001d00e00d2004003100204076411107a100d41e0003400c2c01010b582d01d01e480310242241e0141143c85c140d1050101e4240242400054080e5800614039151503030b91100d454010400c000c030100e2000d01c0e06180c001012402d20041001c1c141c55a6141c82c0502d0510510070300703160713440f82032609500c1049514600c44e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 755961501 1250 755960251 755960269
    0x3120e0a08041715040308090f0607120f0902030d0815010e0325080312040c092a050f161406040c031b0503010c0216050a0311042d0f140402 62
    0x600c1c1e143c802c142c40035210502d4a81404441401070740f081900920041c10b80240815102d10301c1a0120f800c0c90940f4400c090701c40f0020751300c8001054040d0000450b14081c1e400c0340310202c2c003001001030a44280e4001926040d9150480004102820240920362808010032500b0300d10a0a1806c2c0406458000c079030380d00203100c91110f108c007410140c00741241501d41140b0003002808200e035260070481e44181011744042c2d0301155504094000001c850401707000e01c1040140702c0740380c000f1001c000c03055245925044100442001410098861000d18103000743c0001d102d004850311140000e4a09001540003011415a940c0d000808120000b002d080507501501c0d448413049040303607448002c0712081e8a690b00040d6265080c040311200c0a5400208401c52a0013a1441c0340a207a44106001141c0e42c2404050b12801008801803900d040903004803442d01d040901d454004000b10240b0031103001c65100300e526140d2104840ca401d10b0311805641c250184029920440741025800903001c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 755962751 1250 755961501 755961509
    0xc0e150d1a060f1c111b030c0a0c03060b150d020903151e0115120b1c0f0b010e15091503030301060c021518220903120e0a0804 56
    0x152501c070114154484003078108061000a454a52100001840d11080750007103050043c10208031003050044180b9405604203104490343c0113844c01c1c81641c0a6031070106a000d500041b0b1204110849008004000c1303254040e000e031181400c02821403400b20151503c0015480c407440b14035070900c0c080038008003101c01180511000607514061385000c03a0030a40f00168113000040c0850070041c20202507460710030f40c2c80e070b9014190300c1c82e0381300c1400c025004100b45100001400c45002250001c51907031060300c240d48010301162008528110140c0400d40604084406580112a845c00c111041e0140c3e4003401c0c601800004030f140400d040d0002d4040111120303c40c070081d1010035424000010b41101204002d02507030303642e60311201c0140404600700c1c401c0b401051250f048254070f902c40015245a4410103500040d0341582a04000070303c000207040024040e00f0100f503200f6031030710384a0b2444d000c0c0b094a4210010ba220349015040300d007011048802508203020031000947e100e8200c1e001c2d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 755964001 1250 755962751 755962777
    0x180601060c030306050618030c180a02070c050a0611071710052d07020c01030e030d0c05040810050a05150a09110c010515030c0102030a09050603280c0e15 68
    0x51082420110007134401540401e070003d40c001000744807d0000f40d010040944103900b03c809203150b80b0b0038000c8090b414400c0c1e4241c8103031000842d40d1b200c000d2300100000c2c2d0041d01035854154540c800500b082229501007800304902c0281a450140d05004200080500844034600040c40600d0591105510310b11540c0c0295100002400303440001340da100c10b90300050b004042001c01420840c1c05080c1078a40300e025100d040f0181020790720a0241103d0554100050740c1407260300103105010307048180d843d20a220040c0400300e106101080f80104c00081c40790007280750f041c921820000c854000d0031140000e2581c1030b0000d21350f110380c1d001d0000c68401d040d0008550801c0c8052039440e0145120314040e039401c00701840352000214070004402541241a60001c09101005a903244a041e04182c003140e80d00c035040080b1320b481d00146511800d0140610081d501180c010940080c070300300c1d04104130369900c1c400440c241e804405c00d104c80c1d00c113075003880100302034003040a510702a0403000340314 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 755965251 1250 755964001 755964017
    0x3050a06021b0105090c03100b010c0f140f060708060607020d0b07090b0708030108071d0a020a020a020a0303272702040306020f04140a0b0301120309080f0708010518060106 76
    0x340b0385030300c054940c8410192000700102c1c10803600b8036448403580c0960034820303c51003601c030000380380c640f0804080304016100d0800030300c240d030f9406400011040c400e4601c0c0e81ca00a5108804100380100c2c640412503002803c1c00740f0740000041c00c0b0040140031180603110500201005032118403040400039041108020182e0750224100c0f20030145400c000c69030400425420208400500070714160380c03408054a41031900c58119030700e070801c60201014500c4c01000402c010307481950003045985034610607191a50365540101d00c80984552086000030201014688003680d59640c8450b103412050008800d1498610400d586601c190355441020b80703034034001c0c1102c0c404e80c0d0450f40110703408801075495011745165410550040d20a40d5104845020302c01e896103483c484180c103031181880c03224152390070300c003034103a00300a003940480c2485071701e8401050814041003220000103009004103c8a8142010242598401390035103101c403901191040f90005c0102d04241520124a05011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 755966501 1250 755965251 755965267
    0x60e0904061b090611010515221103040308060108090c010f0c0b04082d160f20040f0b030d0503060310020325021504060b0f030f01050405060f0103050a0602 69
    0x10041c203581e12041004400c51061040c0640c21141000072640c0580b030300e02034108085d00442c240d9500f2500e841e0500d0404059000501d41441d12a0f40040202c001c0320032490b01c190110121043c3e0301d0304080c031410220412007096848915039a0219080c42c2c0340445050101005541d120b2030482c05061185100c12004c3c61485101285145030704903042d040d0a0820341401d1003190300140390108038a0843c4600b594038601e0941400f20403484c0c4810790b280440301c00d86d0366245818800201c604007055142c440100b48402c3c11071140440300000d51409454039400c100807111105c010b0b601460504405d0540c0382d50109400141384500c0c1445070740c99903110006424903401c10520b4140c248080207002c50308a24000e50003e000441111b01d8031002d000e101070f660349504041542601e00c50b2800a800074029400c18644900054040c1e031059a100f400241401c44440c14000c00b83e40d1030080006011041141c550400041414080c1c1941142c58803a2500d40036031018186580000d5014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 755967751 1250 755966501 755966513
    0x90c1c1a0402030c040e0c03090a1101030902060d06061805060d05090307020907020a03020c0103111c02190c0c0e101a041a070501051f0612270615060e0904 69
    0x5411100001c00443d62854610103040c1903070000e005030468100502c00040d02000d070301080b00d002e0019500103051842040e601c2c911803040100280d410980c4606000d0016180c400c00791660a080310400318000d8241140100034035548640c09040550a1400b044552614002c1310030071038078220040784a81d00c07000d010b40b45210702000250041004401c002c0000d034045101c14103103100b5429207540104001c0110f040d545409d0200c003c034482048030980f0214a2a40004500c0c0c82e440094142104032640a01c071304952071400010072140c003102c1b000c1010780c41118025061140c4601002d0800e00388107003619580c1d00640c400440885ca00a02d04048642607900a054804541e5070082030401d81c0d4486802440003187c0c6582480046082448004255272000c2450124030201501d0008210380d2000000f080030b56859413080c0140e804480342d000584022104044200d402d90f80d450240121100c00c40794814114444030244286a80b109060950060403108400203803240c0c1005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 755969001 1250 755967751 755967791
    0xb09010c0f17030a0c170609060a1a0d0608030403050303010e041707060c02060601020a03080619090f1d0d02061305030c06180f06040b0604090c080f0c090c1c 70
    0x380c20002010085029220311500030740c402e0344441000d006a94050b4011755001b0003102d4500c44030481a07000901030b0602d812200e500600042c5000c0d69680d5030000d1000a65403082c450404550000d64000c218106014900082c511440154603107440d503240e040c3c0701d02040c0220407110a01c0170102d030621081902c8610840d142e2200a5610000c40c03620800a00407005014094040e00d00042c00d29070011030314045058050301e69131850f50301c003400c01c401d0003070030b910b400d41001480d80c001c035080660307100e00b0001d803442c8403000410f881c1c1d4040301c0503509401d0b000480654080e01c1080c00305680420b103035410034a02103111020882d40d190040c214081c42402d0443c510a520801c140c0104007083c011780259207a054905d071030380f590081038075002c00b12405042c1c090f051010444c1414583c0c01062401e008084468015031a130380074500340105040800c0c3e05612484d48800f0502d031a901890f000008400c44a1405505507107007a2070417014041060481d0346c92030000d00c049a42164 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 755970251 1250 755969001 755969003
    0xa02030c070906092d0209010201020d06030f050c0d0c060f030f0e0106051201020406051e04051e0910060c0f020319060e01060609050d080310030b0f1608010b09010c0f 74
    0x1035450040d12200b01500400c503600c260f40c1d401e801d01c1e5610a20940c0e0b07200c000f09201d9120509014209210820700c0a5030040014604565007042202402991071280c00e014512a407604e031031401603070400626001e122194203220341d03184c220303071400160100303071080480d83c0c1811301491a043c4154141c0c0100006440005858100301415480300b4041d0311607001d840c012a48142204094410700713080340103501802010400c20021040c1c400d18080400002108500780c03185426107a4011412a015500c0b400205c114005a090440d15080c407c00b03900000d8070740c464030114609403004200040460b400f07050020401201c80c25520240b2200404140f00010300158221529003c4018500480d054a00354030340f0784085003140c4650706500854500611605100f040d90300c41e203c0a6002420f510305503462000004001000044624840c48080c0092065854081051095290380c0c0c034004d002c01180000503c8008000000d46e0712509083c60041d008000f41d1030440024117034004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755971501 1250 755970251 755970253
    0xf2d010305010209090106020309030706050904150b070303110a090e04022404051e10050c010e060406020a021c200f06040c061407020d0b13020d03050915090303040b0a02030c 77
    0x200c14410150000d02030080300340d4000205a03030303810041703890b401a8081c00368550040c1c242040708a00c19005000003000040c0002210a450711003400f003050681e02c901400e2001052050a0540503c5410f0301c010395080d400d854440d281c100101500442c0c00340948039140c0101003029074540d07455881d400d100c4040341c516805042c42d118030041d0801e00c1064424011b0350014400071002c2098200c03807440c041d040f84c0c10a43c1c2100140e07034035000042e07540a55035803a1221000c1c504100710641c021030090000507940c40c2c02031402170500752643c14250004050042151640f6071001070944402c100e000c084030703c2960544000c0c00c0011605980354184100c0040c40280140382c207071501128686d03166070f51000c104001c545842e010b040b10180d4040c100c8002a80407482c500015a800800e41240220601d036990001d0709500c601081540040d1006ca403034892030502ca00d10001e400b0904460904223034004000a41d281300d58010f00d080c180020480403001402002600c00b4840414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 755972751 1250 755971501 755971591
    0xb130c062a031d011110022d0d050a02090904150b04060b1306020706080112030c02060a080a0510180903030b061b0c01050319090314040314070605030f 67
    0x305004000720b4143c804075840100d0b01c1001a01c030760040740c03c40c940503540740262241c14107200701c01c0006e41140d91040f581200038109082c0070740c850580a82c402d02c04056264441440035800c82c12650014013408107144108003028103640d56180940d4080e521100c1c00218102c4480c0a4001d008240c7c8a55040f40c01c001e0082503424090000e0900b446001c1e00c0100303015520b05040741d0b05e0600380306a1011174507500040c003480300007a0300c050300180a0300385075a0342c3c4034039404512664400e01c3e69000080851040c014030100c40d0180c1500520440107030340030b090030701902c1310300c210b044075078070b10415551420641014025000b40a2045c0c00402403a00c0320385460b0380c82c4c8120510000b694050080306100c6e042c0c0e6010b2025a80a5101201c41c0b060510007461040d0040083c01c000358140400c800180c01d45912aa0081010703500c82c0511980003000f0b080024a00340302a0000c50601c0f10074002c020b00078440e402d000343c0c4604004110040100b40c903c000421400420510907009070b10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 755974001 1250 755972751 755972753
    0x303110a120507030204060f12110319060b1305090603010e0106030b09061e0a1517030705060618040b13050109030504031a103006090b130c062a 64
    0x1088441d07440c1c1200c514248a5540e07500c3c021422403081c1e0092101040342840c04103503003172288150400d00c903011240064a41c18000220a030398108945004005400c000001c48110040c05524010520200c0d000d0038500720310401000900d60340141400355101000040070340d0b074250415a00022458000c01c0b040343c41c0d00303065001d80412105416140308140c08180b4900c0d2000701d102d08002c21348402429a01c489000d080940300d40d01041d00580300c40c00340481d0f01c904640030b81002e51210002169100b94a00d007040c1844002400548103640300d10340c1e10011a070010100e9803080d440f80d0b0014039955081c00c0d038184041e070440c0c007401640c6040110300030103810500800990340541e40c08014030100c03900f0318210540840381850f100305c2041b41042820600280c40042c01d030103a0780d00c00000c15804403034805801d0030906890040c0c0b66441f50044c011b0480c18190425039030018442d0941c0c0ba03844146001506204180c1003045508030344106545c4442c40c90700ca00d142c21100f00c03480080d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 755975251 1250 755974001 755974007
    0x2030d05070f0810061209060f0501080d180b03010b161e0b060603040f0303180503031003110303070809010f051c060513140103110a0f0e091b0108040f0303110a 71
    0x2c2101d49004103850300040303810141e01d0f103160380807194580d603911001d0120710100800713450100317812074070a40c0754422154000210f010301c0b0b018140070070061442d040401c0c0014040045542203250390300100f1001c1c0700c1c040c0031004407410742d50b007440c1f0140c0e2a00c083c550304030420340c0c070381000d000304003081341002400c0800c030350103148180524064100d540707408081241c0707480f080c2c500801441840000c040041d0080d000044d03c003150340e02a5060400c140c0300c280c1140e10495140b510001c00742e10600c1089122511440c0f82032054000b0360801c2103a43d20403a02d481941c988606204500800d00b144522034421030b0029814400c9106040e503410403c0c0026104078002c0e9031040841b424145980d2845100f01e040d43c00c1029108041c0e6480d54890300720040b101c81003583c1000840e1008103d4664851103900140540f003940c0e00b031071400e10710503810032040350421084a0400d06082041c0daa010420b6504540c00a070003825151941c5002e034020440031488043c10400412000d000c40c1d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 755976501 1250 755975251 755975267
    0x161706031f0e0709060513240603050619060203070803040809040207140c100c060b0f030a1505011a270a090209130b151e0310051207060504051002030d0507 69
    0x204540440307440546131072890040e691a07004454104d80200300350031505e05c9075000f20300c02c0490116102c0d801c0c81c1010503400045c1c1307180c0064000c43c0c5c8a6003071010a041403a0801c0c5d0207401003946014440c01c044000f0b403684030311000034081071404404a02805500d1048400c50440108115912606e030303d0881071462188604010710300441e0340d03001c03660031b189888243d1910a80c3d11384500294582c0d0301c000420503840300c00e41090903501a2107041d2000c0006901c458040ca840c03c0d03500e5880d1003d40140d803016040480140f03284843c98040303880200982c3c961100c41071201560b40a65200740c0c0318440446041075114590b10710004082101c1d44c01405050800e9807010381c18440200018203845110010a40001000b0710808641c411100500503d2003030a844456528010055003c9a001075030380d45920802c0b8074041000740b40c60340d840030b0341d41e441d000503082031403410b03030003501c4c60040c0e21559000703c407040323812b22000b8401e10441d4007000304200c0801c02d908008100800390301c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 755977751 1250 755976501 755976521
    0x70504172a0907020c0f04150e01030c15050a020a020904021801290717031b030906070e040b100e03070b070c090b0a03080406030209120105180105161706031f 70
    0x2000700d01183d03000b403020650b0741c4c0080380500160840c41c003002c00d000050402101e500703900c3c0020305010852100d12140640214011035108c0c10a60428556861400080b011501840410440500c0d015000714822400b00c1d0100c0f0600d520b40d0300c0d030000c40ea0180c59a000010707281c1d0204004900c06400c20a01002c81401b202d1650601298075070f461414030640034060003544030021269400b4500c03400039a80540d41c0c10392400306010300e9620303c9540d0805e54400c041e6420030010000d450303600661068500404813030610032003840300041560106e1105505040102c41c4032005101d403400c0102030020301a44095030741c0c441c62424005484a0b0701d000f641581410b120508020707103042c6001e4015640c025401924240c900041600250301c12070413603400c00740205007a005c40030203201c0c842c482d0242c586034984c08400b0860342c03130840b00010964000d001889030701c0341d00300e5803042411040e030001c43c4240c50325884e075100207403400349030309005456054021843e0b03400701070b41e4014002e14 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 755979001 1250 755977751 755977759
    0x10e060709140906041d0a03020307060f110304020f030c18010f06020a05031b0a12080a1113030b091e0f0c0a0e0601080a0b040509011d06070504172a 66
    0x50398503000c840701c1900d00100306580c003c12807400714201e0315095100e940504d69000c0c0440b000541220118101180664258050b0304041003080074040a80540300f911480d0f0001044011148040300c0c0c1c8a000180029000b2441250140c020740c4080101c9501010700070543c3d16900400451001500c03001d004000d0380d43c0540c100080c03441d000040c03000005a02c01c02842c01c04102c405040100082d00710010000e11a031180040802c000b4445c1c9007550f110b0303950f4003580d8030300100c0c06000d990700c5000c4030020400411031044a0700b518042041074907030007403d221058075100d95040c0362107a904500c921b01490145004a44000018003440b48840741041d218100d0035982001084102845108614110007001a02a6100301403455000d04201c00c002499441c203408034003101d10440f01016540e41d1003011202144404010705007200486000301410f2401c044001c001e400f491046d0b85480002254020f6100400e201c140900d00c14440404031043c142021110900b43c034007030781400707 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 755980251 1250 755979001 755979017
    0x507111302090f040b0d1412072d020a06030f020417070e150a030201030b0112110c01060909120c24021c020a02072115020903070b03100504020d020408010e0607 71
    0xc1401c01d40900900d9100050a01c590f2a0740d6486410500304092040241b0307000e1428031206c03c091107800750102c0d9004140b940c0c0400031520900e2403000c0415440310440c000ae1011900503550313241c1c07420a44503603140c041104035003806448083e0255070401c842035034a64040a207240c03400142d4038125016065026101d0302c03900011200e208001c03107625004011a8018030141d4001e40080c0300c0700e107062600680740155880380070110f030741c1c1d040340140a400014504a407a2402d000b604003600c0b07209800c000c020441d13507400e8040c22287c40541c0500401500440511031178140550344a41610b107429038024401c1c5da1080254840c0d544440d489900c143c24842d4121144240d82c01203007036800808205040c000c0da40980c00021600400e000e031aa0740102c0040d4480c0340051070b01e04581005602c03005044101418000e15820000f101d58091040062031001c0401d480210741c010340b0016612001a02c123000640309075040480035600f054408040181c000030081d1140c1c01039a107580d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 755981501 1250 755980251 755980279
    0xe0a030e09010605040b091c050601090e032703011e02030105010f030605102a060b0901050121241202010305010e0709142124100303050711130209 65
    0x11541c0c00a02549001807810301081c0000c00010004141240000b001d06c0704054012483c42d041c503500007030032035050308a20010010003015000741c11110785540c01a42c00e01e211030700c00044c2502994003150703809007664841107007628203501c42440b404081c0240807607018420904d5020758000e22885001401d030424440c280c070b01c24490075040d02d40c010012a0800404c1c00202e03801366206600540c0704a180b0300928440748061051460180b003110003094840300300040001c041416031102e410311140d01d03090280c03076039001c4509134025041040010941c8000302c0b58614409840047d0240c256103a2020070110550704007404528402d903018000c40e84c03540b0441d900584247c441c01c000c10304484051000c403444841c0e41c1135462024108000061040a405c04201c20072483c41e51150002070012803180407103500c1d01c5002d107101c400341009003008060407110a20500c00a020004045015004c10800c2011403030b030b0f43c600130a000401c4130b944400100941c03049092b14480c0c1310720801c2d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 755982751 1250 755981501 755981509
    0x2100204031a150a14040630030203210a05070e060f0915041518060e0d06021201060f030b030105010f030f051203040305030a0b040e120a0306090e0a030e 68
    0x80940303a100703124a0b41c26500303418030541014054125030b88a004810312026a0702c983c080d100041c11001c02051001e600c080903c411141c00c0d400800c0c6420980040888a408401311603007050020318a4500740003460404030300b113006d0a02100d0b03400d071090031601540d928110605020303641c03207082003015403034564054a10324020806290000310131301122180400010140240040140c1403400000b865410860941c3c0030b50481c2000c01c2c104410030b002d15078000285500e22100f103a180071401d040030809080490b14010f060321500d082ca2501e000c00405405540c050302b41a509040f0740d503100d00c405880d000c101d1121200091030030f042c1300c03400e14050140c1e90480e2000c201d040c1401d800d54450650030191a60180d07007034465242080d6007800c03044021403046001c1e5495640b6810101030190a44030483c01141c0304a0074910300500c111000329140e03000c0d41e0030480c20755440c02c0c18101640a002c0c81d40c04801031515150309406030010110380c103565280300340c1c0c6911864200c04100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 755984001 1250 755982751 755982757
    0x30c071403030c0a080906091203070611030c030a0902040b090f0103050d03061404020d09051501061e0f0f18030b06030106090501151101020f0a050910020105071d2b03021002 77
    0x100044d0348854004404a08504010604100090b003654030342600340000c1090846100ea4401459200280c0c0354140440e52081c2c60480c005034510030b181d403c054055041c1c9010162284040b55900e610701e00440d03503960311440100c07002400da900c26181600300f0040109091006888034042c55070b141c248540309200700c0098a1a411441d203003080c121042c00003e4004030075140449550b00000d4001c00e85c00c110040480c0880c0000340710f01d6042101c018401c00d40c1d07940e543d2603480800c890620098001c00c41c604000a01d190030340302c28400c5403086407121780350030400700e13101644100801030001d01c205081c804c0380290024064580c0d5441b10800715002485004a4078161100c2d60b50f0340c0340720700403004007010b05200140c10500b00050140091340012103117000320b00005841e0136036040c50213a14a400784680002c200c9c501d080c2a024100d40c440d8481d100742d1b0a0344401c0b910b601c0d41e994507150080004d010100c503000d000c0007164188a030744218240c0161081d84078043e0108410300803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 755985251 1250 755984001 755984017
    0x409111914040e1302042a091d0a1b0f0219020a03020114070516170d0203090607050106080a0b060307170a0204020f0c060a0614030a0f0f14030c07140303 68
    0x820792401d8070f0308000701c4151002601076403003c89109080e00140e07842e40924043c4e01210201c3e462102150f40700124858611003041041c40383c40e010170040c4000841d074041c4501124004a550741d507842ca0140d00401807a03079004100780e00443c0c18100c0940c000741c13880042d00705d50200c86200c00c441c4080b24200441d80300c000d43c0b2184095040c030041d40300da1040b120a00c0080c01007824006ca40c0d44180c00c100d02d44101119680c0c1444040144821021100c1505901280a028000720f035400003500c9124801009014180c0028401d0800009501140061005600781c2d10300c00220301c1d210300c3c071241c2a03907031300c1c0f20f446200400300d61404200704500d1401c0c3e030a8001c00011800380c0c2400b019400041900c0000c0d03005000b01c15001d1420f2060600c01c4075211400520301d414a14119211222165140c0c005c1d07010342001000500d11380c0c440c030003c0d80c100c046001003155a16000c03011401805608140340000316425005103000101d440a640d512442210581201c1080c55528041c07168 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 755986501 1250 755985251 755985287
    0x305160809033145050709050a330e0d0c050d050f010c090b07170c1009061404080702040b01090f121b051e0604091119 53
    0x8004401c0d83d0321051541016000742d940f02002c2850311000020040b9140d01a030300258081140b002910210a820140e81002c100341200c220010040d03507401c2d420035001c242c03050b5510404904002d015204140003400001c01c00d240b1103444040d03210500c000c03038a0210081c3c0c0009803c2d50f11001d000b06511020071181c4c0c401030000085070400403c1100c01c40c05031240d5100c45804a000d40f183c00e00c0b43c010a00a9004040c00a141911182141e2041c400c0c1810403401c03420522001251004881e030742c0e5006400303050301003010300d03640c8158400d030400b61030f440c800d8410323030b04101e40560800040b41e40182c1d810824151085203004010a080720000e111000070052030005203800e030721180080c1410314003100e000c2e40341d101d034044d10717945908441442c0500e00104401c108012000c1c8104400311001c1440061038980814125041002500e041e000d0785907400c034841d1610402d4070001c2c2101c107000c0c460059034040d140c3e0f8a0b0b000c070391132105035040344180350a03c0d8003a0404031364190030a1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 755987751 1250 755986501 755986507
    0x62a010c0c0f0606090f090209090d0f0804051005010e07030c020318190320031b010918020c100204031a010302060d1e1508071202010807110309030d030516080903 72
    0x90b4518a00140700c000440d0038555520020603d860300d071040e80fa03201900000084c0c2480d150041205040c0000d066044a91110840326500383e80b0104440d0950001e04060099072541d190031403c10100c0c40c2280740d001d00d0200005103903070046181c10f001340c1c403a4034100524406204226180d216a00a583c1104c903000c030800010f083c00341d92081c080c11203104001e40144c80360303620f07078003018600004110b09145054140b8a0f00d070600c2002aa42d22900306040400d43c400c002800215041c41b0700d45520500010f1812005d440790121107410b10b50400381d80e41c9802c00c0305540c0003504240410f441a072091003e0321481403080001070b041c1da4006000c036040103101700c03840d0080d100e401c01803021145000801c45032445c46009600c850003044600c84402c034102450316142203401d5010552941032800c5600160340c00c0304805800c042c41c0c0c504501d6002c1072950045c9144101041d5903014400c12020803112a4143c0c4028000d81448500102c0020b00420443e00c000c401e4032a1000340c0c00030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 755989001 1250 755987751 755987753
    0xf040509090a0609060f06090e0730030207170118140703021e091e0f040303110307080f060f0a0e090c0d0b090c0616030c050c062a010c0c 61
    0x101015680800601c0840340c001129036035520684480300402c440b410b8032580c010610344218000c62001d40fa0600c0c0810580c5440c4040c1607075005180300d596500101c1c1c0c004640b0398803c0d0559004580d6140900c0302d10403e143c81d000b5a101098450703040c1400c43c00200402186041c090086049400f02c0705c018a030702952920441104a01254206072040020010041c0c82d90800e541c0f1202036545840055404c80f003c0c0441000c0c014520f080390301500241520300c01c1e00c01c14007034007c8110340803842d0720360340c2e0f203019170061119413081b108022000c000c2002c02a03004a4851003000e0308090040d040e1640302c14009203640a00b2047d0b44000d0a05090003401080070326507900072541c8080f0391800c0901000301d901c20181510072b6a00b555860100000100c042010400340c610a9801c6480c2c00e010205085500008540080030880c0203c0d600d42130040c02c00c400402d00200800131540d40c1a501910014001c21302d01003001002c0034120840d28800610409540c90544d4441c00450f54071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 755990251 1250 755989001 755989009
    0x90a08060109290f1f05250203030a1119060c03060e1005150d05070c0507051e090a090501020a201504080309010908130603182001050d02130315020f0405 68
    0x20081035940c02025110a99040c030304843e03002000c0c07142a40f6819034850445001801d8041c0c0521003112051f403c003080001078030f000003100d50000c03192900841c182203c0e0043d40c10010b0344202440d4045900034230760103100050703004c2110021075480400401ea07480c070b072224010008881090076050419410002400d2081d60000308500c0700c1e90302c5180511020304101290010394618000403452061035007000400c00c00003010344400c403020350800165402e1022600d10040815010b9182840440c00981041d040319010550040096480b160421002800f000c50342042000c00341c20b000d1404003821010a028201c500700b28554112566191030b2900264805070009805660f505503910108161001034031088440c04442024946000001002d03181c100e001d0300850280394900d000010114042c02c0c0c54000044a40444035005800603510350081c0400310800c0340c000a4502208880c90240c2015284564031916041c9281040d600890107902401100c51408120600040c68 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 755991501 1250 755990251 755990269
    0x2b14060f040b1207081f060e01060c060b0d060b1503011212020f0709140705031501030e010b1207080616020a0b25030527060f0705090a0806010929 65
    0xb801504002d280d080710303075105290407080ea0214840741c021071341d0403809050a00220000441c540c030280440b60a085140283d200188600340a102c000d050719020000260030000710300300d0007040301c3d00205540c1045006000c500214500c244030050301006005003000c01d403416a82d00002210003a800c07980c81061b4403800340158025846901c0c0c925400030b00401c01280909031540020a0312400410000c150708005044a02840018410803025890300c10254001d03900c24600414007403000c6a195005010103440140c04c0914880c4107001c2100008403041210405801c0b5171160340c0341640900750b18107600191005070011604880403c1d0078401143d0400300d119610762002a1010844509440c8100b1100110b0345420800420148030078010030f0065845d05920458a074425030a038460f08000c2000500c00525000304801070701c6901550300c0218050039040d101912082c4942c0c5d1030009106034225a81030000642d087c10100c4403c006031001e1041035100c900d0623404000342c1035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 755992751 1250 755991501 755991521
    0xa060b0a18180c08030a030b0d0201120f02040909210306030c0b090612070c0201020c090601020d0302030907050a0e01030c0b16080a030b06160213020711010f052b14060f04 76
    0x40c0e000c0041030081550303c18800010480b44006540d0385c5181c00000d829500013440715480b401400c0d40040150b40c002c0d620f0380c40741403000b400003000ca914034640c01c024003440c1c0100c2c007003600e40b24405080004030b540080d1901588450114043c9200000304c1c181d88040c0401081d07807030421400c00440c40100080c00d503284000b0f113118141011680c801300b04000032600c1c0400038902c03804440035541c051218401c020810780e010142481d01c040041d40d02d4480340c181c90b0806a00000142a90b0030500090340038041c01440c01903419a202d41410400d0428001500d100040d0000040c0c1c0100304000c86a040701e220403028092921522402c43c1e9800c803460000a00d903ca04a5600940e42d080041c862040e18105006c00007545005002605082c42da800301090702c10428000441d10007411801a03400918000203290680242101c0030300481c5a003800984028031050300162054010140050003c0030070000c1c0ca0500c000820000402d5666580040354900d1044943c200f03900030801d91 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 755994001 1250 755992751 755992781
    0x206070305121003020f040c0806061b0a05030c06010923130606170f030f0d0915050703020d230703020a0314010f090c020303010806220803090a060b0a18 68
    0x21070724000c01082c5042100d0300c5110043c000c40510031450020130b08400e031402520304020070034034803001800780c0c032002d07041600c611404500f8070600c0644c003a410320b4054195040e105a41468504282d80f03070085641000705008410004ca04000c1c50300c40d01004080c0d03002003d032200c080c9003e11004d40c002a084c505803480a010600c08a451030007008014030f6080c44001e607040c00c120042c3e041c1000e1103280031803504100100c0195219541c10b0301c0002d203084000141c424020714240103902d04c2c0702900c2c0e45040c10b050410981c0d9400d40e020702220701440c0380c2440162500911401a2070b42540e000d01d200c850740e000306a15030710036406400411407a08001512420303035441d260b07213050264049070b2040c480c0d54081c001190320380a103451031441c5000550031941000c200e00c0e2903590041004400c1c03114441501e40b5035185800e000c4400390050184c07a80c5e42040c510305611818a800c059940d941001208401402c00300750003411540318800424000c824080c20001410b4450030206c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 755995251 1250 755994001 755994007
    0x20c030a080d02130819290a020a030209180402091005011709010609090c08070f0e28090f030f08010b09010507111f0908120f0901170c09031e0a0206070305 69
    0x68501004014403003e43c400c1d940052601c0d51821078040d40000c010b1f40c4404c6000d0204411821041b0181d41c0c2200c9000e1004d6111303d50030808038020f0040724080c541c001d81c0d504031090348820340c40d00309014600030394000c0f100b592144a554480003241c840c0f80e000466080c2591007050001c1c605030341010190700081400c1d95030305000c005440e40c1c0101a034194034400802c002a030f50811241000f49500543d80401514010855511140c014206110036940f010015401c54000b0900c0d405c05101d44801c1040d5121403c125500d500041c0080f004501d65030340582c5158010850b00d812a2010b482140ca80786610b40112031541000d0303021501d035040401000002c0c1e44880860031900760b4003206188c05205c0403401084859181d002c04c1c0c040c0c01500d046000c0280740030486004c003c442800d9580d0f00002d000413250020000f11844801c1c003104140540140003100030810b03c5821000c031001d64550003c031480810b0075080300c8030755500c070b000040014188540906078650103030400c142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 755996501 1250 755995251 755995259
    0x71401060506042c15060f070209010b0a0305060d02060301170a0b07020f101509020f0c0d20010b100f0c0c080601030201030e0c0d0b06150415020c030a080d0213 71
    0x10382c40d08140c002c4074065450340548540b181d528140d00d8030351a02c004000780c03541410040c103c40134100803444e900410000403d004d00e144a001180d0005a000d444043d071980d5174100450340c2c0c0c02060300d110010382482c0100341b86103864109208060f0300140003610310b901c2c046c0d00d0343d005503400030b81e1000341c091043c00f50080b400804620703214a000b9009002c0c001c4500700c100e0304282d09016031004152801540c600c540e040c180b5800151000c41c0d00041e6070720207d64038800d85004d05400301005209134120741c0c084d945d00616904802108a89001600d002e49910900340c8807090b0407690000000740c0e00c3c01c0160310072404240780b00c1c0c0c10f05007410040203d4a4041c3e07400100e40200c2500da202400400c11540e05d0700c41c1075040044031010301080061040010800017002c600a00000103440114500da5a0b050900c240b1101c140002a940c594418941944080a2203010050700a060301c040041c01d020901041c900d5010301e6070b034640b401ea004030748001d4000701108100070404110110f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 755997751 1250 755996501 755996509
    0xc120c0c1509150f01080709050709180b09072a02060f0c010c0906110c0d0302010b040c020c0a08150c03070c06090807051c0e060c0a08040e090705010903080714010605 74
    0x107802000b502010700700e90300703006590352048a0044c01e800d5001061030b00401c000c0c000459610b050710484000400c1c0e589906008985100751a0040a000d1204410030400c14040da40045a0403209940c413900300da9070034000741c80340407083d22840c641e684c600c00303400154000400e2003111503100070242d03402c00c600941c0c00d2149801410a14400741e40d180382c03142c000b94000c050440241010311b440c000c2d07080c204880315100d0f04403024180c09100030b902c810f41014001e4021048104d0b0242c01040400e6010400079611403c00700c2c0a405007900e4640404e4000300400c900204003641c4c0040d0945440e81c2d0740c0012554001041c003810000c0c1c10315500f001950900502e488140654016500c5503d1410550304014482c041110019100305c1071402903500704500034284002103c0041d25030824440040c201906410000d1800000140105074a46503914140c021a1224100e0304d010352540c0040d44e45011b5404050081c03001170001320002000c1c8168848014200ca0001c41c407a42d40700045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 755999001 1250 755997751 755997793
    0xc06090c12050c0402030402010905040921021005090a12140d02030a05040308090d081803071b18021c0e0309030d0206090c0d0f020103200705030702090c120c0c 71
    0x4104a410719501e007406100c01000041d903807020407141103166041690010f0701e4a22140b180302c6c01036454017a0007052241c514400c191003c40507a41d045500c0109000075298003501c0540841a480c0c1404102521400107101003145c1d444003c0c0a181d0300c0881d02a100382014132003d03180d003801003003072a028a1850004c0c50041076103a8001c42c0e00d092a1901602d070340d00040c01550240d0220401100003a0b203c1f00598004110b21300f44074411100c01e22003420f612901e20080c00d05104003080f40030710301541d50100103c0fa007401e03030215092485210107090748036020100d01e50344900902000c484045070702060741010720300101c030710349040803000c00d00b82032009120602681105081101030301d0144640000c01d0011511040320410558620800900405001c0d04041d41c88100a40c4043c1c3d03a4a160500c54a5034490b82e1500c402d07103041507581e030100304100d00451198001c1280004403006846c015404403031582c019076100d103800c50440e0003011040603a84100325011407407030b85140031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 756000251 1250 755999001 755999009
    0xc0c03040e0402010f080405060711340e040b0a020d0615030609110f04090c05270102010c030b130c0504120f1412272d030303160c06090c 61
    0x1030314520b400e00024080b042e10240f000d06001240042100007200411203e5000c100c908040707400713050040d407083c68545881003140c44442c000100030000041076401100c102c3d965044480d0301d6480380003244150100b50b070f004020145000100303d5102d83c540103094a100f0a110000f102c5913a44010762400020040c0800441d584900500c034110031f50169110307402002000c1c034030340050548129141e116922900507015603a82e02e24000d140b10303004986000c1304102c4081c05004030041c0d0520301070400c1030303410301542ca40300701008103d029020303401c080360303004284404030345101035400c001c3d010020039841042800c005c04644080d400241035030690013103525120311070071880c0510806c0460024148940e00001c01340b00b0500840c0111292410208822507000880005101501d0102203501e03511038801558030180000c2d2034805c3c001c0f10030710400043c50307c1000c021b150b01d03880195800711442050000e0000d410f4010391400c40460312484000585810300d484400300300d400360f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 756001501 1250 756000251 756000269
    0x170703200a080301140f0102010e0a08090a0e0f07170717060a0f140a0504150b0d0609092103050108190c081902030d03151512091b06170f0c0c0304 65
    0x20505c00c890520050a1024035000c1c0000c000c0050680d804595400d40c0400040c010305001410303e905441d2844024020080c6589202040c101040c0101034400121003060014607010040800007600c0c0c01c805024031504d80301d900a29021600c0140d11100c0180a1a004178000c80000f4031000c0c5511800c006050b0485246440c12002082042550542d40b01038410b40c1442c00b01c054006d00c10b581142101d0407289620f41d00c07122060a60058030712030f8080d441c69072802d15042c0074000041601a83d62190300c0440b54030410303805041d005c41c3d0080c00740303001c10f9005410721000903d444011120307580c0108442070340103030344031031180c6828102c408a078480381d001c000120460404020030313882203266050900c8400c0860060414041d4544101d00040400c84000e6851310b0003001c02965908504070705010540047c2041009080b240008a480c10400d030320010b0001d00c1040350a80150001e4203141c05502c82d01001c0c000b41d00302a2070000c02c0c5904203d40b5868250800c0240300030b041141d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 756002751 1250 756001501 756001529
    0xc031f080f0d081e07020a0f1104060e1302060c0304170a030807080112030c0201030915060e0a0c050324120a030e09090319051e07170703200a080301 66
    0x410301c40d08024002d05a001440341c1070050240d00c001d2091080a2201c121080664170b0765020340807494002c400d0300240150018051550030300146034800c1620003810b0f103041c0402a600c001d4151030400c1152881e1541c076402c030440f40107141231002000c02c1c0b0828402c68cc1001d03140c0c1062a1300c01180e03ca880345541c40300d8010010075070040300031644a641c50408001070340c9048926600002081c00c01001c00c1109180082103a010380d00403240b041d00684403005400f5000101401480c15018031141c15145100080890040e401107122441c40303617891505540b43d4044560071a00c01541246407001050703210092a01d8400d607549050102d8002004614886d08010b441c1d041c0403481c0d80d01030410705e010007102d44000000c03030350603003801e030200600300e01c103802c0c200d8280c043d6a2b02161440c0303d920004440100850180c45118051220201030700c031a0300440c0206d11031104010701150301003c0021031900000400c44a40f909002541c0c1d00c0285a40c9010b078562090b00706401c8990f240d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 756004001 1250 756002751 756002773
    0x1505041e0b03072711160c081b0103050a020408010221090c22061a041a210a0605130f0506010206010f090c030b03070f1d0606030c031f08 61
    0x160141e0780301540194054140e8a04021a14224000d1810110840d8141c0c11401440c58882c3d131080c00b00c0f0014407000e58660b64104109243c0315a16003040d5181d151203c40403c0c85200494140d54003401034403207a050307410480041d07001e0f110080c03d01c0140d641c24030000624400c28001000e2140e0f03050307880d003401c0b4911050030200d004040c05054850303201b030b0300c01d009581b140034502c2e140c00c0c5504010406035494440c41c1c805486c0540085042c0230458061401c3c0150700401b03002a580c002000c00c02d41c43d540005000300d40268030082842c008060003040a6001810549810180d50400481c106407900045152120010303004407145513a41070301d004100d40c40c03003056004482480034128a516040808a00303160a002e5611010358648601890500a5012203030030b41000e01038070749c00d941d40e44088403040854400e02918000c00000380d6485006c1d8400301d0702c120001007182e070854484450641c1103800043c0001c0882c00e0104e0340071104460103000d10020120309000344009501c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 756005251 1250 756004001 756004061
    0x40608030d0c051201151103070c09020d0207060c050d0f11032212050310090c020a0206161e06050c03130f0206040b1801021b0d021212030f07080705040810150504 72
    0x1440ba081f02c1140c10611100001680c2c5000d05030840c1c0b1612400340c0c4130711003204907a00910560f01d0041c0031038900708000e1700e130740c1d000000382c010f6410f0b0314810402d03d17051517020340c03d0750034030b070406000e403242040040e407c008450002c5141401c002d13130100310000b441e51071803400ca01c1c011707050340428008001c010070005801c60807009840d1015040c03042031107103580603540d8a5002e038024480c1c1c4010076007001051807051501200364000d04590048404454503011124003100f0544a5a080000250705030b518502101e024035420070f010200e07181039489419401c000b0034001c907401a4204070000e00c888101c1d0107030440c1c031150410a801c060301c000001e0300c1c02c400001002c030141c0c0c5041e2005c0080e5a11488811603980664945000028405841c0c0c18100c003641d008920302004014040300c001e0103040c1500c01c8480d47c4400c02c054580071000e0b210380c00360344200e0a00f071380f000c00020500070154004108041600d542e02e1001e948070710015056860786ca504040005a007040041c1001c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 756006501 1250 756005251 756005267
    0xc09061806120f06070509130e0a060e031c0b031014011505090a090f0e061302060c03040b0705060a0b191413020a05120c03010302060403020108090f0d0c0b06040608030d0c05120115 80
    0x4043d0010000360382c01c2740060f51070380c03910800607002641c0d59444101c03c80d0140b003200c0c000c034980b03d1261143e40b0081c050000900580034014024461441c107502c08010b684a0700980b100f1285080c50260320f00800e500400140407040010442c0c14080301c0d02c1c03600c9100749807024040203440892000101c0580d00110740c5685807099540c1c0c0424140602001d0b5082c80042c16a0155515a40c0c0ca180003d000d140d845030354020305015000292503014003501052030f50203003004a00c02c0c4000043ca10800c0440344043d5102001c00484102c10480000500c240111080015044940001640c0000c20813a0000c94004010401c0000c00b0301d01006034800e201ea110401c06206403d650464021031014019800300a05000c549004107108030750802050080d660703602d0440e142c240d1030400040c041c00b11908102c401c0c0d510680401c44030b10b8079020710010f8442070402141410301c100340a0001d003a641040da070910a00f0006110f0040402c1c0d030440c003801e14211111403109203c680100061 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 756007751 1250 756006501 756006529
    0x62702040515011d041104030b10080c0f0603090109170c0d0c150b0a0e0405010f06050103090b040201140d23100e0402010c080405040c020c09061806120f06070509 72
    0x441142c5070310500b6a04445204a00c1c3c4007100e070201e840b10080301103001400b2603508184e4607440490004204100019070348e1187c8400d00344103440c40c1c1d03038603aa03655071880314540540c41078001c0c181d00c4d110304000d03014540c0010310310008140e00405850304c810f04081486090203a010000d00c03450118410410003503420b509103401ca4002185481d5200c0e07605444c5014250a070b00d405c0102043d684100103000900024440b820355410240b4240c1e0080a6244081003114280500000e5542c0240324420600e9001103561045a80e03a031700458100c415080188180031003030201c10140b046520807800080b040c3e54150aa0304203400c4140301e06c1c50300800c00440032041450500c00001e11440a41d0441e9081c2061200501546006813144c0a10740255800a1400c01b400274840d0340000c9459245c03c1c107a824904503121401440003251029603414694081000492414100045000c0503500c10b07509680045170044a41c5060050070b4482800145001c41c14520514100785080c503e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 756009001 1250 756007751 756007771
    0xd1112060a1d070b03070e102a02060d050c0d0e0303040b1b0708280f0801060809070e0606070803040c150512150d0501060b120a02030702190627020405 67
    0x82d40c042550b90300c042a00818041d044040007180036940160366110348203000410082c0c00316180c0704020b100c60554902c65a60450042012030f884002651005171142c018158030301c0c04010000c1c400c081e20010301503612503401045080740b00c40c01c5104085d074640701c850155030380c0d00f0319003410074003c0d60280004007501266075400200300740341300c22190141e51008500743c440c443d008a504030001845446100080c41c01400c0440f1790f4010003404c078821203a00c540744185d88624084038074038411246000268400300040c80f0031030f5a000d00940c0110020a103614010841c3c0d10811207800c25503044a840f000302c281403204940d200310481c0028204e00d4002e0611203200d2940c00b690901804174a84c1c0f0b074000c545200c0c0c5d6122070041c0b4940e5900030001380310690741c0314a07080b1541d01c600307078a000144100000c951010344500803030740201001d9006000015907078400400e20051800215041030707484590b50b160700c0031400d050007800f8540164040c000701c07500604c026183c004190000d0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 756010251 1250 756009001 756009041
    0xc0f0303061f020a08030106050705060a0618020702191e060201020304081801020a020d030908070602070b04030b061801120201140901020a032105010f06031107110d1112060a 77
    0xd51504804140c03440c81072008410103880b2450264142003806002811110b4000004154941c2080081150b5032080007266040c0d41c9842949040b204140503d51490040ca182c0c581454a1600074140c1503000072305c42c8504410540f600c041e95240c59010a546000d140e440440a8000d03140b140000d01d182c3c0000c0d4610b10707141e43c030b00c00684a60b50340704500c3d515071030050b10103034420801c1c81c01c4241d010300702c040001c1d014140580300b02403d1003940d070b580c0708034100440d00ca0320104107501110141141e450034282182d8850401c4500101286c1d00200d03c030b540c500000701030b0f254aa0082c000007481f850075090a0000410000c0d0b0405a001c2180080100e00c03040e90740015900b45468151030098500500c41c5403c08042038943d07000e0602d541000008607038040b1006d80c200803641d1320389041100140100304401c0a00461001a11441c40011140c406040101000000c1c03440740ca08014280e1801000911a11800d102034806620a0040040081c5244520088030042c004081d107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 756011501 1250 756010251 756010261
    0x3030415030e0604030c0f0c0506030f06040e0c01080c0d0e1509190b06010c11040606021f09030210090203120715050603010e101e060b0706150e04021c15020c0f0303 73
    0xc06054800c0f00100340480c01c1103c0001e0005c01c3e08104094180102b6103607681c10044203481c440301c410ba030b1881c03140d860140e4402c200072000a5000d101941a15071b205030341c5d80d01045d414580c01241500b0402ca03242c0d4903002c4291000e1222052044480c41014404e04015071854075040308240c1d092814040881c402d0040354251502d950f00150900c0c2c40280b4851601d80b000581c0116114150440d0038000007086e0300f034010406551442078161485080480380c582c400684080007006000b603000003213030740e249a0301c0e50012120740d80050111600700b1400d00c5080391070f81c0040402d442e0f40d9030000d6458416001805015008a4100c00074044007408207100c94403214080610070300782c3e0390780d06142c01c406030300e08104940e80c603103182c10800181d0394183d803490350f030007484101c440e030703152030004004a043d680c100c0c42a14070181e000b5959036215424086012003d065100c0044130001124000402c50407c004050700302032405600e40480101240c070b0070700b03a0610070a10b604144100304d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 756012751 1250 756011501 756011507
    0xb06030c0d050114010c14070306020f0c010e0109032708100209090916050402090f060304030e0916020a1e0c0902040f0e06060a0509130501030609150c0e090a0b03030415030e060403 80
    0x405454100c642609454028407c1a142c071603194801443d1a0010402120040b00000a0321042034400d00034011580100041422600c084c0030041c0480c0c20b412a401d554483c0120315041404119950800180c41c1e45d0501d250034481c10500000940000c0c0960540c10480c0f10070360000010401441c051900024010f400790391400303807601a0340d02090300d034803c0c1d5408209052070300b030240103595242094100104441c1d104405e6500800c40c0b28042480c0d0b08052000725031031000795029004945180d610305045a000105101c4110501c13038442020500840ca444010a40340c1001681c803803400d43c0b400060121680312408919910041208a447d20800c0f00ea0038800c07450031030703a501060700001d4820040350320301003050391030000003204212807a402501342034000c08542c5401440e800c0c3c820300740c8010342c2400000890030242c0c1103080c1089880240c0016078140e0115494a444010a1a540003a0b0000703001c1c08040c007440702280d41500ca40320810480101810040c5440e490203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 756014001 1250 756012751 756012767
    0x30a1401090c05012d0306050d1401050c07080f07080714070f050a0b040b0a03113c07020904020307091e0c050f07030e01090b0a03050907050a05180a0b06030c0d05011401 75
    0x100050054485e4069a804d1281e407109015240c018000f54121055040509081003078000e503c1c2d0702e61a2a02056002e0525826600d50540c480d9045240c00e000f4200981e00303411090301203508000078021500020b11000705000e000c0d1261f002449818a8014181249103076079100b0b03406500c101c030080c030480300344404031410744400c2410b05581d80080d1074210014a2804101e50a60b540801e00e42c03213039401c4103840f0a04817042550220391503e0000051250040314014041d4008100003620060401c403071900c2d8400d0009050319071090b611100ba9054030700c107001030703003400c0303040b14100494220600c00d01c2c070701008a14200303060075034044054449115002e006802e1004d000006c5410368824141c0b00302500303041c51900d807504440a0003070003a140a60780942d0900980102255504000a40348100c900c000e240e90980c3c90b2409040b9981c01c40900110300c2070fa1500082c6016440b07081c000c600400d8854025030352030040c3e407440000c4540607000b00d10303003140c15011080c180c0c1c0c1c040c0b2a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 756015251 1250 756014001 756014057
    0x1050606090102190c08120a020708030909010302210102340b1b0d0f060510030c020c130905060f180d0c12020c0a0920040b030103060b030a1401090c0501 68
    0x4c107204d010103814044003959044c0c1c400207541c0300342e045043c50641824060b0550780f0041d0200c40f113051721442040c0e12805a804519000000c01d0010805494141c00c94424a0340051506003090032102080d42a41d01c0010030600182d014014a09032211360415004a40c080d0b240140c01888180d560390159480a050f0300c0744070312940f0f03422214840c0d02c0f04a078400b440894080103502080c50100000c3c003da0311a0500ca203c05000840465001c0d000d02c0829403405c0c0d01900412510400300405054902c43c020506607550390400d0000744c1c10802d217400f0b89002480740314185030200701d00c984110444054555504000300c0310440d25000500c0c40529a4080e42c50716005000000c05c03494618408070700c3e64494100c410014201500d5402010151a0f5000c00c002035694240360070b800c0c1c410f81c03050b9030503020104010030206843d07074404070200d0701c000c05035440c01040b44c0340d0200c0316030f20310000c45240e59500244004c20001080c0c460007400282451881d41e0000e2420000250300704036 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 756016501 1250 756015251 756015283
    0x1914211506090a05150d060602011e0c08060613080102160b060a0308030a05060f040911040509030903060103020d0c05150301080d1b0b0718080a05190f0f05030418050901050606090102 81
    0x805105c408003511118050440100411607481400a0181c029610402c800b1000c2c1c60079280844c3c064007660500445684904003a611008144159036011001c122454203041002154800c400c1c00240b11100c0c1c0108082c2c50310446043c03650711002d01408140c8940400c803030030000038441205a1307603c0f40171140005103130350312640800c12007a07072990078560007481c2201860400111109c682c00003801654200100e640d03d600c041e80d20310a080b64168154071007001080186803286003007800e80d22684444e000e00e55202c3c013081c0710050710030f080740524101000500c50904200410408640c0c0d0340392600001c080d0b0480700720102c1c0b841002034200c0030100000b070740383c90050f403125640d1014164882c1c0e0090342e802d0a6a258010f10100f1a004d01407a6140b04800818400125a41390800c2c94002c2415179661030f8000e400c200b00d022602c0780418400001ca61000d03e1600484c504003100201d06464481c019908441c801490144142c005100802c0d03181da0000e407869600d07030603407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 756017751 1250 756016501 756016519
    0xb030313031b0521010c18350703060c080103020612040f021302270306070f0e06030a09142806060b030705070302121914211506090a05 60
    0x4104102a0259048070741c018104c07107100000e140301a07100c03415420800d0000c11108914202c01c507018140d101640380d00310900103040c00900703001000e03518107104840018118a5580c9484103041144d810082c000c0d030464001003090084500840c44422414944003125604650009680740a03080040481d0a58800010200711040340f0040c40d450300141000607076088a403940029600940030250b000814050220059010025819015030001c014040d2a918403004070350f15003600900208002e0100e182d4902c98a0b007400460040504203800300d1050000e003081c402c903031020400c094103544500600c00d210045410a00c0504400c0c4030030085480d143d0611401a0100da00107004440d03001090041d501c3d000300040200b944aa02070b690b0f00543c400702d200c518000c0701e080b0b18800b0101c0c00036002d040e1146114403000400000217604101c20046045960b2350350200584101c1502d2007409405507070f0b03503003581c03d8603000c403101d078030b03144e2400f02041d8004498031405005814103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 756019001 1250 756017751 756017783
    0x20703030f05040501022205091f0905070e040c02030c0705120109020405130605060109120206071716060e0304180c023307080903030612101401090b03031303 70
    0x103504001d0314499429024842800c05040c124001e500c503030002c03404403480414035034007940468064421030340004d062500c56901c00000c001c400d0340813840440700c1c544619021a80800520035280201c1c4903541d4506203009607000d00044500c50140c803000d551042c004440b00700e41c000b42040590360b0546a6900402d9003001c1c0a02600c610600254000e0426081280c3d541c0402803160b05180192401d101036122540103407510519130160008414400c0400c2c400344c10410018100d1901ca0180d507400c099034000d401c5065008910902100b2a00218400c1804414040c2c81070700c2c0441406989000e160011400198240d010f20080d0180c41c1c55454000c54020300c4084800c42e024134001d001021000324021440c0e010480d0190030414060205921501ca900d00314850a01031004601d15129032042050130000c02102c81c2c042c0c0314440c2d506000560a0150341080041440103003540d5060002140075210311082c028004d500070701c01441c0d0802c0320381101040369000f402000c024614 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 756020251 1250 756019001 756019007
    0x60f0d0201020f191a0108060103060218040204060c14060709031709060408030a0201060e240a182f041710090f0201032a050904022106010210060e0a020703 69
    0x960b55403001401452113100b0b20822006090034203070300c43c43c95032108405461035003c400c0c13428040c5288640c01000140000340d59503000f8400072410401030741001c6042c60004040e07a010b508000e00081842e030841d41084020081c074601d400e00080034204034507003010000d100e40024800600707079100b400c0c130200c114201001140e03032980c0d0241250390b0f100c0d21051050b640c2d602911032140158640000010301d010919122402a0711981001c1010700c02c0c260104120540c0b44001540014034510029045803070603414064101841340104086002e6581025107040f5103118403000b01d200d040305100d4034581c80485040d1480902280d0b40a404810b19170304d40404159004162440e0080c0802444210f4100552540c800d0340c5c14400c0c003000031b03040c0908a000920381844200e0200b005c400d07071802400a00191040584014140704071400d0a840d60038514171401c1145100340f0038000e0659041c0051041510b041c04107101480c644030700c0c0b0302000713802062030300c08950200b803031010944 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 756021501 1250 756020251 756020263
    0x1091101030b011206030b043c030509030d1107060c080a0305071704030903110102030c0a02040216170409050c03070804260c150a09030509060a1407080a0e0603060f0d020102 77
    0x3c80300904001703007512890960031045003603034240c41354020000c002ca09090401d1091580c0500381000d62424810119099210b0f440d9104c100e060000c10b00400f51561003c016407038034401550303250805090024400760400205422150421840c140c0340c20214100a04032101c102991800080581c2c46a10403251410300744048482071040b42d060206250703001760000c0640780074210020340410100c00599a81c45020301c1800305400000342c201c09858540d028144040d41c050303440b40080301c02d03580c4840c01c0b103010703514103a04100450300f4440f00d0110f02c900f0358000b80502d1004d20b1070030480f1000c0d000310360081004101c003004510202d003408001c070030001440c82e0407040a407650201d07154107440c3c0800341013142100d900400000e003607007a6401081c000d241c061b1a02c0d880c0580e40130a214060380501c20043c1804411300c040400350f88008010004580119a070503140c4560420041c02c4142e01060341d88640414000d0204a65a650314940303105400c4a020b4031810ba148010b0741802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 756022751 1250 756021501 756021527
    0x3050601091e17070e04031d0a03020d02010f140f041508060607120215041211070510110106031a0910140f060411040602010e10060f061404050d0c1701091101030b01 73
    0x400170000703001c01c03d0380203100c00401482c107151132580d0310821014800310703407920301c4003950012148440340099400341014200006003441c0440315148001c0040296a108039407203205050002402c118000800c800807c84141c1d514051419082c4000003440740e014030900035207900f01e015102d20f030807030003048950325000c00701e11000c02d5403030241032140c005103031102c0c07403c0170078a5408030840545011501c1000c0d9a4005d00e550049800036200301c400d64501150230040350f50720807001c07010400014582c9003060300550f00f0304180c5400200c4034104030420301c4000446040001580500440c0c080b0719074042035028082ca5540e81c0e00b8001405807c207005000103640c000240450405c0d4190081d811011703111048425203c503c1c40d07004101c4003980700d51180c1e0000f40c1300038810340b40326801071489100c00c011201d0408e91a200005c5000fa20001c0c2240c0341143c80700104041010040c1300e00f800310303214000304002c02d171a80314254a4202800128100756451030050201da0150416401c08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 756024001 1250 756022751 756022769
    0x250303050c0a0204140f060a05150d0605030f0115080d090902160213020a03140f01210c08010209120f0705090601050d0e1e1b1c0b0703050601091e1707 67
    0x24000f803d049944840946071000503480360030000751f072170030440b9a2a080b03e102810407403052000c0c1c045040c1c5500000035034508a502c503040043d040c0d03010401c0c036002442501c000580c03200d0401d5190010103140c0c0c0011604d82010b208541c0f002c0d0000d02030400c80700c40a0016135940b02501c840707151701140b444c0003548442d05a83c0c02800810950241000000075102008003900c40c00c080e03840b19001f220340c1d00e0320041c40c80052045211070210086444464010a2081e040c035641c1c0140011842d00040050781d408104a440c038940315149800402140000d822501850070341e01e502d4584d68080d55000b8600200840e02c903920a0703040307580c030040004081084502445c000c54403692189012440785440e4207280e00d629030f0204007401040480a41d01810140d5642403115482e2020020030001003180e240801040c05030901c20710583e440c0d6000141c614001c00050449960ba40140001044a9104402110241c40290155152000c1c01c00c1217804142d252403501d5035582000d031030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 756025251 1250 756024001 756024011
    0x912060b100c030e010c0209130611070b1509090d110c12030c060705090603040b06041404030215010608010f0b1804060b0a030b0603061f03060e011403250303050c0a0204 75
    0xa164048800b60700244256110b002010764000112441d0041300b07000f951002d40000881d0000f4101c4038100c031454804c040205030451000c40131401604440c02c02d850f01130310b100804c40c16414a206002d000174044540704103c0c14139074011a62024001210001c4c0000443c4500700600c081040302d56141e0000c002c4447c42010024407a01d90f000525000b20600ca0b907004249003501560075540030701d0019005500356903898a41a0040300c01a1416410603980d03841740f5910710807003810070311a501030b8000300082110140c2142c0d120788168000c0d400c105510005210380f422100c121011902d13403901d0a922a480b1084e00346681500f0a161507002e4030300038001400707602d07031009080d00b8412500c04014000b0600148202840211003003035202280b22203d801c1c00041d0044850b100101340390004805440d0084098605003e802000d10500c500400a015181c1040511091940e6400700150441244010744c510750702804001c00380880807503203045407002003203115102d070340050003884 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 756026501 1250 756025251 756025279
    0x4051609090b0a090807080d061d010602060703050907121113270203030a030504080702040501030507090c110604030c17031906082e060e090127030912060b 69
    0x8020003041d4011a000c848480025280d01400c2c4680300541c2d400c000d442d0f141c200d00e5905e9503000d510100e403801704990740f42c20201d007420319542031000e0924441d00781302081d4144403000e0710309100200030b4401c040c10b20b800c0145a0f0f0000c201c100c110740c1040061000602c441c50820070004035080110341003900c5081b0380d402908103404c028010070840565000344031aa8443c0f0303903480c800c441e010b0b4040d8800c2001c00d0001c1e200c0d6001c1548a80105045410002542d0000307003075400c203030300a0340c2c10350144600303100a015a11600e200c110250502c1003812445944094071103100800240501c140880040248040d0344901c078003000ea0080b2580e0380c1d14010030381e0f10342c0c0ca003095148079a040c070b00320380482d0314600028103d80c503900c4401140302092000b98100258501000301001c1c2c551620380003d250b203010f5208e1402a14080004161b0640450007100280084004103c01150810440c00402d030080803023002d41c1c414091111205465043c03074805011408144d035001021070b007040e2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 756027751 1250 756026501 756026519
    0x15021c0609180512090a080114090628051803071a0c041d06191409090304050109030b070e0a0b03061009062a05120711010206010608060405040516 65
    0x403094034000c031800c120078a1001d142d004500c51000b401000350b4482c00791500500b6150f00541740c440001418015050f898040c2c950079140000e00d01c1e017070020720100740000300000344406a40300b1070741400d4040095000e03001011711b51268800d03091440d69107010070264590840c0941d15070001c14201ca42d5080076150007003907142d1401e40c502500c3d02071000304628869136011a41125501d0044c600c0600b000140141880030140203247d002401c1c81510002005183c1003000500318888528010301c000401d020342d00000414104150308104000d00c4643c0e0040055000c0ea070700600c03030540a6460701400c1c1c51505000d480954400081c400005442c0c80c403100551140500351348100603084040e100742c4046209001c0c00c00490500940c007075210180700401c0810316003401c0c884100d00710f152691401d100c00b0000e015041c0b08006035441c1401602401580006003c0c80100001d62425200400a550241c9210f10607070f1190081014030108000c000d0805001184104005584d07508007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 756029001 1250 756027751 756027761
    0x1030b04050c1806010f0905031b0102060604020f030403081f03080304030f03060e0606090102340e06010c060504081c0203100504050105180c0d060b091f0c15021c 72
    0x1101c90384a80114000c15040422248003c405800c2c80e0722084d40314480151010a05030014408001c000d603c000b54590301003103600080c0c0d03000c0351200d1814060b04002414148014401c5008070300400180741904106811254040c0d090710780b0704900d0b1034201d00064072214944d032417041c20100600101c01d01403450010740c000ca11a440d0368407003644a40003502038560512641005001440029043c0c0c05e04070004c042010301441600d0f02c01e40800b5042c140c480702c1c100840c0c0d543d687c0f4007145510300050078041c00038141d0003c40b564113150200009200d00e00460004209a8807080841c0800100344281e445442d500d1140b0202101a0011039000307410440700169910800c00001900c0c0c181481050b06861010f070200070f280350702c85040383c0100c02c00340402c8030300c400030005912076018030310a020150410f510302980d90308980e41040034207039a6030340840d02100348200042e00250015040380b0b001d980041550302d054040b09004000707004122640103120160300382c0c025014455801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 756030251 1250 756029001 756029003
    0x4090222030602042607061101090c0e0403020606010c05030a0f1707020105220c12050304030b040b04170c1e19060e0d02030903030f2b090b090c031b040204030b01030b04 75
    0x22959240301c01040c2040c45d24090703442c408543d040316509004441c0b0843d50000440781c40c000101d001400c41d07468031940d100c26403042401c40c142c030041c00105035044c416a60010b0007441e107001080923503290603817644100190502880449401010719034040e400054242080140a260a2615000182c041d0004a90001c0769045128203642020b0f0720044240000b60080184a466410040d10400c1812032320f10540e0180700c244400000614800c2c021441076100d60844031860509190411480f4403010100364252401e0184413400c0a0000f0700b0040303c840d04450f00c03240c4034a401a11b0400619000364005031424240f40c0c400d01030741c0e1b041a600006040d0890790158080780c41280c4a0240444044d415082007104032180d65221000c0c2a01040d4a1b805440d01d10510010101c1c1e8100c2c241d540052035219600c1005106005019a80c415000005080003442d0800025280c8000c5154400b00f03810384410080e95445541c1510041c6a01000341851961a03091070314003080e08941c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 756031501 1250 756030251 756030269
    0x6030c09050402070510150602070e04065c0307090305010f0c020f03030628080601090c081005030c1e060310050a121104110712050a0e0105030c0409022203060204 72
    0x7d444028002c80c0c3c040e4404a5040b0340c042e0404908225200104080142040d50310548427805034100d04a03226014107080c0286280c802003403644601c140c004072a542d462035104c08c2a61800004600c000c2c41c0c5c0036448c031400d046035504e50718404191440702083d040a4801d40c60b2481c0c0d03030300144285c0c0c407400d00c0e43c3e10798080f5419051011041641d91000302d40e02600415984407003082c4a110020308691544c4020300380c41401d48400016140020136406840750a8540300c101d18101e07005100182c00078441c4001220340360405001c251360b411850301540c06900303060240c1d40c00401060100005050081c405c0740d980c00d0103070340c11168000c00e0241612800924000043c0c1c074404520700545107901c140b1912080c01980d003080014840182e03800205241082100005400c0021403000c00300c29454841d00c1e541c2080005000e40d520069450501904209000000200f041035404627081e4181c0540d88010804405441002502910369044c44900002c01080a90380140055404c0b2038 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 756032751 1250 756031501 756031511
    0x51f1436071704050312060d061b0e030303060916050c0708100501080d08040201030b0f06160605060a0509130201020f0d02010f0f09120c232103060303030106030c09050402070510 79
    0x11010b072100c00554008150781d0003000900440c4000007451540800000e00c9101922202e403035a0060307030344810322100c0290b03901042c410425040100c91107090b40c00d800550a600c0c090010500403400030307180c0d030040010001e01c43d62452080080342d60140c0140c059421155544480e903556021400f00c03041c0700b03403c00c00041180500000c220f1841c0d8075940d500a213546580c0c0040d0000c2c00c1600c40580c0080100f1480401c0b07844040c01400030310950503030b074041c170721580c10000202ca8014150340d02c1024411001c0120f0707074980c00c45542000131440a490340304414801070785092100d43c8407503080c1c0105403d2108041d0190b01c042c02d1a0080311042c013101c64104804821621709000052191141e5914400003520804c20980c4442c0300e45038819606005c42c222800001e4000d04c2d00c041980800a1034605a00489015405544081606055040c0480082d4032800140652010141d030b60346604e00c214411a1581c0040138013800071541d851003030420603264000d201d81044628204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 756034001 1250 756032751 756032777
    0x1021204020f101403270609010e01020301060504060e030c04290312040b0307110f07230d02061309090f111909020a05090310051f143607 61
    0x155a1043c88049076584840400d039000e1150b18058101500c4407020a600310000310213044401c0400c0740018180000700031500d004c0780c10b1800e40d00150300c0b400850f40107000400c0702c2c85c2c220301503e0580d0420300303001c01c4200074400403d103080c44490303a6641c880d0500c1059000b81950041c02c00b507089044071001406400481417641e6199080f0f04c80d040d1050805c400c000c002c40b0300d0095500642a0b20341034030482005164180b80812071007140f15144c1000c4000c000042c012201140103e900604483e080303901d100010b00c020280d108040d005e2140001c04040030800780c0e8000d0068101e65504008480c060306001210b64451201103601c81194184100c8600d0000e0402e5420003003414090406070401030080042d4000000401c18003e0501c2106002e5400380a01021251480310019651500340c20000450350031615005520f0980a8280240f0f402c41245280d1000d085d60f840c0c244903180030388450099042e4100e441c0003100c202401036100f00d180030182c0145e400d90f58409d20441c070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 756035251 1250 756034001 756034009
    0x4060b130218010e0105091002030a0306082d120307180b071709031f021e070312110f1603031a0d020d11090106020c0307120b070c0c050301021204020f 67
    0xd000c5000011002c000140100e56119132201606640c041c5000d600340131070316010410154040c00c1240140c0c00c082100241c80d6803600c100750051119000504072a00c501c000d401c10380c820101601407003041030f900300c00350b210100043c480800b680d0035042e81c0d03850a074000800030030980c00403c1034840f0007240058168510b000f40c8407040d4011841c3c0f202280303400c816580381e40c00203a4045d01801180000603800c92410000d0400b495601c10243e03946c0c1803407032004001e24200c085a000c4981c248a40d4000c2a400a402560182c40c0b040c0003580e020284040400b6010300310000c1035824000070278058150400c90030400e02d07440f0313450034031891520f407a2a8881000d15006142c00603981c6038050054030341241410f800780d014006c4c01040b2400b00001c28041c403801d030807110150303002c0c404040060404000007002891100303504130301a2650399a000e42c145005d0301203c200140800f4000038001050704140007444e004008552354800340b080c82070080401c49084e4400c41400042d0380039420 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 756036501 1250 756035251 756035257
    0x11a030601022d07090209180106020604060903090e0112031220180411040f0510050f0904062c0a051614090a0e01260c040b030f010504060b1302 64
    0x160041c00344510400189101d40302c0010800d4140c4504090f00c40b807039030303050000d5806080e0103000941d8a036002e41c14003250403a030b86103108000c04041c0040007500d5000c10566000b642c0b001c2c01003082080e900301100c680001782c02040c2d450791140000181010490020754000d48603071250a13000400d01100b000f02d4040003422000d071500b0740089400080c00c01e0040c0188072000040000c1034008001040c11129041720042403800c001030140000d0100200c81b40042030304440d0b400300b000784148020712500410440554082002c54614041c2d51a908454080c20a14034400c0492a688408215051051111007464009507020a06140030b80c0151841600300c48142500440e0080c03080304c101d00002e01c0a00308501c140070b2031034660349081c250402800a0388406065504003045003000302d184203071600341f0820544c0e44440110780803801003051402110b002881403118030101e07041c0200358583c100b0b254681000c1000b000600c2d40f14142c904400e0344c80a1191400d069800300701e03c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 756037751 1250 756036501 756036511
    0x50a080f070605101e0620070902071109010801050103081b0a0f0506011701060305030a050f0f0301080106031202030723070b07060c020c0a0e012603070c140402041a1e03010e011a03 80
    0xea80c0c110040b441090881400110903200740c1208d05407595150610102d8004820440c1c1180030310200c541d0307600d40b140e00e103801340c440d120003004194903540e9450f002c0d120341e180b1100c0303801514642d250b0110081c00301004003600045100c004c0e51035031400d04d840d10380034007401c426101a04020181100d05109510549a00000a502e007500d42d80098895030054105d80703103c10800c0207144411819100694020540a400820880d0640c80c2603034100041d20751500456005020401c0405c1030480414a8258500300f40d0a842c0007001d9200d081140d150401481114009408000c001d0030f81e110101c80b1400e982640cae4052846000c10940b108103201e44e00070480500014004a0302140d050703078022703400000715514001c0280d6110700710f401c070031300c00d44040071441c80400680b03050000c0408802e0b0201e9086140504200c291745818004425610706588081101104c010074080c10403034028030840c0903500ca41e0b40e4410a200e20400b4050b50000070302a20001801d10207004c01e0324068 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 756039001 1250 756037751 756037757
    0x1401090c060c080904050a1b0509270f0c19090f06110618031c140a0b0616110316170303101205010b150901080105030a050a080f070605101e06 63
    0x20132641020000a82005040215015584c0221091001c03e034116429401403580318103407036104800c10040401c890300380340601401100b520810807410b112945074005100c101010281d203821a0840080c058142c800305409011003107064515048050392085929400009124a842c2c410481d03a0500d00e140b2900d480d0702440c040303500303120020300f01520f00c00c60200700c070b081444500c4401d40701c10300c4140c3e480c02070399200004014017840c000d81580c0301050500c14490071840300c001c100da42c4a0394401054000841d0119002c001c0581410520481e0080850315000b2811079440d448141c0ca10424811007052035025200c501c000c029217100d500b0380003d40840a1800c5143c5010412046d011100e6540c1d8000100a03603a8460110b01034945100d0b68503241c5889000240c40000d040e0031a600ca54810704506e000181c0001c7c0e24508141e00c1294030781c03920684a44940c0300e0049803802407403941028104000f28011102610881380c0107280c0c0b218040020030201d50541c105d00541c400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 756040251 1250 756039001 756039007
    0xf18011104062f0a0b04060b10091503050610050a120f050f09161a09040e0706020106090902030c210a03020c040f140c1b1605191413091401090c060c08 67
    0x10030883c5e00e02e05e038000d00604000c501c0952030700029907414441ca16180c04501c080c03109000040c5149162400f1a0a0b070030100180d0401c00c002440004445c0480010030800043c0e48000b94450188000c40d031040307850900413000a13040c0c00c40034040844110480050210008030700401c0000c1c011705040b04032450f0700c0310a007003031801444110550b120482c05c80003005009035503103440c824090010001d00c042c02500c3d0801d00020b0079a00641d01840d07a15090008150169a0104607170700d25507030072142051035420351141c00b00001a8181c0d00150790281c5200d5609040d00812070400e40c40342101e00b0007100e801080007070111004038009581e52145a00000c5207641301300000c00c20903221241198521711000e134054946078058945801404107170230304000c1824245468036000300e1903404885668105448d001c110727001240c0c0b4601c101100e07518079070604641c1c2c0c003d024481d04070055005422011000a0103491701800403a0803c540304000039109102d0401d0140302a44280d40e030b85 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 756041501 1250 756040251 756040253
    0x30709150c050d020105040b280b01020106030c06020312010f030b06010e031c2d0210020d060504020c0a110a05060f130e040f03080703050f18011104062f0a 69
    0x224680c00000c0d140305010103100c1e1080461000c1140d032a00e200150300220395468246071400b84818080c2542000da40581c816900082c2850312011085450150000c0c0000b90840102d0240070194030140c550302042c14041081a0b002c401860703124290074000390580d994680500701c5468501c40a1303d1150004045a5507601c1344948009400004080340e104d604c400b2410307001800c0754554400801d0701405480c6a20401c081e00d0b41344055003205107880c84a0021010751039460307110a808899500280031844110b03560300c49405003e01400c02c42d251101c13201d409690b554000415034042c903010136440002d140c180032007026183c01604c504d041480581c40007980750003a02c1a003d180c080018040746a050103e000c92080b401503070703440c4c2c60040303031b080161062002600ea1810542000e0400140450700c0100700d8210b074000d60300040c070304144e007401070040030340000360b204182000500060300c2c0d503c11460303440380981c3d001540b51441200300c0900303c0d0013550010300d101d401c0b10710050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 756042751 1250 756041501 756041519
    0xb010b1303020d020d020a15020c030d0c1e05010207030509041524030204080a06020a1409031f020705101d150a050405150c070c051207051909021b0c06030709 70
    0x1070743c161018010000266040d40007513544c540b40c2e00514020109522207802080c0d0420082d1802c010a5010300074100c00e08a00410a0f0401003010b00f0150200007600e4110f5a1030003841c401e80d40110086480d00103610300100275a001d100f0780391181342041c10a0300504440015101204c0c00f03003102030030500030522403222400c032417000c0740141942804000f44070241444481000d610a200c01607481800e4030014251005000d00b034001442d06118103111034500140040e201c107900541503140100840048001c1d1240b503200801c0b17801445001d808620b05a00003c108a44c1c90718101000340030f0703820040e41c2d4000c0c246070910002c1403801140d0050001d03400309030440d0140d026200c0b05260740031040b000f050207a0703001c4880b0100048540c00c1c03111394841040604402c03a40e0468131a485404980d4032039050080c03a1041003c555075003440240c080045009104443c0b0039512126198030400090b4600740900e6100e00580c040e401d40e030310700542103a01c1341d080c039103400000c3c2707050003019 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 756044001 1250 756042751 756042769
    0x23010213050108090d2307060e0604170304050c0103020f0c0d02010e0f0a05190c05060f070303050a0203282004150306050102070614070c1410030612020f0f1c0b010b130302 76
    0x700326000010050304000c08c403140500c105910510004103602c0c20203180c880341060020a94100106007402808006107011944c09022130302403a01607258a6070101400d658880c4070074040c050b203d144007082c040c036010341101c0701542104065921a8003103085803500d98510850042080d04840c108118044131600a0100c01d401031a030105450303141c50204003a50711950070050701410201d01241010390500507554410403085041d81503017460505400310516903038100c0c9a402002d4000025400c896100307440d05040d000440f4048540160003c0283d0303c2401a0b409100c0790701070240310f00e07029010b4401101c0069004100c10751501104482c0414154200e20020b41c04000c1000800c15020302c0c0005000c0b04401e22000c0046e05081142c0c400b031000f40c200500d81007071703000c100040e99040c0c40380f02541c05641b111800d80500000965040398031046541c00a5542c0101003414444041d00e400c69101d1850703103d8698031600b1400302c0f4003894004079400d000000c824001070800c0c0750300d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 756045251 1250 756044001 756044057
    0x90712061b0e03151e010e01151d01081b0d020408120306010c120c12120f1521060c020309120c0a05060f130621150323010213050108090d 61
    0x2c0d03171450300480041124010001c2c0d020b218074580f00c1006114071038401e00354a41040090808480340c0145035040c0d010410410b0aa5050110660000d40c900858071340d0244a5220500c5490b510b1400b40e032000000d410034091001107101d030f0100c0701a40b95541040740d004c4d11058550800000003992074800e549558140c410401c1f0289408400240382c03018030005064640d251050600840c1008c0c40440714030440b41e03480b180c113001031000300c6052000305030b0569141c00000c0e8030621340800400c075054141d64004000700d2400e980032280c10350102c0541402d02c8105d4000512000314060a681d41c070307146002aa2114040208120900c1c000000703080350384110f80e8aa040488040390618201c80540c040c002040160000250006100646400028418500f0401b1072894440400305c00441c0c0801003031070030322405110010140f0b080301100964040003c0d941c8203c8094080c50091807032054501060b41000405e08103034002c5050034803c03c1682d81c03441444010318400b900c3d6096014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 756046501 1250 756045251 756045271
    0x322031509140f010501050f0d150f021b150f040b060f0103060e1806100b030402040917031003050c04020c2505030f070e0a090317090712061b0e0315 66
    0xe0b80c241c9003018030907020201581400059158907090520214456141c0719500c1004555401800101d9105031501c80310039544002580c00318450a00000340300b01c08103040165011880c9a505940005060741c60000017030f055007a0f81c884c40001342d00d510041d107000b003c284540700014000d003441195103141640515011880c1b0780e4030384410b40c00c2c20064039041148030000d01d5405003010f040004582140000705188907280c50000100524000900004e2046844403810320078045007810f441086546100d0143d80e9040007144941c4031812880100c0740d0b401100c20189280c58180700ba20078170031003800a09036214903250702926107030b5105082c40354903030004d0b804202d40c1c804010640000420300000c103055401c00d18000f201c5100103104042d0a81007500c880000ac0e40300784401440480c10319995515190404982c3c10010039821000c0c841314031003d20f8003841216049160007124102c80180505c4c02500201c2c1c40c02082c803c41d542540c444a00c1c13410030b41c14085000c0e4003402e106 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 756047751 1250 756046501 756046523
    0x90403051c06030302010e0606011d0d1a071e0e060901120e0f010c1b030f08070e0405070e0405160518040e0f06040c0b0403030f080a020d0e0322031509 67
    0x901e000032542103400c182d0041c0c1d918000c07203909410400c0706903040102424410440712100c1c5090354143c10604880c1d004a103045002d8040140f419080c410461050100c0442d038a04220000c000d182480020403060030001003564107140583c03141e03040c141003c0c14036071403c001280103440e0011a4012441c0309540c1d40007010400e581408100e980d8071340c440000c030781c0b849074200c000c21300700c400d101410b02c0c2c242010f6030b0030000c0c0e0481c7d5041c01d48080c6041101003039070344a009940c10000b22003d00e42140c20f0000300201140c0c0100150030092b800ca4040007580c5840e4602e252490340d22100781c0100f001041155100408500c014482610042022481c4202c09100506022040c240b09a10340d211000740810007070440401c00140c41c01c0701c2c2c80d070300342481c60b14003e00c404a00810941840300200100346c0344402da4040f201140204007007806035028401c0c40b40da07281c0c0100d0030f103103c000750550350b41401d80080810000702c0303410480c4241c68210103000d140040680c20f2085409541c80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 756049001 1250 756047751 756047797
    0x9120705120c030706051501030f0b0612071704080316080910110c0111040914130b042109080c010201090c0504020906040e040f03120506060d0b0f060d150504090209040305 76
    0x250042600c680c1900b03a6402447d82124000341c203940300004e8041c2c4680c1008400c54040d00d40340240c0381c0141452541400e01d4607540c0742543e412401c120089180c200348402c220500c6124401180501d5402e40803080400f1700d41000c03075440a040e1208034560b04014550741917030850b40c20150203060b106456500e000b54140440d130865a0f9081c041c003015401250400c50203800d44200d480b10131916050749220314011400c60075450f8403c038003c01d0104200007013400c0c040480c4440d202401d0008603404040f401200140c0903143c14450580644101c030386822503944107004440e99298440c051000d0340d41000c0800019410000f401d581004c414813001400c8506018401d01860090403d010110006e080041507000070004500c0141e00340814481d0548814040700c0040f8059200000c075204104001030030504140060b5502c0500070820740b040420756880741403131252400800707040342d507200244420380300f2044020358071601e20000503008c070340500000d001d825400314460850100c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 756050251 1250 756049001 756049013
    0x18070f231b01060b041d0a060b0c060402040c0e100c06020d02190305070219020d0507091104140d12050d0b0604090e2413021801030b09120705120c0307 67
    0x14048007940302070340c0c12020021182841010082c000e0103099624103424110001a00c0404007041d03030707041c1800000a000c2d03004903030100c3c014007441c000f49542d882c580c525580c0d80c4c0d001a54140c0c8100d10b02290001458015140041d000001801c403400b01d58072070710152207030120000180c4405408021716030701c800061004010300300c3c00b07a01c05d200102d54000003c0480b400206000709540c4109220b44131440340032510103c5d164103c074408080c4070903180c010b0520039281e00c41040f481c20105800c0c51340c0100c00c042e01c141c44c80111606035503003462080100055241c0c1c8090264161900f0311007809209000400c0800103540c00414151105008640c5551040e8070100788143e03100301d04680400c0600c1210024410205003091003001c000d904815607002074045640c50602a5502046455444030760b012103402c03401d40500c540e500e0400102a10f002c03901d0101500801942c60b0f4150b851b88159102140c0120040090204940c1008200d85c401c210707250700e901c0107010450010315 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 756051501 1250 756050251 756050257
    0x11010b1c0615080610170606041107050a08041521090c08060108060a05070c0c14040f0501080706020607110601030b1003050109031101050121021302091201020918070f23 75
    0x30f1a80010700ca130303107040b645505d166407564011080901c409180984549000260b042e08400112800600d0184202c11540d4a20603000000c00c0e5010b00c046800600000d1750141045600c00825001c0048078048100c41e0744a80241410a1010350303055844061950303484074032000d00c034190b0349010300d0b140c2c5900303450244241d1000900d940700004014041d041c5005d040c0d0007480c0c07814602d80010156603801d07505d481501644060054441040c0c002e030303a9640100c160101c0c080010401940c407003049070b40b580454060000541f10341c4012504281c0700c0c0c0c041c089034800541c050304050b400c0d60743d145050b40c80544103507040c0c60060350201c045030081c070607506d03207503c2605c5034040c00c686400c00d2070940b50164005602c0000808410721352201e07602c80e04107842d504540e0407001c40030200450009005aa9200e604080718840300c0314140e20560040020404c110307a1140300034540c006802c1c00e00070460b0000b00185c0014aa014501c2c040d0303e04020511095590303c1200746107042c44003c0303070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 756052751 1250 756051501 756051509
    0x2100c09090b0d080c06370f150609030501060e13060f061502030901090b091806040e1903141c05190221061503060d11031501050111010b1c0615 64
    0x103005001403044c0c800710480304114140c4104c03248003400e41c02c92031071700c9584480c42c1da1487c0d06468686141114000c0e40c03110450b607540c0c2c1a00c4011070744401c402031110440d408210b4103981390800101d0003920340c01600380b05842c218807800c01e039503040e0740b1a4040c04807035060311021600c1e01e03c0490001040083e1841000d6a540250307190f800c5980014880b4141d98030034010700700304109900071074854180000a41c82c0100b00b12040791100d102260041c4030030110041240501403005c0b5013454441410f0200034000ea80e285868805040883d8040c42003201818a2403290076110010360240d800042e4801c11242440c04866901822242681c0c0700d81c1c00002110a4900b9424250468807441b40d00a0026140030040040d0115804403a200180ca00b0f403185c000038406004100614503d100d041502505840d541e039204052414160401c1c054580814070108641482d018148140f41c03640030020080000c0a410726a00400c6400782039068038100d403a0301c200040c402c204450300000b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 756054001 1250 756052751 756052753
    0x30c160b0f0618040b072a23010c020c0f06070b04060209040c0e210708010608010c0305090f0a0b1506030405030c1e060106121b0f02100c09090b0d080c 67
    0x5403070301030100308000383c0d43d03040c05040300162400d0101203412090305036440842e03130400c030f5178480c40540d038103c540d103109001c2203d1507076401400c020010740c0c0300661004200b000c10300c0c0c0070110050845003031320001e000100c0140c1c002230f010906494442404a000400903000303074600506900e07000d9180380110750984425400040c2c5e10b441d402c040c41007150a40c400c2c1703810030103002d6600c0000c003a840303524900489802a00c224035483d05e0107000160003020504001c02042d03907201d188030302a004068036000800e05e01400111610340224101590650042c01352449840c6e030390360481e040001400c001c028111450801310303540c5520700254000e41c020b000460300c52480e03154a514020507440c1d00c0300d802c114104154600d0100103103c505440982c20150705103003e00c2d08440041c14840102010325043c10361312128130381c2080400d003a06043ea400c0e900301c04483d00014080d18040c410321800146408002c06c03130200c0d20381c09000c9040008007000ba14540588807070342182c212302009419 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 756055251 1250 756054001 756054031
    0xc0e12010c020610050603010b0706021c14070c080717040f14100e130e01020706050406140703051006110f03040b0a120c090b0345070506030c160b 65
    0x6610b40401c512540008114020340700c890402c004200240010f2041c00c81104010901c1001c004140d0181c450100150300400c00300000d441450010f003500130f250340ca40c1107002c00031400880c0f04603403400400e81c000c2d00642c03902d90785a41d9091900098680000b0282d030500010071482e1402c0c0c558070041901d20060a240e48000c420050485034003484d610a00148401c000c8203912118541c8150082c90b0000103a174090a1084038068454088010031045c0741c030b000c1104121086c2d01c00b0543c2c603001d0055003c10740da6a030341a81203d00a458038501d4007086203040040360320400383c21030f04503d05810364507022441400c5614641054101c085541d501043c0c000ca600c0d40021040c98800d0143c1041c0312003030007840301404200712400340000aa800100041c0c1d02094440c603010001641c1051007200f030088009030f0801204500800d28035080d040b00c0f8051000b00158940554400612091454032045040c9495500403a0294120007003603100c01c011820a01c3c8052040c00990310307002e1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 756056501 1250 756055251 756055271
    0x3110f07060806040b0123210106020c030604051e070902030a0c1b0218061207060f02010b03030702030c010c17040e0109061d0606161401020c0d11100c0e1201 70
    0x8165003000f0310441c0a5860b1440d41026aa84002d40300d500240c108040c1030410780c0040114440d10407500c10300310b0400110007070b1a8000c400100181210a281d013692600103030380c81055283e8005581c0900141d000402d0406207410440060030001c042d81c0c00c88840b656078010341800c1c1d030001c4038440307400340c4d481c030000c1441e0b03400004002030380c2e142d00d507440018846907000841c5048580394194080f44440e0004003261543d0040351990101070088401003660b44000401c0c200c010316007070b0019400c0001008580c140041524103055009016000300c0441c5030044a40700301c80d0a0a4401d540160480700c1c2070743c01c80005102403c2c1c24800100710750b0410708240c056800c1a17100000540096919040c240c0c50350001d00d80007882150020307960317040e0468100340ca480e81007002e411040101c41000d07030305605500030611040e80900b5180e03214410f01042d43e008440205040c42d070b030085120400605c1d0349a01064030b0f06504e08059184801d2407002c03800c501103000c80c000c0b580e0341d1541d01c48 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 756057751 1250 756056501 756056507
    0x1d0c0a0c14240c390a06060501050403021f14030f040b060d03021f020d0f091e05190201050d0606050d0609020301080d0c050a052a0a2103110f0706 65
    0x1400204203019804900789030b91015060710468801404d42c03080691040c0032225091014590089209400d05a4092030b19200392507684080048800c84d1a0038000185940144c050301c0460360020320b200b0034419481b2011a84910f00c080c0e0310704009003a10b4000003070b0420800345014020915040010346001e28058071080070280c04a8030450000e00c012001170390009814004102d02800205250280b01e03003600039004209600301800d04018000d500c40b020750340300640c00f5004070268003034440800d514a003401d2070340700c01401c03d81007104115086090141c0c6800100d1062600780d1801120596060486946811080005070009840c1d8050510b40c000e4801400d0400011440c55141484131076480c03648d10300b41c509001040000c80c05100050100794009604141501d6126000c0030f20304a030b2038074070340304850012101449a880c5050610071681581e00c00190806070b9402d0031101040c03003001010841c10000d80065403003180d002400340720180b00590006140b414200000a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 756059001 1250 756057751 756057793
    0x1c0813060309081b070513140604090201050702060f270f040b01091710020301080d0f0c120503151e0307090506030705060a0908071d011d0c0a0c14 65
    0x1480c109030801000344049412481100d039114061508a80c00381030402c1d0040c1003008940c0b11607400100302c0c048500700e89003134008031407140125400510a95403803081000716282c114020303000031014402d0400509001005100040907203020605110040c1c14000407800404081e200ca440c82c054042c003035050000c8454804401100c06014240813070000800003561031049555002d6426080300700e20205111441c601e50b250241550740c1d41c1c6400c800b5540d1456080c4640000304c0210780780303030841e204081c01062540e1100c00202d50b0f502083c021100c0d0341024268020b00b0425048074641617541584002d91402c000f6810080340074a40105030070298107601044085003802d0410000355400f00e1010280d400807100e0b41c1d19990504402c4400c404244c101c5a042d204400c0c002c02d000c15124800114810350340c1c010f10300c42ea241c440b1b0300000702da034405c000038441815000c1400700e549800500b01004103480c0c204491503190312500049019015205010741007808170b001000103003442 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 756060251 1250 756059001 756059009
    0x1b0309041406131d03075c030307030801030b06041406040c0215040b06101b02041a0d06060905090606090c0901020a0209330604050904021c0813 64
    0x22180a1908002196000c40c0c40e068459074507964075041094121610001d8841452080440e5210b11341d51030440c0c002101555600d051540360440c0460210101c81030207042e0817480003010071445c11003100380c10440e00460302e002e0000c032001d0087c0f5980f4108050080315001c0da403819540c0d4035505145180f6a0003401c1280118145800c800c5401d10009005801000c103442c0001c09030143c8104074142002e001e00c080102504d0381c10b00042c801c038107d101d40503002c100c40043c0240c0c481c10b0155000c05081803420b041c90b250780100d1001d4a042d5205030130741c505c541c808200d81c4103030368001914841000d070221440b40e51501c1c2801030381010711586901080c050300612039420081c0004181c00c1004040c0400c5c2c02c3e0000300a01181d00c05c0c40400c0c40d403135004d031400d00c01c0c0c181005100c1d4508154182285d0200a0900000070441c031a10705d450f1040018240d2490982084140f01248400401c2130342c1111204809440080c20701d89650091402807025544542508050070000c406642c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 756061501 1250 756060251 756060281
    0x3021e0406081614040921020c010314010302060d060b0c01020a0311030105010503010e0411030d120c020606010816140f04030b07030c1d1f02070602010c0207180e031b030904 77
    0x5600d000320180c0310b20f290305407a045005062200e480c20002005440800c100900c0764084000301c0c02800c021040b0910b40e20219001e5644000f5564011405c03180e070100008142c1031a0401003000d8204440105003140f6000d0700450195198236006172180d01c49022203600d03070350000716441c1d29541841003212040c1200c55140c65540342800003020b502045c001e6016170306010001c0344c104110060a5040382c00c014080c2c4804400c02e5101410981d60f6040e00901c03241000c02885034a807021400c24801c0e40140c480c05016116500c80000c1101d0400d220810300c0005441085401034080140c070039220202c414541e150f0441c505400100310140a14050508004802d40705603008910b1061400ca0078030803104005400d00003501070740d1340c491104203004842203151400c0740d01017520400e982581d0008c2c490b85076000412031b5205054424280c148100002c1c624803020150046070040c4064400c50382022100703a84c2080440b0903a25000d460390000400d00c0c0d03d81001d002c0d400e28140104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 756062751 1250 756061501 756061513
    0x6090e0103080f1605010f02070b01150c060b030a02090408030a0c090612020d0b06070f021005040305100b010201061e080d09031124070501020c010b0405040f12050403021e040608 79
    0x190340d4120300c0c01070244000c0f00080c042001d40c0703003204e45241322090f42e800c000248a17070f40e050b00b01d20000350300001c42540d071031501da400813458000400c1e01c40070310100382e51130703a07040c0e0000d840d0710009160203a030f0590f05004181481e00542d6515920a01890103403202c04d83e00d0910a0f050703012244100b1a59041c040800c8003045002d4024120100f0010102005a0b40f440d42c2c508050080840040c1c5039803010700850b8810030300c101140185101c44c400c1e25410a402400320080da414051844000d000d0751008040101d0040c45070402c0c15104010f000200c0c00544560800c00c51100e0108801a41400c400b01005448001c1004017100292800c00504070341c156210b0405051a0040d100d00139284800301c41e401c190244010051041600c3c1d0244e214400b9241c194081d60104141c40103030b60811200c094545414444c1c1801240e000000295400003a9510000e0804848040090040c20302000015031550001c46031a207017084061080e03143c08600b00000c03501160010b2240d03501c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 756064001 1250 756062751 756062753
    0x121206010e010f0c0f080a0e010207080f030a180e133804030e09100f08011401120809091305011a0a06051c0c0f020d05090d1101020109020d0c06090e0103 68
    0x10b82e14003043d11072840d0040000026042141182600000c005d21810000410080c0650702c0907074205148003d03406d0701d0b4a03a81c0c542400340c0e00c8407107643e60302c2542c008100403810903000c1d081c0b141d01d489a00c100010200c0d507410940c84410000c540c1c01d4600c0f1140500c0390108100c910038903500c0e145444540e00c8085085212000000140141c94011003150021500341800341521503035440000303000e1003051410701490098460715210b284144c0c0714042c40803403207003018003031480302104560500352907078682040360842c0d4014550550b981c180c108401026605c0d24600c0d24070411040044401c00b10312441c0c03480c04c41e402c0c00000c801d500420440c00d04580d8495410b0300031503580b0720f009034803072a400e1030382040840e115601a1180e4038200f5009402c541201d03114442150540980312942c20540050310705115030340085a00500520218000807034103120041c0c103403018800064070108036804560440c00c414025105502601400c000c0c155110010300080c1c85142500c820365495 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 756065251 1250 756064001 756064007
    0xe0406091a18240409020a03032006090c061b0303072303070215070e0303030f15010c03021009080708130302030f120d0b06130b040515090d1211121206010e01 70
    0x10300e020080300030740e803070300c411244e560303942004a1441e002019080301c0c40d90391034090702d1001141c0f54a240300000340c08440b00b0003000719110380b240040f28064420031044504000041d170205000f04030030040031002c1c503c00c403000c0000e18400c40f0292540c0190b29904044180722540308071183e03145000800410030b00301c5e800304410030786100f82e403546803c60700d5861041d00d048210303100950301444003000b006060050900503500800040e039071044018800300c01143c6413400b140c40900541d020590a02c000f054a9200445090081c041c46090002c15610020540d0241010f2001440ea9040c2801989824025032a40600b01c00c02010403213154030f4503080c180140c4045100840c1c0da1507090032291100e000310340113903902c9404510810344034401c00580390040e026450080c002201c001100c1c1084030211200c1c0180100031005040056a503006c1e04000303030240780708115042c43c0e41480250104412a4006111110a030b01c0f144124490070130f54070003c24050410034820040381859030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 756066501 1250 756065251 756065281
    0x1b0106051806031f0b060a051804050f070c110d050c010f020105130204020702030f060f01090506091b1c020a0201090501051b07080d15061e0306060f0e0406091a18 72
    0x34960140084c441d980c0c100c1d10000740b100e0310805402c803800044240c0c20f0b9600a00502a08201d0050a88216800800d1208658023102e03070b0b954104810000c0b1f54000d000301040b11109228004016981c41001c01081d0b001035a2001166281d00505450f1429030b0230028448001b0450700c001c002034500411240914007440f28084e000729800110002592010310001614000c10012140f450a1850400c150f1141c00d100c0c0c4c4a0440c03806000c01c4191411031242c5003c0d00c264070300f11050004800d80c0c03910503840407c0c4010343d694114842d042948050015040307003129600000385d109024140942529001044540d07051500002c01c20341400e80c100b0740d00303519000550030382c4801540d000c840c0244000c4140fa8100800c80b103001407002d40c0200041c0d044841403001842c0800551003c0d410750302c280c05040c011401c83ca0311410482e00c14000d044a2034001000803e01c16a9101d580c41111030450041b14070400b101c141101c0c0e410310743c051450724904801d2a1100b0b1900d0407401d60410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 756067751 1250 756066501 756066523
    0x8070c0c0f0e060111060f0c0c0c0402030f090706030c020a0303051314100e010213140105040e13060b0609010f080907052e0c030c02130e030a030501051e0d080f1b010605180603 78
    0xc2402708010030001d0f400c1002d4910b11318050000c40d13581c1004094524910400c0310105242e12940b400410440c5c482e0003006130b034145903002451042e45c555002d402030140181100c5039040d0001c1c0c00b0010070444109070303041070100d0b030203801030036010041c940584058160340d000d9607004200e03031a44642000d682004403407018400420720300d0103a00495042c45607034081c0a0707001c20f40c01030008030300d801301808840b80d10a4604005c9922240c1c18040346025030302d000d90203e40b000f01408680c031301030740d0b13a07507408032030300e000c4d18051070321040001d280505140ca031001414502420300c1c0012801e0001100350403042c20070208400d015a0300401c54620801d001b4010b50620340603100348c8100b03411010340b007111a4142e83c0c81d800c0000000700245000d2003001e1007142c0c420700c00c14890824000031b0425400140c4a2800006903840d8480c030b03513004020a1111900070881070004000044146490000312000410030520f81000c001401403182c0024a00e000310809100240e0f80000b2030315624 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 756069001 1250 756067751 756067771
    0xc1202010e09150907030204050a050a0e04060b04060b0c010209040510050306010312120c0216060806130203060f1206150301270c080d181508070c0c0f0e060111060f 73
    0x1903440c8803e0714000c42042030510f4001c0c86031400e20445e0313609034002e4019518187c8150306019540c60410012200300c0c03080300d5405201401080104000f5041003411800c0a0804104555540e040c03401680c1702c0e807002079240c3d50114030700a00c1d24080c020f0613045011076038511029820300c40000c1d19548184001462011307840032040380c80d03001d42c0f00240c4249a0302d80402664100a5000e5101c048d08040400210f444100202e416801555024040e450181009111800c0d200c0c1306130080d4000341441d94484240c61108203940d80b1011180259140719014000c42e040c160340c0c1a82c07185100b225280f00c0d0341020b0f21100d0940324010050455812a40c00f850502c0d01d03030400803c40c262a400c0074440b4007448a00141d50740d042104110980c500790b640c0300083d41d503000c0d0b500c00c542403a210440054050004210424400c101010015000d220343c51003195030b9913070b40c8a030045541c2c01140d0401580c01003080079078208402c80041c1c0302e1708016203840e14005403c041d9100d0014905604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 756070251 1250 756069001 756069019
    0xb010b0705031c0608030301060503040615030512092b14010504031d01200f0d0203040b070b0711100b040b01030c0903141203271626190c1202010e 65
    0xe556a80c20040c0141111703026660340c2e585928000301103074401c036025200a410201340c1c104500301200401c041301e411001800000d014802e2610a541c808103425501c060b50064800440c9c00d2121103002c0c840f048103090301c00c00c0d00e80c5411000940c1d00ba400d500d07540d24120401c0f0101c0c0d001200c030a1500e541002c019042d144840c01610300181d5560742000c0207049150a00111134009480c00f1701d01e00c4030007111805404004120b03a00d01c2a40509801110300b0b021080028003031000a5070003008a0500140d4031841c0c00074a45800c10046410307a0031a141c8400b105903080610914546000a18080c06030010742e0034007421009040c031004026086101d0388402d280c0043c0480d0304c0114021007083d03602d04144e07030817002500341036a10341e10002e01d0107040d055500c0001004000320000840f00564103141c9120940414200100130705480d40c0030f454502c184000740181c0d500e20704104400e1158601c541800c246d15000303034210b00c1b00a03000e100d40a0150380c2100c6503401c540000c50720254 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 756071501 1250 756070251 756070297
    0x402030c0c01020309070504050c1303060b150f0a20030a0e0102030c0a0b090d032306040204030606120b10050d0f08070507120312020901052a10090b010b070503 71
    0x641482a8200220706500c0072052003000b1002140748021100c0440701800710340c030b8004080c403043c0318180e000240e40011010400004896401c446404070000700201072500c08400c0f0340c04035502580c00c0c5281604001000c40c08940c010000d42141d16034600c4600f2010310700042180c1d40c6c410b004045007409110310640116070320804c21121110091016544410b0442c0b07000c038805034003512038821303d001741403540c2c1040d41f003480398000031140e0b9001c00c0c042c0001501240300d44000580050341103a02000048041040c0d401407900500300451001e01d103141a0038104008003001c0c0c00e8041c06124180204040d5842c580e01c41c0c0304a402c40f12035802100249801030080c030681d80c00074242d015402c0000f44192940340303442034060003621801c1c0144101030000e0708038440d0200040c0400c00521142452031446128401c1e60840e502c05010b28080c2c40141300e28280200740f1301094240c450b4041001c104080c0034686c0180481404181413407181c0e502d80d41c49016260000c414036852490a070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 756072751 1250 756071501 756071521
    0x7080c10030f0603080c010b030c0904030e010c032312060a0e0a0c050403050f030405090c030105090403081e010b19080420130204060e0406141f0e0901180c08070806040203 76
    0x20000b0344e1700c070382c11035510151a8912030181107083c2d04d0500c00d020303079075405016003844142c003407203168140c0ea10344030102c0c0c20005440282c034013442901080b00021195106240020f60070218034210303100c20717440c0c2c0034502d143d0083c00401403080d0300502881404000804000d100740c0d8020188101c0801c0d05188410200c95500a550003d0014812082c409015505c04401001501c000b40d421801c5941c4003124402c0b03600c002e20030706421003850800600441c4c4203044e43c0c1e0704600f4002500e00700e620b507200600c80041c4284c00414031407100181a07504c119210040b501c1e039101504103209545484e8039a0300c072148415200000f1031140e65070300c20541d699a040610b412281c6201107480b6a01d40e00028880310419141d030707024502d003050200e407141c205845a541c81300001e088182c6030301244403240c24444171002c000c0034402e0003503245050b9950350721801d01a0107044040002c08600c018100280e0729030403080c81c1030000400500082580c40122664000c4060320056920303182c80e1b504c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 756074001 1250 756072751 756072761
    0x105270c0f0d0b0301060509010308071511030403030b0a2310020f07030609060b04091515081509012322060c030504170301050d020d1704150207080c10030f 69
    0x402010781000400142140540c0e0103a82010810b50003084642e4480c018890140401e00010300342c03040070700c514000241e6410115250b048540004180c0079003443c654400344c0c200ba40d049011070344440d03103070f2100d040c4000c20000a0041001c080c410750701c900d00d403801e40c0c80188540ca00a0003002c402c03010060081118041400e222000c544e6986ea8a09040000300520841112000d0410f01200001e1a05001d090142500a50084010482121110f005000d000c0a01d440a50080b1001400d20403d002c0080078070885907100c2800e25108a40300c0c211208101c44900c4406606a220034401c0840c28895100d1410784021800d51101e442441d4501509034008103641c0c02e001200c260154590000c5010710700c0b03600035400c00b10020799102900c3c042401a113410218144040c8058540759072100c0106000e0203901900c240010b00c444815406138016425002100c1e03107881e4041d5040009400800112000d8240c019055000800d0000c0181080041682b00c001d030070181e0404c1c3d070007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 756075251 1250 756074001 756074017
    0x307092309040507061b02060a050703110f0c0f0d121b06061203020c0301060e13140604060b0a080c0a09090809102012040b0328140105270c 62
    0x180d841c1c5401c1c0341c896620f04060081030300086c02004c02071500ca080401031600325a00078800c0b03080812400c001c4600b034010704000e90400aa10600d010405030600181d007182803040013a2420120704c9082c03120705c0040042541c0144141028007005c0b6490325182030ba080302c51b1912812a414003000da07800d1032007406001e01045d00d044000990728410341c0c80803240310720035001e40300f000601008060803a200343c07050b0f10040e651480081c0d03034508003a0804031258891000d207540ca05000340c80a15100c5d08980850380561749120305030480ca048204540102000300091590b10108400704540d0780703c610988031542c0d15442c9120030400307002e06440603240050414443c0c1ca090000007482c0c1c03011203844005451034410500040d0030302103200301c640000110924540307483c240c0185440e0748010400072442d15010354075000c0307c0440310703111000c4201003800705a0000c1056240081c0c80103074400d5125980304030414002400540d000640400c4542c2c0102e425950410400014455115 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 756076501 1250 756075251 756075259
    0x90a0b010e01060f020d02060f0a0612110a0f0311010e01050910170c090916140d0204090515010c020d03031e150630020f030109050a0e0303070923 65
    0x40086a401d007841841d50499189965002c1415000740050780c44000d45100c19005030888000a25058080c42030705400401e10341d07000600b039554404d4011a4000c0c21030032140f9030504c60b5491000d1a224000f02c0241580b00c6032508800e24642d80d01460390f0710b90803128180145034024507101c1c0c1c0100e054810b0301d8400307060882e0307a5849800c014074890f03000b541c403540300031450003090b9601c50850603622a040043c04034549600c0d0000914440400c080e1020100300c41c0da0b0701240305c1c54200340074020301003190a0141e110350800c4000130650304001c044680141d48a02c03001042d0f039019180444040e0182c801568203409414128083c1603405800740701c2466401104200800710f030b01c00400c400300d05602211168440c542200d10034104c00105048411501d0680d45401843d9150b108242540000500c0c0c03045048512240307030000d921811007995144108410049240501148914110040d510f14a42044054040d20640c02610b240800c4482509140800c0c03540842c08400010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 756077751 1250 756076501 756076523
    0x2102040510030905010e0303090c12030d060e2505040302060327240618072a110d031b0f0206071218120b0720011b08010e010302040203090a 62
    0x794040c01419000504584561a01e00b0040c207400380401584e0040e0b50b210050103000c2d40c8001004011440300d080d0350400e010070894800b4411036071158100404150000a003d0310300484207a0207040c6840340003103030089224601c412964020202c4041d0303a8122412a1661a20403041d62840c401e1104626240e000320b075242c1500e0400a445050182040c1c80004e1200940a1000c150070080d103036103400221442903550820081500d96a0003003851070480c2c41d20080000b500740360030046102c48010480015100180185003c0c000301149040d41c92070070100c16a03800a254025003020007407041080d1410a04002140700d00303002c0143c0080c1010f44501044c100071480324440c29415022039150712607440600700f404213540855004881c0303064035203116110705e0440705008004104001d0600b0410380c84035a03800c540c080452001c400001c030000c2c138140d5100044030401145051210036001080041c1c91001003e05482e4140c50150710b03a128249090701e0070700c0100004004451007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 756079001 1250 756077751 756077779
    0x904051e07051305190b0703120c0c022e0302090307050a1d010602060106050304031b080c070906050607081c06180506030601050103090b07230a0302040f051021020405 74
    0x800302411001243c1c80a400e9690b0384c2d84100440b000c44107121000308031240307500b01700ca10343d002c0103030900b54000d0802808a4840c082010101ca980000c00404203000d13800250550400b041c45035140c645c075100c0091800c40c000104c0c1035210001e065101019000200543e450b10140055002840d0141c91500034031344445540c1c480d50038003020010403c0c111400010312601c00903c6a040f02d045440d06840c64035144c0701200c403810583e5843c075400b04c081d0302400000b540c1000520b4041858400752500070304000c03040054882d2540807910864041c40300c00042900b4208880351301c031610748039551440340034400c030010301480e511a141d402c404240c2d0300b5640b0300036045180304810440507510340340e0f01c03a0015000c40340541b1024080914104c00100035a008039005244a08dc1003490318021000721003442e680d0340408000c900080e00031400f0084420300d40c52400113840c00711241e840010045000400c01d400ba00c0010070721088001020032004074950407100030b4100030f403140c0c03288404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 756080251 1250 756079001 756079007
    0x60305090c030102030609010e040215031510030b060a08090f0109080a02160b0d0c0905270117060723040609050306130506060d021801090b03120f0904051e07 70
    0x81200d50341800d018a019145aa24061007124425240104040740c0c2e642026003201748020014003c0340c100c41007000e055408007010300a907100710070a200c011b5000c407110051240301c600c49034008042c1030a10305100070b903540d4001554121001441c1c43e50f09070756a8600c803131510003290300c408190351038a040003003403041c650000c003c02c000c40d40803500c1c0c3c5400c424402c1c5400c101403084e82c0044000703000442c03080b0810780085d4020342103450002d040c00e44840c00a591540c0012801c1c04500030140303118800044d41100b00d006020258200703103815a40302c0d4550312064000c0c849810811032610782c4c0c1851040181000c0080b41d010307011925583c4034030300601881c1c11401914841d1103030000040c0306614002c1040e407600e50080252045485d40c009000303a842c0412012a07108110492440e094400651a140209050300c00442c4801d08082410304204450f0748008288004101c41e5481640c000111780ba407500903a0001006d54400070a00c0c0082d040c0c2c05030180c1e010a400600c81380303e0b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 756081501 1250 756080251 756080261
    0x20f0a0f0302030609032a0a1209090c0c0f0605040c0e071706120a02092a1b0f19020d06050f06150703090506090604081f0c05271201060603 62
    0x4400c3c2c0807104140c032141c40941e40c1b405803020100d119484140c0b0030384428801c603840180f1204900883c3ca00c4211541c0700d0006100d846d4070840043d0b00c104d010040200c1c1400707100b5641d42d41e070401c21740c2ca80d078031b858a1500c129161400390105450b80d001c10100108540c0000050a8000007421207003003611000340b440f01c00c0d00c0e209610144042c04070b22903150807200342b8030b4440180300800040d1520342c280b05408000074001c00d0b00041c000368030501c1181c0307000307034030a82c800041403241d440180c066400c0e8140b100c81c200224960050806c440207540010705003501640e11061005a0a4188005004101d0184006000b80c0c105020300c507100c98521001801204121514400e5192100d0802514040c180002d000910304090400031820411b008094002c4094155031501da1542d560501d0110020b1004001e40b52040410032007103a6071040d06e02e4240c3c603103002d510b080c0b0b9141c0c0e0242425200e80040c0d840f00b40004c0180c4841d0f941488503141601e14030002d2100756903850018000b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 756082751 1250 756081501 756081503
    0x50601091a100507020d08090406030c08120702130911060f1207050a0c0311070b07080406030513080307050c150711062d0405031c02030105040b0d11010507020f0a0f03 74
    0x103032405002101d6107000b030102c1d00e1448560707030b600e4109034064082000c0c42c120843e0a44004500300108405901c8a0050001860080d4038282031580b81c0f00d0f28519001c01c61403000d02c1044240140d00040ea0340f01c00007054140701c40e101048003003d0b41010700c130b2550105440742d4400c0300007514402c0e20b505000604045501041092465910410b040e150351250fa0a41c40019421031802c0000a019413407500460b4000c03011244821b880e0005245580d10900e025503e56001103020080a40d05010381035000035900d84180070920103544240181c000903006009000011803145d030a0305e020042000c94004604142030a1b041800d4040d05c046101a29404103000c1d143c000f9094090003d007225038100c2e1071078407016449071b0030404140c6540203001114140000c22203003200c041d003003440004c005260100140d80e0352402082004446505c403495014142e001300841c04203800381902c400950003806c03d1a0382e110244001100400102c003011f510508400d004a0110f288070410801e503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 756084001 1250 756082751 756082781
    0x7051b010903350c160b0c0301082a040f0f090813090e030711010c05010e060f090c01020c1003090212061f0e060d0201120f0f1505010503060f0d05060109 68
    0x180ea020f0124942010022000b001402144000b1440c03400c131070801000070b040d40010074410703100203946180840c007095824000100c0d0200050280d814240101c202100c8400680744442d8032000d40d62090b403013011201c0d88070f50741c2c94440104003051740d0000404410000801c0116004074a003404643c1c00805c00444003081007a40803c1c03003400b80c800d60000c55001c00003141040c0841e980c0c0d00202a00e0041c803030400070b004611100098090042c424100c4050300a0f144a1501a00300c0850304801010660030758088401d280701a600815900e0003079400f91840c8a807031401d080203401030309002c44006d4200711403000700348030603a021500318050005034140040c007501c03182c100c54980b582402001140c401d94030114070503142c03004c9e60858480c818144a600102078666290494004071200741240f900c0341120010005180301740d028039040c030301c17400041c40d041c04002403982c00020700650040014800c400c016a403840c103c403414981c0081195459a1150020005000d11025001c0c1d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 756085251 1250 756084001 756084047
    0x908010506010212030a0b0a0e0405030a1e0c1b0519180506031902011b060c020606091504020d0e070803120606030403080a02070204090c0b0c070902030f07051b010903 74
    0x766101003881000c18440341203480c00d41d01c5042001008100c42c038002e80d801240c02c2400540c010314001c5407441107010700c1c043c0d91100c61500018002c066142041040c50402d1174000780d1035030300090002e43c1c40e50071900091400510303410789012503882d90055a8881c884101d140c00da004500083c1d000c1e2000c40760742d040040041018036098400230703a58030707034180c000e05241002c0907202220803144034014900005c82683c0d07415011100701306004186c580b40c0e01d4505200c0c901c0d40401c24a600400182c0700c0034528600564175080c80c2005a56091044d600020301103140c49141e00030700a04414641a1040290f55130072a59990784412038007644891101d001070110b280c90070a9a21641d050388596a1035640c00d9003620007517120283c1268865520709500002c43c81d05440c100c00b918900c81d1031540c1c2c400d1003010707074640070455000815050041040010700030b451885580c0116440c100f460700c80ea404101c070800b08000302c128551540c6000d1003401407507030080d0a402403220320504003903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 756086501 1250 756085251 756085261
    0xc0e10060306120203030901120b0604030b220209130c1e051009080d051b070e07020f0c0d08030405030d050a02030411040903090314010f14160f0c061a1009080105 72
    0xc8202c400043c040d516800501c14520b880d4003411b048003101142840000302e5420210004926030032a0300113980140340a02040401c50300b928000720f0400c110b40c9841d4244081d54006007070800000e08a001c41503400d0703603580070810501075240203420081807000c0d402100d103807458042c5d1070901c01c8500c58400980d40c18002402919200c0903034003c40041c2ca00c1698481041e942c55100303440c18044103000410380700e00e4640038407a81d00648110103400300c89040c00c000003440c040403141c03440c103103421000380a6940c3e179489807040ba00b184d20040258907907a03181032040c00d501480c40c0703c460755810481001090100396004602c81c51040c0101c4840d00c200b002804100d41c06154000c0200740059400d00c00b007408072100711035101c603400001c240d440c1d004c1d0142007592171000d0310b02c2701e03800c0c00810b10051191411004014102d285003850181c41c10a400606515909502030129581c40402031804603802c5404555000003604403c28054002402031600c0800d05c20803000394a4000825 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 756087751 1250 756086501 756086519
    0x181e06040b0c1c0b0a210203070614030a05040206160501090302120a1704060f090f020f0d21030f0c020f07140a030303021b120c0c09060105030705070c0e10060306 72
    0x5590522440c2e480750040f070f8105400f400034542050300503442044608000780e910340161342c0400b0b201c200f903c0500d441201f44113051512402e600b241007842403101035261201000f606403540700400c0000442e907600c907030020030170034480c5c84c8022540040740d25021081c072405403c8238190a1084c2e088a54041d0482e9441806001d007800a80004514500c0c0350410300648240c1508140100000190b00341000220800c584c0c04c040100c0d5890098000b4106514012103140c920200680320000014025900d408400516606418050030000c43e15401d6510a80c800d503924600f001d030401c0940001d11010307507131b01682d425114052082080100b0044c2100c00101c8c806100900f0f003001e40317411541d041d40a0740000c48a829400e0304000c990528000401c00c0729046c44444950326079562030341140509101d0440d0320345003e0b10b6070f00f06200c59039900108070f0780e00130030f20324085840d4a0755117000380702c003c100ea02001c02d142134042484a001e0901d0342d44800c90302252000c03c40c0320380d121100c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 756089001 1250 756087751 756087757
    0x9030702010f0e03070e07020c01140405060a08150402030c0d1d0d0c03030222082e0908090307060302030601020c0d05071e0b0703051306020c09181e06040b0c 70
    0xa0010b00500c4500d11a240102162400e00d00b0040c02d840004d5150780c000d80c6144822078168005900880410f07106503008143c1c605038100407440c0c6440d003420100800d860b4824041d07014200400040001e00031030b440080d05000b60700081041d50b0b281031041c8a54229002408031540307890ae040880b480744903041c0c400041c0c41c0800e10150925510040b410740d9892400d07003045d000d1507003c00840d4520203824100700115a2214901054141442562880c004d003041c01840040c1d1081c03000c82c0c0e108104804901c62100c410700118a0103070629211409004150289400d4803c1040c003142c02505030300614130450081e400c40b69414520b00800c9040400c0180281240d08240c00070b00400070101e5030410950302e10518030302c5040da0b400d81c0121a0b8403050007035001503c04140c0500c20048048803270010321151004280070585c080000c0c0e805100070301000f42e1512407110b088500d1900740a0000e51001289840704075400101c40300e91110000c64007104c0c079451304000a52004040e0b0b0503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 756090251 1250 756089001 756089003
    0x12030905060612010b06030f0708010b070804140d02120a021903020f060a030b10080115090b1b10090807061506120b011b20010203030105060702190306060f0e090307 73
    0x901c0141c85007002d010103011460a4400955228610b145c030613280c1c80c0095010340700e258214170003442c2c01c9000070030011040e00120b2404e6003c00c69440071070b42500989090b15482c81c44dc0c1d805400c1c400000e1003000c0d070110000e4210002d502c901081c24000300b840700071580250340e0640c10b03600d2032081c1a480681408001d5002040c10700e8a00d490400344050501c58000c0e040000f451224400000c440d291520001000075194800502440c07a0112241581100e50300f049100d450400d1801040c030f0041090001c2004405034400000c00d1040004150302e131449a07042003c51005c0c102803c8561085005a40311401c0c8100c5005602120000c1001c07160b07940c2d100c01c4800f0288901c01d01811505401c181000501440d00440303403542420400c000e403091110882c01c41692480d5401456800d03032b0141590402c2c401000305071101011504200c0d411241c0742684a40640300960087c01600058555443c0c01c0c80412003800d585000030030348900d40c2030250aaa40c010450b0382e24410000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 756091501 1250 756090251 756090253
    0x110d020703030c080c01022d2107090b040f05211905101815151719050a030801080a1106030a020c0d0e10083105031612030905 56
    0x500704040b91250301c08610752403046510624100329017400c4d5085e6000310501031808403220b41c00240310480401c03070a00f881076500d42c0c3c1c1d003840c001007800c03016104814466494000b21100240815204140090207050401523154446440e400c81300c85656403409403e01400e14507041c0010545946149912181c1030401080422010304a03000e6090b8548002c44061140e800305086038084c0d4000c038010080c40e42a4018005024244045013516070504218031700d1030030303038011039806954602d0300c04d41da9074201e5000b0407200490b206160029042400076021414a50300c42086008214000007500030f6481d1525643c985038010340318a00702200812004170007015081d2030038580040d6030700c07034030002005060507003007081d140c107090200c02d0000014650305240083ca00e807a21032a400c003e0146040f15541c50715a10784d00d1501e00c440325a2903200103041cac00444d8400080c03141c400013035100b019261141a0b950040c03c8041c0c1991040303135009051596000c1e400e129110303d404054201c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 756092751 1250 756091501 756091513
    0x1c0b012c06070201090e070c03170907140105070b090d030e060903041a040302130626060414010e03071b06050903100e12070f02090117101509090303020307110d02 72
    0x88100203995124030b204a060104240300020b40c0035403248043d104040707a40300d078071311540070f880d004284030740e5020000c119002d03a40174803801030301c0061490700395101440b400d41104407a00041e82c082c0200030b001000b0800010401040030000b05181c18081c8c2c2c240c40c10310000001051894817000c0c1250240090350041c00100103a95602801492400600003101e180c56201d03000b08a00c40054140308a4098075401c04000b5080400c801d1005401103080c059040703204001e8541c2c88050250029082c4020b14804c154000000c0d031103002507030ba01900302c941d101301501d010702c00e4007207801000000c415203142c005030403806a4200c80c5401c070010090f0a2107550142c07400010221881142c810b0300c03030100400303802004c4200400301240203401e601051001441006500703c0160041500d07040038035480480303108001843c103083e0038204404650300505030180702c1c03811110b92010380a13504110404080c19050f90040d4060b07c99a80d50032490b50304c9065050303944620005d1140142d00c10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 756094001 1250 756092751 756092837
    0xf130b0c04090509062a120405070504140f0a060b04180b06030c0c062a030c120403030603031e090b280503010806180303130303021c0b01 61
    0x12440a50100d040030100d4105521142010215078003203c8013072690b48800b090005401d0300724820f8000302400d6984070b024800406e40d0807114090b9a0364154a081030001003010840c00340500f1024080281040183c020840718400d00c60784c3c1520000401148080494020041e900540003500c444010580c6030610300301c5020aa600d172070001c400e03201d50740e189868050380c50000175805010358621540c1c941180c0303200241490b4010f081150005001d003081500d20807101508003d0920101a50f80c03207035940c00039040d0500c030f40b500d08031003d00500204030405030194062001c0d6402655150303d4660003804107003642e8000702c54600446d03000c0d642042001800343c020120041d40c10307c0b800841d0089000c5000709614017007504e0100b43d011005110600c0100a0741d0340c06000d000d0201d03d6a00030034403058880c0b0010701074078011200302d9048418540287c040b990142e003002400701000000c0840d24005181c0090707218000780344540448040c2e242d60a0220800c01d00300f801403211051 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 756095251 1250 756094001 756094013
    0x518032d0c1c05011d030a0324090b0d050a0b15180a0506150705011407180e040c0e0a0c1d01092d0806070f0302400303030b090f13 58
    0x2c140c0d040300c4541d00c4914800b51440100810136421804000841d2101c040c0071019068815480707c21340d58901002c01180c440e11800805c4080700c084c8080010150340e03481c041484082c40940140203486803d80b500f04012030001105e21408894007446800d540c40030801c0010100c50000c1d140c0d1b0b010b00b0020807581001036005a400030001426011414102c0041c07103450342100906440c10f9544140742114403614072081c0383c1c0980c0031328216000d492000d45d54030325813015001c2d1200c480c80d00c41c0000e0422400c00a01c5024142c2858104018500a20311102130404101c0c4200000c0494581c00f03034440c86060100030407081610303603610581c1821032082034400303604030607949105605120000b10040e42c0f80391029201c51000350a003481c0c498401361088840760580000c05204102800c030035201424203445021181e45044080140d040074445400d0450000041d625410b410000070581c0580c0324100a81095401505a0752401e10a20760003031308440007001110400c0d022800201 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 756096501 1250 756095251 756095299
    0x501170603150c0d060806040c0905040c09021e04080d020f0d120b0a090504030c030806030c1f09080f1501050405010f121b06030507020c0904080405010518032d0c 72
    0x140c00c0740c060034065a0981c1109039240b40d8846d4446810200501051000e4030146001401e18120144141e00b0950303a10200a41355203d400300075540401d080e00794242c40ba2507821801c2c1c25039921a200c0703858807107064690491040b41c074007500c142da105102420001c00c101c030556030141c40e0005071190030070b805400740c00c0a940c00d5510499401000c0759440b514422180107074001e03a200d0b00c400600749400b0b400301c40045c0505100f58007190204c6906d5940800b00350000c0c8417602003400c0d05801c19400e5480760400e42050819000e10440c541d02006d000954a01450812890108999031602480102d60080c090441b00b40c52446080c0520001d40c3c0e40440301c584504007060f07080000701d80400710811140c21040c00640c8450602c01c540c0d0b070412a20316064400c41d1413804904080d44d411140d03204601c074050500c40e001c5180c58503110410480944507602030196590f0b0a01030041011803000081121352014544510340f490b030000107800484600080c000f036090600701255035a40d85 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 756097751 1250 756096501 756096511
    0x160509150a09020409060821090f030c0307181404050a11130204090609050f070f0f0c0602030a1b02030c030f03040f020d0c05030c01020114011e170601050117060315 73
    0x2890740c24002400e0b0040384000e10051603d985c00061550030161500c2c10110f001000140445110780500801c18410b022640031800482da8a00c0c4066404007280c101645046503d0385401007003000500c001c0d0f01c40c80c0c1c5d1000001c440c03003000b800c041d00b03442d0b040c4207406a4001e09564002c04500d00040e2026081001d80c40d0018445284150340c004c006050381c0c4030703030450141c09846e0841000100914020160032800b130420604c1d2524101d070005241c02e240210050403c07c0407448200550300800c1c0200364a5080b0070103640e00c2c0b814514800150400c043c03046407007404d4001102d8002c0c404000d8901504c291006146890017000c00c0104a81014100b5030f5082ca2250f103410040e607401c0c3c015902139110b010000c07055817a040401d421b00d200c0b4011721303040d039042c011001280c0501d007104a041d00c941d40d0345c594903003042c501c1500c5c2c40b00c001e030000b07064000c0c10402840d038003d0008041d81250700c01d0780c43c44440c00714440592100d100a03556282c040e44000f054060f40210208956480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 756099001 1250 756097751 756097759
    0xc12070e04031e051c1a040908040b16120203040602060c0309010f0608010b0301050a060f2114160503030f121e07230c07030209040609121116050915 66
    0x700c042c4450f151406001100e801244000510081d6420110514203400303034054010000d05522100307101c041890400c00078400d03035481c245401084800c0060310b01500e2070360310b401d48a001410100c048402c0120f0305560100c0444030860800344000221000e8800303030f501034105a01c43c0d00a1503d10f80001e80100c507a9522401102104421881124020020b4030b0010441065403024142102d41c090861000f1509140781400441c0300c801010049981101d0542d008502003191181c8a02d050705000b840307596403c44400e511140061018881d4045007005d20a50380d03240c0416540c0d20424404400c00303007041c0044100d0b818503942e81035200b0004556054440030110499503040c00413504e020100d1189105140710704c2107400000e50014082c403c0309e1410301c143ca0066603a10300e40c03000034442d52070300e400941040640c0d082040c101c2c4c1d001c0540b03d030391001d07484041c1030759244080c2d00019114505451641d01c100700084001ca83c005052101c135520340000c80c2543d01244500706402c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 756100251 1250 756099001 756099017
    0x240902090f12070302031c111b151c020306100206040c0909110301050f1504022514030a020c09060405060a0e06012304030632180a0b07020c12070e0403 67
    0x9a2000d12968071104840c002d07d40600e01c65450142c5094203078400001642e00030780d00380311028440f44017440040c4003112080c2105184c9000d9240922461200034081c5254440384880c40050382c02550080e04121a03515140c6e1580000702d0751910200c070040e00c0441d00d0380c0200b00c007a845612981c07815000d40356486a40040c1c001103070035034800b501c101501c00e0850081000711035646146140544d0201c90a5203041c41070090107143c503c80030b84400300100100200c070100716802444010741c440e450700743c80e111146488040e40300e01101d000180601e003140300048251610307105291080c80014403d100060406158045241c0001c1016041c4081018891030aa45144034140003161180d080380c0d40c1e5045240070f0040d03650f0409250050000c122a10491440610801e4444840c0104010881c1d50b200380e991540428501da05c00035028071507091040c00160000144104800d07000c5401c4050610b00344002c021a104891000750001f4a007032000714005140b650b00b107406442d00807d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 756101501 1250 756100251 756100253
    0x80708090a030818090c040303020a0b060a12120806041803030e161e0e041e020303090a08030d1a0604060503090705030d08070305010b09060f0901030f240902090f120703 75
    0x41c4030342c0a40082e1281d1820018003600510f017034900507500500055001c2e050500d15038020350f48001010009159107180320000e4110740340c40b001c4400410403141106607000a9050405001194007460b100041c0d4400004249051500544065610418402400d07251070340303086008140f0280790b01818084d04903500055887c5203d02d10240840c1d10b00f40d40d205941800c08a0400b080e580700e00605904c0c0c50800c00400c01707030800000240400e221f105000b0b041131000070b0840c85a5444150712035180320011490340740001c081c1050444031141000052000001110080814084a51b100b0006c020601000e403051002e107800502d10030407104400d8032180000d0900f405800c1c4000050f2224040000d2241d05006032801450304541d44ca10707001c02c02000c600c80b0302c1644088008c2140020342074507030f64460362107101080e02c1d46104119000f41641c000c000364411883c180140b02c0714000c045941c070050b108031039403020021b0201078816110814044010403101c1c004880d4000d903a8000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 756102751 1250 756101501 756101513
    0x602120a030f0b06191101090206041a040b0301030809040b0a080d03200301060215070c02010e150c0f010605040b031605010c0c08070b030f010608090c0915120318010804080708090a03 81
    0x242c1c0200e011071171140020401340203012942e1800b1400d1241e040c901c81c02d01503102e0108880a0350068000d224000200302d0842c0e030b162080e6403000c000c0e40c1000000109101860b8086d000040040350f0500240742c9110401c1103800840c01480344036081420b20304010307802580080c0e240100c6000315601c1c030310340c034005c60039030707002603102e4000340e040303a2001201c1a03240d1184990100803405c2c2400c414042c0d800003800d001c40510602d0050f2144920a40a04605000c1d07503840010441101e00320b5554212050103480382d4820b541c015814034265698a00d4042040b400e07080c403a2021841d02c0c2c0c07500c40119444c81240d0401ea5a0a0b00440c01144030f10307090209001414035581042d0790703801c0603a41803484a1059021900304090901480004900811804001442154200d01649581440300c6042000c2840d80e5805251003a401414900c08005080040c0620260900180055005486403102154003e083c000d0400c048030009480c88054966101c01804088501c0d40b20f80d991 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 756104001 1250 756102751 756102757
    0x2031302060f07020a060c0b0109020a0c050604050d0206100b0306040b06040b0f03041a0606070f080c070e0405060106050301060c140304180b0306101412190f06060602120a030f0b06 80
    0x111070b02050000743c070415420440000c0c002400b0610b030902c030f0f101554880e000c520307906010b900c0300c0720340004081e10540d20441e118064142c106c0259940c0303040c0380c81c0840c1e940e90055262409405880000f17102841e4071180c100403a14600707403031455a96204c0c1000010100740e00680d034040410303c00410501c602002070141d0b0b86001c01c220743d4070304007420500c180359050444407440c601e8580130071aa5480782403d43d0300302944519203055281e4a444c3c0130740755015101150541340b048001c0028902525000c40c4e00460080050b540d050f6247d540840c0c55100074041d11000c14040e01c00000001c459507207407902861400b003a42e0600e46c8038580103060703100140600400750b03140e036100a241d1800b8401140c020103c1c04852140d2460221040c260100900d40c803031080d121100700f04517026040c003400c031510341c4100c0c0005003c042494403050181400e9400d0382c1c4507140081c00716802d4000568116140f0484800906103010200c0c2140030b0015460b8080c50710381c44540f512103903202c0d8005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 756105251 1250 756104001 756104017
    0x8060607060608070e0a06060c1e02040507020304140d03140d0e10020a270501050c010b1008040c06170f0901140408041d0c03060d0309031208150607020901090203130206 75
    0x5400c2c3c0ba49060030b9142501701c0507001d103000d00e10f4202e08000391760704500100301c21a030240605a9800c1200e00900d4002c0984c18043d41041c2031070100015150302000400c240e4081c4500b4a001051900c140810a10010801404290300300c3c24072400e4007913000900400340035003802041c10781c0881c0c2020700f40512090345440d000e40100e01c80751200d8101034a50707500c6420382c11030102820426058000701c8410301c034180c14040300003801101d40381300b9049007903500805003c402e552034090200404281d800c1741d05450180c40000d02248982c82508009480140550b400b11a0380307880a401d4125070014001e0a09590380d140503804040ca890310aa21540c041c0107801d4aa5150072003003401d41c0902491440c0b244d00c80400c001a002c0002d05594200d9800c2d6505100d101d0705150640f05a03815400103031017108000c0c18101c02990140e5190b10600d0402c109640c113030901014003030380d03000d0b885000b03501003000801405000c046038084c1d07920812481c1541810030413900821195481004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 756106501 1250 756105251 756105253
    0x1c0b030a080a0903020f040e070608061c0507030309120308011a09030604030e1009230103111b070f140d02041806020c060c0307050406080a0605130b0f1f08060607060608 75
    0x14081085d80b8102a05050415041d40c042c8084034000d1415038417120903026080034055004007040068641401c3e1854480b041c440158040750383d03040c1695510540d21007100020b0310a80301062802c0300c4c1400d4481241d040d1202081030b42444100c0b91001810340da070700e0443c1418042101656810060240294025101d1244c2c401000c42030156800d521b0a059060261002040100019074600c451020380d03031401252404660381c00480c0071b0480c2161001402c00042801040d8031031241d070030b0100039640d00c02c48040d180d0300c4004014007442803003202010658102030000d10b042c120b500d600d000384000e10008068a11050700c00c00100a02c0c2e0035510a980450380341550304c0104026504100451541c41c19454540c0f8010064402d9005040c20088a00c01148a00701c45400074805080001d0035090201d285042c0300380144900c4040c0e17442086a0401e188003070070a0300810704403203940b206628042c10711420a50368007101401e0b00360051820090b007804a0214881c0b140a802040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 756107751 1250 756106501 756106517
    0x3120c240b040c02300406090807050d03050f070609021507051b100f0302120c0702101812080c010f020304140606010503040303050c090d050f10021c0b030a080a 71
    0xd5140080350700010090b07028600d0032200c2503c036038001580520404070030400e210640c06a10703400120150005a04510358008100410440e41254500050303840340c0084502071503031801000610701551201401180007040101e4403000c809008100d1180141000704045803550301180f102405600c1c2a0400b29000c180d92042180c24402c50f0f0f40c11081401414100b0000000195820b40751800a414000010010156107010741c040e1040301180c41c1c201c014a252501301039139107a2290380120b209104030000717000018068025524004400c802426a40d401c04515000040b0030324402c0d19808014800b003502e12209011300100c200040d140540c5030300f070602e0a00c0a034020000450003a4000004001540c0d030701405891f40b250b010b1a0110347c503110a14450f81520030060340c183c11800c2e4100550500400080b8414540d800e64201c079050b43c0c0c00300502c4100d0140c0844030f820040e0f5241c0c031121b03c041e6500568050310b070007002d6914101c05603448440652049282d407021680003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 756109001 1250 756107751 756107813
    0xd052d10050d080306010503090a0b07020a031205070801060e041107060f0c0f0e130603050607020f06150310150b0d060807060e010e0d050708030f04052803120c 71
    0x14000c44402000305560240d041d80e11965400200d001c004c01031410881e0100010304096002c014101c0c400d604010a0703d254100124001e45171f42c551202500420041020008281c003a07200d8944644030b5682c516003d41d09040d803c44003100c812000c958015210000c0502792004080182400b500c00c0d200000c61a00080398801a1203d9541ca541070054036514404c1058000c0a1214220000c6171142d855003191801e0300c004100c40e81005e007261080f002080199600019810500800e8900301c0b100f603540c888000981e035808420f2650141c004000120401701c0a40010302080c6280021040d00d64503034888040366000440b048241a454810400c45804144481c01c050003461400c000d40c085c0c0100044e1614000311413460080325041c40d4001031100034403500e00608072040640c1d0361003411511011564109000d0349100d00102d11050f010b010103040c80c00343da4009810300518541c51500c4034190041100071b03000038408145480f90018880d000d00005841c10f0b00c4030359aa444030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 756110251 1250 756109001 756109021
    0x13110a02071a0c0a03030e1c0302070605060f181503030309100c02010c05031503070b0d06090b060c070b031b040b030a14100b0906070503031024050d052d 68
    0x440802c05a0742c000c01c21000100e03102c0820190754403a01414045040311442038040d140084041c801511791040e15065500d40c0d40c1600140071850003200c0622540d03d419013000074400300756566560148141d4040d200e403001000245502c841c138400213102014250012030b0070f5900484682e2041c0c2c02903000c8a00c103402c01d109906242070350340b000300040306030894054120f2001400a00c1c0007903002249003840ea408016082c0a41214980317151200d0114034400084d02540c0190082a424a1401c49131814440103076041160400d00a0800c14034240c4241c0540d440a4085040c0c18428580c1781d1804110000a000610401c05070958902d855402c020440703961540c100e003c2c040340400c1c0001d410320301e40705d00d0607511081510742d0348000e101d0001d0b4640c0f06e100c400815500000c0100002940d5845403542110019084045d9448a82c0320174210710010200440c00720b8800e01044641880b241e00c8a0340c0400116440da15908400d990941d02000590006848003552070401680c1c0c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 756111501 1250 756110251 756110279
    0x513060e2505030609062b0b060301140f042d0b070306081c05030c040302041e142a040915170a0807110a050a0609081b09040213110a0207 61
    0x290750318006003507042c2540024103c14025010511030014040142100c0490562500c21510f00e01c001141c03e40381da18001d91103600880e40c0380e01c1b070351800c001c4542c0b040c06030480903c50825040c0000c1241da496031040e03c50320a080400b002c1070880c40507001d041d40b0040014154500419103054503240281008042e14421303004070013039401c82408140302d01c01854203807a40d4200c9081c80c680741c0e43c0d030000c586417034080e5500103544142420300810f4000b01014514003d02c03a070350401d1001c240e40707085624408034142e0b001d00c0503504c80102484807c10449000074180c182c509002d207019624090041038a044500080079205400020440c10030341c284e01c4620402050040c02483c04140c84a101d10f006402010781001241c0c281c100040c0e035460400c034082c3c400144055250303034650030300810710a07050081c41c00c50301c00c1c450341e03c0140507242c0d9031110303001c0700400440300c5a44581c244146140b02c0154001d40588070350340542c55003001809402c0311410384d80109101c1c1e283c81403808a100d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 756112751 1250 756111501 756111571
    0x90303090c0f06191202071109060d0c14010933020d0203180a0b0f1306090f05040e0f030a0c02010210050405070b03071403010b09180601090513060e 66
    0xb11061507a4200340c0311241075030b41c0c0d468401812810141d401005840c413041070301404800130310001d44001007112011a583c207441d030070388045d001a81c0390710500246035010392028001c21a10001040440c0d652a5620b98001041c5400266596110300e504800100385549044001c130100c00c1c8060050b440108801c0442188000c1c804030034003c801070744a201c1d0168103644502d81d140054003503102d9018180040c421002000d075200c1412486038940d80200515410816440f0744c0064020710540101c1c017510342d011000c4249918020801004040741150140c80c0c1c06298102c400c40401130020701840f1140e0340b039000c40304840348002400d140c1da01c040a08064a080c00707000106100007122426100414810350360398480c0801680c810076400d84506158900000218205003240050b021034441070300c00181d0704150011042d81031008031070701c0b0b0028103501010408d80c07038403c0c0c1c0c20030004035641d000a001610b441c0c45602030320046600c20280e146040c06040ca0b02600d1243e01070f21 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 756114001 1250 756112751 756112759
    0x10c2901230108060f040f09021c2312031e010f14060f030f0618010315050109020901020c09100b0301090e0606030d0e2218030201110c06010308180603090303090c 72
    0x51324003640010b0001c071044c1c940900a5948003c41c800745ca14960200512a4005000c17101103007545031314621051040e030007251155452a2241d100550b0301040d00e240c41900c3e070203480d41903000d20707400c0c3c0d9903003008007071440046003500d4003c01543d03c2c03600c05000e010801c04130003c0e5414848081000c0d900c180140e402103108208074400c444901d000c1c0c2e500200035040c00581034031000005000d032020450b034000c1c0b66420900000400110420980c0740c100c5001052201c0e0782c0c2e444d150301c12070055200144c0960400350961f8210701e040d04030790707034410401004000c62689408944040c1d4000742c0113a5109036a0b000110001c2d2420800d0542c4207001300e0060070700e00703540c0e500204940607262803207008041050b59202d411400781103101a05210000400140320a001e4851200c014009c0940255181c40307181c051054401c1d040712100207540004000d141d286030703102c078115800301b17103143c50b02e510464a0310040c0d03503103900450042d02d03403900541d01c80c1050341e1400d0500b00c1c1801b03a04d105e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 756115107 1106 756114001 756114017
    0x903060c03110c01020322030818011b0314060405060a09050a0225170a051b0705060309030d0614010e130f0e0a031805010c29012301 59
    0x204414500d59a07058091000036003d07d9800300381c015000070fa208001601b15810065000d1522541070000200c07074402c0700b800340855840b00c44540000b80c5915964140400014100b074014500300e4042160781403910002c0e014000c5445810310450310b900004d0040b0255505417005520124074190b10005c181d0322040040248800c12654040c41d1400040a400d008041d1407644100c0c2c1c680a10b404504040e04101c900030384100c0803107115030701d40171a090302e8450213507000b501703544003c58403401034458010641d2036a8000101c2040840140012a81e004104280743d5900303a481c04d010411049040c0301a204002c00344071100d0400329250128940003511018aa00075900e010050850a00040007180305200d654005103166084034041490f03d0543c10040085002c4138160f601c003000020340c0d083c0d00764410b2058005100018958101003284d03081c68603024070304415 = true := by decide +kernel

theorem cover : BRFrame.Cov 755935251 756115107 := by
  have h0 := BRFrame.cov_init 755935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 755935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 755935251 ≤ n) (h2 : n < 756115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
