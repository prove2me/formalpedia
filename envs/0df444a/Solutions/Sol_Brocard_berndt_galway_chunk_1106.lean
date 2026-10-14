-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1106
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:16:02.731419+00:00
-- url     : https://prove2.me/submissions/9046e419-97e6-4bc5-a814-63b0935b8381

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 198741007 ≤ n < 198920863 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 198742257 1250 198741007 198741013
    0x1b05090a090b0924090f07270623010210020d0203011d0103080f0307020304050a060f0201110301050a030201110a1a090c0406030c090213030b0705040612020309070512010f1a03010f060503 83
    0x44d42203518510149580924104111040c000b4148501801c0c90030310380c00516604050003d42c5800404001c0c8030072052140d500410881d0710302813200003241d4135130010302e42c00c0d04d02c2461500d41ea40300b0300806540742d5003013009540c0c442c0800203a80095100b4803501440d8030b04070204102410302010740c5412039401600c420f00380b280b0003580010513030020304040151311042000003815103801c500f14005080a8075124400000396401034295210900b0310220390a0420051140795038000f5040c0a494080c64080030040c40d4410481c80c101620700081c0070803562603103201c801902d141c2036038492041e00b03042c3c03102602c1030b405210658116000061001d00d0041060000c02e038180e0141542034001203041c5011a40c03a11000320911081d10180002000082e0510a854000d02400800f00840304210315503d88400c04688030f51060041034070810403000e000003494002d4102c0300c01c82e000140f00304051a482c0c541020460084240b5601035403c010446d40148040d00c20181120300c0500a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 198743507 1250 198742257 198742303
    0xc02030609190b09071806030b0928080f1602100f090603050c270f030c10030915020a020706030f051506090a1e06030e060103050a1b05090a090b09 65
    0x62403011100c0188001383c039114903000040c01101280d00358891070042000040c3c03250450400c1d80301c01070024449000c90b4002e000c03090500009a03900000d03981e138202c0c91f61083c011460584030a00c034030407285030344160204840a0380300a84000c00d00d03042c42101c8c0176020060328032054400d600c4450040c0301050b120941084254065007026a000c0355800f500c51605001c3c10746201214407500c0c0400900220460181c0c2c40e08190514910181c401c40081010300804400103105481c402d4081d000c00d6100c1007680200080798482564805040c10b083d1b4503001c3c12000250303190314a00c5180c1c00242000a0307035020400310b01c0741c14002c25540c50203c101003c0b610a009142d4800c070950340e003000e07211800090303c0d8100c00c03020315201c1d48425150325240c038024000f8159206c40c1180c680c29001140108001400081e4800d03109034441044180c0000e161113282c82e4009552246401291420401000c01a182e0011003a00c2c07044018142940710100f0503035594000000f4a1120504520 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 198744757 1250 198743507 198743513
    0x21e06030a020415090b030a1104080d020a0b090703150e0102090d0602090103050a0207050c011d060d05040b0a05070504060c021c0f0209010b180405150a0605120a020a050a0516050d0c0203060919 86
    0x12807540c601270520a481c1c07954400d0354501e088415200c94005030440c5046800b0040321103046504107050b68002c2c81001d065450b4500580d24440040000b0f0780e40ba051640701000a405a07440302c180101200c40c415440c0c2001d00107580440d181e10300180c45e04000a40b1041c1c50700c01e99201d5a00302c802451729120110040d240c264450540c3c4502c2c90458100c90307800d07500c1720000c01c1c00d80640d02d001f0032503090030310b400c501691003d44241c0c100b03802d00c020040d0465000c800c1e207049481c5443c0c404001102400800d40500400901d9a40448414400d6084c40a1100520031880c400c0d141551903a9960074101e42d075018142d6911200300342c6244075407491410360403841c0c100c81010051500655408001580003005074030803408102d0115881c0b100c45e03004c42c03455501c0f58207040f0540c40c021404000601c18800e050640c4240400419800031040d04100750341601d070381c044211181003208541c00342104851880480c8070f032040b00b000501d0342001054003103110300344400c12000d00e0350960f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 198746007 1250 198744757 198744761
    0x1104050f0a0f0803180d020102060708100f0603020c21030606090a090f1b030b0d0f0303020c061924050f030a2109060c050a021e06030a020415090b030a 67
    0x14000c0c41d40325524140102c0c0c0002414911002002050011540d41c407000c1603003d00182500040f074420b01c1100328000151342c001c20700726032200381032a0090269581120100003001e080e0012400d811414102180d21074040d8000e0012100c040d0480380d0f503518040c0e200c80b50500702d4000c0c0060720402c2c03000ca002405d06801800d0320860060510440c03e880312451402c0b518500d48a49680e500c4800401d05c0000550344010803032440d01e010f12085c3c0c03100d0046110050034103001003038031820200100605109a041e203c00b00d0f07260054030414103081c03194101c4014480f000b05141031414136481d84014140010100000c1c0080e000800d16260078100090028805c40560301406076002c0400007030140c3c00e040c000418008050b8a044501e81c0f170051480c3c005404c48421b1080c6075210101181c0e00213040c9820540c1200c4050400042c90084100c1d202c0d024800758004001000f40500d440d4140c0142c07040c2c641070003040409402e1603030121803010803482005422801040400e070107a01c95 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 198747257 1250 198746007 198746029
    0x7060501141012231006050c150c0c03030406060501080106020718050702030909070c030e1206060907260a050c0a05030103030c08040b0f0702030f0d2c03070324110405 74
    0x100d500141200d44e03a1031240a101e08803590328048040c0e0710030403444001c150440c5002c1c0c0054a8200e05040175030042035034031015569141024611000082c1d40700c003184c6c00b03c0340d0010b50101070743e449040c107103080c1c40500701c1406550701103810f140002c19a1840054108115010140d040f000700f648410b21000600020303000c4000c44c00704100c2e1880070344803210803d0144a0903030300d642d41c554083c20001c3c040d58019002602c00d0b48000001d041a900c001007881d08440c040f540c00b401608c9088054810681d20810050308041403c0c0304814003841c0c0703071a80c1c440c0f00310040c24491542d958032a00c5652069044403070118900f4001840820f200390220f952240c840e4440519154071340421944940280c2020940c0d401c00144071411030070103200344081d54007100010321f0a61075a417800780090005001003200c440e10040240407119460a509813001005800d139910749442c1d092042840450100ca280f140000101c6100010410300c100404110361000a904090404041104450b0a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 198748507 1250 198747257 198747287
    0x9030c0f0a051504140402090108160c050106080d1206060206040b1b18100c0206090103020903012304030207150e01120f0c020106080d03020909040b09070e0c070605011410 76
    0x641940402c00341c071102440311110040c030400d0703920b9918282d03000c0d942034940c405c0c550103240144920041170360040c9000d500a251289600318880c04c0c6034084444e40120403028007550309080340003d45a102040620301925196240c0380200e19119030503080d10400c1c842c01005078000800680840d85401c412504001c1d2103803c105014040c40341901c0d103400c4803024070803901054104d241d562130403c50b007060940080c00d00c1c10b0b00521580028825014450b80c3c01e0506030009050742c003540c0c081d80002c5240010142c0c1c003024801c0712210f03207c03448003181d08030094815104c0208403029042c4040d0f8104545c0d40c0e40c51411040d54004691000682c1490300502d5203c6802c0400385105006114000c2207641c00041c00901e000358040c0340034101c0c8103120515204014413a8161501c1742943d6001e5008000c91405858000c8181e2034911160b00c5001c0e801c0d0181c040c032408002c0c91006094050080e0740600807070b62510600107056030b54040c075a0b4002074a00f102080a406207056271041d0340c0d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 198749757 1250 198748507 198748519
    0xe0112020402090d050a11180720010f090605060f060403050c0f040f090f0b10060503060402090607080a050919051c03020115031a09010b0d0b091914010b040209030c0f 74
    0xc20f81d40e45a180c0603038241c046602c41f08050710400c4600708010144802035803414003500360704000d9400381c4404a00d01b03621500304406010001040002d40154940e540a0300c41000186000d040c400007c02c81903030032503c5079107030202f03070501850003109480950303402c04041d2a140203c48100450415405103040e04252036030660540c910442c8900c00ca00360182460f4064800c103850f123110041030080c200c0b959040114020b018891740301d0b0587e0351100003a01d0050307070740c0c42540014900380250740e80100440c000040200c034290380900039240e14042a1103080418111201802c22a00d0b80d00940d600300f555201d100546a070380110000995029000004405100b40d55040042e403550700299407078080c508064250a5500203269032001160380208003005180d800034028807201c0802806036241103011881046042c442d10740340149240c0100f402200c41d00c0c0c01c0004100e200345030201546801c0410716103061074005c42c2c15841006010303006205543c2c0401c00781c1c01c00035604540241c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 198751007 1250 198749757 198749779
    0x2030709020703230a0f05040f0308090d0506070f030c031413020a030602180306010e090a12020c06072102160b0a030f05130203210409020c1c050c070e011202040209 73
    0xc48240900c1c814040151300e5944e95500d0600094603040030f0680400410104100400a08043c1c1c0915000d0700c0c0e0015401da42c410321400061310307406000c40003802a004100038014010382100f03007442c00068a071000d0005101c1090194112103000d2181500100400c4c0092a01e440351844030340c609100401311481e0f1a02c98a1300b0003240c02941c4c031482100c000003a5517141d0314080040c1c2d8010802103000740064580201c1103603d81610070b20042c0803c00c1190700c43c00050081c050991280da0140c8061344981150821400c04403458008043e03100c2444440d02c0341d5440465801e1040c52070f11009001c1d01c4c5000b0041c401903010051030400c042d17a50010402c0d25900340949402068901a83c450081d5180101070410703400e06090f80c1402e015690090b40c40c0701a200f642c00300e03004290010386894421120760304004850511038004569a4110210b0b00e40040240c05c00d10039030380480d0100d40d1504014200f18a0a0291640b40540000390b5070043c07505800402442070060300d010520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 198752257 1250 198751007 198751037
    0x4060e06010b0307032012180a0b01050111030910050f040302040603080306031203070807030b15030f040b0a090c140f06031312050a08070c031b0809090a0902030709020703 76
    0x4440d00b0703048040c0c030b03610000034400d00507814010140307440103201c4698180c50308040301c00001d07c1501f1404030010b100000041401100c1c0001005c07a0300d215040d1080d41419160020313445100340515030220700070008400359a02d0000685107080d0300541203041600c40d540c0c042d42c2c190400c500e080f4541100304404801620b4900840c001140314a01150720f0b070400101301820058610400303004024144200703c4125400b480319500f01c505828001000c3d101d14000c00c0d0300003d011482c2503c40340000074007210b4120500c42c03c2c0700f640100f2114031240c0f43c00391040b0980f4181500905100400030341400fa4110780690304000c104014860f0f80c2c40104c0001141880d0411600001d0072454500b150b028003600304100407880f030070303850a0380c1340038159003000e0300700f1102a00601c1003100410803181018095200700300310300b0048141820401c0c4618100d400b551000c02e04d103029a4460011038240c000c6030240c0c259480d07006024004150502d0440c03c0290440013007941001007000c100061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 198753507 1250 198752257 198752263
    0xd0c090f020301090c080903030103060203090712050c01200705060309011506020f06010605040e0103111311040503070806060102070e07090f170c0f0603060409020f1009060206090a030e0904060e 86
    0x520300a001503240e601d041e281c8411101710000000c188801101000f05400010040300c0c1900da00050040e100d4560312030980c5003041c02d400006200000c40d08a00034031070005241041840241c1e1094041102c040c426032b05400d5129100505a112540a0115103004001b950780000c0034400091070b802a4036441540480e03e50142c0050b070020400c1034072000b41440024054070070350800b00d1070140b402c8086848042c05100c0640080455000084155110486101c01c1c02c41c0317941c14448004903088008c4150f010784150740c4a481607050024408002080041c480c42d4140c0142c036405292454546000390010180340c20400b82d420f000c100c2d0081440404042c16617032071126025020040f4842c41c2040c00f0078000d1013401c110040460699032081160380c00341e419074002c103000881c0c2c80442d000a100d0341140da8024005204240c80540c00380d0364000310340340c1f1381c01c803051b948422540586030001088007a00040700c3e043c40384032a042404030140c02c548100d0002441500c000c91480c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 198754757 1250 198753507 198753521
    0x531180e150907080c03060c07030513090204051912030807020f0601080616030b030c2205040f11060a120c11011d0c032a060712030e24060d0c09 64
    0x58201880818041650b40801284000c1c01e07041005162600d904c20000c1e5845500600c850004400010780e00101031003103040c0c40b03c00c1d408085a50001d034641c0840070181d0024080c443c002c140c01058140c81c80910745e01c940841e400442c0d60651401c0c0754034200c8004c040101454298416030303850421a883c200001402011500080c01c11405d04c444540c100e03040413207240042508090001215079400f1892900721041143c01081207502c014800d040c0d05001c8031780b900c065250008100030b0103d80288a00c00c82e1207038000c50441c941031000c00c1003a0007141724080004003040341116150280d91300c1100c1d440a00d05014030216651080c0c0c50070750300031107511100c0400c500041400c00364100a007000d501800ca0207803003006040d007080851210b642042c040c500010f078100303400c540c0710002100c080681001100360f42210344c03a00030b000380c000341040190714481c00e5510290900003608065844507410002402c81d100c1700e08010004d20804000c1d02c0c0b140d952080003440819503c6450 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 198756007 1250 198754757 198754783
    0x50105030a0906061205012f3106020307060e030406050409020a03060308030702160e0105180a020f04082401030f030c05100f1409010501031e0302010209100531180e 73
    0x1168844108842070580c1348c0c1d5170040e05008489201c035481c181c580506490007994001340113100743c0011b01d480038802100d46400091501c0520000c5075403031b0702000500c50f59000700c0041c000401c5c00300585070741c3e00c6035200f82e000080e0140001c2c000d61050b43c000705083c400c246400b044050722510380c0c404950040d0394500259102c0c861a101c0d80c40083c0c048002031201d115040d5856142101150001c0507d001c828810410140002c1910a071036043c5d034506401d100844da26240c0300c40341d0559400d44584003140e0401c00ca403094807034180c182047c0341030700d9001c06907072090351140d68143c8240300c45023811100c03801404160101802d141c820a55002c19803034000c901f2815030640724849420141c91000142d0616005001284140355006000c0008007503114840b4030509080340203001c0c65099941c0812114245105558000050300300801c840c41c6240c4502000c100c012100d0908050000540440f600c0400c042546014040070040400d0b0001c100c0b03403000d412007403d00c0d01e900b940c0c2d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 198757257 1250 198756007 198756011
    0x90c060c030f0a050c01152706150302221202010806031f06050f04020906070b09100c090612021201060e130203100e060d0b010e0402010903050102030f0115030204050105030a090606120501 83
    0x1c0131102e0007401581f00008004144e002d0b5142007000d11104804400c08040482a03c080150307001c0d290341d40401d0040101c0b038010a120091804018041e510500c0040e607800d01e1011401640c064004100003150381500b003601e156000756005603034200f030040000351f250003554a22082550318a1000c6030040c80e200740080e04500f00b20400c4440008121300780c1c050742c0705020204894a5000c1190030060f044882800702d96616417642d441c081c03105209070401c80c20056069400354011a01405540164942a0340c1c00300010602d0104c0c000d52001d1130001140100403c2a280900d00016503084c002c1c0038450414100a00841680d0080c1c5094030305c01042c110800607200c101c440b041d003205040719003010030502929000d07054401805508040b180d95000304046a0148400800469200000399120701d880c0741800d008880c00d218a509110540040a80d202d12a2017114181d0360140c44150a6864410071b080003002c0101c02140d000d030351a003010446c9da443c2510003038114450800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 198758507 1250 198757257 198757267
    0x2190305040519083f04030227012111011b0c0513050912030933180d1b0501020f0301090f270203010b10050a080f090c060c030f0a05 59
    0x12441c90f01404501024940724076103500c07806a01c4040c00c5400c0300008000c0c4803180401703400c03021200d204580c4029400040b0441d200300c44d041050342111300d1074124002503400d82c0c0e52070a40c0c500101c40d850442c20881102c1d080800200c01c0840030945c0481803610522140c504650022907a000c01803c0e20000201d0f60100b0017864081c2103001c03181160380050049040140117981d4490402d40c00009011004c0001010307030b081008042583c904809070128200481c04149201010141406802c4900c003400070303d00001c109495019824424020301c40c0c0c0282e0142111082c0201d07640591090a210703030400820003d0010b4081c04403480e06842d6a1b5142005010071949140e1281c1e59442c2003940f5504041450040410003400010164050070391510010f4010003c00100950000c00300c9640100203500c2400b9020303522640e19a0407240e240c40e62f07030700d051020485840520707500c031403602100c0e42401c0c0060000d18a80800300ea05044254900d000300b07412846000c00001e41c0420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 198759757 1250 198758507 198758519
    0x212010213050604030f08070807080f03091015060c02030709020409021c060308030103110f0a030506010501030f060f052701180b0d02030c060c030c06090c04140702190305040519 79
    0x15641e4010b00c01122003a18051440d61410300070a29090081d000c0d460118500c0e0502001404541c0110b501211039969000101044200390304103035642441841400740b40341d04e08800f842240766044500c0c40191519240c10401c80b60084180380c22030301800f4a00001600300030303900203803003e000d4018016844042156110340c2020314000401c41c0c4500b062010000b1444074000c9906494014002414410815020a4420408144041d00104104000003d10101181241c1a52400d0360305006481003180c4400540f1300038041d4800d03142c2150001c020b103180a044158400100c101000c011402c40d0007280320340341c4242d001d0000c00b8019560200c944070f09104040745c0800480b0000b00c525242d8012036501c0600d10400380c050f041c006000703140c03c4410405d0341c8403e0704d2401184e0840c54284065a2504581f4841e54065030038400c6001ca0f003002d0a6003039100f00038503070007001c1102c50007400b40d40c0400360308070540c14840204070101d12030300d6081c0704913500c1c070007040305d03648840c5440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 198761007 1250 198759757 198759787
    0x40e03180306100311060c0a060507080606040e0a05061507030c021c12030905030d0f1406030309060a050304080403020907080414011104050f03030c0106030f110307060519090302120102 82
    0x404203a101e40c0114040080c9400c0c228001e1050703d400c58582480024964003103052840f0340d0742c82e030f801d45c8608103d00382046242c3d04400e114200550710207400c0c4d181e41c6c0c2800081d01590040c0780e81040d0200c00116404604d45c80f860340140b00070100079694461640c41d01c00d0f50701c03a0800354001090b02100c01c2c25414840280c20740f1881d0a004140c1e030320710303a40307443c0d20017003103844a802059214441d42c01032200800a80f240b200d05440100000900343e285040141400007045a000000d0000904140360100c25501554000b030300103071525400c900d0403651076200400454412000b0301020000d078480311410345c410762307c41d21035401c00d041c58140514030807401070780c10400780e0501000780e08a94502017603904946080d5083c8800050b068006802d41c0200c0c00061910342c604034000007809924101da05015000381d8032460304805a00505895400300c7c050600494020008803221207100c041c6001004030914007941c016842e50f000030b12104070b070000c3c0c032440e03900400c0400c4e88842071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 198762257 1250 198761007 198761047
    0x15031a011202010f030b03070b0c01060905090705010e10090305120d140405120a03140a0b180f070516050a060f0b09100605030403020f0102030106091410140307030b040e03 76
    0x355500c40070401c410b0340000c213066003000b607001c2003603141e000400013502c0800402c000351040f48081d548603000c150078a802009a4814140c03200e0804d408584ca0710030228070013081c0c03081a035580052080580521440c0d88840c4550410800d0b140b00c0040422024400c4040c1c8102080e0140d0307890f500700c41150160b40e00a660745120340d03401014080010800609001900d165004c0076440b035415110550041c100c13041c0d949240001c1030308212110840d42d0041d010751a0403140803c1c40d54201e2030b059a4460200d96803100f46402802080055014402500700144848410b000080c1d40b03588290030810105409c46031146c49542c403501000f5039024860340b5810955011409141100306000e1080080c460501440400000304061610030310404040c011b41200966036940d442000400c45911403081044000c8010101d0314117192001c210902c0341e5003507403818090400003d100c000c0f030780060410b400303141d0384080d4040103880d207014801c81c0185440c00341d512070101d0040701107e6880d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 198763507 1250 198762257 198762269
    0x10615120b0d0b0c09040510030c12030207060305191b090b0a0903080a02160806040210140304150f06140f0d05030a08071704050d110d0f0806030115031a01 69
    0x7410340341c50094980e03540900045810490b41c0c00e10341c07101100c0a005100360003c0e40d070040c0c00c10081045d100e85110a80c0c040b039101e0400541c100e0398407801d2030700c5207007841d50040040c0c005140c10403100380300741c1003e44c201e80a518402005000d14181900300e0318a484544103d009002d0b200c80c0454105521000501046280924086100b0300040921000707000040c880b1001040802100748204110b0701c00c80d9102c4442c2910945500b00c45684001c103c2e82284508440700709500d5491280403c0d800700b52400344034504589030399691a4880401c1c14480b01c5e1290b4135140074582d04164003030400107041016480411003801018400c40f0606014014000c500380c00c0c116001800000c11221044cc04c1c3c0307040c1144e80c07035003401180d0200c07401c0b001c08a12030a000030312080c01000702e402c03002c1c07285507290b008205098141d03441d1100040480040861b81409507001018050382c100c0e90700c404010000100d041c000c9800b001c040c9403d810941c0e84c82208111007002040801c581405001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 198764757 1250 198763507 198763511
    0x120c080601090906050a0b07080d020c1e070515070312020a0903110f060403031d0d030503060117010602030405121005130209131e020d0b0a0c02010b0d08220801061512 74
    0x1306010106e07848010398070807110300e00350000342007040c4100c420546915084800095545401e1030201035903800e03000c6518084200e81c2480c03025200b0000448004840c0050721b000444016071440d005a504020400d03000d0025410110a094100d40b00405040000380ca0b0301c0405030450908058943c04048614050440d48104600655035913080d02e08603a49464031159051401c61642120000030481941207441c1154240c10980c100001d140700703400a03603c250256084e000d08a800e000203220307000c007507081000180510b0801518041d10380c0c1c00a022280d5030501c2601800440780122900c00202a00c00380107800c510303042d2206c942201a009546444040303c1d04c0c0d41100c0103c00d0300b545804102c0b10800d0045443d03460150074059013105050b2000d241c400c501101401560000303000551070404041d005180520020001c940c001d69400d00740240c0850b80701400020420a12040a060b10005030201090066901408500074940c1300ba0004070006404c44038000c0440090138 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 198766007 1250 198764757 198764759
    0x1c030504050309100c1a070e0f090a0f02040305070803071403030c190903051b03060106030e0307060207050106030506010303050a0212030106051602012f0c011b1101120c080601090906 81
    0x1407001064404161048546548001104105980d03101d9280401002083c0e0304132595141000c1400c500e120305000c0c0c4a07030048403041000c000c4c4500307100d0183d5502041040c081441303580c140e400b1007680300d41c200d8014681078894841b1481c0c040da682c8150101d6000203070b050100a000ca078030401403a040801541075081c41110107165005d10202a8107076003001c2c560800c0948200940001545c01100303885645c280c10552041c0a2030101c41c8a02a02c117102c000100180b103485103c40240c2c003007015601300b036403aa6039000a50310404054999641b19040400454410b02c10540211702c282c40b49503645600010203401d20109504c001294401400100b0149130040c040366440c40281485c4080384070244010b03559440c4c24000e540b032440c10600358140d2101d0410703200c03403940400720403114402c502100448025045900906148981002c800c00061109000c0c2d060044141803010500c000900d0750022276070040c146078001184e080601c8960f50b00490400040c011646d030511140f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 198767257 1250 198766007 198766013
    0x9050601031103011b051306020708070504050a0e060106020f0606150910030e010501080304060813240b0402030c0d140702071404060305120903070905090715030e0d021c030504 78
    0x240005120151080109040119003550b0a61107001c0c816500d00040fa0700c0885180f004169402c0b0040703034211206080008521240005034130021107030788400403c0704608090034000900300141280a0440e11000c55100c1620203002043c041d080c154018809800d040d20542c0c9402000341185008000d01d4460140780400441120341410082c1d5841c08041107124040b4000c02101103c4400d6500e031100104081c0001300080044840980e01c1c1c1c100750711942c01e4105461240080285541e84100c9101c144100c0c0d0303040d001c0070450b80d540020722244404081382c140da20031900d5941ca810001202d0b515001a482160150b441000c04480340e450142000781d590344041c0200491845e01c040e0401c02655141c100c00302071540071060366140e0b03240541000703194024108c164403e025412020138010b41a204080c0b180703604030300a151852400b44000b4071240e19104070303010161109420000220100201114581540e0040412144402c0d0002495450420982c00c00d81031400340004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 198768507 1250 198767257 198767263
    0x5070914090c0a1106101a09240d05131403070f030516020303040f03050f030a17060d200306011a030105090903040509090102030919030206070804170c0a150905 71
    0x40407a1020301035640f40d603444000e4078040c1d00c840218142d40324900800143c83d0141ca10141242c41e11140703401c411000c60003d4959000c2c10405617000b080900fa031036484041552004a01d1142c802010700d4500c064a2403000d4550480d802c1c0b006100c210f41980c10441e01c0c9002031020303042c04010f1420300345560b503030181c02420460050104440407030058401750030002000140740e40103080f0f9540d280ea40c40d03004040200307440140c2c0c20340241c0b65000c940c00c1000c8222880c0400580c0d800800741c1c07a400c940740081101030700b5550025008400c140004512040031500038003940314222500309403000301860484142c001304580080d0001560003401c1c00c405503415113600f150030b0043e079130799146540d00d18083c5500c80e540c086090414440c0010043d0300440c015440c0e0029181800840d0754085148881c0b030030014016805400050002c0380b06406003900a440b07401035481c04541043e6440d07091b00070a8654401360003005406082158444a0001d0b02c4c4442809100c01c205645800d51 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 198769757 1250 198768507 198768511
    0x11030a091e1e11040c0e030715020a0b0406060b03040f0204050c0f2a06070507050613150b030703080a0f09090b10050304080d050a060501020f010e03041505040305030d0507091409 79
    0x210b80c0d007200e6552820081d04429019040d040540108001008040010840301d4481d60581c001e0207040000b0411030400708203248005619001014a00083d81c2c0781185c4000081056541035592407002ca80d44a0340001140914011021a000b80c401c0e40104011948080e003807400380e105c2009180810b10914081d54505021500440c0380a9046492100001d10380a000c02c0b85000c1c00b810130100d10b4118018002041c000c0c401c03102030359100b0080c42e00c0312001e16009401070380d0f0a03062000680c0284c02010f492000a0103031825555265074041c402d030869014500816030840303040203410742c04111400248410f034014001444403c0c041500e094042403030708200480000018240200402181c0c2c4208070244100300a10700918028010410307030140b00c1c01170160308a04900c03807005000380e0003c800076a0145207024500419980300003100c10340788003444070500000001c1541480a4600c1d21000403022900d440c0c2072070300412005890704145d81d5140b071081c501c025a141c5102a80d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 198771007 1250 198769757 198769793
    0x3200a05060d180303090b0702011406101e0201020301060e010e0d030e032802041d1b0312030406050109060605040303090303080a0605061602100e0f0d0611030a091e 73
    0x941e0b41e5000e212000c0584070040011407526080d060035001c056265002c540458014603841d08030392900482203003030f9504c03215001034004501020a565140120050b85148a41d0030103000f00717060014582c07001c1c00741d00d40e8040581d60210040241682242c0d00c3c01c0c40391024a46020400d03080340001d2048510300c1c0b405400c111801100c0032450702c042150480035003920001c15529a030948540c40000c5d40000308901a0741020b2000510101020044410b0040079016110010300d03920345515984030406510380c140300790a0b40741c0201104100860003640030b418046019814070f142e00341030360480d600640030490204000c0020980c44074982d01940d0f03040ca48200542c55400c000f070040e00160b084958000c8001841c501c08644000005400c94802d9a0382c40a00c15044410343c0e11081250585420440e00d2154480900c1c10550040d0003901c58a00001c6500300d100d99540250801c5035044c4000e55500307441001d10072100c0ca440310014081c1c07180040803059030307580088604805000c2c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 198772257 1250 198771007 198771019
    0x507060504030e031603060c0503150d0302030918040219031a070207090f1a010503061806030a0c06080405070b0a0504090231030303050c03011d04030203090a0e0103200a05 76
    0x441c0806105003051890404002c0c22600d0000d69504120580b01080c4411100c09290080310440503010340c0a40780720300d6101c00000c0d121a020420f00203464020802202103000400c012845a69070348801800c040c0810302c00c102c00d1805106020441c10484085414003444903c1000002c0d000c00c249500e1088901c2280c00f00e403540d00e016440d000d03140c3c00c841003507400c05034040032003242e580c08104000c1100fa12800c0500d082d0b80155803500c4141ca0154101c05841d00c0c0103401c0d60340229498010030007604071080c00c61140c031940f04c1000a90080000105800180030620204102610203400c07842c25003846c05000404c003808500c1144180c240090300424000c1d08050300402d0480584041c040d8640301410701c0301a050704078001c2c001100403920700f0000c5410441400e0030f507416901441e448103070524210400726103070382e4028002c9085100411508190303480d50b5450303000508a0a80350422075066180c0f240b1014203542c50076055565004116a00c0d545400008080310015910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 198773507 1250 198772257 198772261
    0x22061a030402060a091d04061a010f05071b1e0801020c0307060504020303070203071514090904020d210804062a0806010c080c06060109050a0806010302011d040c020d0f0e0105070605 80
    0x16101c44103180c2c1b184c52084500c8501c4401c007800c0d4203da6115a02c41c00c1c08200030031501d084031201d68041550580081c4202810118840c00707000200301143c0903c400400d409000c840b111300003034481e04007003009030340c00d2040d00c401440d040f18a000b420094000f541052800019296a0b00441401030300c450b8a441c04a815924144200e603d0b2a40146c166200151501c502482c6c269080f0750510000e50b086803102002c43c00309094030020030b0018645520354555808100d4031030362390042550f00c4099100100b0040309152142d03180c1c400d494403070090354a0a410080c080f00c00080380c642e00449400e98500408007a8042200f040320310303041c0200942c54040040390214252507009185800004503400707006030020f00d6920504090380ea4000f8103403940288082e12600b442001d0f00d0764881801880198011912504d00302e18034a200b04d203c100800019042d120b03485180c80141e009408100e0a060b40003e0824940e4054104100c450041c1e400081c85c41c815017401420583c1c2d6080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 198774757 1250 198773507 198773527
    0x402090c0c1b01020f07180b040b060706060317070b040b09010e0304060201051005030a030f080703110715150605041e150810151b1122061a03040206 66
    0x1040d5207082040c0c000302d0708401140b51034003801c0c0d0800c050b510b02620400310300e220100c40020f109815214012200001800b0f0307022541d019040000c292640319440c1c102040c02c0780c031140042c04006010781800703c1d682c1d20303600f020380c0b014142540d41140b0303400410100e400b09207600101c90b00184c1c440100c114568403000d000d40181024601c0c955a4040014009821641508001d006a03c1684013038102030340c0c0c2041540e204002200280890b65240309942080c0c01240455070113603c500f00032645540702e1015003107561225000300e079a8511088503e0f88103000e132203184480c0038140307034900040d801c00c40c016046000fa8030a080741d01c0741404030070f0412004042d6100040040440010041c808040d0161503604100c0f10250700c1070344102c0c00240020b030000c1348480000940c039441d003c12070b41c1c255098450001441620180302c8103209100b60388940c081c1480c3d04052003a5140c0c101c0ba010009400c0d101c060f0f0004802440c9030703400c2220000d0391011030307400030b904a03106039075850014 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 198776007 1250 198774757 198774781
    0x60406091107020a05120d0c0305070f0311060702010b0a050f01090518091603032114090304090b030a0506010501081308030c1c050f0a050901060519062303040209 72
    0x1402a410aa051184080552641c0310207001501d10884281c190341d604e44041c46000d10103070030301d200c40b40e100090b1446000d000b850340f44112030107898444d02e4544c031503c40380c43c00c500324281200002c80e501c0000015400a000254000344203200074001845204000b4000318000c0c01080e10411200701300403403e07806a103010f0001d040141182c0210050b84d0015200d680c01215004142c0c014440b103607003421144400f031000c0d81ea03d516032103200c840540f59460780d4082006084145640c42c5101c91118040c900c1c0c6511428690000b940e0340e078140400c00c0c050382c4451001e10301a600c02e441d051f0000d0404103120b030541e1400e2908841e107079600100003185081c11100034080d880d000042c405180a010005c01207000001c00440e000e40700b282c0c07842c00715401101c8141e9030508c018089407000c40726400c06604262024008544562650000780d920107500941000f1604550000c00c00070303822400d40303100700600ca146040b41204c400b0020b05144030007440284205414070004004034150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 198777257 1250 198776007 198776009
    0x90306090b0402010f050f031512030d0509070602010614040203100e0403050a0e092505040504111c06050d030e030111041e0509090c0d0c0308120f0c070218060406 72
    0x1090050110650301d08004200c080141d4003a40001d21010b2501d11441c0a03074101c815003101d40c81428030719a9909030f030b80b11580082e1741c103540c0641c000350340001041040020304000c107034403c000030301d40c24030b59401ca1401b0440c3c1d20040c29641001820002c00d001d1924120150106072409a80c0381d8030410f0382d0f07a4200040e0082c6d0081d60201d000e10041c558004003070724140030781e9181c1e11020301c032140030080848412580c90146048a0720340700c80b0032102c00340d1604940c001c2d060075410a82c1700c500260558030400c0c602c500c0300001040364849048100600800b04844100410145003030101280485200d04400b50034403101410401498409520402d011600c503643c6640311900e5110b01e0840000c002000140401d18400200e000d02c3c0c2800110301496144000b40040310658080c4540003000f10030903a01003601c00000070100b510300c001404001c6001e00fa020380b03860300da9801d90741c2c003001409070846048144101d800507151003008283c00001d403000f25206684090004001c0e00c80d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 198778507 1250 198777257 198777263
    0x130609020a1d01080c010212032404062337031209030203010b0307151214270c0a05010309111201290a0302040506120105040309060f2d0903 62
    0x40726850340c0340312201c64043c103840c2c0c940c040d10000c2010100490b41c80c00c1e030111080b070b070720b000b040402c0442c104016a01c8180b04000d0803000001040c100060480c1c140d03920801060034400c5001078070700b41d840d0303a1800d094805c6441010500c1c141d04288007104464003042801e074000c036131080702d8104c00d118003401198014140482c134000c5c024018048401440b0880c0030350300700312500034686004141e0300b003603600c469460390596050540032508000b14240301002543e8600381c8900c0c4054040c5e00310700c034141a440340090140d116840c41407081c00940c4061540c0c01003418101c0c2c6544031102182200c400b4a000300d81d0080f41c2c140000e80c040112480c0f5802403039103580c55480303003044d08006521070722010a041205a070302455070f201c0d414005410340c0401212000d00040c90154072035904241c001c4d01c40c1d59450340070500582110000d88055010840503001001441c2d8004102c0c0d03807081c000e14082d01170040301f1111400c64203890400401d526025070400c00401d102c0d007469001507030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 198779757 1250 198778507 198778529
    0xc060c060a0903050732370605010b04050901050303040e0420030a050a051c0203030402100201140106181212121b0503090106050a120809030307061e060905130609020a 74
    0x1940600003020955080039403104c5200480c41d00c0880d8101046031100c20107498600138007d03a014809907010403a401c490002258024060b0340451030314440c407400b03000350617012035607241000304102c0046416444248607030301c20402800b442900400168000d0ba00000703404d042c50f00d00c02c0a81c0c0000614401540501ca0410305509008000956042c040e000ea410354503a014200c441a021a14182044015074820008517006060415424401000e644000140801c10443e4418540001c5c0e102c80700091410007800074203101014039034024500355020000d031a24640e90b85c0ea04581c1c00f1810818000c45c3e03148004c05146c00e401194914071081e0700600d80c1e00c0180000742081e0010358200c0c03440d601c2d220022582d0309181c10003030180c444584148014524980c0d420846d03600c010422505800203100080014245009040d00030700c0c552860340d03004400c040d046040b03030f000342d0041c07694a00700001c1c01191000c0812200b1010f4101c1e43c0415286d0803400864005c0040784c1c05404650 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 198781007 1250 198779757 198779783
    0xa03180b1602010b0f090a0f020307180501020102030402090c13090204080307140f070b0d0b030d0504050f0321070320160b0c072601060807080c060c060a09030507 72
    0x40381001610034a5a0520880c0c00a04440128200c030400186560045038800c65009a49800000e607a40811022004941c0c40c03112600e6000340d030025075408003c120011640354158508042d0a00580001e00c0218110310f081c0d0000303000c0040c00380c011207002c24006030b02d5110f003100d810840c0240c91004001d41d502d0390b4a080d1580d990344504003e0710749408200241801319008a140d201c15401c80008003511814401c50405c00e034481d484520364990358201001d1603807018030030661481000e48a15071114604420712504000b40c0007200e00c00c1c2c020580d480b107034204442c0502c0d4481010780301540c440d0028a401e6428402001c0101c0400442d08001c15100c1d138001ba4002c2114602c030044c049156036119840030300d0054640c1401c0b01d4000a2040c48600e50300003403043e50310f07a43c01c46480303003d580c14941c5085903001d4101d649240c000f00f03401c2c0042c84041121910071281611a80e24007804c81117229141c00c40504403504d883d44444008050510450989446a801c86042c469407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 198782257 1250 198781007 198781013
    0x1081302030105090313121a0603030c0f0d081602070b09030309031603050c010207060815040902120a03031a010905040c020a290a0b101110021b060c07170a0318 71
    0x42c0e0440300780501c261298203004103040c50310098180100d41d10000d48c80070850301c1c0b480b181104034024000e9405200520035080c009404008084140c081c0d8005421901021a0001c0032040c0003010701051800101e43c10800f181e0005018007100d90030341c140703601c619050780020b0442c41003100e07a5a052052003044213024480f07069240032a48120201c1c4e0b9034105600040e0380320380c0248135090104071380b80001041c401654038a0300b04120020000100c08049500080c1e10f85c04a610201c91070340004210b0003050303014403440c0d942c800041c484005502002d0b0009003002c0541c028140901d84420784200c045000300213018805512100114004912032614031710030301803049542081030384030041640c16401e846488102d04018100c0102c41110010540d542c07a40d40c18000c2041c41401d40b403000000441c40078001c2c0e02c80890010304402e8a04440618025002e40321305180201001000005115007440460540000011540300d074200c082c00d8004024400103619050106031640e020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 198783507 1250 198782257 198782263
    0x306090c020f070501180e090c040c11070e0603032a06010305031c060b030103140c030303180c0613031416090501030204050a09080913110d0504020a060804110108130203010509 78
    0x10409141d0803280d00f19504c10044a41241d4200c2030f0030101e02203082448041c01500040342d00c00000d02c2220030302203000011500711815648904002040810b040703190250a10114009007645c02c3c07032440034144900041d80b20b1103a101103800403a4403524605400c2c404441842e00c205c1908141c810035a980d040598690b80046041d1b0803880d140c107001110440c0b203103d0141510062882c1d5401c41c4c0c2141da42003000c0c40001c000c01906d01ca00340082245507410402544030b1601800000c18108062400303c1c903040300b01075483e01c035120502811581004074000c9070200d940000c40e40841d44030403910542012510820130000030724049002c1120700484d00300504031303807090301c040105076220000682111401d110061200d4410004180e013460034800001c807800c610a00090001c1080c0b808414a0f030100c211081c404d62101c0400c8150b14041d50340e4001032050b407c0c022030328070302555a8110986602c0c0701e02d046c00f181201117002c40c290300e0190f481c6d560f4044d00801a40c24440d080a60b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 198784757 1250 198783507 198783523
    0x10902041a1008010602060a090201050d1104050a0e0c0306060a090e0109090b010b0c0c0603070318050106150c0b0f040309050402030f0105030105010603020705030f0d14040f06050c0412020d030306090c02 90
    0x1c01450000b000d102202e101d9030f00641268056030107481e00c2d484044130b040241107150800c0e41040014030005804003c6807180c00510f03400c000c03015036030318501001c0c000300044560141c000c182001040001c1441e82c1c008899000404813040c1d03a0758001694203494444998010712060240e00c00080f449801c5648280b80b29405156061003da0381c842c2101440d205007184045160021300060400c0d0a11401031500548103040200301d03191454032400c01441031490a440030b170344170541004110700c040300da010361504038509000002d1027902d0b40410f1004c060300c1100c1d031210820000d0207240c03068200c18040c044c000c0c0250750301d003000b10803510018000c0c09102e00c03079480c16000040e0786000f88202e501c080c0e030013805941065800c1c110308015400c01c0804c01111510761840d10303040000e1180d07980c40785102d0340da2a070158140e410b140c0c0460b90010010154400200814031508030090301306001203070f0440d9044506a4103107005c07000f4006a6009a0391141041d0f0700391012900490a41 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 198786007 1250 198784757 198784759
    0x8040e060411160b1302030a0605040303020910020a060b0306010b070f0f0204020a02030a0201061715250f020c010804021804021f02071e0303140a1107090515120709090302010902041a 81
    0x1900c45e124401c040320758100c05107000354141d02588c034070b100140040c0c0240e0703403190103410014240b0a030704010510340d000e1226240016003088640b503080081900c2001c00c01407099004015640c102440310712240302d81d1002820034001c0000e65010000f40381400814190b01610554a03000b805401940e6904624002030255083c00004142e0f40303141e50402042c410520020082084030005d182c000712405060301c000720184030016030070010001d00c010601c01300d582c0c1c1d40c85c1150016030000e00740b8040003003040c1041740110901c0090b944103000700d00f4080e444140c0710f2898031a0310004071240ca02d202070588441d00c841020306241e07004a0306c41c1c212004600c104a807902040c6117040314031000c0c003005010407000c510b1540320031000c20107070580d01202c0c207040c5003031181c3d942c00314548034260740300d00c400507221001c1001d41c0c002150307034040118080d501c1f000b0200b0b011141e02e4840d06d00e40a048800c598075402c100602d0300c01d4100004198010300308020820200c403050300070f43d540021302 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 198787257 1250 198786007 198786023
    0x4020403060615021f2f0301031703010810050c093c09010303110307170a09090c021015050a0e010905072303060607080a0801080708010908040e06041116 68
    0x107040f0141c00482c4001d0f52032103000c3c0150790360004c03103038040c02010000715500c4d084114041c010151000840c22145200716500c405440c0d624519003580448031083d20450307a900c083c40100041d9200259031034420090140105043d41c4242d0103000714050828030950100f4a582e03910500daa040c101c1c0080d004800c80c40003540c0b02041c40e1200701810b6080c403c3e8004180f0001000428400d000c01841003000c00c050301d241600b0341e01c7d0f82801c208a0700c041c00009400090003802c1d107821180900080080400034000900c4120740a074030385418244031001951039801c540081c1040303840c0340c0050900180110641c0e5191034254018010034021200c041e0324103c0840c0e0031901510307000c01c00d0407d04d80001201031090741e02010540024122039008003003842040d00044c01c4202030314154102c1d40c0c50104035851306c10410720b000240e40c0420b2450345000700c0711004c240f41c41d0841c0c007943e840d2500400a074540401080c0244034024060f280b141c80412000b070940320050303420628a001d0465 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 198788507 1250 198787257 198787289
    0x110d03090c090c0e3105090606010804081905090303041719080412020f04090b07080105061c02070f0b0f0a0b0907050405190f08071d0606070201050f09040204030606 73
    0x1e00102d80c0e03110f5050300403500c0c05105a0440c42d094040190350012030000242c106021401c1880340c1c009503c4000381d86440e10b0402401e442c00f0098154444024645608103042a4503070301d03420b110300d03a445001c0c18500c1007100c04180c0998111810448054112543c4581d944907403030310100c21030402903c6d400f56000142204800d030700c0c500801c0c4c1d00610128605413a0400706540c0e80e9004508030f8010070341d42840d40040d900d52180440343c50243d03040c8500c500c3c11102c0103084402c141c003c5485200140b02141c00034030700a04840560007611070060350364041e07040803007028980c03000051007159141d041044a030710224019008a000340c2c0c06010b070305641010008003000072330b80c540014200348003c2042e0b1601d61110610701c2500650554503588961700001914640e41009003664400413041040080c910310f0042202001056480f490400c5000140035108011000e410098042989c201e08060403003103600e5910014000c6540d20750340c1c0b1300100a440544500100607041e40f207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 198789757 1250 198788507 198788519
    0x1e1005090711011d07120317040b04120f020601091d01020a090602120703050d0903030f060b1c0213030f0305040906080106170f2509050c030a1805070303030c110d03090c 75
    0x5000e0f01c020381360384041c054080c04d10040c1c5440110550b4190204866080902104101c600140340034078011003212145260604050b901d00c8201c4241908009580400115880d4003190482c1595001c90b8049880b0920304d1804000300d12504d43d03070605520004611941c03036000101901121903a0302034503100301424060640728001c1074000342c0072610410601c91902d03065401140218030070f0030006480d0403150515405c0320001d4024410203100016002c0405401800c4081020a00b001c01d42c58180b01390803c40511480d840003c2010251101c10300130140502c0586d40a000c03000030801038a07a5480005010f80403901c01c0315001c600647d030741c500d001e10215107154803200180007403c1c0c05101b00c0003644405078501c44040c40706002e043c003040035003090184070300402083d80c0c2d094a9081c000d06184c01c031680305c01074a01c1a00210310020019501080c0e001c101c940600b00000c2001606000391340383c3d4030a415604490080818040e0410b415902c40001c1900440c00c80e1207040e1205 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 198791007 1250 198789757 198789791
    0x3080610080c030a0e250909170f1b0d09050409050d0806010201060902120604060f0806010b07050106051c06050108210c03090a06110c0402031e100509071101 70
    0x49038000081e218100040246040d03000541d0845000300000683d040c00c0100141013085428524806030141451000b03144e480d0464000a010994410008006c099036460521124200c1140700110040f9046c5040c2c001c1100350752550080a07090362080f00c9945299855561100d0a0400310f8a5010041101e04083c401c400c00325134460300429060700078100c195000a80149454115900c9030004550021503001a0002c414084421403050800004100070349546400154000d148101c007004180c400040f40b5044505d00c40e011541c1d03400c03d042c45030242241e03821075500310790800312990040500000d0301045a001d070100300a1030b41c1710007150343c455004860182c0120350b11010014418480c00003403889003110750442e4640526030010442205099104001141c002c03031341c080b4884030a0040d100e0035482100c0441c503500e0304840030800c030440100380c008140d44400018100920000d03101001e42001003140f202c038603000c0b500810484c1c1c01ea921030111b5080c060681c08844102d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 198792257 1250 198791007 198791029
    0x612120f050a0c240f02270105070f150510210c1701060e150a0e040b040b041104091b090605180c130602010f0b030606010e090a021213030806 63
    0x26507200c440785016910795000d84244410a4411040b04c00b9180070040e00a2080e01c20000d0342c0310b800350322440c00c40c2d0740782c40b8541c00c0801e0500d04258203140070084e0307900208551046910074482e056582541c246400740b03001c9410342c90821403900051000041d0700c10801000c4a82c108086920310302c14840d500c0d4000c04210b00141940d076524414072501d5140811610244482000003400d55a202a50000c5200540340481581c2c2c190b10014103905103618030002919440780c0c1c4100c942400d5590102c3e0f21801000540b801147d94041010080d95401806219100510034030200e004c0381040c42002c82c030740580c002400609400018126501e005040c121000245a041c030000e0702a00c000440c1c400a2055820040420030031030008010f544100241c600c40d400000e009042a81c3d0341c04450f805076800d403080d03010204000c0a43e82c00018940701510175075001603561120800d9002030b001e10750703c003440224004e04200c08480610348200c0d043c0e000b44e855104580b111004d003c9200b140c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 198793507 1250 198792257 198792277
    0x3160b0420150a031e0b0102070e0411010305060a150f0801050a061b02120d05120a0212071202090310020c010507050f031329040b090d09090902040612120f05 70
    0x1c0c020072000b0112410000c1c0c984002103060210b098003442911001c20ba003982030000e03045e6500c1c081e482841d40d041144d00003a0031089240169810a61902d40c100b0041051481c1010b4a510000e180c40d04c40060f114000d0480b400d41e00350300c90310081c003c3d0010f46407408800001d85910000642450001017410440741c4544425004000f80c583e05c1000a40b1258141d80140b01d100070541595000c121213040b102c040d80c1d82a0304d54810090130902c040024041e100514014848403810400060109800415909141c130706424034000d902d019024150a40c0da0600071210a9000ca9001e50000c040003015034000300015558a04292014040d90b42003003030b04642400000d800e1240102c084242c103014807850100404403014001d90000b007180b64803c0c504802081c0010031012036140707138015280401920500d8003140f00100b44014512691842c141c0300c000340000c2d910b80340d10203c00b03043c500e801c24407510a50305095884030300d500705034000107501c3c6503202000c038030450507140f510407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 198794757 1250 198793507 198793519
    0x80c01020f070f091503082a0105012105101b030b0909070b0f0403020306190e0d0e150d0903030c0206071704060c0e040c020d170603031b03160b0420 66
    0x1040c0000d2074002c0c01d2401c2610801d805c4c03090080042801c0c18060322109030a142c0d6131046009009640909410040c80143c050b0f0615006100e00c8082c41022000b0310883c844070407410b80c4038200701e40b500d05d9048202c2c802c545403a841000c1041080070084441d00c141d241845050031100502c58008400c40d800c60054011860500a00040a0040c24601c0d440c906039800c1a840350006410100e05490612510030510360100d041e0704a800b0b020404c1183d600900030705020808080c045001010016100b061801c054400250480701610003140d161032040101d23042d40c0c580900180680c422100241c03246800280072913100b81000000b00c410340003860115111a80d43d1400341204034400401d01404004000c8940c0b80c0d442400440c0380694010540c0b0040f240c40a0080301c100460303079007454500001c000c1e007510300100300c49000c00c01d400c122030b00f602c850f0982c0c3e086014401301c80002e1568180c00405100320001e01602a42c05081e0309021000020b00f181d200000c43c2c21144c0d0418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 198796007 1250 198794757 198794759
    0x70902030903040b0c030703090510020705011101062105160b0d0b06071a15060408031c0e0303041208010603020a1704020f130f0c0c05100c0507020604080c01020f070f 74
    0x40064000d10780110500c0c04807420581c5551080d281908420311000e4142e20105003034080c103900c01e130400020401035420030240301c81204001e46600c2c4500485050200e441013040c040182540028020400079103003e02011241d4040002500c42007425219031103400b1030880c000b920104818201c4070394100c0107140c1140c01704010040c121061500c4c4d032107032083c03107030b403012901540200c440100052031001c00c0385030010090640c1000c07484244d008050511060245040010071240e400c0300204022080d58081d4030240050040c41c42691034500000c4240030800c05040240c08011a498544c03001980c2c851070110200d0140445400008010230400061480d43c48041500540003a001807518210f10020480c2031031340c0c241854009964018065042002e4490101d03e03001c0c9280206142c0565201ca40d5650036498500f042d803541d032141a00802d006500321421241c0c0900f83c180c80c0c80d91240e100e6106c0d41e02d070603658053b01031700c03280107402c07403003c40c000c01504c031201d040160075 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 198797257 1250 198796007 198796019
    0x1c020406080411060f0313031119150905070e09011407090302010f020c09130204060e0105010c1202240627070e040f0204030c0302010f0804050604020108070e0907030b10020a0507 79
    0x10040300030f8181c000100b004041030502c0500002c510900690b2040f07284151300349001458104c2c4048100d0158020078800441240c080842025154025090141c2040c400d1400402009840d000400c584270b80440041e0440e505402d0074403440300034000b04024026811040c0100c00b04482d040700056010905000540c0140059148420390f48100d43c0d0300400e80001c14280c110036200800c0c4080c0106914003180380501038080608420244414154540380018128003c5204000d00858012803e07440c014803c00c812001e1040c44480294103025943c0c4000b6825810744d4070702e004204940c2141c8031840e54415a1020603545400100140c1d240071003140c04044004483d1b910039102e00e0349900d0900180081d102541c01544c005030101d14510014060751034000080c0d00340002642008007003070300071070510360140e0203080c9030300b00b41e030b800c4800c680601c20a165145d04c09860000d000c8c00990650040c1a100c1c420b0744d50f10b0030301500500a980d982103400b0700a00e9603214540078008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 198798507 1250 198797257 198797273
    0x8070506030f0c0702040c0206010519241101380d1b0b04080601260a02060904020702040e010510121104230a0b01020c15120403110a0303021c0204060804 68
    0x8403e21007484242400340075030001d8240c9144880ca140113a000c0001840689040d401c0c40813000708112040c1c01d800d1a01a001d0300c9603000501014006400d0411100d003903005440c1c8505082500c40204106210b00100051180c00c10708003010224a481d01c12080012440d40c0a40c4010000c0141f0120f200310b40ea1920350250401d544c2a42c3c00b03410200003420b80300d450240000c3e02070030026110b9581031010700b84104100c1070240100248100c2e0910f809100840d0102190781c0507190103644000107000325010303111380c0a0094005242100c492035844040d4005406915185000000a50751720070350380311000000c1d0040c00d0640303d40b600211034901584482c41c2e20071000d10050485881c07044d020981001250480c492503100c1c0c281001c02d42e0b040c000c062039680c5c100c0c3e0700540c1c20a0140a034016005400c01e45043c450480085428035015001c0301038441070150449a4103851490010003035000480c0142c000d880040c6003006002c124000c0d2404c0d6070159603423012a42d9280c480d030039 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 198799757 1250 198798507 198798511
    0x81504080405030a030c120e0918031603050903060604021e1308010e03070302060717040b0702010f020a0c0b0f130305070f0203060103060506010f090e010501180e0a09020a08070506030f 82
    0x90362050422001074251401d000484459020352581c03a801415030620003040c101c1e5a00c0f0310100400a80300c0040c66441c06001600800b0404e9000140c05800c10301d1031442c0300300391030100305a4181513130703c081540c000c000f40389100007034080c0e645580f18070f010b2000b030340685049185545001030703c0c1c0d84d041c04000c000c3e0a01038140741e03a00c0b99171aa6140c41c01d08480089040400b01d8000180329404c0c07603010040c030fa80200c0980380401110349080403100c01d1080c060b10040c612062000400d010300e10035004413046035205041155501741e1010041c0c005c1030f0f2007408940c07405c0a24005407200c40380c0035850b80310b6400940c4a10740c403159a41c0460302e030761140c44212451446110380c0005a2420070529020310302c11b00000825090503c00984507500c4110141d041248400060181ca004001000d044600c03e00f0204a1402104840f0200b40da550700300c2c82050106200300030b4128100d070400075035940242e0f1240b50045d281c00c811502c1d960b403030040e150481c1041012982841400e40c1241d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 198801007 1250 198799757 198799763
    0xa05040c050d06061e0f020604110d0506070815030613060203040c030804090c1b21090503010f0506041d0613060905010e010603060e0307021503130507081c0306081504 74
    0x80c41c02e4940403005040f102990084c0d40000d451030340418641a80700d40103070981d807050400700d42c1c80c2e498400c000e6803648010030040a0b642103042840b21a203422521041c0eaaa00409031107852a145100800c100801c80700c403220740071752254840241c180407440074080d40142180070054075254403000c02951000d4402c841525050000201003503051003c1c0004e081000000f00d4031040b1040b000700703021403004e201242021402085400101c0054141c0040d4004035880300035030f10383c02d10a03074440900358400f5405500382064908085100d500c068401d0104980400c01c14031481000724100840703100d00055030b0705c00c10104000340c480c0c600c1100014030851011402440d40e9807003d00b591801089070300c4980d1111402d02c00c10500303004004000003e5001182000e542c0c0c1c00154003000c81a010714040a4000081040380d040034121154a9030002c0071106001c0c0d0705c1c5001035889011403060403da5901d801104002031081c0148800c0380c0c040c4004100001100d4008061210050411 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 198802257 1250 198801007 198801017
    0x7080703020c0907020c0306010f060c23030703020109020411070c1a0405060f0c01200a0309020f06070f12090f050f130f090c05060301081e032502010314060a05040c 73
    0xc40d003243c0e0b4901d54244168040d0380a08031200900d400d05180c485d042c1c210421071403c0080502c0000d0344400f01ca40031603000625071a040300b181d1b5407000450a0410760103128040001c14606158054001c4101684203a40805c0900380c001e010b0003407806940c6c8028130b015408001003058645200540b03085c203514081543ca030079520400600194401203c02100140c0450151000324080c0316a14030909e00d6980d907101c00d41c0907201e42c060740c402c00a021041c150303551084815512100701512082d81c016146d1580c1b0516420248075101030040f044a0140c01000c21207402803040310400c0890381c1080c1010301d150b040c00e042000114150b001d0540103080c1c08801120103180e0f0182030180d0344051000200d80915003002c1101c50344036004a4040d104c2000100214100000c1d411010b1310201000d130051244086e030982103119110301e0812900c0560030a03c0364007484c2d26240707520751003602d003000301030485046190161000c42d502c0303601005094040029080540090208410300c3c130344 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 198803507 1250 198802257 198802273
    0x807060c081b070e010e0601020109153614010b0303070b0606091305070908010e06070503180a030503071d0d0b07020114090a050706080103080306220c030f0609110708070302 77
    0x442ca0308030140d01c1404c0604080c8010005201c292000b50740149080c8000e01154a803620364510803146d0040b2025100c3d5600b00f6031042c26007510900d509900b00880e030aa404031404c40704184064000000d031400300c510400c40d40514014803950f0780d82800640610308000e65030722000d004040041045070000c504109007a49641c50708480380010100b40000180c605014200404055a81d004151703c0c0e80340401c8609250800603516501c005a4030f00580e89959402e1040c0c5800c0903140610310340c2c0702e10380400c1d00b01600480074520070b028907a00c400310301c096030301030311401d6003a810381540003880d5881d09000b2503d140c103116481561400040342080308400101d07074a101c101e480000541100300c80400f042014803000c40104564509003082c0d50568031803050500c80a41082e00c102c1b00b0384000003040c4242c0e40001c40040d000881000440f10450000d00606910742403900d01d24036144003c1200110380c07098120004c1c040c01c015040107015684d00a8562056806406610920710 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 198804757 1250 198803507 198803557
    0xa090c0801050a09031b0b0c0a02030405030a080c011a0d11040b131b02030319180204020a030902090108030408070605030405210406030e1b040f20090a0807060c08 72
    0x1d02e809007152140004483c1541d040c0248481e506061082a100e0500d030141c001c240c02190351900880c40d8004103035280e400d480c041c6d2a40c4500c0c5d121941500600d0300040c107100c00c41010f06030803944100244030302e5072002d5801d000403000712002740e0300c0b0362114007078004a4002d1a1031000c5d540c0c05040040c85240010000d40703001d84d41c1c026450320704e494010426816003070300c5500e42d031007010340020760560811321106920040d8480c83c131700c4065035a049203021080c2d250350303803411107402134011540d42c0010203004024100408040e07018000c65000054412800412502150305400c0a420100c0c02c1070340c02c0702c0c1c03544081c0c000e49003441040e049651030030b5404040c824040e4030140140e41c65140401c081c2c02d548218282076415000440b015101c101408030019041c2412140080e4080020407444014124032807131030001a180100f800c5034902c04801000c2110f0103ea12000865545c12110f0352100c403030080030005842c410f800c0e0009840f000251080030800b1400e03100c07580c0d0880d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 198806007 1250 198804757 198804761
    0x140106030206041401021009050304060c0c050402040303050c061803030a0c05070501060902041a0a0212210702070801060504060b16050a20010909090b010b1305060f0415020a0b0a090c0801 83
    0x42c008810703026402c0720800245d80c04012a00108030071102c203000e006050b48038035480340107503c81c030414840ca4104800070040e2108a007406000e00401c21910b4586a050090040d000b0f840c00c0b0340c40e40308550220f1001c4e4100720440b680c296900d40110311b0b550303030400d056010b030404c86800418400c0600000000510a00510300942800200161202d280c00000404801c5c041d8450f03400380070402030241410340c08140a0000f4042c40007007a503d001502c9159141316604044202ca41d18501c04d1020180c4d002c185a400c83d200b41c0000e10065456004000459413035200d80c0340c050034200404a1480082001610708034018000d6a0800c0d00c5901e583c8900104011a00401c6440b07900111300c968100c4004009041c1c1e00724104030f0481d144d61032503002407060280c00150000800c4140f0510910303881903014040c00f520650f1600002409610b15822900410f100d40c001242c040000368030000c2c40d0004282c003d010030050303440c1c090210703000701541c40058a103038134402808203505000b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 198807257 1250 198806007 198806009
    0x92103050f0c072309040c140f04020a1d0301060b031f0f0306050109140c03040f0c050a0e0117010b0303180102031e030405060610021b03070e0705030108070906050d14010603020604 80
    0x122a101109070b81c85800141300c80706403000b40e441400c14005000104000401c07000c190740e050420b00305c1c04502a4005034044034200030803a845400000c14640c2a54007508a412240000c1000c9419078080010035090b81d140f4003c1058200381400060704024052004a91144005949580040e00d410f400645541650815103d0948a070700400011007144100100c1c2c1c6a120348072800790800c0440c142c0c00344005800034001c17040c0284040d040c0075a48001c0c8d001800001c1249194540c1c031010804065400d20580041400349841d0541089060240d0202c1d00d600070080c1d89803030042c0030704000d02c0e421015018110b01c418800001c1c540a52440d51030113054201d5515184c1c0390902c2e0032443e080b13006100c0740c01440d420311841c4019030000b074040483c00c8458007094059500d0008203140407a40c0c0d105d241c00700c04c2d001c03c1c0202d140d004801141071b00c07120400d940d942e035151036129003651114890103810003605140c50303001c0340380d10804d54600324a400000c07400c15602d4001034425002 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 198808507 1250 198807257 198807269
    0x30803010f180605060904200315120102070b07081305100e010c0e21010e060f0603060109090210030c0509030111090418020a09050c0f0706060303092103050f0c07 72
    0x1c5400900900880310520400303580c960005010550420000c10814003a60808070300458840180e210040c00042150820180713842c40c040d220310b480d1988a4408001c5c0020600a90b0b0b03003002094050018003c60300d40d182c01098204041d20ce42c60201d89800f00180000102e0b0070040070b406c00981c040c0b000122545007940041407417001c0c80703042800c4810100c0c0d45000e200b400c0942003e0307500c1c0d149000e0303030300c0d101e803551314000c444185000350141544824141403409190100300d0034a4800c03aa09010f0f040580440700d403030fa220040d2000301e620182010394802541e05460b90801d201c0d03080305c941c0843d1890201c1c102115080401d094803144403140100c0c11020601c00001c0c05d2521615001915104188048507144c1d008180c1da4030543c010b00d40c8990f180c600041c6140507070401c446040450001c1c1c19a502454200100203141d5070204500103000e800d00001e0140145020f00c030848003980001066030020f941c25903c40c1c0c007520309030100590034003401c482000c00303010050007400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 198809757 1250 198808507 198808529
    0xc07032d090f05010f090b0f040503062e0e01050d0212010905060402091f0308070309150801140108041505090732040e101a04020319050a0e1b060403080301 69
    0x41009002d00380e544454001078100501c0480007404164030200c0007088031032408030a0342c1c42055042c1c3c8803840c032490f004207425201e1141801055031803c180b0900c0c0e03c00c10500444041043c4042c034480300141e01c100d401180c200c000600c00c6180801c404404244010101800881660441070948458100076034950700b21508010550404001c416400402c203d80450802c0104c1020144482ca50001070455103020411004240c0203006050142008a04401120028071002014071000340078648041080301284003095014800441c003035540010000c00600750b151207800140750045c85141d0b0703486020b42c000355000301c21500c0c281000d0040c054004030401c906407034000c840200e00c490301413460002240d048c03450106e035582981803403040c0840c14099615001c40101d071303034a02003a4024030001c188030280c1d48501c8080c48803000c040f030520007036680c80004021540200c02c600d40d5a0061519507882c2d284600034601c881c04000c2c440c80c10662280c071900c5040d0001d80003541c043c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 198811007 1250 198809757 198809759
    0x70e0a08010f0c08060a0303050c0114010b040311040902150306030a02100513050901080604081804060b07030e0315060609150307171b04090203132f01080c07032d09 73
    0x16480f0b0240b01d402040703905000c01a0304160001c510544a82d20010702001008075102c5160b030781c00c0d040f00c46ca580090585041550311880810440d0348948021551a40d5038005814181058000d2800d9903400400c0da003410009600a0b0407584c3c0010461581030003105813200040c1e46c0e0b540203100400465840c0707a00c440e03078445046103599440c0c000d103105844082c0100728541c00000d05a9020341e01500d401d813115800c0450480c100c2c6026402070b806400d000380422921520806408100c0c0640c0c0c40955a003c1b480a242d00d90301018111030307001a140000a00c00d0410900901503a000601111940918546014010342003511004001041d039424846d030300300d00424260b008140d01d03441c10316603507000d004000c0c907100310f1144042041d004030014501c500001180202d168100203100512045c000300811001d411210080c010f0040103028030040d445100c120b44500c201c6100d4524220036070700e06032641c00d42911500803031850083c92104110f406150301d5003400d00381c0c840e40045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 198812257 1250 198811007 198811031
    0x60c0f1309330b0702010908120a03061e090e1005180f07080c090a09020d14100c1d0303041707051302030402131d0102041d070306060c0605070e0a0801 67
    0x18508040900d126440d0142000c91440d080582880440d50b403c1229965080030344010303214880541e21208040c060205100607134030000c402040220210350b0100400c90700c800d800803030240c1e0710201d480c0381d104a0b0424450108240e0108240b4103c2204540743c21a4049102040d1141101d406040924a6a440024000c20404491040701035005804a0750412840310b60340d1142d40100d510502480c0007280422145521042c40a40c000d0501c44807400107061a9500c0c0700d13844c0507210640708100e1201c04000452154801e000c0f00c1742d46682144a80c082400500b03903403114160b0303150000f084001442101110030340710114009001c0d055040c50501040f00480120782803156140c010401c00006a4070031800b09032625801740c2c00940a414160041d220f48402146025258400a008519603007004112104e10a004882c00300700d0f600d48008405607600c5109880101e422080c440300000d510f81c0000390f1000e045d10b030155502c00054000b0b600c031441c03940800e1031039558100e06080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 198813507 1250 198812257 198812291
    0xd0227010801150e0a050405070201140f07020d0804050708010504050717060601080103080313080c010b04050105060a08010b1e0703080601030c0c0203060a020c16140a080a05060c0f1309 82
    0x20042401c240d81c0c1c0c1e40c940b00020540c01c02038031545040164801c1c000a00707955160078400504000341c420440d62910450180c000c080c688541c2000c05c0d101c40c0090705229800040921802981c0c0c0a005000f0106c4c05c207071141c401c050000c03100c5001d0483c2c0410044403d109040c440c0f800764006100203850705079030080e01d004c01c841102544e00040d0812070b0707a0b60031100503411a54001c0c105a980d5840c02c1c0c210720030341d1400b0340c014000030002407010f40c2c844054204156203c4122001c100c16641c030000c0043e144144440308011800d50760042002c5403400006d8008030703810545602c014402c8a00314400c56000c2d40c422004030301c4c41c90510883d541c0c1031081c5000b440081c04c04503140041a00040c0d034410b002403140340003a1f000104420981d80a22400e58484c10f03030039400213190384a07402100c10701701501c0c071035004040c61271000900c00400544036030f005403c04003505054540252818a69000710f11a400050003000104001000e400c545070003440c0254000030b1402d4100c10b5080d0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 198814757 1250 198813507 198813577
    0x13030801090b0a030f2901150801080c0105030718060302030403090e040323040f030b0603190309030b0601110d0207050103050601030605010e0418020d030908010b0d0b1801020d02 79
    0xc10391034080202d40b55198000d141040d25003000b81e002c030880f807602e0701180e04a000408051081000c4880c040d079121065440c2c0e042c0c031840803800801907100d0008072040d040c05d03c81c032540d80d844007450b081d07154000e600454004c40e182c43c3c040d0380f52a218034080c01e00246903104000080d0300000f080700f80341d0b0108442025060b41920f0b4580c509054400404144250b001c00c4104e0b10040c00b001c80340d10601045500808503020003940159403410101d41d080012200a406801035540c403101010310380007400e250030b074152240a9004e017940c4480125010092444e81407014600d10b42c02d0701070782041070b100c4144180e8010300c0800e0610b40010195440a400f04e410706080c840c050106d41e8204000000012090305d0018080103490030241901412140c00794101da00807502074145030380507141d40d051303640c0d1700700900c625a8987c0074041c1152100c80c01a10154103d00410019201210060801110400003508082d40303915404120b91040c07103c07200741d00b035030705880b1024020100b2800c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 198816007 1250 198814757 198814769
    0xa050702040513080a2f01020403060501060302070b16030924060e0606070b0c0403120c0302120f0703050711030115050a080622080f032d0c1603051213030801 70
    0x2000d07007650354902c2280c1c040c070110380c01800124080c806c0410804000500c080c4d0b054104181d10414413603501d4001d500c00c1c08140d4001d41058008240e06003e070007200e038526884201081240c0d2200c0d46d00811080381c01c6010109911303000010007140001c140c1804014003461445501800607030604125041544840d220400f44000c2103096aa48020396410b80d800110000745641e0b504072070300651150380c00040000c401c0c2e050040c80a0780c4a0307030f5130b107400c0d00c01d4080b0380305d00b59490b6000c0800d0007140c1185031824030421000c00007034131500c00b80c6840c2d44207600c540c0c100c06c403241c0001c0c00e603050f41000b412841f00c00401003186240001021005001c2c80014041c1801c0004681112019403140c10048003804466201003101800441d251490054106600c90518441c2c0a2816440310820b5041c291030408040f000084107880b40e0080c0282e400003458400d442a0758206809080f50035002d004007402140100d040d658882403041d084a030040b1300c401040d02c0e014200980c107801c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 198817257 1250 198816007 198816031
    0x9012a060227090612010e070815072c0301020904060e15120607081f060302041502010212011e0503030c030309060c04030309031b2d0503030f0409150b0a0507020405 73
    0x280500f0f40b14000503130f0f0041c07000c0e00d401014403191006640540001c0e12005468444c00c43e0004903a08086580401480410801815500c544000300e0703000006209421381206081e0440010f0315a4000304029054042c4c00541880c40200c000f82c100d40f0182c0c05001c1c01ca203910200120301d4078154200113412421554410180c882c03150301e594428006161205102008011455440516120044440400c00070240643d11030200401a4103c0e100380744001d880202071000700d60060003a20b03140748152541c141240c0c42c2c8118240c8100c455074960841450b0400080703a251410300c0100b03402c003542c800560781d034182001c1a500c0d151000f002c008125a050205000203a4020704100841c2e8000040d04109039050010b1a02800c966014907510780c070407032010841c20018100c00c03048410044d11a41403650350300502d0745a224402c40c146000d24204418072100140360b0041c058034103100f002c2200b541e15084943e0300c42e40090501c802082020451002b1072a2a00465030701c8440e40d142 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 198818507 1250 198817257 198817327
    0x303020f1513030302040e041101080708070f080a1d0a17130315020d0c030e151009020309010b0604060203040f08370b01122609012a0602 61
    0x45070708900c02500d800300501c0035045507014144a07405540180c142540d6540341740c14580350408031b82c1c01d00e00940380031803804400a034800740a48400c5119044a440d482c1110251040440302c0745801405022156500d07000e0010785800c3c1c801034012449041d000300700300d04550822001b40c1d071884001610015041090080240c000700d4400116030b40f040d0000d40c070809607182d9401900501c041904858030301540d110003258513811880400700e1341416641c13408011030340301340d2031141113400f102c0c0414582c10030420740c1c0c3c0d194000c40e0f10a21207800015004050400210540c2c450360083e0016800440d0074050710800b4041c44000b40041001450b4906810b500c4221140050302085134080d04004031200d20b180d0603841e8135130300758030113014201c941c1c40c0c7d0620041ca07442c08900b035500849105400d03c0d04c00c1e90002d40620310056030081c2d810a0314503401116211003521800350b507160006c1030126943c00200c031800312288950405a10f401464400c600c201c8200449170341e9400c0d8102c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 198819757 1250 198818507 198818533
    0x3030a0c1b02060f03040302030d11212401021608010204060816020d05070602070c150e03150f06030a050312010303030f090b0106050d0e03030103060903030e070f06080403030b09100303020f 84
    0x100d400385880c84416540301c6d59a810306a045000b04200e80b01c0c503905040038100c2c03450020380103100c0c00144821149144001080d418215241200d100c1c040304d0722528a40d00d82207484240c0344400710144100c82d06d4030310788114440c1c1000e069000091907034004c103003489403940203140780c2d034030078510041c41140740c0754904020740d0343c4083c0103d4030612000103102000d20516404841d103c98201e5460350001da0b442001d500d0000300c0c21240e5002858900c40c0003564074020a6000301490583c003d9500e903180d071080c80d083c8a60240c00c0f5036040c440c1c13240c202d0008106101901d140c1c80c0f100c0070000a90314606002c0c090b030b03141d401800c103014640f078002000210000241415908070303140039510362203031544102c010806800446c10318400400008200100354001600e014402d03075082c0b01d800f80302d507440c0765a0301ea14080d00c004010b0700c1c0e80500400f0b10a40704103074003034060320b0003007522031000012801a90302511001001025030320140b00f8550100240c0090f408084000c001d80a04c0b85 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 198821007 1250 198819757 198819769
    0x3010b0306190b06210105100509030a110102150103030c030206070c1e170c10150e07030b010e0d050c040e0f0c012106060507060c0f120203060d0503030a0c1b02 71
    0x1105400626a0f9000a195540c03101e10960790580c500900640d5006000b44418104100034401d0b030f07124017040001026402c0c41f5105403801d00502030001c1c080e480b1f1075610150401000c500c160304522034210440c00c9545507249440c0250302030340303074240c0444181c2802800c2503001445d02e41400b00b2660124002440b02101003c0b002179564900361401043c9404101051a14212411a000414420034200300825041003c0e110380b03408111000c3d0003e901d0700050000e12030941030264070000244c407140242c00c40e0020400514041e0b00074485900005e03c0008175000507203959000f00407100c05404c00384140c40811100c4402441c2e201f00e480c1c11980c1d200500a0301c0303810080b14840c15100202803d940080e801286901409940d88503400217120350002103090382c1503402d040c0c1e603407262401004c9035017081038170340d640791070749801d480005c40a544003411050f0801c100f0f0b42494080781040c4050341c00ba005141d404640c0368a15800204040100c00703801c1c400e1908581d8800050390b0b44 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 198822257 1250 198821007 198821041
    0x5070f0912030c050f07141f230a0f0806030a050c012106060206072028060e062d070c151b080a020703080406180611030603010b0306 59
    0x9480c04a454411440c08407502c5150341c0000380244642c0a003103025460101b591010f80700541d00304843e500340041007006800043c00c1d4145002c82005c05d122002e442010501c0010010002c0140301c501607540c6070714a54450502c510004010341c0071045041c1c1e10036002c1c0c0d0441d40450040074209441e0b1a0a52160300c40b510482c140840c1c04002204030714041d10b0388604c072140728400c010180e507850340651181d4044440b480002c800c60000000a80c0100c0d074444100054401440c0c485041e50040c100e80842c500290701c0344003502d07550f00008006006066101040d8006003800b82010300f800c1400a520038050a038002e40305030303681780084801102ca0350102d8245800032900300141001c0695404c8a480301308800e092030032110f0500d922006540e841c80b5a0b0340c448803a0390307810017040102d00601400400082ca500003203004100181c0050513580c0000b000c42000214940d2010111011003500b6020300902108024036440c0c00c1c407942000710016405455140340005d401030f149003071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 198823507 1250 198822257 198822269
    0x31608030d140f2a040305060103020102070503150112080403020904050c011103040302010203032427100b0d0e07050315010e0a09120f0e09071101150803091c02040207080403050105070f09 83
    0x9456030000390360303188184202440c01c09404c1ca0740c958032410035607200c0a09000c00d80c0540b0904c10000382038100082d0000c2c80002d1741c0c1c00310306a07908200b0007407180740d600001a0b805d402c1c03d02c000300c0907a41c1c0b611054041c522034030007050414101000544001a40200008250000c0c401000585d8011085942c4800039028504c1c20b90500c0611041044082c1102a000b1040003a03140502040004a50700191012082c1e440e030f0303039076450f4141000454007038506000018080c1201211041d00070800380e00460b000d45e41d400e51540b010900d05400403040034407101c10000100600b004200c0b082d03421440c0c2e01020312103a003054a4210340f8145089980041160a140e2984141e11a5528a029070402072801985040603030001309105071447c04c0e01c01075403902144181305c8006188400071a070002000d075082c4900072040201d843d10280d406c500c41c0700c031041c68000607500c0d440106038141c492045240c84a09505003a400c50390020280420b11070144901c1e004103420485070011509 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 198824757 1250 198823507 198823531
    0xb0a0f050f04080d0c05012406180b030a0207020112060e040312111204020f0409030e0402070c150915030605010c020906060d0e010203060103150320031608030d140f 73
    0x4115021442d210310361003884030b4010702c2c40900c000303a072015500603124003450003400f440c40381d080404190041c41d008a840090341c160104001400740d40d20b400d06011038520340800942e20800c28585502c00c860100c0403d6001070050110740c0c201401c00c0c8084100402000035504040000305d40d040e002d0405820b010320b0341420400000a50007840d1442040a50a40c850703241d0000c1d89280300c0e080c2c3e800c901c6250342d8250603001e41414814003002c10f40683d50500800311000510009510121003035444049400c40842c483c0d5038a40210a0b8220325135402c500e40d07151419000640e04c0c4464005c0c20581032000410160381d0020011065680440e80300e061900d50070f0001d07100e4455120760090b03041c2488041000654198050b600c52042070701c0620100d80c20020710310708107296002c004c26403000030707030700113481481c8560104038428098111480c128005c216078440001e164040b008507400020807224001040c000d030200094014500310303150070f11010920061400800940340c5030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 198826007 1250 198824757 198824767
    0x1a0c0c0118030f0f140105060d080901030e0a0f0507080316031404090c030b030d09080312151306060914100f140f030414030901080a050402031c0512010b0a0f05 71
    0x1c6440c080c10005580c040b8040d1843c210750300d402c4003002e260500c05d4400c0913020001055000c0b060044912902000f00601540034059544966a40280070440d04056403000c184404410400124400340c1c05014084d501d15910b140051030700c0855004140c55800c240040b091005210980c03840c000c0c0e050801e144958401c0c2105c202900880e03110030385060400850080ca0f030382540c0328445d100b105a003980c40c58484030100340e4510b08140f19901c90bd5004004c00c4603c4d551450b00300c2c1e005061808455210300b0700c080055990022000c1681e44a40d071030400f0070a070b03034110382c601c00200080840c2e280700d0003400c40000d90041c09c12034001c09201452042c15100c51003000ca07000c81042c0e00500a480702d00712001c940f000d8004407411507114400b8400240c0418000040c1c1b110188165104120b650307990120b84054000904226094440c11503c144120303090807142c0c034070090558440e03485440b01841c050102506034484071025400700940f204441d400305100031880080d003800b88c1c5d62 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 198827257 1250 198826007 198826037
    0x10b030706080604200901030c0203180904080702060c16050405012d0f06020c010801290d0b0301021801032a0f180801020a0206070528030905060a061a0c0c01 70
    0x5020004034455105a285042c0c0040b406400003500e04506c0c2030303034104001448054140d94034881c407855480c0454150202c29a42e2030308580d000d5110f44584500c40c20002654007180d103a8119001c1034029410495000c00d0390161507801c4402420700710f030140b000d5490111002c0640c0c942003c682807420304500054240317026450120020b19146848103c0e06942d4a00203403103020104015000a014800001d045c94818030b019841440d2040950203000c1c07241918007841d4048400000c44070780392501c080342d940c0c003071010b4800015079420090081341e03078000041c01c0710041c207002c0c00104d0102034900180110304000481064242c20031808034490b625050300c5804074080d061030402000c0304081039040701034001e409940c480c0e40803649207444030702080ea210b0103041800ba4400c150241400b9200d000a17107010388141c441e040008140c1855140c45042041c111207450b9219201c607801c000711001003041e500380180c403601c2c0d98140106070350086c0d2640003059510741000040c200003880d07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 198828507 1250 198827257 198827261
    0x702090c070c0b0a0216033e01260a06090506011e0302090409080d0213170307170d050405060601020607180e0403090f0e06040f021c0f0b03010c03051602010b030706080604 76
    0x1006121b0343e100c0b9925175074a400e03860307003259080350481e034041d4140c00c60007190394580302d1107007410051720550008111401107030311414040b08004502d1a284141002c00414030940c5e00400d0f841401041250800a0080a4aa0161205041160703440500044500081590358821000c1c0b801580d9000d0000c0050054450010b01078540c180001d007082004400b41d0042003100a0704140c40d079a00d5580d805103014601d00302c0f11803030a4000b080040b0001e858034004ca0000803881c0c0c1d8060070400048441c0741150b4003220201c500b54440c4080c01010f41e010070030039910000f6450303c0c44044641c0b04024140304c0851045110030040c8a010070200740c01500d000c1c000c0c01d0341c00c4070740c0d166564071580508619000d84078107004910302030811601040f64000c54071843c1c0290020540310440c014100014000711207a80d0015075200503000b1a40d5081c00b50b91569811541d011034281401209100080d0f55107242400b035a14059450019071004914034007220610304000c42269070303c43c04540 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 198829757 1250 198828507 198828523
    0xa0b0609060c03120f09030301030f1a010303030c120b01050d02090315190c050a0503010e1801020f090102061003050c0904050f010f06080607090e01121406040303020702090c070c0b0a02 82
    0x16005070302140055040c0c000101800042c070071810345901d1522a5900303604410010f5810f00700980041005201183c0c1190b111301e6020310441d1003d9003a4859480d840848000f81c204400190300c1d680c52318405035103d02059005c0300d209004100080d108800a0054481d010501e034070702d6004075001080b40c0e014080300180c01d1040a020030700d850103504040c000c118841c1703c000100d2511041c452201e200748150303101c16485441da1031869083c1080780f610803100400d0412100c00d4080c001c25551002e0018110725840c020308644c40d51022400642000402032100702410000b40003000814400034000c401c105040c0d48001c882e032601c2c200541080c0c941c040403501907080c1074034911541c000c0e92107035003100c1d00401580d840780c0b10041c080307411240724441d004e0207062110040c40358803034910f039098825100d04408513140c506421403e082100846003a4082a404038143d0150300b005c186c440d60004204004628200069030344480b202c2c20f500458054000c0030480d28004ca000301300200c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 198831007 1250 198829757 198829759
    0x2030607080115030c0503070507050a1406071b08040308090d08040b04210b0a0507090906080309040c1715012105190e07150513091a0a0e0a0b0609 65
    0x40140c5060400600310000030b100d215504114a20301d0380e0b0f01880782c802c1c11102100b07580c03402d195441e03a000458031600506003e5681e8050303d96a480080d1142400840403002c601c098940c924000101800203103200c080d0001d10070010705100300040e01a01241c0c10b03039900c0909252254075100102e10426038050740180240c82c00940440c2107401c102c0500100c440c82c1540e403054590b1845048a5124000002040300030481c001c20320741c4045412040d07101c0380c0c40c580b0b070003160b9840000c24107469081e40807041540001442c8800c0d407e090081c0319201d2441d062518018401c46803200c03000340000c10760303080c0180c02c4007482c4050703101d040110f507a1032001c200ca0306a0040050100000c18040c1c54030a2405494100c491245950b80550981c1010704009132550b0752a10400d000404269014034040000c200510740c0310b0f003196070111001e80080b49000407260b60310301d5124003c0080f0b442951250100030410805490f09001469008050303034004105a10400d021880300d01035042d4031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 198832257 1250 198831007 198831013
    0xe0c0306040c0807051516080c120717030103051509030403141c1404060503130209040b090c0604031101030c1106090a02090f040b0601111504150f0c0e010c0f0203 72
    0x480140700c01d40002c82e060b16103071010744140b03a5503403041298031140d0380a10190850f042c003c08507a41d10070103025009501481c0f46034036200c03243c00f60b14141010700d24850709000c0040742c01006c2c00390300811140d0a04216110510315411522410703500d080703808544480000c0b840015824010038010345004503030194216005c03220407504141c880124040f0112140d58014807000f4036886142644401c0341e060300790a141c2400d19204585030b90000f040186402c10301ea00c5000140c51700680548140e0043c2520b8090703042c4200e640b4244500c0210f46d9104400c284410f00c045000c030100aa01d4001c00d08001490404ca01c000761109110f4401003da14051101004401c2c800450b00824062080340e80500310380d104d0703d00906070501950701510140c0300e40e000079400d5020f101e00303540882001c0e04641c03003601e000c3c040c18101e1804440c00c84466201080d000c400c00d000b40a035140105013003000380101d44840000810718496004464104408507803a4000c0c404c030040e501030f1007600541a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 198833507 1250 198832257 198832261
    0x3010603050a1b050d0c02010605090406050103120c0506163b15030411060412060f0b030109020904080d090b0a0605030705094303090c270e0c0306 65
    0x60018031007202c1a0401c94144403044a050441008207541d0034041e880c0d003170a00a83c5880d880c000c0a207403000ca8255940c81401084555503824030a00c00c5d03101d4540821158111301e0402810301c01d9070303c45010310600d00c610400080003c500107500c10f421011840403a2414075089070140d001600c4180d00b00740701c10380441c40d8040c2030000580151110003441010640e1424801800c15907240e01100301000c0c408a400600a0b03280a025810011701c3c082c101603e80020f00254103104500311440355035540803401c5804103003c0c61846003001c40c002c11036000690040f83c084a4000d00041141074001a0b1800d44001944008190f54112010903540d1800c0a40d0340002e18190142904c20b100f41d68001605181026800b0320400c6400c02c00c118040d00d0860260480c0074041311100b0b1504080841007091240c0c0340d03031400c006030790340c1d001c10d080000d41800c100a450303e403c240404802d00d0200080402c032600070048869000c07000198040780b41111a08100c4440c411562500403071003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 198834757 1250 198833507 198833519
    0xf0b0f1e190b1606110705030403080c0109120e0a0e01080a022e0215090106081b0d02060a030207020a150e0616020a0f0303080f06010e0613030c090914070e160c0203030301 76
    0x10040f070a441c840e140410092800000c1c104450055100080195004200500004014501a00101d4015000452040c103140d580504045200c0e86000c0020507d040000c4103252480c0c0000040a00c459004510750404100d603072280c200010180c00340001d58562144024140b00780c00c505450f40032590040c06041800944503c0a000d94550303d109070310104a40715010322400c0d00312600c6d54010580c171019402019002c410300c0c0c05099010f00324040c0030016072101802807081f1090360750b00594400051041041c050816040520300002207694100d003203401410050403410100c0b8055203915101f41002280f200c0260b000750002e9403604001464851009524140d0340300f91681583c50f030b0f900c5808007403c1d208a500310700103442c0d0615040c180c2440c2005181a00000107020031441d120340395150321007001d510000041c0d0380c0301c01d61418032010f601c000b030250034808050314003a403030f000303610740e0001020381807001950206505605140c0a4440204580d5000e0103403070701d079a5116 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 198836007 1250 198834757 198834787
    0x10e060c01140108030325020c0d0b0711070623040f03030e03061e010e040515010f1802030f0117031207050a120b0a06140d0f0b0f1e190b 61
    0xa003102c29070916000810825070101c103aa01c00c101003e6800204d402042810303810646a040120660003a4000420700303448040c00d001d01c050060030145002c0c03c04000051014048110704407180d000f40900b886400c0d070040100c074486146184980580c0116154002644150b03800012100320520380003003099006400c03c5021003084080d221203689411090f001704c2d250720811103101940c070005001c2d0f01d412480a68119004000700c0340c00e103588031501c0c55824401e82001586481c103003010002e940031f0032224400118121415402e5092507008480d440e0011300440c4900c900b010705141049904106942c0e0150080c0403410860521440142590784040c0344080001c00d140c4070b40c6500640d6000384851001c02901c03c0c1c05180c83c1641c2107030b0344e00003844400b45502d410031080ba82c0708001d0042c411408a60040000e000681108006000c0c02404506025400c0c0303080e8080c003c0c44002c80d0f000c4044041c1e03860b020442003000d5a0b0900c10143c0c2051038444004590f00101803041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 198837257 1250 198836007 198836021
    0x8091b120f07030209010501090b0d021606020310180908040e041e06020d0f021801030b010e030703110a1409150a0b3013110301060f0b070302120307050d0209010e060c01 75
    0xe0b11004500c6c0d8a0b140111340b032181034007d03c2200001048072121070002d075070003042c0a0f0340550302944510002e694840a07648182c9040c102840041c005100e03450303424409000f468400c401c200403058955941c0c0c515402144140601007500400280501c030310309543e030004201d083c045100022942c940000250001c0d00000138181c5041403900c405411131086906003009003261010b030031641001100039144590301d590401c43c542c0701d030012940f01000218051807040ca0340800d20032049046c0108880341d81c0c44000b0703407500600303120021303100c1410f116008007040e00d01d440119900b401041081d003260f40b004803080c000080b01100c10004100410020460707030718400b0b104203030b11040c04907040c080d5848184120741e02c06800019607906130082c20000080c0021981c0c941e505400001c6159540c00910b040000103000000c141e810b120b0103010300d80f9000094298102510010911b0103004452449294006002042c40c0e014401061070110f00510b5280d542d4109192a0702034510707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 198838507 1250 198837257 198837259
    0x708031207090e060d020d06020d02071104050f0115020307080d0204051c02150c0a0507030302060723030402060a1b20031212040f0615140108091b120f070302 70
    0x84040340e1114820b00d48201240e007072a0f0680070302e0b101d0100b00015240c038070100301c0e44503031805500301c00116980041d0440b211078900c010f882e556241403005040f2001000e903485280b0b0102040030680c20070382080d0640d0700b2903200c14400e0450440983c914840e012003e440031001103414036a140c04c0d500100181c0f04103444147d051880c0180a4010b910001c10080d80108030359002c4002c00c00d01d801900c02200d219040341e2101c2940e85906080c141d507074005500503000b200401408940005040b06040c10040b81076100c0c110078800481c9038080504004d00c28800018114841442041104070742210590010b4062000780341420424203810740100c032811540b0b082c00e81c14500440d6495901007000c4d07c140c5013003c0000090503004c0700610454031000291018800304200e407081d1529003002d40301c4c0b240114101800e40b2040b8914200035810010500c08200300f005000c22440062040980d00114070304601d40040c81d415445a01400c01c1d20030301030500b1015000041003011240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 198839757 1250 198838507 198838537
    0x1403010906170a1a0a1d0309011103030115080601030b031b011e1b06022a01290906031c0302070b0702010b0d0f0c05090108030c0705010519080612070803 68
    0x9404502542c5030303c0c2103280079000b40c0c2582d80221039060701c00005548000094400a410081516500e103000c5030307108005003a902c0403802038640d58104071928000e446000c021811585031090000703015980c48149030400083e60081000d5900a0700606034400c0000d0503a01c2921512003020181d6001c40041c81c0054840764014020381c075080c0141062602664034100240040740341c105039584c005000b00d4846608105002d11450031a50484e852042040703c078556030b1034240d805003914010404010051110020b18080c580c050409480c42d1201381c2d00c40c480d556034140042c0c201540806150a1a00d04400641000e9407590007080110f00c100e03125001600c4401049080301c07218190550003400d0300e141000801c00c0d120301075201c0c910600b412070156440c1c04c080b800e108402c0c0d004003140d600c0407410508102c018080580607000a03c0c21034140440d44000100e08031008000e82e05000e081d0000c42c14644403001d54180c060714042c21242d5490703803030302d00301d035a94029a003400710b2031 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 198841007 1250 198839757 198839789
    0x50f040b03060f010813110a0306060b0a0e03030306010909090c08010606110708012309030f0a030f05060409020f0f1305090d0207080309180a0e10050109110c060708071403010906 79
    0x342c004c0d10103600486d02550a820901801d9483c0c6030381c030100e0324080d940004000070002c0000d42ca4020030015007070354910b19890305483d02002d0000c445143e40e00d84280c006108002c2c0b0384c0da0190020007166032400380030a8000c0d881c00c6c181c1880c180c60700f0201c8154248103000c106117401624181d9010007080c100c4850665500700d60707080758103161070050040c2881c0f42d60103030440c180e8238840e00702c61044152881c10011803140150341d4061079844000c80d40f0f031804484948818450594080000d0320305220100480d400941d80111000d070a901c03c8450803000c0031151500c001c0c5a0581c61980b40c20802811303c0c0d60740702ea17586c2c2060f41000c0148107254010855036000f00a82d000c01002038003807510703040000f5140b03400c003d0052030807044c0c955502c903801c3c5000040121101079000c1c1c2a0000300e0354104a40c03141a500c07082001d4039110003c002d0398800f550000ba416a002c8681d240211058440000884001c1c1e45030030350080802c00840045140d0311507a102c1d5046400c0240b16825030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 198842257 1250 198841007 198841009
    0xb150a09090218010f02070f0807030c080607020a260318012306010c17030703050f090304050d0807061107080913050f040609150207140706030605090115050f040b03060f 75
    0x19100f1146803403600441d07502104483d5014050001c0540860b00680703030803030307140c50780118812519848400d4030350243ea001c100703018008441c0c8000c0c003114006844030f480d203000c0207903944201c81d00c02007034004a80081d1186000003000c600000107101c2c201e44da13074102059003255410624010b040c155291005201c04504018068100c008803035a480e100355850200664072514510701c140d03642100300e40400500400321000703500c2a604c6407000100746c2840422071011041c01890400141e0003080180425075413107000100480e800105180c2c2c82c5410b2508501a0166007800700c1c11040105100b020004074078040d18405005503103c10805403104c10b03c0342900c10954103c0610b507510008100464400c3c2c200040c7c0c0b80c0030315007220766410b200a216040383e03c0260161690480e0483c01d0f106a0000d02a03440100000d240c03d002a6007041c00081500c041031140340c522025241c3d00b240824000c0e01641c14001c80300341e42d192160b640714600c285641c000c0b100241304905540f085102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 198843507 1250 198842257 198842261
    0xb01030b010c030c0507050a0306020315040b0303070b040c08010603050709140708180a0b0a060302090903131509050d03080603190b060105070f020319020120061302040b150a0909 79
    0x31050507510b10480a0964405a405010181050301c1c103000c0c454004c202d070786961150328011486080e005a0301d1030814442505000c684000510880c28164510710582d400010f4034801074004504e482c280d2170318076103447c401007141d0081c0155400d08ca40041030000200d00300c3e04a0b6640c0809200d28901300e28002e40040080340c0c0080800e80800100d20036000105100e48003442e400304a50325210b480d01d803458281003c039240e004940e1100014000c604056506d40e4000a1070402181843e444488820b980c81c1c1c140119180c0080b11084598003a100e614520000c02000e00701004290301410000c01984040321002d010380300c0c0f941d40d45d51540074001100d00c41500009024500e40313801004480e164030000041d583c44021340701180143c0d50900401040c3c0708070500128648540740700240c50000034020320450604410350000e50080040333880c5901100000003203646060520014004207481c1700090303080000c1800549040000301c0042c0400c8146442c6d0743c07a465522420602 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 198844757 1250 198843507 198843521
    0x150201020913020708070506240109031e0f0b01090f0605030610140a05060d0c08060d030207030215040e0a0501060908010605031c0c15020405011206051f020f0708100b0103 76
    0x3401c02e5254503981c016841603405000c0e094411844a860410184c50344c82c0350031000d0f20011402a1071001c45e55003002521442c1d80285003e09050810516588132a0380c44079040c001201c10700720700402001001880038040d03002e2513021020413641c0d40c45058481c02025040440d0320440d10302000031079580350000320244100d80d603100b540d031824200520340c40300c101034000c445c0c2c001845200210b400c0e524500a000348040f034071000100c210385031400804114010b81100c0c0588101170701500843e03800304048040e250159600201e65086c0c030b00e502503500c103541c000902c0c4c40040d0142708240c0da00da0080c60490742c29039507002a454441913903500f29641842940d90580c00001070452405101850280e00001420502d03101c040b01d03241c03040e04100c80514440707501d50000f000e000725a080203402c074052105013070400015080c40003241100c0200128220044544554116054400c00a12400000c100c041d9078a10b0354850000c0da40303502485095551604081c10344645501c89d02c2810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 198846007 1250 198844757 198844759
    0xc020d020c09150a0308030a20071506120302150a02090604380a080105010e0303071e080c06100905192a0e0102060112050601050907021002030f0403030f09020f040f0f151502010209 80
    0x40c0381030066038401801c2410b40b5240d60045331120400181604030080c20a0034030b00030340107030110140ca0101155910790007411050380c0c0744144a9001a84c031020706940c1680c820341400c1c00100c040014454140484c207100803c549c03544613000c41800301900203440701070000e0b00c5240c801e9807120019109080701c00800f0744c0560060250038049a01c10100329141140003070b92503202c00490702c80c411070307a0041d45000d105600c08002d01c01c031216440c890000601002000700518100403a04084080a40c0011011581c445104002c620000401003182d0391004055a00860145801034410f0380c40005090150084100024031400038480420306554480050700003030307080008110480c07201810190452042881c0440403000c0c500c029401420000d04001e510700e402d2078010103444030104420085410f005203500140c5880c0406c0707050b041e08a0b8081040c40390180c0c018000c0c11100c9a10018034140780001e2400c007000e040740c00980f484040520f03500010217400f039007030b032040550036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 198847257 1250 198846007 198846071
    0x105010b0a031a0d0302011b031506030e0c0d0c050406050105160224070602030f0117151306050c0405010e09040b040b040303290102010c020d020c09150a0308030a 72
    0x1049115200b903020344501126152480d43d80e201001c003161104032000f10480150b1340d91460b56812583d40ea0315640c0d00009460140800d200802c0c81280300280c6205032400d05440b45c1c0c415082000038800400c903840050005403101c2d4480c140038043c8003151103024026842d240e004104c9505c10000c991721414295030205c00b01c4a154248130503135004003a0403c5110b000701351700c554800481d00801c0308502405002d620380c188581c3d603140c54134041e0f2064200c003101561441c469900499403c161a9074000030034050f60320410038655032220144010f00346440c02c0c0c100701124011502400c00d17038000383d0314145080841c40c2441401c0009075005800304100c0d000141c00a02c800c4c0000e503105100703142c081031040c180b8140920310031008184003881202041d8148155909225010010856100800008141030806519481042019805040c481c000902c0d010401c542100802e9406424402c1055a03400c0004981d0401c1e41ea0309561410614142c23103d070082d078440303503821100510b9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 198848507 1250 198847257 198847267
    0x6050403030801360c0e10081819050a05070b09061213080c0d08161d03010e0327030106030308130201090305060c0d051b0708071403130510020105010b 67
    0xc028012101d941c0c11007900a00e60404800e0210f13182495030800001d140100700d04403200e0029000000d141c10340c42c0242401110401c40c42da00c46081d80d040b800c41000004070200d958030765802c0c00003504808402250100b80c8108002002820081242c00b030f00a5808032512461043d00c0c0b4810710b041d899202c0401d21811a81e00c24915540c0e4208601c0c0f001c035124000c103a50781000c0354101c040c6014076900008030b1804445c0e00a1100c50b0301078900a0701620f080d480b00c20141c08002d840c484024007072120a1056142c0c1c500350710820006c81e040048a460b400109400313248814200f0f00d442803591011a1050380d800d050140c1411b82e903058841c90403694400780d400c0d001054182d010b9041004252000012840c148112401001c412580e9603a40c01c00e00d050704166900a4801458010203100040040491078251107a403684503600b141e40700441e04100e402ca5116000302ca0351030100240308c1201020700294a01100c4041d0f900ca0a03c2424901c16400c841e024410745030040001c200c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 198849757 1250 198848507 198848519
    0x6110307170c040f0905041412160507050d063608030a140403020d0e0901051c0c080708100f050f0a1104122901060e0907090801180c06050403030801 66
    0xc91039884080186403d050594540f29010211a258020b144180d620400d100a0140580142014107400b034000d016000010703608104620a0750140d00e0006030145440042190910804c0300404d8000c00180e4901600d007080c00061406d010300306140340140c55100e601c000c15404500c0f40105910356010410380d0740d2034220407980000d00c0582881e585546505e0f076604000c04480c00786000f680103201c8000640c1020305811458102248582d03980d0004018941d986a07490071080d10b200d2004403101c02c14503001003044402e40092141e405200e6012070914000105034a82c0800d21605000720114010500c040300c00c2500c0b14581c2400050016070126400d810081980d4000680755141c01c1e503400c02509045500141101e200e15070410000c40c50105880000398032940d8903184905514183c0d014210040403440c0318099160000001d82c02409000c021000b01107002c003e0008848140c032214a12a080100303c0e0010300da80c0002c1115480f580070ba0b01502e9141c0c0b40e0304c5403a42008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 198851007 1250 198849757 198849797
    0xf0e07080a0902130b0a0b0f040306020705120c010b15070803070e0a050604090b120c100807090f120506090712080906070c0e09060906190507090302061606110307 72
    0x181240e003102d03201c509590040e1594600d82c030000002c44000103200300500c003000b0b5130654580c00850803442c1801001c103002e42840480e000c0b294401c03001691185a4038015003070810000c40041c060f400862910854001900311211220701102e0380f0303903000303180144e4840f54018030070013070050901840020080d1340540342c940d1203c41c0003814041d0440d5140c0001b119540a504041c03a03064588150050a08080d030078801703828601000f1b401c50004240105043ea00c1c2c40a05a00700101c24010a44842c01007881c08003406555884200c0607880303d608200069508800316000d00c520400a000d8820203d00942070b155142170f842c0321508603858030403040c0c10800300203900640403c143d4000442d0712b0385030300041126040b41031051a128491505040001300950701e85c0d0021010081a4100d0502e00400400ca200e000101501c483c1401c4030b203040590030094000c1d400142d6881d141500201400195105903418814080c0103405c2c00040c0c0030a403108404190025600108022a0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 198852257 1250 198851007 198851011
    0x6120c03030f0908070902120c07030c1b050d030c02011106070f0f0215010e180a1101080a0f090602030a0b0316050409140105010f1503051017010f02030a060501090f0e0708 76
    0x81c3c0760541079039807103c291a0800c3c081d0750204603581da00184502c0c0880c8800440f0f9844000c500d151070074424681c038094aaa000b400c0000c11070541c0300c04054184840b00c10b20f01c09010003a1171303040e85140524001d001286160780580c08541101d550820341a4009241485940c0d0b540c2c404921540d503440580714258090070840542c0256900304c110b041007400e80e10300070f100e60340f0000070b5810032000c20044c01c0c1890441c6006a001280480e020aa00c0d050811402d5401e00e8400d0740e990b00c109940c1d000300a10003044000504100e0144144072a0360047d502036240c0700404c0201c00380304030805d550b9602e246014800304400160801c403e18040e40881e06590040281c0d000c8008450100390843d9026040300d4001101d403201403090f0004100303005002062410108078030308100166109078840c0340714018420680c03007000d2210740300c2900a1020041d24410554403420061103810181c00d1901517103000038130030700c00000c0304000a06060101c62a2081151043e190240d04032016800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 198853507 1250 198852257 198852287
    0x10b070c031211012c0d0e060a0c05010c0206042013020d090b01030b040c0f0e060f03010e0304060e090a060e04060209011e050d051501020304210212030c0106120c0303 74
    0x3c014502d420344428060316010203c103440443c0c189044d038849600745911a50b5041542d44648601c09a80d5040011088281d030105d072055181c0d203040a045414542d9094001c00c29401c04510a50450700020b1141c000c91280b180508010f00c1a55400b10307201d00782900c0750b03000c0300b204071030448004142c2c020501001ca1840101d40828a83c41721900c1507420382c0102d641c00c60702020001407110044420340505031590110201c1c1e0f01e0880205285500035014502c0340c00c405c1a000300c5940c0940c411200c0a07406c00c2600d40307035540c80c0030181c11b071424041c0e50b5028202d0000060707070b454180d02c01e801c2a04c1400c91680702c5074440351203850013034008907c01d03410703c50000121401c074000c208035455022500c1d91034503501d4042c4181c00d42035880c0a0309451607e075145d03c0c4956503a8003c0151400c3c0d4030140d25003812150464805031061401440c040d401c0718004200e000b840c00e000c001001d022540c04024800c45548401c028025500c200015080c00c0d281202807000a1082c1310310002d07040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 198854757 1250 198853507 198853517
    0x708220224030414010b0a0e071b0c080a140c060304080309010b0a030b0412140a050a051210080d020303282301050102190b040605090a0501020d0c0305010b070c0312 73
    0x801c2400300141c540c07040e14141ea45421154540c0c00c60750302402101c014400a070351030003460f4900100030030210300c0904440140403d0402e542c01e141d101420101c01d040e000303150b00041c0760340d071551a51900c8a4000c00d652280c01142c2c0e20314070324000607240c6c04600000d8800303441d40e0788039103070036140d40c0001d04052200d54881c0e15244007680da8042c031501441c058510f10403d07051910f004580c00200524903000d01c44070280138120031003808144c580c414242d003480359882040102c1150188601203542c10a44080401d020350030041d0f504101c01e0b02c0c040c83c115070b4100b8501906903034074001111160851107600c039140c4c3d00e0f150041d0100203900706d40700001c03504803600000d40e030107084c481c030032480440c03219401000300f580d0401c03111048420788240c11403203c040da10781c0401603d00600141c5519200c0011071044074003004000905ca4100c0c0085441e010020b03102b20203002c90200c0400024104030011400703a1742542100c04881d0300c1510070030b40c1c510310b03558240511504180182404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 198856007 1250 198854757 198854809
    0xf03060906150708030a1d1e01200702010809070e010909020f0d031e05181c080a0203030403020d0828020d0207050c1017010614070210050307082202 66
    0x2805801410f6841d01c103240b03090f102d20f000340c13100040f40c155401580549000d900004036902c2c0100302c000150001c01c0c00c0c0007407074501d489140d000d00100710704411004d240c0908041c1e0380e06c0b10070103020f0b030f50b200340e035084502d803680100155610080d00401c403404d91040010044a01198130003880d50344060207410740000c0c100c0002e00d030440e078004241d0101b030302403200c01200c6100080301c004040786801e045080241410603a8000f82e5400e1741c007401b85807400004a030b20048000d0352040a41d004030140d41e11122000d00940340e030816107048025108594840c105c1c14010b1001310702c105599131030141d550781c0d202d081060304d0b281c1c0d02c1000201c5030b08000c441c0003070f0400d00041c40c03846d0088005250171001402440038603101100b0001c00c105071004d02440b120f2106444a0446d40310f0b141040a4031599007200180303104590340250f01c9181071030010700d841d410030055442008551203107452a641ca50510343d4aa4000803000449001e01e81414018549140c40b880d854400b03201c1c480c810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 198857257 1250 198856007 198856039
    0x613060f05090309040b04060b071e060e03070c0e042112060602030a0210140c0715020304030905030d09061e05070501020d0e1b0d080703020f16080709020f03060906 73
    0x40d402503a110b540c5410000c0d058009082900461a2540c0140c608001491030150596a540900d000c000c02c65290140c04068102140ca5000c02243c0c0144003080109140320348581d5035030104104071842e03403581c440020300c03024444542d442107030009040900d0050f2902010541c0f1060000081842290160111005403611031180074000359002103589221800011f031400b1100070003c90b0f258100814400c0700010007081d1038000744482102e6481c1c01c40d0380b4149052020b0402d42c1081300348048104418960301c600741404880c01901070310070180c00c6040840c1d500d01c00c0e00400002c901000b441e0180081c1c4881c8110703556640c2e19060b410131f0203690b545426130f88a4040303581c030191501134425805009003d40400038050030b0010200c00025408100c0210b440d1034050b02d04040465403e007858028030460806c80d5081c41626502158588c030125000114040d4000e2032045c01c1000c40e100c2003501c222080d0500c0100c283c2d055035204410000b0340d24000300300a40242d50f90f2160026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 198858507 1250 198857257 198857261
    0x2030411040e032802070e190b010516110f0303213c06090912030c04050d0614090109020d060509030403080a1d010e06071101030b10030b040e0606030613060f 70
    0x413014a4080e0311022205000a00e006030716046200030300c01810034805003905000300040c15240d5004041400402000165028043c241410070840040e0582d81c04000401000191101e0b0454103e11803100036014140c1d01c0c061719425200d0310481d1008400814041d64400f0343c00024004018550781a80b8481400104161202c4401c04c1a03101d226440d41c1c00e07408041d61010060341c82074414a031603002c1039950555144040b098000c00404201040e40080c12a030244c000542841174501c0649000e90042150016010980d0060000305000707a07418010010602c0e001007050030a200241c9411000f000301900c81c0c15a44020000000050103c002400301c40e015130f122010100d010422080e02c264884d84200e04108040901c1000340c1c0d541426500103a8202d40d003400d0003403043e001030700200300641516174041c1040320204100c9505810114140c602a0b03030600c181040141c1040d0340340025500543e05400c40301c0002c0c0003c6001c0c184017a26801400041603150000c081401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 198859757 1250 198858507 198858547
    0xf01140904020408060402100f02120708040e160906180509060a05040903020a110108010303050304060b0a0f080304031109010b09010c06110310051212160521091302030411040e03 79
    0x11417504208200400e501c0d12034001080c10700d0302d00b0304000c1d5680c0818005d4554140d50024040c03c003021501d4001d00041c00d003510054040007041c131782c00b03003004941540405050380034800040d025a2002c9140c80c4983e4036031202411203008510020b0801d02007106401c1e00401640d00707e800c0301d10026080e6a9800344046c054080e402510346200d081c10003052800400f08620f051007100700c01003000907440b20071250300c580c1122000845d4920703000065003074041640400741c49421002d0128100401100920480344a01c441c20703200d04a08013884100d040901c03541008030f80c240881e160ba5405501c42c440020311840300022901c05079008209290000c0d52a8820f40b40c0d154014005803d1405824010582450003420030811508901029100310f55102c1420060340d10761a00708103040055a90017503807002d40800e4a1455010541913811080c0510310684405202400800303062080364095900103204010b151941c4c0240000707801800004a85440304120040041102c0b02c10b00c0c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 198861007 1250 198859757 198859769
    0xf050c0403050706080f0c0d2004080c04050103020a1202030304030f06060e0a02070b04060b06040909080306010206061c1b0b030709030308070513030b130816150504020f011409040204 81
    0x640c4031800d41c00e10601d0012150451028409a882071108804c02d024040d41e0000d0b04031859030b43d0391998101600079207a050560842482605c18600d140c400080c090025a100c0703004440c10141c416082009840c2c00788406034018039400320030300c42d4101001546160f180080d04681c6040d03070b20382c0c580740900c0300c40000380d0f001c40c0d0b10642441619160303203045801248a200075814403e450302c1d410008640503200502a070ba940450041c0c3d9240d84003960018046c08804116692072414052565031080300e0a500500840c40080d00502c0d040400900c1c204a0001180c500b103090742d07400c2c8003c44445009502040c07003800c0010000c119200a62066845540e40303e80c0610314a40580010400b801007014001c0c03c0c440b0b00340c3c2000040c0b100e400c4076007101207016103446030304114508400c101005000d21000145202410400d0590440014440c04642020b20949014002110016103009522078504480c044c22503104007000303040d60781c2120a262a02d40201d000a0403680690311003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 198862257 1250 198861007 198861031
    0x20118060b010e040c1d010306090e0601030b07181a040b0705010c0215011a22150e0303030c1602030708030406020c0a0e0903030708070912032c030304090207060f05 73
    0x21074100d507402100300c00d065009403001c1c051111111005811003d002d2005c5000c0741d00e0400c0381207213030303c280c00c000c0050a441030200701c451005000c1c02d45442c0709001c15104c545498010031545481400c041081d2005030503410340c40c1d4146a49240d2000352400c0248030303800e0900c03000c19240520744c005c5c032000348554000140d503007198102074149202741360450720184642004028114502403803030031041007135114913a202c0c0f030f0781102510403c80d52062003202121001c0891038600300c0400003c802c40607181d00e030381300a41c4010180d4a110440d142e0300b446109005440e200c0ca00d001c51000000e1006082e109502d0310340042a20b950001d034000f10040c4e02001800c1090300f49124204060903000206560078900319068503560710018001074100700c150000525040d104400c0c0030051b090b60300c4241c01006032414000c202070940802c0450812840c60600e0743c0306088100b459803890041d01440c1480e141c20680c10081d0441081a5001c1c0d0302e68015003468004c6100d610722a611680803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 198863507 1250 198862257 198862271
    0x1003090b0106030504150b0a060c03030609090602030609150a0512030717220b03130311010c080a0b030c03120f0c15090c22110403081602040b040b06090603040302011806 75
    0x84204c1d0f140094459000501c7c11501910380d80719200c03400260f030b0682c01c1000070031030ba900e01180100900d80c40700744078500d000907c5040014940085001c0c240440b10648107807940d0104046042945a08550144043d04100940d043c91030110142074a40d40c296030414030151600c10f90f4500c441d0500000d8071b00014019455101211203008103558101100a10350410200810f00d12001e44510203510201800d04101441a442c4072100040e401c0207011940c19143c02410040040d20303202c1c4501d04003690f4204900340000e0300703204680e000f0000e1165040c8018511042d61041d0310304100395504110584c0035403010003007422071284040310405140740521001e81000c0c50054080d1090040480c082211511103540c1c803201d40d84031034001000380d000e00b0342e10841d2156500044c444030700441c6010320b60031810161844540240c0301440313800014403c00048610510041d6403001c0184101c1844d81802d4010315441840b03400001550702c109241041d80222100c0112001a01e4400f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 198864757 1250 198863507 198863513
    0xc100f081b07021923030718110d06030203060f04050d080402120d0818060c03011406090a030b041a0702072303160801141605070f06050a02070219141003090b0106030504 75
    0x74069a900c0142178014200b91403400c0004e88688851141900c4c1c410a00108421250143d210300d070b280811001469441003001028400344c1300501c4140d11a000d020001040d0310719845c00c030b0784a0f55000c8068542600714440a0701c5403078011308141e802448580e800d0354883c2007080415450501611803417031302e1611821840303032111903c1e01d80301181c2114051044141b4001c0540c1c0c155003580403403200350080c030000715000f0f00a42c80c480c1d81c40b01d01c0e100000180004010614040c500403842003011110110700074894032070070f8a140c4016400b0b03240c20000fa210014052482240c8003441940680035000081c0c44d049013088224200c0110b1364041000031424894180e81030100c000503c0e1518215002c0641010038143c2441480b00c0003910390304120f8003100248095074050000c105501700340140b00000d4008980c100e015118400305e00815440810f00c17034080300c2800080b41e03080300c02201440b92909030803c0d00710505407644002c10028038207020042c06482e850350002200c0ca045d013 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 198866007 1250 198864757 198864779
    0x106090e0a2909060d02100f02030c0714130c020709020d020c030c0304060206090705090601120f0f0b1008010e06271303032a0305180f0c100f081b070219 68
    0x44d100512404851500400603111541840300020079800d05003552040d0a134141e0851143c0030f01c46120340510760b00800d4000d2000502c1242e140180e40c0b55003c6070038203107000c040360390028407040980e00c002020000c022141d0001e04078000e1585000d8200490402c66a14580000c1411019504046020b1240c10f504001499011200e40001e01d075161410010070510b070340183c0f0741c034100942d0000498503400a60420024552108400c0201096011100c8014403809081c1072044d52031441300c090113031041d0889030681d0a6580b10507840d48034182001458040101c507414040d0003001a00b4403403c228a20341c0c4910141c2c0d16401d00b9000074600201141d03035040c0c0900c0c4120100968200c98810340c850f480d0310070b845080020321601c03040659000150403284003043c1d032050310000c8400180100b0149071100c1c003904c45582e06a8407403070a94039110300752040800101d25800096600c079046200b500d9642d02120390515248140d000720308000000180c00d100034421726030422034400300c0c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 198867257 1250 198866007 198866011
    0x30a080c070b070311070f060b030d030c0813110306190b06030705070b0408132d080a030509010e04061e09050108030f21090d090603050106090e0a2909 67
    0x26054903103000780980c1c0b10000180c015203030008140d540d64008103040200750071982d00b540c0040c00c518401c1c2291500e070014003803009801303029020310315218868a00a00881e0301803806500c581d201c6a0300c42c030030301d14a000b00c10810740c0d0a0400e905a0760058400780b09140c0508811804042000d10300c60320796050720307903400000d40942810000c1009299129041d11003240e03000801641075141e0f0b04054030540a007140407008801043e40000320034500e04148542e00c50040301000403d240440c914110050b284260b000c203401160042e0300091144000300070000c8141044400301022001050869046802510060182c030001c9081c00e04148000c00007001107600c1440b5560504025076201d00540102c084c2104000c6007034440c3d48120320341d91502100c03d0141c4036071890540103d607035030480540350300d02184c0100070204400f0320034081c03d81a06e095440b68160b0703910384079210840050042840d0341141d070f1126503902004080204a0035020058000e02c81803a580302008811000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 198868507 1250 198867257 198867271
    0xf0803160305090a0209220503180f04020a09060f02101d010e0d090506070204020903060f0f011a090907020124050f010203070b01050409080c1c0f020a03080c2a030a08 74
    0x3113419003c0c016680c0c01049030b801521503645807100d40c0c104c99044490000c02000401030300011034800804d060540c09989495000c0b070f038030025110a881800304a208031205c4d44000358600c9414000755026071580c1001e60890700c1110481241120074900311041c1c0405a10a041c81d2102800000e01c2405020340c00c10b9100d001c1d02d14400800000b520b401c0b240c3c0718890041002040100c1556600c1e41500c0c807099018040d101e641c03400c0d074000c01204108981c00c50081f02e440c0e00114400220040d926126056400400d28005075007041060081c40100300400b103640712080d2404405d4000701260001c49a0b102c5500c082d401d0070200103244800c07017079883c11540140841c0300030030480200141114000d4a00083c0388a00d0b040c0058144910104003404e0310401e0744810b89a0700901203c103840c00d903035894048100038400226205c211144000d00054049400304481445410041109032800c111400030092074071100d6440c80c1e0703260050328181d0004038501403129082041c807640944 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 198869757 1250 198868507 198868513
    0xb1203180105220302010f051810090803160b0112050d1d0409110a060e0609060c0a0503160c090203010503100f1b080f010b090a03060906020d020d0b0f011115040f080316030509 78
    0xa240803034082710340d01070b00d17481d0303c902d003840385440062f40901d2203000944005003e407036803520012080c58000c10006411120180c0040000030380181008a032400c0560150241803211810402113401040c079086045001d0a01c4242e9080355a6905c075690040d0710584110b650348a4180402101d002668003841c103020100c00070a95650754172080343c01e0359104480c015100e500c4415060b20307015140f1001005c0f8440065820741c0a0300f0250401656403007130084c00d5400d5250790a0300b059000a22410f900b551180d50011102007094000721403080c03180000081956100d50b80300400780011a902d0049110741003444107958034030003001c0c094411040c80703a103000380c4800030a030194400e100250025942e91508010000c03680c04480c100511048150344403907001c00e100d4020051203000500c2400c000b0070341403c40d40601c0d00c0e000c10113550030190002d210179050200302c01c2d00040046911395541c0b00c1541c002040700e006940904a1003081900c008036041c0040c085a2020b00341180d41d80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 198871007 1250 198869757 198869767
    0x30a1a0909010b031203071b050a1403030a15050a0b031806011203090f0b040614040503071d061e040216020d14070e1b0a120609020c010b1203180105220302010f05 72
    0x2d13403c52188d0f00d000c0c281014900c4044500e080035414294101e90080030b542c4003c0b12100165000000303980203080c1980100080d1062001e903a00c95405841100c0e000f01200c107040000c0e01105d009160701000d0f082400c601c0d500502d40241c14a042600142001840030b4415070600d07501c20342d000003421040001918031760402e05c1012150040f803042c00208440586d04001004c811002d850007040e004c0e0488941c2603c03100940d6044000c0c0e120b1000302080c5000141c090f2034a584c1d5000d103104865040303c800170780041804003075440312140e51044000c1032491401030b00c0304440d5007502e0b40244c3c0344c904c0c112103c0800500b0550142d1051003941e210105000a50141e1000d4442004058114a9481c1010202070f120802d0321020710204a00c1c5c00b800040504072a0003c024001201c4001c010b448450f10400080152001c0d203414180d00a01241c42580307130400c0d00c2003600c039050401c03600300a40161a81d2642d040c42c00103001d50905541d00300308650b0054a80842401c0c9818040d00709 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 198872257 1250 198871007 198871021
    0x213090c091a090a0b0613080717060f0118060308031806010b0c0c0405180307060603050d0207031e020409021512010b03070e04050403112a1005030a1a0909010b031203 74
    0x1c14019010844c030039652003000301c4c42e50b01d010485241e43d0f000e5150111140c0d0320f13244952030f00e41c248540d9200180e03002901070b444d0300c081402403203259101c01900e07460b42001c6040310b1003d2031030600050341e0364551000c008100d40720055485402d0105070700304c61b0166488440c0c20f142040c1e10608801106202001c646200401c0110800f0401d40b00010a607442c20080400380550103074007030540c0800146141441070507008802a05d001c1d60440c2c0c1c017004415030803a95020f09200242270b14001040c5001480d002c000c602e080b543c00113102203084022900018044a4452108540180002003100c070484900304840d0040040401c800d040d0f1802c03d9002d040d14001c151900d101e15514000581050f0240f4101800548001d04030b40c5c01000c0c800c5080030151001c00e038140302164001100c8424a401640b0021200c0250740e405c0c1951114045200901820481c1080c2a680303ca0781740d01944695980302c0c41150100f0010414003a050149070500300781a00380c030300c9a081002005a0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 198873507 1250 198872257 198872269
    0x1608032a250b03010311040c0e060405042013080106050121020706240311091b0d0b1003020307030f050123030c0306042a0e0c070213090c091a 63
    0x1036901c42500414100300354840c07022400e44150440da58803400800048140710b0506002c81c44854141c0e81009881e00c481801ea48461200110070741c4440d04100601440c00c0a07000401e403a1890340010b0b01070701000c03a000a06403c14003e204000340000307002c12401d04240920b1000b44030a0030201c6900d149454040d00c22503540c030100f8011034001410004010240e40321410800b001c1031180b8503018032304c080000c030a21a03c002d80f00a2107040d030742022843d0594001b8051005031030b074150500a801c0648600c0d40054106815083c3d03a100c0381d42e26902c0b0200030700c21100540e60010b80d40d1070442c0f400b03022a5015840d55902e2440c12006001007003c0802c003980e8600c99124503452140d2000c0003924280030940c5558050186505002c10022810040c0c444903600441030062030100c0e4003c0354101d10341e0710070815071074446000b09070082c10000080c0030343c0d400903008552030f081d540b100380150780318107030110740750400b90200b04180d140e94030038180910300d00d400d50000044c582c0c001480b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 198874757 1250 198873507 198873523
    0xc050f0a0318080c1516080301080c010302032e030b09010204150e010e12070306020c010c081f03020d02060405061b0705100203040b030705070209100501120207051504051608032a 79
    0x4010140e0389a8214170007452810345004404600e070f0700403603e4a5260603400d42d0401e00c2820741d60702c9580700b2883d00d076000307000390f92150240403110b0180c0e121210000000c034000c3c59000300c41c540d07504008804100c01c46c00702440b58a00c40c001584d01ca280c40800c0504500c00404001001150300b0f5017a00381c0e0b407184500400c00e800711040c40b091540024507504010b565400203100321701c005000320103810190400d41c1d072041c2e5500d0b00600b070380d114a41152100041240d8040010840109000600d8000c803294031560024040a0600b5100c0c00840e00641c4a4000b403c88200642c8903000924410042d003806410103507880c5518003007120f00039659010ba07028001000c240840010000380c402d106480e242d030340043c0184e510b400c12802e0034000b00c140303001e01c900003024440741d622141002d000300c0b0150b030f0b071003c010041c0c42500201c0014001c0007030802c413082c3c05000904030744550703401c0041024240d110061a07581c2d60701c001c0c0e008100c08030314166400450021131032a848401143c200 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 198876007 1250 198874757 198874759
    0x41b1a12010e0402061204030516050f010608030405012c120105040c240e03190f0309050a1412010b12010c080112050d1d090103030c020108060f060301060c030c050f0a0318080c 78
    0x446c00b5101c5183c1660180142500103805089400d8010284600014041101307481034000300416500d8810081d1244214000c06020844482e40d0014010200010800038001d10150007251280751000800c181c40041d0b103001d6584d1100240024003100402400040580d8840a10312070903070060b980e815a03a6001d58414402d00030f61051043e00d00b03100f0801100000d03964280280f03664038102c4221201410198006841100041464244503103880165444c01904400fa010058100700b441220000024150754a8000d40000ba890b10000c011303041004800200382030560080041c00390a0580c08003054209801c200030105d84007240409e8815024074241d007001c21100c0e48101e0700000194015086100f002c000010f0551103414121050b00c00d90b03411603103840d000108050300015221711540300c03200300010040a070080008075103852081c10070b0030f0041c0061f01c840342804402840391049401802c560020507070310a5140c09480000c09010542c3ca00700600c40c0d2341c82807140402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 198877257 1250 198876007 198876037
    0x907050901020703020907181e090c120510060210050606030a050405032b050a0905060705031815041119060f050f03070207031e0308041b1a12010e040206 68
    0x30110300d0348248580409550083c0c0340800f1750a0494000300154941803c00012201c800300114044e00c5864020035598015015800c0240c20031030308030000c00c10108490248110220b00333025000c00c5020312403245202d02c0701428018502480a414003031400c0c01c004141e4540310400c002591504207417a044541c0c5100020316650318a410f0340b462141564a41c4402072960121010031164105a000b0311600102440180c4550281c0760070b80713404100040194000c000005c0010344240091907001014000d0103100c000350705100d50038001188810041010320b00c1c1080140725440050701642c12080d980c83d0030b1109085840e00055800c1c1c000c2d00204400401c49182c2e503031140c0c040c1c0c3d144402e00700803030f547d0b824a0b14000e507642480b44401c0710300c40090480c0b4140d0150a81c049100f039909034a820182d942d95070f0340c81080c09401c002d000011b540041d404142141c610307140c1c0340720100c0328580daa43d0b4405000062881001680605000002c0070b0402005072110f900380c0b08900290112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 198878507 1250 198877257 198877267
    0x100938070303020c030f0406091a19091d1509010b03041511210108010e0d03021b0f0a111c0201030209030c190e3d080a06051e06090705 60
    0x304801a2194500c400314521000c40c1080c0c6e2140d0440040c8100c5070b00d03894100616659071b0341500c0780d50032052052111001401880c8030f22801c0c410f030030022042e910b00f442c103076602ca000d004151001d010211034140d140300104003003038440d0456010680402c8400c0c60032589803c034410440e00c001072000748002200b81c2d01003038045894014100034882945e4031516120351b0009001c20018246150301850660400026040010300c00d8604c3c45910101034000219000e1040d4040d42c40100345101042041c0510900c418050042d08100800d0f80090500d615041c01c060b03031103021883d00c0ca0f211b109031100b0451301840000c5059501a828200584c9405002001030304090b00c0c5081719410036911075003040865040701300c2c80146d400c00b6540b09141d80780c52440c00b0126545c0ca4221840020683c00c203850b2840c4a001f04268012041c0525049600e4542e001d051400c001e00440c0c1490f2034400340700f141424200c03036000f0410400c000d0700c024a001000210070041c003070a14000d115000517 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 198879757 1250 198878507 198878513
    0x71806052101020702060313030e0d210e0904060b0907050a0f0e0f030708010605030d0203090d08090a091a0f010302090a0612020d0608063102100e10093807 69
    0x40c4d40760985c0003000c291316440d00c880d645d400724901d00d1044001031030343c240104642c6050a04100910780080440e0341191030019040906401c2d030000b0340500081d01030560480c3d448001c00d51155200f4640412140305100501001c03480141c9445d09114091102c0b140740e644c4100da10503501c141d0714081c50101064000b182247c1001d08000703805020740c030800f00c0e2900381500000c0850700103030308070341c44141302100803a100d0044580c82540310074a03a810002182303900002c0c103004007004021514441d40c510035002200c2150900c410400e40483c002651460300409640c900302080c01d06501e440014030006440d0300c1540180d0041c003201104000d12100154150340990885070b80c1040045d803070340c0c61266500011603412802580d081202c0981041164601805100000314004084055403c1050402018107280d0400918890f240461b99940c000310f00380c115141c5412500d070741004503011601c4c10038641c5440080c81400100500c51000300b204401c1e254045449844091501d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 198881007 1250 198879757 198879761
    0xa080604060b120f010603060b03010b03060f0604300b0604090303020f040909020406080319030905030909041101020f010c05090d060e060f010f090c0c1e1202071806052101 76
    0x904500c2c503001c0d000c80c019031911900b040241c0100003102000c0392503a07803008210261b0303041d4010f03203c44241c04d200410901905c41c01a541280b0b00030302610b9848462800304010360843c2e840300d46580c0c00d100800c59528003040c621801c100c44481c2a440800203601c030403903e145d02500840c0141d0342c0d90404030605101c2d506540038000002c00e10fa94a030741d1829424041d1608a40680c0310390300d040c400262001d000404c0768000c894440142c503909035414000c0d00208110207060f02d0302d010420018605e5500c05000318400c900c180d0b690140f084114000904c1c0180d41c00200d00c50740c2c07510808500080e000b1055509450381144c40034042a003603e883c401410b41001d0034002b9103d564184035002003041542416240145041400340b0b03a500c1c003007000e0720b50700004c41006c04c070510290404030780c1e0484030b000700d801034801e07241c0080081e65038181c80000594410380141c01c072410078055191440704401504640d4103050101c182020001403203007040c0703640001380300446288886413410039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 198882257 1250 198881007 198881009
    0x30306150f1115070203180402250f02041104180c090b090d0c090b100807050f090409020a03051b0109030809060c07080f01020405120d1e030e1e061b0a08060406 71
    0x903499142c24180301c44042d540340c01c1110012100301c0b07d64444001d80c1418800c0c0d031500303001c514040c11111089800030441d168064400c2c1c5000815401a0025031250700441084007118401c80c2d07501c620f01801c2d405410800b0705004c148604141c2c0d5400d5040e84410080e080d100c102102d2a0b0b03540c1d422000403419000c040c00206013070240400042c0f100e080740d000c0002c00030140c0b0854810004e40d80d0449220004036204800f0030410710402c500f00c0d442c42c028000e005006040000c0350602d0781c00084802441d90b2080394258041415514090100e91a424090600b802d1590f02c032400c540d01e00c8000e003d0800e1450282e034021600ea0181242000101e006040301015140c00c40303005030341c10303010350b0260181501610850658000c040c1000607002040d13500b13030703841c00c0c4542c8070907a0300040495a81d011804241d01e640240c03110f43c409007d160008240154507068040748007140b542001401400b0040350540b80c1444101024400c0c100d62009941e450030b4940e0769207280c0003070014206 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 198883507 1250 198882257 198882283
    0x30b03011409010c09060203040b0301140103020d050f1b0403150b040213060c0c14031b010201240504050903031b0304030c0b070302070308060405060604030f02040204050418030306150f11 83
    0xe00c010310034894810b40c00a134840e02540d0300c50441c40e44646007a80c1d00e20461240400c01541040100040313642d15290401d0001c0514001d0710307180d1682c440e0400e8071419a210582d00441e0302c00d00444403042d0142d000a5600325080c2414189103403600d07595200e1502c2c0d500e048540310b1032501d01a98880d81291200800c03c06003415880d12508000c04144200e80125280c424450002c42c200e09025603d020b8980010001c0c80e40ca84880c0554000d14001c442181c190341d210100d81c01005045030b034488540050700d0344603488501e048100070540324042d20496441e0010014030401041d110094a03098202807e0b440e0303661142c1c0350031945502e0700354015002246800034040c0f03040d030640090642034025500c01081d900c1b40e504000c00c40b4015192658171600411003000000d18010301c114500f80014801410076985e80003040135a20610040c85440c1008000c00081503014402c4c03030068150202400c0d03507800102000b4140c0c0d071500c1ea2485c10322003043c1c000800420300708004018404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 198884757 1250 198883507 198883541
    0x2070503130e070e091302011806030c090906050319050703020618030f0d0509040906110304050319030b0a05151b030301060219050607030506030703050a0b04020f01110706030b0301 80
    0x218a10404803094803600414000d08240303004a5401c3d407040511810030071004100d40d403592541c8200826400304c81c0c00407410702c041001d07000c0c50358210a207480000e15140d2400720b107a14800f0b40c0201449156041a01850310700f40c8140700303507100040c2100661442088141041800d800d005240480a03030000f58040e0000031410041d88440154921809082d411640c4810041842c1e648601c201d0030781d5400141c042c05000b40e0752034180c00000c00c00c1d001c5c140020340d0521801c42d01c40290710440301074505503c00142c003004456841c542a600920524042002401400014001030039a1203028490016103105401450150040310200710101001c2a07252107804403031500c9800902c41c10000d030103141c00101001d284605640c1c0309030307440f0010300400d54031301109800038803000d80034680620542c0000310000d03c0801034500c103c2c0c002c490510192900d88104a42800c00052060410030181d8140402c08800600441981e684c1c0c140440c99044110100c3d00600140e092507034480 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 198886007 1250 198884757 198884767
    0x901031a0403171306051302030d14211b030f010b09120109030801030c23041a0306070915050412020405042603060f0d0b0a27080a0806030d0c06050a02070503 70
    0x80c5028103a0b02d0840c4504401d01c200d41d02c0c0e00055881c02e01c181f001a405030000c1e803140708054170640701d407800c0c05440031700e01c0c0c02c00640c41046d00c8118200e8084111403039400b01440340c0ba40e1041082800d90000100c01ca140d40380000e02035031280c0040c4100008400042030541c1959503091180185680b0080200050b01c0603040c000c4c840c0358207110903200081c0041011405c8040c003101c880354a40d807064503036040d06412040c0b0008000400e030540f040603045602c006181c1c0d041c09528095041c550f00d10a8840c180241d2004480c0d420300d4580910804200400c00220101d03100341c6512b4040b100016280d03203e04106551a0b04915035040008445154080d96480440a940a9002900c200b042690368100744401100340000c0030344003101c100300048034200103410082c9180300c9800c2954481e0580408504080307a07801003182c031701b0303004986a684030340e01c05d4000e60700c504110b00034152040904e070040e01c00380381400c0c0503004036120703000a00c0e09946d58048442195212084a90398 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 198887257 1250 198886007 198886021
    0x90f030c030909020f03041407050a1a0d2d05060d20090c130e060607120c05060727150f110f06010302032116050c040614030c0901031a040317 63
    0x1e075108913030441c1c1d00c4202c88008c0b000c3e8540003c0d80c800b0b4610151440705040d051901c0400c05d40c6020070440c115030001c205036000301c1e4460241007800d0f0880001d140324540a01c91100141245144810005140400f000380681d50021001c110070342120018a10010395048002c180c01600151070704281200184118540008001c0a40040312200d011040340c540c001c80c1801c10b02603d003240c1c44178040c84040d010070b46001603400984810b0800100242e03c07592040c1c02c01130125440c10204080c001110342c948000280480355103042030030584c1480c201059800103065200c905c10800041000c4912424007070000400e03802e143e1030444d041c0b01104010a80d4030442400300307d0003801031610001010204044184c0f90402c64500d0504050b40d12400800c2881144401d580d1803180d48118820fa454621403000900381018417807040e100c881052500d080b80320320401e80a54611001000894404045c00c140600c40c1d145056044d101d40c241120884060b0002040d60382c010010b10500f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 198888507 1250 198887257 198887287
    0x70506040318090e07060e010504031502040e010b09100f020c0607080307020f030c120a14030406050907080a030804020d0c0f080c1306030b060118090e0a15090f030c03090902 77
    0x2884519400440381d07540f280600803d403940c000c010b907000d500051040c409907000c1c2c19a01c112031030614207039003400c0d581c1e1900c030301c450f21007000f610301c0720f60005080c00f02000010106015140c0f100702071340b80c51110300100f000c40a0700c2c0c40d05410070140080c0e59000c00e100344008110000c00525542d00d03200c841c20920440c1c0d10039100003002d48240411b00d51251000710a940340060803034084c10324007000da901d20b00e080c0d02800220080005254100d9240b03441d01d00a14010b5001e003800140303514000c032100d8980003003508040e00560202a242e03001a500016555019a054580110b090350b1407400784a040c120750000004000300e080085266a000a103603098240100c070f0003000c079071549030810200c5407140000741107152490f00081055009080d9003903a00f850840c55071819513610294411182061064206908000500070070300074503100d02e000098180c1d008000c040a039549158000041d00e100400b8000748003103110600d8002e00c3e6081c014503282100759524243c820308119 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 198889757 1250 198888507 198888527
    0x110301150e09010c0f0f050d060e01080a0309050105130b0906091023030c041502072304150f05010809030c010504031e020d050315030304090606020d09091a060306060705060403 78
    0x4050f40c039043c5180a0b5511031950451500d0381d03078036a40b90040c0f41c40012240e0fa8002114102165296400001d402c09218205802007a003000074000b4445e41c0d01e802070401d4400d42c8214104072060007400081214116548100c400005141e0b41c5c59042001040d0366001d0419480d03409200094803442e0365070001c0c4070181000f100080310b0004400c070f205500c00b074002555030310b1001a092005209420b100c66070302141103030a004035a10155075082e00311004010001f00307030f844620113110700054101809101c032024115088050280e007000c40d10726110030f13984141410482d1460200348010703024000c0794011014117000b44902d1804e801c0c00782c00d07400140c0382075945048028003840c16910201d54070043d940c59503142461519074010100195080780211030381130004000c0000c90110b984103000c01062250090440c0b840802c80241017001185e000c0880242071003660203001c078043d003141900e0101101c000d6100c0d159000403c80c940901d1800030581d10500c02130009054101d25a11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 198891007 1250 198889757 198889771
    0x20306070c050607050301030f14010b03070803040f090603050309010c080708030a0903090b03040c0e0702100e0106171c18090f09050f030c150405030c0706080108010b010c0f110301150e 82
    0x1074081d104d0450803079a6101c2440080e00c4180004222400100802039810109941e08000300780311040d9400030341855040d601c41841c542c00010100140d0724200c103150014036614500704141032850b15000e80380d02c92400003504101091010b48201f2900c0801d81c0c401c150000341280e01d0b481c003041c101006141020341940415660540010300792410000c49100300c1d80040404050b500c0c05149600030000548444194040c10206001d091114030134104200368640c00400c4042c40d16002440030410002c1201494014080800c00810000081b01c404203592801c1c0000c81d00d860301141040725550002c4601a04044903511504910307004221064064402d9442011014414981ea44940c041c4040950040403244412503401c540c0c065225018506480c50000003490080c241038140c3c0115001c18040001442441824032030f403a58080282441034010744951034110102851100090500c90301a14500558400790400c0c9010300d071340340c10700445d542c9070030040c1e0f02d244c0115080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 198892257 1250 198891007 198891013
    0x170f07030306181118040e1b0906090405060f13080703080402180105030c0f0d02040603141c0801051309021002100f0b0a05091005031c0f080906070516020306070c05 73
    0x201c0703015001d1050402940300660038510b070601e02d4010700d514545d01201c25500a03500e44030f280c2d20644c248030304018598007a408a1050010701304001c0564000382c161405003504504120000d007000400940103019418120202d503079420810f07489410001d002082c019000c2140340805400000050040d44202e454020301c200328010a01c6100007403040a07070691040070f5080d0f0394206101404080c50000c2c001a04042050b00880c0030344907603500898185820601500010324240061000e10440b442c0004148150403001010348006003d154460002082e44009841e410303030012205541c081c02607403c203000304001a4a0303040d03580c00d07105071905284201d031041c6621321030398426540082c44454205d00f03000901402c10340003080f2040401c111070001c101da0750104a403020200704900b00154550311018000c0c9908400401d600502c00007009000d150400840d40650044481c0780c01912910300d451070441c40e00d10148065018041c1c9010f205d0704c294030011890300345000301d00b1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 198893507 1250 198892257 198892289
    0x912030609051b0d0e070f03080712030b030307060b1807080604110903060106080619030c0501110a03080103024605010f09030611072001120b0607170f07030306 71
    0x704161079001008003e994100655038415030f495006010020b613072405c60310320a803101940301070b10400e5001920300210100b02c150803c001d50b400c000b4140ea00c0c0c5401d1100c2222100441c0d41c234003071003400030701c480c1e160540201242c84000e02c8041070380704c1d02e036031003058200103001922200c4180d55481c080c5040400180c00c00360224100e4140e4140030300201641da190003811100103402a0203a0b50003501c003440c124004c01c0b400c541e4405540110580c2c90801e1800c00007415501e1108003021044e00180c0651011a4204c0d140354112501521404c50101c0d24078034180d0500c03444291001100c0d40900500407824815102404080c152008118540d03269001034410450225600d0f0008002d00300c123200041c1e143d08004041000806200c2c148211569140e00c103e141da0314456200111102d14207007981d022501d1140b6102c0e982d4200440240c0c000805d00a1046a40180000e69803640f00012640d000c0101c403070b200071765120300c0c0d142c202a01c2d0042c050301461003400c0c00d00b401aa0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 198894757 1250 198893507 198893521
    0xb1602090402041e150b0408100222030c0e01090b0603070c0206090310060e06010c230c09070804110a080309011b02040e06011802040b071b05100e09090705060715091203060905 78
    0xc2180c0170348a20000034427400403a4016074029621084202c2c400861a6000074030002060b02c20380050351241c9514100a41071443e080c2c5124016070044540504018940c00952a14800c9903046030031442c00313892003006400460440d20810252642601c18504041d1034480c04e41c1c0120203641d4003540390011911580011a8040e520707207000b4042c0d0071100406800040d4480c0f9001807503103100240d8000d1455500041c0a403002101d0440106210034204810030000c183c0c052152141104d500404600704030070b156607030051074003942c18048000c0c00050480004210b550346590f0040c010b1020511760340510303444450078402c0420403001744d01c044000d85802c0c005c0d50180c48034001850309003002a01c5103151800d01054100034860f80d007501080c02d450701c1100c504100344a4903a00900c5c0c924909109001e54000c0c40405140c005601c04c1c000d0760380700402c88400d01e81190041048481407021103000700002600104070340c07902c9021040c9240c00d50800005c54820003002c002c1359442d44 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 198896007 1250 198894757 198894779
    0x303150f08070536040c090903050a0f0903030e040b0a030f0f0b090f1504080c0d030b0310090b040809030313091407030c0c2904080702030105010b1602090402041e15 73
    0x44d0003011001541c20b4480c55484000080c0743c1c4203002d00703480c0c03d8007a81c0e40b0f604000c8460f07503141a40051000103003030640c103402c8103400e440d80c006481e00000c1c280c40d644000f0019540762480503c20b54a9801e50100d03941c8641c5c081019540113008901c03090303500c4c0f074208081c1080d42012548801d070540016824000826518019211240035050500d28214903800c05c100003441201c0c010303c2400403040c0a40304000b0001c4050094a001031400200700c10103142c009a140c0928041e400c160100c0c0008030b0701d01e4010f405c2540550004c0d1640701440019056000f12180401180c0b480c1e200090440415040301010300c07110961100181c0b12414200d042d10140e210f80b60115048909540c0001c01418204107503c0c1078004100300403442c0400e516807020305940c252000200840c0d407100354542071083d00d004207030712000285081c4058414051900c00031300c000e449041d03680001425511190015074044404040d5000d9007500d0b188030000600b030035074100700118060240400d610001c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 198897257 1250 198896007 198896059
    0x307052103040303020a1403040b01142409030109051f05060402040506071203020d110904050c04060f030f021c05100503010204050d060b030c0319050f0106030f0303150f080705 78
    0x191941515654035510164045d601c40546c1c8420010f48440902d200e490301800b45009500c101d96002107549046503860200343d803c0400c51180111032810343d8807200303e107000041034159603102030710f0310351020009004080580c00609140190900480b03140c030303a4501040811400c4800300807a8580d8000d01c0220b000d5030062540007031081000308042802c04000c011061300c035140151402c80400c9101d021b83c1c00f20500d40000311000b0400c040c0900c0c1600885a0003000e06d076405013014a89840200203200808800c000d255540b280c3d10541802c580481c3c1001c50f064140e01c40c28000e1032902002850121414001c010210102003000c0c0313011300844084540c020130003000340a4a8950100900102041c113505102c0d44083d041c0300d45041c428000f2040c01004030300e0010800f410300905108000c40391201c83c1c0d00d03000040c80000d07540d03c84c13003e000b41c245c64009014120101d24003041c0c180d54000c69a002072101c00021002000104a4243c40c000d6070030003036401048459450f200b600c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 198898507 1250 198897257 198897313
    0xe0705060d090c0f080f011a01080606031b0a0807030e01110a05090d0b041109180304090c0e090117010b030c06090d050a080d02040603060b16110a0302040608030705 73
    0x2040196072005070890b000303402c600340112881145960b4a03100074000c0751659100c43c42d640c2100c00c01808159080c441e40311001041008107900ca80f420000900c000030003810280f00320001f101041c0100c03985003052418090601d10f066a81885140107407680d2000c45003000001e00781400c84030b050f00107000d000040f5515005003400c0216510003998940c1080910030340250340d030301c0f030711020680d14202240224052540103c02c00e0740d00c02071040841c801042c001020031203501c0d607607401c40b000040740e049420540d000200550500e4084a403640084510342d0f1000c003c1001007a8510b81c0881da101044904008015a02c0700c0b10515480d040b08941c2c403584501700303100803507050800920241d41e19214030240c0b0480725266940b001c0c160400360300e4400c0c3e00e0317021600b484119014400e001c060800031001034141742c0d0040c07042c0c02c2000740c002d00601c4440a8101d4210b1078031600c2820024607030050060142d0380e210305405131fa9402050081e2201d200b0a0040004500811248007261007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 198899757 1250 198898507 198898519
    0xc06111005090a050a200612060f18070f022401030611040b070813120203031b0c03070306020d0b040905100b061611010f020c0d2003060f07030e0705 66
    0x3880c06121001080020402e007000d0042005080000310203026441c1c1d4903200b81e60394885401101c9013120b030715080001c803a0050304c0c100902056000340070034442d8840d508443c1d0400c0d02c1e180074007281e103032218141440304241c2c44c6000d01c45d0403a04600b500807a00d40e29801c035814800c1c01c8403100c0d07086c0074003940100ca039102c450040c40410425000f02d00059041300f0282d05d484da58100001007075000c05070903624200b0204e850a582044654824000d00b0600740400110380b540d00000c0c2c507032048a400b498444102200364107070030028030003900c20b07280080a81d103003140d0300c0c100000a940400600540741e4074091405005103818802ca50100f900710004203400c4950b121114010505420526403000c6c0a01042d0700b6100f03010700c00c01000380f02e096005c0103080398100141c1540c2010718900c3c01c2d0f4100364026885a2a410850240746411204e8802441140707a400003458540203906c0d509801441d0170000e1002c104404a401642c4a54040280004c04142c2c1c64a809031740c00b42a42c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 198901007 1250 198899757 198899773
    0x120638010302180f040204031b0303091401050d0902041e1401210807060b03030409020c010f0b0114071e06021308061b09030c0d060c2304030b071202040306090c0611 73
    0x400d01c0d610341880904d0107400145065240e840c0c0710010512081211410203031045c09004166001d81d2134801004000c2410300940d1030040040c00b540142031060f81074075a00e081000555480c1d410800003055031800c5c0221541c214650640a010642c402747c48031100780000281c1403104152080c050000e0394000d40c0010740c90b946100b40c42c0c0c042c1000780c59054036040100d030f560380c043c001440201002032006a4441d4181001800c0d10311605080c1d845514140c00707000d42d66040300c9140b00000d242d24140c0d50b51001807070021060108940707101c3c0350703c05500140c800c00006500500b00c1405441510f0343c141d60381d103d560755a860072980740660003100354588080d4031081002d0841031100030180d4401c80e410f440850171341c0e043c154054070800c4d210803146030082c0c1c0010714980d961000c08240301030300c90106520300f03040c0714601c00244041840c0c0001805c19100d000c0c00716840307280c0d80c0700395501c0b596410800007a040b005c2c1d060300e03108031000001640b0390091030400c000102c0440904000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 198902257 1250 198901007 198901009
    0x406121205031e13020405010608070801030222110c07050d0503090108100b07150e070b070209040c121a0115020a02011107050a0b040807050402090a12063801030218 73
    0x142d08003414103441144440301040c60b0490380070540340b00d646180c0a4070b4500e95140100420340350180d01c104207219680e028441245e0f4482c110b541034903016252020801d42c5c440d200341103100d280b4000744183d071500140108048012004000d5910524100d03200580c950b0108030502c04001c1004055600c1040785041b554000e81e0041e5000c4c4c00e9244a45005a880800054075840340c10100c0b400840d5400e060340740140c41c0710711600046000000c1c010079081c031200c26414800c03800003903c65004000020108080521140f01501d034030600d10b03c840ca010702d4800040c005407410360541c1e00e035103070021070300d1095100c403e0000c5405500401555a4540040d00c64800344420401d5a0241e40804030385512902d13183c0c2c0041c4400d05009a4503844c161600b410222590032140c459401007291048680e1028004019a1111107880300710000501cbc0c82001041056018a030b5001c6c160940c82042e00011610044600b0264001000044c05c0004404a229088101c0341c6000d440d10b80f0009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 198903507 1250 198902257 198902267
    0x242401090e0604020d0603050a03032706020c07120f200108280c0905010306080309030303042a030b04110406051c0314041215021c051509010806010504061212 70
    0x14400f0f08014500075a10701c0034400d94209400c20354031075220380011804c159151007580e1355500854603901442c88400d41400740110603040c0500256008641b03041243d80500c844001030a4600c0110f14542a6161150341d08004182c240e861405c82903d044c1c001c400d03185040c8559070140c3d18030040780d440d2a03505480800c146040c038040c840341e99141e60500001e10903550078074501d807160200c20b0311b01000101aa030340c60300001040d800c1413203854120b8070000190bd4000341d00c030402040b4001240fa1882c1307800502d050285501e000304000100340218002d0316400f40f406504003807800c0301e24005101c20b440d124840c0c01d81003d02c40280316043d004054238507411502c01d10340004c0c1d101450800004d9504039800000518021000000c2045034000d46c0e80ca02c1007600701d0030741c20904581950010215202c031000315103a12030000982c080604001d60000d0080201000e41550b19a0106681c03081300f4051640594500100400d07400c100380c0801114503884161001550140d202c02c0314 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 198904757 1250 198903507 198903511
    0x3010509060d060e010c050c1603120503040212101a011110020f041706010f05030f0601050f060f030f0a0f200702040212040b0a0515030a020f0102242401090e 70
    0x16115075503500608a4036080c00b1b603200084450b80c1d4103032200c001c4903206040a222621081c1020418401080003c85240301c0750a0f10345903050907230712030b0740d140049070f03061075558140b5906015940188115036155403001c010702c0c02c44070100c203421440f000152942100000603907002e1740710354031400300c2c1c51003900184a0040c1804055080c1903035640c080c0f18045c81c4c09060180c0c0d8002c0c10052080c0544a1400c4004110480007450400760b86200d213600c500b410b0158a02031540061a40e8240d21250121940c05070f128892541c0c5e481d016203c045441d4082d12140022410802e0800509070140644041050340b400101c914001e04807890005078040032040703801c40d80a005401e40720076000c1b4200e110b140605003510f040e180c004011402c85000420040380000e5003000d1462580b00010388050711581270300d90450030400440141d24004070b41e000c90942000c40560001884400c80800340035414180c1c215004001c040403000c44024120f0301c06000980705c4004021119003182d00e0b075 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 198906007 1250 198904757 198904763
    0x1017060f19020a020705030f070b04031b0e04060504062d0f0e030f030a11070803010501120b03010204060f120515060a0c023a05060a0c0201060e131703010509060d 72
    0x4094880807180c0c10141d80005281d1405030f040503a00f00b00c076041c144480351f460b0081102414a103401c12484244038011800080e00c2480f0f00c2d03200c0c021041281212001a00c400798030f500d407030320781450040c0180070b0480d0200d0b0b6160030815945804088411080d620014059201c2e484814090f02c4d200101180e84c000c0c0022900d5402d0081ca02c8414002000e000f4034140002d41c0c0c0e8549408590280d649024150745641001c1001d2404511164292819100d0910b4455100b411031103140010308003801c2a1035049d4070010340061882d410620038400903100740c0301e210480c15810900002c5400440f0304c200f40380a4014192241d203003a03c010300342c5150904110a841401d5004514581c5803041c58869a001c440701c0910b41500d04021841410074045110400005a1382c2d07090320b0340009030259464075201c40308580b1480c000e40044010740080110345800d4645060801c120410711182175519060209030041d481d03000c07034101d13410307108064008440c6440f002d050090b4a10038101c25 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 198907257 1250 198906007 198906031
    0x206040b070c061b02010e120f0a0302030901021c060501030c050f0703140d15060806190e15190509130b0714040e07020c030c03010b13020309150403081017060f 71
    0x24105a07420401304521440c241d800015054100a43c1398030740186103000c07030841c0380d0a04c1100300034003035101106d12114840c50050713200c2c0c903034500c06070280c001c5410501440e032811103c11142801075000383c0403500243d034144030f05c00d0784074410b5640740300b00501d00306c00e814104600c4020038001c044450701704101c00e50381460010303050824011502502044030100305a907208200d03466201c4a083c0d00000200c64000300844401110a90582944500360140d051203000540c000324107003044442500140020340c10a9019032420b41c044864042d080c030880c90200071074540309042c41c03011401684911000d0254031249019503c4000b0390300034a010100400000c40c0203803044207000d0040c0b0558004210440c842020581400c85044c00240241c4c9030400c034011a0741c810a66100049642c034005070b8a4550341d40541c10b00c207005640001c0e8040100030b101c1056405014184940d0f80b0102c4120656202c1c203c00e6400d0002c003051403d6a445032000c01c550045001d40e894000c5140790760 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 198908507 1250 198907257 198907271
    0x3030c020f031f060305011a0102030d050c0904090305040905010b13120203010f0f0e071710090c0b032719060213091109041b0f050703091802030405010b010206040b070c06 76
    0x30f4007107044000c070340d400d000e41c5a1000b0400c00c0002d0140c0041c06403090b048860041c03030140001d54900450040c1c0b035919440b5404075402003018412244d889102a01c10700ca081c0b070b50304025100c1d0b4424400c146115180c400002154840700c0d05a900301140d000c01f040d407072403900d61a0048000d00880907641550307a44180391079522a417244000d242201d8602055200341d00007068100b0f25154040040c404114052290032280440d0302c460a02c0c12940c0041c803400c1034103101012130015000720b945501b00200b03000154106800c4140014a44491902402c3c15070440540f94100c03280c400c0c00b03010304401d05200059040d005000301152400072903004d190340311a01d400b80e40d83e01c50030105420300026210000d00303090180e07035a8811407880d0071030b02400f084402000000c100c07034108200032020402d841010f226403090300040c044000301c5502404c1184507400254802c0e1411a0b556290084100055001081592049400a248800584c0c4054003a101a416a8812250a13076a050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 198909757 1250 198908507 198908533
    0x150510030219090212150907020c0103150e070206010e160516140a0b07020d02070f050f0109030b0907140108070f03150306060305030304020a05010206040b04021e1f120603030c020f03 81
    0x409440d018566085ca500700b41003002c071550450344003042c014015070301001040740b007540010384403200000a2034001a402490414044980801d4021107116613140c01071003802507000810030b0684403205029041d545600102d20f005281c00d08400001c103c091040003c000e0003080722541c1e5900a8a6500c0490134000702581401700e6500700721389200e071003030507c02101c0c0e041010802c542034900003022400d0604100841492640c0b01d118410f0525880800d16039108134007810017036600200149250400840003500c41c56140148410824503107000b840079840f0b0456980692101c1d00c0b1588858683d0f00120003510a0b080c0700409540c3e00240000061810321400c002580284059070f01e0f81000e1040010315125540311504540c44a070030700001c103403400015a009030b0704450007100c040c01e5200241d48811072004065000300d80d610b071140c00c0039440f0b040c507100e41c00c5039032203859480070606030008039a5079000c050000349003249408010b00308240060358080000f0112141582491 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 198911007 1250 198909757 198909761
    0x9050a111308060717040213090c08010606140f0d051503070801060306140115080402030a02120604120f020307020d060209060412050706140f09150a03060315051003021909 76
    0xa50304408032884241c20002c070102440044c0c1c004100740b0340017281c0400d1182c040e001100180001c0c0c415441503000301e00c101100c0d072040900f194440f00440480350386200c0a402801c4c50300c10b820204070b2880c0d034428001415011560a240f4581e8920300f40380840d02075400510004150209020401404d44055542000a80001c099901c00803400c43d0030340c94000d0a07160707402e16400781d0242d020014003100d04020034502508d080d520b40214540c0c0ea81c0000f07481c0401c000d40c040c2d0883c80b03095580010340c0c004a84680318030300a00e00c20f02d41800e441003c88034185048010781c0103030014040880186041e40008121501032000581400c4140300081c0451f840317a48140d0400101d010f1210804c10b05200e004005c03e45410600708504840d001c1c86801d10560541103140318000a02e94565520440080c0f50000d180600a0300c43c084020301074014002e46c00180c0741403460a8100e07040104a0090901c22113041d409503020a2440c0d0a00610540380000c0009698960501040085140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 198912257 1250 198911007 198911017
    0x30c080d030e0d020307030f0512010e07020c0108090c1519031b0201060e01051c050a200a0513020f27010906050a0801030803070e060d02070b0709030c09050a11 71
    0x40160021085000c80074044400780414040941c0221058005264010096840094146c18506c00c00310101c03a007202c81384201d40d4003244211410001252500b40000c0c041d00c02d10b903a4007203483c003034140001550003480031270b1a000c69030710801001c40316041580c90554140d6400c00610308103400c803524000103a40c0301490000107581c84280300202161101b400c15000407500003082082d040c0300c008540c00005000d000d0181f00482c41d5500798440c44502e0310300d0141c0003000d54181c802c0310300e01078512908849449541848040f140099841c0188595088500040800d116140c00d0801d91004e0b400205400b84140d10a200c040c2440c110114143c4190111384046a0302c106035034000360008906030000000c0080600101c00800c0c5c00c20029410741c1d0b04a820303244c4079550034604450044030326440c00e4100384003103016504861300350060a8101d108065003010755880c0e03601126620102e11014007004e0903000c007004001c0ea6580b14030707086030312103038003064050807550880e01c0e130347c81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 198913507 1250 198912257 198912269
    0x10e03150a05040b06090c04120f061a040f06060503060d030207030512040e010e070225080312041115070618081218010b0109050618150a020c0301050402130510030c 73
    0x200c008000404c20104c3c1920781c403040c02c558458040c2802c103070320b80c0c0501440c025401d001d0078500504c0d090100100038030030840d5201c042030201c0544103000c0445440c1c41d4103048d0056040c59810300c0845c070700d80911010394a9656545085641d09404c03c029501340c54000d5040d80501000400441e5042c0506a542c000b60a080355445e4a4000c4001a031201644000c0714411036805000e01d0650201ba5154010040000d103811204c802041c44a10701c0c0c9503020304a54400000c2c0710188003042d080301817055000c0c1060142140c00b040c14000b1004e072581494072429010000040058807960206c1030b00702015290945842140e5a0f1224541c070455601c03a010700c030700f030411408106907014a0742800d014002071002032883c40002c1c2c1002000d0185a20030b24000c11141c00050340d4a04034410408018015190507254204010042d403180c040030006004038115590b6608050240f1400380e075024000c40d01c030400c00006280208009131000100321040c440020104100c50103210190030303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 198914757 1250 198913507 198913511
    0x812010b0a0806040c170901060806010f050316120206071a0f04050c040c080c0703270e0c1213030e090406020309010b0306010510080603030415020c09071b02010e03150a 75
    0x1240705009455424003d014500c40c0d800c0c0700700d89001ca5841030300026032050300611520103858580410b401740800c2e400603c014820b0800000d84407190300d5151040307034003c1c0d0903540e0100102c1c107480144911809900c011070b1b08200100d005041400003002070078001e0075a5000e140c7c402074040d040500c241c400c449008144800d00050080a00102c072408004590030004001c1807440a010303518010003040d0055030118500d02458051a440769a42031a03001d02000d09203145503220010703855018240c0d40160490005403c00e02080481d40900400c51400c4603e64805802900c05442c030501103040203a000d0110340145c071802c09843c0203e00c202c00c01f40e164a04000b0050840314040513081c401d80c002c2c00104115201c0c2550100c035a669842c00e08410f40d0b915020034514401c3d5030140076108184109105800d0b80807a1840030040704032002002501c1c1c0b124200e030146524107050034007201c2845200010360240844c480c0050000e02a500d1603402e00c00301a081c45c00032100506215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 198916007 1250 198914757 198914767
    0x90501080c0307080c0d060905010b0706060e090c040c0302121003063206010e030d1d0103020918060307091d0609010507021b03070312020d02100c05160812010b 71
    0x5a0818011607100c482403007400c0c210310304030b40014a80c4d8006443c0d0082014000340504508903907402c4280078005150003400507581d00c2c141d24002e070b071040c24140c44070791038003d011031002d5004182d2401401c9013070080c114140031004100041c20f081d80500181030382084004c0c1414421141c0910400c85a104000681c0c0b941c20000c041c1c4400440030006148038551b160000c00420b0255085e034008522f40c14525603c113401680c00c010000e4540d076151091401441d41c442c0d01003508400030102c070380c000359144c1c6200c0054040e4010780c0d044642c04078500315094003058407820b01030340c08a401411600b00c507503103940e0401100c04c0f2030b24031242030607900384641003c801004140e130005070400080065242030b110017901c40342c8400501e400141c2d071050b9482c00f81d900700b00c0d140196030810226600701c500000041c0d51070070145a02e03400b500070f407000c044600c10540300380003e00100b5240c4524044220444464502e1100d00c12940103205010a5007420500c0d60385c24060100b815880e6995 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 198917257 1250 198916007 198916009
    0x70b011512020903030f130308030405030a0915090302010c05071505040302030111040b160302030f130611071a2808040b0c070507030b0628060e030304080c060c1c0905 74
    0x603003016424145110b004120909003602c0c000126002d5800f664020394541680d12014424120350354070140c8042c10210601061010220040c498118a91038811615a0366148404140108034041000c640c4004080000d54010030000d804c1511400540d070364140c90306107000f242200f05841d07000240c0b01280500c110304091049514844510f60b96074105460401f1100840c8035201e05180d450045183e00c00405008005882c3e0040c581c8041c1511002107802e014022403041c400d540014240c0344500b1044400421640140d8209074960f00c0c4032800e1885a164035072041d28002142d036847c02d0758284c0c11400c4004203035400385aa440049905242c20140c403204400b4003a801009001c10a0b4030014200040e140304070f03580008420031f95034031400020020150351840f800130795551201002541840407901090f5001919034403080380080301859500e01071801041d02c55070125840d980d943c50f101d030240100070040d80c215103409100350b5103580d20324190500ca070082510040c0038486 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 198918507 1250 198917257 198917267
    0x19050d110f0a0201030c051201180f050423120706061401050301120b0a0207080c010501081002070206040905060d0f06050a0b0d05060601030b0112140f0c07030903080c03070b0115 79
    0x142600100100700c4080e03106515500d980d00700314000c2c140350b5120030760070344a8090b03000d8940c1c960f4200c03101c035050340e0754043d00e01581d68000120302ca114600810031000c1c0300c1178424580160340250401456072004425480b1741c16080b40e040207207200b42ca21740301501e5034a00007051410320820000c26154900040103102c0d4149580140c18000140018807540807681c20428480f80c010103001095280e907880100284240706001d010300318009101440c5003c1508911b040703d04810446558603000030101d001ca000f45c0c10f009500090410042007801c6040e00403d402c594018116490320140f0b80e01e950300d00702000c008462135522442002040c1c00c2d07030300c101b031000c2e40c040c0e5561660700c046546281d1643e0009100c141896902c0c5185036450344603002156274101521303c10440f00081810000100c13600301c850071000e0809900040d00000140180d0384200e515031140b00e0300074159aa80c164a4100c5880740b0b06521017417162074040b0310303e61401d50080000c024140640c144245000305 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 198919757 1250 198918507 198918527
    0x1104080109050d230d06090e0c03064605330907030e0f0d18050414010302150702091303022e090501090b091f0501050a0b0c19050d 58
    0xa00502c1841e0015515003142c4d12180e246281031560b95070300560001600030042c50308180740e1903107051180c80c4a5200014040380602048040b6801c0340d41e41199500e52000e01855034944420302c1d41c16100c03100b000b101541c0e403039981044104403a071351000c088003103070001ca0b000c903410282414140c000500d44a854000001c0030fa01e51154079a21102140003081c0c007411300010160f0725024500700e000700b4003080c180c42003004103442c0fa8134074201008080141d4120700d015070340040c120028891030984582d884401c031242d02d4a90986c0380d1f80811021080380800c2c120004020040c0000503a1030643ca41d204084203442855455000d0030001d1600301a0810030a840f10403c80b4412103c0e07007600441120300d0301d1130000c10043c03103a10304180075082d40103000303180d00140402e10a10000104225400789483c4801c84c1641c031040c0e0020064690a1103101d8110300240c00a01c5860410402420072500a0045030700704004030801080300703030543d60244c8080d0098054808066070001d200c1d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 198920863 1106 198919757 198919783
    0x90f0409120f0e1903080901120f02030106090e06030601140307090f02030604110403030c060209060906130515070c1701110c030307020d050708030f0a110408010905 73
    0x14000e042c00d0105540400d035142d809009a00780010204015100324960205403407460300ca903900341d400601024100400440c00421740c42d124000c03000c0c1841d804000598035031508a004010368885d07084256221010340502038075580002d00c4a05440401c1c10152207800c0c070f0340004e40f40c00764540c0280c0ca507505102c481c103110103040c0d000d0340c4240310645041c040d411010340079074400e120b00d000c010042508865464045100b55014018019010f0180c1d4541201c80b00000c0d07143e0050780300088800d0007003402380250b003000c15a081000103004d24007800e149441d91403402c090054040c100ca00c051070302c0c29440000c070035040000040041c9031100c4e501c2c03114110542c0c40c0c4d40129011400361050782509021640700d24115004141c000741440e0544c1c070f40038002046804080d003011030464581000c011884034040040004100003000080c1d0024540381c114105003d2201d44 = true := by decide +kernel

theorem cover : BRFrame.Cov 198741007 198920863 := by
  have h0 := BRFrame.cov_init 198741007
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 198741007 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 198741007 ≤ n) (h2 : n < 198920863) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
