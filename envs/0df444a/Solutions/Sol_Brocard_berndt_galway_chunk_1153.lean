-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1153
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:29:08.459+00:00
-- url     : https://prove2.me/submissions/8e28f60a-5718-4a1c-b577-b95c93db0cb2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 207194244 ≤ n < 207374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 207195494 1250 207194244 207194261
    0x30209090303011d010501020a020f0118080102090a0e0910090206040f0f050a0801090201270504050f160512130201050d1a13060609050f151204030f0309080706110904 74
    0x50040d9201e6040c0030350b81c44d074040004058240320a0203001041a40e90001e8480310030b603410760700e0203a070501d01c40043e02d5030a1103440495140540040108404c070056029103c04441100c1c54680244d4600100300200029546502d0540240044800301d0358180c0241d10130b240302500c000e1405a607600c0c4071500700d2827604100783c0a03a481d5030400c180e00e8810345074400380c0f520070020041842e80d54000f07006032900003035030380c0c0f072441c21011110b50010030710085000f000080c0c002c0c403031031a0941e079a000203082243c0c07604150213002c100c401d101c0e202c2d030b041d04d1180642c102c0e43c0c1825281c45075030441c0b45d095020100d041040030001d00c2040501360260007440b0b29110b07506c20211303c46c20100002184401226410985060713010400703241e000700d030041118800e44003186044480f42c003103184144881a5217210745000141070385a5224500f070f5a220358020f44d200c03400c82006d05012005c3c1d403518803014140303210074803c0e0008181c180d48690804e4015042d50340c40c060500d40850f09948054 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 207196744 1250 207195494 207195511
    0xa02090f03100e16050d060c020c060a0e03070b0f0406050c0a021c030e0909030a05030a1b02030301030c0b070b0c0313060c02070f0806100323100915090203030f090a030209 76
    0x5180c400081c01c4104490b54500182e2134040c1c0604c0c0c1440c02084681480c504090300713050300c8810300c00e0f106009101c00c0c541194050000303940d4161420001d07142400c0144454080c0c0304074040000c13a000b01c6008d441c2911450395400d403030f01c2d03e003880466854002001482e018002c0c0300111006984448451101c2c030001e682d00b0804d04c40a013800b0700328403419100741d8003440c1f40c041000700310709000c002c6940e10005820140c3d103d444040c0b0b48001020803040010f059031030700c01898500d640000c0654100c2e031148908690458844080290a00903a81e00900f81031028010410300022540903543c01403c1241000062140ea1a04401d54400401d07100c0941c0010700c0602c0118401030006018110031001044c403070411138640c0c21a0442440040c0c1401d0a600a081d508003114501c0900441541c04032060000214071410081000c48012925044400010505085c1c14001c81030b0f4150001d01845c10141c1c01c0480411030742c858082154000e861850100041c0d0750741102c0ba0055029 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 207197994 1250 207196744 207196751
    0x51f0201022b0507080402030705010f020c060a09180204050a060318050105180c030c03061b1903050106091238010b03090601061809110c0a0f02030607090e0a02090f0310 75
    0x1001005422500c004c0e00101c1013012000410015031400950300c0c04039034003071810030000c03070426900300c1c10090031080302507000b00d001500c03a051541c0104c00000f524404400c11400d10407100c440b400724800d503c1000c0c0c0240c0f04032000c20480e40640d0007207041c01151480751203412070070b988d1303c0d085a0046469404888a18a624901c2d20b002c2080d603045a9007074008007444214800080e5641c8001856610a21f03e1044031403a151090b0082d00c4088203012007541e0200c03545040640a00024094000062288580080c811183c801291035081c1c006400c0c00b10100b0f040024100410310b00e540c24013a02000d0b48069540248034000b41c002e190307a0300c8036503c1c1d08000030418141007040e4080000c1203c1f429040303c3d40c8801c14071090807142043c0b4001014403103c024246039005101010303555001e000d00c02c009001002e440d5004140c0308038140c5800c2d64030240140d030056198000c2002040e01e080000b0401c960a41c0101103240b0006c00303003036500b05007400091801400000c2010050b44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 207199244 1250 207197994 207198067
    0x6090a030e130e07150e03070b09040e0a05060708100b03130203120f07110f0105041211041b020f0102040b0406031107080406230307050703030f09080c01020a09050406051f020102 79
    0x60317065080c10103600361801000300d000400c00240c1d26441c1e4091440b41c00c0300001c200202d90f6035035200407605034802040c1c42000c030f0a030401c1c5da110103048400c0004910b500b4001807080c128411079109881034100c0903070454407039400540140341c0c03c0c50120f0301445075003242c500c03908076a00902240c62740f900c0c20395501d609c0f074500040d0070143d100d140c07400785461b8403001351161b030005c0035035040d141d0b002940509101c0314100708018075034580915802034a401c5e880c0620303843c04601851448901c0c0c08603103881a0907402e21b8202c0c4a980b00d02803080c07405100174801c20340329811a10190034030421160900c0c0140d1240c083c40e501c41d034400001301d51040d440303c9414081694204c0500244a1034a0451400c000301074641e204540b002400c00d591015103101108266000101580c1c01600369034907100e0300b03c4810300035404552040081400c040e000103841c5098080e40c425900003a00d000c0302c46d81c44512200b0420070b0714a4481c20755400744141080101c04401c0b4040041e10309000140008 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 207200494 1250 207199244 207199259
    0x1202040f0515090d020108130b0a020a080f060a1401050d0c050703021c0206040206070f0c08030306040b0409050a0f150207030c0c05010c030c0b090a060e0a1406090a030e130e07 78
    0x400c0c91008604041d014040c0f001039035240306a4090302c903021b0800c83d0255480091013416070056070300007001080c0c0740c07013408600135540d406030030400002d0300c50316650b44030340100c14002d100407504030703a000382e81c24418800800c010b01011492a8181015818015001001825200c220749850001040496030400f41075040202c5000c01903243d2114125a8003401c0c000e444400c0200003038041c41d40040e2003400c200c0a04100d810450700810080390081e150504035459500a94007103119a040c00c0d0000d40f246807521076620b841394468018243e0014036540c2e03000705030403034006950319a60005824020703480d42c00200b45c0b407031003661a144d122405d8548066a00c1080d00924100840c00004400080c0c0080c041040280c01c4030003078100d0341e90030009515101036a08020f10752070408590103605440014031684030342c0716010040032103440650f19075070788104482e9500641d018156100c0441d0264811102d92078010749140690300603508071000342c5890104014440c2c0c00a0020803080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 207201744 1250 207200494 207200509
    0xc0801090c120b0a090807021206150f0303180406210303060905012105071206020414010f05070602030901140f070210020a0914040b04090b0a06060507030912031202040f05 76
    0x300391089041c40055000e4071182a483c0c401818401c0c0150341e9403a4009110980054400055005202042c140502c3c0782080e02c0c0c41c0c081d00c001c1c1143c42c0100e02982103141000800412900c003038015401c1425008007070031800c1c076401030107401c196502408510079800c40d9030740c001c1d0900b01c50f0040f95800075140080c1117800c07940c00000c0c858901001032280d503a141076a62565060281e9031202030f002800e01c0f40c14a003480d4050b42540150b002e003081004001d402900c21500c814202080903940c900c015038011007042e00d8000098001c03c041d500142c1582d003c1c50704450f8201c00001c03018104a00030300d0010080d10100070300740300101045401541082a512184c01a60003582490b65101c0040c0c402c25080c003810781c2044a4488161054580d940300180c0f04400400030300902c602400c02c0b640403002510203182e45400c007000071a0560090040b50b1100c0c3e8566103418030f1525258000341d2000e1100b030220104a0300804d81c040c2c50155001a0029064005030144400e152104000d0403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 207202994 1250 207201744 207201749
    0xf011e14251e020901180e01180c1502060106110307021809010c030605090601051b01020f07020909070b0306040921090f08060c0a08090f070b09012a1403070c0801090c 74
    0xb080c0303070355000a0040e01c1e003001080c11035090b10035030070760342c14408a1440506030f024062182c961070003041001c0c13210060184004507004000481049450710400c180b99418010040301581c420001009a00d100c0c0054a1081c001e0300c09803410b12000e64002070040c41c0300703800c40c2500704142c020b100c0e40500030701c00c440020b60a4141000510310701004140404002007555040c0000801d01120001446040204029551008568800342d465401d2030340d42100a082e4002c0368040c00255010000107400c0040c2d4421a02c41c500b16039407401000054809100300301c0c1c00b52503840c000c40281c0030003096400c40000f15100c0d0b134201401c2000c80203c000c80b039482007004d50702072420321602c00c1940e000c403809603507107140c0494541d4820007070910b441c000c1c000d000b005104044002500003010000340444210980e940c0310794100c80e04905000c01d80c890300c900c03030607402549400c0c00107468060802c5c003e52a2000e890915180c0c0e100c0c0c641100d0143e00c401010b9451f21403040c10030941c0c83c1003402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 207204244 1250 207202994 207203033
    0x3171305120a0602090112050c030106021c0206040210121409191104020904060302100504080115080d0f02100906062103080a11040905150f011e1425 66
    0xc600059a051503982c031030070030301824842e40068458040d1340310316508100e10b0302a0ba8140003504040451416035070091151a0050041d40d04900b0601c0c480c1200360a105c003d98000c0c98252203e40030402041c402c01011030a1219008101e60900c10342e00900d0704542146481c050140380120055041441c0b4211016003010480741c00000151200c101c00c18080003660b0060b11503007800007090040030b990700041d5218103500308040e0110303400030080040e20599070080c007038098540400042071000d0301400703846401243c80558998411181c00d440d085084c81101d1450288102071411070340d00e1034050743d0031600c901051041100503801c1211025100b082c442500030951002803c426015013103c220989640e4245140101c000c1590040d04a80c0000c0020b42040c0c4404410140310900080c013074006480011050340c0158586414110002c01c0600382c80d01580085819111040e90720092020a00c510070502071854640c050441500c01146d600d24103e0030075901038010120032a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 207205494 1250 207204244 207204259
    0x30106060906140306040f050c0703030b01030c0c2604171504030c021e101d0102061b0c07090c03150b030603070e04050109050a05010506010e040e030405061303171305 74
    0x11998407115402940101042c904d46035100c61300018080c1c0441d5030340212090a00c414070010002d480c0c0280ba07094400d842c10410343d8007070700042d0151411141c1010115401c04c1c840740101d140480384070a00c43c0c030040228114054070301e50400540250300680f103c10710940b44035040c00803c110f807405010f40030262969918040e500240b8051003041c0082c0203500721190311031448198098000c170030308000c0c03a83d5088034034644014200c3d40c180b8000b030f050411155602d00e00e540085400b6028643d084103800c1030449444900403584d00140a000c02480390715400030b041091f1744502e00c210049582c0208014080e0304c452187c401e0705401411014004000f4010103070b0300020a40102d5010160742d00f400d940e0b031f05290707004014102c8050894000c000c2400d00f04070066200a201d51030980fa4603400d0640001408201c4500100307940340340e4003c00051206d031034000c0207071652800341286a24801c0e00c13a50b03070460031a4444114010200d010941e184200031151250024010580c5d810 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 207206744 1250 207205494 207205499
    0x9121d060405010509010c1712071b12090b0c07080d1e030b040b0d14100207020102062a0a05030f070c08190e0a030c08150108070e09031908060301060609 68
    0x1860901c5503200722418450001190302269000e6a102984160403030301c1007001b1300440340740c0c1543e9440249850120b094200c00901030f1401140c032040d40c2c44100780d6000c1c4044940c0e0b20baa88506d5483c1c01c14043c0164190300048a40c80440180812004031000c6e1003503519107494149003c6d6101003000a101c40241c003403140b40d1900d01c1000311524a0325011403992700e11030100d001060440401500305075040514420301c1b040340c80c0103145070000742c22590031129043d0440200d00803d03e00a00603001030001c50105801654210351820717030305903204010440c2e00203034065030340030392107080105401104000400204240c0c2c154004006c1c108460000043c0e0b0795914240309280385803444035142590760007010300c6150701c4090140082e00358408a40c8904001403d0700641c032402d50f03d03229801141c0c9030240481950f0f41216043c000800f0b0740740c1010301c490b0000300700501e042c031a44001e000c0c460030f1201209007142144d4160b111071149051240606007598a540c10030018492141c004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 207207994 1250 207206744 207206749
    0x60303070f030e062d16020d060b040c1206080c0a09051b0a0306140a030f080c010213150807031a0105070201090e0c040518190504051009121d 63
    0x494812590000307800c0074468031441c069a50074589284160018800710b0401003c0405c0d510801905018860240c816542e03014070180701c0c80740c0c1e0400e044142030414080010f080500d80680d80c0c0d03105000200d0022055400701302150000540c03080052000c40100c10003c01c14030814002d40300520280010340314020100398151064131071501b4071552900000c4108034405408540c020410001039135594003044002d01910480c09495040319130700d0b04a042c00d140000d0b0484c01c50f03600c91402100668281c0301c01c231460b088a542142255001c02c040001400d000312880c002c1c0604503103408001c407051000070200d80c0010500c0c000d0602e4458403900003540c80140148c2d00c07409103455507440c0e88030f200485803010036a004a0040800c07400b030144600a074005070065440030f4521606c0c0603050501d54002d03040944000c95044454140e0701c1c50002e0a410855109020f00101d03414026031240c41c00c11100d0301001645c04224a921034085070f54441000c40b80024064402044140d01000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 207209244 1250 207207994 207207997
    0x60103030f050a1808030415020106050f060c1f0c030b010305151c0c08030417030a0507030f0908030a02010e121e030405120a0c0c0f0b070f0c1724060303 68
    0xc0d074060000215203000300714404c0034002038034034001d082c0840c42a510410550780360864011881d80107806103000d000c10b88140f061208840c0300604440f82e12040c1b0007030140551248000c10380f540550240c0c1a034414141400c0e2402a1200700001081c281460004040f1140d060490b030401d401c00042c010348500c400040441b407070084507509401d076100040040c020b490398000802d0346070f4142c030018040c100131001d00f044409100c650120b40403c2003a1903100e1181c0030840d401304ad0700f8002140400d1003140c4082d8400124200306000760303210f10200c0d1554020b01c05000041c1c0d103c0d005c00f03038400c40c24070156201001e84002d0601b090742c04040340102e042010031348070380020080700240600030104003881241d1030401301c0035078a07403504c0002401d41045040c06d0b610320500c801700240b40381c21890b1800c00c03075800c81d0005040180a6403000d10040c00910251540070030124042a401045040c08401c150b20400074100521485008103a040c0806017600542046800b04045901e0210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 207210494 1250 207209244 207209267
    0x320030a0b030304180504050715090e0a09140a1b050a0315020f12100605030f0612010e0601151b08160c0f12030809060c0d0b0a0308030a060f0806010303 68
    0x280301040a00ca1107000c02d155024980c444102ca2003084003100c03094080e5800907000318014801d4500e19521490007100e180d6100e0808000500030210820901585440d007642012800c600800c1c450001e4071444481800a035080c0865000184080100500074000c84440d202da0403251107035503d41070010790500c440d84005840b104802d81d103001f160ba4290704850320a00d80da070a0702c0e01d03040103c43c2c1040018088030002003864081c44003007106402001038a102d5110408220140e80e203101c140322107201500014644d82d92607004095100c00140002030207095a03824100c0d52f084801001800c904400481180d02000800d2150104603541e0840314001c480b14414060070529180c200e610f40725551010601c0b081031307180030950800000024006c03601a41e01c03204580c80e0524080d4640704180c07540d008001040011816081203900b012441c000020903c2040c16521348440c447c95008860800c0e00039a520303014000c3c0d10f0a8500c1a02400c60303040180080c2d0705592703010704404d4918 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 207211744 1250 207210494 207210511
    0x70b0703020a080315030607030e030304030e0d021003020a02122701110111030105010806010e0a051003020f030c0d15060e060d09080c0604030206091b060f04050d080a032003 77
    0xa155000d16008020703140701c590b4400c80c0075a492502c844071801903801c1140c0b0b140729006090115040512034020b5a0500041e0406103240d41c0b9103035801c2d580990f011150310b4224402c80d01002c0560781e170031007207012548181c0740036a40340c40c4c114000f402c00e1180c03d80c1c01e00b0711005111032090040f100900075a00000b05410002c0102c4032001641c4030b0b188904c0e0071009608017010000c204840101640c101c44003a00c0b410030300d403510001981c0c0d00c61401c5441f900400202c4040040d0320b030403503003c0e11410082c14014a410042001001c155000701d9214940200c000f81c0c00c45002828459489011860b860700e00c852410844001d00c000303501e60046116038404550051001d0b01c035401030395081d51100321540c0e40c1c50790751046615080119010b501500400d4000340490303002040c005e480b00810300003444901c51a404011464101503030401c1103000038080464a52204a1078801c1e1070300850341c0700e445110300c00703004090301c80801030140145012000e09403420341c2c0c903055982100c000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 207212994 1250 207211744 207211747
    0xc06040602070b0d06080304061d0108012103030216030c05061008150703020f18010905060a050702011b051f050114090a0b120105070c0501110705030304141f060e06040e070b 77
    0x401803507001420171500300300040d0000081c0001c089801c030b07414000396550300c4005220f582034000103550380035003441407203a010460100961420501c15074400345c1c034841d0500509000074011100038061000a046010030000d0b0000381c18008100030703d40c1d101214031491109030b13081508494036003942c0c003030003600040c8003000b0039210b40c0a901035921741e410744c03081c09488188a809030300320392180030b017154040340c114603002c0780750306005044412002e03071034a44030b00d02001680115416101446104a0020041c81c80380000700d042c80203561824401d4041003e07500b1012004040740c406130b0000120240c480700403004c03501d41084d031542c4442425400201c8001010205003482101d1002907015440c04003000050394000c0513024045024000030094003104885083c4e00380700304c11000d492a4020310000300090b01119000042a101c403050701d040340d1020f0b2929110004904054000c10f440d2402405000a081c04050f44a0000c480500421210019464072402103014400d5403100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 207214244 1250 207212994 207213007
    0x50702030417151612090503090f040f06062d0207180e0f0303070e3f030a0302030402092d1b040308251e0309150309050c06040602070b 60
    0xd110040d110524040d18402515096100e000702022070011600811417464500310084642d100b9100310b280c3c0200110300c2e00d10b1203000c001e0b0709290801c44592058039a0a0301161681034000e07140200384d5621600c07084803c1600204a8601124840b544440b024440503c03681e4000307601c00440c2c40e80031400d0020080c56803100c1c003810805c042c0c402c882c410f0380d480c540420030010041d131084119541d80019801050100000d20740012075100300b0364510304070309040300510707c282400040015002a0414440f100090458000c11038101c0425404020072065091030300700541d0180c00501c81d821411030b480f140143c0c411000c81002c0352032a0440000b0b4152411015400160038110300d002d450355501e2507c8909a40900d48240100304d841140c4020000400c02d90384117a58400c0003c081c0c4481e150740010b107103095203815405c01124150010f400717407a030b403003050b0410301d66503011403040d0300e0741081440c0003803800c030440c01288200000c0112baa4041128410390358041011641e452 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 207215494 1250 207214244 207214289
    0x70b011203120207030c0209100b0d0b0a050306010e06181303030902190b0301150302030c0d0b010909090b04050105091b120c0a080609190206090103021615020705060a0507020304 79
    0x149014031042c03070741d480012070409040c1c1010858554501c00c89010005603074005041c14400b00782e22038000c444400b40040d082d40500b40d0850440710001601943d81203a41e0ba000a2901101707030300c14070447c51040144003240c141b0300e8609503d035a02500290305418107103c0074050281c0420090308055407010a401156035112902d010655a07520710000b154550b20744c0c840c43da1082c820555640c407001d9000c50200d000c1c1c02581c0c450301e01c08240b982403e29400001c40031b0900504014100510010040b07546515807040303c3c040303400341003900070b145010300c0d056084070409401d1400a81c00343c7c95114030700c003010220422081080d5814090801050101032800315021311003036004801d04008156000000f8000388542c851900711401210f4000c3c40c554070220300b240107504060104a640722950194000380145202140c2e05094407485440c5c4069050502002c0030740070344c0024405007441800c20543c2c0e0000d00c0a10104035605103170710043e40d24840c602c99540701403124010940c210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 207216744 1250 207215494 207215507
    0xe07061d0d050304230d110607080c03040603020306120606031207050a120503091603031205090f0708031908010b030114030708031c0c05070b0714070206070807030212070b011203 79
    0xd5a00c00101ca450b039484810007200c0750800b994140400c035010003504c500e4540321180d140d806d504129001c442c401d00da03051000340d5004110588008001304103030000d681041000380001c104c1780c1d40060b02c81c24486d040001580041110b01d0a690050090040d1590f0100390707600c0d140001a94580e55040d285840c609010290b803024000b501d0a1256213802900400198450030f03121041d00e521940c216110019503001d40005130004021607800308084019600c06900034051404480207000c0d0508581d00e04010791708420501c4e00042452001c00100b000e01498190041c200b1074141d60600d25402d80b00d000500c609403c01c50310707900030101c0d03172014000722000c4c1403104241c95a80300641e101041840b00c034141400c00c186002d007a100018491800e5508040d803000389684152110181181c0c0f07101c07030744039419812004020903c01039448400030500307580b045603c0c0d620f0360101d00340a81054a007100c101004401041000000f80362400c00606549048440c0c207000d007074904044030344 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 207217994 1250 207216744 207216769
    0x70f030519020d05040b06060f04050402070816210201020c0c060d0902090f0114010306180c090f091b080106020703080304060b0a030807020906010f0f0809030c01050709090e07061d 80
    0x40e07500c0003071025042c0391190031252280e0700070b44c00e00d541070711403030140141e5101d5802e100340d98580c240401d00c403d141079001480142c3c090b4604608100001c281180243c96041040744e44030780c40180e5800744805c88400e8103841001e40001c5040000402086485542c1014007620407400060101d610003041e61044022a0f0060f058a56030325001398060754944080c010488440e503040100c10080d846406104261019668040100c7d02c0b03080300c1c03001524036154140184043c0360300114404044201c0c000003404004404280504100c0700c0031035240c0d042200004000c244001400703000e40028000c400c4a90001d0040e07920340e2213003070050050040c04081d903030154100d2030000a200b004c01c00307415510b008440e0410785480d0107005660505021a24402007001c014260f12210701801889070b00010000c01d0b00c0c54803640482c0913007140d104840703c0300031540d20381091144420501c580c000f4445060020880c45007040070180107941c5a19194507807108141e460411074036080c422000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 207219244 1250 207217994 207218041
    0x20c0f0601150c14030c07090f020f07060902040902060a031d0c01050a050a0e0a170d02161502010615080403020f0303011a032a03061009031a04020607150b0109050306070f0305 78
    0x44646c0c85442050302d9110a200b0042c4da00e04003203d1020840140c805c40303034110b125051813803619102d9502e40000e0800418142d81c0199692044009600e41000410103800b29550001d0788013000d1582d651500d500c4145a417441d400f1655111159801000706c984e400303a0b038241140c50b0101038000b15005041c81081c183c00075240b450010b000381c01128005a59000d10b420b035070b1424801401265240c2509800700c1d115200034004102c41c00040709a87c084007136900c004a44552540700346401407507007511540c0020722950802c014907905010b0881c4811000c400307140f0715450195000c1c548102c80d0000148500000046103800400c2254207804080c6c2084100b15231030244c05102841d0001ca4903580518401c088591219100d44011016261f0000905440d4540c00007881641c620040003241c108078104444400304102510f10107014079103840104043d400c4000042102d00341d0b0b8000c0d4000d0780900103200e0790329040300301c0350401034003450000381550317965500d0307113028a45501e00c02 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 207220494 1250 207219244 207219247
    0x310060303090510081006110708060c09030c010804030203030f060424060906020102090a0911040302150c07050d03081308040b070803060f0d05030d0c140a03020c0f0601150c1403 79
    0x30805410980700c2c0c0032104220751090001420f8042601c0c0340e5412941000c5188204005101b10703805840480604e0189100315203c0701e0303c2d154854075050041d1442d54031000003060304805031500700519040b0801c2840c040c5214140b07946c0c041d40d280005481c3c010301c21138500002d6615107960f4403404420311240303419041d02420407050061030083d8014000001ca50340c2000c01e80500500071954140c402a1110f00d04603d07047c2040000d021555600100c90010071000000d643ca5840001d001d6810341d00c401e580d0b410404106242c48829400300f4081d080a20705400800e41040e4a154400307944003c1d0380c0424603510740344246201703d4101c003842100c0400e0020a1000b120b01031441244207407542c1c0484520300080003180003940d440141642d00c10042809000140d030400600c58003c0d0500d90380c4c030540d1040f13a20081d00445048030000740d0101d00120000e00c100300900c8031002840141500754140100085901c280c402a00181300142c0b140004000e54080400516221001a02d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 207221744 1250 207220494 207220499
    0x31908131206320408090406060203040f050301050f0f06010c0204050907060215090703141c0302030609180d0e0d05010606030c080a0606090611010b13020d060b03040b07080402031006 81
    0x100101d81120a00751055032a03c010400001c50304603140707811200c8018083c20343d03250010440c559441c001c0003210399602c00c1c41036001ea901c0300e0184a0180160f600516111410211108003404040d0300040c03090b0b0501003408450a0860f8a981e003200342e440052715241e840d440166124040e21400035002450041000001b20000c41e4802c2038a04681c02d41d184240c01c810107003207800003618444a1074019200c1080054810ba1100c00c0c0349040d00c00383e90040c0800101c0c0c2030000644181a03011980020400a03503240c03404d8255842810140701302031414901c428240d440a05107010028850041e4a085103a5100c20360380e241b03282e02000900810b902d9100041c09008a07014034800700ea0940d0110780c0c511107a0240c1019103440e950380c0382ca002d2805008954400902c803071414103560b00d0a1107602034131251204c1c030708200440f00150f65000380c104603000f01d44c5290704c40c004200f802d0081c80001040700d5a1141c20888900e840f5003503803580d0002a040049510301040c43d10701c1c10030b00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 207222994 1250 207221744 207221759
    0x5160b010f09060605030906220f06060323070b0a050403020d060b0a150c11060702060c0f06071b080d0e03040f0303080c090d121809020d15030203190813 68
    0x10301e00341c403005001801529a90481581c00f030009983d12007090300941e0028040d444001c110780c2d0103c1441000981a00090704c40001210307076070100f5124107888541c180306114130b08107040305544084102e540c00d100c0320007180b6250f540b03c0c00b43c00c912150006441a1051092040e180a10f80081001d8402c003000d00c2e01c40c000b8000c80c00014001c2009400001d40c0c131000c056034640680346600c45449c0c00720103030740d5043c41d003040c42d001541c0610144415809130312410041c20201d005d100051225049e941d9085280c9017008140d0350410045001c03104a2020407106414600e5000c807005072201030b20000070b0003411039100030381900c0c8400b00300020107807071119100c401c4030b00030b81311503042e9121554011800d1183c48425500b050b101782c40c040c0006c4a0500703a0328401e00618041c40e441c0303d2000d442208210a40c0031000301900402c404031803101c81e204007690480490280313245545580d0110ba2a100c550030410400382c01e2118031014050b602d01214240703004052840d100035103a104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 207224244 1250 207222994 207223019
    0xc060c02190b09090a1d0115060315030605130f0809010315050d080c19120e040b0a18140a091b1d130b0f01030605090d020c130e06090d0f0311030705160b01 69
    0x220a424081208006485402b0740704207004000c0e58076050340360508580710000542006010710254800840c41070010403200b1540303040503485103413204e0356190003000040176076980011054402000c1d030300801581d50f03200e00503c45994484041600c0303443c4c08032210308160718030740d01c0c20140402e0700802c01004014682c00c01c00079841d44a81c0030001e01142440210341d0030802594015540000500a4560a0810410b06d80c0c8036000882c0c41c50813403215561104007039451000c03280e00c1d032003072404103d15581d2240c1c1100300304108404c601e260035402d0203411000c580c0b0002e1811040003040c900c02100707200194680d040341a24a85081c00d07104105800400d03c026a08540703008080b07140c0e080e0210702840308190540c000c01c1c1d840158010012043c10070103201e5102903171804203901146017032080e0f501c10300c441e00207800b819103140000f80000c50344c4408941014a8141c440a902d0701200551350002101c2c5001c170348680300d024510090640710f00000d021030408400000320f0b1255006c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 207225494 1250 207224244 207224261
    0xc0506031608071b020f04020d141008013605010c17070f020a02060913180b130b0f0a06270606050702010e06090307030c060c02190b09090a1d01 64
    0x792400b031290750340101151281800000c0300c1100b540341d1013034405803800c0541040984001000149001c045400c00c20072150030b106007030125196401000340c40b0401d110140003e114200c003c1c002040c8100031300031800c4001e0040c1d03110704800c40c68004004984031b0f0320622503600100070405116410400b801800e2180b100c43d800041c440b0001c2c0d1030034802c481444000089400403d0100e01c00c0e400c1100036000480c58640150402520303e564061600581c080c000300304007444030075850360514058110009009464015080700c0d14000540c81d00c0310a1360080c0003814203e400e460f03c0e1158400340001d03a0110304400c501008440c0b250300c8003010b90742d0085c40d5010800c55140d072104240c80301e00a081c0b0203800300303900c1300390302025040110003411003400040a41b00160384980d50000c1006040c0c1080c0c00003a000200c0b803045050038442140e0912540800301c0f01c0ea80361000b9964140304020003140100c428034081044140c040e002002c480d00d416440758503003100c1ea42818000c11115 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 207226744 1250 207225494 207225497
    0x9090a020906010f1e12110309060c040f0e040201120c030b0a080f0c010e060d0501080706030506040b090711011b020a06141302100908070303050309060901050c160c05060316 77
    0x78000310b40c0560082c2c00140d013102c01901c62400c003420b5407240019545a03c03074401c050111104004092042c4c5120380c1610241507480117840303040900c0550314119005240e4603003003200300001c0c000081e1008011003224a0000c0c90801940c032480100d401075862102c901e003040c2041c50f1501c0351600f5400800540a05890956155a071208020380d82d420005048180381c1003c1c128050b594421038500f42d002401a1640d850004405038600894809034000c1c02d003a08034103001d0020300d615005440c1c0020045a0501506030407400150000300f001e01070b2002e210306462036481842080d04070015020b03881c50442200140c00d07101a44801d69008100c80d107501c4c080f130b403903140c0500e1603142d4000c095110305500719543ca5401e0029208100602401b405010752002070b404c80100542409140300e991103035141c2c2008103840d89000030180c14200940d0500c03041102c90208a000d0315000703242688114100e40d61401e2902183c142504801e8012100100300051941080c1c0850142c0145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 207227994 1250 207226744 207226759
    0x50d1205041a0a021515040c0203071202010e06100503100504031704032304030c0b0702011404080d14090306040204020d060801020d1b0804050712140f1f02120402060c010b09090a02 80
    0x45d00405508503001c58040c086629008109911800d0070392048510703000900407603213481c4032a00e80c3d1815800c10792100700180e441d540c40d059803200038405a50841611a01d40202070304142c002911240031503c81c00c24159070740c0026003818401c0c02d040350b1180c07603c10444450300f000c0c107000703020302e014031030b0f100e9540214a641104154280100c901b2a40c005a0b41c1030048d040c030840b41c0c1075910040c4281d041014207150304503015040f9000b4401407501400502c0105d038070701d00c003501028031900c0740c0a8074102400940103549001c101103074015030454006035520000000c0c0c90040c009508020f07000d61000c901e4000906d21070b4045154090101504200e0214240e001c03a01c80c1000c840080543d007000390704004042c480d905614600d4400ca1505040400c11184689065001010500c1c15442000031640e00320b0682c1c02c2c0940100c500d2406d6240140307481511503039403c007520082c0100c06c0029940410f072000e500c400d0f1031003002051000c0e80d052000c4075903a2004d45440c01d034401c818 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 207229244 1250 207227994 207228013
    0x306050d05031602180a05061801150e03030c07090b04050c090616050a0f080d05070f0c0305070503070611070615120206131a070c05040204050d1205041a0a02 70
    0xd09000c642039040c1d00c00300540c41c1c80080300e03441100f162110400c0341c1000780c1030502d8106200d80c3d105103200c1d080c180d40c00a240c0c5410301c2006503003a00e90f1444080c0c00b415800600030900b1440c0d12102c00c08c1c4900340f29401920680c0403c0c610f03c10850341201c240036070030003c0fa0110050b001030414580c1120248602d0300c42000c00c4815104600490f40e102200304420703a071b802c0c100354040c0d995031b019109503101030406131038110380c03d0400380088401c43c000007806824a501d0344542504810b0354030b030040805480e03150280840c10442006801d200c0041000f204201c4104201c3c0c400c503904c201c06000000801210b008260000310003142d10509000784c12810b01c544400610480d000a200c014400300320360244038284c0c2c0b2a25030045801c415030400324002c15210318041c0d5440c0340d0024265940d0850800803241c64190304400d1199004010802090b901e007204010403d420044050040040c0482903a540c801c6074000129984942a1615001d0742c000180440c6c944507002d50700ca190 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 207230494 1250 207229244 207229249
    0x6090102040e061c0f0809090708010311150706180309060e012a0501050f070e18010905070203040f08100c0305060d0803060303040b13080f0a050d080606091306030201030605 77
    0x89028500c460b410441c0090014070305040400800e49401c158146074103030351340741c5800700f50300900295240c0c400082d81c3c080605000703281030b91104607403400d400703954155918034400705005c04c0c2c00c1d0310441c04111600d6158110340119541640d03c400d041005102c0800410410000c1000a5000c40d040c80750000d0014020079071044840c005030b49980c000c00002c030030020962902e40d40d10082d1254055000c000900c01d101e058020002588003a100e0301d000040100500341c05400340307004241e059140604400340b028414152406010003003226a01c1203800ca1450146030302400406086803c00500001c0200f0742800b070382d400d50b805100940160701c1c10703403c0d40c8007a6071454202d8108680c070000b01e03031124060f64000c2002000c0e2850a0358071004220a5045072030311100c06454032404104282c010058030245c260b0041c00303880404001d46407aa1600d1a0030340c01c400384198000011035940e6024210707040c155000f441d2010b0051401d2455004007514042213002c20300c0c204c004100d40c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 207231744 1250 207230494 207230497
    0x5010501020c03033406020706151202011e0e18060a0905090c0d0302030408030403150e0c030a030c0309120305030403080901020315060708090a0e09010f02070b010504090c0e0108030c06090102 85
    0x8440383c28000043c40c0e5510017007503031601508210704a00ba1031840d00010404d00081c2400360240f20086626260011000014800da5005100d400914181d400050760015006005080007910216124002180640700055105002680480f041d695280b20310f00140c0070b94042c41c0c05403140c014080d141c000c280d01b110015106101242e100700700c034200a2500e00d0030f080700c103031203441500e09041c2e5404146256800c6600b007211301100718200c80d51106218402d8040d015001401000002c0c900340220380c848410351805020406900c01401c103150207186828018840380c2e05220801180c2c2c02d000702540c0007602c0450004004d80003142441c01c05000b6280190740c08000d07140078064001c2001003691000c81c0071282c2a609000d01c0c4160341e11a04150001d0130b110480f402d003864400007043c215100c0200e00401d107441804103c01248594100714156036066500240130005400c203102c6d42d4030307540d000306071f003420810002c42c10107408000740800140300400c660702e030f031109440e181c207030f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 207232994 1250 207231744 207231757
    0x10306180c0509060a0b040f05120a030504052404090e1603030807051b010e0c0325090504020d06150503010606140706050c13060801051302160602180402070605010501020c0303 78
    0x1403040750074240403d14010454076003080000b840200b503107a40c1c4030301010903000765004102c25401e00d0800c0140d42070170070f03a8a0303c41d00040003505c0074085030340c0d001c0c0c41400355000c4d141c011081807104402d040308242813643d0006000c0d0b06107454640d500b1569016098a110411860081d000c2408400d4010070790303d02640e0341521a20a030303941e9090100e49940020350102602d40c000d1020800c5000300b071107034007115244000a000001e43c440281450a40d450200341548400040c851010383d400301521000c1e03031103146002c43c0c40d03203c43c00014554008000040c01e060301d00b55881c5e21038490741c42d42a00300c410683c0284662a602c003401d482c080200c0e03403119803581c4100704c081d00003203070b5074002c1d54482c103640380f940d04020604d0030741d0240c41034503000680856800350060140789070001ea401c2c506414118250724000c0008082134200031039010082c40c0d2a00854030500c01d09400008041c0b888006c7c000310348400003414040701501d4281324150160080c0c0c54411000d007404411500c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 207234244 1250 207232994 207233003
    0x6090307050105030925030b0903040608150103090b10090606170a0e011b03060305061b0904090201030b060f04030614040812060f0607060c032a120605060c0601030618 74
    0x50440c5010010b60f4140d1000b40340605900035035603040c810700c021102d0240c03220030501c0300000107802d6103040301c1c0f13520b005440c51183d6401400104400c540c003144184c4c1c061040c1c2c04c2040e1a00405006030040c0c0300070381008140c8000c000401c80d001298105c103c044641940050100690310390041d11410300c80201986441c3c151000103040a0380e641055031503201c10000007840840264030f0342ca091030b104e046c0302c002039207804080041c004108009500300c505d001c404225401c641b03081c00034078415925118010743c0c4078184001568000c0d03012403820744001d8500c0707a0302d00030442c000c2a00c0e070103404201d40030f82c0303001840204900340f04141c51085900c0701c105464040c0103154404511001041168400c1d068040c85903d5140e01e0090420240b040c000860389800b000300c00343c10f8662041c2d403081040c40003004011600c807246000c0c0640501e9040045028040c95000d00c05040c450b0022600036400090032980e803030f00090414102d03400b41d44100302d0f010000310300341400c2a54030006403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 207235494 1250 207234244 207234253
    0x120e03040920030708040b01051903031101060918021305150d150c2a02100e01030905010905030c070920090d020424050603010b04090c14030406020711060903 70
    0x1020710140e80c005548100280610098002d49007505009580300b20b820030300103901c000a21040005848001d07001d0201229aa403500b030b0f481548900440d02c5100103420010154004c82030f448081d03100d07501a00030114180303e9040c0902e1410b0b0500e06000040340600030460b0100d0900055105e483c0c0100c1c00000e2490040c404c1008000f4040d034a084141d03901c4881200c403c601d03040e14803032007030807441c40e0316404070070440300120240326021500411022812651810300603a01e1a00034401e1404608064400103403810040f0b00400414400034029803a0407810320500030000050aa000c40d400f0890f0090b948400c0400151045000701c08814504c40c8503010f0804d4480c4040e00c0042c0c001703040b030100008a900010180c1c1d100b10400407003a40360709a0103071002c00040d0701d50040d01c1c2c1a10403600c0c551502c954907407103110324800c049006a6070902c0d920700720720644000080300e213901d9000791682400e040440082d800590b04964115030743d802000141411400e58540140040292 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 207236744 1250 207235494 207235499
    0x203090a030c1407030f0b01050607030e011b08120117030a05181503040f0b06190504050702030c0307150b2215090c0207170105040f030c0c0e130201120e0304 70
    0x241d4070301c0e00c40c00307046554803d0002c01454469042004500640c00307445041a804041d042c42c101e12001070300581d0150b401005884c01180c0c010501e0b640c1c106d070070300c1c001401c540305d6082000b24808500f00102100b00c0052131060031020665040e0507100195400110000d0900351160b5a105c0c035900f0340003241d4140304c2e1900211802080c5a81e10002030005940004210303400c48540c2d004a40495590100100f844103000f0040707541940040c040e520110102100c80c0d042d41121346034400ca070301c01c0f030316900081c507100e2091003521420760b02941125100c2e09145889030b103c1e080000070b161020300c1c100314620949404107a04090582c10070070301d03140d900242d00e6480501440c1d0000c003d049060400022000c6a80c801e201c0c0d900d006502421300c80d4201012014481044480410940e05100900001c203200c0402d512510340e15040503109100e4500c1c1c884400c0a072036000b414002590010000582d4600101132542c2c0e100741d07100a160075048120f0021100302e07c07a0f258003640144400d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 207237994 1250 207236744 207236747
    0x5030904060e041e1106042306030105060412050102040308130806070206040b0c0c01060302130b010e04060806070c060f020a091d010b1c0b09090313120503120a020c06280203090a03 80
    0x100c5003460301841e45c01407444a404041005a801340d40441800390b0003150381200030b0406801c03007240030000c851103403855160030001580c40c001ea0040c1e440c01050441700d90100031095040380c00665104508036103c1410b040da00d500c1c9205441048807501940d0002203641c0c1c800718010b40b056a00c000206e46544030004400811713040061241000c0d96201d4010025907220341d440415010f04a4010850101100c00100031031440c5800c80d0149080100c28000d01001098640c0c0c014030078a00031240544034101000078007035440400c543e45100060440c0010385c022426015074145083c0110080d9040c2e01115500400f449484000d41c0140010310481d2888101c1e800b0310b5860a4020880d400039000050004c1000d036100d080d20b42c0000b41e10480b9844000301031006040d650b5455020340f081c0c0e280d0540b83d1040d0b02150104204600000d0581040c5034107541125411138102c4940d0300d0001d4200c0d4400b050300142e140320700803107030464210f10482e0003241d2041c9c1289002d0403582060759030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 207239244 1250 207237994 207238043
    0xb07030903020c03100204060f020c0303043b0402040c2c12061e0108070305070603090602120f04020f04061406070204090803091c08011220040905030904060e04 71
    0x1000c5046015800800082da9130030011000c225940f075800503a200c1c038209000d800b6480d40b40c0700c002550003d105240382c660340801581d0442d0007904000ca00c80003041a00d129440300804140c80c98400039407482c040a20382d8048511852007a0344c00c11445840c0d900c103440502c06140c240d5085070101e8040842542e50350440c2a41e068003601e007280088524421a00b0010f0440c2d54204080802a802010300494a00c150040c08104042c01c07603d821a00c0d10394072200d03d409001c05050320b90140b881080b94a44c11920441059400e202c40d80c00e100c207040c90309800669003a8490106980211414945840b51904840481c18421184006103007402441c1d08200001c1c1d9004d40c4d2074465002140c006002503200e42420030240926000070010003048195078135910341040418170051040000c00b5264072101600244880030050341c255400d400076516008450300507042158501c00c1180c00000340003c01011141404480d4981c0c841401031170b0100c50142c00c000d04650041855051000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 207240494 1250 207239244 207239261
    0x10b03040b06100e0402070503070606060f050a050a0912061a01030e0c010c05190b190510051e060c16050d02010c02090703020c060408030103050105091c030e0f1603050709090b0703 80
    0x1d04d030070261a5040018102d8014100c1925150000680c0c6010091284580b0014118030705007500110f000741e000030098001d40d15800c0c248607001542042140c01103000d0030042481c0382403026001800d01d40f510141060000c2d40904004400010500358017074060403001646032002402c9084842c00115000c0c0e124050903145c900444107440e0303c0017840004410524003032035299005040180400310308200914600785000d29140c18062031007441d01c0d16a045683c01c0b02d01c00e848c0046043c3c0b0400d4410074a510301d40c00b0600103140d06500c180415212442507040485040590f03892302484417400c001d5000070300140caa075400300014980500d5440c1c00405602d001410310002803442c5190040584042c0c600800102c01001041000d0041d40d5020301200301800e0800020744003408500e0300e42c1c0500003499180d034004500c0710340800001c01440f401108071806449180101e2000c131416001c11f55150140c80000f0901c00598002c4001456000d80d60510566803010110024070b4101e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 207241744 1250 207240494 207240497
    0x6060818190c050a0909020901060315141f020715020f030d020f070b090c04111e03060103090b0f04061116020f120607020d020f0d02060a0c03140903070b010b03040b0610 75
    0x2801c0114a60b01d07071610307074005800c5d070440005a21502e40100400076005034010f0b810182003101d0002101040703031141c8201e03456001103450603190040020000d90901ca02403507140707904c0808044890f4000703801c3c4120b81040c5003100c3d20888164049072114200c00b210801759000b0854007641260075401000c0c52146403020505206d5203036110102c0c1c3c0400d84030740c10984d00c01c0803002640d10301403081c0d18a00ca2481e40d01361900c4e8040c4681c461410119403171100419011000445603406900308069050380200030361884c2c81d098000004600c07059605990f03161038282c40c1a104c0494a04451007000e0160541c140c89a0707990801440c1c9040c0d10302c1c5600510380856240700400204070b1076004802c02d40140c141e03041c141d48021f19211040d0f40c5011a9800425203840840c0c02240e140d42102c2017000114181d010058254080d0507480380b00e15517050300d041003143c0c0200c08406040f9061142d031151002d0b07641e444006045000545020741a5080d02c8080340c0340b894441c48000d401c1d02903 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 207242994 1250 207241744 207241763
    0x30a08040b130b0c010906050109090506070f0530070203070c0e04050a0b0f060424030221160303080a050f0606070f060c0c060f02040b12070c0210030606081819 71
    0x110f4a40d10466080041c2c441d54981d1100c00c444100f01d42405118094070b10501c00b0040162242c0b40ca80c0d8400024240740203004104810303600e054030550480d000444900048181c1e400080d41d01170341d4040410020f5007107a000e5022a45052011044581da1604400d0340c4550504044441c152400040c00c2103400c0d01c56180910000745824000d80d10540c00001c1045540c94010240002e80c0c103001c142e00e05060a8440c40580c440758070000e141aa90141c800c000a85500d00b01d6a8100700c410100c04000e1184104074050f004400b15594141d038401c2c0d480d5800c1d07440b1030303180e00159001900c0c4d080d00140d111340000c0765800d2450142c00514051041d2804105883d00c5d030400b150740340f414410000b80360311910420310086000d03c0340007105078102149842e1034541c80750490f0060703a1180c000541070380007007031280c0e110b420084061600146280d41850601101030014066032060001103140c220001d030142120001118000c52008080d041c03250010348000310b0032005100c111903112a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 207244244 1250 207242994 207242999
    0x406180315050601020d140d090f050106080307140102040f0b070615090c090e040b040303020f0418050403030c02010513030305070203130311010801050d030e10031404030c02010e030a08040b13 85
    0x81401d100c100d03161801100041ca800e120000904240c00ca0042c4c1c000d200f04911080d10b00c1c86c00c1c1045440303800190400041e014020b107003200c03e20680a80c003400a40c2800004a07401c2000720003040d615104500580300814298816400d0303004503c14003642c2900f040f01000540054001000098828000000e0070181e46040030041291a000a40900c1e0f0f94030541c0030342d0b82c020060b103015101605582a1910b029954a800c071030000348024101030700820700c16040b0310030400780c0b0060f1031400e200d00100c1d0b105040101c01084111b8042c3d0000741491000c141144c01803007814014240080c184a01e9076407510180c0142c400a82007008500c0100b0869a0814103040750358003451117902d0342c1440c2c07070400e400103000f90f00680165102c1c42e4020385103c00a500030380c05520b060415241480d41d5110310301c1c04d134002c207031004000d01d65820701300410081640c40860b02030610701c04d885400741d10a089081c1503a61240041c02043d6002c1040144189903103800906140118114856183c7d034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 207245494 1250 207244244 207244253
    0x7080a02190801050907110c0d032003210103050c09070e0301110403050d05030108030a12150303110f0f100509070305191205030c0405060a021203010f060905060306010504061803 79
    0x810221020000b424000060115241040c03402d034100b180340c5841c09807503001d14031403a140d0791280e8115201b503045012035020103010319685a040441c0c0f8640340c10158042e0b8146171268001c1d00040c8a803240c0c00110b500780c40807480c980e81600c0d0080e0003004c00d04494024022580d40c007034941c1d0b0a00c8500110244180d509010394450403c04a0580c0d0304c6030b2941c80c01c2442c082602410a0a001052005115a400010a46a0100b007a1400c5a00041e1050300c00c03004081c0010040b000c48440030001c42810303005802c0400e0a03810600711014114103a42032522481504003140182c0c220019035000001c040e0002d5030058242c40950300c860369640e03211484c0c8294190b540380c0240fa9446200203207c840c1c4800d00d48013100e41801c500d90f150003800c1285d2481a0300030319204990114080b0300092081000c808641c810000d221303a203586038040c440310842c103841504c0000c1d4a1006c0840c45082800940c2d02030f83d01a1101410700c1e007443c0341078a08401e034800740b000c0c184e81100c0000109 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 207246744 1250 207245494 207245527
    0xf0c15020c030c011a150f04081203040317010b0409022109010902180105010507170d05010303030b03010b0f060909130501091b0806040c03120507080c0606041805030307080a02 78
    0x52205001103541c0e60801d4001400d4030400502e100d01205420050202c98035030041d408100309006d01c201e540e8100700c1100c0291070103540c000303d40501c1089100c0107000c82010042d805a8025101c10071510085991703078401031000d018041110505000401c080d0b086ca4001d401265000e50b83c203000a0151807a080050004032008074060b91500c0f06079055040804010400e450001c48c040c80a41c1000300103005072141120003080e00500c02405410080c8410941e104950300f81c1d014402540d481c14010013505032072084610039464284c601e03810385004c201340a00148042c203201d003030410340b8040010200c0001e107900c203640e020402c0c0c0ca001640c00c0c46890308013480307402e04034050000c1d1010710300d207d486900041e0031980101c0a000200e068a04504100c03584000c00303050741c0d42503003030850b424056a48000e010b1100403034042e4200c1c0340821100c1c4210b009a0f01009480c03030a039100c03c0302e540d2000340a4001d420400114922603c42d840c950b0748000155009490301c441c07503440c00e880 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 207247994 1250 207246744 207246757
    0xf0e03070905090a0614220804081b01020106080118021c120302040906170a0b061c0b04140102030c0a03020a05090d06091218091d070b12090d0f0c1502 67
    0x403604851140402c05c9464490400c01c0403100618400610b081500440d286074280407200d07004590708004000c00c41e022044070050858401238950480c0c810b0079020b00c0340203d810b21030155080031004901d40c08144101000344101d202c00039a1369119400b80888424042c501034510f000004020010a52455070341015284950380169190303c2d202d101001c94070150869100c41c250030603501021034000801369a182d8120707050701c1c003640341c11000494042084c095154250380000c0751105200740109014030460040b046e1070307031a04609003070354202d100031603d540040f903042c080e51035040e00c00d5010b011503002504203145810f02d01800900c0400d0030754000c44034103807107814000070003c40c80320450011030b503820304158210704012050030303000040c081c102103181d99980303d010140190490030030050303168080d2402c168440c42c255469611248919403400141c1001c100d5004001a40000079080365403000c80024004034102c40000e0909020744104050400a00080d00944002c055 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 207249244 1250 207247994 207248011
    0x110d050331050705010302120c0c150703020904060f0503030f03100e01030f030e030a08030a02210702160f051305180d0e04060e0105030604080304030c06021303210f0e03070905 78
    0x892801c910b0320924028850f00200d0405005002200640031108641c5800200394a010b030349030895215850314040e140012070490390220010710403200d4050740204900802034805003c9a921a500c0018940e01807080503091391080040c000b14407600409550001401e4010011460341c4209000910f40c0a0300107880c0e109002c1c0c1000100341e04410701804010050b0060060300482d0703255101c4034003000b011903030403a4000a14440304005180500442c0e0490541204513003880032000703603620003c2c0c03080c0c0c80d45a03075080c0214109100d039400108446000b008000036980140003c005060050407000d28440b01c1c000340d02c2c10010606c40070070020b25959031500000c0c1342e04204400d0317443c00c5c4d2002180d1020040103218646012403010380c0030f42c120108658a403074501d0125036a1583d40720140400d440840c0350040710366140089000c03240611204100c4004c1544814129aa03600c0c42002007441c0c107140314403160107140c02c07400c81c003070090a031242940e035580f941d010750300215080326 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 207250494 1250 207249244 207249331
    0x5010914180c0c0d0f0f020607090315090221190b07030924090b0a020a05070609110a080d080606092805060f0c010f02161106040b04170607110d0503 66
    0x45c05030b1003046908072868620003842c0c5820180b60240880050b0300016090702c0444006100c0701d801c03600b00351b16881c2d02400c0a405000c1c5031b00c007456900000f240407215400350704080c0c4c000d540a007038600c0c00d4581000842175107480742d82c0260001e080040088515600764041121601490050351100c1107603110007013801205071402c1890788100514501103a40f0501c1081e050750788c02410f54091342d5200070300040e2440d950402044560000e001d0700e9028035099004910900049082203c07100c0a41340c2c0c0740ca5460380d0702041030500443c0305a64012000d86414032030036807440140c21040b0410701103001816120800325149500050000c101c02200240fa002411001d00c9100c012000d01901141840591020700800d042810b2001c2c01e1100300d0032401c041c5030340b080105c030010a460a1156940d95480040d114201d68003800d18100740603a00000d02407070700070201c0ca00780304203c0c0007411310400303401d105540d40d400c060154004800212240601c4035a21301128801051251155 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 207251744 1250 207250494 207250517
    0x2206020f0d0e010c0903030c0606150504060f050307120504030e0303210f0103050604031d0a14040c11030d09060209030a050105061002030a020303070309020111100605010914180c0c0d 81
    0x6000b502c0c0d2001030300040341e2514070b082c5601070340140c60009480c0c2c180f900c11020441424101c0207441c03941c1000040b4000f010110307a060ba009801081103654584031104030710200038064a0314082240c00502150003041c08400707042d00f90380142e070b0041c46424101110134040010034910b821402840c0c1c41c0a860494040c0c1c4004818140390340a0001d018070f10096045540b91600d8100150004040c000b4a0005080b20344101801003200d980141030040ca25a03181c1e4401c0184001e9441a8040c07440c00d02c3c020b402500c45d40c006100c000c5107100540c54001c29049400003043d00000580b90142d09100000c0a0f98081c0310341c9404030b000d075002207000d080c200b04005401955895000955000b08038448480743c011060304d501c4052810b00003107401803400140c4030848400c007900710500a00d02040340d40320a66000304e0030382e94280e80c0c010041d038482d80c4020034840704042559201c440c0c1c2c40030740c94102c0d40802c00c603130206281d524a8104030380075111614025841d9102c20100c0d1245245 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 207252994 1250 207251744 207251767
    0xe01060b090a0819060b0307080303040b1504180b090a0212150108030703020d0807092d06030c05090904030c0209090c01020d0504030228080f03040f0501030908032206020f 76
    0xb10003600c1080060035095040f007008a003a5407203004024001768955505c0c00030307030740d0030b0001e08024103130075040e00c0d17903803a1918280c40c4207002140c01e01b10034403141c556030609080c1403080c00e400341d90146440e240f00d0025111494900310041445109114410200c4010307160045400b00b1001080004c0140e014030030b50907040c1090503007010541d64014819600402d60000c1c03000c2c03403c00d880c10800a55207802404452075202900040522710034a400034070720341c030a030f4010541e0502865400e0207403912044101c0903241d28461200c0004d200780403010031440c000501e150040d1082c00c1000c45400b07250302040c1c01403c1114800019000030f9104580c5580500c0325000010003487d1171b500d46800c1d980000c2d6032100a91300b0f80710034840c8020340120a4801d80e018000303841e0030030844810491100115a880d03002d0f000b8406404c00604000469502074012044655404107101e23055030b480d5100780c1070f0300a000c0c02e02016140c5c0c048206002c18041d200500b4020307074960000e0b070744108803000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 207254244 1250 207252994 207253009
    0x12030516062714210706060e07110c30100e030d060e0c030103060e011d1605040501030b340302030103030e03062a2203021f05030103080901030e01060b09 68
    0x5240c02500904110204c0c0f1914a00c10700044107141c0c803903034560b403007400d0074801420315420a0703041d500c1060a0161075608a40b07074a21a001c10411505100342a07000d00c149140303111965920041c1008202e1100d005030400fa0124440030030032100c480705003102c2c1c041507c40e040c058a00b0764000041e02c0c00c0c203030414040c900c080c04441d12520f546046c0401210100d120511024120640c4c0e2400c100381c1c0c440a401203111140d075010300030010004007011540311a803107003800380d050b10029000509070800d409818103c5c1d8000c000d080080c1d41d440c0340c03421014241440c42040d21007002c0705a20001c0b4220f00c21140d14855640140c40e58154a00500520300325600780784207501c034804024840c1a04100c0220001c13040d200c0481e560b401141018040c082d221300e400d02e112810180074400e1850354260380c2124000c441c02d0281d08030000301e4120141519038400005241040180b003c101240010005401c040c5030006034103d03000242821075000350421980c4090001d882035281c54202c2c0c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 207255494 1250 207254244 207254273
    0xf08060c031b0901050904050108060a1805071502070801050108060f010501030b03060a0c030f02031923040308070c1e02040b03030a12090503190804020901120305160627 75
    0x6030301914600300701403120080c01c40d00c0c1032040b40d6140010941100d900c03400a48112410107403040c0000e584511070703951145000c036400305900d460a110041d202c01003030f201401140d0031201170840c50b0308180c5000351740c4c40d40c96244000d61040c80000560345c0381c244661402000480e003c1c008c9401c000400341000007060f4041410181491300d10022941c01090031900032550220018240c904c007a021703405003510303844102c451880403003040468103a03c144019101e00d45141044240c20440b030b030300414000340440c80070082d680000940003d018403070a50b08040e19041850013003800742d0780c00b100c20860106010001e43d51101400460610380120b1100d280c00701d000c0c501b40440001c0c024101d034540c10003000784d203454121807024080103000300c9510600d0481642d4010090043c06411000c05030380c00c80c050072140c0c000190b905040f069042e45e40da03056581e80c1c5030131807550355001088220301c41501c0d440d54071680c240d814840d0391002c034807036840501d80109101803420a05650044c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 207256744 1250 207255494 207255511
    0x702010b040c0c12210920010804050a060b010c021309020a050a081f0b0301020c1614010801030803040203070807142409060a0302040503010207080301080c0103060e061c08040f0806 80
    0x1002000000351560b0113211810885142511892500c00000e100800c1190304014520346010b07004014080e0101510585020319586001d4080801c001100c4250046030003070031541000c1006400664075400030b1000510502d82064041e08079000190320307040c420448055143e603490410114140900c40c00000c080865100c0344051605101988400741035180c40b81180d1143d0440700103500c10761090035111400f8000b1522650300b401c04603031321440340e011810202030004000619080000000b0200c8506075683c02580e4615034803a80310307403c05070040764580030f090800b181488040203580300406d41180781e405411420700c00c3c800001c4105800306000c1d0121040d40180b24115800c944c5100d8041d10150f58908031484124001d00945c1c1141e03505500000b02c04050016240c0610305032800c40080e5004641c4100040d8100c41c1d03903106054900742c80c0400143c2c546000030b1110080c0d80004260000c401503541c40d0a0180c2c02a08095210345001d0340c144001d4404000d01030b40004031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 207257994 1250 207256744 207256757
    0x80c040b06041406120a020a1101020405030304180b0907050a140306030c12030c011103070e09040b04020913060f0504030f080103050a240c11010f02130b03100506030702010b040c 79
    0x409010034010301c82c1d0700611000b8030000c600d0305800d031074a070b0440700003488404a54105003400080305d0065884080400d0015550460300d4110740c0c0107100b210100c81c402001989044d142200840720880b1410309054241e40e200c048182c5a01d0300c40e001442000301d0368445582c2c500c0120301074032010b0078010940d0001002d00400000da02c001680145100e42210284d80560110540318079500c81ca2501c01425403c0c00c01c02084007118401940c01201c071a201c40d444c112030001030058403a0b0444019001889681c049000741c107088400d01e41020a41010420719840e1744c45000c1501c264640440d40c0366918001c000915034001d500c641811114a425812540341d0340b02c05940d2181e9101c09040c1034488801c609410362110f003035554890901ca01845441880d0501078881002402c4000081d42007000100d203c40b074a100b00c5140550713118005200714180200600c06400c000c08507001e51620502c00700d00f0359101005180700310043e0380041113100c441c0052006440c0e1040512062090 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 207259244 1250 207257994 207258011
    0x150506072d05070515090a03050a050c0d03080703111b0c090f0601020718020405122a010207062124050d080f070303110406020307030206060306060109030312060b0d06080c04 77
    0xc01085100071514103c40006200b010701c0d1145e17066214000f5403903844840020300104101d804a40520201c0c0550180d0f0f001401c4081809114014080c000740054840c4c07002036000c82c0254881c034524041c01425905000085c03074034554100717400c1c00215065120306d18010b00e40c50f0103404280e0180360614070006505161001035600e80050284092031008032040c240c000c049036041d034001306001000c2d20300712071404044949880780c80e0418401c50700300c402c1d81041c000b4449425800b20304103a00404040e4a084030813513540f43d203220b0403507a01ca0b03140c15070b00a0004034050300c04405550420200490915032070650441c40b294020382c05055103031180008142800305903521480c0300c030b54050381c071aa50305c5e0450007401d04003107603000c500000c01c01091181c2e001002e007081c188039400300c440e96181c0e0740415550781c0045a0150019240000904c00603208040e00600401524004512580c44419580c81038101c240c2500036290f036968204100d41d81007000503404a01914104110382c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 207260494 1250 207259244 207259253
    0x608040209130804090911030d0e010e01030f14091501030c05010e0d051e070e01080c040c050408100c140a0801030b1801020d020c070e070210150506072d 68
    0x1040208040e12440c003050002e40492161102c00304000c1e880a0384036561501c8100f21001403c0d481400d8400b488004510115410000345d010780041882e19100c07001032200004440c0b000ea401445410151510080e0f114a00d080c020078010042103ca400c1e01c628240caa01803071325a040e4400710f01c0455800041000c01d114005000a80724203181c405030210952022860148a0400040984c070860a070407140b00b1a107641811624031400c20f0310a4580d4600700c10410481c2030007010281e0f004a4400b010703a24180c0d1029045000134103105003415510b500030350602507846c010340031150310b0300000c0c001d06500201d90070300455641a0b41f818503010640042c268503050000401420100700450039141103554402010a8600025596901d90138a0703070002e504030b10386524842c4115880484c0706484d6035a0710f442117113254018200d44504a8900b0041e10305d46002048440c04400d0116103500c0f00c44c024124640605009109c4084c0c40701402280000d203104603002035240b0480d040050b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 207261744 1250 207260494 207260507
    0x524100f180b03090a060e0a1a0403032703080708090d0c03031b03090507050a030b0403081302060d020c060105041b0315090e0a060b03120714100c031a0a06 69
    0x2040c0d03180031005046552491884001a07411003400c0d05408020004a1a00050b140f5074040c4680c6090108000c6400082d956040c5004000c00c0c081d4440c0d6049107204940b02d070a544035020b8500403413401c45a06101c8864101c2d0b400c0c0359282c0744070815480c00c2c5904108410f0700000c071807401084a00d001a8803076200e5404440e900200b100c01c3c041e0a081c10b1090300207a00300444d43c2c01103000400e4200c80607006140e510011109030051110024031440d00e02d620303034116500660201a9030395955021601d160000342001c004100d4071520300056210700011740300740e000c20000140d80351865402d00d807501005a01030352040e404c010407540b00401c4030201801080e40782c140403980181543c0aa66030b40c9450300005000c52400d002c0746403820000903d5010140a0041089100c41001c14140c46802140c520f140c5a00c04000340400181c00b0009940d00714038802c10750302d4800c00041d80c01e05a03094002102c0000e0389030494586544201000101c2c03182040b6010811030b440e280c40074141 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 207262994 1250 207261744 207261767
    0xc0114070c0f0f15020a03060815010e040f05010203190f0603020f040f0f050a0917030705030105060a030209030f0601080f0705030a0b0c0d0207060c0e01110a02040b010c06052410 79
    0x100140e00540c608220607000d01c418040e0303004d1404107810f0f0140040310020b400110400700003a003061380c0002c4c0c00c8030100303000190042034000c3e800c1903170a0003500070021f10080c10886074000d00d11211000300e00c0a101440c080c90b02ca82e81c407680c00004507920410b42e1100681003407841d140050400051781e401d0105107000c2000d50300800d820402c2d80840c0b000788049661582554180010400014070310b40c044181c1c0c41c411040b0000103841c01c465040700380800c654501c00300344100018030032031821501070410003195107005450035402ca80400c0c01c08014210003000f0ba07009400502034400c0521064900045040040180c1468a00043d0b55641071100c050400e41000000c9182c04608604548030a01c1203841503589034000e21300742000b80302c4509580d0002c0d0440643c0ea03580c0d84038141503004d400c0030700700500b42c0d03002a03000c000042c070700c0000745414402003192070000030b1080d020307081c840c104000f46a121400f10b83e0041501c11a1100042e1051440c0c0400a5400c0d0b00018600503 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 207264244 1250 207262994 207263003
    0x40f0e1510030203010504080a170106090308160f0f0b0a020906030a0c03060f060206010e07030902031f021e03040b07080402100e0a03020d12031b0c0201050d0b0409080c0114070c 79
    0x40030748a038140303001c03040c00725003000e5015400d140810007804001d00c0203003102140c9036504081e0903044481500c03034003000c0c0900d000045280300d00b00301044660340508154445015419000740d129030700c00c001c80484c100111081c1d000c9640c40b00034402d601e14180d51011009100b03503e8865174000040e070512005141610403a912044500310754403e500c5000030784040404115020340750203001e50b9441d002d00c1a2480d442d030300e000168019100e406000b0b070030b59014005200103001e58020b5502c6c0348004007c2c07c01182d0034404500342c0140c44044540c882100241c06036a401c05003064031000c48010300c2e20041c49000c13800c0c0801a141c0d44001e1030f09200da0710306030fa00454000000781c1c0b554a51b50001e5402800c1c444280c051041401800a4203011614100101450800709a0b00e15100200c502e010904603840c0f030f40554068001090310a9889000103082540b0304001401c0301e000310001c0d51000404150088182400d21549503101103c2c400d0007428980320400805c00f03101001d0061 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 207265494 1250 207264244 207264283
    0x5030304150813020a1215140c0c1f0b0301060902030423070e0408040509070801080d0f031506080f10080a12020c030114100b03190b1c0605010302040f0e 68
    0x83d50b40403408102d88240360b0041a90764800d68820b0010116408800151190003c600052480c040c0d01d104142d800344107410800800e0f0349903812035219030000e44c0c81501c2c500038280000f1000300c0c0d0088107054103080250002c1c0d500308107424107007107484940101c0400b078810400d010108820b0002041c001900d2040d89200c5000ca0171001c2c10408507900582c0e00d000d05200340001c001c0c4940141064400517508045169121031341118505400e01c00c00d9400c0d003051010818413803203210307144290312a9090100d10001460902102100700d80d12810000755880280104c062035503000035000010228003001071410071729015221141120000c200d02a0740b08440c54842c000d000e29400404001c0003003002c020700d210468440c001c225510a5100100710002c110a0f0458003980c2c068a010720440022440395035050005020041d041544180c1b89000d030708000318043c240d00346041c4102c10229803545984140001c2d02e0006c68026407480c02c101f8412040c403000130340f007030701d515240c072014 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 207266744 1250 207265494 207265501
    0x201150806151801031a07051e0310080f030304060605090c040506070f1b030213180f1106030a150f08060402040b1929040302100c05120a08060109050303041508 71
    0x507080e405040242c00a40f40d4403000200b48407580040e80d010001d0341c25001000e5440400c11149840703048a00d441e58440c1001840c5081160405141c0c8803000d07200c8610503580703c8942610380702074210040f620340c3c000002c00c0100003880c042c0c040104003e0710180003e00b0000b140c00c4881c0524000c0794082c1c0c1c1d022400c0310500042c0d84c95070029940244080208021000c805100c1d6515400141c3c082e040d1001c130713103c00c01c129104060088028068a104000c500d5940300042d204c1c1410544146c040c560303040c1a20380d0740000440c00390407600c600044210041d0480d1002004c945c5c042084011000010464040f01040b01d690260381207a000030160124000580c1b001c2e1100100c8028000284000c180c450b80c804000d51007040d2800750800504407455042c03070f80d2085000003500020f42c5482080c03080d0080801c0b100480c412800d54880c10702c0041c280d00107812910302030000611080a1100c3e558220031994050481500a146418100b0003503049034034410030404c04209420001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 207267994 1250 207266744 207266749
    0x7090c0f03150b0a0e0f03061014030a0203010e0607030b0d03090b0306130615120e03040b03090f06070801031a04051c120f050402330a17010305030a020115080615 72
    0x4028040070342071541c071909510130003450001c03528912030040c204003034010406c1c03a0001d156440341c880390016290050502141c0740c6a840941c40c2650548212102e8600680c0c0a0080c03004040c40080140765030b04d0402c0d001000d0700e0440ba5028029803040e070100380031a41c0180300206540c17005480725945d444075804925200e45064481c10801d207003040100e4244110200000c02e04020754404162074a48040750341110644c1203424100d500c104802c00c5400c640d130717003e181d12680700c0080d44e4030090481c500d1070800c181110070310002003070100103000b00492522000201e0307803040700c203060521f0f066840960f0f0720860140500001d00400108003600d10500c080002003504000510614900021590240c81c041d1000c0384540e00740c3d0b070140e803a5181101a05680242c000000d00210401d050b03d00c09640030b00340007810045001d82c8110011081c0350814000e52246000790341d1aa0130340002821a08014240e071401241a142084110702c0080e009800c00380f1180c881c0000700c0301000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 207269244 1250 207267994 207268031
    0xf040c1409072f06090c030304151827241703090a170f03270a05040504030c060b01050c1510080601060309051b0d0f020f03030c01050907090c0f03 65
    0x842070311031030780b50200a000d00415200c5c01000030760200c4205051200070141c03a800f8034010315011141d11140f2a00081c403a08141510303207104a4241e0341c10303454903680704039800030b000b840030488241da000c840410f80600c1600d40790079458100003404c140c0b000e0811aa5009442462011700620151780c0074000c0070300865440d44030040c040808240d0300c50b0b0900100705010360b840c2070b5000c0d11050041813400401103504080c4190302d1500020203a07000c0d200d080354161401c0790400f02e41040410907444600c01c00d0b0186020341c0b1141114a410701c6e008054030500c1d460141049814046481550707030000d2940850641606620f4180d40c40000f41c2e40401c3300da40c80151581b00d00400083c040c1e825034444407000f07002e0800d503445000e0b5070548494480146e01c04c650403039002d4070b40c003010982c01541207136240d100421150b404480031f40024610b8001c032860040307a03551072041c490a20410403030400140a00c4a043c4681801c0c0728020382028141c424140a15443d0954500e0701d040c27854 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 207270494 1250 207269244 207269297
    0x70b0f030f04030e03010f1d06010f0303081f120c0605041211040e070f03050f01020304030806040c0e03030c0328140a110a0c0302090901051603020d0e03030f040c140907 75
    0x1c1c001c07c10f415139495410050003a903042d0b4504001d11030b01e02c000101c1d001c80ea49050b40c030b04445481e9164070319942241c400800928100c020764075030000f04101c815210511000b00418905054900624141000341500d15488001800020002006a0403080017103c181075042100c0006082e010000715010300107a682e80d1200c0d000b0413401094203108281d0060949000d8002c880e895049103140c0760803880141d6010b0081884200003684514154108490804092503d0381d58070b10b2000201c1c0c915044141c0a11a0350000304121303070005103920001da860554103104070038800b00218040c10311155a1240c104089000a2082002d0302644406140c80314800c00c17901c81030b40e0703801c08d6071140140740005c911900804010450a01c814003659010b00c03500400c40d8008600c1d10403c3c0d0096005001a410641e120310810045030414405548507103084200492189081e103407500c040c90054100d220159082303c00c400c202d407030b00f0b01e0455000c903150070304841c483c06800c1561303080b41025 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 207271744 1250 207270494 207270499
    0x140a03020714041d2a0a171006060e030c04090b01091805060405150a0c1d03070b03090304090605100c030302030c070501020316081b091005090904050708070b0f030f04030e 76
    0x4c0400b200c1c0c0040080c45002500c4660b5041008002200d89001d41c907419520850384903680c0e034814888880d040d800280da80408000701c1c1c00c0040a11109415501c00d54880404100b580310700800c4c5090502c1070158401c1d0444013000509040e944410280c2418010b100c08143d0b50002c00a000007031030b031030503a0301d5040001c070741e01880c062424595509441c140c40c051070034840d0200d62540c40901071304185000584604007514440500000401d8440f0a080c0d49440f918a0000d140802d05008501a06200c1e000d55641e03805d066040741035440e513500c00ea0281840d0480e058a565000c1c00e5424190340c103150140e80c03902c4e54480306906014180c405003155200006119420700c42c440203020030803030f0b40c4071601580c0d681c142001c440c45213014491a0f079007007045240c3d540d160030b0038100c0c900e5980741001e9043c00440004101010030403601115940d20a20051010803c100480c0c0014201c0442d51407030315141d8a035105050202910b0700c10f440300507001040803d03000d403c08407a00b4802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 207272994 1250 207271744 207271781
    0x80c0a080d09050106090b06070210050f070308061206010810110f0301080114280b180403020a0611030c040302010f0201110f040e0a0c02030f0c070b04030c03140a0302071404 77
    0x50780071200c000c18908900300d03125880c00500040c00c4d21540902a2001d00003001c440c2040031a0f0207002080200c28421400c0000400c000100311920f01c0181000c01c0c00b070741c0d507181c90789030100501c00c04440c105000ca5942c1d01010040000030000103400400441d1414042040440b00b02450094014a081070301c1d10a000300010819610540c0144521042d1512400f01c41c1c8986800e0300728908481040700800100c1610f201025410350041249840c01600c0340d40c541901440074403040c001504c007140180c1080c4514000c0c05924004c0c0c251a81c0250911440d50070108030711041841144030080c1880110910201603600030b41c01424001f0420300419500c201180b1600388a42c840e00406c400c2c02104808126030240a204810440005400940c40c2210807074824100f41c02500494050f80305042001c5000300000b0060030086104e8994902c41904501d01003102410000540705182d22485440300031950000320710045841c0c03483c2105c140c51003800410080d00501c1c2940d0300038081d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 207274244 1250 207272994 207273007
    0x30c030507050102030420040614010c1a0c09030d02010509060105120a0606090506011209051203041b06030209040b1206071107080303090309090906010311040b04020d23070219080c0a08 82
    0x1250500c0781070102815031402841d42882c0400c01100e986000d412070401c200d4080d15040d5004ce4086102e4501440e4500340420756406100003c1c6400c48032203c1c60306020a00f20380300d0404000b41c0014034540c2c0024041c600d040c10403140d0b2180b05203e000d01c80e504003448002148401d0001107089508048140503d03603d84500101908080c2c070881c2c005010365002d1110603240348645081c281d4003402410b899001c0d02421586900040e00650755002070014101220314102180c00080c55a038902607112420602000115080340340d8107400303012802d40c4850a52004a80d0640c080350340e0400e41016252219020700d000e0f02c84c0c025101c42d20001041c0502a2070000c06801c0822084034804010780d11160180c0d128407080c071005002d201c1e0019029110700e01900540804440a8801410f060440030315030160f50303400c10008107002a00303604800085950030b100341d1060b0580014130f01544ca0048009031000b503c80c004d4180d62700410212001c0e042404280341040d0400c2882d6161403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 207275494 1250 207274244 207274253
    0x4031e03140709060206150102030f04080109060b0406181d01060605030108010c230a0c150902030d0302030105010c02010c05190b07020c0a030812100f1409061804030c0305070501020304 82
    0x1c54014103040040d80340014000da02c181c3d8400140c400385d60161296499880c4400e10145592103058191b01050100b40c80c008415006800109400e07800490050703801c1c00c0090485034403800082c019400c000050003100d000500d0281c09070128800022120416600b861030641a601405a20f50038040f002503003650180241d07040c0d43c3c0e0440200100c0c500710400351081c030a50f044080180350f03400c8a40882d1903880000d440364809500f411100064140d440b1107504288441074840155200138000a6040c1000901921041e90404600c0c1d941810000381c03184040402c003e0421005140100411100b40510a0000c1103031000f01a05c0c42c503407403e1140210300b290130000600c50740742289032600c0c00c660303a101107d401140452410700080d50480709054014440c0b4ac000d103503000c001500103074440c1c00d90001c00c003224060910b682e600003040040741000d084d251003051300d84c001540c40c40000005c0740e0004d86c18109000610600c1c5001c4e20f15010705a000740c07965102008100c28007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 207276744 1250 207275494 207275501
    0x10501080705010e030a03020a020d050109050d03050702011b120b040209040c26060906042304050106060f140f030417030916080609060c09030709060b13290304031e03 74
    0x21982604c03420800300158041c1990b404a010002d00160720941005000d401c0c803a010320340e010f010b100003080354262521042d1400036405201c05c0026550010040120381c2849048c5044200d0020964088c202001c010501c2d5040c1d40c2da070803550360350014010540d4540e4100c0e2404000508140180c4841c580090b00c41e0300040c1d0909840608c48218134051412030100910803800100101081d45070107080c0001450b0070440704a0b0212035010100080d801856010300c910300c50400842e20f13608000c40107210340010040030040c06010958900e081d01110185c50710f64003184030f0315840360f446081c80d40100c0d40469105d60842c1700001889004000800c140c600d0662035a240d268083d581d030b4030f050361030001f11101d0f6543c2e00b0020204a01108000042600361002000c46129039143d41da0b90f421283e85510201d51580d00048001e502c4000300c1a00c0700911013800380d411204030501c0303505a48100c03a50401c01d040300000000d03080501500686d00c143c1039000b0b4442960202c0500607005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 207277994 1250 207276744 207276749
    0x151b07031103060106020a0b0a0906090c030204150501021c05040b0307120c0503090a02010c02120d020604050c010206010612020904140103050606031e07120c031b090509010b01052a0105010807 85
    0x10000d88401c001c5060800040b214100c0e44aa8014014400b443d211040c03d8003001e00700d101c5060700e81c450a008a01c00e8028540418080c42541c0380442c0b82d841040129a2006600d40656250301020050340e078001c101038800405842001c0d0741c100c042c540484040c441c5030070168900d480401400b00e415030180b500903000c1d00400c01084800d0f071041042d1554001103940580781d40c814192500154410756000d0400c3e40b010746000541c141010b6040c0c01c046a086058005920940030001480300c10404103109280a0014048070350605e030340140030740702444c89000e4046d00022422103e8030b60f540314952130f2804040c040d425503182d00d0b00584401007510346510a2107000a0b035200300301254450b400c0700303440b000145215498041814500104410180d440301040100000424111007401c00c0b2220941040c008103130616184e0380494030080c0130309400b40c0c0360603240900d6036001001c0300c582d10008076a4208000c00c001504a41c5d002c00e05034840107500388000000c00100c005210b605 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 207279244 1250 207277994 207278003
    0x906095b1a0a06030b0307050603070c0c05091e0c0906040609030204200301150c05030f0304171c020306060702040608011e0209061803120403110906120705151b0703 73
    0x2008900c110000c0c40c1509032651075480b40b040141000b0040c0207034000400c0c0c41001e400d45810f29a56800076116800450b09000800c000c01900400c0010003072649002c1c1c5012110310495043c00780c201d400c40d420014070800c40f500c0c10408035200a40c92001c1d80c0b40400003c00c040da84503220600141207040c0c0e40301c100e004600781081c4900c0d07415582a21900305480000f158216841c2036a4140003803400d44015080c00700d450400c0c000b24106000803c41d182424079125030703a007400d00c0c040840e1a084a89002814030a04c402c0b089113a002c140100d522075040805a01e0f910748000143c0c1e2031049000083d0300610f052000a44a0419000241020510259000040c800d005070105078402c10102c242d00810070010114017801c1c3c400e9401e081c0001a0842e07094408e8811041d8603a80b203900140c1d900c0c402840005824038042c801240e202e4004e036003210034404001717100c0341c1e1042103000f0036110f0400d41250300b006001d084162440c65584054105000140c00c00c00d9441e19800e0100340c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 207280494 1250 207279244 207279251
    0x220c050406110c10030f090b040c0f0f0602060601030902120d0f14041805270c090a0225050c0d0602040f050f0a0306090c030b0106080906095b 63
    0x80b002c1004280a54401e038050008614400c050004030005c2c900741d9481c0034110b64585900d40464440814140305620035070f02c6112035400c0c051090012003256116800303031054050705000199021494a4100c1401e007804181c650380b03480003c5004101d054605118800d0304010b080203a48850805001c400075103480b280b40c0860941c0c44560b12450040c204e0b03020030303e200601c000e10319900c819800301821001702100200b202e071140448281c0c0d0405005680080341d4194640b40c411300c0250000a402411403620942c144201e0030040c403442c1c403800000c02c0340c20050070721800707000d000c04424006124411408042c40d09400035000781c0034010b58410310f80004205414140140c0c1d4412130010820803078280780d90384407800781208800c2154400280400040000c0100207001d000c2d0510340c68132000707881c0010074946400002004484260700060010300c0c1310000754115601149080d100c42c2c00941d101e80c10039610700b201401d1035001800c070021284003a040140140d070b0810110002c0c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 207281744 1250 207280494 207280517
    0x905160501111203100e0c0a0207080c0f060711090c120612031c0902060a0f08100308090616020901290c0709020901111006050f04060e06220c050406 66
    0x450340808a040720800d25400441d1010f00d804454020b1903100c101091803d0555841d40d04d02c107070400042e00c5840380030801050900da000d805201e0305000d4640701c4014482c0e5815840040d01800c0f40e002000d0003100b0004150060000c035242c100780c00780e0043e000403854100101c404143c0da018216565000c120b410200d1400e10b410750a03904d50b4020000210301f070808454403001c0c3c440103045840c06031640c80030300c00010307100d0f44007a100545050701d41e2600722600450150440b0130042c08440d10369241a0144000bd58034010386000981c140c50340ea031111020f1802c858422080304010354026250400040d004188004015080c1c1800015000d0411083c5030000180905140d200c8030340c001c0300d801e125040083e800392030312a9051504003101c00d001d0b0312003400e1400c04030014244644031202440b460030161007035011070b003007502d04008681c6081d01d400a0341001608483c0316058140301c2c0b00c88036031645024500c00c90918810000812034680160041d405441203a002c02d030301390b00e04e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 207282994 1250 207281744 207281747
    0xb0901110c06060603130f03030c08070c03140309071802030603010606170604111207031a06070f0f0206070c2d060f0804080c0f030405031006270209040905160501 72
    0x55070300c0003070312200a00c000d40380e62007002082d4000500b24060740007160149808150516412400280aa14005160740501400500b5204000c10308400e0040d18286100041d501c1080c2e00701e40790391004419280d841d2804c10a0a00d801d543c00340f0521101c1d03c620300d41e1072403142c0c02507014480460017040050b40c2c40c50203882041541003001004a8050001400e605250f0854480b140444103000c0c41c1924208800d0740590051f03403c1000260340c2c415170351712402c0100c0410740b08102280e005e810005681c0e10b20441c940d64520003414009400000310440d210070003a0745003198884840c3c1102600e8250f454441e84500301c0a00c401ca8106120780200e0780d1006000d07064030722681d1503a80384903414009441444002c0c3c400c5034014010010052000c60500001e00c40c5800b050103107583d280340c07508043c0b034050712202c4079a085240503810400741080f1007030210045100315401c0741c802d03c4440042c009010780040507800909200d090010810082040c1c5002802c42002c10545a240c200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 207284244 1250 207282994 207282997
    0x906080d080a0507020a2f010503270a080c1f051015020a060f06080709021218030403020603041203050901060806010b1303020d05070e1e0103110105160b090111 71
    0x1030341008078001c0c2012802c204456040542d10401c03900442e0703030288095844c0c0d0000c0901041c00841419160b15171400802c0d46510828510003d19011f811801c00440c840d0000e1000d030350040704060140c0c000c2007156000d224454140d50000309003a01e03103084c1c144070364540c07042d0109042840043c031802a03224040e84640c1d07010f4080078001d841442d0801880e6071443c0d4151805109603c00c05000c000061180e00440019002266000c1582071400d44c02a02d0f0044d80d81005003203034010321248003500700b100300040e407151028903022090418031500a0452085030006074104000104010501880f1401c50411361200c0d43d08014581d1601d0380607089520a006004d400d030024070041218840c454003a020f000b0211006070425603032907002401840075080100c403035803c800c404000007520500e256520801000300341d40034508071030034183d407103005000061035607561003c0740e6820391041c0107488101e001d04015a10458040c1000140002c00301c600110039170070181d1030003003a6113200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 207285494 1250 207284244 207284263
    0xf0607080112080306180117010f0905063402031c090b06090c1309090b1807030219030506090717030906070209041a180d0c15050417070804090608 65
    0x1c14900480c0c0c0c503541d041e8198009041c1540c410340380c011802a40003030b06c012500a1a0181c4c818409401221170300d82550511203031114028a41504440840e102007a040e9001c5800080c41e50804240c0c4680309003189603400381c10038a99420610b0001a400100400c920720410007411560581e14075034030190340b00d42c400184580e101c2c1c000f040040c10700031075041c1c2191803041842c3c1460841e000301c240e0681142d2000084075260f02006040c80001d0945c0c40c4c005128281d480000680800c0301ca030380e807450703210090040002022000b080d01e0044103440103160311038207460b403501309804160758a00150149402000a074018420070f400e00100b180c005810242019042580ca902000180040200140d82c5008170400038681001c601c01c0880c85990520744440e00c008505034400d2400b160500c00d6000d0016050201e000b00f090b41d2002804031001045c049540c0c1e5481c13408414081040340d10704028000491290100700790300020b80b042d211180700802200b40d84125050b51820f11a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 207286744 1250 207285494 207285509
    0x70b0903031206120f0105010f14061207030209040c0e032e02030a060506070516050307050d0b0a09051b1e010804140102071a01090c020604120c0c0806010303020f06070801 76
    0x30022501c0d03a41d100c00c549a44030700f0040070309060a4075103007a00e040c02c002e44056241c41c0d640d000148900d42c0d4544103034014000b4401402c0b001107013480412000d00c03400c1201445180d07a4000191614407075011901803650140c014064a058401d000d0001e05c80240464402e0240464501140d41c07400b009800d140590345206442190100254000317500240828501988a0a01250544a140083c00e81702c0c41940181040c0b040d075258070806a10740e4000521a070000c2204000c255950321845003d66003004244449449080c0c0b070800904000b04001e0841c01428100d03044164026407040070701e07800b596041d90041452030b440382c030111009405808100036071f010402080f21036424040c5540401c0c00103280100680b148241d841c0416090400d03141c00c80b0050000c0965801000c5d0242c1044c0000d000d14100740d552849248801409034041043c404000403d201340c18802d6401050600181c852550b1242002500d55095101c007080a1087c072020910b0148288100342c100d4006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 207287994 1250 207286744 207286747
    0xd0f03030b15041a130b040f08070b0f030a09060e06160e030a0305030903040e01090209040605060304051e0307080313140a031b03050c0609011a0d020a1e2402070b090303 75
    0x9041c04650100080f08020040f801e01740035500100071401240300151140302040c503203443c6031400100800c0019007149202d50808401040000098800d40e8841101c604005849a640c0d17107403840200300700003000c0c040301c2c203014625041c11404500c2c180524126a204030466503070310000d5910b50109021713503405910102c401030100384130750041c42c3c2081d100340030380e4a42a503501011039041c5082c3c0008003c507500240b4030086262034030800c0c3c018002903441c00d01318540790303c800b9103d04040300c1c2800764903803020781c130141e20320b080c0211403c030b07580a10760903100d05005000c0045400001c0084540341c2007030402185030800003030b00d07001a503415038034114004441002d4a42c04c5007440803c0f018404140300d8039040032414025075209801c5c01000050003c5804101f54035214040b810b1170040c40300c40802c4026880304420481030329101200395200b040e490b20b90440e45889039220301e4150841e100603808d01c081c55034600100d01e40590842d94400d460b12400041882072805099140d0700 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 207289244 1250 207287994 207287999
    0x90612080313020a0f2120041d070e0a02041a0903070e181c020304050d080403020a031a01050a06120b03010608060108010c090f0503190c050d0f03030b1504 69
    0x144015903012010800c15010010658003065074040710b50408407640480f034005005040d51854501c840c8060b08080c43c2600c1e440d9103030020b00c404040312542c2e070450030091081c0f003a1581c1c2c00827030383d0314081020364803005011180340d81c0b2070590b801a1821038a451000c90400010740c02a034080d0743d07034481c55142003001c01e45080b0680d4030150103250980224107000801034503c0310722502c10b0030001c15201a0858420b09542002c420600c0f090300c05800c074405402d6941d00106a509036141a20b03407240202c0c00b810461034901941d88020f5000e540c0c0c21010081002c91b02112900044200300601c0300e076218001c100d003000a40c041e0b4800110454041c0d401d81031143c0202d1941140540005000394684800b030381030181c260003040701c9c1da450341e242c01c0c0036aa2002c0392000030115084402e402034141000680c807008a4003026415103032003c00041800420366419004010040c4082d08000306d91070a00704602c1c03100340030b4001c01e1910103221002d08101d100d141c4810024848185001d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 207290494 1250 207289244 207289253
    0x318120c010c061b030c080906070f0f17090a030f08040201171503070306150e0618041722050303070b060427080306030609160308030a09050d0810090612 68
    0x11a42d40003a1000c40d2540070442e10070541c0c0c841310142203229074010403034848540d006050301c0d00280040c0a294001000c1003041075010302d8890310809540f500c0d541160b00010100c4111803210340e42c103001015032091291070000000d04c401000e119844031410451380101c1561100b40486019000c16088030090130039210400511f607000c00a5103404142c02401e00100b440d0280d01c0e001200d0740d40d587c04600302d00d00d509184a2004040e0300801e81d026103401c0022514000859054000c07450903d000b10b030400c00322440da01040100050681d0322407601030f0b484070081200e595910320f103c2003032030046124100403049407505500300302c00020720b481d000b0505c4010007042443c0020100c03100448003008440800c1000001d008051842c2c407805c02030105414010050b10165803540001c070b888002400420b006412603400c59511610390303850710400400390071810740040050180c1e0080c01c0c51a500802080d0140c2050916410b070a52207100c010300b180e40f00d000d100c2080d1014040100040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 207291744 1250 207290494 207290507
    0x151404030503040b1303080a12060906030c09020a0309021c02010f030c0206130507080102040b040801060b0a0206131a040b1501030b060412080d05090a03030e0d08041b03050f0318120c01 82
    0x40c908102c0022201781c3e40d44590305c09030480002340d40010f800781041c201d80340881c0201e0000d8207401d10104601031655840080d4031141d4031035602c6645c1c000c503100d00d03c1070180d4444c41d9150b4020b8005800d400181a1011180c601494200e01240d408006080c20a02c82d200381c0d1700e480d1298004210944882200c28003501040c242281c4070f200358100401d9041003800940010001c060391141c0300ca0500242a0175146140c00c070a4482e5010302140e5100c1792f00144440d040010fa921160401c4000e061907a9604041a2142c04011f251000d000422500404040c800c0c4081d00090724050700400046050b80c4100301003640c425828041405143d100d5050015000d104079891854844215205410348070100c2c0ca103c101d03000054410b081c541c040c0030340e000040751040603206810310131401411440d009000030f0301d401c03c00c8a40d0035021307c5484c00c641c00743d41c101c8101e6004032000c02c2c1c140e40d280c0c49000628081a440190700700c480c10070801101d064600040a000c45018000045600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 207292994 1250 207291744 207291757
    0x121b080411041b021f020711010813063204020303031914100e09031e090112141005010e150901141303020405010506030906010303140f04151404030503040b 69
    0x100383d5882d00581c0c00a4641c1103541a0ba100da0040c00c94440303184443d01400d1440d03081e000c001c07801000175a000841000140645010908240e20380b034485425041e070011910000502d510314141211600020b1602c800b258456421002d504130b44840d00c640d10010800d440094040e80b041c40400c0628200504c60010300200d00b0f0000b4a44583c0b2240c1c418541082d1884100030309908020302c2284c00c10007520f51b00001c200000d515042e09840611080707000109400b07600100440c070a40b00c0d038410190940d58848441007400094240b29100c400d01d8002e440381500c14680b4100000c0950081105440c0d07220010300c02d60b02400c210b200f0341182e03400158003e04220300807079086008481c02d005081c20f1030454204942490840c0705001c121081a08031500c01c4800384100704150a0010701c0300d054035418030340310500350400042c41035540207624290080d00c501013400b081008040c40f0a00705003c1a50710b40780030f280c030031240f10307804c0c0b0860201400310b400400040c083d900d02c09009200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 207294244 1250 207292994 207292999
    0x130f060b010e030105130203070611190606031b0509061c060b01020f1c0e22090302120f0909010501181a040f080f010c090501020d0c060209060307121b080411 70
    0x7441100000040e0840c5e208403020494607940614213015410100034500140c86281040a01201c08800495941208400000e817048440c0c50b103030108001600100001c0d0784c05181208446c0101d0360380000b2101502602d4000e680f4400040c1c01403420451400303d4103400094144459001e4035510040c12100740302c507041d80310303e1090f030741c4202c0204281c584420400350030380301c1c0783e0700214000d03d04000032040e0786c851544071801502c040c02881d0355200112a040001410078044e01d01a81091400400c480a6900215802000c981c9500003001da81000311900c000b16a2500300540301d00015070311980c04079020306014000720400c2d02006078004103101d8002d0030266100791513150070714150000100d41e00048200d0011600c2400b4400c00c01141d0306140311810300b0140000d58820b90f050002c0100401401d1002c24041d040d41101c00782100540b0b1190b80e40f5105a011f0108010026580540c0c1d1030901c80c441001540034000c506803802d42d0300e40f515a01c403901ca04942403405c3c51640d5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 207295494 1250 207294244 207294257
    0x92307090b1e0301062a0b1614040b13080304060c0210030e0a12201f060b07030504060f140307080606090d0b060109050105040b0a0309080d05010e040605130f060b01 73
    0x140042e0340d0101440c001c100b40da44651030381074050b8110421014034010a6034034404641c81000203222000d455a0000105445001c0c400d44040111918641c012966400090000e004a01c0000840080c0b41790f40d00f040300c46480d03580e1a0b00e82641d9100d6032203004005800700c3c0e191401403400701d4045011665a20b800302d0700d010302d56803245c2003841000d421110410b0120f00380c4002a04202d90740c2c010140400e4201c0c0c0d80910440360307a00c031000744100314150343c0c2e601020104084280e02050103001400281501d60440703140280980d0b015006100100e822100c5111364184a801c0020200d9020000c5034110b8031000c905440c1d0200140100d43d00c41c4051210035060348491018891850107010540c2441c1003110001d030050b403858001d84e0410404000a120030803480e401c40e0200f03460b07403130001089203440c00c29504502aa92415140c01d08100000036500801905180034500903402000075807204103c8015142c040e18004001000e00e800c5140401d1040d0300108008406041c81d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 207296744 1250 207295494 207295537
    0x311030f040e0f220605060d0c0305010203070e030f03070303023001061101230402030c060c0606041107150506010513030c1d07081603020f04092307090b 68
    0x28034a038215400c010070a803040401c1212003076900c601a074020070100c4c2c41c0d08840d03008481070720903140c210901428103034813040440d80e19107030344085201c0c464000c0b8188102c10307220f1810718083d500646200300010100807007000cbc01d02d4041420140700d05240020744c5050640d903000d60194001208042c961024030159080c0e0f1542c02034041c81295110890100560600601070804001021800700c81d80c50102303c1242043d88001d0b020004403100e00c0700a00f55110b20000e0314089216080c207820000100e94201110302c0014818068401101c3c10f00c255425148440300c81e001d0800081c02c0060842c0003400d42e03440960016820640602d805890a40415004280c0407a1644200d98500080030200a2020442d0359004010300400c50319910b03003404034004054100180a00c00100300c103040c2488401d010350f044507110f8086955041d1030310303600c0310404000c0c5810440c0030404820b40c0000c560b4889031a002074031038400342e141d01c510b00b8103041000c80c0d80e03007201a1300d0580d10051511b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 207297994 1250 207296744 207296767
    0x1e0506090127050703020d0608030f090d050a0f0b0f01060806060d05091c0507050c06041a0a0c020315010302030f1c030c050702060d0203040c08061b0319050906010906140d031103 79
    0xa107132082c85551005a5140402c41031384040341d402d40c0c4400f4840e0020702a100c040e00034501101c2c000b001c111116940c440c5035050481c1050105640146040c40000544007000048580d55220f000101034a0159a90315082030f16140012541c0d543d20040801c0301c400f20f10f0550340940e030404196022141250045903c09024040c50380102000c900e0101c0c40b2010020200450307000103d0030789203642024a0483e401038000003030740e042203030850007080380389260b4864152003c4503500101100c40d00c05c104400c01031214401c0c0016401703409000c3e041c0c4502c44c400500e1340f541d5542c4000010803d401c54604500504174100e52004001d000c00c281c101581e50a40903003410140b0b030000582ea414189892040e645250740300d0310003030b00803030204000c60604100d140304041000c4402030741c0b9035030050303210140d162042c0d40446041c6440240f01644034001150390503510401020492291030b114010426803d4041c030940c0300e038030981e2000020f0300c2014070850518914003180e0410221842c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 207299244 1250 207297994 207298001
    0x6070b04110a0303020f1b130e1908130b07020f010e01110f0c042711040b030102120106020f0109240603120815090c0703080405120d1e0506090127 65
    0xf0a034010780c002a0072903040542400452004a001c0a0107480c4800340c03004074001c800038401c0300d070000b03907500700d882c0d624101400714004c40880d01e0500600020f491800004130342000070f1013010911003150201d1043e041030111800190000c0070651003141500045501811108086040020850300001024410081650a462210068400340d9081014003040b6960100060400d5542e2064048015101e83c550030409402031910a00320710300e0004200a04064103010b5003540c4002a15512f0711403141c18581a0340c0300c0e90a0780c441070300038500c440c2a40c0c81d8107000f40041141d13381180311483c400f0641000c0601407480400c01d0b83d07480e01c0c0c803070360340c903800074200c0100b6911030070084001c10301c282e110404e51080322041140d00340048151403500594034010f007484007550200f0300344002009030000304481c1c400003e13640e90000010101a080c04040116040e042800000710500c650007131511441c0050840307031040e0b00e480d815191075499004c040c0704000d8620303a03555030311101d0300 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 207300494 1250 207299244 207299249
    0x100b0d020d410d0801090e010b0d0302010509070f0f0603051302040905060f100303120902010c0606300f17040906030804050907031506030c03020d0f060f09050606070b04110a 77
    0x8080c4180419030886901401241e00c0c000816003008100f400400c0c1c11102d480e05403a44100001290070400610500510720881110f0748818004070314001c0590540140b03105038581c0065030001e80e9519103080c2c01c41003c5c000d05452014500d81400054460350040364450a041103841c0510015000f140845002510603501d54008600b00484013040506064002020380c01452080f440d40e100240300405c0c03010300c0e001c480d0f1182c140505582c0b142d2002d80010340c005104102150341c40c2c2000c042c040c1441140040c00c22410140000c2c04010489041959000244203079080003980d10200000c0c840c5d04951070003e020302022031800305c6442480099441810710990340c500b00801c004940030010710710030415040c000b0b400b0088000019000c01c844040c100440c03a080c0005054000e40180140581214982000140d01003260703000075040360500b104200499444500d0041994000c4a0042d0040e204029050002d810f4a0440340d000c0d004180e15409210014006950100a135 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 207301744 1250 207300494 207300563
    0xb0d05100e3a18031e02030f07060905040b060901081315090618020d02090a021e070c05060c06040b13021002011a01031509050a0219030e100b0d020d 66
    0x80810302c80c1001400c0d400108441282003000103407480f01c900305480310980c08000c001c61540100403614140650145800b03940c0142075810707034040d0585c40c40d0382d090f0078031400000842d8100006244d0601b445800b1340004e014000c5440c2904840c01510700441c09017007034016010142000740030403900710410013400b0466801249200090900505407541c800704902d00206084d1004010f9807003120f200e41550b03041d01c20340c405940301282c04000f401010b8101500f800803482e600c0c9202c00420091a8103403183c015011316030b0300c80003171080c00e0044c00b03041185517000030b0101d0301103203120039070356884003070018000120307019a40070941034010350700c2e91400760b91650f001441d03603402003c81613407076a000c0c6810041c139140d1030301a1903090424492030702e2855071080401c120100c0303501140c3c001c00440110391018941054001c0c0240307098900100140110303e1003101f004118020f000115500406542c102c106640030491040c82100085035902c29103510f00724100b1840460712030700d51a5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 207302994 1250 207301744 207301813
    0x4080c070f03080406120e150601030e010f0605090c030103050d180306020403050102030a05090d02031b0c09070f0311040b0f13030203070b0711030309090c180a15030b0d05100e 78
    0x1c140300900580f2210a406c070905091040d5854200340020740603d18042d03000200403552280401078000344000b1542c1c1c0e0207035080607006200614030b80c2007503080711020364080b00386540c2c0000400003400700b0300000b82940c000034a1003482a01c00d6030750750103500c204031505408035540d9650004a0780700d58400c4505035000302c10032907000640c1c03140c0d075448203607040904007400450030b0080d12485019038117460b9a081c4a03030290800810441401c6115003d001c2404505024002400ca078200005001c0000e081c08400320008160106903821140c03181215410106150000c00090300002c2c040d01454400460003c09a5000c000b0203004040c4e02c08095035441d441d080c4a1220070038100c1c442c1c001d5101308000b00841e2a140d20f040e46c407803000130a040d15098a0712030308111844042c4040c0d072181076460082040694141a51740512713060b1020816556440103100211641900c0540a900141c0c80f074a107411440c0c100400c5294040706448031980da9005402c0607103e04810102e84140 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 207304244 1250 207302994 207302999
    0xd020a030e10060b160c1208042606060607030309060c050a120504020f0f0604031505181902150d050112030e01051c020f0412030305041b03080304080c070f030804 72
    0x702803040100d024000301091001074106441c800b40340c891074444a450560002450080c03010151162001d04071803000e00202c1e0819041804998100d4060650b5036070380c001d440710300300106408004007000070700050001e030b940d4030013000016080301c070381a0b09154036070201500007000c6203d51403e251081d00c40c5901c8598540c0018007148100209001861424080c40007694035040300c100680006ca489a0380d0040d900046000ca01865000802552912100c0030341c020894004c1441009440040427041c2401c0a08035545c001720303903d0348050401c00c2d01c40d50150030000c034015804100980514070b095009100f41080b504240d10403c041e1a030210311800309503000762000c0d10700700b0918006040060100c0c940d42d4011030003240300d0f03102d540020300c00851161002503800410241407002912146030030081d000d800704850440360241d00b00e0031251144081074200d03055a0300010000c0c1140e40f2640c0d00900e65000c000a01640d00c12a100001e8031101c0018143c0618440c8081d90340b41d91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 207305494 1250 207304244 207304271
    0x403030e030c0610120b18030f030c040509060f010e0d0309210606060201062709020d0b040204150b18180106020708010c032003040c030206030901090c0b030606031b0d020a03 77
    0x46043d000060045c1c10084080040380c184a882900f1503074850113a201009491f02c12803039071258015040581c00c0c08410008608041c0c4040c0084490030b03142c0308219580c1004020021011901c914042141c031901e2400f43d0a0402511a41d0740c80f03402d0507013044c2d448078410b0080e1040c100009070344c0c100b654425420003000307016450003420103000a100c0c0e0750420350350040d0b455001401600d001842d406640c0e208107180c12404815402810030fa8180c00d0904051402d8442194140c2c016801c0021440c2d4444d9900655402c64a54034003042c20030101401201c41d00490003445030340081e421341424440103803144114000d0901e41c0041c005907152070401801d48081300c0803941410310b4a0300c0710a02d0000801190030005c00f1610040d520b503038515140680c080c5a4001942001000c0300700182c103501548140103003030286403000488c0741d82d40c645142c10320044880c1d540005092000c650080062441911480c10181d102420b182800b06c07034108130780008495000013038070782d1031803030846 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 207306744 1250 207305494 207305521
    0x406091b050102120403020d030503131707051b0306060103020c010e0d030e07060f0f050d0e0f1e073501020c030a030b030d0914040b0409050a0c050105030f010504050403030e030c06 80
    0x8030b2000c0013040c2803614540000d664000e22442c06824048004002545450060160000ba9601040c80c08030034130350842128007038021010407a0580310700c03000107400c403d0315104400040c41c010000d204555410300110003035000311807942a107640328003042c0c2d02910140b001c41c508071385a0f5000145d02c40501025860f00a499002000b4004c0041160441603405071a80d96208550f0a009540b2032802c540000140683c540c0719001b030080840c40c5990400200e03107091000d10400c0b420042143c4a00c41d15203900c0d540c41200140162010120310a81c1d442c2d115000200c8103940154072400103412150990780201404c1e0715581000074085d5035140c02d40b090920000c400c3d0001c0c141c0e000c0c0b0f608050300c025070f46d003ea0800803d080e2803122aa540380e4224010100c1d000c3c0050052041d5881c0459440d03070304a800b141c00300e9010001041a5200e40241c80c490380c012490b82000d07034a401c09200080401074000c0d01003645030303121507514040400003031903041500b8008015900c0d101d101c0000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 207307994 1250 207306744 207306763
    0x60518040c051f0507030908010513030207081612020103150303092301120504060e101d06060a090c0207050d12030b040e101d010509030c0105060402090907080406091b050102 77
    0x1800003100c410103c030411000b000110100d8104242c0d12039280c201681c5400c4036900034036041d0b08000c100b1849640c0d20008500c4188290222290b45031201100307522070054042c0424000640c5900b04642a0010003103400326006043c00103a1ba0a13000d070004014034550000e80214035100010040000800e031280e01d2860200302e03003c810407141c00002d040c0c441e5002d1498403192680042002d1010391703800354110755025000c56010080c031402c1e40001d0440b0015440c1c00b0303601c3c41b0b29020310000201d041da201d104000c01c244403440c03c0541c2d80c4010201d85030703c182180304000d004030b8a51141050211204e000784101c510f250515100107007901c404207192030243c2c1c02d10b0f6000003168000a01001c000b081c540000c00c10702081e03185040d441507006074000b015030801c1c0520806807000b100502400300c1d090300078000c580c3d400302440282c1c030800440036002240400060410ba00c101c848641091041402003450500c03034568882d02c0111000d030300c4032009034007020406036030100a001903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 207309244 1250 207307994 207307999
    0x6270f0f05060115110d0806040e161701050f0903030402091509041515050a090c0311160b0708070c1403072a0e06030601060c15020d0c090501031b03020904060518040c05 75
    0xa400203018002445500003a01490085881341c40e5044ca84409002c100d038803072404105020223340d0303501c0d041160303182100f0a19440d442c00010070f6500c0c1900b48424400e40081000350310b162915400d00140080003090052094518440303000b880d17554030303c050700460041020100f20520f0700d070058100d44852400c00781148a0000411494454100160031200d00e11800a404c1c0e9030f2050690240444810440c894040007400c40b01d0b82c80c04600e540e92240c0a041e4411440e503401320241ca240b201603c100300823640e000900b00c00031303030100c0d1901d03c068010b0040d6410a80960340b00c501011185d9001d034440092548180e071040007030088100101303004540802a4100302d40403d41b109410b0081c9020040e0001b007110038080e00070104000364651403001c640d41c14403013119174002c2002c8005400001d041000010311580310b4015480b21443c08070025101c210740726003da00a501010030503401c540c440e500060030342c0d034000b640078011002c00c21f140100d04c0c4c80e00d45841070400340d4100f40e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 207310494 1250 207309244 207309253
    0x101e05041a01080a0b040b0a0e0901060f03110f04060b0304050f16180e21040504050c21070e12060a05090d090312030b12010906270f0f0506011511 65
    0x10070340e80c860440764020380300440c009104104a800704015000880d44030340c220034030910000701c00029088143c0305800040007080b1407525152401c4000100707100c0a40140c030221001e000510b800c05140300c40507001400000c1060b0f4400080082e030704121002c1c0e400d41c2255078491004a41400015801c41d0b5810040141c6801c249602413890840154001019500c00c3c0240c1c1c50310301048480100901c4100900c0300220101c02c0403403651150003a54051400c0c04003150981c4144429518a02c0301c1904c41030b441d075114140740c070305074400030548020411480781d800420345030815040041ca00200c0603001c240b500c1003900301030b1a805803c0b5103aa50041010f401c14982c4030b8860400c2d01e034040f0341c4442080100804070f02500c44540c40301d0340084040010208000158049100302d4400e0000f44210240c2078103030f508122400c8800e10005980c104568005288841d829401501c5081d62400700c1e81c0c603444172460004260410085a039003001c0380c076115034028542441800d0014000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 207311744 1250 207310494 207310541
    0x901050108150a0608420112050c04020a0c0c0f050d230d03020c060618010b070212030307030b010801240503040f0f03030b0a1707030209101e0504 65
    0x1ca0342c0304030740e91001d44050401008501d0440c402d4014000070706800742203d10b6110300005250b01c54500c03416411000a5681c03403440f200d00c070f409010000c00350310a58040c8681c60b00d500f860340302d404036504a0b264042d40710310b40c0c0345548a2000d0000c1451985c0d8240c1050038034500b107125501303241c0040104000d021010012070303450200380c4a80741e44c02407100b2042203840781e0030410f40d220005c090380b241c002c02021024841e1f00d94090590700c89a10b00712071103034907034000344211010744e0462070f91144110b00c0140100b0714090010315103a4405000100c8208481c0744090540d00140e8001c40000d8440d01f12800560303120010b0380c05271100e042c43c8038410700101100e0040c1c6000c4000c45050241c08000103090080780160f000d1010f8001401084044044c81e00030020180c00d140c9070b2107070f0022103020412941c48100078550712109001845042d003940c00f004240ca0300100882c2c001440320801060740791080c112290b40010403106070002905140411090300d4110400302092801200036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 207312994 1250 207311744 207311759
    0x1050c07020f010c0b01030f2114032d06121209012a06050703051005060306041113060507030e010e0d02090a0f02130305160513020d18030c02030609010501 69
    0x11a00450790440c1c00007594141a0010f032180402024081e0403842410000828000503400340c3d1800c6109140d41d042c2d81071407901c4030000c8080c0945241c0001c04030214010b000160400641d000f800300c440c0c2c01c5030179144c003251080804c240c40350441449042070034401d031810091601d80c07842c6041c0010340348a40d044040e19030a4007801074414100001e443c41900d2004484040c003984240111030b282050101e814540003622040c0c40803400a46890001928906e0208840080e0b031001405c07549151103460400c4007521b49142c041d0000c4004002c0c180000b2489001130004200c140c40b129104c00716800c0152150900581040c1844840204509a0394611800c0400e0315812aa0882c0c42e8840110440c006c088280861800750310020f0800700703c200820a00c0100c034850006c85081da50145440c070540209072041503040010041c501d044504d440c1c0240070310000001c0001043c10380c0900e80b0b4008400700c1c6080d80807031040b09000003036050a0046079400000c0744001e1105500d040f44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 207314244 1250 207312994 207312997
    0x120c070803150a03020405160815061c06050a150f0302040f050108090109060630110607051c0c0615050303030c0a23090a080105060105030c0702220b030d0201050c 72
    0x1403111000c805540d4a4165030361203540d40302135034000d07204010780e11b4000c0c0c83c4181e0305076100c5244086040000051001e071034a055503603000c44040d04042c01c10101600444040801c522015191130b01e645001c07816845800c0840c00821485d100c03d60003c441010203072107081e403403108400b010300411051041c921140e4141046400a280c1141c040da40c524400d0b004100d5448000c180c039041540006200740c0c0000b04c17640d0344410b00c0ca006160100c0908020000d0702d2004001d0040c440b14030042818541080900b41082c0200140c401c80d00381c2c03075581c92989a0400e0303142e0200313114a28010602c0403a10030040c03800340c0f01040c06802d50914000a40da4080109143c00c810b00000d03007040f00a2040e1a00c2c0721701c030b01b101d0049010ba00362a80030f586503005820781d28007406a2002c00900d0b100b050081300d00410040e15000d03c0c507254010569095401844107a0300694036502d400c465081d24031400030000c400910004a00720310504041c20590f24411000440e8100400c1c8034031440003a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 207315494 1250 207314244 207314251
    0x3020a110712021012110a030b01080609040f0302030403050f100509030c0705130e100c02060c07030c030f140c0a021018090e0c060f0a18030305030f0405011b05120c070803 76
    0x184e44921015080c501122007084145031141064103200c00c2100f01d00840d00600030044480d01c1c2807040801d5800115990003048078013507446a800e00210700803a440211102c440d0f40684103030f030320b81501c036121246008102c25416400758440000c0d19401a000e1084641198502001d1450726034030f81852540d800590042d14407681d149100040da40100b94040d0f92016600c8041e038640d1010001182d0050085480c80000342c0284000100110510001c42d042240c1c962035001c40302515403070845890346051540c80c14403809140503120343d0000700c060308401520030018200700703802d4414041c5143d03141222405101d8460140b100700090305040f8410750301904c0000528500310b8a03414a828125041d00e81c012800080656842080200908071801181c07110308101030782d40c60303402400b012484040c0c0010014008203141d41d9079550901d40040c081c1d00003081401d100a0a50241c0d0700c800d100e031001c20303000103081d1020880b002c60668040c0e2540c1e0780d981010119140c4614600c0000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 207316744 1250 207315494 207315499
    0xc0922110102010b100815010e060708030402010c0602030f071707050405060d06050402040305072309060904062a0815010c03140c011e0e0706021c020705030a0303020a11071202 78
    0x40c800d456641d100f50f216030108030006140c3c0a40c8030a400024180362000d0b21141b80d0902c21000c94042c83d409204448003008025108515160090311440c2c2242c102910403030420407018420030124545001a5003e85015013549115060214019200d000c0c407104140440034410208a4680e802405503001c80303605503a040c0d0380d00d00c4051200014000c6810841c2e2252001c0380c04018044001035010030f646101c83c0188070042c413840c420000c1c03506000201c3c1e028100200140913410009a816000340c032072500070460417408403103c40c409685110510310604a8103222988540c00070059401200004103d040009800002405404119405030600c4510b0030380384890940c42e411175403881c980b0b40081001404001c80d202105440c0040d00c0c910703a04240d1440034002010070f8500450b1a80d0300140070200e40010525102c10140a1310015070040090004030341e2814018000c803284203076030060b1741e150f0526010303004100e011030b640708035401900180030b030b02e001c03425190105804 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 207317994 1250 207316744 207316763
    0x1060e0d03051b030d02130e01060302070c030f02010c0b010b0a0e040603021c1a01060e01090b090f01030f06030c080307021f02060406151707090f0903081603020702030607020c0922 80
    0x402459034034500c03645c078096049910016052007040030340207644c0c054070125201c040041c0da807240b00b201a4003e411010780744000d90344c010000103916800400301241b06050100444000d6240d14001603000d82c040b49070400001015001c4641c05007603440f0540e021181005145c1c2540c02103200002d094600742c021481c4000c4140500c0b070b400044210001114020701481d685800008140408a524941c041446d804010402d1040101664001e2001070801c100b103079503520046018003401402c407080d913580c1c0d010100100d000c4540440151513180d0007566640500c0c8103105800b070041c0018440700b043c40040c40300c01030303001c602e5680180c0c10140110f2407400b420102c0c060717074410798001e02d1031545d020280b04c00030001041d1042169400c12003007180c030645e011088258ad0320b41d10700030300103104180043c1c0240c400c0024805a100c1a00d401810031201d0390100749820421340c0c011f00983c0c00403d20446900d420304216a2040c5140c422060044400052400b600b14016000b04000c41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 207319244 1250 207317994 207318037
    0xd0218011503091a04050f0604030207030506060603010b03060d031b2907140a0302090d0b10060503060f041a030102031003060c0201021c09020121200901090b0309100504060501060e0d0305 83
    0xb0007054034281f10702e4091304c0321030400d0314001c3d594082900c0115028080c00e4001104c1785400c6003900d0480f5224035809245544d08070400c2241594034504030103010040400c8203031032001d12200c08210780301e522700140c0802c0040b1020700c0c0501036201035543c1c1c00b00d402002029548111404105110a070126844030a6400c0960190080841030341d00444c16034000350501111080e8203001c0d03261420101034040e15160202e840e44000c03240c098006d24801c0810003a41401e0780302d02144109041502e0080c1c950500003400c0e640b06440d01c601c2559107800a1003440300503c104c1108884c03d00086203080c1004010383e5400702040403e002080d603a400440c00d59000b0303840303001c03102c000b1807801700035484081d1088014041050407880c1c0ca450110644400030500c000c46540e140c050b1035811002e4503040f00407115920061090715580105d9603441d182036100d020f41070040788034041c00710b0158144140244203200740215144140d0300b04042e080400d411000b10394003c400700c13007402c40b00113 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 207320494 1250 207319244 207319253
    0x30507020603130510020406080702070807060c0203070b0307081b0307020703021e1008091506030601090c020709020304200117040204051008030c03040f050306010e150d0218011503091a04 83
    0x4500f048044d01034028054490903115880e070003001039079155200c13507500380c0b1001e008a81d01d011500503841e03154040301c4c00f44042c6004040c5840c07120310013000c6079050b81d00c481d403101c4603810540700030380400c034483c040c40780c6002d0350111503110340d4070300d4800f50643c9004440255108114403004e40241c070704411139020650440c60100c5000c80241422a42c030700100e0303000f0040801110054082d0280d8841c114800356602840e0380500360041c000d09981e420018080028403001050205512686000180310002c50000e14441c0307004500060f03003040340380b0300520007038494402203041000e903c107694003440300403000c0743e0019010f440001d05d81e5180485585d81607070580221582e0301c40810003418000c0000001c0056030510001d0f4076455544d030050641c1c0301002e005080800c1c034400c0004141c1550301d00404a204401404000c10003084e80101d02c4070301c0070440141001c0500d40040c84400c40c44454080582c03007510701003080300c10b1911802c0506030200403002000100c14003050610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 207321744 1250 207320494 207320521
    0xf020d02150a020f03040f06062903090c0a031b06050c06130503041809060b01020705060f030a0605060703020102030a0b0324060402041d010e0a0b0d12090e01090b040513030507020603 81
    0x4c941c04007205039a41000d081c210f424160400c402c4030b04900340100425a11040c00d40c10450000132004810121010110403000d900000c04c5480b00e0b10980a519400e07503a855084130003903010b100084e070110f003201403a0783c0521480d0405002c0c070801b08603410480700c000584643c0142080c0e4000004d12061074082e0131803245030311841580c601014061040034a0382c0c880c41e209840f0700e0381040b12203600c0006a031118007a102e07140d84410705206c034260b040c0e5020015039002c15421000500640c40c3c0c40001d80139000f00d4403e5006030760101c100000459288103030310101d00110018a08040c499034107070160707004420450141c0307815501251840d25250142e40203406a2071250f800320004a030f08168040d8248a0581c85211280104450541521400c0300c0000c010300b4087c0c054010f603d4240010482c203070032004025036903100203085001201e83c24080c018070303640030800950f510f04000954002034150b802c0610032201d000002a04041240c0110b94180c5805407039070748104041402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 207322994 1250 207321744 207321757
    0x30e031306230408071d04080319090b07050d0e07080316080c01020403050109122606060909090c0f010503060a1e09020403121407170f09040f0b010f020d02150a02 72
    0x810110f40401c0c0e5401c0850110159131207409040340c1e04c0e10326070381c00248941c156005003801c41c0c01c00208035080100c0d8041441c0961076000492084001d80d14842103000071504070b8000b800102d1090100d901d240141d0710342801400c0109011820f090f00141c0780c1c03152080d00403040842c510712201b0003503c80c0aa590b003198403002103448503a42d0618902800003101c00302d6564800b00c0802203c24000c8003402c0c241d000005d041c2060902c40b00c43d9503c060809403c4590152091010400031f94903202c0e62480f40850310040c014140c5410140424201e030b03071541c541800824000c00c580c47d1038150111044800d5a0910709074103507042c02d03110f140385098210052007800000e0200038042c0d40450000e0701401680c030f010010003500807241761800303095402040844604881c51002c5100e601401594070803c07501443c0202440000f002c640792a000103403696101c0828105568001c14820000303903003400a00110202010001c0d224555440b0020314000c8100201e101c460203941642d60703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 207324244 1250 207322994 207323057
    0x70f062c0f1306030b18120f03150a0801021b011d0c1c120c050601050603090a0b061c0c0504060501030b010801061b0210080603120f0706090f0203030316030e031306 73
    0x20311b810059010091000c2d900c544041074401c085003001c840196038100c9081e0708402100c1c0d4215201c070640c07204040c0b07484503840e911180922004c501c001081c4002e0040400c074000c0c24428440c020708541c02e59800e11072030603800003a042c0f03041d0072040104c1c0c844941d000c00c4460070505141035a1002070400500005041040440c1c0384e2045180c000e07000d014031038000d60899070541e070794a080025900c0100c41d200082e8021111010001c1c001c2a401078000d40300400c0640000729100d140c54030140d02d1501a501420300a03401c011504061181030090f00302032a0a0003000c01c20b50020b8200a0184514002c0080b0140d42c0c19100c14000c011210040d401010003070400c07481c24004080807401d6500340e10900400b0400388038000704604a4426800070b81c001410285142c503044001c10080f18160751100510003080f0069070140015032092030b07200941c60003105c00702030060460300c4025900c0010b0b40100041d6120842700048042101c100b0320700b400c8500703650300401940141a03041d654 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 207325494 1250 207324244 207324263
    0xe0103050303040b06031b01050d1b091404060302010e1003061206020301030b06030610060f0c06150e070c02030a02040f0b040c03050712090b06060c070f062c0f130603 74
    0x4000010004501813400303059a0130700c036210031003019120a0350390080e06010790701c0704042445502940150200c607804c40700c002500c521014203d200c8130810110000010390907407080c41014406071451494480c169000c104d10390460b4006001c07a00b44c440401c2c0320302c00c1c001c2c0800c1d0f2300e446a00044054040c0f020304c00c051000525100010f50420700040302c6480140d00095941e00340040e01a01c00e0781c4812082080305c0c0b806200ba074281c0349060b0b09070200911003500b50b021421703a020381015286440700d154501ca180c2014002c03c0c007805031000007004a00000300c00507940c0002c04221450701100c0000325095178042103030090451081e41c90b002801c14055012a58055005921403e4661102c000c1410241901e004880d10440b0040a5250081c003040241c14803401804880c1038a80c1102e46054649082100015081d03122038001f500a500d908200079140d0091500c4003408140e02105800e40800140880c15480c000b03400303101a90405500780005810100045400c40a500e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 207326744 1250 207325494 207325499
    0x2060a06060206060d02010c02061e070210020102070b041407050306010b040e070c050d08070c14011b03090b0a090206040806161e1706150c0f0d1106070e01021011070c0501030c0507020111070e01 86
    0x20362040c0c0149500b43d2203130740b48ec0031100046006000321080150f104404106070b64455490300c3d0b82d84400900140248030b070840110700760300c04104450180010042c210349036441c0c00911072420b24010304802c1007020710400540000c00000350b4141c58070460030100700079516814103d503040070a40700a001d07124100103550711018103500c5007210310340c118800400004106401d40950f0040d1200804803614280021015611036020110940c401040103180c107079662a02c0b0310f8260300742c03995480d1245075070503640c403d070304111814540384034040c041c114a20500c101400c00e05200c40c2c4070400e800c055002804540c0d41c1d000320841e401100c02520f443c0d9200030b81099689600c090f004105100d00030642c4480c50141d5032548045014500400c1d040c0e0724510221101300342200070606602c5400000340d088034080c00742c0e150f1074402c0701886403240c401e800c024411b40701c6648200d040c1407030840c4649140790700404590030680c0a082030140703c081c04060905d4100d440e44081c1c40b00d01d401d00003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 207327994 1250 207326744 207326797
    0x106230a030c181202060702030a06020a1701120206071e020a0b041d04050c060c0115031202100501180209150f031e06030c100e1002060a06060206060d02010c0206 72
    0x382c4001c00503075291203e00c5404485040e0f98241070080303045610810a03000c1c01403801070028003000b407020742980c1150065546242c04d81e084041c0d42c04c0032450003065502540c401040941c018040007c0d104030304005034002c0b404600c1080c01c09006180070350040b4248504820210f21945e0780900f0b11000d0399520f20580ba4590018054040030644296020700800c107016100703400346401101806003418001c082109a13441008225420754844140c090018000c250100040d0300401c0b80003413403140d6120003424105006076a0038420f142c00c0060040705081c2d0841c1202c074680b040e00503aa500d00400045641c21000c020181c1c030303440000d43c1031000e030803100514000d48441c000340310315101e9802d25a001541c2100e074181c26501140100c8040d1400001c5071501c10402c0c100320713000121280106100a00501c048c8026030301500c24030000c2c51440c41417600030002480038180743d00302140044c0000c66450406810080052440001e40d5500d1040b0703100c04d0100545520442c209144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 207329244 1250 207327994 207328001
    0x2160506010902041809170a120609061d04032025050a230103020306221a010302040303080103080702010521091e060402090a180503030a06061103030106230a03 71
    0x1800c0d281d0701402ca10501740049501403a40e203107501c900510b284c452109001102c503002800001c0c20000a41102c00107020380744111405042070000c003280d4903041c4901000703140b200d0043c1d10803641d4810f0811020039401100000c02c0400141102d000d580c00f60701180c50141c5d15501d2101d49002d44c140b425000b1960103602048071400d68050070f5040d506d60000484403004c1c51181c90010107022018074941c400d500565010301d0040004145210205464104c001c0840040042d16640e25440b040e1603810001d403064440309280544c5001e00b5540d0007400b0706810b110040200401145c4041160b00840543d08040180ca01103d8081c0f40c200010114410a89070300900e4080c400d40800d140511002c1c08603000c840c4030060076540c4999080c007503200300045c01940c034541d940c3c020721103c0020624041c0c04a003d08021034903801c20200d120102d615950205061002e004101c2011050100a03039045070780d103003404486c86101160105242007185840c00040c80d00140d4500440d406030f1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 207330494 1250 207329244 207329249
    0x3020c011e0b030f120901020a0609060c08010b0301050a0501030b0d080a02160807060f080a0605030d0504031106030105030c0108040303090b0115120c2c09010e0414031c0216050601090204 83
    0x180e06015800c02c80040c591100c48041508419400002c04000300d110380ba4014000d0b00010700c100c8004146544540040319452601101c006480c1c0e45110415a80304005a016001050149195500d00030003d014500b151003050f0525031100d14070b542030355070381d61034048864005416540c1ea001c0b411009440340140315120346503c3c5018404640c80c0000200c403c140d0702035841e800030043d80c9040603910880018400f00c4440c0c0c49401c04940741d01c043c4900302e90f100c0c003526020703102d03800d62500400e07000e240101d46004000a0004100654002902092068003804c01c482d07280c4035410110040e08001c2805807035108030400014140e10070500c4001030b40c185079034085142c00c03100307013280a89261022002c0005c1441012100c3c51039a4000c4061145900b80c2c028542c0c241c00002c6022040240e200c040000740d07080070481480f002004480380d08020700e0107980390540c9550078a602000282d002081c4560200e002040c1d00c0c0c502034030012694205088407017643e501d00c8110041e601c5030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 207331744 1250 207330494 207330551
    0x605130c0603020a2f070e190e10021605120414060a09060809030d050907050a08030313030507240b011e05030f0a240602190803061003020c01 63
    0x8000000c0d01c6100e442513a0601c021942c0c0c201c0e2030702100c9401580140444040011070b0141031140c810a841001140002d1001000a100500e0b01c04c0003140d1000100d03012005444c2841d014040e403c801151401d2801e0703005a0040c0c0300c1c83c000c00e11800781e5010f84e900410034441d0348107003000b40100030050011111181c07071246000d030b0182c041c00040c2c011000d0b1078000c212520010b109250080801560000d03950048a06145540c0d100d801620780c140c0345040140c00c044805c0c40603050950002c000780441740000c621714142825012105210940003078100312011445804100e458489900441180141d404070309440d00e506400400c20400c02c5800310304019410b0b00140600890007051840685603903066a9594405171141c000081c510041071741d41c0c2c0031050315600000a9417241d0240507244541280c2030210184c500003545203040780c0b16040304c644400103100c00d4120390788501c050301e01075001403441034213801074081c58001180c29403c0c10604880212007114012142c98070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 207332994 1250 207331744 207331763
    0x612050105010c21030b030a060614040504080409050907050904060c0305090d0906030506060d060803030a140c07030e0f04020a0c02041104061b1a1306051f060e0a03060513 76
    0x2107000549010009080c000d04828550007030319240211410341030b0706880d0038107000c1902c6400308002420305640ca6021609207035034100078017100c0000b284403440c003107090303c0070456030810383c58442d4075000d98496940140c0d2200001003c0c44030034882c18006000107401d10b01142403515120010703084101c20500040d10342000100390303003400103107010384070b20170f8803030305003103420904110042c2400600c02a080340e002c10040c040c550345803244030000e0654401442d00ca040955200d800c1d600480c0b40852024144810f2080c5c4041c2d00d41114210f0340c0c982800001001c0c60310100382428007440016901c00d02c040342111328070390030041c01d55030944200c40c10803001d6004103c110782d900482c0210f400085031143c61070304000c0310520314030515000e40d0713080c04541d896544207520942d00b11009000358103c00016420800c0724020315400503443c0100244504460507401849901d920650081040400929440b0780354220f2a4010750b4000c24107000c1c0d4a07001002c0e0418101034001210007024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 207334244 1250 207332994 207332999
    0xc0909030305061915140f04030807050d0309020919141f090203040807020d02130203070c0b070c050c0411160501021e040e0a02070201090503060a0c020105101a2206120501 76
    0x44c0250300b906440c0f02081000d4411182d500072181c0341c40155000c20120000c0200301c0081d070390721000e040114420f0000948d254000c0c076105040001c4100c04000381401c0603c80b20041c1c0d6126074842d031004642c070450903282c07810040d44015007004d800041518003810140b1190028010540e0140510700c0240741142da03590307286401300c0c40b08903000303070090f0003c1c0041c00c0189006075501c81483c0c00140507c0074004040c1d40303042240d009507040c20118907090480c104100d058115035a0002080c10816a444020340702d05441c3d81e902e6030078501c01e941d2411403030312032074540003621082665292814440d5150f031a045000390700c401500e418004880e211480c814406c4421103080e80d12040d441d10040d1078010700320019402c920b070300300c2c1809040340c00803c0715201005401d00c1500448000714800d041e0590190854401412440056200710000e02007404900303201181c9080d00540a5543d40c041900d41000038284001c4a080640d44030000541684c0f0002c0c0c9400302c412000100080d9a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 207335494 1250 207334244 207334279
    0x121a100504060e040504020a0e0f0703180308040b0910060303020c090f010503030d090804050d060f060608090316140a05160b090a030201050a090b0c030c1b1c0c090903030506 77
    0x118030a2074001074509140c096581800d0b0012900141f01526082506448031000c14542d8400c840d0341000c2e0100e8410400502e505024801c2ea41c118448410800041d6850080c600c2ca0018009061081207070f020850480d8108090820030444140c2082400e48a15009454801c18407509114200c0000440d00040502c04402c0c102d40c0010011450400810f1500002d0702400300191143d05041c040017032540c44880c412140341d482050001407d130355141c004002c491540c1c1120041090010401442160000442d401031000d0410700a41c8106031905080d003c41858031808603000c1c40007440f0400400154482c68241070000c0c1110241c0c46511072500c900030040041e511180000e01007026500610041640808929044804507100d413507141e01b41c1e100720040780c0f07a07070300010350540100000e210140168824040359103241013244001001004c00c4000100904070302c149010810500700100d0005020015040c40103030001d00b8041c0041c6412910341d405020035112881914 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 207336744 1250 207335494 207335497
    0x12c040f05010f0e07020109050d0c021206040b0a02130b3c040303030f020912030915180405070c0b090a020a0506120a020912010e240103050715121a1005 68
    0x8076540600f40260340d03d03081e10081d030001d02900150565503503031000401b01700b080c050581040c61584421034403100500c10b0040d021840725200c1c410740c12003c00d02c400900d02c603580c3c6420040500c0e000d622800c100341c800c01d158800794071620205100207a40c9075061041201c0000d030034203450101701400005a5120900b9041d640c11850020b401c100500c0020b0099010942030580d404d401414070486901040b50102000300c032840ba94004290140c1916000d002d4050b0625600103860400c2e124045124032040a8046280304540351800150068440c94949521903042181b250031030501201c0309840710f42c0d560f000d078082c0d00300800101d40d0b418800215a1410b00b8514003803a6541d40103004002500320881c1c4c2c50340005c55200407038000009006009402d00b2038030103072000e101e10180f10b01c51388a2b4501c00510f0b86c0680001003000c0f40001c50281c00b16059107441002c0c90781036940840c0e801401207a1000744620301000c1c0900c0c402c10070083c80b142d0070151761540d011040c04409483c2d5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 207337994 1250 207336744 207336749
    0xf14040309050612010b0d0207050d180b090306180102190503010504050105010c050c120f03040806010906060903230703080c01140f2707030828170601050702012c040f0501 76
    0x4513004c0c00400001c40c003000200440401c1c0c00380141004207556a440c10304a01c02001000284a41512408078904c00301d0b80c0300901008560604e40400440800d880d000000d008036000d184443c940514550290112039100c50002c6203071140401500c0050129042809500d018910b060000b203901e5001d5117100c0c5031150004028001c0000b11000c00070705a4101e961400705d4050540f0100322104200003810103052000081d101c0d03981000c8801088800f954805030070400810410400f05074612041c80c466000010301c0200d002d6944da49504e0101154401000f089001503003004440e419030106191619803040c5031a02d4540003442c2044480030b68400c200390080c252900402c02c202105141309110080507120055942d4407901c1d51034000c41d002414444420b800350440091110000006040c1c50608150005860484104250000300418180240040c0600030742e80603440c10340300c01c4429545980b43c00d1081d21200c044c0c0f840282240d01441c244090f9000c64200d81c00303040e06 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 207339244 1250 207337994 207338017
    0x406050d090c05040e010902010e0a05010903080c01060b0f0403060e0c01050f280503010303170c03010b0c0a17041811181305010e19230702010f140403090506 70
    0x922103440c5110000344100001258150030202002500b929240903880c0c2c92003040000080802c010300024108010301c3c2040c6101d90030080c0140102d0380c10031401e80680e034100304519212008060400d0040c00d0700d4000402c180408100446040d002100400c20b07a0b204070024400400b1b540070403640c4103440c0e5a02070110b6030a00c08822445003440140010280000c40008415a00249801c1020034280c0010010748000014428550061050388554605501c01d450614240b803588420b40018004c0e840e80f00400200105410310030003070f11103555000341c805400b42444464403a070130341c464812448009040d80c54045881c9103446a2100b20188009441ca0310000b441840f540c03640035088103030f00c0400412407540120740307441298040d112005018500741001c107090804807009448107014182450044030310031340743c11290301c983d4414810440054031030340020b0307000d4040423241c580c0051400c80c01d00c2824084010143c0558000e44070504a940c0300c100340070251244041011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 207340494 1250 207339244 207339247
    0x9070515190f030603020613030c1d04120c080313050c06090a0b07020409170a03050609070c0b042f120a0f0b06190b0309120301060c0f050102040b04060c030212040605 74
    0x10070140035411000010b0703650b18001911584070303800911241c2102120344041c6c440102c082c010021f051070101e01501c070f0460602001041601800301c00300000708000d000020003190121824040e2481081542d88000c1c00c645074a400349654414012084080e12035108282c024501420900110f030b01440c0c010306100e10a600b4800a4078040d488140c04981203640d0f0764242001c90103c0c0d8546159604500103140d40d08181c210080940d98090301030346c820078481040c88612038020981c034002d1680010181040c0c1c1d81da0a240f10049140b80707225170740c004d005c4164041c051152a4002406204981004c1c4032000b0b4003d00c1c4da2000020b500421800000003031034007040305110815030110700100540d411402e60030750f100d402c05190b404203881c0072010060107000082400b840e0724980c04110b41e9411581350081c002c107a68401140500724490013a00315090000a40440b400b034500d05d1b1060759601d030740b1540200010b4400c4415001800303a1400b081854926404580454250ba545c89 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 207341744 1250 207340494 207340537
    0x110102011d033412081501050d0515130209120c061b0124050306060d02100c050a0b10030309060309030e010f020a0b07031d0307020d14030d0509070515 67
    0x1240b01c10882080c01007604240d0f1240c1020040905840e1000fa104031000c02122498400103072195001510f11600c0c1c0072030105448140e6400f03c25100c84908008000c200c1f40c840a0381143c640c01800c09a0790054030005495120b0b01d842d4008186108059a80e011f46401c5541c4940d2151312401c1d003564061400c210001c47c244540c100101c000c0a80400090301064060145600341850780d94100c0c10f01ca80030f0200300d42d02e000d004030740d840901a01c00d11440c00340355002440d2420005100c1c0c06000c0403407080c4040c020200714440c092540903000c03c2982c141841c100181618a01c8201c0000700740708404500d4611034000d108240d5490780f1011090040c0c05d00642e15200e0b0410500118403d40300084041000e8000260281c0065100000d61903002c4c2511514950034015080c0c455000704110340050f1140308006100f1a00030000301c01010080210170304501c6206002c042080c100801d2011108000c583c0f4411110111622030030744800140b030024034020400303007142d42143ea00d1003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 207342994 1250 207341744 207341767
    0xb0924040305091513030b010801052a1303150c020a0812150904060c090503070e0606030a02120a1b0305011413021b0105160302040b0313050102070609110102011d03 73
    0x181800c0301d0010700301354841303040d101c40c089540c211183c4a902c0c03999403041001401010f00c0c0080c003516200e0028003441ca021440e06400c18a4540030490070310700b582c142d069032a005016100200540c0320000055542c909000d080c1c82304807828000030324541355a88440e40d00000b05080032030b07440246523052403509440001e0f0303128000c10f000c1c4804000036001e0020780e50085541c1c0300b10710030340000465441c0e00304020510041d5410560185c1d104400a0110310000e0340b40320340c840001c407003503a03881d42c90003089006406a2507041000fa8000740a01c4644541d40d00000c4d242e901d4020100e0644031205422000d6903000e104001800c5e004926906035410581a02c00d20f1401071607003d49010940705c0c225076412440d14045801d039560b04280080340742c15034882d4450320b0381860150f09146c1041282185403102134200b02d07000044008980c200306080d0159030445800034001c101c0c0e8141c6040076510141480303403c138010351810382c4412110b40b60700301c00c04000145100442c10036602000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 207344244 1250 207342994 207342997
    0xf0b06070209150a0b0c030309010606050c031b0f010e0a0b0f130b07030e06011403100c0e0918010603060204240906030b060909070c0c0b0405011e1b0b0924040305 72
    0x3212600050f2034900805c1070703401d040c01046d1610007280115502e160030040542110902d801120422004119040b0b400d5000001d48411a494422a040100c070340c2410341d181c01c02d082100a1345500701021071000308008a081c200c464011511498203544500701d40c0a200000c80c3c4007034038031444510010201c3e04e032094465004030f0300e0400040c504801c0300e426292034401d9006103a40f03080c01c084200203040c1800794a0803108072001c14492089035090103440ea4181c00c08207070044850100192021040e20240e0074030504c824005c00c8455128104003020354420b008014a805c1c00892110103034482440d204482c900ca0f640e03d40700c0301d0615501300e001c0c0000c80d444941c000c01c18441500d09035141c503080da00581c40c2c0e84480500d02c203645000c40c8841d000307034071012a555044c0002c000b1660000b50306c44100345a020038080b101d2501406030381c8100c015804000610600c4582d80801202032840307802030100b5401c84100001c200465070442d143c840d4100b541064107008140003900980 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 207345494 1250 207344244 207344281
    0xf2815080606120a091502030603011118010e0d0606060305060a1401020604020f04140c040302040e030703091e03120801030c35011415010f0c02010507030c03030b030f010f0b06070209 81
    0x502155078070158840d407144a4601001b015030b15400000c0c00301c60301d030905c40c1421590868030a18145400e00460709084540390b1a103a06101d1940c2c6808680d0b62100350002c07030550300500030003078540c40c4d540090040c9012a02140039100c00b64010407400220400038005e00016802410b0f69035443d803d01841c00b04500e850b640054551a18410b0038007400a524450040c100101c0d4640345140104400e41d00150180405a0020000ca0010a07400110301d026152000b04425602812400e101c070341c45015403010300a030744c8043c401c1283c19070002c541ca0480c2e004441100b50203854021030303000400c0f484c07417500c0d003414482c0700c1c480d000200032201c08010840c0800019444c400803400c88112100310b070240e9410007540000c3c03002d0760b0080391041035480e540c07400d07010a102c5940003914a00c50045c0c05018031281200c40d60030988240c0111451780b1001d0151000c02c0f60745c03482c070b0b8060480e58022074a61400e00621815078207010782a100d00ba070b001018901c0c0e98036281c0b4182c04a10b10b06 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 207346744 1250 207345494 207345511
    0x61204030f0e0409030c050105010b090d060513061d0c040c02070909020f030604241406060310050a08070f08030f071428151103060f281508060612 65
    0x6044080b40da64551140b00f420a01a8403103209154041c9001070071544141c0202c0c1d03a203002408002d10741c1d04c8407a003141000c0d60108002489480d0400b0301a144001c00350020403a80c2031840905135503501d01c0341d905101d203210088445808510041205940c0410440b10060303000304006c1141000030b400c1140c2d482c1c009014641581e164001181c1807000494060328407000a0420f071440d151581c1e1080c041c0d1446040c02c11802c0b40c14012484181d501803d0a8861130012020840491000c5019401004001c1050038260303500e040c1c098035000345104000048214000000b0f02d0030000c8106c40001d1030940303501d0b150a0b500d0361035400b0f840e68140304510a1140a541c1c9002c2c039004203204050b96403d500b58280d14020749010f00021141c0300c02d1400030307410700c1000c03218502038000f0f60790041000c5844222081c0c2003004a001805130405081d0b480610260713200c01e45034407034100741c15103003031003e140e02c42c840f101c005a40da52003d454482c0c00030750401088040d040300011558204000c6e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 207347994 1250 207346744 207346757
    0x71b0212010203070315060e3a20030601030b01050613082d0312040b06030f06011d010501020d020706080c0c011505040e0705010e060a1e0c0302010506061204030f 72
    0x460380036422070b0000ca8088020039640d60f51010b01215800c480c1004111f40d240000000400002003542c00031100c10400315011444a20b1001241c1c01006904c1070f03606e25a590032102d018140381040440e1741e0039900b101518241004c0441c1030200b9041c0c140c0703800111010659180c4000d00c2040d0703009210280c0d04003e41d1801186c140c200b0f01c4140c040d4002c560010316240e060541a80c08180013a041140c1d50f402007201c07000b4024558492030b802600003400f04d001c0d035079a101103814040c0244010320f090154900105101c10b821088500182e4600600300303141c4c1c0c0358001682d13504401c8407400c0140c1d222540400595102c0c40071581d1200100c00401d0030134000e03141c12825203c2c02d18002d001c0349000780044c041e0382024030800d200070141c00b00510203c3d142c07600107001c060020942c203014103400221958440e0240020103d420b015046544a4145040c00103080002c9000c046006500342070100e0418540002a40e11008031000002500c2c0c8580d41c09032021000580303081c0900c0704 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 207349244 1250 207347994 207348019
    0x6041404020702090109140703091122060803121608010e101a030603060a0216060f1503030801150203090f120a0b0112050c030604050d0f0909060f03020f0306071b02 73
    0x39080304080c006c00e11030317a012070500d10303aa0345d40000c100000d01003803c143c6041c08260214150a007170f48000802135a00764100c20516051240758003981c0700c5541c0e01130800354005641c402c0000105555004060103000d5034413900e080703001c00324000c058040060203080c014000350006444050f0095048100310342c2940da203404189400c0a1440e924500d52404000c208507401d00740051980b00107646011072a01068030804074080140840180c4000d554802d003554819040c0e01031424010704260000b100c0365039250080c02c2200034080c000c9113800c031000e0307000d2207400082a036540800040540000c01000024400010448011280184540c0480350701041c00350740194040d06110009080c4e403149070401c1c900c1c185103500f900d070103075000504000202d040171501c901001d42503c0d080c0c003500668002203d07524604d81041d0442803600a0000382c0301c0c04803145404407442581d061036160840010551030360070407030322400801e01018010020b5048100880a030a1008040561015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 207350494 1250 207349244 207349249
    0x102130315020c0a06090201180609061b0b0108160e010b161104060306020a020708062a040905070c0b0702010513060e0a0f0501090606050303041820071a070e06041404020702 77
    0x13202c2c000546005079a02d04810a55030300000c0c40404c00d103194040041185070000c001c1500131903100d840300300a00c0d080160b85c0b110a1680403030a807604a52803482658450b10081e803a4950f030380c00c031000c4480341a000185020140c440078100c400e83e0b1690703030600551000d0b8002c1266010402c417000003007000c2c45d45e480c1d076840c40703200041d5014620050712004e0100002c1d192802d80d80200c1841e0384003500304212400103914800e00c1c3c60071f2440d140c04040c40040707503036018000c580000c0c070014149010014420341c007a503906960f901622a00a050b21080070580c03c8130340c159081c110b0014040400c4000c9013280e04415021b081c818201c1d6600c0c01541ca42d503214405140080300c250351581d140344140700c0c1c240103080103010103c014628091420810002c41e4260000c1003034115110100707d41d5040c142c0300c4100002ca80258540d5441d2a14031b00810342e00100c08400208030034440201e42e020b442607040c40c580c0b41d00a400c2e07502d4503041071092440c0c0140c2000701a402902084264010b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 207351744 1250 207350494 207350503
    0x1b030909091209091a100201060302100203030a110a0c02010f020c0d080315030f030a03090c0e040501020a080c0405030a11032803080a09030806010305060f03011a0108090102130315020c 82
    0x14040c01c4030000d00b20441c02d005007009610350007104498141040044141d00c900108000103204549008030071807098000d90142c02e903a80080d50007c001241e001c3e6a0390040003c0d032142c0c1e071481d01040702d041302c2d0300c00383c01501403502084001100740340703110015400780240b045d0446840c0111403000d5295400038000e6070800c441191441404014000d0111810343d02c5400c03003008a02070140c5104148480e56280200130711034013015142c1203008288880160403501604000d01003202a142c9818058042d5000100003000105030000040609108000791410340708014040d08002c1d0541d118810001140180305a1600a550700e25409000c03141001204c1880001c1001e80c00307000e4100500248030080c22548814100b94a41000962150002e94031170000d0900041d9134480d0710114084c1c07804115415095880d09a0b005441201052801150002640c0d586829030710080b4043c285d000700c1c11040d030402c507a100140001261911201c00300e9140c00001814003400310b15103483e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 207352994 1250 207351744 207351761
    0xf0305161407140a0305032205040f2418020a12050702010605030d0302041d070e180a0b0117010e06011e09032a05122b0219031b030909 60
    0x658000366082000c0f0b03900040500c4201000c440f4001d02d0b503e5070725030544034850408402211030b07904100b0070920308080b9178117028000181c000c004900f01004404010140091003a003c80301e62400e003ea1108801c07c000c064074607099800e0904101001d540010b50800c000000c107000e1110368824564036036225080c0304010560011a0451814040c1410548101e8291003014010002031040c4655000410840c1115101c0c5800a40d900d03041128002c4484c03230404c0e07000151090003441da65802c002c41f8040e0440365010000c82d40b8080064488007603a02d014904500404010804860070001c200d0740280103042002043d4082600c00030700340e801d40e003518045408400280140b060005074031103060f1003079022420000d401c070b003050740340550b44c03080c03910420120003007a409400502c000c540442407500c6140b801000c40203100b41450400806100501c1a06a08003110544060440c500c81c0c045d22201e004483c079604c0d0490b0b1100c4441d00390700348041644005100003403803289829 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 207354244 1250 207352994 207353033
    0x905181c03140c04120218040c030506010f0503060a02030414070b0406022116170c03041403030307051608091305070201110c0d120906050f0103060b010c0f030516 72
    0xc104540840c0903003207403640103104045041d00c2c1d0030850201c400404850031344120300300380d1502e070b0307140d10015016964403144000d1007038868050000b04416461840150703449500cc0d0385c0d550782c80307107000450440d09201d060b5050340040c0102e001c032105580255001402060010110500340d0701e001d290071801d41c0310341d000210000302040700542c1408842c6030b104107808405403555240381320122501030002c4020b121010400c804041020b1084100020a049244251502a189141c0703440383c001c0d00c40c043e400aa440345001ca61310b000301c100c900c1004a5190319042140703a240c15680b07280f480100719140101003281c4100ba540d25000150082c100c504040b0311072404000090035a400003441c00300d2001c084c00924440710000c220001c3c2c00c038151808200658a002085001d02a5514013400c00c07032900060020074034170882c41e41d0580e17010b00d80c01e0060750308131401141c1d2800d940401070030500aa17149400060710500061440002814086020700b02c2615104e8060303205504040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 207355494 1250 207354244 207354283
    0x1020408030c0601050a0303080f0a151401080903130b0a0e090a060915180f110d0507090b030c0702090403110f1e150c0a021204090605090603030a09090518 69
    0x1004554200555405400191b4210049a10f1756401030036070803014252000200403d00014000c504661110100180241148414965482d80072506840d50741c00c4a00190755080010300d0740380c0002c05c68004901c2c2c40f4174044c2261500004523021340000d400e2004003d5401c11060340d59540212182c06045514000070340c0c1071800e00d01100701c5041d03070006c5010b000050000c0020078488900500740110100b004604041d2040b401c2005215803014030340d81e1840410042e0005003140e01007031180780142c0710940e507640c544000030160f0004071020301142404011000050400540c429003082c03090500e51240106c00303d00d00c0c1012802c150181c0540e200c00d1107010350b40040c00c1c1601858185002601c2c050314600c0c140140200d004001d440091000104076103414800c2040d24010100c0366000d0340c0300e80d210303840107029290500c101845400d10001194541c940032040321103804094403954172241c0f41c80c0280010b002c0090003688040c409107a604000001072080300c038490b5070140d000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 207356744 1250 207355494 207355507
    0xa060c0315082b0c0b10030308060d150f0b0612092505040c020a050307050313171f0b1e100503041e08130e040c09020a2f0102040803 59
    0x1400c451881e84511003503400244401010903030140d280c11002080700c50a001d401119006554207094144c0003004414404204000303042080c141c1411b40b0b1081c6c0e503a0703805031102010031480d2107680b50040c02d020040000003030b8014240d800310f104001010b1001c1208040b03e400074295030000e5602e80f41e103154010030454084401d00000c6141e0025203642c0b03c2154010f0000e0310b40d10780d9070150714000c0d03a440b0442c03071303030340340200400501968000200c9655014500d011912904602a01000017859140101d01284a200921159000100100301009031050220040c104000c168040d941e0340d0b60340f80d04551107624058080403034004200030701e040b0101c240284101d020b600340042060520500000485800c0d41003003640c0040492151aa01410071107001e1044003800001b18510348000150b1078500840c41c0d1255004554100f400750755a004907081e0f101d071411080004641c04082520303023440d40d9141a9110360320410203c06030000611a00b240c2c81500300b012035034000b0488 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 207357994 1250 207356744 207356771
    0x110d0f020109210b04050a060504030f0806010503070f081512010b011b02030c0d1703040308010513050f01050d0602090a0803071e03050d0e03070f030503070f081501110a060c03 78
    0x44801400200010303e5500c049880011119440702c1c070040c00e003c0b12601003414000200200410144c11031405c100d40c1c10145000f9021140c04001200401d0726480052103540c003800580c2e103e61410348450303c0840c0680800c4807440f0300100780503901d403004403005141d03440c0e0100e40707404216001d00005940039420005803025009032000500310102c071001900503100440c07048201c1e4401e031840310042a99140040628021028420241d40c0100401c81403590190005048450543d8a81c0c0c05084112003001030b91000c607108440b90102c80010440c0e0305000c15400170303071801040e0040c1002040070009414401030760210406a101044440500c11003141c622950040c0a42031800d2800359900034045000381c3c001c00c4cc04656401910456000c01c0c0225540e60b540200441400c550619016103540c0042d60007000180440000d001c400e8081e54442c0d0060315520780759180105800011200f41404480f8040da5015401e502d01c005455801403007601d00d641e80380840c105801c880d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 207359244 1250 207357994 207358007
    0x10206061c1208100503120a1110050f060909010b0d0311030d0501080105070905061e0a140a020a051b030619020403050f0102030603010b0d08090906061603030207060c0305060105030a09110d0f0201 87
    0x40e031107a0487e0300360700741003c40801256a05d01d420700b043e400450340400b0b058108180205900841814101000041c04408c0c80e00e1b84940003c651884640d1903000b412800c0b5282c04060b280c000c1d484c03074845800f29004520400040c10010201c0385000341000c01c040540e50207034444880e5a45034400e00584076044080074014240c21340ea4542024142c0400d5480c08102d03072a8101075010001e1030f100b40034454401c160070050140b60207641d81e412400c00956914803ca419078190147c0880504035080041c400401008014001c003441e8403140c03032030f182c111140c480e90151281e08000c0040010414402100f00700082c41c0016200d290190506007960039440d015031103014a0350801000078031500545141c528140ca540c4940e503115800b00c2c0e40e41c81000401c800ba144400010410103905400415100703120f118140094803a489050b4107498040d140c45001c50f0090000074030b00891a0f01c01c43c01d1600512035100c00c400c0c142c0c08126000b035544015900e03c50307072030750302e00640d40c0041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 207360494 1250 207359244 207359249
    0xc02210a050f0c100801030308060a030206040605031b0903070e1806010305070303020c10050a03020702011110022502030c37090516021c090504140f07020a02010206061c120810 78
    0x2144210031440c4c10000a14000b030501005041c02202c1c00414803980341c1e07038164005903034081c00b10350341c2d1780e12800301600c41e4000701c48242d5007451440440e00b4202c42da1082c0d8808a03400303402007604a041c0600c0074003014005242c406900e075008100c0c420048200502030007507016802508455056003402030805120710601805018401001d00f1055031103001c49103210b107140781c0148c84407a01e200481b284407180a81d80064468030340d4040362404103178002c00f01850000c1842c580c00c1002e144640f400c40891002a40c55084034243c00101d00b03100b001c4103034a5107051643d00386903090704480603458480c40d00d201d410384e0700c100040c80401d205103d85e682140e089950303052000703818440203585600302d440c8a02101d100320100c1001e1400303900a0005070a00500601007a03651020071180d482003102ea99400344038a1011580c424004900022029010381c040d00340ba955681c2400351880385848482c00e0741656000000100b00c40e104e20070049400350b074a558803130500403d070412020294 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 207361744 1250 207360494 207360499
    0x3040c030c091e090206070b07030615031406010c0305040803070f12030e0717010e03040b030601030b0108070c0f1118060307051017091915050c04060c02210a050f0c 73
    0x201402d0700c8500c9030700307441844400d50030f03010505008a1022400d280600702c801848018808140710b14a50150000070903200115001c3c030200c0c50b8130300101c0a454501700b005c00800002004102c181d48100d10900066009080c001e1409645568003403840d80080c03002c1d21500c111176808030401c91100700a142e00300d04e030b16003405509158800d4544403004c0748150100d16400c0110205010000c1d044040304c070328210242c030313140c0d41e0347c180000c5503030f200315a00341c0003914101c0541d409600911001d030240309140d4a006080c0391a80c2c0302040300c1c1e070400050b60b0048400c0340d010165900c0c200b480b000e030748542070501d4550500388245440e001c00d581200344103016140001c80f03150350200d00b02103039040000c0000c4840d2503003180c5a090103113020090061511411940060004103028414140700b034400401455841000581e404e0056015080014070310242c9503003d46000e41119500e030302c6100e41d032006603030841403151412440719030807a141e40100030b0445104401303002c14103540105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 207362994 1250 207361744 207361751
    0x3070e06030c0f120106090e07080a050601060c03090312020a02040501080d0e04020f0702120604031d0105040501030e0c09070c05010e06011511010e0307030503090f0f0d0e0409060203040c030c09 86
    0x1200c0001c0c1c545500c03404581c0900295000804142c2e030b0703520348412082d1000020012540c4500a07100504060342d1012144c0c803960100003990305000800100c0d05030040c0150043d642000e90485502200c81c0d419010051041808408100d4000d0100d06030200780e001000c1003100c510500056500503400b0612a4008060080445810100d62501031070100c0340181d0315161024402e80500070f4001c082c2d001030184c040510000030029615015502036154943c10781e00b803940b0031020946c0b20003018001082440200b04a50080e0016602c08040c01c05546206103c00c0210f840081c007140c0010008034800e0512082c42000e114803d4690710840181401d981445008588003019103003d004000d909640c0504042c0d0a41c46009010741075401d8a5a428407818001e000750010b1350108150700909503043d152140c00030700402c8010078180588505114544103562100404000c0d5400a0b240c00500c1c000512602c0214801c920411401c070800c1c0c04c5007001c0652076040c1d040003200314039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 207364244 1250 207362994 207363001
    0xc06110d1425061109010210020408120921010609060f0b030f060303120c07020906012f0c12070e0f0f0606091203030f01060305070f092607120203070e 67
    0x1009802c0b1084400380c240e50190119401e5441c01406074035000183ca65071500d02105a0300e29000002c00c2058001d90884e402560f01b020600c04038442da126207500d551200c00c81c1e18200c1c400d080508040040100032807a142f51031418840c816083d0726a608250350b43d0301301072140ea0102d00c41c40e809000c03051101480d460a101041c01c181c80040d04070500c150b04100041c01668007001210850920340d9801c944605001c5c1e011002d9030850710040703200340c00140c00103501d948500340320100c0d18480c8a10a545982302080c50103814184000f030200c81c0075551422686032900035074152200d2a620041001910b070104000410401401188800603a80b00b80302c11b18240c0c0707070300f1a000070045820342e540303028802c001034034203031140400074a900001c0300300502d01d10801c80300e60403500c203038405000540d25001e085075800c85c1c2c414403034081100e00c0810311a001401c404d15644c0d0401d441200601020400d12506e42140b40c2c0c4900d40a80c040e80c1420114203091005400418120b000383e040d506 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 207365494 1250 207364244 207364277
    0x70f1202070b010b0f091e040f380a080f010e06090307171e1306020303010b0a120b0303040806100f060c020103050a090213091106070c210c06110d 65
    0x4006200e80c2100010106402d031001ca950340c1140c42d80c410003401043c0c03200b43c130320f03280c81010b02031f4204a00c03c41c41c2c5070300445210024001e1007024406041c04513813405e00e40748051303040308002203001004030304c6080c0e00d096601e41c1140d41c00a010000001c01184051040403825191840f4607050241c0005007844140c00c2d00105440e41da6074040e04150640c10320100c4003e050045900c0102440e403140b000f808452100310003026000f0308200c61541c45910b80000340c3c1ea0740310038840e0300781030107082103e41145c0d80324403072451a0741113510740840c12202c2d00e00082e1554000c0e8001014540261003031080303e096185e00440204254011641618a442c5003e011040e003d0740180c141919500010012091a40446041c0358002e01031034021900300241401404504011900b19080d030311000781e180780050030764000c13503444620110352034101002a255042d0030140d009024200c680d030305002806182442c030140c100e695402c601641692010b41c580004110140c0600600d108602d5205 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 207366744 1250 207365494 207365513
    0x92612120c2104060f050a0219021609021602060d020319060302030601060507050c0406180b030703080904020726030f0105090405060a02091306121a01080601061d09070f120207 78
    0xb81600108001980e460420f20094072214101c0c0310800d20b04010407180c40020790141000700005041500d8003001554240d9a80c007201c0d101070201c108052040092240783d030001d043c2100821404e4101911030b50100700c0340d8104415401c0402d4010041006410403030103045410a00780303200380030040c07450f001b0903100c1d2818001c00041080c005550030038001c0c200981448030401500400103607a0303d0342042690428007281868160429104081c10b286c0001c0180669401c045041d10303094190007000000e502101007180d02c291540318080d1400560b4600e42d01240e03414030b08070303500e142529a85503000030582200b44528001d206000100320b00081c081da12401c00c090040c1e1b5110310000143d00003001001c406405402d0200115911540300e0807000b00c00c0c81280ca2040d04500002c3c00351008809019402c2c843d80034000400c00c0343d204070007005200c40a101221a289007000201d011480c0c101c80160200340c405600d2413442c0d9001481b05503144032a40d007181880e4540d0354a0380c0c40c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 207367994 1250 207366744 207366787
    0x32b2604020925090302011215120309030f08070b070f0c020d06180c150309050a15060b030f04031d030706031a03030a181203092612120c 61
    0x1940d140001403410819034880404a81c00040380206036440c11500800341e02442c00201e00140800b510f1841200c01d90160780410410342c07103d070020b641002b0014040001e00c6c8030a4080000a04001000c280300003500b5141d40d0040c0e10060342c401c0c250908006030b660240c410003c00180d003c2606406501c000d1703128110358104c64181c000034803400d000d4040d15070b11120104c00070076043c0c10020800f09944290444a003900b00b410305181c01e0406604940002001910f1a0030690010b800140706030006031180b251080002080c50302c444421016800445107440459401000e000c01c4c59049807088070f800c40d58440118460300c100c0d020076202c400358407400b0181612240000b03507010308130384103680d03540c4042c00310b1b900c44440410050403040400702000c4c0b2464071010100e02500301c400410f0036a40c040d11022440c0789021546000301d0b0043c1100c0740315000d8103240c03400c0c0300c00a01c07400344010307040781300d42e500c8480202002101e010090080008000200a400680d040103003c6201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 207369244 1250 207367994 207367999
    0x3110604030b0f060a0801020a02010207060f1a090c12011203080f0709140d0203060a0b100e0d0809010315060f02010c1803061119230c1b032b260402 66
    0x1155281c40313010660240d1290001c02c0c1950000c504c0401140e030560140000c28007400d41484803440010408084440721a080700050780b021041340703031034101400f986401415402e1268030f8000d1541300d4240303052082e0000088058018420024554041103050b0441000004c41080e81070100010706071103124818010b803604090b071403c03201d5a0348500d070a0899001f5003a41c01c0d03032030401046c3c80108603c1c59902e00c28405103103203c40303692040d2503c607511407019000da842403003140c480905540000c0d200c1c2e410940c4810000304031954522101c3c0050a854844a00704036400300041c0c00d40c4c001c0c0e940c4d00100018818120f4440104c1a44803044a41059000945810801c0c814205100341c0020305080401c20701003211090b1701000000281040704541c020003001100103d0652048003000001e0350b011290760b8003815507902c01e01c0d0081000034100c4011158000d820154a608464ac10000240008800b0280e617041000587d81d44102d65040384410410541c00311880c401501c040d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 207370494 1250 207369244 207369271
    0x30b070c20090105120a0b0a02040f060203040605180a081e120a09030204050a020708030c09153a061403060a111206010e04061202040c0206090703021203040f0b030103110604030b 79
    0xa05e03860034414040741607042031910314a40351000c0988080c6d401445100a040c0380c3c0e0381d00107566440803066070140c507000d0380d900c0d24203049501c0004d10b184801090680c051480023001031075600821840b031481c018a1004052000d0342850303181480d118070250945e0b04010880740c4645588a107440d400d0381d03411140050183c0750750501800900880c50000d00c412000420b00240c80d0a1001420a0050481c0c0d412610502415030300302c9070185400f0a94040301405112028050f041c0f109080c2c40d201e054000b1840341032544140c26502c0342d80c0294500b1515041201d00d90505001595120300b0b05141800701070030300000c0c0001c071300c00d403044c0b4801054100003041490f8861000d404882c0350081081c05801c1d2219921040402c046078200d03c5680b404420744504d07400072402c81c1c0300d981c18001030420145580c0a20a8010301e009010103240000c2102040304001001070038003400240d4040c6890351b04501c1c200074400749140307008e0701c1900144420400034001302c0d9000e600845c0200640c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 207371744 1250 207370494 207370519
    0x1006091712030403050c250905040203010b031b010201060b0703021e070306060f060807090b03130807020d0302070810110406211a0a120209010302010c0c030b070c20090105 76
    0x5504000207940152640c020000901062543c850301801c241554007080d1403c1c99442e04503403441c0c000b10a515180c04507102010402000140d100e150700034005000800c1d19002c3c2c400190400d4480740350107031508425003a5901950342481202e0203031080d03403100b6142811a4401070342c1da005021500040070070380100a0488001805000000c580c0a4400e0202c540c8401075085081c60602135400043d21860000c1d140074454800b000840717a4a406441c030b50b4480c03040300005811003d1081c0c646d010104a40801611956009100503010340e028003200c50034030951a0402c2002103001c0c50003814610b0000044083c0f5085904842660030b014207850100c0c61030080c40305158520f00a038918014140c0a8006091a00e00740307201d0440b02c0207155505e5246004440918900181d0001c07503078001400154010104a20458020006103a41990300e9450f881c6290341140c4e2800015441295003041007004200708120000403100c2c0107008150402044500c0e10502c130301d074440e160030050f0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 207372994 1250 207371744 207371789
    0x1508010503061f0f06020601060311071a060103090206070b040b01080f031801092403050714030c16080a030e0c010804020321041511070e010501050d05190c0f08100609 74
    0x2144000c1c100381140d50130241c1c1e070b540041c1d1600400d100300801b09050403000c0f0440c14038803049415003a4411448000c40d059100030094040006182c20305243d40c40b82850f002d80d030703280041c4c45032510030450302e86a890a841c0c019a24141a44a088584e102204540081c0404020303074a150040c5400384104142000049808008580c44070070201d41c44418010810b150248025404415480c1400315485230b060480388a08640b00184101c00306202041c01c0c2c1e1031042c018819915a44000d9541c2505525040c00c5940041105000300e81e1316146845841d2050040d002401d40908092400b4076040d000b2035156002021716083da00da0a40d03d140c44d0340740b094241c40140c520303580040d04483c1d01200280899214410303a640314429800001414211002d449050b92010f95841d403c0101c60b2403d1406003001800c1c4295403a4040c2032082d103030419225405082c00f241d610f05501400ca4007004d000f0b0a00074154940c0b10b64440310610090341c00640e03440407503100f9510b1412203004401e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 207374100 1106 207372994 207373051
    0x306140f07091a0d020f0406170a060b1b010e070915081b10030e0a0c05120615010f02010b09010311031209030a080c010209040f06150801050306 64
    0x40825070f8511100290100c003000b800058101090180f10080d5a0000c0c0c201c000040d010030b070508507402214031700941025000313001b0030403282481d0108265210312030444240000c1043c4020050300709500c4001180c2088007580ca24580344d4081e2400b07454100341100032400c0011002c50f178078030081120546518a12182c1e0002c0e2900b00600010b81c40c58501d44040c035a84004501400d20140411320141d031017841c60356007113802c00d4100321903e01e8405440065500000400c00f01e519a40b400d03490b83d08c2c01f401c11566480400c6070032030250500703044654100d03903c000000100110550b4034640034408400b6140a5070030703800318510307900605070010f60503800050000b0100e4000001070541000c030b84000f624200758038010606890b0bc942003d1086645c0324410400c212030500741e0540f10445181074a001d5145c180003c0e83d0345405414100f00001c00c0038107440e155811344 = true := by decide +kernel

theorem cover : BRFrame.Cov 207194244 207374100 := by
  have h0 := BRFrame.cov_init 207194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 207194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 207194244 ≤ n) (h2 : n < 207374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
