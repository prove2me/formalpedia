-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5513
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:57.642854+00:00
-- url     : https://prove2.me/submissions/61109f18-a64c-4813-bac5-5851c70aef7c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 991366906 ≤ n < 991546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 991368156 1250 991366906 991366927
    0x150306090c10110a110d150c020f031615020f0c010e0c040605030a141213090c0e0d1103010f020304030f1106070f0806030a0606081b0f09040b13082b02 67
    0x134140c10866015055648000f002800901e20000e00d00c1d0140c152617074038900d071456074003075072192140c3d8505800311420301502400c810364034441c643e44100450030b2540140009000c0e4484800740540c0000c003d420401522604d004a400c540441450b0f83c1d1284280c0d0728490381400b000b003840409550611002d414200402c0e03842503103901c000d10180c1803840350400c040003800982110856607081950b10b00010038040a000c046014a110b454a0009165103e500504002c46a140003400c02c40c84908552500c0d86e4654403444113a425540342d182402120840b44020741c440e910a40b01c0f2904104030b0403000b844c641240210000a600090a1200c91500b280c0d540210000d0b62030071040d949d64034008030703017020242d4000502160900c0f2020540c9000410b400f82d0407112103124807a90009d02c0c04024942141c8003503d5040100f000220300429899955580e100704500003082d82c0603a1903890340c840798405202910a101081024080c00108a02d40300c1000348240055082020048 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 991369406 1250 991368156 991368163
    0x40602120424150b070c05120a03121401032a0b0414030a081b07050901060302070b1609090504030512091b09040b060108040f0f05030d0e0a050705010503150306090c1011 75
    0x242c00c00444c020500fa420807501c00d04a2001d09006409043e03829200070b0b0b40c594520602104801080c2c4201a01522001e18402e0700002001d20485035216440d60311203403400c0380d160b040c2c042d14100180407100501c0800134400c005140c09915143d4440c03406c851902000d03184681144a070b00310f141c8650200325600107442d545883c0c0c1110314000c91203c203000b85011415884140c00c00713403880000884035007540c094803072140101c02003600ca0381e840001481c4a81070440710030208a5004003809803420950207a40d200348a8107005180108510110034840f0301141e10244903032203072140c000007200080d6020207034041900c09550604103a66901030724880200403504200070f4200041c00e000c62106842000c903044083d000d1000c1c1617080442d200d40c004c41c540282c440c18400784000d4075100154010046070010b000c0d03c8411304003001140c141d40b0140c11889060060f0900c40055502841303018060703074550b0018034100e40a441441050104103079101d00f44440003c0c2400c8a40707020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 991370656 1250 991369406 991369409
    0x70303110313150f1407020f0609120318061009060801021e0f1b031e0301050d12110d051c11030a11070609050a0201080f011a0304060212042415 64
    0x724004807410700c9803441400030a612080750340c840e4141039281c040450b5208400d4090305580e401d03190030b540a02316960f95014259960007183d03005c003004030021780b06040034540006d0b0550115544041c010040d40c64003800790744402c160103200e1743c01c100680c0c0034420b030401408140c00950904034510342c1086d01494150001d1040071000030403044607000c05003180d026440425409044040c2c03545201d17a6504070040d203500e41900410582811040001640c0c1250001031031031880841c40c4c3d8031062003100c10307140201407203800170010454000074400d4003508441c56403069299000801981c081780440d20a81c0240b52405450a018506140859500c090001e001240040a00c2800401841084405007450f49802241c1003000004995020301500036030710301d80e540e1100c0180715542c10b002c0c80f5850845001e00700e00031000e140d03500078603030050113040b005051884000351420351040444046400c0c51202c030111042003201c101c980003102481c0400c011031072141c3c00c401d0855515 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 991371906 1250 991370656 991370663
    0x1060312080a2a0e0f0d030c060e0a0213201c1104151b08030a0501030506091f0b06071202010506130209060a0e120a0303062303060f060d06020c03070303110313 71
    0x1909480b0040ba00d55101400000b00090841546c241ca00d04004011005210302200c2d09400c14082803500040062003101d034940003800e0801d000c0c40f44402d24024040300a0315a1348174100080c85030207541010151008401c03189115400549003c4140116160140384424011003484140582c0c4801c0e442c3d007000c01d241d8180000504090b10811840141d180d40c01040e4800000c2081180b0030a504564100c9104d401101d5050305d031212020745030440f45640c0314504000c1e00901818180700d41001c661004041d0ad047d1801416071100303141d908000c02e05c540541c1d10781040c40554208250001d07075003040e6000031420991614005a03e91092500c281d08000440220002642e2945d007185583d08444040354400e110382d19001d4042c1c2410f00c07400081c40c0519417640000703107070610407192502001740a000e00b6a81c0d4040084804406401d564024060348204000500d0500c024400d004180b4003c54980c4100e1900134103483c269807418842e40d00a00c00e0204031001e94000a810592 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 991373156 1250 991371906 991371917
    0x314010e0103020103020f0f0d0b0a050603071202031003021c020a05190608061c11010e01090305030403080f0f1611060421081309052a0d0c0201060312080a2a 70
    0x380200c5ca119800b4488e4028018034000a0000c0041140e52000304060016501881925902c008000c02800f049440c9070100d0741c400405072039071602d1b900543e03000340343d040c102d51403a880380c0200e2035801c0d80741c01e0f80303d10001821310f0500354501104440000c08040310100c40c01c2c0ea000c1e25803000005184122410f121040303010904e1503407503205031610308048108020180f085030402c04040c400211100d070208500142100700c9520400b0308205580e0007034001c5141503e10b41d03802026901c20180b40a070040c0c02d10500303403040780c22001482c000301c01010741085002e5900717085d042d12003c407885500c159000c00040084410704081b0242042403985200442003003030030148910b1240980f800040000032070085200d000e1580410f006801c20303480b008030b01c44081400118500402e00b214001e01046c400b0301d4030012075030070042d00c6050b10301c000f03c0d1a942d259034a403005009101c030200410251010406070305840d10a40382170342c5100701d80d9520004c0e40d0f008100d0f10035940c08490200308 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 991374406 1250 991373156 991373167
    0xd0b0601022e06140639060106090b030402091f05100f080105030a08070b04030c0b041110080403090506070c031b060f02010911090402030a02090c0a0314010e010302010302 76
    0x80c02440200711034400c20381c240c1201d19148148414004025003a02c00040ca482c0300410703200301444078841d4808018205a01d00a031008a6180300240300c040d084145001a10414080c009411034000c9800c08600604240d4100b44010f4200354460b002030b40c1e805800e00401c809a80c3e40120941c029081040310200240c0e100100d4002c985150400e41d0003460520b038030a00290301140280d6815003907a1100d6541e600d4904050f00d402c00c41b40040c100000606c040d40102c0c2410b03a056400a01c2410424800d202d941d480d800070081c2240c1c1500c50816900c0305440d13034204440d5450307640b03004c1d260a500740d103040d0b50301901904160050900540c40801c098003002030703000318003020759041000200c64aa04031408a08880e86000361400a0171800e002c0618600500401100e41d900c6184d01090380070220038046007000060081c1d038940314144100e03000d41c96082040d4003e00700e54160540d01c000d0741d10042d0640e620241c00c4807900d5680c00041140300403116415042d242c8c24a409a40e0b41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 991375656 1250 991374406 991374409
    0xe10020309040e100e0708030304060b011107081513051515060403110a170c01030507030f0c0201050421020709051312020307051002040b03041203150f0f0f03020d0b06 74
    0x50003614816a00103150220f1038070703102c074009240342e4581d503003000c180709200100c4030700c0303440b030015200d03070039040e801032011500185140d000784232a41410f00d072010040c1d50004c840707031511140e42d101c005160803103501080e080c8018074002c1c5e0711040707a608040c01c402456560039580e6214024286402ca03400010894101c61400c24801302040186016140d42e22400c201109628102d4460f03c600045a0000381004502e203d5410000c071540217003414680460064015081c014080d10405640e050320408141e114802d80000542c01e500004aa00d000d143c4001080d00070402418030940c501603e045035507001403100e00b55080024040b481d82c45002400c83d0356409045c00420005070098800b031056400006843c025004100302c404584600f044842284294000d50898180400c001400328116800020442d680c5180c0001d010b500c42603800c5510301103130445140c00c05000350070002c0003441009071000e0180101e404c03800a10751340c000781d00d000c80000001c054090303600006a40d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 991376906 1250 991375656 991375663
    0x180902030c150c010b0405190903050d02210612121e0a020a060b0405040f02060a091503020705070503010c0f0815060d1d150711010b060c0102091c02010e1002 70
    0x150708007600e010340041200c0100001034000d0f42840790740d58a485000102840e0900440c0c5c00786410303108620941c4080c4c90010054001c855042c0c05004040013a940802294801000c1a00c100000e00c080340d450814100c884001c0548105c1c0300e0714070f0028600085001043c580030703800411500c1c1c0da03603c1d0740c1140e01d5490004008916411240881e88030401900482c40c2d00c0654462030003000b5002401003004222001a034000d001c1a075181005030040c00d03c038000f8000c04c94a8200300e004195a850301079840c00c0505c02500c0004d07000f103042030410a04108c0034000c0e01e003c60090068109910006201c0601d501e5503404204501001c100d00451010007481e0100000d0700d002d58404000e804e1a0240445201501c0860240e411250880c00c01051404032203000d0b0b102d108054a54503011610540d01d1541000c003550b803212040140d0351030380f004161103010000090b031180e030769508026480c1d1520000585100c0c2c04444400140e0380158901001c5d001103507510714002c030140c2d040f4503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 991378156 1250 991376906 991376923
    0x1090c0e03070b0c10180212011401230d05061f1d060a090219110c0405010f1502120306010c080705060f040c32040b100c1b18090203 59
    0x8050184034000b1402400250090851030744c101d0407207161265004400045035080e0480710015241c00d003403480145000c01031320903200c41d0f8800200e11050983c108800491082e8000c012103864100246184000c0c1805801d20340b00850b12000c8002507a112940c41c0c10006021070440030b400c1111601c030081d19040c50000d0440c0c07940e8034400d13948021544400d05000c0d6482446040ca0a100181c207007614021200354481802c41e00080c820f104005440c49000181c5d50702d4a809520171000d40c984603071281724000c0c0040d400022000c3e1410052500640052101204541026965240c640b03039072411250061420300c0c1150040680c3e00300045035000b10303440204580158005d0000344003198201501460242d07120410260380d40202000701c0044034000c500741c200704288001c034488403210b10004a500500701040e141d0341d400010701c4042d502010480400c00c0844c010062001c00212000c554690709041581c0d1824950030709003080d5540c0404000984800004d421500c0500c00c1e0f20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 991379406 1250 991378156 991378159
    0x1f0507080703020f06010b041203080a020930030a08040b0402010207030b0c03160e10050313121e02010902060f0a0207080d0f020c0d17032203030504060b01110601090c0e 75
    0x151039116502d4001e450fa00d101c1c0061000c0d1050100120700c0350b070282c00f210103c4410144030080180303250750980b42d00000800503842550700b4840b1624030384032880c40c1407010031140030031902d556201c40b481144881418030224643c0c02404901900b5410510803608a5042103441640e40d0311480101c0c40d01000b9000100b29095440c1840f140c4103056000c0c50003030504460f0303a00d80d10500704085581d64951403074950301c10040089041002d005000641e0009404010315a1150064030342061810710381901c18009000c929240341089020340c4030050032961403000b40070030035290300003070f035107014000c5205c2480c080080e884000394003c0003103800400d20031054416800c8804030290007128500c190304050f002d0400004c10514024a51400580d0b01c100d140d580b45119040344541500010106000c00d8409901701d100741c5601902e83c0201403007030398082117520b8140351020075030f6054038182c0c0c10300503154802c0884000205e040d505441a86c1d4000680c0001240102c0f03042d010104a82d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 991380656 1250 991379406 991379423
    0xa020307090603120f05041206021b0309011119060f021909080f070e0703110f07150c03020711090a09082d030c0f0a030b04140708151f0507 62
    0x4040701c00350401803c807409a8000540c2d0783d1403610544d1008243c0d01200c1c00500100700600400214080100c901405043d005007495142c2c0798060b028480d00c04e400080d0750001c00c80f1500303580d00040c440c40d54000344010340030424000e40b2400c10b8255480c07008208544419009080200b0b41d41550300c0500911455920142d292802402606160141d0071890140003101103500d00c0000300704040700e44822075650705503242c8a00314010050030070b1851000a003041490b03e0040d40b400905000ca0003811006500c103040802c140844221066840a040c0103002c0755010450070807025108070000c0c0e072095a2550f443c4c071200010b08009034024145200460001041004090b0b070b1083c44800c00c540b030000d030901c400b600c116800101ca92658003541001100d0802400c0c401074143c035400d80c200810503584070360000d01904c0071031042d4641110b01d0810044560ba2003400d480c2c001320645807441465400102144140703081d1014002442215100b07254140d1041c0c0031070300e83c0c58200806 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 991381906 1250 991380656 991380659
    0x8060112180c0503120a0c150608030c030a170601020c0d020a12150c020a02090a0f060e07050903010c0810090e030705010207030c0b010501080115030b03011d010b0a090e0d110a020307 81
    0x101c0840940d003c1c0d01c4c007a1003881c14003c000c001000440303607002c01c2515a42440403e660b1802c803605100f00a150f6000d807103400000b5540401c0015115004012000e592140c80001c0000d2410440e4031881e070b406000300c41402942d91700407075500c0c03d580341030b10840b00c000740900100da28400c1070782c00508041c403030140c10014009140a065207806901000b0b105d4a800b00c00220780e5011b2040010754090700c104046110000d151740324034443d00146001203029540c95000c8008004102c444074041680001c4030341380b528007071060000d443d609040080f83da0a1020343c07807600c0180750140607242a9140c1030302c1c211410420503521180c0c0e00030025940d501a6140c01441d008020800f20760500741c402c004996076001d440140d0580d80301910034125601c0c0c90008a0252004c40c005513095503a9684014650b41c2591110300005000c80000c01c44541d041d09000411149e680040c140340c0c41c00e01404a001404644001c00306035918011410032003c021280c10500480002540362088000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 991383156 1250 991381906 991381913
    0x9201f11150a15050a0e010b03041104090309320d030c080730020a060209120f010c020c03010204030f060207150203010e06040506101e201b100806011218 68
    0x36180a881403d04000f05075840c424032001d10042d014400b28804000018402c0c41d2030f003400303154042d00078080c0448440b40c1c1d0300440c08446542c0400e4000030311154040c4915078060313207203000310030054050064004c00703a8046001c101603110002d202d05080140345090500c240513101032541c00c8140550380701e0076454a800c0b05d004079401c01c0d410301000d41503444101286070881c00b0080554000d00820b01003aa6a20001e60121040d00d9000d80841c2c881088220100220b00c1e071804014000225100f0651000e46090143c1091921985c0100418070000d0036108858070159840180503868100038034068889402c104034002c402071002c00000341c41c8454a1140e030140c4000c2d01d08200e07588510b81030118007401c00c501600480c45010002c3c8000080c41c50391a10852140340071002e01078501e1142c840d5001d5220141e0b0701d0380c4440c4096506001d850702401c4100c00c00c40780000d4004022602820341c1030700038002ca040c001c04101c0c0d265114520703082544145000102441900d900b4603 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 991384406 1250 991383156 991383161
    0x1b0d050103022803080d060b0a02060a05150f041116110f09010e04120e060a09050f030d0f35040605070e06040905041509201f11150a 59
    0x300980c4108500f2a016051001440980b5034210640081403001030964960b8011580b01e018201000f5a84140011303681c9440b001800c0076802ca0380c094150b85c100450754206960003c1d0504607005658900b41d40c40d0390340c0041c00c0c0c040c0f400980303001c01d0b0041c010408000390f0188003034000050909840482c200080102000300100d01161940f40d06040b8005000d002c510034041e0410080034000407401040300d0410700c046007001c42c034028611800070b40c04030740d254014078070140119500403000d120515007c00c00902c940b40590062004030404070004140c944010440d0707042c48254909144100307002c5502c0206200c4190141c2001941403101e40c00a1408584c2500c55030b15060100c1c400500c90096400804002000d40b0305140c2030030b2010f4020b000142048030844030347c200740c1d4a0a0038074040e5650341e80c012130800b640040083c524000d0859402c8080307114014202a8000388a6400c8400e10081c16500d8040070101c43d040c0d006240000000ca000044500d8001300085a101034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 991385656 1250 991384406 991384409
    0x10216031223100614030103110d06060f1a09060f033601050906151c020d1202071a0d1128090b0702030d0305130f0b040210050705151b0d0501 63
    0x10181c5032503440c0c0c1c0d030071304481c4a10081e5504191030410001000414401d9800c181c80d981f008001c17100c0c15080355a0803045501070341c454015401550300400c4411410702c1c0c540708114296440c1407510b5185800a00203129180001c10185404004502c0380c1c90824160820001c00c11826200180110900c14180e682c0c0030b00307581036600385000181401c0011410f10301610140c2440c8601d14078010400c40e1841e180b1041001d00c024000e008030142e590746001960480c0a074032040380400010f203000341441c030982c006401001e1964070000c240701100007200d0544600c403a0010304003a0410030040c075441455002d003c110000341c21044011a0540480080602c98403036009071075854801d15214003428201a5150700300b0b003c42e1801e0750080c0c000ca540454091070200c55001a641c4400c1e4144418800b0340d45032106a0030001141444645606580300d507003031180c01d0080640e00d250b40e03280007c19003c10a81c980300420324011402040044000c0342403c0a511840c00c8810040280400d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 991386906 1250 991385656 991385671
    0x360204150b1602131806110d1a0a081b1003020d0c0306090510030b0a180c060305011d010b03130809041a150304030206150a0e0a090c0503010216031223 67
    0xe10300050000c4014405c604a0b0007900880c849801c40640f90140101640a08000c105400304220762042c0b055100301c00c4070302c0a40e15502d07060104402071090016031a04000c3c01036120714020840280018520f40e0320305412034101860003010207045000e4011610b1028030309050001d1010403e8164110405550030340030100035640e51040e43c00f1100840c2e110140000000c003011820340d6980b03811580215031080512200c1812070396800e429115a40e0206001a07515401400716160300c02d100d040044c81d4015400295042028040080c40003500d200a2550030000d54000c05c206041139962a8000904c200b1881400380080200788112440c010722407204600640710907002c40301507a000d290598000d18443c0e8468802110381e44040c501d1a80c8121001000a0000045200d403171140413002d4000c01c040742a494981d0104185d9000184a64014400041c00c00c1d061010702001c0b64040c94424141048802010014014000d00ca001d10610304000a030100f00b800d0b106015401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 991388156 1250 991386906 991386919
    0x50304050c092701150f0317250303060b030903070510020c1c020a05030a0e0108090f2e02040f0e090312010303050a11070603360204150b1602 63
    0x26000412030102d10031203000c031021441c2003100364169041e941a0307070640204000010381d003111240c0010802e02d0b66000c4210800705510a00402c14060f40300d03661707064000c588500740011045440c130342c04481c03209260b00b810800f00e003000b818401d801c200e00070880801a140d03281804404151244d02940b41621644590210090f04001c0c503c2103038904816000504080d01542100701407401e58050007074118403542d4100f50115a00f80001e00c290300d01074070b603071913a944c240d070008d403410354001c0c01c091036604500c610860054020400c14140542c80e008a452a403045801e400909480301006055900c00300e00822150804a0340c0e07415103038549180d113140c0e950070514590380e204114441c961061060010000640120050126030000781401104e800d400015545494019403114001a8032201180c0c12036513003015140d00c5aa941c500881c8696603910006180c40305040300a00071036036403100341da8880c14000d00c000580a001d00c2140e5424105008080060b0b00250036071041e070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 991389406 1250 991388156 991388173
    0x8010905150405042d08091207090509010c110d14090307120b010807120c0515091906091208041518060305061302180409140703050a05010c030b1c060207080a05030405 74
    0x140c41030103200164406d8000340390400e42824000d08a94030b24040b20766201d0f10401143d0450781e401164030407038107070b400000d40c2056a44000c1c0600c1090080b90a41d42050500c040b8107039210b50515a4007140c0b6461036034801d60074001c40d1400e525603108040d0804035810300010044940304090480b14a4421261001c3d00c4008004010702d440368002c0035aa030f4048100818145441843c0300081500d40e1242082d0310300020078110640740040046d0880610000d02513503400160b4500a45a0390918035801002a65100110b01c1680100355600c002c0c0d08a460801d4804e4041c0100401c03c000c940a03095511035001d0050319090b95558030810090031b007401c01c818981300b59850f0001e16041c421210011800b4400107142c2c008003940c2e03c181051240803410710400c5200010351042c40104499105030a02c982121030040c9241e04050401150841543c1c500001080201d065500458100010b141200c000e10802d10b00508a03035003c02d1410710150800040c510070b500540c00e840340340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 991390656 1250 991389406 991389473
    0x70c020a080a23010b18040206160b061008070905040b030f010615020c0f0d030813051e011407140a05041d0114031216020f04050408030601021902010801090515040504 74
    0x13190055045c03a08088011295116540607004d0035070054005001d403031901070780000220000001382400d903442044e1740c06101490030199640540c00c1e589103041603140c1803e000082090b0064494544182d8482e94a411155010f006250f104c84180c8020880305a0b00c03115403101100030002380025001c1c0c0a6030000d682048054410980d1000b006091541c000340d9080e101e40300c010788502900c008050681d00020030030000000480103c0c24030454010003030020381c1c02d65841c1d4040c0c900d842103140901400341d4114040868083c0c58000e85603d1b801d00e60811607140c000c952000f841d514828800e24038900c00c40c03001d603060f1080160103c0340c545090f0b081c0f580d02c1040240510546404128600e408a45013641d83c180d50f10060283c4404101c9800003810703100181d0b01982c80010000c18010550f0f0100691014003c030b038200d041208105800180c2401d10512403281242d440c0d1000942c1d8404a040310524500014410480c0c1d003041c0c105000c023031180005c840c000340400310768800c52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 991391906 1250 991390656 991390661
    0x30c0f08060106111e07090c05070206070b062b03320a0302070c0b1216020a02040504061803080712021e09010915030f06091103070c020a080a2301 65
    0x1512400360041015074070f0100f0444d412542c1a00d480300b03500844412800c204408a4503540320504540101b202d1400c0c041d98030200c4d07078441201002d00104000b140d0050f01c6e03810541d91841d40081f2001c02c1680e4a001094403422901054076007104505801100312a044101860060003988e0300c92107880c0001e101d2100d001500c0d02822843c0244d20230b02c000360026001054130000034030303001d410143e055456a000c030816801103088100040b4207d2039002d8658202c1c0d80c4460b0810802d04038071241071003e0740345c0300c845902a02854503400002d0600c1416085034a4613130782e1114400d0607811504000702154011380e1b401000601000c00c0c02c00d55900e5000780c440300c1d13144500d0040340e0500b11211210b03e13404009003e050140e140000036080a5840d4180c40490081d2408a04080d6600c880d0045900304e801080360140341c4880c00800341c52040030381c2ea2041450400807207884072400061603400f42513000c44c6c454481d8028907010442c50b05070040300540a43d501a5100300c40364000784c213 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 991393156 1250 991391906 991391909
    0x1e050105061005030a09290f0703110a080606070b15013915060e04150204150c0f0c08030c0105010e2e05030102042301090302010e13110a09030c0f 65
    0x42c0c044c00802e040d00582d60009058074884c00010308119801b910042c802c400f5881c091403c660300804101c00b0036029440ea03170b4045818030f0100046642e0050109c41802184c040e42c080080140000f84035403101e80440d8022508044602c81602e0443c40d400149101c50b81407500060038080708030811640b500031301c400c50090142c24641c0d61000400e82004d807a501200f540c0c11203072600040040701c043e00c40c00010300502c0c800d08503c0e00c1c06003004100c10321210302c140740303031441040200040c80040c1c2c01d050808016161029480c0810b0804800030840000050f00381118071030005040c0c07200000424032407165200a102c0c80ea65584648000b8408540070303148010b2140604080100c0c040030a96501c591290b215025910355001c81d0890700b26401000c001d070030008600002038a041000c900c182000d181c914510360039980020622003842d10528019501109004c040400a401440843c0c0c0b100400c240c507241e4401004043d4a0244410b88010507182004152090464891030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 991394406 1250 991393156 991393189
    0x103060509011208070209130308010806040c060804080c1501061112040506071a16090819110d02190e0906011a0310081009060b01050a2003071e05010506 68
    0x1400e80c40e01160f0008182d0803601216803210800401c00140d451540c50743c0581c0340c00c40307820308501192901806500e0103170000b41ca140d009208001c009480315110740c007079880030b01c1e0244103a202e03072514419a014903400019103000b0441c0c0c518016161141302812941c83d5546c8061001e00101001d0b1120146902001e00020030032043c41203080c9880148001486000360000ca509601c150003290207003136420324843c2141c01e0700c81d18242d43c48607050f00905542c40152110942541040c00381c3c42494a00034800d24968030f5801c5180d40b1070507072161403500500130290700d401e034000c411018910b5000e10a074032800500411818100003600030305272190250b50354884181510100c103207420007031403807550120b01803002c03801c00801c2c8000030701c2c10326000000c80c40314020b203001016100c543d0700d07140c104142400048103c0c1d03481089800020305080c1c2c0707051444800d1075002c0c1140700b0b00d100034107485511420f03082c58a0308202c003a090746004200030083c40e200d440800c01510514801203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 991395656 1250 991394406 991394419
    0x50604031502031e04060b0f04140711030d02040602060103050d05032202060403060e1f050c070818030102210703020a050415110105190506060903030f0d0213180b01030605 76
    0xc01c28014180d00658000c01e8021145032041302e419840820b140d0216422030340a81c071208002a90300b45002443e80101c17080b1401d12450719681d01402849200400c45020041805840c0c05d035a413051040b18040410001d0035503990703442342000b070340d909401e10003240e00c0c3c8140802e8401413881801a40d02810003ca51070010303e65801c0200071000a5002c142d0f4442c0b0100000400286c8a00c0341300340400c80c0707501070701d102c0c01d80030068034201c1c00150850210700e085c0410031000b4503d00303045502c89544000c1a94441140c030362032019940040340e940d505988001a519154250401e481d003041c42c04040001c2d1a55418404505030b0160000e081e0200f00280418885800300642c504104103140c5020508000c90a4002c2d082d00c90030740d0244613091000591040c241c4072030198690010043c3d8140340b600030b649001c04d40e0b0340700b0901c2c495880400800c031559450047e4049500386160441c2d02e0038030940301c1980c0e6041711410b150305014503160645020342c1d540640101d0045501c000d100d13 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 991396906 1250 991395656 991395683
    0x10605120615090907090603240b0105091216060503010f061b0201141603030621050c0f0118090203330f010212041508090a080405010c240b030705060403 68
    0x703003e059400a45004a140101440441c040b00144a04070065002e4103540080e00314103c0c0c1c1e9005d08022405404046007050809000d5903006411600704507c1a00e50800c010b034007842c040e042c081e13103031032030311080b0b82c69480050016840000355058038007046056410b00d40e50101543d00350200550405098481100c040140d8040c50140940100740a055460482c00245920901000c9071045021030390703501c014440e1107650130341104000b0504600021080c40c0e502c2d110f641d2485000c443d4800c1104008403440d99104810203a20620401c4240d41e104e40c80c0c0c20700d0000380d0001c44800000300c0c80740e040c659070081e0040340b0b01c2c8c0642d40c0100d400108802d80d4140402c0380c1d00f030510a41584190060f101034519418024030040148140703200000d0b40032500140402c02c050100c03822030381f0004020000c2012102160f0403901d0900344003000040c036280591900401c0d40c2600c3c403246100c0321448441105403c000c80001048081d60f056075200e500300032060050b80405000d50000800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 991398156 1250 991396906 991396909
    0xe040c060206090304150e0d062f09010210020c150f0405060f04030503060112110a0c06060b040f180f020d0b010207060504270b1c1712070309021f02010605120615 72
    0x1f01c94090140181101c800841c564a92800b40d59010b00d04070075103c0c040728500009490400040c00550000c603220703151101070b80000750345140c0c051018050590004030b852402d401002503170712543c0f2070041e01e500b41c9040c1d1050112290110f5003950140910303000242591280004a0f11496040c1c41d01c2d421a1220300c0110b0301d070b8001c5440c45a905540e01030044609904030094910322803203a0b035201942480b0714000003618050380c400420b000090000784544594404407400752214041e40808066584500030081e00124454810481c8006418040304400f600311040c0031a0130303001c0304c0c40700c1e0b5035250480c0c1c207200e075129940803200c42c1069000342c0902000c00d140c020004007000b05440c50240001107030700380451206041210400b4a00b81000b640001c50b14680c01c0703003d103081c18182c0d0f0b00e268101100006214100b0103649070800411541c541174aa8403050b80010381460380042c885019000300601d0050b148030f45210410340160040c00104140704042c00d0884c4d0b13440128450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 991399406 1250 991398156 991398167
    0x402010c08070221030c0708070b090d06140f01080f0c030c04020d20070c15020a2415060e031911060403080c1f020c071404060e040c06020609030415 66
    0x40807a48400407042052007402c07000c254014244e54440a076a407000c1150659181c5145075002e0401a04060000c110607440c40069800000b010707126100750300480c1c07034a10003c0c10400740c103d1903055100240452108031810940c142c03084032080b2200442030300080d81c0c2d1040130b00d07801c03941644003420b40d440b1070500740c0140c0b54180e078640e070120b00c085002c0080a81c040d06004c004c0140480441c8100a100e0450041d000500c1c65070030b440914445068025265004808050f00580e81441c3d0b00b0b5140581040041d100d00ca045010050046041c440805041d814452440042c00b030034615440d62030041000010403130100aa02e081e5205680c1e0b000c211034042c4070346a84a4000e100010104070200010460060a54050407603080c80c0d030010b901d0621148074003e2003034410b201018100e080012660b00342d810391803104440d9540c40c6d0001c0d0203020590010a040700300c0c0818841046000703400c000a4403466002d48042e81d80d12041c60782d686c042d512400045035540170410a0719070044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 991400656 1250 991399406 991399417
    0x109240906090807030801050109060c062a030b100e06120a0605061201030606060906020604150f020d02070b0a090b0c090114161203061802160f12170402010c08 71
    0x646010800555a407200c90468100000c00d594050b0001038a50825038070215081c0584400d0034000800c0e801d0103c0148815460300004100ca9562445400750749101928200b41c540c1e5001500c070302c1c07e8800e030001c014104d140c1040b40502e03202e05032083c0c464010a01c02000450240100381420200e4a05404403500034094003160f43d038440021900c0d41750140200b0b011305c80503169107819495803601c40c0c21940c069002d1410082d070030031b040c85000d0f0f0109401b60090340240740103040b400c01100f41401070075003008405010740700191600b900c0100d074014024050041e0b4400340305555402c0e115080c0c0c1c49500004008190002c00075070172011000140140740c1042c908403c1c2c1104035003c240095001400341700da0310000280044c200500307000e090300d052686260502401749080c031802c1c0001c0f041021050030607008591089080c21030042d907060503821044400114030541003400124401d201c4400002d03840380314441400a55038945409036606a44241104540b500c031401c1c00d4020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 991401906 1250 991400656 991400723
    0xa0809281a0408190804171e0409060f0e091e0111031305060601021f090f0605180601090207020f0d06020d050403050415182105030f09040e0109 64
    0x3403407162030742a000416541c425481450800d94680d400b0550101032011300c0c515004102c012400c01c000a1090105004140d892402e055154903030452000204050940d400c8001480424001070b10038450b000b00040f121a0000d80980b10b0f101c142c00b1180726822205141e4682c4014200c4025220703540c8840b40c1c000e46c0b1400003c500c00d5a041c1c0d211940d01c00d4a88814410920382e9401c00c1c060309004180d0000024001030190305040365481008008928210340710a03616010f139418008901492040c1c2c0f0350000d0100024581040b811440c101b4428240149104d85000810440c000c0d2003221100d98004218403030395080c18003040113000c4012800c82d507158081c815407240c0310040c010340b40680e100f034540703948490031b017064200344801c16242d817401c000c2e004500d0b2070b403130341001c94020545114440b1201510ba034104a10101040580020001d00c80010074903554880c02018001c083d50443e001c0c1305580c01020b2440c02c0c0d900c0100c021b0064541c0380005600780492810300307001c00c0c95 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 991403156 1250 991401906 991401923
    0xd0516050d120807050c1f0c03021218071a0c0105010512030301030b100b0c0c0f01090f090f090206130e1006021b0102210d060801140a090221030a080928 68
    0x21926500741018101c040c240007020820011f4141c0c0540100040c0303071054902141000c2800e08043e00762040601540344a101da104c4690800b1018068540031b0b00420920035a0303035404005540135503000c100c50761003a5207054000704551030414806101010540001c0d800c3d80d08640704c1c2100c6250141040310903000034200000c1016a0700083e000d2502c480c07018084030f08a8509016400c10f80e9124241001224003080c0000342c0d00c07006400c16219103820006440000c2544003004007202180a94404000724101c4009042d010681c0183c0790340c3d005440880e100c1b0b03622880012070901440c00580c100359000d4000b56407903034110b815801c05104444500800c5d00c5599100005040f810001490000e01005524040d0080d00003e043c0d1400030080018032014241035103001038480390846032113400600a6590340380c2d591403140c010345000d00e04e01c0518964a5a2507004150300404104070341d00161252001181e40d06014116500494007038600d00800e807410003c1c00c0d07049400720f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 991404406 1250 991403156 991403167
    0x151d060c0a260702011518020c010207080c0321070f110a1428080a0c06110a030f0f1505100c05010203010807081c0f05180d0516050d12080705 63
    0x2007465540c03010b000c001c44181c03003036410105002070940e003c005d0040440d8144020401812511038504a001503881000680351109141114007911846030040c1038248080f911074040c2c4008001011848144000207880b03d03801c880c08031801c081210f185011a070600d10180d0350a006c7d0140d8100c031201c00080d10f500b072100303944000346000e507011051038580c0820401600c2008620116a01e12041020105410003641d501c46891141c0c1d844a0104201c0e20301010400c406600304c616200d031208039003600c824050303400500030308121231149881c071305000c8035002502951246911484030b490f110400305042c01c0038840c1e01525200c0c02810411179400c20001702d00c0a1000d58003911420340500500c4d403621005503d02210940c0c2c1540b2200385031074019a09130000c406c840d154070b0500f40300380c980c0c01f4220f0f04102d04040f4408150407140c121281000c0220128040d048007250310b85500c0025103c0b41400700300240180018401c1480d00d8800f28440d000f1041035510810b680350240c9000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 991405656 1250 991404406 991404437
    0x80901110319090615080111280207120605191406040e030c010e150907060504090504030e100207030201090801020702150c030408190606230d03140403151d060c0a 72
    0x1da99000720404004502001071051b01c41c2030044881885400d030381d10b81040502c0c1803146250b082c070520808466900410b00e03012900a010020061005185140001100381010000303800c0454035a040c442802081c03612504d1540f05070600f5448200d0849402d64511090000401c9900380303480701c5202c00d101161b448031090150192100d000b8000e0b01a00316610241049141c024003138040c0c9401038101440744a6201041c2c0c0c0403901417050100780c0741c94070b040c1964a24440a0129040340c1070740c0201010540004500f01101c0c07003030340c94801d0580d84580150803401911030003548035180300703c80390b01d155042c1d0150541c0d94505040da850940d440200702e02c0d000072b0700c0380b00002d004000d1010061220512a00340100f400510100b11034824005040f000741210740081e105040264a040034075108031038000e019140d1000c0340b07503a01e80300e0a20380c00a43c242c00e61648201d050030844507180404403c0034940340c2d1079100418032602d44501741c1c01c2c83e070005c1c601c8604104110b16100c021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 991406906 1250 991405656 991405661
    0x1109011d060c01020403021f0c17040f06110d020c010c0209040219230108060108010506031008250b070206040b0319090809090906040312270c05010809011103190906 73
    0x102c081c00320005a80307500c0d510502c000f601400301c01d220f14141f125641c100703c540110034001240d6005c88a2070200c0c0008030401e14502503504548000f40407013001249036600080e00c1581e580700e840885070203401c1114101e0b555482d141e60a40081c0e01c481c4c0007401401c00034005904148020440c036a500c003e4035210400d003195610220700b81e540c049611151848442c0b000c02082d8003881c061415240c02c0001134840003042c40703041e000d0700c0300000181781c107000c07114200003500c072900541c3c001c00303088002501014078070108602149024000081d001e0b160000322018158041c040300d05180c41d158000c5141d80000300110394000d400805452820080e1140da65000e10811907580c458807a0401e00410404c02482c0450700e602a8080c007010030b40100903520110f94a1034041280202d0805c08051600c80c0807076054152828940070040051b001c00007000d03120b0aa0302c8004c2590b0701751809090301c00901114004020410104803290241c0950000b1104000c00100d941041991203008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 991408156 1250 991406906 991406917
    0x30203030406052b0c081003110105090f040603060b0109091a1203040807090504110910031101020f070311030609030301061b0809061308061b1803011113181109011d06 74
    0x2034013540d4a1807802c5c483d40050304182c0103185102442c90320b5045171381710704e002d216000015060041c041000354113681c40c0d101616400700f0290042c058140c3e44d103400d00180c44101c442601144180e8000700e04000d1611032a400c140c01c0440c210030514500c424006106424910360078507000820010030304038010004a0001c000000c8005503a150038106480c841c034030f0b10201482092028240210305000040c2c42050f250030030481442400340000617450002440380301c07201406a00e0000081c051070300518800c1000c143d09545c6681c4c1c0704d014007a20380c8001d0085002254441c2c040c00b041c3e54903601c045000501c111081407400342c0b03000004170a60004450180c40f86003101050084c80800e100c8250448201e100211074240c00490002c82030043c201328200c044070035003445000da134007500700d90f4501e2100c140c400c0c0c2d1641005500b10280740b00c1d00444028001d030403240540d1502c9442804504c00300720360140e003401003050044680300c1c1d410480da101c0c464074900c400700c00e070b903000e00901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 991409406 1250 991408156 991408237
    0xb03010b03070311090303031603020d0c03091203020405180603070b030f090c030c060904020c10020703110d1815030e1b040f0203040305120405070e040c0303021603020303040605 79
    0x203840780b07440c1200400b5540b4228941054a101384111040c03602d0000550360000c0310704050200402000d07408800a00400e1070742c5200710301b0900d518003416019405003003903034021082c0320003e10901000303400764411441402d8020340311a02000c0240380d40303807480e50044002021390710090341e2740864000381e800542c1e000625000400c03d10100c1d41040080080500d01607000e13020013031031000014228001d00da07600703004680014070409201810300081c16100b8071030100b1502e464603401d00400c942035100c402c40d118420540c8000e9024021200003802c0c070009842c0c0141642800b0307540707008450440c0c103c4249a11250000c8a031740c0244002c0d280001840c0b50090320340d100400f08419160712440c9403c1e10792040043c4404268083c00700e81c1c4100c111040285a52910700d03115103480c1c501c1e807041c0e0410100d0001e00040050800410003140d000303500701c9101403c4d00c400b1079a85120761100075030690041108014442c01000981101c40349819044007010703007d00c0103a581d440c0702c00303c80c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 991410656 1250 991409406 991409429
    0xe06070e030c040501062a0503220905040f0618050d080a0c05040f1e0819020406080d0c122001091a04080a18090e0607021e03070b0403090b0301 64
    0x80e0142410000b191408900302d0b070038421549402005407068111b031180a048030403007071410340c0c00c030480203000c3c201981c000100c83e503903001c1343c41641c002c0c21030100b10b0115004d403c8000810003a81d008260141c0e4215003886d10201040c0d8810380200f404481100007802e55114000202d881071245040d040c1c480d0315a034407a0300c1c0c0780106d08111001d680c03ca600740301086c44144a640040240d403070070380f40a100c100710340100442424511100ca0741c021000c92203045030f00040200076104a695a42c400d4509000c2c4a4481ea1a607450381501d84000c40000ca8501350750000c40c01980768a1100e0807542001c000c0c50201800c0002280c01d0000c40351026034441c85607504003e03547c242d074a00e10b074050401d0450782c241603550a40c41e20038030384040700300401d840d03100075600b403014060301c010000e4040400c004203110161907200c42d02220f040c0301600440304d0403400418680038035188104400c010310300e000e4060350f800322825001740c001c0e810404550f0000c1424241b442c001d5000e4020013490 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 991411906 1250 991410656 991410677
    0x222102060903070c0b07051204080313050a050f090c3a05010f0e090328090503070b04030b150405100305010e0c0918012007060501170303190e0607 65
    0x603290080c0640040215401005003001082802021205481102c06050350310385e000e04000c1d1809645400c0c000c0301a10026002402c2c1c0d40000040070050b001802c5013890030703034031070400101110354421550003400c0070b00700c1e070f041c1d01d40382481c40d5102b00c0300402d182c100501d800018003408624108142140e6003406449510245041c0c00d150240d41c0c01024001d070340c10300440c034041403900d00c11304004030552404659155414019102451b40700741c884104140030441089058621201000104d24045030203d12818085641000d40c1d02c00c8800c41d1801c0c0c5195648445001f000340350400340c50340c00900b181d1a550310b000f41d50244042d90540707900035003103081c032608440307158909043c10f0f400039400d58487d440300941e680d409005081c08002c0e100c0d1000d5620b0140c5160a03501d011148182d41c005c490120030f001a00c00c060180c2003c02c1280c0c0c032001e0000707800182c80500000c2e5481030001800328136018100e00e58461000002007240e00fa42e020395442c200050340c124000c90f4407c200d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 991413156 1250 991411906 991411973
    0x605130c08010204120b09030706050c040617010509070c080c2b021504140118060507111b0d0c0b0309010219051207030509071805090f0f0622 63
    0x8080000c0d10780c1d034008601d01490b010000500800701c0000038210201000056001101803043d610070607001400ac1c042489c0100c1c0f00c0c50303194800d010300b1021400b29240c207c98441425401816180040c222850320f4403010800d49403008002801c81e2620f50070005d05540050500c4a0600c2464490b0b039801c40710b41040704402c3c95100b0708240021075000710181c54075094003140e030316000340e08102d942a0703100203640c0386409440c1031001180010682400d84040022540c005c03486100b03240c2c7d82c070680340400010241c46130b04503144024106244a01c4003014a407a882085000348110441c00b541d50741c95200c80102d41040b40c000074141d44c0401c4401c90301801c00d6104040c000c0500d041c03031030310440708402000184044d0000e02050790f684000f41c0483c10030045400500b07412880141c1d226100f14060303014001c01ca4600e051030162000a11100c000024400101c00340d00024141503a00c018415001c814071103010742130208050b003039101160000400800090310307542c01c178030304601501 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 991414406 1250 991413156 991413173
    0x60516201e07081c0e0402090a1203180504060506030a020f040f030503090315040b1302040b1e121504110d02100201020901082802070f08030f090709060b0406051303060513 76
    0x144180036030f00c402003000d0541e0740310151060640317044900603203a0302904041421103455402c03941c020221500c055040c16008a1210040d096040108009a03140c00602065070814446c0c142c02c460306001140f480301385070300600013005c8034000c680c0c2004c0e07841421006040130741d44140d95036000055159003506080c401d0744071a4100d450164510304040d41d8220769050300070306000c402c23030039003c03648219900d68000340c940c140010040710342c1d584204004444001e00c0540e4a1081c2c080f07030402124100080b840074203424901100100725521a01d0f850104840610f060b42e005444101e4a001070742d8400110755421507680c001071700d0350324100c0050700035400901900305468000320b4244000c4c540c80074203200c844083c5005600c81c050742c0740440100346003070720081000c880442001032421106c14020300c0b6509100c100c4026070742d9201400d08585642c001c042c0749050420080c40440d0248000340070032403401c2c0d401e500719962a1a070600312441a01c20485c209d00854a0209024594 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 991415656 1250 991414406 991414423
    0x3108010e0d1d0927030f0406050d0b040518061003031e03060b0f190e0307050d05120304061e110912210c160b03010311060403051207060516201e0708 66
    0x13401146070005004020001e80a90f10409042000000e04c51002107007a03040205034500141003031003541025980c06410000a9400035504c0c40345000080c000b00e4648001001c40b5010707100c5051144c000c0b650001440503507207200d014142c85080010f10314020b94020b01914018162644e16500c03c1d031020611828880c82200070003174411010f800c640e0340824200e04440c0c04503507440c0505402e140082c20460900307400c2d09000d02c04010003082c050644c00ca407441189022408060102c0c0c072419408403034001c00c0c0e004110b00240a151b900e03052110141d4201040c210880d4951203a02040c2070203803902020054520002191000004804000150707452440d912006080e90030700e0442c50b032030b010503c0b020700b500c466401d2a03140e949580046070f01540e0403005652016041c60b085699035484548120342c2130345040c0000c2c091480c07503541d0b10f04200306552801a403840c034003851008120303510740c00581c50050348000312480049512100780781c1c8406010b00111407600c0c41c82c0703043c074840 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 991416906 1250 991415656 991415731
    0x2010c12091208190e0304030506011a0729040501140610140a051e04080c060304080304030f030b040c020106150809060705030c3108010e0d1d09 64
    0x1401c040c440000c21031000c2d02100119854594419900d41034072130150300034085074203200c81c5003400070050b80502200510589020b034003194060f90340c90001000620241d1001c42d032840c0140240030003d80b60100c5003110720014210b41c0a000c41359131030043c001e00d0680b81150240c2d0740e200000d20480c503c480c02580706504903041101040103500241c54143c00c2400701c10030100000b04440e505002e98240c2c2c902c048607064034060301c9020056480160311a0040004d20b02c1140c1c400704141c0b0b084401c6910442d4030510590468560f03680903103000e034140e03e89405042d03d4981c40301d156200d0344500d0301020a558000301e16107281c40c2c0c101c0d104000317541c502020444000100300e1054000912550007041b24500240c0e00d0755500705894150280703140c41c405400744141160614003001c1030350600d0301e81c00c05803c0051a581c5000500700d5101590340c40640e0030019040c84107074000d41c540111f0400c043c403100b0403801c03c180045c02001c412a82e11001810700010203c01d0b12141e12020140e465 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 991418156 1250 991416906 991416911
    0x171201090f1b17101d0103050601050303040b0d0c02250303081f03021519030e011d1906060905010f06020d09230103090c09021c140f180d02010c12 65
    0x5103941e00420303100c0d90001d01c038521651107020880c00c01d0403510b104002d02c1c02e00b10004603e0100d500b2516105c0d401e110549080c0300304800481d007480d001c41114100c0340d1207501c26240c80000c0741540007500303a90907207800f9401540d0b11404043c02002859480510440302104428110315000e400203402424030401090343c0506032400f44100b4a4000581c3d404480c02d00040750030102d0b004480c4200721449040c27280031a1400b2001d501504031560a00b44035000b40701d890500420038040c0c00c0100028003842d4441c0221421400b2001d4403108118017949011a4440d216610f160036140280c0c02018083d40100082044940c14428000700603681d05c0d05c86c0c501031a0041c200402d8180e00030a02902c004105240550b0f8045e601c00d180050340095101405a550742030440250088010a035440c050002d10401c000028842e540014103c3c92081d8503544508005c4181150010240d2501500403e042d07241c58a082021800d883e81c16400462403106d0086d0041c410b0310301c840c403e2111030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 991419406 1250 991418156 991418201
    0x30c10020f07180c2309031f05040303050105010507170318031204050c011b03082e050102070b070309090c0c0506010b071b0b0d05100f080f01050106050a020703171201090f 76
    0xb0171003403032014034508500e40340c0c66444a000203400c2c84c204450a1200d0001908502034015503900136a215034005c0d14200000ea90751001915070340b09504000b444820030043d100c0c001c02200001e982c000405111442c2d0030540401168a1a4041c1c07103034552010f2610104410448100b000b6034000d0428a044180110440708040160449241c024180041d0b28001044030100b200d0328201140009c090040014011010440b410401e000303450050081035400300701801d80e14201c400c5264540e0b074044010b890105140000c0a41016110403c24641800c0010a40c00c000040c0a4051898103590390103040c6451a800b0000b0703031340344c00050010802044191614429281321200a000104090347e41c902201c4828815801c17030410103045283c00300360a00d0019810011450300002000246d8171141c0503511401510314800c0140d02c00c100074000240640701540342d02100c1410f07181045460b40c03020040c060700740c102d074200d0b55076102c1419880800c2d02030840b051320200d410b001d01c0c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 991420656 1250 991419406 991419437
    0x311011a0109031e0c0b190e0f04090c080f0d090911030a0518010e0102040302011704231204181b0905010e15070303020306090f06030c10020f07180c 66
    0x1441d80e8407010304102c0140d031041e03000e80e00d0a0010350744180c0c032401179600c2c2c1c1c0e2120b56821132a00003030002c0152860303051546450314080c0724004681c07040103054068148034401040040d00034414220340d038000d03905d00054151000c2004283c0824194043c088100c03500c40020300c80211540102c00b400e04080804041e02510422281c200041c55004a00c030359400302000d01c0700ca5034660b61380f40380d07180c0032203003001c100706601402c10749100341e81d0359940079942d92560707184c2c4200b500c0c040c0c03240c2040001e010124903021410030040030108140e4110001f0041725142681041c0d000c05c070306640385804900c04540d54450072002604810302e0900202d104000140381e940c090181c0d0341840210110000e40d55550b01070291062807440709250749260501e40103010b50402d9074450b0142c0f050002240403569120a103c3c07103440d0140041c04081d603140100f048403900d120300541580030700800201e9980e030910415001d0410032120901000304102141c00f15100e070b8600300100410413002900d107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 991421906 1250 991420656 991420667
    0x3040807080a0203090d060e0c010c11062107030506100c0b01170109050102040b091c031e09080a14070f05010806060705030c072705060d0b1b070311011a01 69
    0xd10740041c400e40d25204200e90a0b0310703520900c54042c2e409000a41c0300001c001607500321242000504055a0708000b01c5001034030101c0e1885401002820307071003c0207000f0701b401b1018011020995140d0040d8120400d0460f10008054503d00e000a4441c0c0402c041414010300303c11700505146807541442ca281e80f03411307420b400d041c09035880b08000f400b09203100e100c094101c03190094101d0001c42d5a07698580d5a07802c90382c008020700f03004058003000f4900040d414400c0e5402e65070540c81d14a5400c0c0e8842c025118030301440440020300c1010200401c2d14401003040c40c8a0900c1044081254856501e00900d002142e502a10782c1c500c00000038021a41e0101c940c68120106491b0141c8900c4140740003030850103003108240817481681000260301c0100c1c090741448100ea040302e00b034148140e10410051300c00032500d0b42d42281507840c0c41c60029040018003076210359040c048004e07400800900c4c03611176000205c1a000a800c64000b5464003001b0311030720312002554203403000d5112034000041c2c030303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 991423156 1250 991421906 991421917
    0xc0e010e04020d0f0809120c030106140612040303061512270311030d05070503070e19050f0a0b0c01020903010b0f0901060f1e11060f01060917120c03031b030408 71
    0x41c01013080c00d07070020021118192520842c1c020300b00c555650010103860750f58065003a129202c0c0d801c0c01c100013001d01070004041401c0001030420341c0740c1964502403140c032201c050801c904056517141c000070503440c043c40c0052801200d540c1c201200c82e0240d4008181d6880311070604065004184070a18a40e20205509540d0750508108188803020f203c0142580500701c5400059030800d01084401c0340d11000441c410700040c2c41e0f24400d9410f2030240065203103009100700ca480b505d03910510103440c01086111810400604055059440d100e500381c00303802903807503000c96130740218144040745401e02800107252003d80d0f40712404081407000842c60030062042c4000d104044c00e824403c80e124088100800c602684408801c00c0c11101c001d141d4280815050b00900840340030400c05901c038640c181c100c03400e9903101c118440c00c00b6810a00c0c0b211a404c120740610400d0315a494081c0801c1c0035181d40f0f12400040c40d100d252001c45041510b81140e6400f030030760001c10411001588100c103880 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 991424406 1250 991423156 991423163
    0xb060307120e030c1f09050303010b090d0c0b1809061f02070905040812010608091f180609060b101202091519021e100f0b09040c0e010e04020d 63
    0x181c81551200d20304010126048058002d0200142014540600280303224442528031803c8500818040b0040d0484070301c50b8008201e40c00800c010400d80c0100c0b00138290583c4010002d0044400c00c1c2d07030350700110000d070f840140c820102207805c0021070810f41e00d4005209056894401c0c51400000140c24103000c1300c43d80c1522010a43d420703040a20801292018000708001004241444e08060300710750000c11801c01c2c00000400040f4125110300d1145025640140c0104401c070f01440820b40101702006681004661300c0c02d0030228414075410f100440d500810000410140d00d04000c803d488440c980540656455100d1203d1700e54840e101f0320010030304080040e110000368000030355075201040700e02c0152601081e4000d07407212170300304102e640c00c803074080f1802c0101d11208400c40b40e0341d20a09400030f0300981423030b442d581c46d141c2043c0c2d508060044c00062800e00d60000941d0300b84240c40c00e0700c3c944000d0b2014003511002d0b514003400b5000908000c0d03400c0ca0294000303800340e585800000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 991425656 1250 991424406 991424417
    0x1302010e063924070c03050d0f0501090b0103140a02030a0605090103050d080702190314040e0c07050d020a0b06040b0406030210020f0c19170307050724030b060307 72
    0xc0c00c0502040210880001454881a2107280e0394141411034000403601c0b21240d005614960705880e0000c000007040ca5158003155505585014041d034105080d0481501400010046514814018828a2507408854170001499410500140c04030744518034424181071400003a5a580c2000c034528942c410724044000d603903950345540c3c2d01d02520180e40034540002081380040b0400c080454901600a4540e4072950035544a44080781c5e50114088000754084100d0200e01c0442e200d200307950300c0c1a6600c212a86000d40e0b80c89211888501110311401000e404140700003001401e110035503400010b84003c1000404039100d684030400c001e080288a1a605e942003481a105e507007240c4002e40d001442d105000843c00000307500c0c0c0b0f0100b02010341d50300464101148070701e45881c1d100c0c04105085071140c00d0909140602c64001c0010f0080301d22480144150300000314108003010140c1403800034541310780a42030b278107055902d0168581c0289030601c6031480c0b05850700d8007500d40c01181807808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 991426906 1250 991425656 991425667
    0x30f0606110c040204240311130302010315050a18020c07080309090a0c091716090501051203070f020103020309120a0c0b13051203060a0902030c031b130302010e0f03241302010e06 79
    0xa1300100b0b0703002008c035030302c1c0e40102d060840003580250040c201c0c0e00070b807030a0291480503680c140c002c0b02c080c000c040d400040b105081c0074040d0540c00440c00c21480c0740c1b0061404801c540e030702e0304c2c180e0b19a0020515034400503a2070200d0800d051819004401060144020034541c00050b00c0d40025028141c0ea4a102941080c058401088544030035030135040c40d882003076140d40c4004c01801c801d01070503000f11034840d46a51040000000c9424054006080c0303007c28a0aa004501952025014885a10880c00b042c1e440c0307840705008110107070f20750f198464026080d19101d1400000104040c8250300c20070308000100e800032444151620b0a070400940d02e950ba100015001c1c002a001514224408410002e40010010082d402088444412080c48009005070082c9100700c520010682c00700d118104010f5000e480c20b134a110704010603c001c14101540480c2c50020804012a544610030700100000341c008030075a030b0170881107025903140c40c806800180000e030b05c041d01980281c00c00a403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 991428156 1250 991426906 991426979
    0x604032004020d02030f070201150e041e120203070203070e07020a0f0311031614011509050a09020603040f061a0d03050f070203031606060b1810030f0606110c040204 73
    0x125503c0c00b802d2142103481c0c0c2002110307142c118504a0742240550b192089000710110742100c05021036410f40714013034407035a036943c80c0c580900c1c200c001115500355600700b110014804002d6110b5564081d4025502d519030b03401011b240840991102030544610750078000c0c480c1c0d0204180740c080b0382000d403000c20b0f29a245000c40b8800418030050140d07010210710300000d0300c041810404814041c16005240501d001c040900700d403058161300d040c0c4540903a08201183d182d401c1070750303c0381c2c04100004142d10a41c021810039801110102d401481e005940c0d800c12026100c1c1c548106495182c9440001c8060b010a202c0c10760076402900b80300020511164800b4040c003110b000380d50103401e40f40c40346003030300048441410381002161118100702e008a5071340341e0308065034811040d2011502121401400340f0218480115a4504040d108c554000341d5110a0080ca0010700c0d00740d59961516110182850a00d9503202c20301e0710850040104002d0007070319041c007580b4050000702003180c8490b01034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 991429406 1250 991428156 991428161
    0xf11010c0611040513021206130906140f1b0d0b0d0f050a140105040519020d0b25031119120903030b0a0503012a0e0303030907140604032004 62
    0x1640109282d0030b00084000710300104010704210b81042d40d4008070001c0c0240c81c6000d90103001c9a104103069680c0000b40a458240c1e04281c4c140164040000d588145440f16015a03d43e046c1050750303024580d00f4090024010401643e03c00724407181130314080327010040542148110540850400c2d2200061500340da00c1c3d061b40004a64010b00c0301e4001201c03031a146454264000081c3c03204504400309078000c0d0818040c03240300b00d9100b406001030210400b000c9900460103035090380c00100d0102c030103000030109901540150489202884071403000035038030118004040d400000c05007012550f6400341d0350303403083c0ca0800042d114900704545001c04120340c0e5246561442207406d080c00320300700c20301d90182d121007504501078400c61001611442030509a569100c040011072105951748003200011103811441d5600c1031500070708c01c0d000700000030315580050340c08102d2074008000c00c00491110034102900d95005641550a01d071441e1655030b8041c034074000f01002d1200351014020582d0f981d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 991430656 1250 991429406 991429427
    0x70e090f1801060b160309080f07150504260d1d040e0c03030d0902100e0105070308090c03030c060907050909120a0341241201020a0c031b0f1101 64
    0x444c80d903512442c1c04400601c04091442c0300b0740c0420204040480c080f800490388500b0300380c140d0700030f08210380707050041c45800c10f4400341101040360503c00418030480503d0000e98115101d5080f6400c401c050045c181041410012942807200080380003800449000c44240c07080d1040710002080412103140030b06141d886980d03194180070000f440441540f0540c80000d000d402515042e081d850a041c0035100340e035903008290301007501071001400091080e082c2d154080d1061090300c025440507004039103140c12005242031680c000c20101b004000c02048104000d2800302c4070000542000e60040382c6844404041043d0754400140d110f02ea00e021703800042401e00344000d114807402c1e00002400515402c0584a00100c0140c4504c82c40b84210b0500207002d0f00241c0380d40c840c3d010000c42110aa8604801c0301c41c0c110304e10400c1c042c5642020710191a0316001d41d00e07000440c2042c0e207002803180500e011300c2e030342645010030900045840c02440b249440d600c07a4080d02d4101d0039200588501150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 991431906 1250 991430656 991430669
    0x20301020d050c040f0f060e06070f05030310081b060702100207050603010905041e020a1e0e010b03010816061e0314040c090b04060e07081b030f070e090f180106 71
    0x1d0400340042008031000400446452405007807071035460b0219240c030aa450310402c0002a2350032407440c1945813080041001d1485410301141721580b03075680c5030441d0422104900c24019208082140400030700007400c0e00c0702c0c000c008076444030b806000680340307005612000c0d0041302400c144105060007008280003078503000b041d06440750ba441c0141c0020f0034007181c0c2282d1b659246d01c0c00c0005c86854030300007420950f0003000c800c00c5505003411143e02c96020036100051002541000945512103546a406483c0c504106540c96041c0000c452502c244001e8003829805c0b81c5004200055000509074000d40580707410120385c0880680803006002c2440f061400c003201d06060004000b8503140c014202c0d18400018000524407104100c11034003a84100080089040c0002d1540c603c0303080c0712035010b046a04950700500580354001130b150802c070b5015203000d082c502480241600061400412070080700c00340782c1450403c4003514458805402d48040742160782044102071303002c0d00901c018100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 991433156 1250 991431906 991431911
    0x5071205030d0501080d0905100e06160b04050601030201021c140d0f020d0c020712080405091e091b060f0a4a0a030203120306010207090e03093307020301020d 70
    0x84030310169440c1d4070208000004240254000a940d007011241361402c48a079403150801c90303104c0c404bc4502e503841407000703011200c60600703a00005a541c4e42d0740c07401280907a005051540c114400a440e0414000c4607964440c81c4004400c0945e501000c51251400810031103a250b07002c444881d8007401281102e1850540040b072108040e01081c2d2001c20401165800c65121969a100399000814203030005000080100301c00e014906200354095084a038000e5800030041c0700e03409040174407000b0740341074520b504290120090b003942e0400704100403108984c0b4620b00200ea01c010801c610036111484144081c0c074030364030703106400f80103840e040f8040100e001c0c80145580400385145116030b185070442c0400b91124a1140c18580310010980c0c0e4060024581c14200119a142d5900700804240c1144194a00418002c07468080da0000e41e14800085483d04200c1c030801c8007c4032a900c80100401200c1d64054408407111014501002c1c011034640d070314043c5002090292241d292032301c00050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 991434406 1250 991433156 991433159
    0x90f010905061503070b07320a17040e01150801061b060c0c06020307050405090c07020307051306050307060f3f061d060307080313140d050109080d060501030905071205030d0501 78
    0x211981000504003400400000101102340310056542d410010140b94082c81c000780005000c651a4032603510000991401c0a5942440300c400315400d03000a61b080840801c410b07400760300130301d20501520046c100405800851004001c03085101c0b140a0440c54a40d090010b44034007981c04851342c0354100000390b5803407904241c0036085611511405028142c0c210008143e040840107560a10782c0c000d0140c540c10303103000100b002111010340c0b41000641c1c0d40400099568042108000910300c07030712114600102103c0180c0f0341c4034200305c00702c00040e1000d090815581400303100f01010002070203044803005034034070984c01000740d60420030102d00003800c0741800501c07400c03c07248119421012500a1611044015224000c41c400c1d4035040961402c14080c031100803004118424010b04110902c14445d20743d6802d60341e00c010242e8200d080090745008031040e5004038000340200b82814000014140c0e2071540d180b4061144400402800300c060040160074011652600c2100d9014441c95 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 991435656 1250 991434406 991434413
    0x140402090c2a0d021f020903100c0c021c0c0509070318050105181501060c020d0803070807030f0606081302120a0c06022a120102040914090f010905061503070b07 71
    0x1540460305500c040e10942105042261001482c2c003401008050317a40c880b0b80f102801c01002c1d40060004a515020b25107030340c4008843da20402495908560b00c11840010900510840250714801c02c1302c41c1128504080100308966002800c441c015038041040d691150300407401001400e01e503403c80c01d0020754820a01005401c1180140007980d41c20002280e4a2402d0b50360f0340010006400c500c41c18801049458000c001180c86035001518400c0d108400740d40e941c840350720498104000c10909403e00c104241d01d481390301c403074490507074082041d1410920040c0403803400038018080803801070032060464603404052200c4a5444080324824405850a00403540b0f00e409680c0c0140b00e040c0b4000460190340d400f1140180e00b1000780904400180d082c80b050701c0703051038090510340d000c0100052041580c0705515128418400d9459103091402105050812401c0d151105030704195041c00420404034040b80c0007075600c0d0708142c85000e00004030b810210580e0240b909108049401c4090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 991436906 1250 991435656 991435717
    0x2010b0d110306060306060a0e04020a0b0403080c0607090f090b060f03280b01080103030804060e0d180b03013b0c0a1115061e0a060c0c0603140402090c 67
    0x5941c11001d94140765162028103541d040d044420176400314210f042002a025881c44441e0050b0000d00a81407403900e03001181c1e12540103500480c4c14034000160002060320078000507130031102c2450544030403854107640131308011480c0100ba008684d030795202c1751950f549004a80c0c0721800440381c01c1d120701e0078071082c1d046090030803182e29030300e00b9400e1a103d00c1103040c03140031800715051f150b1421590960710100c1754103030000c00448002c0d98406851280d0b0204000360300894059a4400300074100e8002c01d11480d41040d8030103002d80509000602401c04814507804c9104a4a40c100d4016004010340d02000b004042d404500050103000380041e11751240001c040103a5640c0719040c14143e206100c2741c3e5010031601c52415044110042109407428492807007400002c2c9090802c0742c002c01001464100c070680c011000724100030b00003010404d071102003100404140c14100600b03810b80110f04020300d0000c00c02072103034095800064000c6055819598001c5400841c00d44514401100302c49 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 991438156 1250 991436906 991436933
    0x601170f15010e070305090616110f070f09060f1509090c05040e131a0a0b0301051609170304180e0102030a0e06060a18020d090b161403060609090702010b0d 69
    0x980400c510300260704d0600034000c547c0507801102c0181980d0361101c280c6402a00c081c0b0140c2c04000f41c0402e2041000380402101800e0501c02000c0c124092600c60301c08222240b035400803440c241003050820103030100d0940e90044602d031075282019404240703000c4030350918a4100d80304052810351403901540d03107c00900240c0d04a15041181511031407070904841d006420000c2800a40c202c90280c0c003101040920707004400b400022078544010b00c0060309450f01101d40034400302170503040c0124141d1200490005113002414041070320130051085450744183d000306545c00c184907201c0350003562503074070540c0d4603003d10703008540700e007012245100a03041c403009030b05e014482d00000c14100c2c68240040c1c4110b43c8a00e416046590060062401075004910841c0142d03684080c2c0e2000724100b074441d0b40c446c044902000d401c606214001a020400d00141034581da0f03014400c2101c5501c0e10030032221400000c031810005031340c03120422805081c00241a41d040800b03c1c1e1800e040144404207550f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 991439406 1250 991438156 991438169
    0x303080106030f0614101e1106152803120206150406060c020d02130e24040c06110115120b06030c0108010e0a0e030a08010512070302030601170f1501 66
    0x400003000c0c652410b44002c0d000e5440b0f0003180250000c3c60386841e003440e46c0041218140000001c102c0704417035090300000c1581c0008a840404480600c000500c01326600142d058050466001c0341c00201d610302c1b184100880000d400b070020481c001e010b40c2c00e800c00a40d07000d0700081d15115021002900d6401c01d65050320040010b1484d03110504c1c0c00c0c040c410640306156190140c588480c0c080081d4035031f0b01402641c00002c03101300c489109140b4001c120b0041c00d07100003000443d0800c24103400005d11070300da0300100303070224080c40004ac0e4000d1803842102e10514000f00440b184100e51401440c3d12205003202c007911050020300250180d01216415000351701d44078050391400f05040e1540720614685000130b1110f401030100004103a906600640088000150380c1581410b0340d1866120820070f80110700c03100700400051829510311400307a41018081c000103455a0301103030740c460b810301803510701000c1040c81d45082e400c1044406a41e040920803515200f01d45030b20030121200078050075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 991440656 1250 991439406 991439411
    0x120f010806070c2a05010e010f08070e0609030313060909091e1a01171e0606010c050a05060c031008012306040b06072a0b16020f09100806160e1203070804030308010603 74
    0x200d92344c01007860158100319521501200d0780c40c0d5004a1344400580b101a910840a100460180c0c4040000d41aa0300c1c90003600d28001d4280f580c042c1103140c0c25030003501601d04181d80000052014038603008000c3c00c0e2024440ba4591505d010943e172101206086104a081d500003e41d0075541404006000740040c1568240010030b00c100191000220003044030b58484000303c3c03843e510542c1c0b445e4090340100103488154660b40d55450801606441e0a600b1000210a00481d0850019002c0085c00c080008001803900c00d005040c00000354241660400d03800030016460340c0700d6820025200c140204516a540080c0c03512611106003203484400f80344040d0109025540c0000100c02900e030214074203402c040a00d400a048050700c2030040340c2000038540410303030548030140401e020b041804000c0096504000320030f0f10b40800185081e009140046c0c0b003050440c2c100143e003489600a485130494102c90f01190307840c52040d180c000307003009000100001496440361150f41a61804d0750305 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 991441906 1250 991440656 991440677
    0x5030d0906110a0915031b05040515120a0b1521090105190207050717010905010509010b01121112070815190605160c0605120f010806070c2a0501 64
    0x1004401c0c082c801d05031020500c10b18062042041c01029502040441d2034041038416000d50010310501f28054400081a00400d003801a0719042c0000804120982c0400d03003404003201205102c0c6801501c040d580990303500c905030740c03a01c45064049602c602e2068040d0354401c0311107215141c100c40d2584200a050078404240d20000c103000345130003405180c400c40b5903401d504602c0f60080d48207040407903291080b617400080f0200300f00340d03c1407400213032030000031610300500f0704c542544c8000b41811400d0749440000d8400e03030b81001c0040201540e0410024030000702c401050304900c00c46202003103070700380389040003045035001004034130690300d0103022041140c0c04000d00c400111521094000c040040c50180140c0d485407002d4078400f84451401a800541e0f501c0d50f40b890300e074682090002540004004809809003810103421405100b5a45159031521207810303201c20000d40f0742d1041185440981050080c000380c20088000924407000c50000764138142c51000740e03144151804900c00d01c86 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 991443156 1250 991441906 991441931
    0x70e190e0604030c1e0b0c0403021201060612020901121107021003050c07030c1a09250f050f15040806060a0801050403080f06010c0609110108011e2105030d0906 71
    0x38400d00403585030b1500c0003811529a40c00b00d010700d074400300301042d070421704003000440c40c0f41c4d42d040e00404024211070303611070550041c04540800450b138203400344c0c18180c0820045078403104a14001400d8040141c55040c3c00c80101c42d039007d2103008501850404c0309140720400d0030001004224404c4906c14001420164140c05880b0304580c4062141c00500010000c00e0040668000300e91066140754042c0c2d803e056440981c190556040ea4540e01c0490350000b8100c0d100390800410034001d05500c001480d2000c48980b40101d030207614000d50341c1680410403a1108206c0140031203803018010b88a0361034205140d6146402ca0b1007600c100110600068591010f2240300c1c0550303095a81c0e20b40541d00c0c00801c0c3d502c15005050300b4100651000b40030085005842002012841540707814081c5203250001450b110040c3c1004240404190809500c48403a802c03103030854a10207000c2e41c540811359108a000c0070030500182003804000f41100120030030b94004030855225040403c203401c4c1015 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 991444406 1250 991443156 991443163
    0x6100e1e1906050111280807031805040e030f0f0c0304090902040b010e1320070b010f0e01120b0c090607080309150c0702090c1902070317070b0612070e190e 69
    0x41c0d24501740c3c0c211151190300e00200f0490103582c00b00c014105000c4203826903440d903640e40005010350000700300300e2101c115860705c01500c9009020445050000351880700381c1e01c1d01c0784103041c54141c1c2040c0008460f140104c049040d1160500c8410503241c4640c0c3c0d401c03202c0040d0acaa407008034891440e04a011803590b00600b41400c0040700500040c07a11b000210b80e950082c510591200d82d014600004140340c0c2c03070300e2001026a9441140050301c5549859181120901c89800075140f03100031000510144240c0c1c01c085042c5900300ea15408140c90707a03818682d1510030f01c0d0009411050014000c0107200d1400300540c01500107804985800c0300006c1e00b9140c00e90261104020340074100603950140c80d203140416009000d07540524503003503560300403211112400c090000560050705c010818040111003003d14400020b05292030001142c1d113600e11400028507080c42010782a100c0c915090041004c0009001207031117044060038444000200301150200c2205102e0a00b8004043c40c1400b0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 991445656 1250 991444406 991444427
    0x503010e060f070f05270406060917010605030316030c3e030316050313030f031710030201030e0a0209101503060e0105150f07060209040e06100e1e19060501 69
    0x40c1e4406080c5070301c26071483d06d40305248014a140300c01581c0030440640d500c1c80b0b440d00074074451b1036003e40e461a200710301c94250f101a654030038903454064100040d49006c0704541c90701486641c004c040c07941c68941602d10198082003e0010145a1404003070b000180000c11055034100c80d2460100304080140440400400c6070b546e0190010320600c104200501003c2a5486c400d0b0260780c1400002180da120020303480c2d20a0b00d0341d042010f484018150480d012076258070364140700c800e40d441c029040e9100c19195120003410559603101950108000b44044d600e100d07801000258a81407d100a08001c803490040d070b00e065401c86140d0480705e0203807180008135081043c0081c41e503840c160400c840307041d540c030700180340f810104181403820510130300400c5620f202c2d200040e150f86603242800200c03a0018801d10260780003509200380e807a442d00c0342c039049030107900d1480c2166a0301090090060039000000c1c541d158542d05110900e0110f84070007884403040c12007000459900c000444522851 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 991446906 1250 991445656 991445687
    0x110a051c02040e07120821010e040809040609020a0c02030706020304050a03320319080603100f020c100516050a1b0302031b0c040501080d02250503010e060f07 70
    0xc00e0352450040c10590404060080824181e03a92203550340a00700c001500910102c0d0a08400140a820442e000c0c0741c0d00d00c242842c0350310030780c59810111001c04840000e440505031550100e1960385617179483d0040717800344c0003084c4207644681152801400d031100358903049100b40034169002c15179920020070340e400c840c0001d1004100c54a59200c0707100c19040b2111201380d080b0401a041360301d000040801c11940750110080d41d8400c4205401c1071207503000034a510812204009100381d65900188001150000040000e20341c1020142032000748110080309040340620001c495440900e035001c0fa1040f2100e4850105400e003020007120140301d210005804501d044014050003010f8910100455209004591603c0c0c2d0341c405141d20340017001c1341d95030b103548a601004407a042600405004001c0d8800420340b070582c4810294035565100701c942c074541030034200d1030001088100c00d4801004003500811402801010058031024100d034240011480100890940c9200d091307083d8100d00c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 991448156 1250 991446906 991446949
    0xc030307020118030209011e0603051b09030703022107081c080c2215030c02030d0b06091e01080c090a030f060f0f021809061809070f03110a05 63
    0x61681c01514034100c1c080c0c400000b105030540100040e00d07002c600030b0180044a40e95255450b10605100e00110641c0100d010103041c50107101c2010302000c690139100000d2134515845494030710200385080340300d81c00a50300c00b000c0c0d0081c82000700003c0b086059031011406940701c2c5034031096030710740e43d01040504c64080c8800038440c0032214455690185c05c42c80c0401c18510300f0348508144065100d600d13407910703003c02d14142c3c200f002d1a00c404062015009034103040c090300d03050050203903d84c05024903001080351568508625652220708685040000400704540e4a55440b0b141c0354039140300c00814040303010350001c1441c411707040042d94401d100c001d1514034414115917400c0c2e111650758100300d0b41203031105402115100a03000d41036440b17286a20060311189070110071012031710721404480c02840c15805000e400d403500c086240081d41d90038007444c81074030f407a4006441c00c3d5803540044400540301c40c01100b00320f44800c009a4244040361070a540e95151010080d480c5805d0180340600503 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 991449406 1250 991448156 991448167
    0x9140c07020d06020c031206010c1a180709050412180902070314030f07020d0903170c07120501060302130501050d020f010e0411070615060206180118060b0f01020c0303 74
    0x490410051140c030744060080100e40c040c0b80d44501c10390300075901a0400e500003141014600345c18004195004c0c10918180340458101d48408003031960754450f00d142d800e000c0d000900c40e240e407004031f07a04102c011012180340b2581d450b1400020710054078111041400200d00c03401c02841444202038070b00d05000307006071461400d4034800c020350044000f20f0a0105a103001c600d015407510166103d0b0382000500c2c1a145004e0b40c0007800c0c01a0324100c2c45c18025210801c7c40070401c4400d0040c0c00c00c141c00244d07661804048030151420304c035a48603003070301c4042600300e008014040d08130340110707032081e41c1c042c03405c0c0780c4071040000b552800d016840c2c00c4a040740d42e1002525004100d240340e000f040c1094007111215202040036211400039069800000103141010851284110b282e01d4284040407001c5500f0250b000352101c0380500b460704206808005156011001e600014070158280e4005400c2c07a0b05191136005000c20012092103840070005510b06940041150003020340700601851a18 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 991450656 1250 991449406 991449421
    0x10f120309090506131109040c03052205030702030a030518010507020d0f0c09060b090f030a05070314030408061519180f0605040c110706030c050a05180301061502070914 75
    0xf00802040c555120b181c20031006402d5040e0322a100c110f070070b105d02c41c5584996075030030b002c1580e250500400c101031400c000c000041d14a510403600041c0550f0719203400d0030860030a60b10390301a11001030350602078400d44008040d041001000030300241e42401e0403c07655103005403043e015230032020703412203401e00328003000a0307205181071040c1c4e02c101c9540c1030498460304100c00301c840780c0e005107882c000c0001e22213540b450420032010380140c0071001814104940d40d280741d01c1d4201488001c020002d14009c03c80740c0319081c03060354050400442281c1d11442d010340a103180102e015245400b034a5000c0202040c000302507007503000d5484441c024003080390b45510000040012414080350742d65540e1020a8554a6000e03018507a0f503a5580d14021000c0c50903200e00b090025032040c401e151134103800c102529041402c3d101c05070301d241441525041400e110f0100c44050688459155180c0640803503000f19100882032000200d500302c8944645614201003201c2c0d00d0007110400010403400078801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 991451906 1250 991450656 991450661
    0x705030d08060102010f09030305010602120c032b090c1502010524190806151903060906021213050d111c1b11041401050108040b071b030206010f12030909 68
    0xb80042c0f00016007070326000340000403640300000860000340c80d076004102c01641000340e6144204c00318915842c0c045102c00c20350703581c42000104200c3c61592081d1071000c01c00d02c1120300018100e04c3d070522028040b0318108003d40f044d8011800700904100325540d03124414030a80e407051030804a0004101e000d50390300a0840d0408681d0f9601540800ca12079052900324101d0005140740c000825060502c130390760900400040704020702901c442110210300c4d4451021900440390403400000c0c1c50507050030f010029109504288104000e1003050080e404c42405042c00020b000340281d90341c901c001302d0201c8805900e10285482c50740100f00e00e0024070464001d03440401c14506104204241c1340c52090241c2a0001c401d0794440d9001100440c94102402604852410880405910344c1040c0018040480c081e0001c1c10391442a0700185206015100c52941811002000c4000034881d00d402956060709000f2000c0103031031803d0024110b51644010850154140c48600281e810040d90340300 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 991453156 1250 991451906 991451911
    0x2030d0905100e01020c0d0c031b02150304050c0f03070501170604020409061502160b04061d04060b07020120030912071e0e1b030c0c03040305061f080705030d08 71
    0x1d00d07009074003010940c6040341c4502c0700030302d003c1d078009038645042c480c0d0681401c1111030540207001403200a0800280d20a0408900041160b445c0c00c4c28051400403800c2c6a1078510b042404400020500c07051260001d1851440081100c0c5002203c04040515840340300a00c1068007190001c0c1e00100d5941c5e5540b102c0b0741c02200900010708165035512448241c03081603100145004d0b8070000003010a505100c070a09000351103203180110f520f0044c00c000c05200d40c1c80350f5010030140c48400609400300e84031059031841c0c0104284111501d518820070301d52b1001c04100d0125440203460381080652454900c0b00100a90103035090444000a220440d44482c045030f1407406854030100368400641101c2e94074452002681d191513081c00040d2410030000b070402c0100d0492000c0040080f0b510034112079210b2410340c2807a48504001d10114518022038100800a020f10750822a424803c001d0042c100440c140c620380b042a078540d50301d03448450038064141c240c0c101203000100b40c1c3c010760141d41c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 991454406 1250 991453156 991453163
    0x604051f09090212010c180b031b0d0209040606080105040b0d0c03031b05060c030103200f010e060f18040c0507080a180305100c021b030703020907030b0a0e040c1502030d09 76
    0x403442a1080409402c580341280520041f5201c0003131404072040310307004040601800001e013851824a043c18035076500401c1002c0d0720b0f40c0c00c0080c9004420170160103803043c2c40c0c0003030030900030151103410141848209001d0b4500032890018101c03128030b801c0b5459032400d034110104466203415610f00304ea144180c41d9403003601400c0c02960384c00062040244034422400c03080390b251254114038104840110302112107400800c0004c02000b5a03440314040102c0010074288411011048004520b9502404458400c14a004100028a0f0689410605c5542400c5800b0060500482801c0d070340c60064800182070203005101514809010390840c103102c212075240349004175620350f01ca1b446c2210700182da00c5483d4650303586513402c0c3d030100440c42c40018000362090040443c5400700b581e604042c0700203031144890202242019020b60f001c103032810300242a40086903159480c2c1d01e040e500075103040310303280071800e000200320560120025406015601561424070040468006172041071000d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 991455656 1250 991454406 991454419
    0x71e1410390c080a020a0516080c010e0102120d09020f0603160309050102040306020a17090c060a0c06020903061024050d2d0603110d020d031206080102070b0604051f090902 76
    0x8008580e0340c4010f0007283d04c4a81c001e01c100030035490240d00b0500010300500c24a200402c05003d21040816280d8621000b8640b9019010751240100d140040414001c89211400a200c65841c2c5040d00612030140c004d07070309160381d505110180580b501c802c5030411000c803c0d02f89840c0c9410701c281c001030303c0daa0142c4009030600b900ea8031042c080b43e21003401540440c0082d0703d5002c00442210113564042d0220700034154071a00d86022429a10950400d0410060310045004c2003100c141d0543c1e81e800009001c8550390b00e00040703a890b8240a80c01000044600c0031a0507003520411300310409855074560ba00307828002c2003048100541140040300500c8210581058100c01780011a1a050300d0313030f00b0002c1003851642c100a544115080700ca41e009074030801104001d6129482c04845d01035051801c01d090307030180c803050401000d0710b070080c0c5415400000e00d1014884100c0010303000e001d00302c8041000d900d81d412664030f0540c1d0030803c400d045000c2102080201071aa0040d030b403e50002d40356 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 991456906 1250 991455656 991455677
    0x4080903100204140405090601050d050f0a2a060219050f060a0b150f070f031115040309050306090c01080901060e0c030f070f05071e141039 62
    0x90030702a0401165200380d80c00300b010008010301c05a441a40340303094400b00214182034800c940c035002c0500030303e40a00f4080b8100010003030200021690304800c2001ea0b81000107501d4038940b800007182e54000c01000c078808012010b07010000c00c50440e442ca070010101440002008100d10114010a4819000304080c2c0e0b450b8400512100d8401c0c2c44c64807000900a624034200704100e440f14062940740368060100d2401c0b40e83c034500f1540711541050851703111909c00d03d011500d0f15070062006080e03006d6800c40901c4151a107120301d028522944076200c006480b041455940c680481b84155076500103120009254020761909030811a130b54004542d071034035504c90182e010f1054400d90300b60070002040203100e17030540b03175036640241f030a14041202a5007010018024010100050603541d00c0e241d03903101c1954a4a07001d50f005a104000e4158922400015500c2e2540c41401e0580a8145001031075480502c005000c500540c4020403208042c0c000d540768500c011200ea44030074030852803007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 991458156 1250 991456906 991456909
    0x9050d03030e1b030d020703150504020607020a03060f060509160c050f01090f0203010c050307090e1e0a0903030c050301180b030c150a020c0105040315230114030c190608040809 78
    0x1020f0035019040c108005000400070a242c0b80c002e0000d0b101c07007150403588051001405c101c82c4161034591050010803c1d8450740002405407017032401c002e5100d0300c011400410400d50f504074420081110f8010003c180d5518140701c06081e040380c26038110f140e030b00c201c0ca04184c054561100094060000c68515045a886103030031a513540005845a40500700e20070110715090141c0f07a4003038100c1c45c0ca40d0079400d05a4000d8044c221501138000c21751928000100c3c02c0d188600030002d01c0701d080b0301c0305d1118100740520800918a102d000d4000030306015000017068021401c13241203818840410240c0b65a140404c001406403a409a42c0340c0928010b517041a519100ca0761401d1050004081d61010b42c40c001a25003aa200d0700c80e41401003e000c10000308000040602c40580e50074004244100e04601e8100c0c40c860030100d80c5040704043e400440e1071845051503281800064044542e0402c1c050f0401420f142650b015071004804410f00380b007030910601b40c0e42c1d0042e203c1ca08a5082041100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 991459406 1250 991458156 991458163
    0x2061804150302120c060712051e180d1e05120a020d020708011b050903101d010c0305090615010203040b040815061c061802041b020c060a09050d03030e 67
    0x4150620307480640c0000c0c0194502205500004d503d20b800030580e107111480070803c01d003d25000600130400182941c60a00d0280045915100300c2d11070000d089110a00c100000c2d410a00c1c00d11100b1404a02c0a00ca40c1001c242c0040e0882d00200200e001000c52072081d0081442030b8002c643c103000b003809009400103a00080c1003842942d401500480c035142070024075106107544410740c168102100004c0003d004141c1d05007070790716440e10710b689005d40c0300840c0c0f07400c2034850070104462a0980d903402030382c0c0c03094401043d81c0b10440288482c0c03051500031820b9800a0b222110b8070b4101c4d8020847c03041449012101e00300e07043c01964181a503c402d0060a60404d0f8041c42d2030303400c4100c0c0c8092802c0343c000c0340741d404007049803807034000412116400d101300c81a03000144116039800060a0b0940d18200e00400158028424412003242d01d4081080e00502d0060300003510071650385450328905030b826a105a01180c0c1c074150841d1400d020012080403059040e402e155441511803034680050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 991460656 1250 991459406 991459421
    0x20c1207050d1806090513110307020a200108130c030f050c03011404050a1211030409090209010e09060c03041704150f030c0215040c0e01030c03060e07060c02061804 73
    0x80002e440041c01c1d001c00a84184415408100d0003080e40304240802c64009070114241c503400d8500c50712002c1900030fa40020701003c54110324000303001c400c105501e81c0c00250081309512600d200307844440549460841d08149089040c0841c460000141e00b2039285882026818014401904540d13540e84440c4490380038800107170b6032074000c3c1c5020707416800d09000386600201d629008000134641616440d440d11341e0008020500e4a51307142c60440c0ba81711380160958880e040c01620f5940c0e6649181070014001e100c01240540700b100000100303105000803662040034000c015000b1552802d40c03040c46644028022071340c1041c2d000c090415918944044e0001d80030b142213a414000f00010040d0051448400c1d00041500b01108083d0003a8041090100000d030302084500a0b1100e01d0014403003400c941010007410001000001400f80074a01007044a00801040007981401c14205854201c00d008500102c2d5a06c8200304c0141446030060010f401c4a0790080d50070050800000e05492a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 991461906 1250 991460656 991460663
    0xe10062f031e04140a060507082b02040609051c0308070c060f050a0509060402060405040905030f0706060501110a11100c0b040605072a080c1f0219020a020d0204020c1207 75
    0x125060000104000c00d4040d00d0303134119191341480d45003c000034460310860704000d00f050f5001c60810302500080105800e211078410750034541044558200f0000d4005220703c00000300f0101002850742041518102a0010301402071142c032600d85042c8c13a00140604600c0030400081c440002003990340c82015489441a08003080e9804c2c03615a003025503401514142860f0004400d2000681c4c2d003100300c1e81250000e0f1000300d414005820503508601400b807030524155000120001007000300e0b808101038540c01d072190402d00d0403502080ba6100300c2c10303000401e40480c84000720741070b26101240200444403850080000f510740d07030310001c45400c00d07030741100c07803d40380d50901c006683c10810210098444580d1800c0d017002c400115500d0309000300c000380c218480061248401032061005040d1041c40f0f902c4d1005d0300c5901000d0000a40c00b124030602035417900e201804803144041240b01e0116001400310a6a48454081000a601020540c013203803017502140049a1880005801c40d03502 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 991463156 1250 991461906 991461967
    0x102031006030c080f0a0c1b061d030f180a050301020d0e070504020c03030a050423070302010806120615060c07030602040e0105030105010f12030903020a0e10062f03 73
    0x80c1c410090103607084184040f00740521482003291440e0042d03c281d80c4030404c801c0100d01c1420401c0c2c161150740c1034080c24030201ea0070b02003280c140812600a10303907038409503030711146000c0c4602416807a8021179005801045080181c4c1d044101400082003d03a200146000c7c078050b62040001d08907440026032202c0c0c0c0d600ca0002940741001441b115005080075113044d46081d1a04c1000750b11791100910502c44140d4600100e4144000e034075203690001e02d6200d100f42002c0380c0c40c8030303281d0320a00ea10003240018903080009425042c095040060708404200800c0191181d280d40001102d41302c5010340c0195090140c4020340d901041404010340c0541c1006a4450401c001d580714014140c004500aa040c000100f10320740740445400d00312280b00d10100e0318612039150441d0160f03469800030394810500d40d8040b0b2441040a4281c1c0510a42034000d1272035a6111000e8078002402c0baa100c640c461091440062030407611491001d00201500341c0f4640082c600704c00ea1940c00b6654200603024 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 991464406 1250 991463156 991463159
    0x305041b060f1805130e03160807111507061d1006140a0302090c070309030215090108070201150b070501060b03090a02120111040515070b040b070e0f10050309030c01020310 76
    0x3e4001caa8402100ca502c0ca64a940c24100808075482411755464018516070391090400c0e104018020b6542d282e03981010040603080901341802540c00001050b01c507d800d061000501d032402a1481da000215400c034581800d0302512403170300030b0040782010030082080b5a00d4600f401424003880c05622f4501c40d0003e00281401e0765440d4078900c4030b2249001e184049000d1025a80d41c245840d4842040902240d440c0340500d011105101e0750b50000750014481c0c0461241d8260350001f40603041003c0c0d82c0c2920903a90104200e090710710700641040307000e6021000b40001003000004045081c0290000f0031240c0d83c901681941c0e500031a003016243d004119900110300e03002840710382e0a03443c40000d10107441e803840c0e60b120720702c2a440786500c03e62240080c0074100b2034110030b680420390003402c2e50580346058201580001400c6900320700080c5000d11401181c50041924542148050008010501d420174182d8a560010b88413010f20706c800d10500031110000d000070f510a0071285110718008d07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 991465656 1250 991464406 991464437
    0x3061c140d020d031409280c090501031a190509030c060f01150203180423090c010e040603170f070c120b0a0c27120305091e03030304030305041b06 65
    0x1c17002030707030310103607409803001804150400001c000e0540c103000c0710803141c10b54450343c1d072050b9244090300003440782c204900005803101041d40200d048034083c601d02c40703420b01c407540c03585000c050484204000c0c200c4a040030024030441e034403040e0b101c2d1115088034546844081c00300d140c500d00311110f540704420b03100107000c2030801558148a4100341d0000318105445040c00070000c16618185038003a541d50035807040018800b005089451100005a2001d82400404941c5a4062010041c0451514080050903050510a6100303c0303410044c02e00b001c014141c0303644c40320b80c03010700174914002042c030004020608a403c41c800400c540c8045070604540303440e1a0326208001003850344010301c0d00e41e4403281c003900040c09003290701010f50034200402004014050103503c940000004104540d001c41c20580c0120007418900c504492850400a0a0401d180b680c080c007603545c0e4160b0024804500068040d800076600980308812011840c07200d0900d0241a11072075100d080082c09135084003821 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 991466906 1250 991465656 991465661
    0x5010801060b1216140703020d021c14091207081b0f0108010513110a020120070f020d170a0305061306050a1203050d0e0a0b090303061c140d020d03 65
    0x1c1420704501030803c0301c036080b495070b4004010462841002c48409094145205207000e81070381c0c5540d60825203034061810700a54401c0b0040103000507100701c0c040c0307010214103503d100f452221603640b040001d0075500c18076410340e04426071144e0002c448a5448841040600c8448090b112800003016000c403182c500703070514880304030030300d021340032403650f01c811640d12a40b61415280c2c00d881d45140c000342c42803160700400410b20002441d800100e40060034580c10340200035159a040040342190b0450340018500c0d10070144020004400d0300644001420503010040049008110031384c6480385601c180a07aa91001404500003a99002080210702d8071112304103120000d1803013013021a080a0100e0380790252070146002d450324025806c0c1c10944204110f5401c03801c41c503801e0204540ca080d60550320554088100c03a401100c80005181c483c0001c1980d00c00c000c0100402e40c001f403458450488160300d1442500d0214612001c403036112000c100200011000b0b6000b080180d003540001400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 991468156 1250 991466906 991466909
    0x150f1203080a0216030516121107090608030316020307120203120a090b151c0506010302030d050307050403031209122a0b0c0a200303100b0307020a0f150603060501080106 75
    0xb0152050020300c001c5000c000140d8046549814115503c01009482824212140b00000e02d40c074840c000032044982c7c40f100c8401c901c3c05050441d0520754550076a001a91703401e0250310700c00d0b4030a100041980450303c40b400b040d01124010b4904d8581141c9031000c5101d1400301c1040941c3c000505011400b5000822517481b07a000c030401c12201c8200d80e19024184000b1b01f00d0111005803886080c0c655849440104507050b101c0203080f4420792604e499a100e031402d1105922034081c440090485501480840f4460900c0d5900c4925141c2959802c0c3d80f0394544030f860031031540da02e84800c1d000481c3c0d800018140700349502d4054105407074100351100349266413a2024140c0090310120005980b40142940000b0b503019181e40f030300404070f001c031b8400001280180306499034206175801c4103804801540543d0071266803642081d11641c000c400c07440246c0d613140041e40800d96210100f01074200c1001941d00c940c50b240d0b60094842d202506446168201740c03070381650341d4010000c0e802d0900c603110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 991469406 1250 991468156 991468171
    0x170408120c04050d060902040e1b030105070201151517130c05061603110312160801050904030e0607050c04020d140603010b010903120e03030703080105010e090108060703150f120308 80
    0x245040c3c1048089000440f000c88002c00442c2c80d04042401c664682c2c121202241e00c1d43c048800310540303541200703080908001018081c3d442c103404030365640c0c418000c600c03124440301205480c3e180707040c801d0320f550805a182c8030100407841e1030021004c014040d40b40e02500aa003100030041c0c1c558107201c0c47c8010b250307104c0c0c2e2003030608000e20352040c80885110b20519816090224640c800d00c0340e414210300c101c6400240134032010b4208078038440c050074080c0042025950701442a80c85c1c4052221180080d100503000c14030441c4284898075116004181f42d80c4a4815114a041204045410303a000442d5030424240c0340c001ca40040c1c04601c050300d83c0f2141c00c0b0000e00c6408082c5001070858840ca00002d095400074841c4481c80d5801341c06a25844500642140d82ea60340c90b0400600300c0e4828000c01e0f002802980194413035103031400359030703060f222001d0103491a80c441080c2038000703060301442c0d81602d01d2010400121000780d818078034010440a031410120791414a07006296000081440 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 991470656 1250 991469406 991469431
    0x40b060904241104060c031e09050409030201020c0706020c040e19080c12032505122403060a05040b010b0705070909060609020d0b10020f06130317040812 68
    0x2002141d0703145100e514200c0d80c082c0c00e0b6541c042c40700306000a803101c1075a40312403110018001400d5944104818441c2d4042d0f80d03040c0da40c500f41000f03081d00c0f8803484620000141001001e02035071a0950090300303054441c4c00014074040f162008141400c815a003c840540c22213401c511050900d40200b2144924080292030703c48820303442400707589140f040161440d10017186014800c01e041042c401c0240200e20295105d24051800403c0702e06003102e5a07446034402c0a0380a5118025403c0e100c2c1211103045a0b03805070303038101040c0030083d980e03181d0107a1460721400e08010382d14180040c1d401800b08203c04070712448d150a2203108120103038040000004100542e40c007240010503404140c400341d000c0442c22204a003010000b81c07040b41c0109502c0c034800071b0600c407601c40c01d61220f0550401600c80400508641409a0320350a4140025205c0e411800000e80e0701007001d08002203080c402e0902480c91620340140800e0301e03c0c01c81d421160f0060000d803042c1c00482440149a11100f5100d45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 991471906 1250 991470656 991470661
    0x30c09040c0f110a380a0e0d08040b060f19140406050d0f03140d0c0f02060f0114090903040803070c08160501090303030b0406090e300a11100f05040b0609 68
    0xc5641210100b04462142e00d80580f0b460100d809142e480c00d410398545c105042a81490101c01000303003a08500c011141c821620350802d6280603010881c860394110140e801d441d96804207201d1918000c4402c0c070360014814a08400e40845c1038102c2e00601291410038518008510a20045030340c02c0d040603210311510304030800052602502140c0eaa507040c80e01110003250399620081c01e01800b100b0703070141420b01e0304064800ea481a4a19078004050f403c442c0c05884801644d5078503182801400d0100700640c41926050070700140140d04042c002003204c0c5425511050b0034110340040c81c0440c1c2d0311151104c1003200c0f44041060702d58454109041c170018920b06000608a007003148002414541c0341d08e03403000355944580c0120000e010b102d100780440d008800a0701e1300ca0300b440000c0c4800703000603580b0010a06400300d8048410301481d1070340385451351452050b540050024041d0030740348651200122080030754066040b4078202c088002c100d90030a4902402c142000600c042d006141d41d008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 991473156 1250 991471906 991471913
    0x50a1103060d060609051504050a0c1b050c0d140607110604020d02041b0329030d032408061005180601110a0813080105090307080702010302030c09040c0f110a 70
    0xc581d000481100d40740c2101d50603142c2400901469807264800a281504000c41c80d00300c0f829091400d907003200c04000036540c03000182e048440d0703103400c1c00002d004032220044089549600e400103600840403100c548060100041d0400c0d0000412101b61300c220541100784e00d41000f403030741c2151240c1820300701154818078080c0d44100081020b440740b07201c18a18825521182c3c4400360f0b0841600c1c50003410541840003401030800022900c0d6901d607541c40150140990b2400b0034180c0c840103028007240404e0040880103440000c140040340391072002c410311442c0c01004204005c2c040003002c1e0204c1c0c81c10405500c6000c0203a8006400765680214002d010780340f03004501c0e440702090a00c41340d49440e0344602c51804421a000501020000407080014800e0030007035001c030341081c002400107035504400261607014512008040c101d05100000066019802a40c0c0c48400d003150340d41402c10300c800003030590b40c5070260003000c07411008800c6c0760320f54040303007514904866500801026000b0364 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 991474406 1250 991473156 991473191
    0x7060c020607170c15060a03030207091505060403140c04021218250503010b1005070809010203090604120201030b04110a1b02030303011706010905010f0e09011d0d03050a 75
    0x40288141d2000a86070108072100c01c0c0e4420210103252115200c03030898141a03a40c44d100846a200c5200180002c3d1403032814942c0c404c203407641640600084c0f8501550070020301131102d0b114000c18111840030500b0345615019000850041c0030b41100b00e031010411500304801d140000c4d004a004004500c60741000c2100b140e04070501150844840c81001a15401c002d1031703100c0c110564082036442c100c0300a142c40e44105a410840007041841d01d01d9042140102540740c1110100e10140101004a441100903244204040c015649807145580c0007540c182c0c469000120304503454029041907507414401c0902001088d9002c001c41301130b02c0210410b6004a20207241048240c031401c80e64403241410183c00c042d4090210390b22540c4a904a07240843c443ca0b60443c10b100d61000040c7d0b40c0342d2401203a0403100c640c200042c981c0d0800320390390107070200106040e484d50749500c0b80381584407858110304003005901c409040755182801004098070030103050000a14100804c1b2102d41800e403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 991475656 1250 991474406 991474427
    0xe0c09010c0c030203070b09090924090f0607090602010b01030501061b08071407210201200a0c03050105010f0801060803090d171206040c030c02121e04180e0706 71
    0x900301040701c004640780081042c040c603000250036000e180c000203080740540c80600300c0400c003150700c446183d650003d031039504c0071100a41c1c440c1001d10301300c43e100300c5030180031940c001d0400346c10368513201c000d080c81c01e240202c142d40c00c80000701040f600708507903075081c420980500400d18045c01700b9450004002c0c2450301401921034410601416201040100c0301200d40099005c00756441030080407000171b0f113443c920321400c1d0440c00310301030040040351030b80d5003070b81e446034142c40c1c44190341c0a08200d400100b2400c601c140c4c15109524540002c100b4074a14007000714403480000c9a10b40c1026801c881c209080d40c0079030a143c1c145a0244040d401c04010703540c40150984200094000c2418500c2c40e0250502d40a034034800005254038584038001d08603440381c4001d443c180840902d01504a040301c641c043d0490050700040d56920300e401ca101c0040001001d29020240031030380450a84e4040c0d40a68042c071a6840da44c800b14280c008503020300d41c018800c0340040c1000e2482c00a0141c9480c0c5034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 991476906 1250 991475656 991475659
    0x5060d020d02151e09030f0a0f0b0423010911030f03030a050702010b120d091d0a0507020c100314090601080d1404091103060108090615042a02030a08010e0c09 70
    0x5115000c850840340050b1004c9038024508404081d102c0c116914280d805080740d070b8002c2c007900d015170096400c0080c05c1c510b0268441d070304a10b0034100b502d46004481c4080c104455056104822030722400c0a04480e604000342a0000a8010128034059078010390301000f0301d009030401c6000769807a1102006695000d412042d0115495555410407401008402c80207940035455610a00c4000c0000550b0b00203c0c0594585103882a1500b00620005204070900c842000554000482c564150f400464100542e0f004840c00308a0080c002004072049110040000366506008000c00300c00c0c10340c641d003150b6861b000d01825414096180d031202c01ea2141207090000c241ca08041c0d2041c00c0f0200d0b0010a03500004204001ca50b5014100d80c0d44241e505a00061849010445921010400074050f071000c1803051030303091740c0b841400094102c0c480180d400744c000d07084240c41d4020b130102903c13201d5a80d40c09940c0c0d85104444c05800c0b120706030801e0003104035660030408550b2420f0200c42410300c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 991478156 1250 991476906 991476919
    0x110909150d0f1703040c0f0b16031d04051302040b04050403020319050c0d09240207060c0c05030a05030c0d020102030402030d050313140d120b060a0302090315160305060d020d02 78
    0x14581814581c501254036000c0c00f07030000000300400e03c504a2030702401d4034030040c400c144090380e9003410400c0d0700a484030b549100c4000090040020700803071807503c040c0004404a003030112500e0004084540c12150303010b071030501802250031494148101c445100048804214904142d00c000307540380110300008001c01c00180c400d0b00c00c07601840c2034601c1d00c0e04100071200a8400703040d00400c885039030f00c1012003160b40312110340d130211440010759031545103a0b40100102440d02c6411582061007007002d030f524640341000420b0640b4140311903a4154001c000469079202ca448516187c5002035454400716441802480016940854403002d1400c907450169182d89030001c00d9407280c03810403001030401003008000c5580d1100401c00301103c148540740d1081501d1602d00001c281d600e0903401d940d000d6420000b410356207010354081c1c01241000f80c11600c0c03007220880b00c0f40b04801e00703a07503c1c840083d1400302c503600356626020f0103900440c150b6220b84000401d03804184910174011000b40f1468 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 991479406 1250 991478156 991478183
    0x60b03030d0f06051e150d020c010f240f05010e01121503110303181e090f0f01050a14040f0f0c0816080c0415020709110909150d 57
    0x5408005480605007042810403004032860b00c1500241180d100d4140944500c100c0440d034141705180b1001000400b421149905102840341041a8010402c0050656090214056501d000d00c5041c2d104c810110000520200ba00000d444007403404c500240b00c1009020140002410041120300301c13102800e28104407030310240140c400c10a22840c850881d45000c0e001e03003044907a4902c01c02201c1c044d049450482140805050f203d21600d034049014400c002d10145040c2440c862690710b01c0034451031200140c00c3c00d0001580754000b910540e0303140c9401000e014801d4001600c0c41c1c01000d0454031480c3d010700d0b040d43c26480b5000c2c0103d803403140f903a07940031901c44225600000c404810614041203070141d8000d000d841c584007034824800e81100c0203c00708100f4007483c8110f010b911907000040c1820726065440000440d030541c031070210b004401d000602a5128000c40e080c62030401c03916030b15500764900b88050003900400e03400ca501d1000c0480c0000717458441d1100340680d04201c05a4405 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 991480656 1250 991479406 991479409
    0x1209040902150a080601020613170f030c0d050a06030b0f04110603011d09070f0b030c21250e1302090a1403060708040804060c051006030602190503040f060b 69
    0x610309003102035001840420040e0b154002d1500402c0b01582c1900c409502d525030b1401242e403407030122441e854142c0340d08884800715a460107101c0640d1100c07000c0c05d20b8810541520130303458209a41291141130081050350035a42140101030b072003015102c0c02c002c1c040c030756140c241c0300380c40281c42002c111000b82c0c003240901440802e10308015030050102580c1e569240e6965541444103625140c44220300002300b03800e0207010400f07904484e155000404100d0a0400746119640007034501c2d0070b008020018000308440028070100002d41d161031000c4245482c0c051001c640c00c2c103000d403c1c00152401c50301e002c0703540c00c0380f44511041002d0fa603406914180012500c02845110030320395200d2900540095222902c0c01e55008100b02502075903055104c1040503034444000340c5006210301c0050000f1711010388600845948103005a0845001c54a1407001100303d0704160029100d1580000e590f104414000707000000f90764542c0742c01c03480c42c50151521140d40343c054200514980d2200a01d40c0300307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 991481906 1250 991480656 991480661
    0x30605131218050402030126030c06010303033e09040b030a08030402120f250302120d030e03040506030a020f0403020a0e0421050a0804020a0f0806100512120904 71
    0x22a5070102103070320050321185001e03000190162400400c003000d4800402c0c1410300f030003524100c480284c460300e81c6101c15800d40310614038403221319050307200501c5000507615003044214000c500030b0320002640003080b1040e200030354512455200e9111100d8003110b180414103040060205130201a544072280c00d00020080e203d42d8081661600c00d05401c0c0e014091110015405139200300c4c0e02c0c09440c10301000d110b071500d1240d0f011601c0c07500300307040b400380607210044400380c6a10303254890140c00741c4035400a1290110700c0030304d41c03036903104280104c80d25415100e80540d00850310021801c041c0717400e00107401803200801800c1e00e1500402e80190b118000380c141c40c0516401003d04107007903260982040000780495003562038101a42c00380f1024150014081c05108003640da144c40d104100300d003941e8011001d44100e1b0800b07000750b00051031010074050100900041809004075041c01003007122040c000c0d4100c5031040031864030031b640700030700003d140300b2950400403a16110418a07001a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 991483156 1250 991481906 991481941
    0x3020304090905101b090e040312020304050a0311010204050a060c170a0f091d070318060501120302011a0604030f111f080a14060f240703091202010504030605 70
    0x801ca410000c021003000ba01107030540c408810b40004118240002400f0716102d42c119800d031000c00c00a00003803007112034507882e41d94003034003e0a240008070b80000800040740d00403181954142c1102d107010040640c0f1990f05a007104c0c00d040258142414080001c000405500c105014000c40c4007410041001d00c07080e0960307000d01003080070b8465025442c081e1005651404110000c2c0c0361000210310301284010f10034421760221080c1a085d59000001c0c2d00400000c41c0c14540c000c8100d40c042d0006001d80205400387c280c0714611246010b43d8034000c1d007540c2aa00c0e810f4841c0c000c0d824554015159007054401702d9800440c5128103503140c0c01d00140c1c062807030301280e80000f602554040e0008400340d4604020103e80e035000403507501c1200520031a4180d1403844e03645245480800d10514000740d500c0f00c000310051917110f110a0b00100c5412001e840c03030140701003a001140030000e150b00403d03603e00806011004144030019540000d040f4402e50100405082c0d4600110b48076010708040b895 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 991484406 1250 991483156 991483169
    0x1211010b130501060f02151303020109020a0801020417030702090406050403090317040e0109200a1202042312120d0e150108060604020a02070e0903070b0a050403031a060d0903020304 80
    0x203001e01c03040004a0040d080c24041c80020540c00148801030600c00254511402055804041d0941714501d4400e034101401c0010350866407510840c41c05a1b5408012400420005e000165160301d0200320581d050b40c400070300ca240d80c10501c542030140c3c459203100e03584243e01801c000b40350317500d9140a94100005400283ca50003903480361081c9030041c0002401a250320b0f11050442d03a0380c8407100d1041c0c40d0f0b012440c60101d4045994229080c4802014001030000c50900d6003402030800035940480c1c00c95403040102e0310b03005420a407805580c00c0040000c0744255a41401900c60480803541ca000d07441030ba400803000010b64030081d41255110b44a0360300d030a4261514406803101d0387c0144002805003540304d0040d080426124a810310845200c7c008507006044007501c1d00d07a4404c8441401400c00260740402c00c9007a000a010000082c402e0342c06000024a500b07040c01c0017004c440300c0402c44141007051205400803075030780005a510540c242d0300f0104000c00701b85022070840c00b4662000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 991485656 1250 991484406 991484419
    0x4060b15040902071e12080c0c1209040f02030402011b02030705090408090405070306262107060605010206040c140a17010c1701030b190603050a080d0f05041211010b 73
    0x101d451070941c2c004200c4d007406850b400b61080004546014140d444401c001c2101020b480200040303030003182e107980d00c580d141c0d2009061101e500c03941c5050040d0780420700d01007400080c070a141498a40304405000009400450642c6090b60000e040d02103070440103811001185200380855904003e480702503c4003600181e6a0300b030504d407a0403941c005080d214071403400c0000094401d4402c0c03046d0001c0786c0c2c0550b8174803003460004039540b46130047d03100d00d100540110b00700b201c0e42c41e070706100080e852201d04908954890341800e0103412621075130840d0341190040300900000c43c2050b200c0d0419150a00e28641d00c0e030809400140c51104240d00111807041c0c1c0038003802812006512049100400ba01e4000c0c0401c410b00391045054000d000080c004120741d400300702c401c41c0020150380e04032081d02c03001407a907803a0b407038081c54600500c1046521600003c0d00d2076400170390f4041e21114001d03500040c030513400e15a03201200032850729200d008020084e004041c0700a001d400c201c050a4014010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 991486906 1250 991485656 991485659
    0x3041a071e0311120f09031c17010b0c0c13020c0601031401110403200a0b0c0304060306120f0212072301080705030403121a091008061003050604060b1504 68
    0x400c140300c910444294081154245540401500800c540141103d0f00e6041454014069000b020541080c11b40541511821400c50404c00812403c01c00081441d26000588a0b03489c0e8100c4841805030440d0103143c00a11075480581c000269010075100211030041b01c02d038003109110002e01611071b07080090311840b8000400d0100c260b14122404c0c0302d0800a02c01005081c226a039188614800100340394241152903e00107000a040c413450b5400a0084103000e94820200f401604040040b4405400014042040c59010300c1200000c0101107040c642e442c2c1d5035142c1040048184902034041d1190f844410a50a800c0c0b2114000d4030608102030181c0313501c0c0c0100f140340c0043c00840e40c08a81c0e000086a10980210b09403481654140c0c1d42c248440c540640c200064091541c3c0d07100022203401c0c1030700c045d9031128000c500c80c07210400b4070184e02d4641400700f0300d06000a030400b210540044010710201e4000320718540d10a4215402044d6640c1d00d84c0419441c8002a000503012a8081030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 991488156 1250 991486906 991486943
    0x30b010e0c0f12070f031406090a021c0f1b0c0303200a03230c040311040f0f020903070f080a0b0912070c0e06150d0e011413030206011703041a07 64
    0xf0322600903001c3d65070320416400b9a00c1c0c1076088500701d801240c2400303040c030b0000da11850440100b69120364000c0000d401d00c41c8a0101c4160008030441400355103450340f41e2a03004800900c2080064008903821402000c1448030141440742002000b600b0140ca03280418582c010120418140040c800d03038981c0c0e40d10140c04000c0040524540e102c22880420100300d0748c2c0c400c00151180185080b0251910701442c59031034010344a040d004840d00151103200310580c880a912034400340c00002000940d03240ca01100701402c24295070805e8003104004c01d030900060364005084000164400350f26192030b00e40140c0300b807401031894800d5410450028980c0d0403c038141c0d1b0403000301c65a82007002c041e5110b030f4017000400200c4821540b180001800340030344221864110a0004010400020300602c1c4e030f2054040b140011904461240000d014807420180d04011f02c0e03004000b2191b04d80f100c2008014005d49902c00c5100e0994071409640c0c1e10600e0800c220220f80302c1c598405141c0345000701c00e44 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 991489406 1250 991488156 991488187
    0xb032703040317120105012001051509130809010f020705120f07241b0f05030910020105060307050108040c1715090f060109270b0619030b010e0c0f 65
    0xf1106510349100c660755000e0b928054989400201c04480c0c082e0b820f12004441400b104808201c488405041101d000c200078442d29006001918080c2c8160303182209100202401a1012226100d6001e96030046002c5030f055501040e000d2130105504100500202e00e08811034000f01d074030411400c8014548240060300000c0c907100c0106403400c8a40e01c080300e149200c032403501034580c0c901500c082c010141c03041c5801d1001c1c0c686111172803075150b426200c091240400d606d00329011b0b800054200000d2400d40c0d404503541d13039640300034012490a0303000b20352126941c0c4070b01c9041c803400e10041003c2003503494403080a052485205581d40c00080e142659840400c42000034142107030b80070030414040840c0003541c0c141902c00408090746131a610300004d083c5400c624007221040e00d032864007108800c2800c28028040c5a4142c03079400c00030b040041c0e011600d080d45c2c1101d68104002c00000c2c1441c1c00e890b0454980c5182907805550360229126103115040d4038416040340007c1c001c4081c4900d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 991490656 1250 991489406 991489409
    0x818071d091e030a0315091505040b0609061e0c0307051006050f1e0102010b0a0308030108010f020301050901091a0406080a030e1504091509060308040603050906060a0b03270304 78
    0x941158062050805040502580015500b41d960001c1001a00e80ca00176005050141543d0244141e1660354a20820446589404040710050140010090740c0307400d02512144460031a481454100305e40d00285080c41004107254011901045080da48a04d40080c0e6004e4145103090701d40d030300e1007460500d855901c4106803c039007070701d004400b00341400c0541030000113520103804c1015150512044000c0c403089506075030704640d00d411104d286500c40380700c440001e61290151580729410040603c1c25944040300c40c464070b604c10b1004210030381da00380c4034604660702c5800000790321444511010350b40d5140800f1300c2d00f0134209100011424000101c00003091700941e10003100004200403c4a00f507201320740040720440a01080c0008031a07580f060b000c40146143d4000140d58500c40c85c800d807500c603401551403280104007003225030f170940603565108103034001a008a01e403402c0010000002401a01c400d04000700010b592000f41c80031401d0440f58444058480342d1140c044c50f540d82d400b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 991491906 1250 991490656 991490671
    0x607060b18012601050705160c052106061c20040207080d0c0c02030714130e011e2d0b120106061b020a03110112050907140306070818071d 61
    0x1100030982c0056018401d0501030031141d87d9580c0b410358072150321012120000c07020360320b1001c04400003d00d655800c0156400520841c02c0325281040c1001550a04034024000347c0100101c18032214254002503e0080b030950000c1103e294801c45a5480c49070b007801180d040c0c00500c0040e40505100d01700c0701030044002050024406400f40b02c1040b10741e14800300d0000d42581c0114424400813070306100303001800c48094615015803800b0821581078451120000c1f280380d545000c843c1c0c4040c01c0e41120802d0f0742100c6c90038042040107840c040154a40c0441070400c069000d02c1032400300480f5080b28000702c0780140300013020b21184002b140288aa071103038101103041d0300c824849004402125021441c0c0060400b010345186031107a00815100d0025141042118554032090401c90301c02c2600540141c001003040301d040203480b070810705100c50054401e03800b8000b00140c40d9403106149500200103603001090b250010038952400074280c201d90503c0c803407202c0e020190000c4d200c0300340c0b20b80758 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 991493156 1250 991491906 991491959
    0x50f12150f01180506030a1e05040c050616030f0c200918060103110409140c1003020f090d1509050102131202030303012d03150c0302090607060b1801 66
    0x40c0c10065a64030740e1100f2001c407085040c001005145081800340d42c4c400000310011138041e04886461091011064206426941c0c0d03105110a100c1c04043e40000307031400b614101d1a001d40d100e1a80c1c1c807a41c10110040400c0b280e1080341010601c140307001e5103050b5200c440b40381c075203078441031802410480d00344040c05180440002012004035201d0f01c040402400301030000c607400c3d40c46c1c901c4014100c400c0b190b0802c0d00c59181e10001044030042c02910303042c81c1c0151003c8240d030010400034202c2102c0c0f1104050040c855040b4100b07100781102d41e04642210780100c4512245000310b180824035150381c544a20b400e801500b80007042d001803034030300144600048402e8407808030f80365038828100040e4159000703000520441517450092400b50001c40070308400481065400c03880c4060036002110701280660b6004144005c40c003801c0302148541c101903003030225900200d0700902514101900c5151161400c0d1202d88900b680028125000032480c15030b5a15201d00e0070150008101c10300c480321 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 991494406 1250 991493156 991493179
    0xa022b0e0a120803041b0f060206010e22021909020901030f061a030c12010b0a1e351303090801180201030f0e1b010912050d050f1215 59
    0x303004a070403401e481c0c0310765155600082903101c900103a0402002115a07100102d001308212880090301030041031050f00200402e070621300d000742070010690080c0b8028400d1400c0c098038103101441c0e0100516840b85181c20031010b0b00004080044460808140c0c1c00a0032002c12408102e030001c01702d03c6004c0c0c034144110030400c030341030084030074a104211a540340050340c0003d005044008641002c2c402d200c0904100d403005503818040b00030b80c446200050002080410943c003d0070300649181c070000701000d01820401d024188126500400d8444e0b0401c0d0030020010b1159031503a0390145001030701007101e01c0c1103c10340011925030b034025400f0824110300014251414001c10300c110001c0103c1c4d0840402950045d4050064603090b0311720f042d142d4840e803840000c10000f001111054654605040344050000340c03190348541c000249800c042e2103040042600065881f01c026068508595942e2441200c0200d6002351600e181c1d00200150034412443c2080409190480040b0b41c45142c42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 991495656 1250 991494406 991494409
    0x18031d010c0503032214101109030c01050c0a0605040b091204060e010807050405090f0103030311040806131a01060804030327021905030a0f05010c0306030206030c0a022b0e 76
    0x400c001c1004186901c20800540c0c40c3c91101201c0c4400d94440344d403000191207940d02c1c5641c0750300c20a04a01d0580c840f103899004144a401800c2285402c0c4800501d040d5070000460b490340c134080251414010002010746031204100139051a01e0b8000ba82005241081e07d0128440c21090f0780200c03061044103060300a0480c80c0781100d003140e240740c5848d40c40301524001501d00600c001c101c0c0041c0304080c880010ba44e2510001d05124600c1b1a404032000d41c1586400380440300010010b0510260510050101120000b403c80d00700e504c604545505030350030f03d84a4502c000da0384440d900440d07044000192250001c103000d010741d21985041c07001141c10080090420b006041d8104030101502c1007002500f070150302d081d009080144c4001c2d0311a29080883e190035241030f003c4407200c5022440360240042849800c500c2542458144026485c680000d030040c0005010035482d9100043c0741100340c1d00030040390315038498034415070781c000500c1000c01c0e0003e024151102e020684000704039007035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 991496906 1250 991495656 991495667
    0x5010608130605070203070b0108030306030f030c030703080a091b14010c0201090303120905030c07030c050d0209041403040302180406050a0902030d05390708210702030118031d01 79
    0x90710082034000d01090141c8074840903200151074503040d40000c00001001c6500072580c503010744184001103542e400d00100f0315142800724000149107400a2000d040d4640b070200407a2030740387e003610340000c3c07640700c502e104070040a80a5000b01911048480203080c02c41c05030316041101c80c4400640317865490783d8015904000f50b400c0090020b40310505c20301c0000d0140c2c48400d034010146600050f55031160356680e240d584016030124140e03100710410000c0040e05c840c81000307040c044c1c580300195040c1d940803403030100d40584000c20603c2c1324803018040131003c2003990000e640007072000b180d45581d04984402d0700010303a400c6c1c2c1c1250401000a01741d25441c01460841903000e802031500d003004090460341a004416071035001001c0312410715004451040951070740300c441400e99070003c035102030f00346098410b03800200c50350050403540f134107002c1c110580c910786d800c905002c46e900d404a04c0068010032900141620407400003001c1e00c14564058000c51011148a45e070350100310400005469 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 991498156 1250 991496906 991496911
    0x60a0206100609080c1e0306071805030111030f07050f040f061d010c080d181121030d11040e1801050702031c090212030f03042609042706020d05010608 67
    0x8041d40220400c2c5980c1c01c0c0303444130003071820302502d6005a543d2004000390420b48d064a4010024600b22507550512030030400315001010101c2c002c00250340c4001c40107865010003040c5e02840528000080d007000e0152041301c905a0742c1c540a641e403992107072822001044d890044000040340b0384e00134a0180300115984948100507107d89840b03151700da6440d1a50780c03000e04040300b0f26032a00d00e00c1081105100c10451943e10500c0d015603982800320038050341c500703403002107500c4a1b80c074240c0d48511072000c41121032210b0881d002180030701048403040340a2080c4e40c01074032020140c0081000c5441400050f86011102100a02050715080c104076920300407102200f05070b042c110031070340168815034041c1e940d092000c0c00c010000c461005001d1b085400004191a041100108000410140b00c400103c40102e0300c015005820031a00390101340d00807130a4550146a81e20304110b601001c2c0d00d0000100000300c013201803141e83d6850f01c40f001e90400011f07034803824181400420524007a00c1841e2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 991499406 1250 991498156 991498169
    0xc050d062702060931050a0e010b18040303020f04090c090b0a0906030e07150c030f0206070e0409051e070f0e010e2208030c0c0609070e0115050405060a0206100609 72
    0x82c00c20780241c00300301c8488403160342020980007a045c03441d80710603a69840380000d0420000010145000b083c5402607522100c08481d213070b454a10400001d565908001c450100e00f6807507101e06549500e0140c0080c424440b6800402c0004100010002000e400110008040e9614400c1d003d07515110603020340210340d481004035100d60802c1c130000384654881440e450003d4101c600039903aa43d0842000301403842243d00261b0240e41d0a814180c00c40358041c80c841d5648014030302c0d440c03c030000070000241c0484c03040c8a16111003500c1c0030b0060030013100b05a1030440012041007858821b200c1d513140e090788034501304904c0380080060080c03403106900f412540d2101e603030004c950382c0c55101500c04403841805a03517076005d06100008941030030b000c0e511825410705520341d41c41040d5038152070844014190000d0790b01c452002c0c030016480080450455281c0504800e5071286800250303854092a00041d400090105440880640c001501401683c000142620031902c5410407504041180540c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 991500656 1250 991499406 991499419
    0x2161401061809060b06070503040f0f060e042a0806180f06190b0708030103060e010e0d260906040b07081e070e0409060e0105011706010e040c050d062702 68
    0x2c544490705604148501d500c2541d0010f0714809000000380c07940c0040e1001d8909902c00f040c01c0c44009040b2132804060040c2020703148540381f03421801461000310144450180344c41703813480081e18962074140c1d084c0004100d00d85810250341103008111440407145a0312076800c43ca00c000700b20b050b00141174054584040c01505a03900d10781806103c2c070702d14102d0784001c8c110b17410006484083c0d00180c100140714014240d50f0354507505007c800e480e0182c0c501c0d0486d0749444034005000c0c00014000b40c4104540c00c02140303148451900404000314030410054001c0010108110050003190552180744160003404842d01c480404a0304a8011210760345070304180034518105031485902740b47d00c1182854a400d6010001000c81d06881010b0000c403116511020005c0080e2020300905026040303000760008081c0e000301e900360341d510061080001c09185080030500744060324042c0b6004c2c1502030500d240842e02860309030f004203a4900000d040044400819020780041140b001c825900105076 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 991501906 1250 991500656 991500689
    0x30515091b0319080712050904061a071104020c0f030706060e0c070b040819020a03020708030a09030f0c1a03101212030f06081209010228030c14010216140106 70
    0x503070f0805059440c01d032403039a010701c0380b100059505080d4044415040c2d80300d64440b0113040503c425540540c11100f96010006080b4202000b00c0066034981a0000da2000c01c015003400824024451940020320754020042e1002070203100000901995114140404c03246998060951340c4090540f0030800100c401c100c10000300e40410800c0b5042801203400da80f030300c1c248407003070720b081d82c0c041c42044056080042100b0505406120342002048920301452815001c0070b802054030390903010060108103108040350902000189441c050244480160000301143d490056603400031034034a600901d0010001c55412840380030000042c0c3d102005981d5180600019005803503041e114002c22640c40c1800034040e5820402e4800203680902e0340d40d0b603000803c000a0a1811003d08601100b41c0440c400b000e040c007000000c0841501803800c3e0006144607d400e208141520110381c84960000c500c0c81400b0481c520201da4461040742000b01d0901d6114055003a604c0c10b1003034050080040b0341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 991503156 1250 991501906 991501933
    0x60f08010b1306030b01051e0306070906020f0c0a06110f0a03031d07060815040b031c030c030203061f020312090d0914030a120c0213020a200604020d0804030515091b03 74
    0x1002c0c2046001d43c40e1040c074000e5123201007480c2400840b180c41c0007407070019041000940500c410345000200a01074000f1302101004280f03040c1d418071603002080340f074003110000b014040c0500d4a221400b103040d00c2454a5504004000d08500c9900c0d2601004403541c40801000004800c1d04948007a216001075503034524210105048001505401503101d60f000e402d00c1d0340500c2031031441d02035100003445411904800038215001c140701d09041c540304100303000b1070b0b0351000201251045040e00c03502c0181c2d42410200d041d80109440740e5a19010300040c080410800701d1040400c081550b07400d41c82e0f5594940790005041314060041d016000306034010080f821a01a4040c0c010036802c202c0d680d0340031540401c1d034081c40204201e440c2c40c3d010a4490000f030b03215203004011010703c0034190050303400762406601c40001400c0240b041d81c80c482d0f480100103015095600a40c0c016003900e60602000200234180001196111510700811007100b109180b0462083e150721009802000301042039034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 991504406 1250 991503156 991503169
    0x906090b010f020d0e0f0603040506101202010509121c0302120601170609040305041e030b070801050907051309020408060a110c03120c120709180603080913060f08010b1306030b0105 80
    0x74146d401c05203d189102c0f01c0d031111f100850103170b44200010003040c500b00030b048292203066040241d81188000344000943e03808015107503021802c40700d40d0030101d000c40020345000c401000d641049503079031700c856007440d4041d800b41114080120400d001561050011070f83c28030240c3d10200f81c00300100c0131501c14101412616446403183c20300c9d45c0391a44405e00312003603844030500c004c1400c1001038180304101a4200880d044282400c11503c654103180c0051403054006014000b000300c0403441d03c019654482d04030f00103200b0200219034580e2246402c5441d0340e0700716a40c81038181080c2080c15050f604808483c001e1480c4070265052240458500c0c0400602601030a506c200074801c82c81c00a942400c1d075801480b01391a07a41c40760b482d141e1304400d40303d841c0c080851581e14241c0104041a01441202d111000807200d902c2c1c440500200c09000f058240c00000002564620110390000305620400584104655900030400100d480c80705035401408010091204840108450300b4882e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 991505656 1250 991504406 991504427
    0xa0207020f06030a091e021008101203050304050d1e0f0c170c120a0504060e062106010e061305040c170f01030210050702010905150d02040906090b010f020d 69
    0x103001e416a0710201c400529260825941007112a688460342820002e220b01e003442003162a44181c4450303035203500082e030a404c0c00382900c018050821700192500300d212a00314042c20411a00b04454409030a0080540d0000c58080b9068426005401c1300e1501032b00b50030380001086510b20100c00402603003280c85200e140110340501a03180900c0300016403400f01c03240d9114240c407000383c0314203c150b005858940c000d030000e40140780400c5070500d00c0d6030040032202900d110b400c4ca2840b04200310045080d0340f09038000000c0c28019031052000000115030443c0c05000260790361069028a4000c02800744201c0030f110885044903402003060341084c0d000f04140c012107040440700000c1000c031081c0c07030700c030101c0d0800070b21118000140110f03c1c01a10040f035240b01850320300d0030080940e00291119156010b182e12843c030700310002c5080c500c08e80c00c0700c08000070118150348665075030000710060405405540c00444c18001d420605520610700180409801c5c2d00404265a0340384040d2001501c0303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 991506906 1250 991505656 991505659
    0x18030c10110115082b1d010c0203010219030507181403073c0b0d050604110c06060a080d200102040b04030818040204080a031107050307030b07180501080a020702 71
    0xc0e0303880030b80744481440900b0014410300010340000c000491030b00c1440141d0f0b88a445d039501d004c40e228038002d0f6200740704159061107131071aa55040900001a120601c060034029810f600010391040b0f90304c10404440c01000450f1801c4c041c6e03484079042a608040742003100700030f00782450000c0241900c4030018003261000030381581e01745d5442d02880314081c09501c10b84407441c9810303209641454207070440903044203400420554403d003000c050001911501d90071000c40c58540000c101e441d6901c1d88903200e00d83c0300140182e40d9070400c00e001900c49504070f52061080703154140015001c600451415030040899442d40411340034082a442d81c40f203100f42200361994240000f007000e103020002000618011310745140c0f01c032642c0c1c20208140c0240c00c103450189006104c10040d4150000d4011481a41410106058601039248070300e440c0195201d20f80c103114480300082802128041c0c14003415040d503441d4010704940503030004485640c0310300750000355150300041803885140c0c0a091078610 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 991508156 1250 991506906 991506911
    0x1a0306070e3a030207050d0f08180a090e06060f0906010f020a060914160b0405010c0f0f140d02010b010f1115160e1906050c07090c020318030c101101 66
    0xd64034802d044040d40c4800308481c1c080d0400300307030141601000368500410003210030203007150b03081e510000a40d040c800010005e4001041c003124404a411600c1c0195001809103000c4580c0c50001502424007540e00c0f008030701400c404038486081c1a048500c02880180404040751120401110000e00c64200340f011805800401c00014407240940d10b43c00d405081010176440f158044603060900840800d0b040c0c0f042d01c0c4040117413811440644003280c00900b801004840c00d4140f40412900c078910060841c90b610801c841040b22803100c980501d0382c000c0880d038848200b05e000b6800c895006440c14080740c40b866540c0344861054280c000c50200440544064a0b89403100d100c5055081d5010089000010751007014030380d0020340e0814000c03003164000c440e80185443c0412041c0140241f0f000c0050000303107510280d40c1000a4001010040b400300015029004020b450341c014032140f0b24070000d220b21081e0b184c030303000034445000c40c002050960070310790014040d84c0301c810028501d02d4554 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 991509406 1250 991508156 991508209
    0x15060702150c030301150c05121615090314040e0a05060d020904030c15020711120111161109060108131407030c1706101a120a1a0306070e 61
    0x1071852024241d10030311000115125410581c0c842c02186410900d11b0810041c0070030741020510010360010315241005000342d64103500005800710700d451440141c1119018601031004100c20fa20200c18a07000e60340c0c2441c0303071546400100152240f0312481c04155514804215a10700c01c2d4009600440c00a141888000e442c1c1d021a4118808450aa01049188401d20b0030300044160f400c0714035241200440c503000d41d95680f45681069408818064005815446100c0300258024081c1d2000540141d407a0f009483d6680e108000070001200c02e00c00f40c82a40c8014144034140a00a102c141c503110b04940c2e61850101003c050f8210564550484070401801c8100a1044d000510300031000500c61900740599160b01449058049551358005d1040050910070213072180141c80b0384160083c1c01c2e9400c296005014002d04506201c5130140d4070500c46c42000030350000032400d081c0c18010722040300b0702d800c040c0c86210888030000031980f20840e601280c502000146414a21139105800c42c4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 991510656 1250 991509406 991509439
    0x17010f0905010525052b1d0d0507030507150b1509011704020307030b0702150a0e1506010909021c05150a15020c121e0705040605060315060702 63
    0x100e21010065070140d40d0340c4181301e0303034041241240d0b400603405080e01850009902005245214851444c0d0048407030381031944180040c81003403d07620030071020134014188031500d080388104017001002001d1103804014240d032400b42058900c0c254040e01d0f4035081904a484031605540074401c0c140300705940358251000765481617282c001324118103c5568450b400b18002415404100140032440c8204404000069a000071170380140d0b603000c55990f000d52a8144164a404000000d4404c104c00f1101005080311256100e2041c6030060002c58a2402d10b40e61444003000c001c0d41c80c81c1c001407c0d814140b00c2184e0719002065004000f100030340d5822540b001c074108031041a12200e20715110350340c90288901e00f250342e440c00707400300d001400c01148c0f44500c083d5030341c5401c0502c140969034100000501040600c200c1200c0d6440c0340302a20107082222805803150f4250059078412480c103c00030445050040c1540d110340c0c2c54100403a0180c0717a610030840990080e01089030b10804050552078076 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 991511906 1250 991510656 991510661
    0x2220f060f091503050c01030b0612150a0e0f1b070804080c0f0303030c120a0e011505120f030708090d0c06030e0c090402090402011206120813091517010f 68
    0x1460000d810001c194180030300035040d01c140501e4860616411501880412000301e900c442e041c03c2400d00140340c19201c0003044090184050b0550455100810081807c5500307c0e074242c8013038101d0380310012030f0311145141d141d86410f0741c5071003010420100182244e0055901d40001c001c0c0b03512060305280761903841d240c4a9116400005941d080680c4901c0141003011401c50940c034114041d42c2145000341d003005aa0080f40c590140503803482c404150514150760003c100d007a40b0f60300034000d20001c100180068007103449018003410120301e410041030701c00b01d8143d4101101c9805107140032415202c507000c9810514810341e210b20f045100d14001000030440c80d00503c000e0700d012403410302400e03065003410b6180d2203050040708560101700044ea5124205580141c2c2420901d4440d1811440e0b040184001d40000a401d0b5800d803000d0203016034000a003800005400715890116110a8850242e5a21a5200200341d058450a016041312280d44417800f1500e400009401c10341e44c1195020f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 991513156 1250 991511906 991511909
    0x11010603110a050f0102060c090d140c0f01022805071e061202070803070c0510020a0c05010501170c090403122306041e0c0e130b03150402220f06 64
    0x5800700089140001802d04060a40c018681256408510129071002075100d0400406c010100480016a88519520304580704511600003010b44449002ca150f0a542c843c02944131030f104030381040b900b50341507100107800c00d07038002625015103500d81500f00494201009001c1128603008144003c03138401c040a00b04c280401140680090051a018006e80018001d070b42443c0ca0600402c4101c2c0400c84c8030b02103a03040400ca280080480c0f4242c00d0083c01c0100c0407410904281c0002000d1000c5035001640340c80050090008104607680d50a0b849186903000700d1a00b043e402185945809181c03051581e54070a0080c101903c0f02c12480c0c21250448222105100f0901e50048810410b402e01940c540d6020310159000c1000300d9010000d5207000d400f1901d2882000d0b121813913645c0040c85001c0c1c440c545807014145212000b143e40003d00074080080f40d9a0082c402c0701500b144000600305490701617034000d01101c40141c0c1c09100803c0403030261a00740102a00c903c09114010780c240704100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 991514406 1250 991513156 991513163
    0x9050f22020d0f050703030909091106030601050d0912090e0f070c020303070c06120c0f0804060b0a0e0a0b18070c080d0b030619060b0703021c0c0b0a020c1e1c11010603 74
    0x845d034114500a0244c2d40c403508075800d800e00d44240c04000501050302e130b1116900490701c4544907503038040100d54500c1482c1c101070b040c0b41080700e020108890002059400c3c81543c5503016034944861520100c4942114800f80605201d0041000d003070107100e801c2c00160028003070320303d429007070b03200e01c843c2c86e103681d010b040051007901c41800c0b07400107032080040780c02051500314030540319800010806e2802401c09001c3c035546681002213a516a26800001c1426180600706494000b16185c02808515200d5024160100610100b003103011259482505242ca60202c145607a4403030302100d40085140c09415955000802e82d03030381c0c04000842c0300d148070584004020f054001c11000b07450705030707005050004040c080c420000340c0102d41d1848080703814170780c510a41400d0204071144040400701900351607840041c04080d298540007850f009401e50f0440d50603400c80c10b50b00c010103010301d002080b15005450013540000825004001e030f0720142c517007e0b400301c009030b000702d0840301c0c50360084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 991515656 1250 991514406 991514413
    0xb040e010305010c2607111005180303091e10020706050601030e061513180305040f05090c19020c041a0f09070807053109050f22020d0f05 61
    0x400400000b4013802d002e10340701d407900b54030340018000c94041004404001c800200c0c00400014001c2c2e1103118501c4078105440100c400500078132a44070000e00e003c0d50702c503c420101c1c0015507610b03000001240c0c040e0504d000180910800c20301b0680b0400e40500b20600309004401582880300664009030000d603000380c50009260509100150807541d144451114913048201040355101070f80e09440d9034090280d526810000c048402d1100070002440744d0011100500300040a050b8000060b209461142d258201000e4462080003030801e001c448005611030200000e8030480002d21481c1d41441980c01210440b44181c0000b8066902201c100c40803840c000c146842c140c83e1180105a0700201a01c0c014080d0620400c02001c1004c020106400d0090008010724034400200e107a00e0781440c0700e174071950120321300c08001c01c082c0c003688261003003c0d05281c0410500e584911a1600480700c4410030310300030070000101d000351280b03600180c0e072128000040c00003242400050b0310303e251140019 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 991516906 1250 991515656 991515659
    0xe130f050a2a06051b0102252d140313090213050618012f100507320403140d11031303020f0f03240108120d09020103060b040e01 57
    0x12110701107500b0100341149409041003065541243c2158031500884600144100300d08142c54064400c50140540003500782040480c1c0c02d8849040b00a4284580d40c0c1d0001d10349040c80c00c601d10503010440325a45040c014080300020820010f03031550b00030040c243d9040c0004003c080800d046e460b4000100141c0005420707403441c0c1100c20b008003510040300d1460901400080161020704c141c4070160500000084654400d15594108109a110102480d0078010720021217601c41344400a042c05807400d20011482c468060651401c58540465820310001c1256607200c1c0212561541480a110204004004a10031035180101c0140c0f480c02800007038003403480205882c82240d560f101c2a0001c0c02004c0102420684800460b90101d880b075228456400000381c2d074036180c00707545a1601c0780119042450024031107915424500c4415555281ea030390844a40f9400801c5104a55200c1008100110181640a803111a0041c94001140740d1201d0b2002d0055009801c50b81c42c09206100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 991518156 1250 991516906 991516943
    0x709050607020a1806080d03230a153503030403141c291309020f0d0f0204240e180708030c0d0c0b0115020f10240e130f050a 55
    0x540681070b4074a02044442000c1d0809d03203d0030a4400500211001400814001d0882d40c12180c0c80c5544900c4464550b56078840141002d10300c03901460200c540841d62800305c01050340c42c0c80c401002c45000d03500e0740c1d44139901101d802025100106014505110700007501c01c41c00c50b420501900180700040141c0442c0c203142202200c00800034465031884204a0305403201654040108072640001c94010740ca80300050a5400c405125500400841390703107030900010040c071982943c000e40b020410136480e20b0507000c0c1c0281c2c0e02000408000702c0641007080300340c84504294001c80300b0035910b00703c0c2c0340201c40a09140103640030000c254000b207079842100005001c0740442088606024282c0051030f91051401a0305104956400c1d802040903001d082c000c0c040040302c101d40350165041003040050300300080c007203041c810b03c07007844a403902980c0e042141c80481c140c81036919006041d54400c00d5840c11000044e0f001c6808040c01d0003103000040d030030031500c05240d2140e021040c01c60140d40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 991519406 1250 991518156 991518163
    0x62a15090a0507081c1202160f060e0a03140c0a0f030825090605090301181202010c1b06090302100c03021c1802190f080d030509060709050607020a180608 68
    0x421400c1c0b1900501c2c6015845e071811403100c0440200d0f410a910740841c10000e5000170301070038070100c41e40818421040c2c108441d0b0b0046a01c90703440b580c0100254441c29203c207135030f0b00c4a104001c010450701e420070005e0000c40c1000e03101c16500b9400f1252407203c1e40d034541130512003404003100401c2c145401e000f411182c0b14002140810910340098242880c150001c02e908468890380c1c052050014103a069a1030079045280c1602c0c4404490800801500d00150b030406120300300c000552030520b086001500c103500c0c050b4101184103010300b90800075100d14000304544141182580328009c0340c08010b107020300403140200e03002d880040c5c95044a0300d407600c00a0880403c1c440300c501d01804031401d4032000d040e928075160152032402c00020249060815243c0b20b80106011906c2d502000809400c009001000e088a070750701071100351070b80c0c000030f96a00001e80303488001c210b100e0300a10850030100090001d050004085901066494080c2c811a40000f0b10302c00e0740c00d031590710034017440b1400c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 991520656 1250 991519406 991519409
    0xc0c0a0b0714060f06062110030201020d02010903080f2505090f100f120209060d0203270607030b130e012c0309040b21060411062a15090a0507 63
    0x5000303083d641c500340907100d100d010010718451081e40080f800307002c4200c00c035110a484c1c00c40302c218824541030500c09501205454401207005100f003200e202c2c050b40c41800b41c0f1506c140d140e1101c10b416100d03516072124481c0300521032000c1c0c607032003620300410b51403254030b000b80c40440c0d81f9025518500b80c0280410900c3c0c1d000c01034080c11013181c030301008036402444509840410b162104c0710170300038441c0c0c1d0007078401d451b01709910540118404060041076801980100070000490317403801d900c8c0307080350409145449003000d00c0c1c2103500000c90725406a0080702c6d55903002040220864580c140040884150a061002c20783d1340342a403031004421074202c00425002d00801809081080140d9541c030310902580c640125251180e4a05985403070030410300300e014101504a21101c02c0d040c442d601d010403101641d034400208005c01107418018201c8500c107049544415508007c1507810420701e0701c020200ea030921075141c008218203030ba00c82c1f5138000c445010281c058820a800e1891522800307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 991521906 1250 991520656 991520693
    0xc1302070f2301270807020f100504090e120412080d1803110c060a0f0c0624060903050a0803040206070c0b03010911040806070c03091503050a0c0c030e060c0c0a0b07 73
    0x1000703444d0102c1814440003415181e4440400d40d0745502c02c1c40031030703c400c540c3e844460308000f401c000034080d40d0700a40038100384e07640d4000410550341a44545640c86a48003184000c1590421041c0709085200f0700511006000d80f0b0303800c1c40c000c2d0100c01030f800c45000302480301c0000c414050800405038000441c841c20214100200205034490000a8180c414540318a050091440042250500444804103c1c68010174100320104011021000d505c1b44005056140800c1010200b055070140c546003003540d030000000c00780503100f95070318030700c1f948068000e9034400740030b0108000241c40142a00701411074109855129494406a042134038589040c00d002c20708107002c203003c05d110000d4599400140c92409801141840c10140c441c0701007900262a0045801c1e007a038071403500f5070086c0c1d00504c50b41c041045174082104c804c94091950140040002c0c4481c14454000d00d0814041c1102452075810b4400449a4400150342612145e0018044a40118500741402102407030040f51540 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 991523156 1250 991521906 991521941
    0x327030102130b0a020c04240b0c070306050a2a1d060702061e03040b040209070305041a0907090204030b040b10050102070911070212030909090c1302070f2301 70
    0x3554042c601040c038143c01558900c002c0400c040c000d951080081035403d50010700304015035900544808041031000450460b500c1a69034009080e150085c200c0e61500d450101808140e13042d072782c843c0c0c04ec0c140500f880311019184d040e60701c517100d098880590044102c950807200b4000131140688440c030b24105010f0b0280b004050141c0c030340c8408003114542a4110360180e40d80140228054034440c0305541c410704070802004000401c421035003194011802100c0400507a501c00004905480341294001d00003d40014200303248007146007210340120030001036507071003911180c2e40c500300d8000364401d4517406600414041408603502000c0c1d0041d10440c228600641000d0010359601c080d0700c111520a03a8940c180d010704a500c800382e0f1422070f40280241080340c0359151480d070303035000345a41921503050080031598030b8500081c0c40103103100241640e6110307201d0f82d6200000b034001e40c9003641c108460100b4600000e085c102400011400c028a030310341c1d5142d06e0609800c6968514201c01900c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 991524406 1250 991523156 991523167
    0x105010b0a0903030c022110391125050a05180a0615050405040e070e060f0d1b0317120621060f180118060e0f0327030102 54
    0x41e8000d08000c2602d4140c185141c40410743e101059201c5e00d00f5187c60017000403100384041e40c3d000410082200b10745a001400000540b500d0701c50000ca40c840390a028800c1260b080c40b480140888500c2c0c5000c207030a01e05482c07a004086d01d4100340745070801e9554215414218440a15562591405840700742d41c0502c081e81420b0100e41d41d5251848041c0250034010b001418090b01900010040e01100b804040c03a2410090301030309641041c09100d203c0e6050480300084100005288001c5484510a01945481c0d06050001d4041d1005885403c68501100c6030f0120305c1c60103807200f118501c1c04c5d2101d412407031400c0c840000c50120b81d5102050b101081035840c2102c00c50800e9801c0036044441d030003005241040341c60140c80280f83c0d10024003500007004049007102c40f21500c60344a502014080c0100010881d0880700540303012a058160006c400c004a42da99101964800e01c4800701c8002440c1103a40502c1c5400c0710002030300c000d014020020780c0c03805000c84400c101009800030760401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 991525656 1250 991524406 991524427
    0xb0307080303010b03010605131502060406061d0f070e030105100825090b06070f0f03030b030a21091208220506070303150f0e0603061018090c0f170105010b 69
    0x4d10040c80b40d50704001d008274000e0301d550500e02c03524000300b2008003200050010118007944500382150182c42c080d1401c500042c000700c8903107850344403c0c4485820160b41d52048100204454064a11010805144600e58180d14244074a9000b62900c081d4810070600d090a40c501c0d0001d0711500c00440000701c0b10900420100f00e1540040d2940c401700814601c012402082007401400f50180114050814030760030300a041846c4101c003030080c0c0c2c003802451004802d0660b50a07020317800030034009001d03122544504861144141c000564500040c1050340c8010310b5140c0606020207554501002071020008900d05116400e2101149d2000400608d00000100da41c014004013070141078881250b030400540072500a000341590300d25000d90306403a0300b41e410080070101e429a02a100d054081f60b07080c00b03040c2408048501032080c400322003020350402030181c00f03410b108681d1100300c4100402d07105c1d81201d51402608414007080000001c070b0190701e080da40180d10259880c4410003000f20306 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 991526906 1250 991525656 991525679
    0x6050a0927080307030e101d01060f0b04050d0c0905041218050a060e1f0e030f01140c13030609030329240c0307030e150a0c06090201021905010b030708030301 70
    0x1580c00c5c100019521101d1a055081000031000800001d11300415684c0542c4075405450329a81000001c20440351980c10800c0c0c2c40d041801502d4040c1d00c14082040f86140a408a8400b03500c50100b8031041c1c0d6681e6803e1041d1441554200c8220210040000700680e000800da4180c0d44100c01b8241600d1808020405060150140408004c0048030040c19a00c81442c6c00f2080c803a942d518410f05c40e05000c00600d00d5408040c694482d0140c8404659940b0050103491110b8a15010303280140d15444200526079201d04002500841d0b8040300002052841c451807024034080d880205010090000b1441c40008445544d010303040a01e10495003525004034440d1810308060841c00300300c41c0c003076040c4040d0140f8030b401042440005240b200300342e4800d02c00808680240c2d40d078084c664a400310440a402000d2270400003840121690011418030b03000301c40c00134010b0058810000802c00c8424880c14048410394040e1b440b002402c185050410038900240b000c400a07600795410f2454415a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 991528156 1250 991526906 991526911
    0x3020a03020103050c160c0501020f0105101509080f10050f0712050a02040504060803090a060503010e1f051806310c0908030c0601330f0306050a09270803 68
    0x101a44c40b8001018681e40008440c03800d4041c40c00d5050308100e0307140c0032100704224000c19005024010301c403100000140125030241c100307555414112410f141c0d0520380c41500d6488042089195240020340400510802001b004580090071480c441010b403c4240c54024044005108420040240c5242d00040d50040f2609044000c1030989406c0c44150280c0500d070001a8031500d0301d5000222004e00100502d120744d0281c6a07074005960790703c42600e10f0f001c01d00c9040c01c0e422504000075840480400c90b078885644103444800c6280d190000b2a0000468a521021042d00602400310760710303050900c108070320700b5840d940410402d00c800e20b4a00f804040351300c0c03a0141d00c5600c500c00d940c0c0968030460217002000100d0f0b4556080e081c845a03035010a200d00b1544402c0920034000d146112056034080140c0c0303980c0380900140c03041c411150f0851030a040e00816548441c041100c1c1d8070200d4100003030021700c4011844101c404510300c40f4003c00f138007041044030420400c0c00010b14060a036507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 991529406 1250 991528156 991528159
    0x40c060e0d031b06021c0204051c0f032f030a030b041e0908210412170f090c100203090109090b010e150c0a030c1208010b030a0c02101401030b0c0403020a0302 70
    0xf4501a5854003202900a0008140000c8901c0700f180240c00c1242d4054012102c08030f0341200041c001c4034039005a04c9400d54040c00340c50303000c0c80b00d2000c45d014500210440c5409003070b200007800c050201214141e4a0900d59820760000204440051341c18040e10480f010101c404010b0918403032403441302c2060341510714048940380d081d00400c5c000308105507008004058201040c60300c00014030300e5440c00882d411614105022a001c4541e4403603504140109402d1502140584402c908110356a03001880c00ca85440384809180303940d100d8650504042816400035611080603100141003a400d60300085150f034500400b05105a9012103003003242c010644030f40c0c822440c1e55059050501c49e500350540d00f032003640f440b4000c1660148011070b115008400d500701880780c6000c1180c0114080c0b143d644044001d01c00b00e41c03800301e164404080d440c814012560101c04645424041d00c0710741c4a44041507116400410501014075081d50f0b100c1a456290b0340361070700f1039002620343c00e880d000c0030303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 991530656 1250 991529406 991529447
    0x3060c27090902010c06050a06030308100602150a2306100219080715020406050414030c10030c02010e0601030b0106031d070e100915081209030c0f01090e040c060e0d03 74
    0x1842964080d1456605d8950408000d12052a1400c901d20240500d48811800143d440d00042c103c86050f80c1c1003030507507850358050100803100c801c030603031000c6003d030010034001e0703542c0c481c000c542580c002c490b000410b5001402c1060302e0810100415203102000440a64120340e04030a1820209502c4a0042d0381c0402015214181800c01c401984541c1e0b070b034000e51070310003e0080754458004014004540921030340403180c400d10740505031541200101c1d0354211030441c0d4a04051070081d0800044215984000511129501401c41c40c0403000e07442541d80414640040c48a585d143c020620114040b408410014032485042540c0d0081132042e000c440d03e8101c017148002c8150310343d880050010340d2052203180d50510503144401100d2003461000d104000c200c01c8600c0c90002954600f0710000c019103145804481803000440780382010f40e04111000001180c0310450a0850b80500e00030240741c0207840c144031028050000114044d03100d8070301007202c44c00081d48031b0000300c840c0d101c6d42c0b0b59 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 991531906 1250 991530656 991530671
    0x2a030b04060e03040848041808210f0f07020118030e13060501050403111219060c0203043c06050c010501050f0d02090403020c04050103060c2709 64
    0x8100401200d140b41040d0300000030006000d0900090a0300303600001c95280d900741084080800c0019542405103051341602c40407000302003404581140c50003000382011607110066000c010000442d940100c407194404290105107500d00c4c4900e01944946a0110a03a0b0610801c21441030900801c2c2d144c0748090480010002032007074100c4243c82c0c0d24140c480c4024440341c0b501410000303442440602941e418901d440d203440300c50295004549040e16114a014119160003040715082d40c030458011642c01d54130164448200300001001c1e01c0d02c880205d00d410310303290090940d0106e44841c0d045600c1171205101c8018240961054052007280e064140d503038a0b40c42000702e0102c6a1103250085903908001182074000c00106441900d40000704400d030380300c10030000488080c1842030382140d031003502900181015204150018040e0040f00c0580a4510010701514400d030000c90320340391104c40c01a5515007001c403203100c0ca40e241c0040d10100080f0301c09181d003c06640b16281e81180c44045 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 991533156 1250 991531906 991531913
    0xc0c020907020309090112061a0f010e040b0a06050702120c060f0706090c06080118020c0307031404170705040b03010c300f1506020706080105060f120f042a030b04 72
    0x1120413003040681034000e030390395410040c950921007840540d001400c02488485203030f1a4803040401c944001e05483d9120505001103a060307499004041e0010754030841624540d6a0401d200003d04503a91110b41d00c031500d106020706a4000500c03c100c6038410101d01c1460380c4c421042c2d5159081106a903174071840c0c0790404001a1100c04c10190203c540d1a40200f81e09600401e980e050314810201d40304841200d1002c54101d1003900e1414480e030b0014041c20001a2180038000c00f4407829500326420315450f070541c0c0d010107a6001501e070240d84450402c11441c2024000c90080000450081180c0341642c003003c0c240f0040c0070480e003581820ba94440c4003607022144500c407544007201c8100829503103020000000c08107006400000d8813004400100c00d40300040f10425180c543e6201d40142c0d02c1c000030b01c040d94100c0044007040d40410b00072150020350250107544524481c01b800c80303040c1400c2c200484100540d0902e0320030384007114030b0060098091140c0c0d008a9610140c595040d955506 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 991534406 1250 991533156 991533163
    0x403170406021f020f0c0a11010212040b1803070b120a0903080f09030c0a0807020906030309100302030c07020d0f0303050a1107031d03030429120f06040b04020a1701090c0c02090702 80
    0x5c0d110307120080414810640d043c005141034407540b0403004107000c0600c4000590752203c04440031400001d08000031700a9140403400381503240c61940c4a100d00051003000242051041c1d005000d400102081c584520f02548045517001100c90744204405640307a180101180b000400b101c00302c6944101165030f40e00c0410444070349901a0741134840301b1100d4a800741c4568804c02090748071f2018040482e55514001c000c44540c4000101001014180c440f07081e400b9410042c0450000e600601c1300001580300c0d1107041e05074510640049849104515001d01115400780460040a240c00c13042d54002200d9011505811380505054000b0320b0056a001030200d4004a015017501022400240c59881c104c0001c040801c886040312a000020650740900d0140d6407011a401070000d0100751030341101d00865402002c05000801c3c04061310001c142030f40d114429000004203a100c1180a5985860059025000c8014107120754081c404008110a03402030010703200d8142d050106600138001c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 991535656 1250 991534406 991534417
    0x10050f04120e151e180324070f180e04150603020f15040314070812030402030712110a03030f1d03060f13060609020a030e030901080f0703090501110403170406021f02 73
    0x400c006a581d8106105880049001400e098000d2089494403507c1d4000148071000d442006401c006840e644c0e03810844006d540b40320700c4001c0c400e0b20a8030340454000421a24040c0002c00c2c2480700b1404c00c1d1814035040e01700b40181100c054600b4a00780016921202c50000500e800c8803244005101120340003414420740c0d000a00d022500940021b280c0404140d1301c0c1106c44020544d90700407820078030503007070703110444009605800000041c0324140e00e030f41003500310034051070070f203001c180c011000f242014403c0d130400c0d070110700c4036071b039111240780e125a4100344088a071060000744c1710a440881c0c0c0d100c5000d003000c5240003d0700002600302c2200240701203031039042082030029a035120210802548610080780010b4140040750a104000000712807a556041c1d59690242da20141103080520001d042cfd5020541c81c0d11055021031f02c00d0003154180040c1c03d403455a124503626051040c29540102100705603001d01c82003211035004180c0c50740380e80c00d0019904040c4d040a040c00004d1048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 991536906 1250 991535656 991535707
    0xe030409061502010e070b0f0f1b1510061d0409020a0f0602011a0d0b0702120a1e0c0302150403020c10030b0909010513060e10050f04120e15 62
    0x91403000248488040c90040707007504660020000b0854000c00a80c0f6008540960202c0c600200123216060100030010101000100141418211002500d1401032030324407171100f41d6803210301140a0240b408052907000690a503000c01942c2c0350050142001d040c110f410400944d11035125503054680344c1045003079582c000d001c0e6800c02e0300c0340d184100141190086e00015880c10500303280c1010070701070108a610004010940001c110f5854801c1d0f1600104000118060009402e56410303142c005032580201c00d84549405544840f604410240e94a40000030000e5020300a4080f81d00440c00c00c1e0006d02804113807036540c3d698103040c3d1405030704a0600740c000455030340c00410b40740d1641c840030b40988201c078070202c562070f040c40d02340c26244d0642ea05c4902d040d02107800320000c3c030301380d0100e0542d10030001660089004003000c0310071104211171007480446080c04100800c051404451051052400e0142441e548500070801d000d00c080080c41d14503c0001c0c800020301717104601348c046000b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 991538156 1250 991536906 991536911
    0x1021e1207150b010305040f020618040213180203040c1a07151d0115051012050405060106081e070804062c0d090b0f0919080a0c060c0b07030e030409 66
    0x41524151082c0309040c018002030b03d1501d1201c0c42c540d0700c41c0c05035501468002014810308009a001c10034254041c9558100315086500d003841107444c0c13800600303607140110761500320701450140500c1403000511a22004ca500c1002040005000174074004107a900b02100d48508010740e0300e14180c84d01c208031010b0000302d11b000030300706924842c3d04002c0c013041e0100c2c03a02004401d5005a182620381100b160845813142a20a00c03890404000c080b480d502d0030300d02429070ba009546c0074011150705403002d950641000005010013500101034640095210040c0c000b00070415080700134122028100e00100031285d8003040901c26107420070401c40d02401001c02560400705800b01c0e02c80100c01011303041d030050740891030015000700b603044c0450325410342480c5480002c800300c69607a40040c1d415075001070894000900005e14a03011805000c800005080701042824941160310f00e80c1d0104040081140f800d400007425240b0740c83d013041690030042180c3c88a05001c908502491b0044070000d403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 991539406 1250 991538156 991538167
    0x60c070f021c0b010f062c0a031e020306070c0b010605070204020702030105460914060103050102031b0406020c092a090a17030f070602040f1e1401021e12 68
    0x440800f0b014100c50380c41c0d600c0d800f4035036180c4055030781c1202da0104003860500096824412001a68141043c000040c0b214000640740c4d900c000315034400c1c8078200d921b80e0b0840c5984017181810498660842c00314108014040b80c9a81c40c011180814000c2c07004219010800340f04640301c0e50159210071740e00030000d01c907510b865241d02c84e40c1c8a0302c00c0190640e01c12031101f602150b5480212082e40740303003c1c0d45d6004400011031640068800d5038402c603020071805150f440b640f034003072003480c1c043c0d80708000260713590504454260003c91019107140380c0d0716040100b000b00580014503d03040007425a14a4002e83c2c0e242c4501e030310410205200c0c041241d00c06505100c1d038915800420030280c007200c1401d00359403030707819100c0300170881c40b02419254820050030320808201405050701034440c00c0b001d0700c0c00c0c0d266021107041001c1c2d64480c0e15040100f0042442030207029151802520f4080740c990780c0ea0352030b840001d5892203140345030708101d281da0307240c01002003040c00801106a0300741c1e08aa0ba0380d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991540656 1250 991539406 991539413
    0x50604230a05091303021b01050414060d020f0406080c04050609010f140309070e090a030f121104060309033009020a080d050702120d020a241e0e060c070f021c 70
    0x382420000c85c0180508205000070207000d1000c4506000185e444600b020b04286800c0756402c9591134480d0711050a104903902103c01d4002001601c101030f0525072102d00d00300e4050003190018211498540091009205546030001134401d814024a44040041c0c20701501703503400e4000300001c600e841000400c2108030400007d0283c00c5650b03040015095507541044103844003000c510003000100d07000d804620962060145180c1d1005081002980010008440c00c0c01c0c0c4c800d45c04440400d03207401d019000c0c103812a161040d0003200c10340712105030242580310500000c07810010150b2036503401751441903465082d5103101400f111001c8070007014400c0c1d409440d9800c4031008038441c4030605000140c80d440410121000310b00e54000b03004200c0140d41e002d4440090202016400806820300008840a401850341c010400c01c040c0444501d4a8080c2c2e0a44099144043e501e91108041c1b1007041c11071002c0703804594012601c056001510b00c0090840d0352504101040c41c3c80c1d146034001407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991541906 1250 991540656 991540681
    0x102703030b030c010c020a3f022110020a0908060f0a0501051903030e010309060516080117061801060e0c040e07031b0e0a080d03020d0501050604230a0509 68
    0x1081e20407400c54012820000044500c80f1021030000d41010320603000300400f0100030300c0412444000742800307000101035600329002c2d020b6864080c0740c0d20350003c1007000750b00700600c0448500e540c4440880002c00c047c0c0a0301c1c2c0d210031810001500c00ea00103034000d581c600c210800d0f4081c00305142070b5015418007880c21890390005403031180560b850706000040e2172900b4950680d51114079000480e805203107813130503119400c5044185040c10344400b42840003030070702c1c4102445032100200c0c4060740c200301c07480140710b0b9105030050f0001040a400d031484070440024486e90004e5045516104014080c214034054103080d8001c0e0380e0f2001010030b02142040340b42c050b2050b01d4810031208170603030360040110305032210070b41c842410301180c0310b044445901c40c0c6000245a0005421144256520f441103890000300007003040000758081040540c00380d450190b94010001202c000d800c040c2480142401c841d0610211062103500301e04207541c40d205e1400306030081400520b500700f14034140c2c0c181c05c40c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991543156 1250 991541906 991541921
    0x150c0c2019091d1510051f02060603030a020703350a020f0d1218081b06060a030206161703040819030603030806060901030e031801091710270303 64
    0x55050070b02007450038074100300a9025643c6640401040c0c1220200c1144854503800350245440007400c1d01e0204543e11001d107401084100141100003030212000028107080307000d0301c118801d030000c0011024041c3e00280660079039401450582c071303050204e40c1e07404214003450311b05141d490360a11060000300d00c4401a100f901d03600c0e020384030031800c43d4401c6038640b0310705400d0b500490a1142d1801c0ca02007541c0c0101203400c5040291095180281c8905034250440406198003490a000c451744440051043c181c1101d000d0390554002c0381103900244890150b802640503400d40c080c408802c0c4440600f030002007120078400d259907420f1508003940300381e00103445402c48480c10100702006074030a12034a01100e402d9903c0140390b440320020007405500a00f0303854101034803240b0302c40415009100401079075003030082c14007624643c540098620640c1e980031403500e0001a90020300401d0221b001c1c2002034506800042ea07140289203502a0034458a002a414800c1d084100070560190301100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991544406 1250 991543156 991543169
    0xc040e0d020d030c0801090f14090705040b030a020f1c1e0314031501110718050108061003212105010303080901090309140d020d0f150c0c2019 63
    0x41c00781030000b0303043c0c042c1d070751006840700011640d100410045095610030301c0da040283c400401c0b003031140c15400403814010b0325841469000b4010402c0305c2d2820707203d00ea091710019006450b140403a60005001c210000200e80d015881c0e02c3d4450001104060300f5107003080e80f020780350101c0107200c10807000c22001010100c010540010030144000421b4090360721a8401c1c0143d058490544c600441d030800039128101d985108540c0c02150180b254407440104848912000070b640d8500400c0a15240002c1c040c002032600d030150034400f007012010040c801e5919040407141600c0d8078042210141c150565000706209010080418440e4541200381264040d035110302e03250b294821000d013203502c40c42c1e004000c20300c810307010019004000c15510203024028402c034102409500440c02c0303086540d00448030900b00040c0e4400304541c142c0c181d0421440c401041104010341c11000e800318440ca100035005202001020b41e40400c1107400c440c4841028140042413403241d8800007a4892500034903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991545656 1250 991544406 991544413
    0x16030e060c0303040b0c07260c0f03091003020a05030a1515020a2f010c050f03040b041e140d0606051002030a030e06072a0203010903112118030c040e0d02 68
    0x1b400c030400f1002a10041038111500b020344182848061210864100850449040034015540b0001c018480c1e1800081070002440e0b4038903152041048000c241200c51040c18810302101c40400d0340300f8241d1798854070600700002c10a0400c1080c5000c0d03620341c0c4c059001501e41d4540802c84660100b04c0c0031606100b00b184d8a295650b1807a20703c0c1c4007031030710b1016814141c200316000c010b42c8113841101825000764151024040d0441c03415080d540b0070f0b0040d0075039003c0083c04020024955003c10041c05640511201203800c100c0200c0c821140d000c9000e00c1688811001c1c01406000c1e488907000384401000d0594031510b00c00301a4580d080341d504940400c2c50720084640441e03002c01d26a20501043e034441d00244004210324035181c03070000d100150b201070307240c0c0c450040c0c900748900040d0300c0c0291100c04180900c04d00451030071050100340980c0020086800c05c3c4024204143e034041800d04a1029a400d540d0010074640002c65040507406030806440040028010921900e030f04542d50130b8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991546762 1106 991545656 991545661
    0x708090a030b070f0807093318050607230a05060c1222060509030d020d02030f162c0423090109050316030e060c0303040b 54
    0x102c40c160355040030722010f030b90028128802501c0901c0c050b10240390400c40284107000c10b109003a00700c000715444a24401c0400c40c0407081810691840c01e403007048000041c001500118100c022200c0c10f1004910341c103000080702d660a812440154005500342d0500d011818100426003450003500d41560014030140201401030340011a12038030b900d65400e000c07407000405400c0c0d400d02403e4121008008045a44800c203554000000048954a0850031415481341200ea2480e852000440501c0e16415501540c0034600320301804416036203c0c0e61200720603140c02c0c1c0300408034000591a000b610090b80d16801c443d040d4020b84074488000030701003030594507103a4407030f0541ba40d50300c00c55420400958010b035001103108028003d0010503180c1e941c41c3e01c074840850701981c0480001c90181400381c4810700340708201501503580d642c00b10032555166003040e10100d42c00c0608002 = true := by decide +kernel

theorem cover : BRFrame.Cov 991366906 991546762 := by
  have h0 := BRFrame.cov_init 991366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 991366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 991366906 ≤ n) (h2 : n < 991546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
