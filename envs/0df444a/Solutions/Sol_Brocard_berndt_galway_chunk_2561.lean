-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2561
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:04:39.454458+00:00
-- url     : https://prove2.me/submissions/06ad2807-989f-40c2-a408-e1c3f65570c5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 460431654 ≤ n < 460611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 460432904 1250 460431654 460431679
    0x302070213020310050d080a03061205032209090501020301171f0f0f020406020327010e150409020c0706030b06070209070813060f0b0f04050615030a021204061a040b 73
    0x1c03070280d00300800c245445400503d0001d60b9075a00817101c121103004420196444280f030b60020140d41403034000c002c001907202201c2d00012400400c85041c03003e00c5228a40719070301003405c11350b5204c45511a40d030b041d081040b403105004040d4001c504844641f00c0c0310b0703d00d072844000075895035884003902c03050402c0c841240041d5005a00003c200340d10404001451900290404041360800d42041c4010382c4045000208800d03c0c11310341d0305000c001303c1d0280400549500091000310b11004c80c0e400390b2540f0718148425058501900d001c0d094460341503441300c80d8404426a0340c0c885100340e02c0000d00341041400c40c0e04011007141c0b4102e1300a08041056920030005442e07500001c0c1c480c0c0b03595480c4002e41004a44240704905500300c40c130741d000c16028148000c2206070208485558070540c542414000b13142d590a5484c080d00340c50a840a490366900207151000f07008040a1031603400880080008100d5154000c0c0741c864403030925a1040d0501c002484212080c8038680c80c0c00c141c0c80c0c0c410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 460434154 1250 460432904 460432939
    0x80607050c030d0603120e0d21030905010603030e032e0e0a02040507121a1003050c1e0a091502061f05030a060b0406120f150e06070c030f03020702 65
    0x5104681d840700459181000c40786a18003203a0040e4800e954005040c800c2404250307110002425000081310301000d906101d44480d04c02490400065412580f0621040750f124002d030010007046130010700030803015075a420050240520055054407900407030803141610800201c200c03200c5111260110005010a0201401440d8081440c0e0b0035224440c104030050f91107000d020f104410554078890281075a01c030034806d641015030a400d0300f020206c503a02823503c4a00a403009218140b1f00404c0d83d0300c61201c00505881960f55041c41e0300c1d02c032203602c062902c4c4000101403100b000d5541c1406c1d5640da000c07a040040140c040312005070440008500104807544a0748034242044820218490fa100f00180c502540040d0848500351504010740440c54184924001009a0052044801e000e95183c01600d04071035402450003820001c42c0703407440c0140c5d10440080c00d10100316800f80c244180082c0c14402601c1003100021825a140b0614920900aa82441d64040d15002e01007084044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 460435404 1250 460434154 460434157
    0x8031908040807140106060f020307020102031905160c0602101b0e010210020a030f06080721170c100f0615050c0c04060b0705010c03110403140a02030610050f0a08060705 75
    0x10a50b4540414410708022424425003008809000d1000082e0f0720b252002c00b4058140740b00c514400c2d034100340b0803500980d80110032a800005802024036040d41c032044107603514045c803031000c1d1078040788004041c10030007078460010550b0869000c449412560560031000d41d059070301c8080c810045403401052036801200084200300050040d01c10000003452503900301e0700600503460000751200d03905580e4013401e200350000303450400c000d0049641003ea070310714502c50345400d1a2000c00754079010b00030b20803410301c0c280300106004842c2c1e5071105d0707103040d00da592009442049012807400041600540c6070f88a03c40807200c5031300d4186240c1e0401d4505039195041080401c2c458041c4414a5800303a540348210000f0b0624000c00c00c0d194030080c20300c1802c507909003002c0802c1c1450b002542d6100b442040903503081707aa1241d07100c595501b0f4900701c2030800300d0404c002909881a002488400700b000c41074141610425111301400d801040d081001c02e41c06446060269003194000c503186a200340b0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 460436654 1250 460435404 460435411
    0xe1510031113140d21090302060f0304021201061a071119060f0927090c0b031501051809220302070e0117251205010b03060108031908 59
    0x40006100d00011001030003940604503060001d161150103200c8030000f20320200740030030261480403480c0c4095030761252925840c604448007150104070040800c1c40b480b01c103405903502030551038960000300881261038009075000c910a1510401c05255104141310303000888180040b040740d04214901c0030b40055200202c156641e49a100380b841c0d082d01da2030407103442d030300060a40210305850041d0007044a00140248006c0002d0f0440400000c10141c4c1d01c00c00c03200d40410500450071402c83d005004051102d0010502480c05c040003444481140245100d1954014141a061304441c01100c4620903011078441040b0b42d48200651414118000b80e03010440b542c1280b11704450b10201e040d1401326031000c40040e8800c500a020018004845070f00500540c0e440380c0740a440f0041c07803501c8015842007120320030030b100d002441032079148000d000108200c568204030381140c0d0078818003030014a45c00da8080d2149000000b180040002200c0a40100c02040080070803220f204517141c4a025 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 460437904 1250 460436654 460436657
    0xc15060a0314030a11060702060402012d030902030d03151e0b04030f03022806050901020412050102040905010f032d021807020f06072f030705060a05010e1510 70
    0x104408400a00600006119221240000d40e1200000130000f0301e08100d03134600400c03d0300071070280561b2a40000f001c640250742400c01515000014030070322103c3c546604032202c140d0001e4040045070390568425400d02e4000d506981c0c00b0a40310f901074040e1112044a001c100304000710401403c0d02124440800340005041c1040460392401c240c0c465402941080d110405580c50010403d90104040c1510301c140044581d0f440841603d40ca0300b84141c2c68018010948540001c0c085a5083d0f04a90141c0080c01c00e94401c403c540c10102d000390418000e0f10308c200e152000208003c1d0401500e0011079500885800802c001d104110a00000791075803c032070480d41c4031000c00182d64962040e0b2114010082400c8107140c4448024503141449100b00d5254102c28240b010450344419418108401e0780703040c40340b017559002c20b04010010021441543e000218145081180c007007006405487e10220500099807038082c000d000788015070fa91000901007454500281c100002e070041c0c1107906 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 460439154 1250 460437904 460437919
    0xb07061d03040e06041103130c170705041a0d170f0a120b040c0f18120503041a04081005090102070b040c06020f06040804060305061504080d030c050c1506 68
    0x458102008020102000000c0e07080840e0502c640c012107003000c0e074890403c403010300c04441c1031001040280f0000d040918040c011100308400c4c00403801e010340051031840c2e0300c3c80e00400c036805aa602c1d0400e038000d0238440c508010b003036034890706c2031007800e5201c610040084078400320641d180c500100c058015040050000d000c0160031802c000040c0001840c0c51b11404407603010740401800300c03081070601d244a24a050004500150310072008a011170710b0b8200102d0042801103c840c6c1d9080c41e60100030708005081e214420000003001400c02ca035044a000c1d01a031038540d0014400380034034081c8000c6980030104100001c105508035503001441540014a8400b01740c842160310304003141c013941c041c40006020000c0f07581c100022800035035600041c5c10942000c0da0761401c28070542c400d200425844101059242d500e00c40070b9140451800c02c3e1658483d580c0c11076a4541c44810840c1000c6840d0500c41e80040b0302900496202a4071500984041c0102c644090111040a080184c2041d032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 460440404 1250 460439154 460439171
    0x319030c0c06030b0109090507020a060b1206130c051806130212070e1221030a02160f023f01020408030d02180a0b1902031606140109020c070b0706 65
    0x719a2107140280405035000701d40b9440e036400141010b5169030082440324a00b00412107110380c003182e15070281f0342c04000820b2010035040010a01a501c2d2068103841c0a010107200d0650004411441c01c40e02c5080314544c82580c0b90204402c07850115244002201d682c0c001440610304402d10b581c0c1100c01510050030410100c81000703c03039504413102c2c40842c85002c000c214902d0900084100e9090080041c05a0902001c80144c520250580f4414260010011462054003501654428a450092000100c2d2581081a040910b8840c180c1c02180e281c000c0d442c0c8251000e5040820342c400c00600c1722590300d01104103520740b40398103901007030b95030074000465110010700041018070007191000d07071030f851502151301080c001102c0e22442030800500402c1007000c54401d07100d030f4481c0110010007800c00342d54142c4c01c0d40704001090ba40e0420b1401444200001c035404118400303110100f00c0e500b40c0e2901c01a0003280316058000c4160341c0803840c20804490008001c158042c46040085402003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 460441654 1250 460440404 460440413
    0xf0910110a03050a0203011203030b030f121c05040206031816170c0307060c0308090703060f0c020c0405060a1a09030106030506190209011e030213030302030901021b0319030c 77
    0xa22121500360418400544000381c03a906000c0c0d2a00b00700d494000310f145500d400b03400803220b03003495401000d2580712045000b41d550300748a03541c103d421032025100c108a0042c440c03036061f404480802980c283d8103c190592000e40e110b828402c0d54040c001d9442c40d143c007040e80c44d80c5c4031000018040d51040000c4a0034180000720604018102c00744840c100b554800002818001c0407003603a402030b400300004010495002205140e465014240a032458480040312424141e035034001a02c668280f00c1c072291203000c01e600070041c444c49503081c0d030900e0b03110004000541d5800d8a010754030262075041400451000d5602e800345403004c01c149481d01a55601081c2035034040c0c0d00646031504442c0070000801d40c1103035400c9156503002011454148210b00180030b4224600e60104201612080710103601e000707604031005650000c1050b418250303245002942c0f54080389406005029040c0c00d100c4234403035500c0e01100510b000340a0070400103204069a10003150318025000c000840d80c049020a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 460442904 1250 460441654 460441661
    0x80105010314191509150e190510021c060605071104052a04030b1302032506050904090f0609050d0e0a0b091906020d0e010c0308070c06020c010e07050f0402040506030f0910 76
    0x1b80d09074004200403241600403818a140f880344030b800b2800341c804200014a0115059100116038100181c41e0740d868500d804c2e1660110558449803841c00c50301141050b040009400d40342c4c0f29000c01d00c400c1164105202c1a6001a511004c54803200304840340840e100b59403090035524a4168241045c0d45c2c0e4a40d101c0e04801919410b941c0d407420b00d0170100394101070202ca240d140044804c14890102003560480c0d650705440350004100380880c45050700d5559811a40d02e03583c100b00103c40e8404581440c1005001518040700d00e032103540c0900d2017081c000d0044101103003000704041c90540c034192140c5107642c0544c40315903101f0f030620000312040c1290b517000f03030103000342d035000b0b1891b48004c62010f02682c640c2c503101c0c4e050103401001c0400007035008040c03607401000d07890300a80780c0d5a2890054082d0084549841d510b509100e0042400709000031440100c4d407007150000f0424200c401070104038800d41c051580c02440410004200d040b010701c0c0700e50401d49213400c6944000b41c00c40303240d044 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 460444154 1250 460442904 460442933
    0x30e01020d09140d05070305030711010b0d0803070e041a0415031a011a0310120f020307080c090a140610050c03041202010e0a0806160513080105010314191509 70
    0x30b04041c01500b50000f842088182403540490901a00c3c200182d14090b185000003441d19080090f12074846110700e00a4000341c80528020781110300190360380c94910700c030b50000c03542c00c0c00080c0100d51320401403405009509c86588003080300ca089005031014480545450700200c07441400c8071034008009280940140d40b8805080c010020795410501d0610340b010403034900202c010f40500900c8030340c072062442c100132910390160340c5580154030726040c0c0005003002c50280d41030184142c00105020042690031650703200f03c0e5410121760b9040e11040c1240c0c10b40c400d556913100400d0014405080000c20358865504030f081450074441540381c07243c5181d11a802081c1d41d4503d00e800e0900f1541c2010300500012800c42c0c1100c02039042102050340c030040203104104e4201c400b416102e41c9400342048911070080c5070140803000da180d10602c0e010b041c00780702c212000c031260900f0f050520008180700f65050001e8950b454a440d5589401031106040d000700c0f81c080350781380e0707540c0001444030b40604e03003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 460445404 1250 460444154 460444163
    0x40b16031409071e0b04050f120a03050307090605310801060303030b090c1c1a040f090c1d06040b041b020a20010c0209070309051f0c050a0f030e01020d09 68
    0x51007820000c00008400e031244e4401c003240e0b00810b092008000396030569007607403010b9541880715290000020b580e4001c40c1004c0e009400760f20720500505074042c00444c444d003940c1e201ca80945580b44030807203180c03003490750b0075004414184820701e0005081540145c44110103400040c159200c1a43c5421140240d0040b80425541c0300c1c250454240084c1e080e41c0a20421451400d10031038405046042420100328004180e8030080d4840c105070085d00300300c0c800030241c010000060302c3c800800003004801420380c0c5132148401c0c0001c000d0004c40c088288600c0c040010b404903180e00007480090424040c0243c1c1c082d1305d440403203422000b400010079004840b6401400702920b24100341889580050070348180f000103030195100c81e40c110020001076641074800354500d40d151072045006151195008095015481500344040c40f1070740c45070301710140c02d40308000780d008940e0140c0e414454075561401185804400e03072052806507121540031441c2c1e1001524000750090b4440844000c541d0031207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 460446654 1250 460445404 460445413
    0x503060c07032307051204080c01080c0409090c0e0105060304080a0311040e0a0c0e04060b07080306060f04030c080f030a090b0306011e03020c0c04020915070c080318010215040b16031409 82
    0x2c5c00002c01c442d44d01c01c0000214140f81a080035906d03601c4030031131141e5030b0502c418900850084188a0115401007482003810800181546020758218006205100d4040040d40020805181800c110303800340380d005858600c7c08103400307820b60280503024a0700c2c03034400080c84001000030040340300a128201801001501d40800d40001d829000c001024500440c81c001040c44804002c10450b44844c3d0401541b0780c4030b0769100000303441ea00c9110038a0b04090000b1600104001e19840da40c02a50100c0d01580c40c9035140c0300f8401e80e42d000d80c28801000a40800d0100000e05520700195008034043c901a00e0b000402010030609469840d81d510010740c2c00a001c1918035814412004000c508440a61911030040d00080c1c941104620190582c07100062072000c0104244000d030042c40314109403901c9080340c00c181c004049030a44000e01600405207044407030200c0e41d45151046d6844882d010507510703800c42c0c00640c183c0204203202031550320348401c5078103c4d07100764482c03151040340000d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 460447904 1250 460446654 460446667
    0x108060d1104110d180b010b0c0304090e1606050c06040b0406090203061f0902040f1505130608010906080c180903160804031b12020d061410050f03070503060c070323 73
    0x81d007201c0d0002c00c0b21811407240b640a0000900840e221411105a44070307082d00c80e20f11442c1c0c1070072b500c100c2d071010110078600100c4500c006004246596001d6801c00d2002600b90765440644140c85001e2080702550441000500011043e106041e04140078440010f4103800f140d002c60b1911000b52504800f500c2c484642107038040805105602500c0a410103605082c80c09007684071000300703402013000c910179110a6a0050307220b6000d83d945c000f52100010300c455a0381d40f000e09813040038001e52840d18200301010442482c0041c1c044c003002005010983d030031107581d180c582140005014082140800c00141141d4002103040f01c44440c00748010030b540d18590302e007488620309030b940c060101e091064000c10039028050000e118140d0162003400100fa150b217080e000502c101940c4c84034900014044c8422110b8035140d00d420b407841900c1848480030018201580c9458174410164141c0c00381e80012015002000640300d6907100c1c2c00d00c01381100d00c1c81001c10010a40040948100da80410741 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 460449154 1250 460447904 460447927
    0x2c010c0c11040b01020a050304030b0105010306050f1003050c1903020306030c04050115050702011701080c0f1504062105070507150b01090e1e01090204030507050f0108060d110411 79
    0x40551454450a1003608208155241242018181d039224403495541084120590003480410f130240d50000660343d0f22030700da19042c00504d000f130180900181c68034501041070700f4a0300401614940c0204184003500c041d200c2180a002d0086c00b103030700e464050155901211020300d01e4080c0608030380340541c03685000c005041c6000d01052001d481a0304044c010032141030045d0f050b5020268610f06135175202030034001a2041c1c10040d68401190784d0000c00001d4980d008510518003036400c9a04204126040003001010035500e0841c01140c581007008004460281c150150f03040d00405000489412000d255421a034044900402180d0006030301810021502201035105101a60070802c524948000800b08203d6000700e104180d0220041a220140c02008215010f0b0b0881c00d040c00d5070f10b6001d2131000c0c3d0032502c401c0720a0f120b02da101040c98507001c02c13099460384d8180e40300205139941c401001311111441000f0b13505183c960103a00990303103d902403540f42480403010b95a86064001e01d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 460450404 1250 460449154 460449161
    0xa08030f0d050a05040c0b0a03020702090a2c0616030603020904060617060408030a0b0409050a1b0906230a120b06130e1002031f1205010c0c05030412062c01 69
    0x400303400391389003904100001e0000071041003035501920300e00b6201d041e064000c0d0001d10400102139801516402081842405a04081d051140000c00f0141c901ca000c0720300a04802003c076041180d0f0450305c00511860f0b0034a0f6000d444030060701e0f001c14840d56039008600700c2d50040d141918159228075081c802c62000140a24032110800020852072030581c44652060001400e050095a00d4441604003a6141d070031041074250000300b41c4801e0311207868a070b41c07801da046400851007050b0a100144407101031241e01c0c101c601401da02c40e0002003904000800c248040000b42d0300c18214070000c6100e00c0d070240110b41c1c007440b60083c40750b641000400c02810130046040d007881035082c96400c0c280c0300004100d404980000c082c01580700d8a07542d482901346031170024103001e02041418000b420f00c038048051001c660040c3c000300003400f1150780c125156903020001400c3c035803040108000400c4d01000200280d40506c3c000590316600000c0b007541c01c00502c0c0000b198a203503110f5143c0c400028030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 460451654 1250 460450404 460450411
    0x50c0307091205030901032309010b1003060302010c0b06040e06012d03020f01180b0c01090b0f0405070b0a09330201200c0a0807050601060206010f06050f090a08030f0d05 75
    0x25498019003900c1d60f680b943e64820310081c24100741d01c0d5001082080c0e1f01e00ba40881da20032403181180705142c9224158001c012034000c0d1446030600203645948036020b40300300003d680e010303502c6258130440b50710380c90450007001d840c07203410598448101d50b0444083c8034207406051000940c861640b0910724080b4102c070941030580e140f40201c0c6007000140da4a500d0007078200c0c401e080c1605104c910061104c480300945e880154045400940500182011b506c59031040d0311485c11b40f195a25009000081001c0c1101c004040d54011003091103220707440c2c0023070510040c1a141042c8407507101c010141c1158000e2184449000c480402240a81101841c2c0784400c00e440c40204a40c240c041c1480b01501d43c1151001c00908000501d0708000c2000d0004004175900300805650703421189c9411560b8031024420a4018040d1070000316030740004445002c1155160307990a81407070382204c02c2d40c2c035035400b0031101c2d940705840301c3c3c001480010a10240425001d090182c07504c4400d0f0007150382c180e5800a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 460452904 1250 460451654 460451669
    0xc0603011203120c0906110c04050a1401210201120213030f02040509010b0a120206090406030804080609030a0806101107030b01180e072c0c0d1a0d1b09050c030709 72
    0x40c04011300c003075025032030101300d0314a45000f0b818990594880c50805050000040d0050b01b42400c200d110310494100c0d9126884881c005075680e13980c2d03000341c1000c0d1035003881e000441c81d121120201540c80380e406107202e46000303540140b4104545001414484e01c56004841c2895048001e1040d842c05106a5610840000003800584204c0d000640100c1d102c0c06031800c20381a0b85e03031a00c1035403110402c0d601c500700c020f041001900d490b821f01010703d1b0070070300c92070380791388a450001440946d010041d100ca0341e107280c456041680324402044190001c011501040203c00404000400710402c041d82c001c5008030514107141d4107104a48003400c40044004194509040040540300000240401125440c5000c4100242c101d2010701110f5034100c0c0c0c40711103402180c144144103400900401100c50b000030100804041440440c29200c40c0401d2030b54440300c440d0349500420032201e043c01ca4600d100c1d036806000d176155000d82d812541c05070b5100c10406001300c204030724240c001d456070f400781201 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 460454154 1250 460452904 460452911
    0xf0504110a170703021c0f061a03010b0714060f07030e011e0e070b030a0e21180406080a05070e010b040e010311061b060a06050609030c010507050c060301120312 71
    0x10a0142561840340c0b292480c403045030300050f40051190341a10390b10364400103100c0300c1491880d4942c018010010020300c2e42458241c1c00110304800700ca941c80d09000019a032070031a03107041c854403001c0d0400c4506944d64140000824110403061103110700c07642c184410843c250800c402c0050444800203a00b0700141c1c5840304488030300340881110989049002000b040c2c8800300c10f100c5003813034680e0f0700140d2008404010300900c101d540c0c10101c4c94044003400c94160300500d8001a1083c504c4000303a81d041c9a00704280c00b65900702c03e0138000d201c00050004a802ca83d203c101614114502d941034810340c110080c24003440104503001401005d03000003842c00c060400c1c014400ca50030603c0000e00d840c40e1524100c101c0c0c2c848009403401e404510f4500303100703520480111600c69104a5000c0700c00361418201060070301d400400c0d00c4a44002900601040c3c05d24401598182e2050209840500c140c10040c283c55444038000c50280030040c0315046003004600e005009a6030721011224400e05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 460455404 1250 460454154 460454167
    0xb07260a051c1d0d08070305010608070516050304060c020a0e061008070201063302210a030b0411120a0c0c0b0705070c03320d050318070f050411 64
    0x1485410703603442c03110601046400d07002180d2680c2c01041088003820b01404030300ca004030301c014042001d5245056540b694441581d404400b281110024000c410224880d0700c0407030b5000740301d00c010300080c2c0d41d450122040c00580d9100c40d4034541003a80031400140c000c1100b034045003441420348004152000c10380b4000d040c104001451080c40e410828100000500041c126038402d40104000700020301c00b00d8064903901c4100f10305c40704103212800c60f40c54050702c1d0401d070601c0080c000241c40700e540310040484110f108a10000e50006545108040d2242681034050b40d442c8a400c1910b103c01c0a110b560341c034890b03007003500700348010458540c1501e05540382e200715401ca001c01c14a0713130f0b02c600f1074219035030303111010b44090241e007038080d0590344000401f208002d51000300208071900b04041c10408580e145901c0301190300e50150bc09140c00c108294445c49015001035500507406100414103c20f4080c41ea40c50f000fa1603000b0000d07e0040070302000031b0304040c80703a214008000c85102d8903050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 460456654 1250 460455404 460455407
    0x9030f0f0c01031103060319080f04120b0105090402180c09060f090102070608010315020702040906150f0b040b040e060102010209030a03080402010f05040e070806130608010905100203090d0302030a02040b07260a 93
    0x801d045040449804c040c01a20104888800ac982c0641801800d0503180c5803201200164048041c9045031400f0b030810000c900351030701d10880d900c2542c1c020b00c503185044110070404203150014040b01000281800788410039a01d0002a0010280d8040703510f80301c00102000920303000c200d40c40f01c01030217205001400414210040603010b070340b1444015035224030170310106000b0b00041d03d000d000c1300e28043e2210841410b9550100c101d400348000c0804640e20f59085040030301c01c1d48540c100d00d5108120030071000d049090121b5000c80c0c1400010b080090000c0070034140006004202c0001c1c81c0f442c208011580c12414900c00155180341440c01d01742443c842e4800c1110113050103041c044a1000140e803540c2d0360200001201c0c503144113024083c0e442103101e01a1070300ca1021900b40c06000366030139858116109482c41511140002c010009290b1001e60080d1300c044c0102c01c13155020007000c20b1401141e0000c04071148118200442e036041606081d5a1201801080c1e540c41e000700f01080f00d4a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 460457904 1250 460456654 460456663
    0x807240e01050a03090312020301030f0221100b0d08031317041a0c2814030a08012105030a090503010e010b130c03020c1204081e1209030f0f0c010311030603 69
    0x1100c01c2e050000341500c0071b090607190f0100141c12402000d000000210401112084845090740300717482d44e1180070b0001001825840807001c142820383e00c0144000010540c1c0c1c1c101c8206c2100107031400c1e0035407071240c0300c50b45598402c071400f11081e0704603130100c8108076003040c1c40c011604035190b009061038103043c110b0350002e0013009950940040450a501c0402c02888101c4200c0b40110200c400b02c4960700413005102c91650051fa8a410365052802d881c1001000b101d04203406651540c1031682003a03001e201b00002081084180c070301d01800c00300099403c01c01043c03061203d45030321407081d213400201400c4d1203100000c3c0702e13141d041c03424003926512030400429841c1ea00c0503020502c209040400c070700070b0080c1c6100310b595110b40d504010712443e42400030400d030398070700c41036500c506441214904880c15000a5200951144031002071511501001d04510301005060324088e40c0c0150305645802651884540b550b0001c1d0750038203941d03816100380030002c4050005241146801000a603e4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 460459154 1250 460457904 460457917
    0x7122a11060711131a03010204050a0524031e15031203150d1401050f010b0a080c070f03030506092d060411040612050a02160f020a0807240e0105 64
    0x900e0010070001c040000000e050b60a0180151011203d9036000350781c0720107417000c04030031554001d891000e4240c078181802103500343d840240c001c0e03020341d240c0024001024000c2880c5504088030b2110f41c41501006002940280b1010290b41a80d5054600e60503000b40081e11000c00c0c001950b042801c151808038001b411000c82281542d00c0340d9030711545007501000d80f10581c0c0c0c008228031084003084065440320700e000c00d109000300035650f41c262541e66900d07070030700074611015810b00c8081c1c0720718400c2d90001c3c0e000c500c6072405410a0020b43e42c034001c00c00c000d401240429180d2041080b1818948a42a40929010a0051019a8120540e03890321650485441c1e106424000880d151240d8010351500d00030055841c0c0e942d070341c60100a085d8481140d4440c145402c04000c6408146203000303495a00301ca540488808482c19610003020100d0303c0002c0740c000c0311000d000035000600307108120003030800e50003c42004c400d0003050010301c40c1c081c0400d400d103e061030780705036241d038840180d560 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 460460404 1250 460459154 460459159
    0x90f160309110307030507030b0903030415050a0b15070203060c0a0f1d030a1b080c100c02150a0203071b0e010302191809020418050303061507122a11 66
    0x4241950b03061038041c050000700115050311407104008104070b00040e0540071a40554541d130300f161196005140c4901c01510003529001290280c0da18130000c9922241d080a407500000078901070241c0880c0c100351a14070b4881482a000c112442941020302c02654003444502d6100d20b4445180005001020000040420004000b070703404400588040a140c0c1903800404039100d0000f1803403d0008079008107a1411484110303000003c9000f0005010385040500500c6069180c000d280d08880c64001e075241a40e1040072801340c110303540b6441e40200443d140320f43c00380d03503501c101d4186440d031480462803501c2c8400340d04400b0080c29050b0340c2d0040c11b40b075046588030032007286480c201c040d02c80d254001084018503082007504e441104d81c405145136209690074440d488602c45510706c9050300410240480e0000c03c0003552528041e458540700611412001d030800c1c10a44440518030240354149012840c840480300b8603282061144841e0508044400b003040f85555030160000a4400880e0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 460461654 1250 460460404 460460411
    0x10c23070212060903130b030f010603050901020d06060801051e06120714040f0512340801020301090f1b02030a081e0f0105120f120c0f030406030605090f1603 70
    0x1000c542d01c001c4040400310300801154290f00300003802c9900c03680718280b81d8046003610320300040e00b0f419110a8a10032021280c0c11540340c0e1074040c0c258082e20001f031a014265600304101d48030601d0b9403281001a00b600c0d40c4542c0558102020b00441c1201c15290310014808100300840c039a60303010031101c410f52400f448a885840b607290966143c4104403800140a00100b0b0101304512030051010446008681600388400314503a0241c541004850781900c68486d05603001340d0741c1d0b80500e01c08041c00c51442242c0300c2c40d03845101c07608903002a04101106526000100c0d8010f28901612204400d0340510b2140c0a2680102a42d40c0c400c116600381070148500c00641c43c00241c8090101e0500d420200d2440340c030705102807000034002406540d1080000700790000b000b20300014003030070131012603004000c2c0c090140c0394004250044945c10807584542c944480b11003009102400041ca11620b010481608150401c540030500809202c40e24581340c00b008044402c40381c0603504076080b8203000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 460462904 1250 460461654 460461667
    0x105070f060c1701080a0203010c1718070b0406050c010c09060903032106030503070203152403070f081011031006030509010603170c07080a0305040314010b21010c23 73
    0x759030074401c3c00400c82c0c01c0500c0c0c4000040030360003c0f51034040c013482200200038680f8191010b44000c280041c111103125000c40024036011062a0704007162421041251a40d0b5650022080590300c40e400000001d0b40204134500400c1c002d006000300c2c0a814144030380c0c21828100d0007899a440c6110150409c07181804400000c0001d40326410b94050800c0c0030f00c00c95459007092656a1b0207518124083c1c13090786648120000d6000d41d85000e070700f0810215100402d80d003100b00340d84810f5041c036a41360041c040001000d8a05030070755001412080060700b00c194458094208403075007034110100b017103070400c00c02034100302c218130b01da0580340780b41000203058841b540114010305803600010b001c3e026480d20320710317014040000341c0300d460b030306800300e038589525015003d07111250084001c2c01f1030010702c01840056611000d1078194030340000002250150440003c840c0006440048aa02c035046500301c08040280503ea0088425092600ca001d0f5800007440038441040c0075541215400301d00f8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 460464154 1250 460462904 460462907
    0x403120f090804180b060d020c240403091a0a081e0a060f08010605030c01030504020310060f051e0a150c0b01030c170d08070c031b050604050106050105070f060c 71
    0x20485451a8010491036890b441e00340d1956105000307041180315140a80188143d072401541e900c070b500940f180c1c1c201184600c007140650810348503440c00740107220503d40b04035208171802c0c0c4105004601020a800c0500f0080c0496000f6006418a40d000144c3d404c0d0340250601211149802441c2c40d400550b5015022014000c0c040300300c0e0392aa1005052024801040d0408010785401003e840e0226030741e05840d500701c5c0e0661140d5601a0040c0d662401158060307030010303511500280980d8190350102d40200c0c1280c400780c001c5081412440d50074800e0b030a0001c402c074400403070002408481c2e104000000c2480d0703441e1040b03541a04a4801d50b0103454400c18505440a510100a46040d6100e1501000090340c40c002c1c2691240060424900103d0001e0401d07400c0d14203850740940b40c0c0310708400715640007281c001070b0140118107080250780148503640424260141018012074201842c2131800e4a8079031384801d04001c1c0520403540420302d00d403c4041c845501c550001a6040101030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 460465404 1250 460464154 460464161
    0x7050304110a0905071e02190b070c020d050601061b030e122802040c030902060304060b0d0f11120f0322050907110705030118020918030f040305150609040312 70
    0xe9240b803800c007001c1c07140f400d800102401004c0300080368036501e0390740c5c113808a82d41e003440b40654010f0208048c40c038010503628100603801112514040a41d200107400ac51088840240100c40641c03101c0c004010b60b6070300020a43c035400f0000d8400c2d80794521510005c0c00c00001c80070891041c28022445040d6140411960050346c3d40101000040034940d0071440e40708034a24000d90043d41401b1200c403c151103840380c2d03041164020641d80c2161102c5e100c0314020a000b00d9404d40040ea10140039001c038030044c43d01e61000f80f0a4010320007040100f01400300303c8180c2c40f00b40e00c59510032100444041e00110584003c07581c903200c40c4003200c0302c00f580c00742c510b1510b40c891900400b040090180040d848a1401101c951000440d01c01c02e55a0052600700d074164035070311410983d040ca120006113044c503882c1b6044203100701004094880d829034203055a00851800003c2c1400080400030000140041c01581c039410a40c1d40c498903005000c1841c240c1d004000404020b920906080043c09961 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 460466654 1250 460465404 460465409
    0x60509040602030a0f06140a05040212161b24060302030709020906160c1a090604060f1214010f0501090e0411030718090606140f09060f0d06050a060e07050304110a 72
    0x88240b0a0300d0355181c100d240c0240c401f04150003251009070114090030907000301c9031990b2803075400d00754642c0d0b5903c072031240070741119151013004001c070301c08520240f4020780c504206004000e40010710383c60a540101a801c1c41400704402410b0000400250350b012406504a4221071405a82c41100c000014058481e5101100c0104600314900c028800c0155045003034451040103509410900c0e12401003900903079000b298400c000f00000d21050b8440c0d140c00f031702c4901504041290070b40c821840d1054030b881c0d101c054110101c0c20010864021320b00e1a0030f0091034203003003003a0101e092882450031090024005001c042c00b000705418961410007112000309142c6405007113420440c203903140503202c2400180c82c0141848804600b07144c01000c010381c200c000405800741000d40a060045840d4000d1220b07074052041c840800858451090606410344a250700144078905224450308540d102c1c0c01c45040403035442c00f0000d0751030f04401166082500038140207011121880081c0c4044000d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 460467904 1250 460466654 460466681
    0x10b0f041d1203061512040305070201110613030905040c1713021201090c060f051c0b060f0405100905010c140c0d060b0a060206090a060e0a0501110a0201050109060509040602030a 79
    0x210700840c900340051018601031041150110f071200d0b1800317210700d40f81c06100226901100701c900890700107405400101029481810145108590f0301055410408101c03880ca220070030342c4840e50304040e88400918081c180880d01042000b10b400f400030030440c000c1004509000e090b0002c14801801440e004c2d201550003050000380800b004d05142c080d240f01c0364211400145a030000c18818002c148038400800315645a60038009080b07802c104140c081001c1100140d51481c064055880394002400300d40705014038560340c0c51400d0144230150721483d200008101d0b48581c00c0c00740740e17800b608000c1c64942040142404000543e000740c14844107030303811a4440e00c88608401000890b400c05000c0010445040c07040f41e82d41c50040e601c640c3c00f15444046604242c1d0f900001803031503440b05040c410398008a52201c0b40c10340d942400c542c4d5001c052801d40300041000d40c0f1055090113010702405400e00203120603071420012400f0340c000604000c01c1640c0200c002500c1d440030350b0200e0708038000d8 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 460469154 1250 460467904 460467913
    0x91216171213030e0d0c0807270c021911030102040f08160e0610020120070c080a030c030c060f060902030601030e0a080702190308040b12010503010b0f041d 69
    0x1500c008480340d0201c058508104000c0001801d040c503480001481150180c40d95084104c01c14104800c1d071000d040c04444811001e48085190b90003045443c0140c100c003603203020301618880d44201ca8246904508031640d08181c0581c3c47c0c03580c04601c000e030700d8200c2c24648072860500d04e030130120140e0406815402d0341c400300c2c00092041c0b1245642c01120030f14419110b00703040d82c0c502030000007010b004030071440d0000c5001c18207070700b0011030680840000c2c0c0700004203210711900d1800c9201c803400c00c0500c0c000b00440c4100600015501d0701c0d0003828000020030710015580e5024000110010018080c13204a0316201d081c0b00d2950010315001c268140c0400c182511003041e4002500260344a90020b07152540c0921100300004000481079081441641040b14507800c1043d008409000f154881108500010000300d0300700250000d80307208101d8a8841c50b15410450082c901684124440d03810301031504250340b60604d403103803030410030754021071901e80c15407210044d00003119840109104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 460470404 1250 460469154 460469183
    0xd02060f0c0a021201020307090b03091e010b100f020a03080424091b030309030b060303070213061a1c2c01091203200d090b010e040b060603091216 65
    0x307000c5100140c8510032101041c0c0b43c584420b146081b0b0008a507820041445210180302000c1d1080144d0741c0030740c0740000c4959034600c564200241e0403d000c1d520390140c0d100da0f0a40c032941343c003907500d00c0311489501c0c100e00000d2050780006d507603810080001d0280300c03816010401740b040700e42a83c0802400650949501034040e00000010509a401170b514036540b030f41d010211816a110780400c0780c4d0950345000c445419501e50361303000074028100da40c0c580720402060b40143c49000000003110445500083e21602d800c400c080300c1c400b10402e00380c000204000b01c1d015442d550700c0103405e0491164000465800c1e00b5002d5800b10b11882c000f000d80096aa05107803801d505401c0f401c0520700c904640401528800000e406507902c82a4040030841c0c07030840200d890007854082c1c000d10031f920101003800791040c0c0ba002ca10304000c4e0010b0031103440c00d208000c1030107102c4034080d4102605989941c0356103801440103480e6400040c503428481000203040d886107441c0102c2c00d92440c3c101100340000700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 460471654 1250 460470404 460470427
    0x100f0309030c06144204060e040305120105090103080a08070c0c0803130504020c190609021e0102010b0d15091103010501090b030d020c060d05061903060209031e07050d02060f 77
    0x4003110b0761904882c859000c062415044201c5d0340741e202088010310720a13004154008954440000756a40003035544d003002a00e5003081d68914015402911081d0f03a5004003580316460140580165004200a400400025270703110201c681231030040c50452425100d00138102c5040081c40d8000c1c2ca11120607a0108110324040000d18580d0b2000c0402ea0981d5541e10038030060707024044165030503030400a59803d0101d205000c002800c0d20906c40095036202c079074000384000000289032040c500540b9818010342d40c0910800b140c0c485d04960b00700f03035000c03207070b5070a8121000780b0042c0c000c494a541c0e01d40e0421041d041d10441101000b4003d014644e140d190304801042c240c18203510038402c010518000d40d00119038802660343c054071192400c01883e80300c074003a140c05000c0039044003005444111601c281c0d2400e0000d03512484000d43d40f820390100f00741c03400c070819041c080c0c040c010011001d440a00084c1a2007164400c0d01c10501200302400040c80d00d0151007071156825400055240085 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 460472904 1250 460471654 460471691
    0x4030806220b0301060611060c07260a08010914011401021e01020903010c36031505100b0c060f091e06010501230901141620100f0309030c06 62
    0x400b0158000c0003060b6a500c8100c40d0101c0c100480a01da801c000c002c500d25400010007060070324060840e0081c054003603000901221040c01f42d01c81e40080105513460a1a80100e1007801044012818010a000000850a424418419a4045071402a0010507030340244501d10500e4208603240000c2d00b001e0750130074003039030000b21018820751078044084030450250f102440c0c0201d8004800030300c6c01c41c0782140e10031102e0030180081d5041499a00000184000c040e00540001e40400402c10303040100c0107610780c1c22076411002e0360050a01c5140a400e8000030340c564003280c9680064000e444482d0201d04025800d001100343c5004001c0030b001d21700c00042c03540d040711400e0740d54601603080c1100076082600005451882c60404001d2448298072892400410700300b0740718120b00d820700100010030707070800082040b01d00100324400241130b05441d080c5941414070542d00601c0401402d20004c0007543d15544503001c1c0b42c0d03924194414144a2481c036013107070380e00a00c2000800c520313030350a9901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 460474154 1250 460472904 460472921
    0xb06030c0105070b04030c0516080d031a1c170c0706020705100c0605060a0519180b060a05030a060e040b010504050610090b090301020d24090c080403080622 69
    0x9124142a0301090351107101228031072900070201103026102c1c0d0340d0803a10014005402c0c0c500d8070440c074a83d00780c0d0000144a50081011500414060a02c903002806540c0315820007a40001c0d614000310302604c0c0c5403402904000400303007401404c0b16901c2e009c10603d1080c2490b80e5003000104640d0307540c050001d0700c50181c41558003210700365a035a07010881701034801070880c00041c400701c03480310000b03402c1c1d000076400203030042480b1031560710ba601144c4035502c8071441c11a03c41108508108200500000c03421011140170b050100c44604804204107229034803c0038100040040010340c00b0b44254064400743c8606000d1107003606050401e144a48001c1c02601e00c01e51419010030b02c140b419071621681440320b80c9800d5034061a114000050383c000c485110740554003044000c1c41280c4c07500c01d6600303c1905056811003200400400048086580c204c3e500f1185417500815901c0c0c2c006459940c410750503d0040c13040d550300c10214601c001c050807100e9102c44c21408080002c0401e0f041401c030b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 460475404 1250 460474154 460474159
    0x1051e0933332113021c03020a050d05130e010e0103140a17031e040c0603021b1e070812030a02300f0c070b04080906070b0f0108120406050d0c030f0204030b06 70
    0x800c0c2c403040394a520111384144020750120070100131312821801d00e003a1400031402401a60003106007a100e403401c0411000605000807000600c4078100e0040c4180b08014250f2006041c200f9814400b64404484060001800d00d0380d04039420f20881ca020001090040d5000b490004142071014010340300d9003055410341c0c00c01031100c0b1500009010b94451610941d04101000922454000c003900258030020044280c00c00084614811403420410351a12038002d4030100f800a9a205c55a07042c2801c5411200341c6800c64004000e4011001081d00c1d040307800d100c001607641003083c81011060000107034042070041a4220940002c11410002d84a04a130801704601903032402c4410200703100b4041c0061040e140280881d010400601c041c081000d070182180d031910803640c030340c444c82a904840c4500314401c2100140b0500005102e8042d0050728070310f240b414035041032006440d60103400040d03440c040e80c2c4c46d046003003148240c0100e6440800381408540d916240d042c86c40e41c000085500a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 460476654 1250 460475404 460475467
    0x22808010e0609040206092407081206100207061b21020f010204050d0b0a06030602040b0703110a03090509060d0b0a0c2601051e093333 60
    0x7200c0381404500a4131695000b00540d00d00040c4800f0000d80c20402511080d400c8a0303100074210305038502c4001d01c461401111410b80b00c0c0c443d000804070340c00d8010081c501034410240008402c030340009400c400d9030280e080c0304c3c1c0e82c400e0b454200c0c4044812000050141284003026406032995618004800e00e560b500f9582220031402d6042c0c241e1041d481400d0b0001804480f440114583ca981c1c65040240c201d800300b0220344d42d80300d2b031050740c10079040200c0102000070044101034106170002a6900c0c210042c003a0b0440d581c50180860110f4030405019021000c000b4143c0e655100c01d041e0510b600824610041c00d00103481c000030080007241c000400c102105d4040c4040c008a078412080c41412261291a0300b0030087c407030416a40d40100340324000540c84442c0036980c0d00e1210b8416011104916050450194281c2e80100711000102d41817070344540c0301170141c8400702070b41c807820f030000e4a013803031039400e00004d964a1240005070140c000001c240c2000140b00303482216401485805100d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 460477904 1250 460476654 460476661
    0xc0705010b01181415040e01260c0d03120f0507020709090c0909032c01030501121110121b110d0e0f22060e010f0501050d022808010e 59
    0x43d10000c00320100840c821540203810000507001180400c800341004c0c0810301c0c015200340110045800c01e4000d010f80c11003840062007690345001030212004100395810068122420740d030b6848200855a45000b806442109000c1c0350091000c0380300c3c009900e0042156400d00b85400004004c1070701d1700001802a0000000c110300c841c0141955950031100a0ba03035249001003020042200303200860130706c8840305c8036407025070802281e070910103ca901501c040b00002e0000408540c0140c2103620050301c80c0c240d03140804c440a0802d500d403201500e15560407021500b003641e03010b00168491507464104182e20208000301c005841041c4031948407101015070010344030341c071061000501d00024240015a210714a000020340386a1000540303407032107101102544c504e401c0d0280141414040d1689410840c401c07040000a00422001a0000c80e090505000070024804c854280d84010f402281d4102900461105840591900c0b49400c546e22003056000d01221424401d20700c1c00301690000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 460479154 1250 460477904 460477907
    0xf141b0402070302061f0506030f06040507050708030402130b030f032104050d0e04020d050a0e0f03030112020d02040e0718050615191707020c040f140408210c0705010b01 75
    0xd440c116507043d00030b8031700c55988004001400f090401d9641036004d6901b4000b60b151143d8000714001c00780e20007000b8044c90308605210076a0f0000d0504010404100204070104010100f80ca81040d030440384003051038107002d0030300080c00b85842d00795450b001d6541c1a46111074000000c14130a4110f03089090f82e800410520112400101c40103132254002448413030071248191001302c6240c4000b8030040c203040d010841c280880e00116001e03c0d10340c0e40c9103400408001c04001c008401b503004402103140d0360404040046440401c7d2000307005200a907a41d4046503515040405042103c10407034000941e65004c1c40c1040c4900300c7e55094140c94500441d0ba00d0910807034220003541690400b510b40500038003102001410b4541100812101c010985c0c007240503e03007064050401980102505d910401c03c12085a841020706204207241c00801c900d41c056172800c481d8029001000300d03458511510743c02252a03003023a10079282091003801c10418209003800740c0425400f07032008100d0602d24200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 460480404 1250 460479154 460479157
    0x1509190f050a241b05031201031e1203020a030e062e06050a0e0f030604050f12270d17031b070201020a0b0604090c0b0c0f07061b0f141b0402 62
    0x95484001c00b140100d44441ca025a2441d40041c21001100d070640c021074a40c0c071b040d82c1090b00101643d001c054010800e000c07085040140344d011603090325001c0d14990341e4845203040c10144040c00e146c8c0101c0c3c8128a0360082e840740c01180c40040c180c2d0321a02c0d00840607080074004501e01500070074806d01c541c0781f41e00c00c40200e03c107031000d540b0784910f4503030785c0350041d20442c8008030800c0e48119030541c000c405d40c9060001c140030b10f11503c01000c1844400c94007a041c41c0303000d15030f80c1c2c002500303024062440b81a01d604000d08a4400c070810700c9240401d012421040b40e40c1d402500c01c50b0025090031850030714100452140b0701a40603035608003801c40062806100d0b0190190050b400700e4400c0000c40c08001c206030b0400c40c020000691040a56507550440391954000000c004001c501454140014403000340c2c6039074090003400406040c0341001c0d03c0b2115030641499028411074000e0204484903107070001c207942020614000038546180d03c1d42d1a10314552103500c405c8421118621400e0500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 460481654 1250 460480404 460480439
    0x30c0619022a0409290106030b010509010915170115020706050309101a0301060608060301060504050f0708041b0b0a0e041107110303040e0f15030703021509190f050a 73
    0x1044100c40e40507a80421014107000c8101303595030807017062110351041001c42001c0e40b112641403900704640c0f40101c081c04a840d1416094103000781003145c00d03000e80c0e1000c3c40d802a9803881489203045414244100c440c1c0b04040030b00082081540c5c0049102280b0604c100300c6c1d40110f47c21940e8440d00c58100711450300003601c00c6101130b07100e114031a40d1054550010001d20880d0a0030801003058280020300b501e0031688000081518001407081d142401e0040c0f03009090159020301003070030b022003841c00c50107000385540100110103002c00c0c204113024905280102d005000c80c281d458440030b154000e517204d03400070380200380c80b5070f80200c19051502440800300201150b00d810103040362610000030145e11212503240c04100008110300c04110790a600a50301401c42812074980362130752401c205124902d06201c0d9000000400041e514000200e0111440c140d82c01d44800b6801c0104907591004140b440b014404200701140b040301d01359502e0102d50040310500c0c0200c3d07440c40084040041c28 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 460482904 1250 460481654 460481713
    0xa030b180d0c26030105040c020a0b010f0905010801090f0215070609111206090c060a033909083a0f1b080406030b06040b0705070306051510030b030c061902 69
    0x13800104031a261503880b80d1204040d500654103000025a00d40f007c2c0d40d426080740300b50303c400c49014030000c860782c421b181c090302d0707000001c100c02c06454035050a04885000000d10410b4950001a10521041c040d00c021981c0003205000d49112807070015144003110002a0003418100b800000a03080003400e24051a4a8000303405015001028040c00790f100c0b45681081c107850b16844030301c40f500c2050740c0c41004580751b1403c80c0c1c25803841c48000c421800c050f4107020414004020f000d10b0300e0106000803207188409016610040040540c43d05002410041e2070f5000102410010f10703400014941c5101d0f0f103a82c600e01c3c940c0c80c8c0c0c000098904c000d042d01800b000000d00040c01454001c0d480180a0100240b0190070240c0d60195061540e1000000321070700e80012008004000c01801081e8012141c410078030840310840c004281c0403a0031560b20020103440c0d002e41c1d51b0645003400340a24420001e4103541e03940c141c0b071444008081034104000014070800d45602030b000a03d900300c20000032072 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 460484154 1250 460482904 460482907
    0x111807080a0f09030f110111030c03060a05032e090609110a05030a0b010b130e09150c12040b0a0605130b190f0e220302010c09060e0a030b180d0c26 65
    0xd540222100d81180d03046c0410707503684000319241007a001029610840c011080140c1d24907199080c0400415240d0009001c0d6005c214803140d031300115100c02c4441c5c02d9420300c9203c001c02c10031194015209003c000b0f4061880c15460406112890700b1300100c2da40143c1c0c4440d0065600c00c20306548002204010b000340c0c036001e00601910160900800c007164581051040d070710345545152851520039600d02419074041c1640036920401c02d03084503880700c40603d909041500051030024940c4008000808a00303610300000c0001c5415031181024080241c152600426418a850014044154100d100c0c03050100c429070500e40f002c40c0c0900b42d450001490741003e2416041d1101c4031000b616868035282c0c10303a00c40c2c8004030340300c0800b000c1c18065400440d583c0c980c918007400c0450f0b00d410800c10000208000074490710741d5a03002c41100d0380040c2d07070152a40d680d0039411f0200c0e0401561000340c00340c40703030203040740741d0020050700454000e2000c90b801c05901e0b18080c10400461344c85000e040d90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 460485404 1250 460484154 460484177
    0x10605040b1b060f0a0c18120c0902040603060801140405120d270311061006110c0904060510140a05010c140a060204090608011503111807080a0f0903 66
    0xa0001904000b8400180000b0400ca00709109041020031102081d2185001080180240036406120b400c2c0380241848080d404c40845011800c4e030583c001c000c80342424a0403c020000c0e101024030082040c800c04640301d40e00d501004000e1320071403043d11119800c00e14607403090340c001c0d42000e02032a4800010100c1d001c07030360300c0c0b010340e40c000c80f19400d00580e6603421410158129103030b04000c1490310b072014076440c00a140140000031b440300e401e64141d1060040010303c2046048a005950903410701b4a0b0310004103101d41d1819045032a01c80d0040d20500621041002a412260207000d03600041c0d10b0b9161100142055415003010301944000c501c1403c004650280030048400340c0541006601c904c405440309252280003642103900350707800242040851801e1091001500c1d00b14001d129510780c0000c5070550345154040900340e124800c0001b06c1c241d81c2c0081d01e04020351030001030411413505a1000e00a0102207803132082d4282000b085210003c243d2249440ca50ba26440b40c1181c0703607 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 460486654 1250 460485404 460485419
    0x15051f08030706090804120b0601030c020d020c1509030102160b06240a3e0a080f0d15080a030f0e030a03030b010509130902030f1f05040c0504020f0703090e01060504 73
    0x2c842c1100740d076000000c0201180600380441f1a045c803074000d00e1072180074145400014100c0b03504600c90421500032814110940c0c0c0e010804a102d120200d07408107034200107141803c0640710f00d040d100d03455840002e1440d02c1c040f5100062032010300a80c08a0040d81d19401409400a2003085100c1826211080078581c0030a46d0040d00484002c2d01d1315485400e107029070311800414600203040040740304010b01076441000881120058030803006483c03c11180d6440841c01c2c000c40200e11450030001c607541912481680c4015200c1d081c0141008203a9030302d011b29524ac0c0ca0450003980010403042d800002070f0b014040720030180304c0160040c001c400c0280c4049000f00614100c0e00d04026081100740c0c2145d545d4101c4490017120440300085011140c410513103081d41503a40c8003c0c83c1c000f403120481103090414040c50504401c0c40211303403507507a403410500101030b80d04000c2d41b01c0e10100381407400001440180100754480c1c3c41d801002034464011840d42c0e1030900c68800040e508010500c4181c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 460487904 1250 460486654 460486661
    0x40b09070b031807030c180e070614071704170609030a050906310e0a0b0a230901030b012c070507110303040905190e06040b060d15051f08030706 64
    0x850b509420303141085d489645000342c822081c0d0104940911404c10052043e80510031011214192030092102500c1d00341d01410441d0429165100d02001248520900023030640300b1030a4000034041d00d03916500c2c0e908004051a41c001500701c14803c03500014404480081111a00c12280e11414107004848042182951001e10024040d429000c00d5199441c07508401940191405602d807464038280b8168a41049008101400e544e042000704552621600076030426140c04a40088010104203c0390f065160782070030554101081000000034480281c0320035040c2c440070540042e0040d581540c80311b641040024a100c2245520080f8003200d0040008201480c4526001c0400c40f0700500001c0c115045544841e5900b40c450041141d01c0c40b192130001030100301e55004102517580c202105644810041005015040401c00f14050795107040500c1c0016078400706142d5810b03807004501018200681c0c13040646001d4a00c104517103412005120203a800e00da001303500345132068581c1d8014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 460489154 1250 460487904 460487941
    0x20c090609090c040e011a06040f14011403040303050103020906030c090a0209031204030b011a1801200102030403030902011e1d0f030a03030621020904060c020123040b09070b03 78
    0x2030302c0350711003c08040c0c03603900504441d8108000000380c2d040c0e5040340003513140300302c0f15010b200e2202080144160040107101d0800d580118010a6001c0007090060341c030b8000c25110800a04000320030001016410742029050701e200740d03000902c03074481c1d50606a556000c00c8000e50700860200000703004410300e50140101190007001c440c030300882d1641902c4660302c90303001581c85024600040c82289030340e081608603040c42c94403941c5071003440502d1804c40d92480d0240c504100070421b001d04844415014420b2400c075180085549050503d000340041603104400c07408100e280494401d04908040440b00598454a40030b11240519001045000c501d100090b409003251085402c5c0340c40400041628500c00c4c0c900181c054105a4000c11050034038480c41c2d0840300811603400141c950820721a089544900003140649100206a01401e00d03440d002102c507203080c0500c00410380245060380114020703418004e183d1a240140364480350b6038050070180000c1080401e600051703100303150300f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 460490404 1250 460489154 460489171
    0xe010b16031e120c0207050619210c031b091e081c090f05010c12210c120b030a02010c06230702011401080c122416020c090609 56
    0x20580380340d000b049604a0300c4003100000300c1107a89007040400c44e01c0703503182003903480c0018070800d864100040d0b007510621040c50600c52061513904040c074040d0952800c020710f898900c11f070042440c0f0024006280c3d000c0d100000900f003105081d03944107400001040c1008954501d9a11400c222841940c0f1803178017115042d128a50100144841041c003020340c44103549078405038499505800140341c941503420031a0f2800c00b40504101603a004003030900580ea01c00e5107000240b4180800740c4010060720324000c078148403d1150100c000099001c045c2c2e0b420f0507161812000b00b0410005e0844858008c0a0781650240750b00741d02540c0a02e0340c80c0101032254202150000200b5009000c80d01c21030011190340d1200806e010000b902070080705000e0b8240904000258500403ca542d0b035800c44800783d0140c020018042c140d0b140502c200130003d10180b0a410b010341c000b0aa20410510480300304007400e2a410704038200c00d101090540031010300909400c0b4640303030a000c01841d80d001805441 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 460491654 1250 460490404 460490417
    0x207050606040b1c0c05030d0e0a15090621090825050d0c08250c05061c0f021b1e0601030f020105030717130b0109060503100902010c0f14070e010b1603 67
    0x900355010040c0501c1c1008030396804000540c0c0303d0901c00b4443c0150046440404902f0030f0a070900d500460050441c2d00700d290a055035100360300c0310031880c04000d4501c0b248070f00784050f60b000d001c0030500909041e07d10313811110403c0e01840182c00c07041200c04005010350000143c2c0380209100d4500040c0306c1e80290080d915040074044d12045a225180d04411264510580030041c00745a620709001064103541c9a441c140c400821042c000c078011219003802c1c4e940700b44001e14508142c2c1542e4021001c034001c6c52121942c0d00301c15603695001240c0c40b041002e107151120400c3c4002c0380703040c12a90711a2010300000c6240e4015201a000200b2407400c12194203444180010b1a2150310b0107101b02c0c009441c40c01115041407071045e041604040d125905101d02002292400606088600e00c4004002910015840100c603112402440500540410200c680620842181804104542c00200c0f400303207944010392880c145092107803800c07880f400e000f03034020000044803801c1014400d1a114 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 460492904 1250 460491654 460491659
    0x50f010503010b010c021002031c0605151c11130915080304061b030e09070c05060603031305010e040908030f09010c030902010c02120c0a14041d0d050706020d0606030207050606040b1c0c 82
    0x1c800640c0d02b400c031b03d60035160701e81002a410940c002e011040c40e40c0c20904e24090704405400c0c070b2800302d0b2000c40310b080d644940c4201c482101a0545e4075104880601e00c122660711a03580010300350010b40381d400300380503200000b11408000219030458140d40c5910030b20081d0014581191602d044054060000c0140948925a40d40d40c05500c191501c1e201c078540480d60341802458481e000344500c3c0a0351082001c0c0424110902552040310024a84883d4041d55000030801808403004002c3c5010030100500c40ca2040c00da1201d480703450004000c101c85400040114155810140080d0100e030001d04928050b081070411007184002c9802102c04095010001c41c281c418160720000c2c4c50044a03500161901d05401106008040c2111203521134243ca1230f020f4542e91a0207901051180002e251010001c0a4050316070b00e251000f000c000c2680d55100c050040e600c40d000444560056200080c030f24541480342818142024013920881032500307028010f880d80b41d40003651840c8410600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 460494154 1250 460492904 460492927
    0xa0c050d030507030c0804020f0d060902030d110f030301031e030315030b01060306050402120105060a090306180606061b020402090402070b0c07061401060c0210090810050f010503010b010c02100203 87
    0x800385200065a000140d600e004200207080315070b00700101c1d080014001c1400003583d5071715100780030400101c50082100380d5904d0500000c00030008000d405024401122440941001484503040054815180401e945094054491000740001400201c05503e80b4500356080c00d0000740c203074881e041c001403040080c0f071215003009082c1c0c4205e42000c00900140802c960501528008150a41c3d05500b459601c40005200320b105000322030060a020842001151084800e0b00066400c600c003000400f5884262080b0041005000e0703400701d0900c800010080d02c244a010703d10700d42710040048541d0283d003004003030b6000d1003a0591043e000e00c00080840ca102c4407850240001119440d6130b44580e20740b04003a5440d00b2003542110910200421005401c000c6130300d81c82d0b50465480b1841c0c04c5004043e940b08440d03400c603030000d106000f85801d01034911750003180180201980003516070381c1d4008050a0f90540c00f005400200c8041030100103040c5030403409003211460040d24141000d1450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 460495404 1250 460494154 460494163
    0x61b0503031807050303090901140415030f0209060d030c02102601140d02031005040c031406090f070b0904051e0c120609010308041203020a050609031215150a0c05 72
    0x400d2410b0220008901081610411440c0c00038a030580c080c43c2400780f01000200704020500c143c1040380c6034100b0f02c034407565035541b040101c1c03c0310b0503240346116200e05211042100380c80049005141c1280880c00c6403074080125081e5075455540c0e00c018404a17400c2c4480a5004014442402105040c03a0075103104031000c0284507415111102ca00d43c500f0704000740600d8102c481d14040e44090b40c00304007507180490b40c594221038401c00131505480d2450004d0032550941e001500b0159114250300c1007040c08a80c00c0c2c0140040c0085540f00f0740d10741c0300d4a813203500313a00c07417000100e404202610305820107030011a4000309544140f1a0340c5203c5c0281041741c50211012420204c0004032400c422041180c50750300704d4001d9640e0403003581141c0d51900144114000c0104d600c1e036504026080510801148001540c8601981c915042c4404240d0b030340c5d00940340d604000c00890002405030105c41c0001c02070b2450003041c0030a10314101840c00c0c040c0c0e202059280070044d401c05510302280c0c1c01c20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 460496654 1250 460495404 460495411
    0x6020409090314030405210f0a0e043602040f05040309030302070b0c0a080904090507030b090d0314070c0c12030f2c100521040506090f07061b050303 66
    0xc50104064940248a99140219680303181c43c1401404007060000400481305a60340d0f603400d41d0070741c2e1074640031014001c4441560840304001a0306030140d07802006041740010980b0f042c82004551a64034200c280c1c8107003001c05810120440071549070811081c01c91840c0007400c0001d4600315165450242e5200700d4064010030340702d510030410540e040040100a103103004140d82010b1030401c140741c0782d0122200181c1440e10200c0c8010140e62640c1c02015070645c81404c480900340c0c0e030318150440c80c1e070440d6541224042c4003e1a110326000303004600c510500c240d03d02106a039103a0058030440920340d003d441404620070046401c0380c0700480040082d02a480e02c07401491503000061141c588072041c4950310a094001c0300781c840c0080030fa07a046081c1190152803014010400f2580d5001d04101070100030b80c42581041c0f0202100b10b4039000d2030140c0c06560042d0b50780c80740140d64800d0903c505130039920040d0f041180c44c2c86803601c40d58064215400c0034650002e522954610780003139 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 460497904 1250 460496654 460496669
    0x5090a0905100b0f0d0501140708070c080310090f0c0f0504060c0b0907030f11090610021507180f0305010b06070812040302100e0f0706081905090a06150303030f02091509010c060204 80
    0xd0703101e946030203c8c102a403603207c051490000300500e8162401000c03c0002d03070b00241501c90120208182130052008039018101f0710030100070744011341d00d028000c2e060081008007c580b50504518000c3d2041d0120350654055440790700c44060540d072805291030f0700810051040c090400b001c400030399110300048041c0d000384d50345042c50343c211040100e10700c0702400d00e1344a128041204401e417500440da5402103400c0d003a0719100c0344c6c2c2e035410645181101123038200a041c14088085070400b15a464001941d001e0780080100c03059550505c0440e20960002030420381c4107020301c60301c5071078001a07030f58801c0c441d01c15921420400b400100560f440c1c00c0900d03200e41c00903c40d00b014020704002081c01010285042c40003810810004941c496484c030002c01d6480e15403000400d054070400890521a034803d808103c00c0c9102250b40e440f40301c9600080380040c0c104103403c074000100c0d0080c0c403407020005002c40d060700a503120200442c4c0c080e00c0000e050240d4031101901180761351018000900f0036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 460499154 1250 460497904 460497911
    0x110c0402120411090610050d0b091f0b03061507050307080d0f0c1d0409031710030b0709030305180f09010b031605071208180a0c05090a0905100b0f0d0501 68
    0xb483c00710007512943c1e6016010315028000c01c4100e54414940a5039201941819940c4110391400400075040010b032a64010068505101c1020070342040c0c1222405091862904075440b8a445040c80c0700580302594170203003000140700314100c010014811f840c4901c040781c3c45c0035170a80e00c1e120f1039000700750b00758101c07550742003030400702d080902030800311061903d00007402e9021000720704980480104080e0103250343d802d4080c01c1500810044041b454490100e02d6107207480500c0c2d0b607560009000840b11001e5400100715203078003d803107880549a0640740c45041c41c2c0084001409102d1440c603040c0d00c1421300c0315150031030b02c603942080d02808c40d4169140d17580c5811040c411151051401810401c0010003450340402c4070a40c8090103280303940380c680b80944402880709066919903451804a001d07421610003009514170140c41210010f80303040c445a550860000202c075a42d00d0007071303c580c0000043c024060850790040c005050f00409030003c5141e81008205001c00c500c40444040c2e54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 460500404 1250 460499154 460499161
    0x40c05091c21120f051006030c0c1104020405030613030f0c080409050c040512010e190c0b090102010605030d0c0c14060318010608070602010603170c100f09020904030c02011e0f110c040212 83
    0x46c22040025000b0350400748a4241d441c2c1000b4148007809401612940d1035101807070050f91250102d03801428000e044802e41e041299081c1600e048000046000c644403a0f12100303c14041d81c4030300c108a400c22a1203040c80d2800d0320341006440000c0086210f664200030220742590741e840000d8880e035a0134000103011191146251820070b442c5c600c3d076a407200c0c1070100c40000b01581c2c0c00d4420350b050800166100c8a42d030340184e014149581180750300d4000c80c0da5000540398046000c200c06405441c80c0d00800b40c0d21201040300f149480c0c0804d0700001d00f04000b8009205244407401029501c8000098039543e541005041002a030481c60041c0d440d80001c0051042026070981d56075000c001c55840c142e54205055aa03060708140c10324401d84820062614a0507035000820040c0c01a0032582c851400c3d240080020300350711002c034081401074010840380321070b901d003440310143e9a807129040030303428030403d0780d0450040486400314441c001005083d40c6035800500502e9010303c122001605 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 460501654 1250 460500404 460500421
    0x90303040c06140412050a06051807060903081b16080d03050108030c03040e100506070b07031a09150d05100c110c0108160509040c05091c21120f05 65
    0x10769640c414003c000150400e0141400781408403000c80e01105050b10408000d0301d0001e0a02e020310300b02030450f030b00d4032080003802078552104008a404c10700039034880f10b0b12070741c05460300b41c80b030700028118120505c10ba181365010342519044c0c0941d0312003281c0c0000008040500c14110310740000300c0703503041042100c0b6802d030980030b4203024180400203941481c0140d030800780c0d603024500c907010050004001080740080e100380004080c140240030f040c0d0b6503810b802d0600041a081c1c0382040040d1405641ca1003218011110444000c1c0c018096115516169109a882e16139135819950002112102c40300003030b82000000100d592602003c01d03503011004016025420048203408640c01c60040860756a0f40a585642d008801c02441c0380c030448041800c603100c2c0100a4105d400601d85034404445030703084805800910f0086a5100003070f19800244841101000e000070001003a6035081c200900110700b078480811803500e865000c4904a1503500240d500c00882400700903581c0c0144090728 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 460502904 1250 460501654 460501673
    0xf030b0307080a030f0504080304120b010503191103030f07230303040b0103030807050705100509010609060b1e0c0601140f040203072c060f030f0612060f0a02070b09030304 76
    0x42012409440d00d5894060210344800c1e410500408210340c5444c01c0c100c960088080d64041c04800f411251182d81315849005007605c40d0388c054903400f844500006140c500029200d5028041d444082c111807019a02c610280c1e410020319645804244060380c150513682020342035940c01444000b05000741560a903121604101145289030070400411010580c81c00c90181182e0341490b00700c40907504c01d8000c03104c50107900402040d40c043d002c203820780710079181c000038081c80651000b08007099480c40008121412449580307001e000510010045031020783c1c8551400d020400300929042d03000d0281814244246c01c0310390624075003543c59170305003041c1c20000a6a201941c0c114694100340002401610211844803400031190701c802d10b803503000c207088810041c0d01910b05a110714003100c0c2101c1c90b800480b10304564150103000030307540b464039418115010340c5180c00b405041c1c48800aa41070400014804103841d0303020400e0000049144d03201e070384111034070381c09142c03641803514100040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 460504154 1250 460502904 460502921
    0x110a051c050402010c14010603170d0b0609130b0a0e01080607030507020a0308130f02030d020106300327091407030b0915030a0b01092a05040b031e070f03 68
    0x800c0e00d46000c000050760004100c408440e0040b1501622400241d101805884181c00c000d2018850b4000c2e451800c64000140084919085040c001c0d4401c14050040d01c2c051207048030f074401c0000d12004089002603000201c1c4803009006544c032252507001c0c01c4100d0304281c1c02940c0c01c0d40034000b00903a80e60305105840d0410110b1029081e140c96a440090003000c000d082502c02408212030941080381100061021036800350036240301100c00c00b0068001e18203442640c002490b011608408101c05181d030101100c03081c0c0303149405140c00d171811900c46102130700e2280341c400c0140c030302c0c0d82d003100008040c0002c02c104c10011400320b20022104500c2100580100c05050410301c1e41000c44d0780e183c96070b40c0d20894020f64500800e14000009103410801413003e403000c0c422900106980c1303802c0e0000c02030707007403c0010254031802d00405c002047c04210a940b002400500c414000301da001002150854034410b0300d01d1000c1310003018182c1a0b6420717140c0c0c102240c2810310100a80f07030103004400c0c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 460505404 1250 460504154 460504207
    0x50105072105072108010329090303011d040507140112090b011809050a080903011509142d04020f1807080a0606050d0b24070303060b090f13110a05 65
    0xc60003c2042c00b0b01700d2241030200500d1603906d00070007241d442c4d02c0d041d003503074038a010565030034181008076980b5120350080c02030921640003074024030f00060380030355154096503101000342891850058075000c0c1903201c0540070b04206d040e0900041c40b010900900c4031a90140554a1342035250840300c84541c4441000340b80410700304081c26000c61404692070a0b9241c0141c80035640e6444580020b00512800782c91142040d61964007113002e404641c00440300c0901c60322964115160319083e0070000310200040b0344da40c040501c460440c0c1e00030b080c0158000f440509100200c5070420300040c0d00c400042410801a1205020000005d0784116125080540c2103020800742c2d050000081552140d03141c900e8007961500d01c00522611600380c440b58100c844055410440301c0c1e464090f40750741c00208140e0000e4181400401d2240554084440469005007004c600b0541b110500c81c14a001c20f032102142c5596101a1201c000030b00020514070050f6a2503956840710100f4120b58413494454028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 460506654 1250 460505404 460505453
    0xc1b0d080a08040201050412060609050604090c0614040506030403021b010f020d1d0402070f03120c080619091503031b0c030305070f020a0b1c05070905010507210507 73
    0x10086216602251080d21403450602000d0f9140d00069505228070341c04800a004c20034901000c0c0710080e80007109480c0454070a00071616450104015900c141030301500c20380208600f00080340c0200300c0039885c1841c03440a40d0403e9900c200040350f07900115802e1b405038100c1c007503500b04c1c580355041040c05050300b403c080240c0d0044c0000255a903ca40059809201c000c0805180300e40d080c403900d900a0303c0040007507641e0301c42440c21811740161014110301207085256001080c8000b80185440035406658002d00c65581d802003203200048004451600c66801070042444142401103008000041e030111400300c0c91440d009021710383c0b803020035060303c0400d904e079400030f490822410203c0f0b405140c100e803240000c4c00c000c0d04a041180000354807040c101000a41c10b40218064110303102a8800705c19440b03000304000c415030300211a0b200010781e0908040c032556016501820007140145040441d084104100a201950001c045804a400410f1450130010341032230440f1000c81c5005141c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 460507904 1250 460506654 460506679
    0xd230a0b0a03080f1c1b080a020415080403110601030605070e1801050f0315160e0d05060f13050a1b06050f1c0e0303070306090e07080604080706110c1b 67
    0x5000b5402454035900303d98400180f00281d51246103003032551701c02c07101020812150300110004000900c1c05204010502c0c410000d20003008a201303940803030746c080f4020242c044600404646101c0010400ca05024222180306400c00381048002d02a520403440029642051413002d802131040c40400c500c2040d8481c07411202e4150240307214115042a101000c80300d0040c0002401c0410841c424100162100700301310410b0b03031030361046204604640f124051520414244880800c0720480075110364030400c0404c485142501080c0e42c0180704120703003501d210b81035a40b18245116050b00340c2d00302c442d031981e1400414184024000408080c20701e14541205070060850a000300350000da5000000050040c4000040e0408484015048280ca90320302d81700701c019004007528005d0070b004926002c0782c1440c5e207000240141c06c2c0c1d0590001002c0d5541c1d160303681c54241d401040c045402036241d5980b403000e60612030162001c400d001e0050000b88411904401507140e03214239091040c503042021 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 460509154 1250 460507904 460507913
    0x180b16030b030307020f0d0224040501030b0a0303020d202a0f030a030c030504030812150603060a0302040b040e060702030a0237030306050603090d03110406140d230a0b0a03 76
    0xe0401c80e41031f58011207840b40d078000100180e1404200041907403280c0c00e40c000c1c0401840051043d00c200b6201004560700c03c00034481c4400c850700000f0702583c882e80c040c910043c0184d4041d000405942034030117142524a146500745040d15841000304909141000500901030b0a45807000fa41900c110a02c514140c000130f03075400d030128010b8140804106a43c0506105500b120040d54029081c20f90f901000900759003c40c01c110781c0ca6028545150a441683c076055003101d004680041100c2100c030b05540800004114107042c0d0355115681d035001c20084a000d2191500c1100300f9000b40d80c075200c40210103030821201a290300c5004030046c0702400040c111027010100d0718122503101c10401031514040c0c004002a070402c56010101004100504000017100c0d9208481c0c2e40d020b0104807005850100b0030301950060202040c074104200d0b8113003036083d014101c0038040030130100d90140c141020b0706443c840c0c0c5849900034080320080107000d613540e004a03141d1420a4480164040c5107896 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 460510404 1250 460509154 460509169
    0x90209010b19080a0212070c0203060601030e07091a030d170a020c03040902070201020f150703060b03160f050f0412021516110406031707171309180b16030b03030702 73
    0x204803d0110000c0810380c00a0b0943c182d8054072000c10300c040741428442e40140141c03014182c128030070b109060002e0308035403081c01aa0700d8281400000c05516060184084c058074140100031503036122b124080080e9901000050140c41c43e5850344071442580c18081c0391034482c02011000164010061205c0c10880002241c0845c0e100440060300c51240d0f02c0100d0400d034003043c40352280d04c50361121002800b070a0341204d00039070007034504100c2a551008002030a010849080c80c4443c4070240c1d00d01528091804910108880d01c4d0a40c68040501c2040d034090700960040403148800508000441c1000c400c0c40d0a01085011120b0800c1040182c0c607881c40b00600c801005201503040a40280c0c4032504043c025590000c51512165001845a216604542c0b0f082da000c1200c0c0600f1481148010120343c6688965020b4041d05802c0c00044405000c500344e01ca40e40c07400402070003001c11021600140540050b45030031511007901500181581c041803461072003508104070440c0103036070748172 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 460511654 1250 460510404 460510447
    0x2011503150903051207020c010f0c0c05090c04030507080a1101030506030303062b08090414010302100c030917030c07060503130b06041d03030f070806150c0a06020409090209010b 79
    0x105102d0510718080f40c0030f0058904142690f010740c81800b840540100301180418021303a40c6c4002102900021262003a5030701c405008000582018041c1c0d09100c9400e9520403a410256454103a603551440d1030402e16038080c070b0481d00a000c0312010040c00d15111442a80c091038248414108000003039180d01c4090580d81c420200e07480980c40d01c0c8550031034003200c1c070552000300707100c011542080401544000c048074481c61070315002074007100100380001d040c4c030f4001d0441d070580c80c00c0d80002d6407000060701c000c1e0180103980d00002820b015481c8201e440b00300c0040a10f80700e141c00f4007454a41810340d0003503400e009060003084171030700982044000d141d4000b040c0c60701c180c98072030108004140355151309144030002400c1d11248040000150300580c81c2400c40c9046c0e07034400b081107a1207001070301c40310340c0100b844480d0144c040c1e1200c05081d602801000f074820200e043c0c1e803400103d0380540d005150b20394544510318158580b050314107004001e5800007a29119082800a095185d0b02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 460512904 1250 460511654 460511693
    0x21170f0a02090a15030b010e0d0f142d010f0b01080a0222060804020909010509030702041a0d0506091b060909041b0b190309110f030c090a0c02011503 66
    0x1040a8442d651660f0b95030004103014500302032180050f00b0002e028003803900303806012803007840011919007004020303406241e030829242d4880300c000703a450f620041c6004601620b98070031404c22802442c014840032580058912480242c20f15060106080d22280c2106211462400016a01903608030381c0d0703035a2040c071804005a80d07007110240d040180084411250804006013004a00d65030000f107100e0080d40210b800748600c1d030b1517100c860300340d41c8100c0b5020040e8000340110001400c0640044040202140c3c1807059103907020f01003400c5500305031064506a102034203103d01034205005e09460550f04921000503004d040000ca1954810062454029200e86000a042c40001202540d800070204c4130b010a440e550200a02e02e608504104444a15094443c080c0740e40a0306c150f40d550356100c100800c0318513502c000c001c0e600405a070740300d4050080301c001140030354418546a1042e07042050000b183d4002c002c00a00311f4a00314004920380c0815003080c00481c90782185908801001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 460514154 1250 460512904 460512907
    0x609050901020c071811130920071b050d060515010c0812090c0303430f020f040f020c010506060304020102060c03460b06040509090a21170f0a02 64
    0x402080d80001c00e10640c240e10b0418020808032a01100071f6503000c110b40d840d0b4001d200080310040b070320000100c400c0c508107581008011540000310034505c548410920500030211482d50352020400000c85094100e81642d42d92042041c500d01840007807000742c03428070744500030080680c0c0b440d22a1040781c035100c00c1c00001400041d44103004000050441e500a402e894454528140c5100b1075260034a0b856490b409140d0303a00f2442a6503d07401c0d84070440b88264000540c025240c0000e030443c49801640c000c4c10034140324940e83c4903800340400d1412102001603907648085000c0d800c507070000d020300e8800c2104005010240c1e9001801c5608405401d9219990703485108100950010800000d0502c010320382c0503041e48102d0519400304181e1104100300d0a103443c10854044928507201c00383c1c010700a200c00e210390f0a101c0f03c0103038403850f2041215080d0f0b07000d441d0b024520340140303080b1207010000a04e010880f036200c8034000b0052503019460986007070090880100100c0107080c5140d183d030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 460515404 1250 460514154 460514189
    0x20403120f122912010c1e0813060c030f18020a08030414060d0e1204060215090d03021309050901020301050a080c090402011409040e06090f0a0c050904080c100609050901020c07 78
    0xf200950800c00d805084020065100301e001c02410b00b0f00d8a21687c0c012280d00d000103070300039000309100e0380314030080080c002c020708070307030b545d0600074441c0080c2c1c04100769031846140598807a6205481401e4001c1168003100c225520412003624515007101e005504284400c0111003008014545e0300081184c1e40c0e902d032420030300c1042c01410440d103001e015106000000f0420b00050008200343c61b0181e0986e083c0408000100c5489030068803102a1a0b018400c0480028800d81c0644050700780e000e242d841c015a990b0015040d65010f0352444900e0350f0010040005150800c50b803402082d0380d2000e0055009070600140c0138400080020f41070241e07103080c00c1100b1010008440e80d1410042013005008a5a011349650745800c0701c8440780c5c0d10030441010b50f071090008040c0754441e0b101001c8004141000705000083da800341c0112441c0a080c01001840303903080c014418004d01100700000e100b0710f08012401500d0700a84441c0561b4810042816502804540d400982d002c01507082c24425 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 460516654 1250 460515404 460515409
    0x403020d0f08070f0f03030608160303200109060606021c080f06040f020a02070519030b040809010c050703050312060a0b161112060405060f0106050418020403120f1229 74
    0x219512004000c0e4031348040c10410089851a40108103000c1e0380c04010090710303202d0031551840341c608000745000c000042080024412520111424008040d8010032031010342104c2c2920404c400850b5010344840c801e120380d903410004100358490380b01824040e100084406011080054070307130707544002400001100790f00c41d50445440004582411076a03451310010007511420f10b03004052140341c490400780170390995400c108040e2030b00400e0045039509c60b035450b242d040c2d20068882d03062007005880e41c00070910500c01d16006501030005035075034240e061958031074454000c0001d0f00c14a5666001c1c440e826400c41580c0c1002441c2c00c20440230b402e6814402829003602c01e116500800e1005042c0362000b0200c2d160f0700852042c003c852454603084980c00448400b401500001035091004010469104410048000c4004070040ca020740325195a040c0c069010304000101d201c80d1101140310b0780c064144480d03422101420040c0a80d5040001c200508150388204070401000100d401079 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 460517904 1250 460516654 460516657
    0x111180a0302090a090c050f0f01050702040e0303040305070318061403040c03150e1b030309190305030310080613080d0c0315091b020d02070303120e0d0503060a08030403020d0f08 79
    0x7903800034203841c041d1030000901406843c40b480c089906411501e000503007070802d504144a4580000d26000400f00980d0044030183c10144050f40e2044d03d400b46804500c1050000314040ca020350340d0f80c6e81d00c0d0314604002c0c0a008032400394460342858010200a9568408031002050480e070100d16520348950038111402e00041d00054243c000c840b081f804400350f01d901c81c0034040c1d0800203803183e4a40d00c6041e0820305240c1d410345a0103400401c58080149050304200301041480400803007482d0302da454603451a001200c0d0301c0a1140c0c1b680302889284000c0080541c00348418005400c0320350642d40f50012400b902125203404c5407503010180510f8005d400c0070310400007900c1c4440820355201c003a0800b604000c1c2800b0600105c041c2c2001d0801c3c80843c1d0807844e81d00f260010070001d403840e074081760000001402d12078030540d501d03404000d0502c14000d58060950305e49e9100d440c2d003484420080d46d00c00d1a44160a180c3c8100010401a186c00c204d035000c07030b03400460b01c0b00347d02024100b6030600e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 460519154 1250 460517904 460517909
    0xf040311070b132306030702070e090c040b0d0f060b01051e04060f090b1617130608060a061b0c05090c1c020304151d2b020111180a 58
    0x11401401c2022a5160800d8042c00c00d4030581400792100b0b81d51101981d04880390600a05001c400c1aa500c40160400307500440d0003903c94811103141903030750f21980300280015103543e0540c0e04510752840062030310b4081d042e8565012110360000386510380e240300c100f0b0782d0709800400781a120a00c001140c0c0c000ca041e40d14a1811145ca0b078940714000010b00c0315030784280034090118210045000100c2d00c50b00f020000e59452a4985180040e1f6142180440d240400d00301d46a00b40030440381c482030b08605c050030248020b081411045801d000c1d001d8024070000309414011142d10508100721a070006271203101190700c04441e034822006081c1212884d0385074000c40d4024010a040c00a11003880005141a41740b0f100e5400341e065a03062800180d00c0252406007114034241c03c040701d4500141d010858200c01201c020700400544807074a410180354a1007602580d4140071508610510701c080c50040802c544020040c210404125019078012450120403d203000c0d0026842600e403e90060301 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 460520404 1250 460519154 460519187
    0x1113020c121213230f01111908041523071107030f05031b0d02060c09060f0d0603020a0902091903020d2a0b19020106030201050f070f0b040807021807080f0403 70
    0xc0c4c5010350a040e9a150030300c101101c415880d01a104190800c0303541034804011403003202c03a450a250392422902d030200a0025910b12407950303100c81c1c0204042c42032244243d0b40075008482441c03054001280307250001c044e0418000c1540c00c00b014403001180030b00540307500010707000d00a00b50303062603841c5006043d501c1c2003504120210300301e841c2d0002504907007040c26a007110619600d40d243e0f50072a0040b0391354550003543c18404440b003440100c0190403212090132000444959075000034180c054583d000040c0b00d41d0004514519003000182030b04250b41c0e0340c2d444e200b050f00d036501240d0001e14504024004010f2403500b20039200442811125640840620003021503c401980046034041850f048442004030b044860845c01800754a003120b40584074035050003444042c85600e54400c00d011a280e4000024540009126004103400b4a014520844c0c03560310314410300203403114007160200c1c0c06101008210486030302400035503003d02ca00c400b0181039280e070b10701640c0031134000e4041d45 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 460521654 1250 460520404 460520453
    0xa0b220501050f04051b0901032019050411030118050601020a0b010f060e030f060118092001080603150112060603120f12060812071113020c121213 65
    0x11221804220240a103002e0410341b015045c071b440010303043c651101180c80d0404004001040440c0544103050307039200340d030840f01c07400c4a054400034107441c00c0310b4480c540031182088280410b0400e407081207500e406881c030051840d41416082d0f41481f120032070082c801a1101c00184050340300f0700060340c10b60b03440859074200c0d50716400c0c06540122507005030300004551705951100e500d0009010b034240c5101c100038007981c4c0d0810f800c081900c0840001b0320103154a0303110700e1001480c201020034042c80d214403500c0fa00c42c49000018541c00025288910a0340010581c0d101075803644040340c111070392000d0600088200d4a03020f40039041d00d44c40945042c003000702c201401504aa880070b01d00c00d0581e120f24840c0c00105801d0308907091401601380680c4090551441d2450b80001132405502448089200c80c03d180001190502e10314540e50303207180c000c1102c41082e402000460405081004a01c1c00c18030704c941e90b400c440740014802c285481d8005008d400b030005000c40c40040d01001447d07a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 460522904 1250 460521654 460521661
    0x261e280c0215152d150d0e0708030c0f010e010c051c0b0604270c1d2b1103010c0e1903050304080a11031c140c0a1505090a0b22050105 59
    0x9413050240c82142d4012940c00c03c3c031042a203400d00c880f048190079414414204080008000010325042c11410382501c110074010405100800141c0424610f52008003110130180d041d050944124910904180c2c0c1402c00310030002d60000c0c2941e801c020b100a01250400350f0280d8000a00f001002c03036034200100050101c4c0c080103503000103050041c00b83d840b1760044203182203002151861031510000800484441e242008030901c4080200c200034404660403550278451107010140c10b01003154142071912090802030079240c0d000c1c00326001c0f0003c000c106410380028000d00c0e0784612262140300000b0f0002d10002d00401044069900103013145d844540300c140306a680c4135005415100007404105000300c40c5000208036014104080146003050410712060303036219018039288448800500c1000745d007640400c14151110302450344d10794821408200c07071084034809480701c025030b08440b0003e004281031410007900f001100030b0740010300c0310441c41440d102200032710080c81e950130041807 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 460524154 1250 460522904 460522939
    0xc040b120105100e03061924030c0b1810050c07301502090112092405060306010515090a030804080d261e280c021515 52
    0x80318103803902078030704081c1020510010b58104c06502c84081d490b5020307400040070720340400641d40f2820558030011840b401005804044500c1b5008060f03840750641104000f40310481a1260081010075003d42c602082d813442c04003004111180d16008114822008141f0352084003100c00861050302500d050b50b84800c09241d0111041d483d00a0b08440c074080402503000000c0d01031002a400f4020003034454041900001a40240640c9070503c2846086040e124105006840c0c43c0f501c84d01e2048000c0d08442c0b5903a030354181c1d0700343c41e400c0145803d0070405541c0340003440f1070555004441c440301c0701c0d10800a025042c86145c0310650070414880c1e000081240910240040e501c4038415514a500c20b00c0c4101c684110f210111310000d407110041c1c1204440100c0c8180d0003000025262f00301100c1544040038207070082c0c070024001400362014806107080d9610030b00d4406503d800601551014800007075031050f9802d8012892180c09002c6106500030248422201c0b0001e403180c007459940c15036 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 460525404 1250 460524154 460524187
    0x121713150203040c2d05040c0c0c24050c150402041b03060503010b01021606050c01060902030c07030306050901080304090213081c12020a050d0b040b0402030a150e0705040e0c040b 79
    0x4541d540000001c00320103080728030480c4202e541c1c140c038210f0350f0f440c0b86c4010000580310184000e81404138004852020501c1070326142c4c00f500d0001c1200260109010720b030012400e039442050304004040c0203510035850080340d0142064002c003542d0920b03071550300006004046150310010828071461882ca80c03e601908144205c6004500802c8041050001a606c6104200d840505484096014040300340604040c1c03420385400800047c0003510344c481d0000f00e030710594580201200200308034040540c50f0007002e01a0009841d4100154500b00b0800d54030f000d40c2c051960b1040c0c000c2184541450700e980020010f00e94202100e03080c0352041c40d04420085506c0078040001c605641d080c0e50040300f0300840d45061025a0b41c14540120042e0040041401d2710303103140e0041e01c50442c040c4954903400174500410f010030300082d819800300c29940804641d0b41c07002c00c440042000300003000303810000790340440da06112829081da03940f1140c5801842541c020f884030200101d03101d25038a40383da0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 460526654 1250 460525404 460525409
    0x10807110316030909050f070804030509090f060f0a150507030c020d0b09070b09060403141c03290d0b060d050303010608041106090f100306030c0b07121713150203040c 74
    0x204c901c604291100442c07000c3c2c1d201204e1100c42c002188012881591140c0480340e800340c000c0c50942e00301001440014102c080a441113243c0c481a001444028034010f00c030f601d1410401c44206140d0b07072800584158210020310104240318001c110b48040c10f00400d02010801d070f0060602c6c2c1ca212641c50078100980d01a1480c0851740702e440008103152202c40e084840da03600c0100420306082c41d65441d4202c0590700084071006003d42e10b41c004228003000c6550b0656071243e00e010402003805040350300060b1503940383b10010050405882495111400041c019580003040d084c2c866442c0300204860f03044007907000b445848000000500c0c1a80492481c3c00340d407041011440343d0350510200810b03802800380c7c4541c000c0c110b540700d06941c5000c0d0a1419240450700340451629501d4640102c01c900c2c0e94401c3c20750b103000190440c10010f101c0d41104126541d801c00955480d200c685000003100700403c98000032102c000d0390000c1c00ba11440c0300e0a4808803510540d0340e45801e1401900500310340c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 460527904 1250 460526654 460526657
    0x503180709090b071112030c040e070e100207060e04022d070201080a050402012c13020c0d020601030f0f080d0507030b36150d0503040807140d0201080711031603 71
    0x2180410b900d681700700540c0d504002200d00400c0e204c82c2000030314013164400f50020756003e43c200300c00110071942100e4a0f21404040d1a02c1c81c41d00a45010720000f040d1480440c1c046411129060104a400480380340b45000c0c00d450043c2c451890681c2880c1c10340b00b41c400c0c0c4c0c40c0750440301e1030064804002c20007000c10900c02e0740c4c0c0754102d0f280e415100c0c05a5800352002404281520040c00e00845640345007002840c03404254944003151070003091001c4258001c1c0118507400161513540c810040000810811701840140000e40c51500c5035100c1c2c40391000c00030007800342c5104140c1480781d4582560300307864481da0100020b041810000d00180b00d0b26200c01d008559000722000940d10040c4a1211400202e0b00442c881c109601d03103980c0340000030143d10043c403541c3d1315401c55444074003500380950320031802140c0c1ca5080800b407600e00b4a4980c04100141c0311244540c400781c8030071001c4010a03030b080c208008251100304058422582c1c21400c68040e220105041d42c520391014040150903009 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 460529154 1250 460527904 460527923
    0x70b03041b0801061805040309051f08010e0105010e061b070e0f070c05061501021c090e1f03060903020c040e0705040e060f040318030b1006140c0d050318070909 71
    0x1148481c0f401c0e6280707481540c0c1221624480c0c124840306a82086500605c03900d001d5652a0302c41001840c25000031005800240395818022055500b00303070a940500300c081c089140360b42c074100009010b071031032404190050741c001c03914403c40803030b01e001c1581c2428044161900a5194034107040c07403c41c01c49075076440c1d513108400b15003003500400c504074031141c002c00605081e540f460884006021995281030444c072a110456a20b9411418004401c1480b56a000c08a503d4102264802e042c060903803940d4a03500d40c40440c0c0940641c0c905821294045408142da00c4c00707040990510507250b0255401c2800c20040901c00c0b00c010400c4002d8410403101009904203100e18541e80c1d00044803a2020041c6250104020078002c62520440300030984201e06011340360f50301c24504400595103a5600600b07a8405d204564008a200144644503c0300c20b0500007668140d80d03851404180700e80600c48000302040d4418000c090003680201c0c0c4030110b030b01180e5640a1076004140c040d0040d0f998210 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 460530404 1250 460529154 460529159
    0x315011203031d0607110f010203090123100302012d0e090a02070c090906020c03070308070f1403040b0603071502060406151a180904050f070b0f0a11070b03041b 71
    0x4020b80c0030707a031042d40c060083c40c07155204103060390482c900400c035003a54810b00000e0603009001340000e5100c2c90554002003004414541800e00c081020314060375000b24210030020780307440120302d00e01240e8091038814940c42d0343d203103030306090701c001011410711954010700440c08503040b68007003070b01c00c4050315048481c0e0364010350724080b0700400700024080022204200140e0800303030001c03110180101e800515000f049440d030303440c617031102d501140860722200400001c80e4210010100340c0c2810704000c3c2034490f030200610150322005100411106c04180883d02640301040248080d181c0c0305074941c01c074210007a0181d078424084800703d070151304090b041001300218151940c12078101c98010059001216012040d03a00690040c0c50392540e00c1540130a030b07940701884075010340c1c00b0700040c290140180c1a01e50400c83c0b140c100000c848010480081171407130b0070301150b08031400d9141034802d503e104100e1900340511540200b00c1c070f450200512080c00120640240841c0c44034500d602c0320b56 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 460531654 1250 460530404 460530431
    0x204150c03020f01050c0a0302090f04060e09120304110d0627170a09050108070e130506010e041a0d0f05070602010c02190b0f0402120607020304182009031501120303 73
    0x1c208980c1e240021b181400104407040c02034000d8481c0e900024036a80000c060300b40404c04071005030344042070301e105000900070981024095154058001000ca41c0307546841e4650380d080c1d40308207459902510005070352005209036680000c0f0b04205030b11035500d1803400306810300f50340403896800b40d0364100300c038500741b00038180c078000c41d200d001454540c8681c9500d068010b660030200100a0390910244401e076607240e40d503007400d0b0790485865050004080c20480001400043e450b1741680c02285009036505c4000c4155014000c1b081080b6000b0103000c0852411228459041c40b00401a110b0040c02144054040d08031400c40040e0b0b50842e44900c4054410f0908515007860250081c2c141c07001141054458002d016485030020b00381c14465003941c0c240074586142125801c0058101103410300002181c5101c41c52500032158046c0102840e140c100320b0401144250541d6248000507585210789003405203814002c240c030300c216213646e03580a40c049a00f1200c5001c800181c507080c80c003502803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 460532904 1250 460531654 460531661
    0x4020c15180105091518030a0918021204080f0d020c0a060b09012403021c0e0d050903030937050114042103140706020706230a0506040204150c03020f01 67
    0x41130200010044007100803503c1410020150602d074407890310045101004c3c40410050503008029541d03062881c0c0703005440402c0310b10340560090000c0c01000071664601d041480a90400d40140125644803043c5284020f07074412100034100440c0040340b101d0440101290108010b802a48144440c4e031208040081810b824010342965030031003005544440071250b05441419041e00b0f0040c80c22810007070007840d0b40083e0790b4181e101c40d01d428100c21030400c1031050716228031040c184182022000d400294990154844460103980f09091142034800c44101000103403600040030384501909a51078003c513174680c09294089580200e490702c0301203288044800f00c4903507010800b0480c500185107980000c2c0514242c4c10015809081030880c003030100108015442058016920190380c03504109861000a5003c038a09210f1208010004800c1416900408140e40054255a10f10004000303000300c3d0040e1000030022460320b4038160b00301c01040b81180c02a0202e406441040d12001c0c240c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 460534154 1250 460532904 460532911
    0xa0201050d0509150a05091e0c01030519060803030f010e0f01090507020a0503040623040e010510030e011d16060207120312050c131e031104020c15180105 68
    0x11010021080d14a44561099400c143d82c08141d40301c0d00001907903d001d0103c290b500b0341c02c1e240d0324024014036140401135500c00d40d1848030b2040710205e50030140d985540712aa0001e05040d02c4100140c0b00c1c0e0300000d0b40000f5030307681040410120380c40328000c03944e03a0421100144042014000030800b482c1512007144101d292000b0364a02c6d03800c090140c1c010b4000640300c84250701c29581a400003640501c003a0026141caa6500034840f4400c016641c0c03100c6542e1400500c0200c00c003c2401450151a00fa03030543c1c00503260044440c40d038403000c0300140414150007005500c0c10b403590f106030360300403201c8502a412104554000c441d8001c000e0003000240304c0d0001592081408104070030311030000484031402810640c4440c81c9111558065901c100c0f08182c03d40c0001403100021f00300500034501030040c2e0051250440450906100e03038000c280009040038248162070922961281c0442d12040b200c4001d5a8980090407040c1900c031005445540285038014420601008140b0a2911 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 460535404 1250 460534154 460534157
    0x307180801053c04060f180b2811030415021602130b0a03050c100216051e120a030305090d20011d2104080d0f0e03010f0209120a0201 59
    0xe804043c560f2000c01c0040078561652a10482145110510f1900340552249000780804542c001543c85100c2c21038100b5004400038005800c100000300d05003a1405a008000140202031303040c60320700107404e00c0390420340203200c182000b0482001e119000301a41c0128469115900301d81174590480d02680200b03840b480c101c510a403401c0380540f0b0b000c5881c440090340381d8000241840203e0118044c0c83d115042a15141c1c08103034a00c8150a1160200d61034070002d10181040c50601004200c507c0103a1003000d05c20009100b030513100d44590b420708005510000c0000721000b142d110010f45440c01410250007203071411000441140c000700c0c10075040440740d038864800382d250380c00048a80305010281d820641d612400000501013a440e145420801d00c1c00030404061495082030060314004c404a40480e01403000f0090b80c0000202242090300b00d00300b01e155441101e80407a1107800e50504541e1540c201040fa05450300694010312000fa000c1c0c40103107440181d10861583c410404000a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 460536654 1250 460535404 460535431
    0x50d05100302031504170403060e1902060d2012060906010201110715090204150915060e010e032b090f050a0612090501090b0f0f061f1202030718080105 67
    0x2400d41c5003990281707034418480c03c0b00d1003039941400c1508480d0f800503002244d405a03200f0388401d084004100040000c882020081c4541e032080d070114020780109140c3c0c0541640340c0c40f010300700324034112820404025050116885499844c41c0c902480420785000d40503240000100f03116500c10702944401010842c513040c0b44c48400ea455400c00c20711696000c142c141d90b10140340042e9181d016001144c41825071000340e4a040c60380c50700490380d1107120340c00900b011190030410190801c0e0a24008002401c1c04031100e1000e60100f03040094051031900c401c031311650340c0c015840c3c00a000e011813000950780c0080c22a21452a03030301c110f0b0385020306a0b01001d140410061684339001920080c00180c01c04204610b071642c400d400d40707108420440d02000001d08001c1d04001c90754500380d12103003100300812241420008980c002288401c00130b000e00c8000318141c03089001d1000303210520f0200300119aa0300d4446401442109140c03a0040d0013040d008002866000500819004007107122504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 460537904 1250 460536654 460536673
    0x12060c0a02071502010204030b0c03060904060b030c090403091e08030426030c01020315090f01140105041a030f0c0301270603060f0f0501090e15040302120703050d0510030203 77
    0x640054004140c940110302c518140400d40c6800c0401407218180560005603d4608515028440f600c004200b810504410300801a80c1c0d51850790960300640c020300f0004a200122780420b04162000c440d081c1c1000c4500b0a01041590001840044515035a02c10003190100c0c850801400380ea886400035a13407081c801800740780d104840d41010a0880800c0940b441c00a00741542140c200c1d111342e10035654040b0801c40c0e8051080c28030300060030201c5044040d484d003000c60008565040c010602009100030103190b459001e00c0445015148030f000480e00c011040c80510500c1d44100c0f000c0b00c2d003138040d0780400c02d440e08540649046e25102c1c0151415180c034441160420541c00414695807500ea02000010a502d0700c90750710102d1f114080490b00d032204d4020f220544d603040c1d000c18400740c07412441180c10b03071010940f800110601c0402640341c8e01c82d424200d1400d0000820100081d60010f0004100368001d40100f8031110390603414881c694480b00c00400481345807101039015040320014 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 460539154 1250 460537904 460537921
    0x6030a050601050c06010312080703140a0533030c06120c0d020409050a0e0d080601020a0f06060e0f0906010518040201050d110a0215061c120e0616020f1206 69
    0x156a01ca41c0c185015810310304501030091414800b80c0c01510021780e0411100d161660044400d40e020b5507030304040c016291103550101150500030212160f25560314049245a03584800b980c00c0c1914089581824200c81c1c1301202a8103907200309a0701c607114800f0b07044124200101560380100c82e913115280c4c00d03035500310501c200d60702010203102070950030040482d84075003510035140601d62b00480001c0c03404405210340d242102e4a03104200f4000c803c020000103a0780002c080c0c9891b54000d00350b085003031052910390041c1180340c00c403400c02131000040110307029162400a115018100c03c0741c0442e40da41e414425070815420030311030b10142403800680503500600080c81c0c91031181d1400176014071040b0012880360000e050900040c1c0080f007000940300482540355420030000c81d89c58000720701085e522480d100c84040000c2c0b101c50400c880c58a400d0013001001c002410140c00710f03079141d0041200c16591510200c040344039115103001c0c0e03000c03420402c0301d21070783c001d1b0000182407a480b40341c50f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 460540404 1250 460539154 460539161
    0x209011203120603030c051e06010504020a0314010303030222030503030703020715050916060212091219060f0c030902010f05090d020a081c0212071b05120f010e0c06030a 75
    0x940c107102082d1058105100d442c450500114020f80d56162101d180d40342040c00c15044c04100c40042901c11803041e14050003042a81c112281100d0060340c56419101c01c1d800b9010300c10003480300341c0b000340c0000141a0190014a0a0225050711840710344501c600304c0c656403206d0002500f6640103000213400540a58001d01d05140504042c401d241050305650341917800880c0c0034407840c0c02076503002141c82c0e2480511b001401513400a86186201c0b41e0071200030380105801684100002c00d04d850000100b401641c084c00d2890300c0e0102c00800e5810044003821107401c3e0000281e1400c8038014045120b4071800c210258140c2d0394440600a082d41221a6005441d4159010307181100c0c0000503500c080c01d241c010b08081000c1c01006440850282e100040b001c464415134003d00340c6010039034150030488408070b40c00580d410300c0c0d1071152105030b800d403016007080e03400544d00101e1000c0007200144250903001d00700028000c2c0300e07488046130341b6202c0b0380485c50f41003201440030a001208541 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 460541654 1250 460540404 460540439
    0xb010302070609060e0d020f120313050d1d0f0d06241e0f030b04080f16081c060f0306020f0c0d050c060601090e0114030a0606060201230103020901 65
    0x24000d42800d005450741c1c400c44050740000c4070f08990302d903000440e2100a0009180c00038450000d424483d10000086031a100886802c1c0c1c20030100100140c0617154544000401c06d80101c2200d018103005000640108800d00c00144200b410341c103414118507160607446c0030040040c2c02540400b0059442c0c5015001d00e004412614072121050f40d10103403006040703002000100f04000142454040c0340c0c0b46412990809214850b08d6442400803542c101d02940c1c0190f8003098003a030791001808040c5480c000c2c50b0102e28128415030f030b13281c14006283e000c1d02500d6120042c940e01c1e1800b040e41001101c805104540e0b81c0084d2000c1003011401c644c0c040c10401410720b40d00c51030190040d09540c01c0c60400d10341c00e4041503001c102c01076000802c10106038018400c0c28000d003158213120000a414105101e00540c0e1524104406070341d440502c0800301c110f510501c144009a00c81e0340183c0070b05009181001038282007079800e040c503070031030303d100e03040369005001c0d10007503401e1015545000929a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 460542904 1250 460541654 460541657
    0x705070e040c05100e0d11030319110a050304030b04050709050705070303140601210b190810050421020a0c03060501181a0402030c0f040806060f01051309272a03080405040b01 77
    0x1c0d801800240c0302071004ac402c0d59044440341500d07204504028151841030700d9206c50356482081800c0001c0e000000701c4060740d400070005680c42e6101d00e03104d0315100d025003011a03001d0400d42030190b07040e000000703410150301c2500e06001c403100d002031130703048200201c80b82d500044078200c200d190903a40c43c2a6011110001102082150072000030549500d620404070440c181d0407802000004800d02039042c5884007100c042c89a030805071175030003000074880c110a8003110600e20748103105008008201e0310381c0d130085031405169906d0800d00001d1009103d003071001c44c00c950b0400c11505c0f4500c602d01410219050600c0c0c48040002880000e4100426800c0c603100c2c1000b03032480315800b000c06000103000304401010b05140580601c0032041300317a203015040c01002c1c00300f2101d03038001c440040d0640d8605400064610b0a425415000f0840c02190602d080c85170103201040c00381d0304040220040c41540e01c5081c1c0459484032160402203480045c0c41c600e03080c40b045c801440c0239005601c500805 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 460544154 1250 460542904 460542923
    0x6010306090228020d0e09061c050d02060105190b0f0c060a0905070e0105010512070219050a0b06010806010f0302090a170a060c11071a0705070e040c05100e0d 70
    0x3903040325070880e030008901100c152990104110602d10380c9000b54410b84441c4007800380ca07501801e001c0d0415400c120441d12496a0000152040e1150340400c600d80040c0c0042001898450070480d40346c071660b004807001401041d00201c1c0700d007404030340c3c2d1050000c107001c0010341c1c2e85850a001c40c260841054041c44460801c1420083c600410016004918150000410118034035226240184a6100d005034410240040100b83c1e000001e880d40c6a010b0505e4100c40e50790101c0480c20010131603072800d0801100c08804040c8040007800b80100d91203040202030b41c1d19810700541c0c010320304903256400030b0080034006900f5403107500600251540504a0351001d030720f030010f194071001c1105031a4400d5228801c2c11041c06224081c0198074036180c2480e0f40c1c8074030455102a21b81da40d170f00401c48654030200c0c182c1c0c410713400c0904441940b42c010341901c0d48240c0358104113038000000e8400b6a4592000400480c6502d412220307041013140c40e450341ca200702c0524042c0704052003820401d5540d07664 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 460545404 1250 460544154 460544159
    0xd02010804140607080106090e0105010815030f030a050903010b12600118090f0b040605090d020d051801020a06060e01050a0906120807080c1006030b0a09030804080306010306 77
    0x6040120600484e40340d00e400c190766040c01c0008003803c001d54032111503005880010089641c101c24241c1d0410201e0804103900d800c4100406d25000380313140401403e2200280441c0c1c007a60017409801c1070a4114024410080341c1010030610030f021034189017480c0c1080841e083c002c2c00e1105a02d402d8003081007054240200ca00d601102102c1c024005003003604446440034417001140880450700340000034101503541090342043e048144c1c0640c0d104146c6e44c03000034405000c861001c45000c150301c418110501e150926200c005090255400811031080314803004040c1c2c0041f0b1036080ca0001d5a58141c2043c1c01e01240540c02084054014154092808902d010800d14020000070308844030f04800c1e6945083c0070301000607101c2e4801300c1000d1030100144040c55007840f411201e00d40060481d51502d000741011521403180c1c412500c4148640303c1124000343c05c41d0071440c21680140e81d81d085582c0c603007403160300744d909024000b00091044000240082c0c0c2d0100030395001107040c0f600040058 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 460546654 1250 460545404 460545443
    0xd0f060c030c0e030a0b060108070e0d051b01090b19090803070f02090c040b040e0a0621060c03180b1b0714060c0703140a0e100302030619050d02010804 67
    0x8410503200000603441d41c0ca48005550450b881010b9503005a00620900000c0e44500b410000050240760400c40004041030f0254490003c0d40491440184080342c50000e51500b16542c058041c000c00022609918205c090744c0165061004c46050102c89407500005440e260f03003003000c1c40c00850501804090104200c101040075245a80c807800619440581c9801004001000103140040846007000140481c0d0003034001e44045600100c1581415184e1084540c05045a0f400041b014140d014000340752405020b5007240b501c0c01003008001d60403510604409441c4007404114003169407010000c005555880d11540c400004102c810386031034844003484455000040544982d14410340c20348042c030003444510f8001401c121554540102545e01a01c898000c071210381088a011840c00a120f019018510006100a180c0c0c006050120000350094105031200360040e0000007000944c01b000d121024207a82d001440c1030b40300e481c17540c011039035584014011641c0c070300200060740c0d402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 460547904 1250 460546654 460546661
    0x5010f0504060e1b060a0521040516080304050117040201020705130c0806090601081b0f072a030b0a110c0102070b0103140c240c101505040506030304050d0f06 70
    0x240c1c499100070804450b528840c61030501c5143c0740c0200341a00a100d9402c039a01c00088400701017150030400d032134a440703a29000c2124030072304400360079903011b80400c420420081000e00c01018080307480401103032240b02203035407400341d4004d01c1e01040a000c2500c5035800d40c1c203039950740144140704581642d511940070644110714095554076050301d90640082c0e0a811041555015800b5a5818400d1401e800024001071028000c2c01a446001c52511142030b4000129950004030f1030384142d5a071010f14042c003004240c59200380c140c070003103c011a5282555120181280d4204440350f07001d031980f81c0401e00410000005035451002008a801400310078005402c00c1c0f07014100100e210b61440c00c00c580c1c480784204c02c00708180c01c20198600305981c2c0301210840701c0440c14074502030062580c15040d0503c220006215140300c0c05503200c0000d06c0c41c1d0016119a403400080144a5903184244010b80d08241c80b41e9503d034009000510603800c207200c10a080d2400781c510010001825103484049 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 460549154 1250 460547904 460547911
    0x2100e1e010e120a170402180405030c031210352409010c080108030f07080d290618060706061d061e010f080604060801060b04081b03060c0705010f05 66
    0x20030300040f51051900f60070180c0d1181700c8181044030507081c506680061000c139100131480403424000c0c0040f07010f00c5010801c1e00c04d074006d05404c0780e036207011014a0201141040380d05011000c01e1040104e0703e082d0502005101c036024022a0322070f406c021210204010428a000095120342c821001c0101115008554407050b101c42416480c00e00c0d85509080d034408100c0c51040c4074010380100b1030703054000100c07003401c4402404180c40761300d40c1c6020440c900c01c1400441c441030a044007035105248898480c1211200e002d12502030047e141300b44125806000002e954080c1130325003144c4181490001000d0710ba204050004045894017110003945650600519000203407100300401d0303040c103000b40d003e41d211460380da207031482036031000a00001c0f500581c5000c02c40b8640220300342d40c0311504040c024294140090003d00c1e110441034032640c105201d01c010512540740d04090080145054028481002c1d01402050792422a80003666109400881d415942d0b82002e0420701c0b818030440d0f00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 460550404 1250 460549154 460549183
    0x90e0a2d08040914091b04060315020309100b030318030a0204020a0918021204030f090e190b090105150c150708010503010c18050f0a030807030c0302100e1e010e 71
    0xc8440c00c0c80f103c00700b211810805262180280c0092010b0414005100041e1031012046020402d9498020401400c0c890303000800701d480c0800744020048041d0061407144c55501c0403a02402c035035408a1040c1e8000141d0f1682540040107048092014201c0f001c138030a00203001c0351000bc1c81c80d03021600b280e2241355400c00117240000305000314074003904040342c48250200258100f100101c118041028094070042c01d00c0741120b840c0c000d460141525000404c40800c00400e14a4401c048802006072102000703040c03864000b00c0200e45c40c2c441c025a0584030090a44c003c19080300200d000c2c1940100c140083c42d00c541e105904010100c2480303036103c0c180310355500e150782d45050241425a51a0300800084c0326225000041208490140300100c0e0011106c072061090760a0100d0b0100e0044c0c0c001400c1203d00080b0942403540144079802c4840c40390382214400380c841c010040403180140e507010f016800801c0400c1044440903041c44040b04527900005090f4241e458842c90000d05000c070b0035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 460551654 1250 460550404 460550407
    0x30a0f050c1e06040b0307030b0d29010305060c03130b0901140117060610031e0504020a0e070e04020d0204080a0309030c060509030c06070314040e06030106090e0a2d08 74
    0x21060704190b0b011402204031005050300c03620103034001070b000340250b000d1a90540400301c0040c0d01c07503119402a01c1c800502030024641c40c0c02c03e0900300b144040600700003080300e4080e00f0044440741050400d034102d030780090191283e520343e161b03100200c1d40f0141113440400f0144542d035000c61a5141100d005030584000080d500106031036000701800c059010050401c01403428444800d000700d0055400041100c0341504251310700800c2d0004c0401c00d0742c251841902c025405002d412662116019a0003261f0000802c0d86c0d40b10388141d1541d00b226158002500d58221410606064003c5c01c0b900e500d0506c00b6080a4030b4810091414280c180d054000401186041003449208a0208058070707852400ca46801c0017000440e41d5400c040d0400340c0107503c00501d100c10b1612071924034000c601c0c8a0003050b51030740d0b00e0440100d2210300f56400d510030752815074002a600d080f4840c03440c04000600140410404070384611004c84620162480141540c1042200019110195500151240000c503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 460552904 1250 460551654 460551673
    0x604061d06010912020f010f050408070306050a051602120313150903140a1b15020a050310050105180607020f13020c060a0b01020a020928020702011b020915030a0f05 73
    0x14846800c50740b008120400d0310340000b025845406c1140303043c05080c01c0682c0303203860404044a051003a0f03031012429015000f404420441c0c150803890045004072001d00150725150603001200d9000086007025070f0104601609244c0f5003400341d540f05a054007112401201525059a103826002100c8522583e820307880041540000840e40400035420303010b41400200714020700311451658071074100c00d250381c00c40c008001c100b02c1e2405100b40040d10540d182e0b1800c43e00644540c1040d5206500030441540101c0c2951248050702c00c4580a8581c0c01c072004d10722024413086501c500d1060741c200021011041c09a16000c000390340788503911500590765500310801c0b44c188000506841c12181c1401012450360780d00103040003c01d6011104c028994444600c04904e04501806074042c03c4e543d1200106410f0040d07025001880c000c1c1c031543c0413101c0c000e0210f4049040040c0c002d6101002e10082841c1e0400f001b0030340e1310204081e089915180150721910590b5004540440c3c080d8461000e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 460554154 1250 460552904 460552907
    0x1914040306020f0405040c0e1e0f0d061d0a03090506160b01150e060412020f01050705010c05040314061006030e071a07050d08011505030402011b2118030b0604061d0601 74
    0x6121742d00c812440c101d0308d0391801c400010107003040b600c007102400345500d00d4400700b5583c1e55011001d40d80020118030382e801c102d2030214003400708802c000021001500c03141021000216000d000b02e03515944100e10b841c104002c115560308070030500751071160546011400101080c480c1d50192400202c980034140243d40700070724000e038130306085010303031000d001c03c015049108031810781c0c1d140e044403659862006c11004a03598001c140c000b5217a582001062160560800c00500a40e4041e215190402d014512640da40d0340003590586090017440e40c08000f80c9100740d00c507002042041c4241c9904995403078005110810300041c101d0210f10000d40d40781006010800d2180d461554202400c1c8c96141c10b500b5028044211690010b03c480080001c046a101c3d00b941d08104011000344102000b0a00340380840384017807080805803c64000000c88080c1c02200700d100744507090307484504124115a60245841070182000360400d448c1c90f0042000d4000d501d10215203070711850700d9115840c02400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 460555404 1250 460554154 460554161
    0x603090f061d16060207140d120c1208070c1103030f0a0518090606120c070b011805010f080304330c03030b0f011220031611031914040306020f040504 66
    0x1000881c1601c0c1c80800c00060b600070806404035001047c01010301020000403562000b240345e4003c0862910660b8031038181e4003d040311042c03074001c42264022078a210340c181c448000503500032001c5807000d008480042c108407007607400c00902600b900d0401d4500c041c1d410850b00841c003010040354000c64511540041c0042012038032078111500d65441c05c1101c0800c944e84100203c0400c0d01000c0c0340028a60203401045030040741d8000e624400942c0d4800c9a0041041400d400010031030800000041c411414141c100558074268051450a0710307102004800990144022040090b6800760b03001c6440d04c454100001d4070b681d202e6024651452070010211298861030764824020b00d812a0500d90b0310555060f1781015007200050304000c0d111004c44d03000746646141004050000c200121200e003621903183c5a801a140c8440580003071510a450f40100504040d000c0c2c24090b5001c601e900c1683c041030789544094415103010348a0715003030240c0c2d2120b820307070464210001e810009400c0074031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 460556654 1250 460555404 460555423
    0x14011e030e0f0a0b070507050c09010303050a0e0d151d06010b03060901060216050d03050d0c0504330c020a120b1803070c0e190509060a0b060307090603090f061d 71
    0x20300241403c5648100f84418081c1c1803000b0004003240f000c0030404100614051100000c00f04081c540e501d241c01071040e80b001c4008000524110004030003420300003021010340c1d40c0074030008107001d40d540402c0010107411045042801c2d25614503c500c00c0b06000c03541c0039081ea050f2080d030f40d1600310140b000034001030384980c08640c0080d603201f901c01c00c98041c20702598404c80fa00c1070032201600f4201c2e840e001d07004d00c4404041c0313480140c00d445130304100208104c03070240791b070710f40925124640744203202c0f000411848542c18101d075080650f8448c100d2100c2c080c0c8010000b5a41c03d4a03240340c2054060900000c55660014100307101c100e01c103400c2072181c038070ba40c4002146084039681d10380844005da031081102c04055038010032064a00000c5001c141c2002901c100881c3c600744490303a640300d1003603515480543c0b230109002d0301c1e4100481101d00c03914507510740100c0b580c5403150880090034018410f888826007065600c0026426001d6040041d41504000302803000359000e603402c261401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 460557904 1250 460556654 460556683
    0xd0608011503030f140d0c02070303020d050903031204020d0507080d2d030f0b13060905010e010b04120302190f050c091003060e0705031c0f05040e0114011e030e 71
    0x81002c20010f0752020007040c021a0034601084544052070f840441e038000d5000e00000d060034001e90341c2186600241041c100c80c001e81c02c4443d00061014140d403d8406d44400c5501038100300321408515060000300ea4000e8805014640003407443c0d242c99003040f800390400c0c0c256400c01d1400d6001581d0006c1b14a03003980c16003072140e50140148400311048038072281a07205041d00c940c022865010141e008500344031380034000140d484100c0720000000e150700d016140003149800d0000c19404052400503068650002c4240c7c90642001813000c54881c0703a034402ca08510400901c81a050304602050820504c14070303030708200348054a0400d0414098564150041144904010b02c50b102000510122504542c00150080c20b045840d42011041d8100682500c01c800d9940280442d039403681c18070103903d41e282012142c1c0004122028462fa20413280305c000081d0060054000040a41914120505110080c0c4401611022080840d00703003050100707035a81c1d0809145541032100c034a000801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 460559154 1250 460557904 460557941
    0x40f151202030f01180f060f031401020a02070614040b0f2106061614030f0301031e020f010e01050702130608070806040503181201140a0f020c10050604110d060801 72
    0x151507190440c441407240142084658944000405c0c403030703100e90360300400400140146030326201e910441d1211440103c503e410481c07903140041c5010700c00c1e00c411443c66406840174a00d80380c0700b00c1c0d41c0c4601180301000350ad0100310003d50385003e10014840048104410740c0c617010820051b103483c0001034070342c002400440041000c0b0759941403c45840c0041c5801c642e1800c0c5003410f00d00214115600310440d03603c40001d01824850615000d54105d0348903e1405030744061401076005420f00950b4000d42094001d92101c209600408040d11100700c1803608a051440e1500090030000c4921840c0c00215078450007480070400c103204c1e00000e00006d000801d07090800740e50382c80d40e80c0f2414001520004544650020540d902e0000a100c1c1d5081c60003801017031246528036001c0396066031111403191515070b03103a030b130031802d4003e5500111404014051003000905250080d210040505d9409951f030700f0316110141d0703058090a120f10020780002030407418420316901715041a8038843ca0100c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 460560404 1250 460559154 460559161
    0x1f0b0423180406020f040b18040501121101120b031c03063303140c040609060924032003060405060604051f020102090a080a050601090218060906040f15120203 70
    0xc480407039540180d800000180c1e105100000090240129081103441b05800a1640412603408805541c0791404a400304107607640e500b00d081c03001c0d00c0c04c2c500410320b54200403d10342660240100d4500c9410070200811f02c2904200000d0908528a002c0c003000071400d4404082580e1500c0340002030004800c1d0440b41c070030b280780d0b00181d00e200d410340c540c0c000110841d040c68061107500039440d00d0601902448290524012031501e81e0020300440d0300180c03251900144151045440c1c10850b50780100700b15030410901d0381e8603091403180c1000ea05050b2248040c20900001c5d010416100314003404154480c2481020081940d00c09001940b0501c014041440603a03146107c11450305440200e091482c040c0c50f005901900840549a50005070000300141180e00814103100b071030f02c60000d40c0c0f1f2680c0c0b1501c4400807070003814040984011104c4402c02242080c1b4001e11300018000d01e038609203580c03405180c1c461a00758015807030b42580700784c01e55403413904845568051280100d0a500398a03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 460561654 1250 460560404 460560439
    0x6020c0d020d020d02060f0d0b03010c050a0807020c0907020f16030218040302121305040f15090b0d0c09060e07020d080a18051002030912121f0b0423 66
    0x440312080a84242881c0030b42004540d104804603c08a0f405003c003a102d80750802c00100d181c214400302d009042c100845494640703010b00c1347c0401e079a01601e40d0740c01e1503400e80d01140c174080c0c0100b12405520a180c1240341660b035030541c55204440d01d40c020300c4900b0b46940302034202503032042e2811070700102076014801a0b032000b414039100d03504810200640d6807641401c034075110402018181c040303030025100070310700d410510b0601900d0090303030305216600404e5200412aa00d81c00314109a80d0100b005101900c41c42c1c00c642081e600c010100001f40066071a440800711003980426080d954461040003807200d220342d00395105083d400501500780b03001c5030140101030010311240501c3e9540701059045243d600500300c130b4941010813107104140b1100708100075802600c46600794840c1e041142501003040d4203d41840030792070b0300003400b42c55044904400b1240351142c0012260591404103000c00700b0009480188002c4005840514031358444151301c240f460304003070052120282000126 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 460562904 1250 460561654 460561669
    0x7240219030f021615030c020c1302130e0a0510050109060f050d062408100f0e0601050f0c01091a150f0f03010218270c131502031306020c 61
    0x40c0e0981000c1880310002d0b40220708040603d51000c41c2075940e808045459402d0300f0b54841007912a031020071002000300001d031303a5100e030810410303403003503600c01c1c042e2844020760090280800c00003000c241c5203450b8003000e8a1030908603018000d0300e65400030001000e425074000c1c401042c0a080c0310740801c1c1482001440f001507035400c0380a106002400754031041c4940c1c0b01c1d030004c1403039420400c41d41c0118510701e480b229150442c03a0000c1e0f200c0d004a10442004241d104c122000c40d0990b03070300c861520340352144440000b4805410b100c6c040c009111503030200d41c018005c01c081070000068960503850040c4036900003407003040c0c552901008202c440183c00302c6a1140f07200c101d49016018400d900043c02c1d48000810b150780550000c191000206800300070701c0350007481200c515464036030f9600e5015402d0805121403002d0403040e004251140b014500900703415075074100180c01c681e2034401d20803005040d80d40003001641f00080a40b01e000c850304521000e80310b00c0c409000c04c0398490f07000a028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 460564154 1250 460562904 460562953
    0x20f071101081b0a1b060c03060806060105070f0c0e04140f12030f0402130606030f11070f0f06020c0d0801060e0d02030c0609041b022401180506030c03072402 70
    0x600f100014403d6516015821607030b0394a00c2c20301841740c43c04071032034440090705010307001c040401d041010100c0d043d41c010801d64880c15042e5165410895030352903150003180c8428050311003500c00d0b000424107100350046584102c0c00380c6c3c8580c2c401410215850f19140c000d1810008030f401210150041010310742c01c60b134014400380140390b082e8503103000188819010805c1d0040d00341c030b040c10005074590560007540b02410480b8080040b55030074110b42109214a28004181180380d00d000c03000141840f0700d600545018030001800d0400e004851840c0c001500ea01c40c010603c010010050749521144840e031818003900d12000d0903000350701083d0f8414404224030b124030303804220000942c0301c550191a001d000f104160300c0d04c020340d0001a4507110090304480259028880506a1560742d0303500d1412224102120001c1e16154241c1c0002408042c00d8998075004201c4119580c0e41c08201550150480140c02c1c07062416a29015448510030b00c18a0103541150f205482d403140c0d1200400407 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 460565404 1250 460564154 460564201
    0x2070b090109171e010e07121502031902070309050a05041a040c030e0a0c05100203030f13060e1c081006050301030f0f0b09060901110c0319020709020f07110108 71
    0x2402c2c0228000f0301d00707280e080d41120b61184010501d10b521240d0540006601c10604410703114600e0f00c41f02c480072800650706014020013080ba0498107046010b038021070788a82c01d500805900360003555038805036480903d06600040c80d60b80700380501d01e00123031600000c1500300d904120585c06904085000512180b505200e0340d03540301c81c1c0d140300d030080c0c000703410340e45904007030b0354a4240718a0030f841a803c42c0e0088174007031400139244604050000040700d01602c80710f40104802d942d40c5801da500000d082c0720072a190741e1156080d00140303c00300802c1c121070030310710088110170080c0d0340f0040012000802c4903100ca2000d48080000b107070840100da064a4000c0480141d0b940542482559105407440c01011480075008020342c421011400320301814616009008048040800884900541007480020b4000b080507840345101200c24052000d070710b0056030f002940c0c038031301031080341c00c0030f0011510254006001c4007004001c0c1c4120142000c24203089189081901d5041e0b09002e01191a45 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 460566654 1250 460565404 460565429
    0x415022713020d02040807060804051506060d05040b150109150507060204030c03030804111905060a020a050706090303020f010603080304031209050601170c090402130f06170c0102070b090109 84
    0x180303503118820100c00d0300120300c80c2990f5802c1c0003198603000354480d05c0355810701c0c0611003011403058410042c2230f0146400a00910344030903d841001500c0c074000e006254030400c100320107081e2110038090107100b81c0c0561214103052a06a40810400f60880340142c100300308104140070b000b071070031507001160001e407030706a880c1d4010385800d00c0248515000900141c0d602d0400104250740300f401948520f12854001080214180502101813060815550341402090040c001400c11030042c21100d18248101e8140490a442d6503081984079080f240004800390400d00c141368040190400448856000300102071842c0c030f921a00b40401f502c010100040110210b0000d041c54010b220301e540c004050f2030082d41c0d2001e210220b02003001c0751152034040d05142604528024880610840d0090300b03062140446800003001480d00c0d070800d0400542d107503030104480180c03541c0040100b5040005021050000c0006450800c541d80003035424041005401400c3c1d0f8804c001c0d1048076441c0c14600d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 460567904 1250 460566654 460566727
    0x1e03170423070909050f1006050907050f0d061712131a1908010e0a09050d03050a0204030f0804050a1a0901120e030304030815010207031e03020c0a0608041502 70
    0xd030404889a01c200803013410315122206000b8003080509080404500b1200b4041c1c3d80140c14040e070b203ea21a0941c409002d00004402c01d018000a1500c0c1080e1035035245440d86543c60b8000322a03654000a001c035600d00001d407400142004165540c0c1c8089031390360f0a101d103461b61a201401c43c4c0c000c03400d503102c10131242000454044240e520b000100c840310941e020702180e005100003000d102d012400b02080001c500d1118447c411081c080d0341220141528202191041d000781501174540031400c1e50070000000494070015505000ba1f00c00c40700e25503540d140008000684034140c0000c882907844100e10f541d0200c40b4001c440d0007003070a080c00e00704021072114403001402001601c868a0100000300410140d0000d90300c0e00c103021002468a2120b403400c01240e984c0814000104000b00c1e0b08124001c01ca0640a9000942c0c801d104480b20300f030800300030400c0d9000a0340039401041200b4184400c200001070108482e8074022011410203084140404803002220303000b81c468000320460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 460569154 1250 460567904 460567973
    0x2070b0121080c100f092a15020c19080601150302040e070e10020c01090611100c021005090a0b0a0c03060902030c0703030509010b0901030813031e031704 68
    0x1054001d41100c0d2003910303249005041621200e10107503400c15241761a41009691101d8030800005c01e82115002410030542ca042d194030000e001c007200e403801c8981030001240212045c140181004c146d014040780c24141040c0056488079410940c4454149030080c04601c90024000341141c01d0710114201012100c4c8054000740703c2d680008405090050410505581000c3c0b071891442e02507401c8800b6400d4264204d80b01d80c0a00420350002d46104410080944500c1314400128009400e80d00c0c840503110040e411107106901110141c0c0004400b030b420788070648502580040000b0180905219a80c1c4070351445034010300000b141943c44508002c00c9109030301c800e001e000700b01c0c42150b49080108810201d0f41091000710001790030140003508031070040c0208002ca03080074010701090790841d134070315107680c0000340501203021340007000201041d840140c103c0c1044002030203904808050400a01c0400801c00300c154a5026509020008408035110b6000d0100004004417040c0740100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 460570404 1250 460569154 460569209
    0xc0d050c010c06020904020a03050114040c1e0e03010e0a1406090709020c0c030f0705041d030a050f0d090308011a0a02060a050601110726120715090209090610060302070b01 76
    0x104e171900705102007411030213076405074840703416100c0342e52900652400c0c0b40c0800003902c0380c100c01d10000403104000b2001c0200810701e001d0412005090001d02017880780042401c580d24030381000c00f590300103060724051142c2504422981c603c8600602804d113010901d46a48800c03510442001c41c1d8001581c03603140006001510b440500101503a2003c50002d1500da0394803114020207110346e10b00214036000c1149060488184500c001c059401c0019000040d240b0f6042820080145e800411056010200c18403810310b144d0310945505c0c02950509502c0ca000c889485c00c10f801d4400308000c00842550001642580020451400f0031155900e0004032801074a00c1d000c81c3c01440341201c0420110707400713a020150010155030b4902000801028595140c1450501030b0305468100400d202003100007501d10a403001070040411004801d6020a0410808544441d1a40c10400600003a0710500f1400700040040d840e083d400c00070661101d04000d8010b1192110f12410b071001d0000e940414070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 460571654 1250 460570404 460570417
    0x1305010c140d0206180114180a0519030212040e0402090402031c05070b060405060a060804030509270c09130e07051005120105030a0f030f02011e0204080c0d050c010c0602 75
    0x2415980c16a29108001c1d42c1c521058545400c80c1c017042c40300e4110340311305210720b14224007120100ea020303445c0d140100c1400c00c0c0e9070b00c2c01c1040f40545403402000c248200310741074a05201d0102c0024210b00c5040090400302005160f1445034402c0008101c03298103110078070382140c0c044419013a135031520310005e80340994a540c11055840006940361031503030010060483c0074044d80c0048100d0b5144001c00c8110340c0210340d680c1c0d00c007007090020301c01944120a03441c2c0c003a11a05082c5c2c5480c5030040042d0200c01c1844070343c00882107240c4a0342c0320302a525074142c3c1012070101c010b070070300364003100107130700d41202c20f45d0b030145c25564152104d800d820403c1044010311000d00f10b10414a403414008140350b2214100b8011085a64000503ca050014000d203401da00030a04030b500b52403590701180c241142050050840d034981020080301c1c0b0003949081c3c00500440401aa5289001c888508204868401034460409100440d002c03820100e0300c41c4070417000b481c100f14800e0340d07454040d00900611 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 460572904 1250 460571654 460571693
    0x2150612100c0914061306110c0a0f060314060312070521030619030f060b120f010c14030c04090c0c06180c091806051305030304060b01030605061305010c 68
    0x450b07951030072504482514155880000d4140480c052142408a40c1c8149100d4100010719803604100251181c2c1032940a00111003d0722000810000098040348898104e05890a610b42040010303a40501c12011180182c45c11270080b4500103000030b0f29240100100141200000359174401c0020602a041440c03142038808100710100500c04000c0c1d400c102c482d18020540800040030025440c82201d003208d500401c14402ca0080381e45040151101050150700800800100d00c0c5c030a00c1031001041081100000140240307039040f0003846032171400d03c4091081c1c0100f0a010500041904a5096030650303407002c21594030b200c41c21a0450140603016200030302e010500036040324001c24004102d0301800e04001025100c0c40400101c4190300c41d01c00d6090030303c0c03508100254007604159400b800c4282c0ca0201c074030f403544031542140c2c822142100c9032580c0d5140c4125641e01407042101510381641d400d41498100400c140414900b806994144070140c8404810131040030340305200010322 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 460574154 1250 460572904 460572911
    0x1180c1b08091302121602210d0e01020703030b1f09030224070c061e05090409030e0d0501090203010c0f090326120a0b0f06040302060c0319020703050d0215061210 72
    0x121004002200540c0c45c01c135405a1b1280002516100086031005002c1c4103d11124244000640380d16550044038000035440d02c481b4101c03410f51003031001e8015580a510041050b40380e90042180b05042011304821180000c070360f201c507031030784080142c06880d410b0ba10b0740524000391302400f12001640f44074280d49203000845004101000707131040f007100e00301d07181c881703030100000c00403e410398005034036400140b01800090300600d002e80141c00d00034003d040c00000d2084003404a200c13848104c02c140e072240c0d1a40382201c1103003400d00c51101118411f02e0038124603203c80c80001d100038064400a0710030031800c000215001747c05842210044461003000d40d441360303261141d1581d42812102c069030546080d494030310b942408030244101000060015203401e0550742000f049412501d680d5031288018494070391038070440c080c40300f036040807900141000d070f14600d009450512400c0107181150800a072001220b8490715100b504000100c80c03c030150100c180341076203001d09961070a01160305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 460575404 1250 460574154 460574167
    0xd09110909210f09010315090f0608060f15010c060b0d061e0b0a05060d110c0f060c13030f0201020307020907031505011d09040f0b01180c1b08091302 66
    0x1800030b0030000080000c0c8480701000d03060100541c082c040c4000409101e8020801c0140340c0d8401d511041d1550028a941c007845030325018a001121030002480d0107003590385200344840e400030440036030b0180a030350003010103181a1803001c580c0c081d0041114140081c0340c2240f000c1060540142207140001303044100305c0390017400c24001500612041d00d02c004030a81c4c0441d043e5041d400303001503450014010700500d40ca01010722542d50b21528081a406603075407194281e01c4a42c10003050a0011500280781074940700002904000e00070300020f2020108010701400300e40380681307000c2280c0c0c008101c0d440003c01400141d04608c24070b080254040c00c50070403c1007443d0154060050b41c400d011034482e10944450055400000c40c50814403410106044040c940c6420f24041e640b144c40b41d58100a14880c95071030184001c0c0a0f00700c035402c0740030102100c0a07256544503050b1040e03e10310b40109001c40c074072180c04828100303181c090004440003521f1092038030340480f2070380001c0c600c1e03404564170403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 460576654 1250 460575404 460575421
    0x3070e04030810050117041b050a09020904060b0a09230415060f05090d110d02150715180b0c0c07030c170307030206010b130e010e06150f0d091109 65
    0x50b02102c0c2203008016008021540354411082c01000b00c04041403103115469070b44a039003903441e00580c000a082400351012407031b51240412a030060250401c05600c95003141300304002c1e9000c64114100e410414040d80b003070142c0c000c406008a91100c4041e5440b41c0780b401d003112000040320304090b0014107050183d0480e140008640c811211156a10400d801d54013070100c0c3d0500c0380f140140d0340410030070550400724404114040f040c1d60000c0190344d0001c01503020882c0301b890b52007000d40d40400400d40c94181b02d1401b01060b403003100c080080085070120b20701041c00080030680504508030300c800055009865908480c8000304e940d0413070350110b42d02e16012011800c0c1c1c0c0a1079101410103601c8160300003001058680095054014002c113a00b000800b50031604007101e245120101007074006051b50f00c20361218041c01d0001c800300d002e86014030511456040e680304c15000c0c0c60003001002091a094400c1d61400368005402140c0201907042040340f0840c140f04d035540c0544c0b42410b20500c0d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 460577904 1250 460576654 460576667
    0x804060c030506010f030f1d0609071410050702010e0405010f090f05070917071503060e160503060118171c030513080c240106021204050a0504020903070e0403 70
    0x1184181428030540d03aa0840c101d09030340042e240c2e540401e440c400744001181c000e070880b400c604c0c040080025150410b6500721110030004601c215183c02c050b091060768402400040d0282003400d0924150190034001300ea8a0840890450708008000c50504c0441e0b200d10180000804018000c0c4040d503124200e8641a00c468415003140e00e03e09981051010340134001e1a10505054482d000900d1402c090074202d0042040d005465008102002c1340400060314080700401d8107680020320325040104050314260046c1c000584181040070f41000a584801125445102032a1140c2c1d024205185001d407465603402140c40b5a02c1c00d0b48600541600250300d211a09002500c1030b801044004280c0c120b420561301c014030107846104950106080c0002030040300e003114202d400c3c0341102d0340051520212454042c20914a880c01005040d07170400004080c0054008c0c41480d00d8900310010f501c103200c81c441c050250b900030424101643d030903c12a0002c11070100c0110788d42c9098500146603 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 460579154 1250 460577904 460577911
    0x5060d0e2a030a08031803160b010603060b0304050d18050a080a0512040806010909030c0209070806030717150406180602040f0e010b03180322030b0a0509030d02090301090803040308 80
    0x80700701015081014500010180c1e24a41c00607520383c42c40e2210590740c5402c2c0c80149545180e8071080112007d1104101205034085026510304041541003030780060545005a0180b0310303012050091101040e00400c42d4148403100e400e191104608814000069000640c886d641c404030746c40f80002d001c43d000c5001001075208500f0755052107103480e00c42d00540030344d0050300e00d5580300c58010300c45526907510001c0031038003c7c2809e26043e201c41d40010740d00c6900300c84110025843c0800d110581c06c04203e4040509010a4088098420703500e42c0307a656410380348005644072104000c20709104555102402500700a003d41c0600003182c1800b4029520600c0b5000400e200f584000130490000c40d08103043e00e05403041146151100f000c031100d00c074840b10304400c0c140000c11030580d02c030401c000030980c11100b4140000c40c0c00c0c55820050341c4030f500103080c050440d00301810090070080c040205c071181c50300144010307110150701c0b001ca40107141ea401c00528a01c1c0c000f041c0424075402102280c407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 460580404 1250 460579154 460579213
    0x507021c0219060216051903030f12110a1e2304170f07060e09040308060109080115060305131e030c050d0309050f0a110f0d0807210905030705060d0e 66
    0x65513a502c0074018107c104903e82c08180c41c2c140e40500000b442110900c00f80c0c0b00620300f1004040b135583c500d00484200440014001c0c2c4005070074003502e80c02ca124403003100c0070304d0301e511411089035001801d41010140c00509541a00200c10003030340c1000280c81c060140d000300300740405084060035030344034034404010815100d22500018110f2045420b415109070240c0f011341c840c2c42d40e42d42516043e201a0070382c2c0c1402215440440c06c44c400b4803603c0790243c1080001c1c8541031804c9000390841d14080e22081d03459800c42c0107107000c03400b29807000c1c009c441075402e02da184054600f01260400e0300c2000041550140082100e030580e41500920402e90141c41555900c0755480d40140c0c3e5200300d101c000304a0000000d81c030f01d0a25000030700b800b0211025000031861401a5140211640242c108550845d4aa100d049075100c0c42c2041058400d168100b4401d00e030b00b441c00086d41e0308031901c82c032485500d0001d40f00c2c50750351031034201e600114504812146030000101546094006030001d0a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 460581654 1250 460580404 460580443
    0xa0312020706021506010903150e01090b01090609050c0f030601020f030a180e04110919060e04110603100b130503150702060702070e060f1906030e0c010507021c02190602 75
    0xb04c0c00d802121460241d00c2c141c440d10070359441d50b41c035a00380d90308610306c0655040d0744051521010310700307010b40c49180b8840c0d8001d681c40d40c1040070607003c1b1421600044207091a04041091064400d002c840700b16010003007064480c0ea0740e40c0102c0c903000d400b42c50103007640800309086500b241c200226001109010352240440f40d112950040c03030007000c4501a000c0c0f510681016a03d00380320020b140c1210b2144078007141644013038030788010b5480c0c90b4008528281107504000910001a45000c4036080464500d49513040507084a08003107028045d06c010100005403c03503040c11b44038840c03030092602a050380c101556170407404241d15812101000540520400906060b2010401e503040c0da000307441c1000991142d87c18020b003065a8038a42d23800011151780b0782580d13a410000c41e0000d191554003c1030081c04141c40605020940c2c1c06a4180701090040d080186c1d034010070302c000d410640d168000854040e0001640504855801100311b007408a40882c1295000ca140007040100e6202c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 460582904 1250 460581654 460581673
    0x7080301151103030609040507051207140a03120302030a021b031207020c011d0d0605090f010e01060e06090a1b0309020a080703050a0b07050405041a040b040605010516020a031202070602 82
    0x3030b62111101d45950545810400004186107003402070250040d00943c100c0e54080d40b19804191011284402c501c0c00754001001004131015071042e805a5040903160716041615598a4400d01c0800010500c01d168000c000100600710a82c15545130b00c1c0c0720812451081822000319440e40d001c8a025808404100000381809000048012810006955071004003e0300098481800c6a491400d603200135814242800709080d0300680e402011020b02030481002980c05060840e0030170f86104030540d06000f420040044088800c42e4455406d440718080c036550900144000d00c02d080e2145990280f201d0f03031080242c0e140d17000c0240b00e0300c02e60303802d81c106448025465540515100042665110402110010307100241031504400d96082103801e01e81c8817000103080e241c400001940b140c0c41400360f00c84a03d400d000e100e894140984040101c90b007400c3c0000c000b031240403060030000a45030010303011901d44c0d031850001540c000480c0301d1220220800203448200381d1054600501c02e02d0f521 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 460584154 1250 460582904 460582907
    0x712110a08032a0306040f0f0e15090114070e04090b0901060501090f050901060f0207081203040b01150c02060c0c150405092203080a0b030a061e1e18080708030115 72
    0x21895149a0740070540c1140d075170710f0811000d85155083c0c20115a101c01840e464800d69004540b5400b4503500504021010b100c074814030900010400d108580c1800009205404c260602d96000300c402e1408202c418052030201d009400340d0036004108155000401000c56410b42c4041d00340c0c0d109980d01c040c4542d0741e952200e0102082c2c01101c1e40b00c1b1078200100290380c0610400c40c07210b03d090040d1085240c0d1000850300b014040b02c41e600d0300b840008108820444180005d50150061102d400c01603c01c0c2d141c01030012000c0300009010b40400100c000083c078040140003128840207007070055000d2251002c82c0e06030014070805008010140200b9403600c0d1040d612203550b03032440030100d807682d0741c1c0d101121004030140c2042100399980d25096940d46050104040703050150001240d45000704107200314440b0303c101d86010140c0b801040541209132a110000441c4078038001050f03072030581c0110032080e514650700803d01e000008106081104c2d8502841c100e880c03c00c1000105d000c40d400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 460585404 1250 460584154 460584211
    0x11b0b2a0c03030123030604050105040515040308070e0604152a15111c0c020f28050f0105010f060815010c0b190c02010906110f0712110a0803 63
    0x5101c0c1942d001400180030b555016010f04601d102080c104d0314402500c980400d0a00c44161015903160351038808220501408000c1440369241d950100c000034501074900411840d4040c115000b04a07520558080a84e0b441c000c4d503000e44000903000080030414440030302294546040704124404841d60510040c004c0d40c4884007407a0400c002c1038414100303082d007800600050300c645000e984284803090404c00d8150307a000100303484540002d005545400701a1501c0c000401d404480d83c0492002c1c0310315118000842c0b40401d05c1c0e0b1680d082c400081c64070501708108403a480145601e090000641c3d03651140302c00003211071030b8681003180d0302c0e610440d00ca107031100780d18a03002c07507401c010b15130008072494100e40d032003903035580d4443c4505034001104051700c085490743c0300141e442c7e0304c1c91000d0108134484e0025040d659000589003484500141e403540c041c00d100a0316200c503034100500380f540299005003460103110190740400754603252a801c1c5070025184c02d0301610704030003060403407243c01e074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 460586654 1250 460585404 460585417
    0x70e2106090102070b0606070f1a04030e030a020112092105040f08190f03031509020d0c0207080c1002070b030702070303110307020a051003060b13080d0815011b0b2a 73
    0x12002c50646d0384e2041400348590012104580000024059030003041024030301c00700c1c8031180c124024813030070203050080c41d03440c41452492083c7c00c0010b03000b0040c0c0e080086a140c29400381c5002c0303a00059420480c12440320040e4541706010040381040c089540035000b802915590801b8020b029100c504041d611221001c120601c20030f00701508010402c04800c1c5207003507119203004039400d90305000f00c00700c83c24258441e00790a6008203a03410111018054001c401e2a588000c041452420314240d55030300c0e51105586c0107114070326859441c94402d02c1004090522a24156641d041c080b000039a22840d921041d00050801840958404030103c2100c1a01c1e4005041071140350401c1d0070056500c0f281418141031642e100c01c0002d406001c003001e465181005521038800914240300a4181040c413101142002010300401400e451070702d03492054524286000e000c8101602c0c44688407507500b0310b014044040807400c0183c204802c8400c0310b42c001054040d00b880c0400400d900c0d0107401a013 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 460587904 1250 460586654 460586663
    0xc030b0c031e1017010615030c020c0d06060509091006090605010f0311042102190308040b091c050309030c010e031005270601061b0c030209070e210609010207 70
    0x310307854194000001089820424809143c0049a43d4181010040c02042c01003800e69455550410990520460304a03007540700342000e20001ca20000001d4a0716004241c1034462038280c4480070030301080d544144041e01c4050312180942c01c0c40240030780d0319a07902400380d12003802c203000800c90364042d000d142c040316410384906404c40c02c00c200503000760014055800070340806000009003406686410070344440503101c0110007043c5401440407804501c21740a4002100070b008100140618007200c0850b0411140203844000c0c0301e000441d0104ca40c10014006099100f09d0024080d000c0024a00450304a0407580d4600f226801503840c46035096249602d504010b200c11102c07032543d001242d009680085c80f201800000c2001c1d8483c402c000d030741060a9000c68014030880cbd41008600700503900d000407849245006a031140c0c003005450100074000c0f040f032804510f5950080440440d0b50300b0040189003514184d03042c6410b104c10030068850180301c1c03a00031a40f6130b94184212090030741c20 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 460589154 1250 460587904 460587931
    0x1020708030a2007030c0203010e0118020909060601080c28110105070c12030b0102071d100902040b0f090f040905030c121305010f02030c07030602090a0503010b010c0b07110a0c030b0c03 82
    0x4ea460540305850081816600765407144030106003102d003842110000700301c4081e10290440300f40140100104024070311525644000244a00e0360f8101d80e0f215801505c0700b010a66a24032100d684441d41c50004004001402190176001c00f0798105800101402c0c1d088000c01c031a5560850403a4103645029020b0001c142200c621450345210f50010003e04038180101c400680d501d451011400780650400010215030b4401c4c0208160344141000041c0301c40380c808e604003810180034014620929040b04280040062452010f0311031082e0340c0328a0000034810000c250307486c14459180d42c07110614035414004c0c0d1960069041c503940a44c0e060b400d0648280070801e003000d0040d100845012000d4044d48000d001c11071800d41c04010300800307144954005600c540e2000248906804603410451081c4d052494000c010f983c000250010541c11148600d25a2101c030000d45800f481ea150400407405421140f800b030004842c60901100d1041401402c03540c2c4c2e80348100e0301404161100a02c0224 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 460590404 1250 460589154 460589167
    0x17070807080a0b0909010b0f03070803030f0a060902030403270605041509030f050a02180f15040b0d0602130e0c07060b13020c0a03090b0a050919050301020708030a20 73
    0x104010103075200c0b42c10300c000a64410090300050340c034402117951a555039154180b62981c1d003068000100c030101d043d4010b007a000c0c20015020346a0200402c0f08581d000c0080c0001c00402050b00142c0c001d00600c2400c540c1c07410207080090190101b000c0d250440d000300d105440070a40024604021103c15540e00380c00e05040a0090290310060004241041008400400452201c00b000d1514601c118004c0101107000c1c810300407200000f540c8144000ba0300403c218500602d0014213901045030030000e92801c0700361740050001d00081290b0f0340c00c10f00100d084403c006681c0d00030071905208200d41149255904110b0181c83c07012600811894410302501d800500e40390004000c04100410000c4034035480c5038500102d810030b0340703d0754444d44902c10710014180c01416032006454040e04840c03030500204070152844c46146210360082085800300c0383c0041c16030031710801400004009541d10201400c145010f500207072001d80f20b01d4581507590103500d41030040030402d4921011403a0510313a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 460591654 1250 460590404 460590407
    0x1141003020903030918180d200a0c1d100302212e1811010e030307050307110a080c090f0a0b09091f05090604080f0409021917070807 59
    0x10040303005150035201c10300c034410803942c0c2d2801b8440a0100b000d085a11443c0001032a401d4000142d5101c1c4150000e12000b4400d0381d03c19140503094070410700550042c58815507580c500064a00098a9203c0002c0301107640c45150390090104180301d0203510003520380005803800c1000610000354404a101c41041d03c6c2014940e00b00c0140e65180c0559445070401c202603c00c05002d0441030555001c445103010b8007206a00c2047d000c0c00c1509403010400700c50303031340b01080d2902118504d03041c070462a42c10303181ca640800484d500d0310751110680e502c4000d0391900864030501c0f0091140300e80000c11000c501180001480ea96400b401422214a610f0b810100c0041c15409090504c0064135261004456203c804c2218020300400e0010094810214112440303e00091000742034181458107000c0f840e03d0020b40507822903000400a5501e02c0045240d00c05813260741d006101300d50002c0b0b00300c0e03190710042030008000903d0303032110340307004001c003502d0010b440003204e881003c582003070003049825 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 460592904 1250 460591654 460591657
    0xa02090c0f0a0512150f09090304030203160e010602031e030c040803070309080c061305061b0a1a07050a12090c080703151401081b010309061a01080114100302 70
    0xa10010885141c424444400c5866920074a62030011440000d1940c1c03030b070400c82490a03404181e180c02c60320f14444000001d1072070079008032882e1050344040e0205003003040a00448004590080484e5481421149000001c0c0918807a03402c01000340c800010302980088101e130f00c00c90080e1400641c2815440080340d850b00007806074240d1010500c000f00e0240700420003400010300944134600c00d1440c114042e0b281a60704e10080d4024242400100100490f200081c0d05403003003100c580e61902005481401c401c0710540030b00f0302274444c008003a010321000001c00040000710b81031620050b44e50f10800c1d039452007a07045620010780a1580c0b107860540503445000301c544102c510a0400340c0e40e142072403401c0626081902c0c521075101103100031000310700c03444502040e110140380700c03989411503032034072131066107601020030703015202d0f452040c1c4c483d0348508402030340102e08016031110010516131440c3c0005c111408600c110b8004181c810300c0342a0300c510380794020310b400c064141a40c0304401a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 460594154 1250 460592904 460592911
    0x1030503070b0411060f03270a031b08042603120a0527100b0d05060c07080403020415080c031507181a0310060903080a0c050a05120a0216080a0209 65
    0x184070341310311801100e0b511603004000340007138a85890303200d040110100702c80ca4410b01f1904042a030b500901c4840e50008164007100f260142001c0e03030311038004010000d01603804540140344810000e40840e0b0018417412011130b02003040c40301d00c035040e00e0030625070b40ca10450344c2c1740d80c2c3c258040d00054128019600415803060300000c01305091060103c0c2c65660b841c3c081803525890b0080c91204440403214880d034183d45030101c8150003003d03004d488403900d60030b0180040341039100006416043c40035130401c0390300843d40a4420014a00c100e110726810350300034003d10006021f070041465062030005816080d003985244101e0898890023015101103006132008403401c1c880c140c000440e03404140390704540c503400402c10340e524580701c100001c02c000540c00010503c50003007414808602e0020540e0400301d8107090581d42c0008909040d49003050a0701c1c024420b01c03611210360030000c0c4410191071103101356003c0b100540c0440003003041d03030003090040d505903900c203403410005803900d04c0c44c03c1d41 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 460595404 1250 460594154 460594163
    0xa02060c07110d06180308180304030215030612030d0f050c0c060a0506180f041103070806010603110714010b040e120d02090402071407081c0f1101022109011401030503070b04 77
    0x180c9204910344d0b00b022038100801a0081070031f201c00c01481c002c0344801000d40c3c4d5000000f4500d090306650003c0e00035217100c84100708115000c070002c0d2240d2a103501a552030700075801140d44607210a040030f00030b01500c9603c1a00c0608000100b4410f218620546d02d080005001030003003552508804d000501c0010401e070b6000e0a0402000c18840398000001e000700c0c01c500300400d80303241500301407031454030b240c0046020781d106040400507040c012442505440d003524010400e1420700e0041000350007a808050200c10715042c482c6151041580841e01c02d00e402c0e5018011070740003c69260300c0305804502118488003c20000741180d00a50041a0a1100600050030030b0184d8860000c00c00c04440400441c1d8491281485040030802441d0503002c01c981e00000d40c02c0c001c001c0240032600c1e60702d83d001400070007240c1c052514000c0d01602c00c03074001150070b40120954610303190300c420700c02d8031140003a52030301da000007003452488c81a5041c2d94124009610789101c659600c0e110a100500c15117 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 460596654 1250 460595404 460595411
    0x813030f03110d0906110a0203030103120203071205090a081b04020f0c0102070323190e041407020a150b010c0f0f02130e10060609120501060806010b0a02060c07110d06 74
    0x30038060102c0981100c0d5104040050840001c0c60907604940b0810398a611401c01030100d1a0380d19400812241500c2c0d111a4655020034070b00301c01d034958010070790003d080041011203041000c0d4090050b1080c08801ca804510050f0355000030381c0c0b14607084400e010003400f9248103051030b0400ba0002e084030308142c1c412034502a01004110308a070441c4030110b001400c224040b10700103600f941c800c1c0088148002c2d851500c031900310525800150082c0a80900001841c0c840e0580e40725800390a000c003021405d000c4a2412500080d01c5440d8050700b2941409000901c2c501c8410352310401d0450038046c1c4480e000d01041d610f91a074001c500050072102c03084d44541c83d100607221001c00c0400c15880d01c5000c40e016620400342824500d4603441441d1007403902c0340030806503034004806412100c00c42280b045000c16400d003a805007800d500603070054440d4500000d00c0388110341c02052080c15950070354030191640015a0214480e095026061000801ca242c000386031620505078224403606000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 460597904 1250 460596654 460596671
    0x604050d030905030d0905060a0804030215071e090f0506220b0a030b060a02100b0f09040506090d050f1c2c060a060303020a0b090109020a0308190813030f03 69
    0x205880308100c0200c0c001808140708100074103040002146a06150500003200303424500481c1850082c0aa400c0c00c000120f004102814001d004203004078640e40f1440107039292908015045507024500d0201d01c4103ca00850340aa1185c0318510070b80c0c24010010402074136000403c0184c0e0400b0040c401440e4a008403140c180056a40b06ca005011302d0401507107401c01804042c0880301c091311881d010355800c0184100d40c60f40440d841018401c2d010001801e08410004107405030a540f2160383c1008048043c0010701c807001900c0343c49890044101c81c1501401c000c03c80e2280141d0519142543c0c040c0005484000c6004020b041141842800a1000100301c0425040c1c0a182e030302034026650546403413810302d8180049940010403200500c0854510b80e0002e607102000e07500580000040c03c00b1406c131010a420007400c10b5002402001807607101c6c20201c5403079015280e00d154152010f80d90880042c050410144514480d80c0240400c03001d1380c030103560107910142c0c89410190b542c000d0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 460599154 1250 460597904 460597909
    0x92f0a06020c030607050403032f030a0210050606040e07080a11040b03070f08011202040b0a09111b0a0312090501110f0711041109210102030a050f1305030f09060405 73
    0x20000c004990041079074503600c0050600b0241d001c1c02d0801049802c000901c08a80c200c4202c494465058500c0d00040341c640f0840704102e41c084007600024000000d031844017990002d1010307d28504000104466104c460412407180f20303074858502c5072002c00d0f0001b102c031405400e00d180d00c0320365000e010800402041644200d130340240c01501d04100040706200d10315a0012001050080d00e0615a00325410584030100858624600a104588920b1500b06503210004c0140051006082c148849803c0110864507504206040ea22010405072254052007000075446003051b0141c0b200c01c0c41889058161f0042c0810b160b0a850641d21045040006480140240080d899003594191038000b903140c00c85d170214190003d20311990801100d010f890f00d640c070032101101d03011a00104031241f0b6a005810510100480514651011040090313003071042e084141304070248a0a09116610b40041401519105002400e130f035000788049601207080000a180d0308000608007400d140e0349000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 460600404 1250 460599154 460599169
    0xc210f11042903010509060606070311010608011d0118030e041b050c07080102030105060406050a0c0519060f0e06070513050d06090b09061302100309150501061101092f 74
    0x900c01c2582d18040c40c5840104030480201c1c4148104030001d220030f007400c9441170f580b1140034184521a040c0001c0d500304042c0105040c0c1e00041000009000103030340e62621600030942c0c0e002022019030200031491081c132040c454120140302d40441e20500b900b4648045034000017003407600740c2290b07841d401c50200c0703641c0c0c1a18001c84480b96850943d21040842101e051095a500c10082e980c01030006004540c0d402060b60295001441c11544a0a07921b4007180c1d01010303600042c089008a01615080d80d02c14400c03140e09a000d10303400e0240c0a5007090042c21951118400312554010202043c84540320700c0060141c005640220707001a80c80f103001590584210a088035120b80c5c80c81400c0c1006400340c2c40582c4500d03082d01620b00b9240900e581245102100380007441400c05000040346e15010381c1c0441609a00700c888549100c410121903c003c1c40280a5400414001c954040c003040e814018080c8203688512402c4e0f40130f2028250f1504041c0a081c19030486481c0000c0c0355960312400c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 460601654 1250 460600404 460600421
    0x1a090903070b011527150912080a052a0106050f0105030403032a050c150108030a1119031d030d090b030a09060c1e0806210c0301060f030c210f1104 65
    0x14407460500c6d1504001b4800d1005801c40e0400741304817214100020000f06002d02c00c0c0540040314071340e035180748080840f0140f00b882403202d000f241c0c80c07040c0905031420050b5040410310090080244035110f008100c05048800540750000751300700300090000b03103c0c0e0040e0401103042c0c4505070850a0004001000100f204a80c800040c40440c51820702c00d020052000c0c00c69541c100c01035194100a011034891082194140c103004804000c00082001049400011206a00c40801005051034014400e6050402190f8604030403101444185408500c00c04000182c0d21341d426000c0c940820007049400040185500d0343d92a40c020000c0707112401a4900b2094030342e14400c3d607960000c90341c4501d080c001c561104011800080101540300d010002d500910886406500f041162030400c0c030700300c1c0c405906909075080c200d00240d800ca044000d90306692140303201031441e0b41c8071a120384101c01403104421504818040b40c4020811140082c42031601031b00704544801c0758240403500703850750103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 460602904 1250 460601654 460601717
    0x7060e2e171302190506040605030705190809240106030e160608191b0c06150e09010b0603160c02030a061107170306180c0403061a090903070b0115 65
    0x2c2d906001146001d045544c4c810802a610840c19814040410000c0c0603601659041c4880000417480742d90049007540c98090784032281c0300c0e04611640c0300502c0c0e00400d8403040b110788100880340341071000520b41c9a15200d840c946082c0d031a803a0110803005000134404408940c05120701c088042620390241c1405440e10b80c0714032a29061180340a28030784110001c843c00c80746400740c180c008507810400c2c5c0c00404142d2401024140643c100800180040e415a080c955840d081c00510320001e01101d51240000000030404620b4910500150748000c8a0120340007980c01c150b07201c00f80c000d0718521149070000d0207c1c0c90a00c42c99030389204480400c2310714081440c000c10040200047d814103030300b801e40d02c0c5500d2801e60500720041070002d071004041c02030000c51030300020f800314102410b4400658110b40c0c00d104950f402250320f044980304400c1c1c83d00a411020000f408810300000322a205584450042c0c6d05a06c1c1030240b0580020320303a07041082210a80820815219241580c10110b945 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 460604154 1250 460602904 460602931
    0x60a1205010b0c0c1c0201140c0312040c0f0810020c010b030f07090501050103020a081b09130902030106050a18050601020304050621060913030c050a0b0907060e2e17 73
    0x80302a15844d045020f4811403040302c00005050302c0d6640c055800c42005c0d170a003002c1d0082c01c42e246d2698114061035022500910012030740c1c010340c28450740307028051809481c61281036a1181038000302c9140500030a0030369409000704100c4002c05a004018990305000009140511307480040d040c51103d5003088036650040e4001e004511051256900404c0242000c40c0b40c0003105c2c0014201c001c00415a0700480d0064030b004d82107195032802c1780d035140720040fd10540c0720007050301c0c1741c000d050b246003d9020b50719181001c40d00c0d00344845208141d030900300044421100b1440d10001500c00104028111700040c000060652985400703080752113511100c4a520166000b214031605c44000c0c40d052007624080700307004e0350003e00d040c1144010b40503e40588820158101140f900b040000c5c0140072800c12410058046008110328040d1120741c2d50301072400d01050100107a10580c11510040f0601e03481081c20800030b000d1286c01641c016042c80c41081500380c0d1540c3c40c030130782200d918418010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 460605404 1250 460604154 460604167
    0x10b091003060c1e0f140a090e060a060c14070305120d0c0e0f0f150d02091521070c0203120306121f02090d05030406020109031418060a1205010b 64
    0xa03030007640c3d0010003e290039108410340014550008440b080c1e0320081c08090010008068450301402070b01d0001d188006550b0301c1140401410f601301403184015180150000c070310a0320742200720000b02c5515a64501110000391110114041d03080e84200c85c5100b14200080054402c2c00701b1b1a0701e94580c462507031203c80c48c2c10104141c0300300d1802c0004121030110081d003541d944003103100b0146015522002d10442e44004110021380c0d5025419011002041c84003110441c1d4000b042d58034800d460090700e17900714080890850149a0021100d141c200711035000d00b840444010350700c0805860a8403040322940c01083c240760341320707980108000b8004100002821300841c0810241d407c08010503804000c9050401c00c0380701c011410992540025041c08290355244103525201c1e00300040da41d960755900c0f0083e00030700d111201180070402030801241640649000d0355000301242c003590440f161b04804200455000700f070042d081c03144d82d83d41070801c02801d101d071502034218000481d40c1c600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 460606654 1250 460605404 460605413
    0x106051612120509162601050a061514090907030f0f0e0606030f0a080a020120031009051510020319031d0703050304090207020d0b0702010f0b030f120c010b091003 72
    0x5a000b401100304c0e07407100310b910304004442c0d2001c81c01c5840300112000c07154034900c10421000e00000b084440da6003000248040c00403554004401c40342c04205c1484041e0b2802406e0f2800b410280b002d00120700240100526410004201a4440c10034076001030100c1c2546100c00499500c024211200f5680700101e2021038401c000c0700d60056822402081d00b80e000300600e5980d00f032400401001290049403100280707000750041c550020681d1801c120410400c41e480026400407a2071515007250a100041e4074001071007240e00a9101ca03c1004905c10014103101c01c0051204a08003148420000000f0501a00103010214070305982e0114a45482c44040b4000e0050380c5992062078001d1701d002c20018200200302c03401c8600c01c00000d03031540541e0002421121a045c40903101303082031410442ca456041d4400341100c035401008225070004c0d4014165900141c003d9606035500c00403218040900c807a02078103880d11140d00100c0e40c6803048020031040b030001d071032070441c1d440d0b208020b00c20030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 460607904 1250 460606654 460606661
    0x160807050706030204050f040e010b0916022e05060d172706040302120a080d05010e100803030a0b21031b15010e04060f05102903010605161212 63
    0xb00894941941050705000024204c641c500034001d1103a583c440c600b04000c0300a42111010401c0201401d40f03519001c00540300500060031040c5c014040c000100c800002d0b1035694400649044440501d80182101030708018000641001c0d0710401075550140041c20310100c903d00c11865242c8030351500c0e80751b0340840021103145142e4400e44007100080c0100d845440c15501140d4040f50500499181c5442544c1084600700c8050712032180001c28809200064100904a440c0c80054521607943c2d2440342075a155030f40a80c809039001040481c4ca141101d402c10b184e00e40740180a0901207502d41c80651150b42251800343c2035420104004440300750203041c142ca0401d00e18080c021408035180c2011440704140100600c1c600084045424400c0e903134009800c14140f031a0401060502c031120041c80e048034072a0741c501c180118200b10300003a034240380304080c42104d0030290469003080f80c10b54158110345402d2040003c075200c1040410b124004820510710680c0390a446d41c28490305100a6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 460609154 1250 460607904 460607909
    0x121b0309080c0402070b04170d15050a0b070308010b0901090f0305010e1905070b1608070f120c051905030c0a080301060306140904020d021207080c0a0e070504090903051608070507 79
    0x40d44c4140700a0703000c600b0240c059540039070b2001690324441442c901c40202401600d03061034040f803800140c14040c0459034441d0081e55001c4403a21301d080e0ba6240806214425690020001411b00004002801c0c0c858040c2c00241c805051107031010703031200c2c44055041041d500913a110380d101c4d240e004400006120301925281c55414140070840c1c66207910781d4034902d510804408101c00140308072204141d0b0101d41751981d22841e01541c0b941075007428004510070341003c0c2c455100038016480c00e0750203680c2001005611002a180216210b001c040c0000180c0c1d0301079450740010400710350400d00078000101001c5c420006207840b541050310080032103500303421180d202c04640e80f5a80c1136584007041e541c1e0059040380c40304c00f61030045c0301041c1f00d6503425511404078070506201080060011441058281c4103943c104000356031080c01094180c0241d030f142020460402c13090012690503007207260782a0090820910341940300202d440704460001003641c403804003282410400c1000d0141500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 460610404 1250 460609154 460609159
    0x50a14041d16170c06120c0f0c0c130e070302010c0c03020301091b0f050f040c03060f060e0f030304030b041e1e0302010e06040804060e0a0504090807050d1b121b0309080c 75
    0x400610010218840d48146003000c844003400400007140c001641049450010001c410549c07140907410304956521420300b0319510504000300c6c1c41890a40c0c40c4036064840e04140010300b0100d185400544200c51000801e980c034070451000070002d0f071005d00800500f10301c06d081132172010b8440311040c485c038074903500301d40300186000c0340802090b6101c0c0b000342c98510046900203407000c03030840c00703030002c0c0100c0e4840320b0782c8041c10000082c0941c11049803074100005840b00c3c100040300b00b040603101d218500004000440090114011032080101052030b81900e02c001026070010380c440121040c418080f00415088494144d0100755081c083c15503442400317002495a814140d40d140050300803401050100302000e441600b0030b80e1080500801040d001d0010880221541001011507000103c1541c1500c1402c1d000300c030903441114149059803010500c0050307901c9543c0e44555500e001e02415041207281d0003480f04c0c0058110403880068442e13115403210f03d2401c002d450800034540603051 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 460611510 1106 460610404 460610413
    0xc0c09020309070f03020a17030f03010321020105160e030102070804140f060a021b0f18040c09060f210b040b060901050a14041d1617 59
    0x42c0607100003000e42c3d4031281c4403015109044000d2000079080490f4810400c00da080c8440e03081d03044000070040e203140c5002030b035040c203c0e0b400c280c000791040128801c0b00c00314604c18080c034541480715400280300f00e15000b80c0d110b0540744204010301c1401703204c02a4150381ea4003903045a007100e501034115a225629150085a070145441e00035010300c0690a039043c40c3d10b4010242c411240c003a41c003c024800280c00c08040036511080e00c0740d04085581800406980d8905034130072550241c10401c0704520300381c00c0a9880c4401a0b1000707c80e80d1414009020000c00410078030f054074040c5070210003c009920f1152180d10703d110001c2c01c4801c1386001d010403c070714000760500036801103c610106989900c00c02c03000d80b005120b8114600a0b401044205040035008806145c01c0c1000f0090301c14141c1e00361350f08141c5407400c403d02d0001510402c1c031420543d294205044030980b4010f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 460431654 460611510 := by
  have h0 := BRFrame.cov_init 460431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 460431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 460431654 ≤ n) (h2 : n < 460611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
