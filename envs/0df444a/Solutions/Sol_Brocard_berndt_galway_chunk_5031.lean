-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:31:08.4541+00:00
-- url     : https://prove2.me/submissions/9b892c31-6ab2-413e-99b2-832cd174172f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 904676258 ≤ n < 904856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 904677508 1250 904676258 904676261
    0x30d05060d061b0f020a02100c0512040602030d2306090c09030a080c012a120906051302030f01060b030a1a090a15050a0b040e07170c1803030a0c020f180901 69
    0x46000f803a0b48445180c3c1c1c40c000c0480e10342c0381a000084d4010000c10384500414802da502c04071160203a829074540d101042100c4040358000d034010000351b00045802200c0d243d05204484020011507520010f240501c41000300c106002032031a842901540c0109d4105c642250566010140140803113841c02403d0034a00c005030817160345007140b5801c03c035a005134640d41164034020f031030f072040411404a002041c16a00100c09040002c0e1140d07840c620000414024011140600201095140340c02500e00605080160300c071031500300c2c0da0511038100301e03160b400c004407a804907010380002100103441c03182800400c00c5100559005000300c0034001d42010039070008200690031103e80310700326a80d03400d110b81d02c00680b05002c81c0807000c2c0410001c40d1031903a2034a61003981450f00c81028140c80741694003200055442000c44c02c408100c900805015030482209044218003c504010880400514129400e68004d0050034000c003c0c00190300d5604642e101c1100b4050454110b10380b0203640c07030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 904678758 1250 904677508 904677551
    0x1b0f0b0301150302090a06030b03161e0e010312030507050d050a060e010f0302090a0e03091903300309140106140f0901050303030a200c030d051008030d05060d06 71
    0x34001c120b1006001541d00034821140003201c05415102e04d00d180c113070f00303500520a6601d056014040d460900c40c0886071540820040e158040460022100c668240340300e80146811401d0400e07007040051002c11019a41007000d00001c1c41c010680d079460400480b501c1c003820a4004203036007004248840d6401c2504040300761204030300385000320b0f070b80c1d0305001020406c03510003e03400241600106000030308176000103c100d00c416084903e8400c12601003030351030307000150082c1c1c0c03107070211320038410000303048010307026200c0b060281e071040c0c80d011529444500344c28441200340765640c4038a0040281d81d2412600c917090150080144566804030342c101c144841351094031070303116100304800d00e20b0701d180c4a6050392005801035042d03544d01021407000301040601400c0d8440c4425943d5041079184004101e058421005552120030000241e015180c01a0000c408011042c0302840711003000001e503081e12501c18008206512101e0204558550840014081d036007451001d80c0b2590400b15000b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 904680008 1250 904678758 904678769
    0xc050409021c0c140906070215040e1b0423040e01150f0504180b040c090519052401050f0405090c07050607021f050a021c0b01110c0306041b0f0b0301 66
    0x140480840f2482c03c482021103030b04e841d09401428406242a030a051028100061003d449505400074201340b0f0301140d0440c0e445800101b850a0801011108030007406451110819406d41403c2c20614148100161114440c980800f4030418180950340d5400981101140700e00070090001c0070042d00d20500081d020f14540090b940300006540d0070a8800c0c8070030b04109020010100883d40d0b41c2449406000e041a03a110b050307204041a10300c904d101c0c007030169900c11024040758141d82201d82c140c0d10001d210034400000142c107009a408100b0071801184003d00e801a40c1d14a1100076010300e0103250072544e00303c1c41d60020010203400d00c0300200400e502403c200d621a03501c0403002ca0345c840b031500d0310140d00e00f490404203140132000c0d009203800c21042c2501504080340301c0030b01903000c054500e11450040d1214040d0142d944c1010444100c0e0210fa000381000107070401c01319030355440c064401030640c4441500c1d032100360244182360014261001020380d4559035562a040950000e0044 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 904681258 1250 904680008 904680011
    0x803041505010e160c080f0f130605040f171c17010305070905100f120201030b0402130e070e060912011d0a030f0306050d20120604150b0901090c050409021c 69
    0x2100b00c46000c5c00c8500601039210380410300d0102076040703101d82504a96040c29000900b40312100300c2d48901c1c0031100150030310341d0f80d03a525903180900820b919140c540c881c0c0b0040c940c410b04001c42040208540608820707003a0000e00c01c40305180c0031140c403134032900202244a818000401002400308180d8100c900e07560341448103440e410944c03c04241588203481c0c4487e0788020800c10741000144032004140141030000c0c0e01c0d42e4500101d41a03a1250b1b03c03801c1e2240350104240301c0344002900690b082022450182400207520021528a11075904ca4603c907403204204950402e0003500715a0403030503504541003121001e945103540e5850040350803008114000000001140309208030740c22180001e1280448050707540b0307074140311405100d0300d528124283e004041306459441c4010f070040d104c0c800508003894642040034954100004c5200040c1c1440c0640c00075558410989054518400b400a205240c04501356098400c503440000c0701d0b400810390001c54844020032400c040600c00e130 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 904682508 1250 904681258 904681291
    0xf050418050421201501120302070603020a020a1106041a120105180708070e06160204060509040b06060313020d200d2d021203030402100311070803041505010e 70
    0x1001890700c2c11091140008008130304015807540150031502400c0503d000341e64040000040c04030500d2002d0300103a06003081e444032003080580c10440d4200418152404500b00f8020305402901c03490103c00103010032641d60003840c010f41c0c695080320000c00700122503040440481c400f41000b40c101c5907043e0b440b0404440000b070a41426800ca0500c0c41c190f0484c08080e644541f8242c1d940d50018144100b080941c4e14000101d48070f40000b8480b4001a0b414804400403e1040005a0380c8540040780640314078000d100001f5107079105160007110807905243c03282e40340c04204a210000000184d8000c6042440c0020b00541901c0c1580f45840310031085415104401801100056040004c0007040b007e80c45c4500303181c2544884800248004440c00c40c0d50254001032081609150008603540000040c001180707004064829013126030700782804070005403891106103010703201006d4404003000001404100c0c00c0b0566070043d8590035000c024a584410140f080d1072011100b62600455821 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 904683758 1250 904682508 904682543
    0x911191e0315020c030c0706050d0606050906181c080d1a0904020103020d150906090e0607050702010c17031003020a320f0a0305010c030507090602030a0f0504180504 73
    0xa490380660b50400310340c0b00842c8038240304500962001459040c2e601050003280d40c141400d101400c010b0060760b0ba00da44810081d40a1001c072616607025005118040240c4005030321100305540101082203440c8164058510200d6020075000700500c2c109a01010740d503040018540141070038410400c01000b003c5c160050520106c0d10007160301c0e9202c406040040d0056100390000e001d00c0b110101c010800701d990b03a4209005100307036003020408548400342403002d454130340f0551014130300c1070b070003013405003031501b400b4100713100c1d40c10301074100301b000000302c0f06100c41d10250050715000030030b415a8030303d0410110640c4803e030b80412441201040b00025000a002d2a5041c0003641c0c00e032000c0c0c5454038005082c0c07801496190b5070f5000070442052a54507a00c25072020000d5000701d002013805070364031070010103c030401450300e010b010748180c05204940d8004180c941400341ca05081903144c01c0f182098402c3d0003180c3c800c1081c00803000c50303420751081031b4000b50301551142c8450628916180c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 904685008 1250 904683758 904683809
    0x20a0212210708271e070909230a0209040303020c150c0a0206070e060d05040510020a120605060a1202030901060810020a0219020d030c150203041211061504091119 72
    0x2441d18840a40c00500b411003965048072905170348134926011528501d40d00d4030300034103480d8030b043c05030ba80100002300c400c11003080f6580584441005d201421240690340e00155101002800140c2059400319800d00e0610003001041c0704051160f200345901e02d00030085d860307594003012004d0700600441c40420030b824040d080140c0910b40c0100050b0400d2a44030100006000041060310f583c442c070340321400b142c1104d100600c0e8010701541d0701540070800c4900c80c000d075030080c3d0009000d43c0003003248005050740981c203d000341d4640030300981e903900c46400d181e014000c00d4102003410f0080400039840020300e580107040c00103054007aa100161000c0409070f000a110102039005149110320b0301c002032060055140081c4540041d8016154100c1e94408907002200c00311071208442100809403a0460740300040c80d00f140d8014149860720207500022001c40c005003900558403103020400704028604c0031448900d01525200c0800044040000010780c5032052290100300f0b1900c42a440412 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 904686258 1250 904685008 904685071
    0xf0601080601140604050d1b0b030603060a09060e120d1104030c29030f060108010b0715051e0a2406050a0f05070212150901020a0212210708 62
    0x200c00142000307030700e0035007145031440c40714a00c0c41d4003200800001c43c2696941c80b201c2403042c0103080d0010342030030055040d04905003a41003a001c030b51040c4100419940c0008070f0a60104800d400800c549210f850020050003140303401007039030f001c1c0c00501912144003001502c4a40b918141c14000381003102000961072041e8040580011807420080c80300300e0350084003d0205613090300c0b0b00c0100c3c1c040d4501452503002596102c00103e01582400320380d40c0d0001d44140542000c2c180303149407030391a039141e40071040e072010031840840d140c0c0000703800f5280304022401040c000c1e4121505a10300001c408009000301c2e5882700e4200840280f000f028001100e001c0701369181781d2102c23454180e070f11005680c03040381842600c0400070204989030060322004450944001e10700000d00e41070a170850150603955004000b2140b036881809048102c69002030b8590300216a4808c1d82e40e40d80c0f0400505a10b42418503030120808000703001d003e095a84482018440d00048288850400d000031200080144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 904687508 1250 904686258 904686269
    0x30c030b010206130c0807060c030315180f110f0403170a0c1e020a030b1e220206090303030112140d080711150a09030e040b15030a090c0b04080f0601 66
    0x3021000410380039144c8626182c090041146030704071980d440c1440e241c2a100d0f0003c0380051a05045401016014003450540c00e05410380d03030040c5414050041b090000d0300d0741c280d0590303480b1628400c0d1888250300140002146017403159461002880804803503100384021100041503c884200062506003070b25000340f4150f640c00500900b0352100d9840100810790158400c210b2481140103960b031442d420000e6200e00d41c01741c0e2501d040c6c046442004082900f0710024904881042000301030720804c08140084054080307003d103803a0010544178040d10071a00e8042c40004004668040d00c1404803a41074416150360302100d15481a0313a8482c144034072008042070042010608160166a0200f02002c60791304032a8094014003c0c00b001210a031400105150303a03045820178035074080440d001c840f03020348045c012041683c000c9800d241c0014416031040c240480800c0c521203103138002c00c859507001004260b000385c032040080c0c0c2641c000d10582c4500e20602640c14014000410550704032036 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 904688758 1250 904687508 904687513
    0x4062306031509041103060a1b090b0406050d110d0510090c080103031b121d122107050601060909050f0405120f04090e250f051e060a0e01030c030b0102 67
    0x84000b000d019004a025100702c0f00b454902c030512a0985040001c03d204014200e80459400c1c49078480c03907140740ca40b407144403c1140390301052292100190444048544034940f1071341e10f01000b01c8090040c003002411000703094000400080707038181c0b50080c034010710b50820718461480d9036144a030107d61181110b03001180c480b00040010a004100c00c408500b003050031600d5a8849940b010010030a030110603010404d039000c00e030b1454224510410300c1020581c1c804103440c0d0b0240d0810b580742441031055221003241c8d404201300c00b15030030940e00304591120464005507103900000d070030340415001d1084428a0113000442c0a2103c10f0340340e01642d040310184c5070b1240c4020400506078440035942c89591010000081d40c11010311901481001d900090603650000b2640180f40c0f5900d0340022180040821082c403880d000200c0220403124101d034104024105105040d082850b03015059501010100d03031a500c01e90481100b10b1041c2d0241c1e010401c10b48108000d80c00c0780c50b50844580141d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 904690008 1250 904688758 904688791
    0x515070b04060c05190914030f150901020403050f07091103160f2c100f021b010e0907121103090706051b16181e0f06050406230603 58
    0x82c00c0394090b105010715031030f1051030280600079000050005141400c006429100704000c140b04000391040403a80440280c1510100500c0c02503403815401c0c2c1c000100c92503900450b404010960445000707507880300a03107022680100c01035440300b4140c03180000c1d080c10464140344251114088a12034464114001e0f80c2422210003100e4030801c4415490034080350800c0004082e14094911400706074420880000b81480400c0c8940440000d40ba201413003201c0a8141c1030355004207e19019401d400111481c00c170914004880304540400e0041d0042c1584061040720f55010317003103490341c0800b00f1081c064000740a250812a2000f16000103481d0042d4900380b2155115000415108a8018050810818000149003030001084a840b405d66100707034200b180e1541403404844c4a40303051020403840829180140c0e1006441126110ba03607503822030323500e8005055100b0b0028042c0500104410303901d0b0010000001182691100c032200700c0390a415807441d10f80101c9124411255181001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 904691258 1250 904690008 904690013
    0x61005070309091a13050408030412090506040b0c25120c03080f090108150907050918010b030a060b0f0a0e031e0105040b060d02220b190515070b04 65
    0x2500160401c408001c403880000a01c5100d03805101c01500c06501110782808925003040301c2c0400d02d040f001812402c100421000c51580000c1d40d9219400c00403001c90008a018101c400e001c0c0c40e081b199110101103030100d6070080309030281c0b0441a10200300c0713807035800061000c0f0901d100b03800c000f00c841014940902540f01c1c00d1101c1c0145900c1188c80310241c90700c0e41e4803490140c100e44840525010b001c19130030240d41c0c0c0804025000850404585284d00c92000801d01080008200b074060200016689000352140742e495a03c240c0c90740c94000b100e507103e4401d0501c60388140d6240c030781581032520200710000d5000441d095001c048228620f000b1580105a941d481915009a41401195003820122400b48400e031104401d500c0002103034541840d0401101c00d020b850103000b1011a6441401a01c1d1050764103101c0c402040c92400c02c0341c8054022000d4640d140d1a0750300005180c071a046c1c000358045454040d914220b5840740c0300a2000302100c04c501410b01c0190880100c8800702c0c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 904692508 1250 904691258 904691267
    0x306060d03111603080304021519030207020d020d0303140a0c1d030a0c030b060108010b210c040906030b010509070f021002090301271208060d060203060d05060c130e0610 75
    0xc6640b401c1c010340d40390000035420740341e503002c03254829907214800000304411890a606814482e0325135580c02403c03c20800d040782060303a00c0b00070020905900150402c250750740c40d800d8041d415401001181c1401c1c6901c0d0040c00380c0741410400c00d117005904042006504980201750340310100b1340d250341e02c5840e09112112207a0702c840e0125010300410103444045401c2c41c0503100614010580e82c402070505500040901105034000140310505004204102600420301d40380d01d08440ca0800168036038402c1440140314507404524150310708100001040b008481060480700308541c0400c40e5aa02d071819503030040f54a08120058103e1205060744031840d6024181014000e0000141030b00080d0080c0c5041896014460307544602c11404010030a2003500100241d41c20f1510743d4490402e84089040424500c070000c000c141c0101c0040c0e0251100140d041d0341c1030308603089035030600b0802c400082a43c000502c0721440008103c001c100a01448481802100041c1c490400020001800c89 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 904693758 1250 904692508 904692527
    0x90f24050a0212060319061d06040b010e010b0f04090c0909021c050a0b1c0c1d0a0b1206010501110321041a060105040e070e10030e010c0c0b0105060c1e0303070e0306060d03 76
    0x5007100408032070022034000c05c0152702d10880c41442c402200d0750602640900d02c010590207040c03221820030011021481d6142500c1c01c80b050b80c500414494589101503950918a030043c001136031012485103007201100c4202043d401840000300310310740340c41c0d41200c141c1d410080c000d81c008a45030303000d0f000c8011000000304410b00070f0784a030524940302d4900e480c1203500c9800c03070b010440305041845a81120742c13003443e0f04150704560040f48841320b00e80c56a00d4420521030303281400708603101082c20b90010310440e152a030070710102607250b00904007840d401d088140d0f03080d02e003400621501d0255050101009002c0c01050315854103140c90300d20640444140140403608025007030752203400c41d4554801c03044810400d6240860b660480c04400350844213000c03450030811902c00c0828011820300704a031170550788299412503948194075030302450b2404030286045c0121000910513100d000c00300c0036500a428503a608400b440c001c5082581d507542c00e4806590011000c070f81d08001078000c001c101d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 904695008 1250 904693758 904693781
    0x5040506060a141b0c090115020c2704050d031803051c0e061302011d0108060613150e09100513050a112704090f24050a021206031906 59
    0x282d26010880130411000205100300103400c0d80040302c0300c5264601103109a000d4108107040307011110107040022741d2501c081809900a02c01c60901e443c0180d81201c141c0d41c0e8500301d01c840c01550415281160351030a4003000c0b20002498001504100c1c1924400700c2c0d4880e40595490341050b90813129070844035003811140301c0352991901c100501220503c181841070701d141d40c46a0803d07565000141030500c2144103281c1d802d111580e074103016a00180c5458201c5001d940b8180c82d0056580e61048041c212b0b0040c2c00214a845e071200700880d07220200341001e203815120501241c03180c0c0d88400c0449201d00403290701c814041b10160403208190f00003a80720100040118902c0c2c84c01c0715040c0d503a0b100300300c155100104002c254030134040c40010f0210050741950200010b05158031000256948000002d0004c00740ca260000c603400341c540c2e0980400c0190400f08a1800c1890003c0000d6008100203011071041100050041c5008141c2280d8000d82005440c104485ca958590040a00c80e110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 904696258 1250 904695008 904695047
    0x90b0117010e190f0e0c2d0d0804080f0c09040b010509040203070302040c110105091c21020f0405040e0703020a26100204030201020721030e13150f05040506060a 71
    0x3141003650813405500c0e400c105032240000c0e1251510b1125003008050301007a4000c0c81d501ca03078120019020100b402885a5086c002c9801d560610b000504403500c420001c0c00320384001c14046a00030300440d580d0000081c50048a1582c00840e040c004800e2003114041d040c940c01c0c20040196040402c0110f038410b20003000c3d03030f04468803580060112200102503c0000e0184260145c48400c00d12606400c00400c1000b4a241c0440000011135030500105403406c20403a40d01e91404902c0e208007040384000018029501c2d05c0240407124026001071084a1055042499041d03030042d000ca9404140d980190070017212034180207414902d12805114000c5040c04010800c1c40d85005000084c058001084090390307440c55400024548441d41e0869034504d0f0303141c000096a20300e050880c50103540d05041220b0100c10500c001900003003200303603c03140c3c03a0030030035580101412402904150b407081c0580c3c1c001651107409020440f081258801d420074010070852032058000e800307144c50041d09009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 904697508 1250 904696258 904696291
    0x10f06090f05060a0e090c0318010603021e270f0c0313120e0303030a090507051c0605131506230105070b06040209150c010605010c0201020d0e0105090a0303020601090b0117010e 78
    0x104006ca40e04450070b042d03070580482400240c01e034804540030400d001d40c00030301103030713083d40c00207048119210840004840607444410090b1a001810a10264060740768071030004651080041181c04696100104404c400003071420007001c4213072800b0300411000d504c8402c0380d5555004c01122014191010310240503892640399500308003e61080394500700102d007040803032070300340c1c54480660421481140e5602241c0c01212490b00300b08640e0303400050114094a6101405c03610070b5002e08090143c1d400c4402e07140544103250014412203810220610540c0301240d414400c14560b030149a0008200300700c0710001c5001c00c1d40b06a00244014001403410451000013903540701880f03003404980f2804141c03608019028820800109420308040b1001c42c51580000d40382c4880d00700700030031721808002001d000d0344241c0c2541d8003100050300c3d15101c95100e0038040d541da102449094075640c1010314510301544141140e0780ad0040c2801c1c2541c50740d0070107006d602c0c0d01000502c2e940d40c0d440000e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 904698758 1250 904697508 904697537
    0x91305071e02010204080f100c091d0c04090608030c25050105070510090f1703041e0c050306090f07080a050d0f180303050301060f0908030a0f0201090515010f06090f05060a 76
    0x2d0f2450315107c8003c3c58501001802d074000c0d1102c410b00e64050240300300040182d000e080385040c142190907412002e681c0e0b220907480083d80281d40111031003600d448070106054170000b00501150b01c2060846a0074103c140007407046050803e01c0140061502400304090350180d0b007d030220b540302d0030640c3d05111441120508030f8081030b40a0f07804a01c83e4440d0380a005c0320017120585030b000c0036200782c51403509450306281038044c500750f108035401c3d41e41540c0501880e50f4104001d404014181c41c401e04000003015551005140b411102c0d02503840c0000f034030365000661a9216500c41c000c4e281c42c4542c0e04060300d1600414410304180001850301154507112982460b000d14401d8940036101c2d41002d03030082800c03452624070000c0c07001040e0180b107200000001d0794006100c0307241000101c81001401c9000d01020f010086c400c4c410464142c2d003040c5c0710b1000d18141c40b0903100011089030380e91411595000588203200e801e140c90442480b15061010040055420b28207100c5c0303643c050710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 904700008 1250 904698758 904698763
    0xd140c0d0b1807081b0c0c0f030309030a0c050f0906091314151510021b0303040f090605121204050f0a0b030f0106030e1605040c1403010803091305071e0201020408 72
    0xc42d02c6600244d200410400907403042000082c050b110800d03801e013005011000d01c1e03500c8031748034150f51268400700441d452640c0e02304102c544455002d4160381015001d0f15240c40020751f40c1c000c03188611480b2070000c1160134020001485203a00907c10b80486d16410340070b50207454240c0c0181e40c022804003a200340e10204002c4104c410007100030078180c41ca828401d61203890003500420703210b510f50011408809600013452080004000c512600c0710400000091861003207502c8030038031216055000982ca2400d43c01181141c5098a00c0000807018a000030f4480039000f03850044a40b080c8003d000d1401d164140d403940c928090700c480e8001d13807500030064403030700304a80c1c0a2003c0e00000040c40740c50f1340750054900006200004182c00c0398004102443d11b9440e00072240500e5440c1c0110542c070b840ba20b5007100b01d10406003a6513403544c4502c001901c0f0b5000004482c043d9505201e00c075500c0d1102d1048034850742ca10341d6040c842c084d800d403030910a9440030604004641d000d21005c41c03150342c107 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 904701258 1250 904700008 904700011
    0x324040c0b0408330424061e0501020606130c020106030f052401080312060406030606150311040b1206190602071a1305100c06050703020d140c0d0b18 66
    0xb030001000d100482c0b0441a0071022801c50a40d54030b1080e0300304a41e0780b8901032080e41c1140d17015aa094031143c06c044440861207480c12095240d90810781e0014003281038614003599440001a82c007021511003005a9498100b55046500801c2c1120921082050b903400502032207164800802c0f90765032500c1d00b401d410b82d014810740752500603441300c0400184a004032040c00a080805000540c905021507880b8001e04030322050344068000081d40503980c035400a00a941c0c0000104802500c444400380d000c5048a100400300e8a003811111503030b200d400c151021a52940030302032528503815001402454042d0609400030020055051080120401c01340904150b6005252640c5403031282c0300b405084450001c07100c681042001200400285090140c0300180d4a0301c07502303d103490017100c840101001c0503143c141780034140b01c46641d158004018201c804401031207102d0709050600c15000007910f600540840402c119040d54140b07400410150760010600e4210021310f43d000400c441c0f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 904702508 1250 904701258 904701269
    0x812120121120314090d0503070e01020f07030305190912020f041e020c1509070e0615030702031b150109180803040f020415030506060d060204081506010e0324040c0b04 74
    0x480e80c0c00c0c58250203013160f0303181d44008060018080c40803491000303065031002801d0281000341800d21440164000c00c29141400340c0481200e01c01070b900d060040040d00035283d80f9035400c07071445000010030710691041083d02c08410b4501c042020715401c003c800c1600f0072600350010f0f140e009007151024900c9060064500800000d45e480c4240c00f24941031000892030f4509410142080c0140402c002591b202960503401c0029201c0c1c80f00d100080311140701c10941e4076043d60001c2000380255022015120f40e186c840e003094011802195000d4031176241ca6800c101c1c4c0c1003000700411450000d900000b60141c8d03a1018243d480e1000d45a0030104d5104a41c1940c440610801030400c50505104802c1d480702e10755400341c50103096664103a250640607003080e2150001d566103409005a943c101c400805400341217802d55021140442c03501d1408071000d80c0802c4071130400c0002402c011a21080700807002041d404150641c09100ea9000400340059403002c41d622404921442240d005001408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 904703758 1250 904702508 904702511
    0x20d0e010c1737060503120408060601080103030807141306021b0427050c0a421d22050a020a080106030b13110408121201211203 57
    0xb0070110340e1404080d000780000e29980c1d030101031200300034141c002c240c11035052018a20901c08031a5806800742070590402d83d03060049401e80c4040102c010004c0c8200c40701002690b503690b84590040d50410001d00c40540880d0b100b000050945108803030b01c00c041c07003060f1405814401000c00318000800660402409688244d500c0030308400c80c11000c1c40400c4d0116818030400c40c4113185903080c0d000200e40c1241402c90740700303620f013085000d00160140c244003401000a103561043d0000e48907181c440c2d5005248070aa9000340c0711601c1e00002c101f103980159a0f00c0071600c00c05006c071681c2c000c240604140c000348108004095445008031041a010300c0341c0e011030703510b0000c0008100e8902030540c252aa2040104e042c031590041c1040d81124860b0800091030000b110104501c619483d4241c00c1c11440c044803d546040314001800c180d40304003045170741c15400e4922a1b99075100321042480400b00348401001640b91102903001c01c0002850382d00c5002102c0d640d1502070955000d8440d011a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 904705008 1250 904703758 904703777
    0x19030504210c0b1f0f05030a0b0703020421140a030e1c080a030c020d0905031906090611040602010e03030f13020a211208070906030b0301020c0304140f150d020d0e010c 74
    0x901302401e02000342213441402988140340c44006940c0d203029050003000c58042800080c80030b4001c0d4181d42c0182100003a21404070303881d604020350fa0524980455604124403418032940d200080c2c12261150305480d001e521901100c100550401c0c545e2101e81800d507041c01c0800081d1040e00076011550441c0c0300032600091003507002c0e0811906880c198100540c03094200400c1d41d0020f1484004504080c03c1c0440c141c01e420000f002c2c1c284000082c0465040400175804907110300024001c41d06184d000300240741608440d507440348002d9681d942824468004240d6007032089820014461009025003002603032160400f00c010041c07002071410442e000700b030700244012580b00104c40c07210b51801400914100001400d6168640035260400d0354035500a144e81d00d0940c1103990fa55000d40899440310703555848a9180114003610798040d011000112074281486c01490380b01c00c8041103000d09085c0680c101100a410400307005040b02e440d41a60240d01400703102d00d201c020803603610780500307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 904706258 1250 904705008 904705051
    0x1e02040f050402010809240a0e030c0f0d111507020109140601150305040b131e08091207120f060603170702090114010c080706060b03070519030504210c0b 68
    0x92030050000185402081f05c221100e1480160844190390307001c0e0b5401d582e00c506400700014941e680c3e04010f00c1c880043c03e6a03e9440c0020800340f50f10111040303e5010700c4140c4111040d02815801000302d03448404147c1c0340243d00000d80d90710292501c000110a0150b40f501c80c1c1003001200880e42c1500303c3c0c001070140728103400c2d00d030640f20141e00303050016060640d50b035500554001c01029600300d1581814040101c010700c01880c0303a260240c410500740281c1003400321035020140842c1b00b039400007039491411201250000840c2c2030481100c4100302e4689aa400043c5030300c0d0f080324400d560780000701c002503602088416000c5440700140d1240f00c0d0744140801c24030180c00c05c40f01082c00705080011a0b900c20b800c1050181e110001a4460b103442ca04400a441e498102121148004c0100140540c6c8540a844500011414000001d110b070006404440b0143c4010b420b4811110442101422901942103000f040345003d42852407107489800354980b050f200d1500c501c1d1414440b807007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 904707508 1250 904706258 904706267
    0xf030b0f0a030b0f1612200f12010801060623040e070905030f0c0f130e01021b070b0301060c020402031306060905060324011e0e010305011d03070b041e02040f05040201 74
    0x90200312005141d90045c117482010309052901076100f15500e403a030b03c99180c01c414042e40d03510f41c40318003d000e54641801e1007810303884d41c001075000d20519110000000b0b0042050180c00d04507001a1034841c3c08603a01210844204110344000c08031903410007001540f021440c003460b01c1413070103544000c1d0039070903c1e040504054100540080d40c1c1d00c010506205981c88803046071610200302c441141028403e80010090192440c8a000035480031891044403581c90007641031800d00d00c1c05807617120362519024905c4e03010030702480001030a402000b800506095001b983c20207040c80d1000c00c1407206a40c1c0205498182e00400318868460342801180e080130028038161096000e10085400b400914034151360005118103800380725060b0318040f500380310211000c0600306002011410350303100e0412601a02100c01c0b5260300d9246038030605181400030044d2000240d10032292031311900c4540358049032200c1c86402d010000006007040005a03203502c50a9040c08107070340040384501e0507000142 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 904708758 1250 904707508 904707511
    0x8091c0303051e091f1d070e090714010e0a09020310062a02132c1006060203160303020f12040b060301061a0d0b0604180e0d0f030b0f0a030b0f 63
    0x30701c00195005000e4404d20100e1000322883c244041c502e170100f050450740700500800c1d080030002e10000040c1d0401d0510100d5003505680e805054030b805030b140c0785059a518032651044102048010314914084e43c421441030048542c000c2c50046070a45643d54142264000d40f400702403440c03102c008000d015080f260303501045443c9803403010801207129241d2041e41103090024495005800b00600c41034003030380400b404c4103ca41c200d0090711558000031b001800362101540d428031914002c0241a0320600585098500650240d814154030a603404090001e00074210241a003e000782400b10342003401401c03400060108001050825060510800101601c0140603034101101840030781c0707668001039060355003400070396502c0390300009180044c200720040c01c4d4404400140012404101080c42c0c84621000c0d0041011600c03040f0100d5032402080442004039199042d41c0039001e010780c0c40007010b0b01c00949004034900c1c0150000301000746a400441c0d405440703c084c0002c0000c40c00055 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 904710008 1250 904708758 904708801
    0x20a0302091e0601090f050d021504060c031206030c0531060f0f030f021905060a11010c08010819060f060306140a0c051603031d011b0203130308091c030305 69
    0x61551b81015440030701a260350080328011036240440b1021901c881403203080f82c0e1284c2d40101e03180c07600d684000302000207202c3d0039800070f5034001039818a070101748940412203030300001035003000d03290905003c1e514040058551103402600c1c42d956400b07160340070b03600d0011480200040d082e400c149501c0e0300e000b0540c0101c0c500781c0d0304200c1800015580a05450300d103404a40259090046c20000c0d0302d20b0146800140c3c12890104501c1d60203504505110380220300c0200a000d03074100303290100e031f203583c092013030303902c2c6134054a04150901482050030b0708560040f07001180107840746082c803044c1d81c80744c2d02c100c4000d595204050400020145496003250000c0804d10036001c2d01c02e0003d0003401804048101103214400c03650030140a940301d1144400c00044610307010b02d034640118000d00c03400311400507a620340600803c681e84084101c401a41011803403450483c1151103607441e03130b0400c101e250303000b200c288543e1110412502c02c10010610968021034241b03802c00c00d00381d4055040411 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 904711258 1250 904710008 904710017
    0xa0c021203160c0507080f060406060801051014040204031e06110f04180b0d140c010504031707020d0f080c19020d030e0f1507050c1206070804020a0302091e0601 71
    0x7440030034901c0441d0701e2805003161900e80c103c604203050a84c1890b0140c2d010110302c0c13045640180f056403011070141e110724010b4004000b165a95078082d4240c4404440c8001d0800c102c0701c0900c414400401d0701d11403032001510050515403669200140550f4440c0611b0222003008180c4041029900401c071900070780d04205030401a0000700724031180903c0c001c61011050501240089000540c002c050b1048020f00d2150071050904240525010903840e80e2001d0040d0491002c0301c0d4051022901120b9100d0400700b1110b4041d48600060341010340704076030000c0e264043c0c502250300102022022030007401701030340d5600c007446c0c05071a014402c0300034595055180d0400015070f03584401038240a030503041005050200b039002614600010150035880038845003426040e154681c003030102180300d00c0c03c030b80c03500001c04100402c3c81c04a08001000c0d5100500103140140305414241c0c0042c40900700012007926a40020009441100c2c8445c0e01c001011a02214071401c0c0b07680e980000c8213081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 904712508 1250 904711258 904711261
    0x7210507020a030b0a1b030c0f0906020d050c010e1e0d0e0d06020c0709020f0919051507030233130c1406040305030a0c0510020405061608120a0c021203 67
    0x302d031404000c3e210107400340c00ca50000031002c0340c040e00480007000b0000b4405110b202100c07005001800705003107040002d5841e0403040d0342d0901610b654010f0382e405400a0401507184007084078154089130078002c0554071022400d000420800801100e802c900c0d0602e000b402100301120b00d444c0410420008000780c01c0c07200c024584546c52081446a0042c81c01359032521500c401610740030050740f0206907140300284041038006000040c020703d8900b252003040c001c124602c01801c00d8100d000740d0b60b02a884851182402500c0f200a00d4154800d006036800c021030050609442c008004a2211298105041c85040150351016603801003c2c60504001c44078103440f5012011168058450f1b6001440c20710ba1850303446206590040d54400200e959660b001d030001040710b50a404100c3d81c512508100c0c11506803207000351029648040c2c50141010b41c1e6811120b030000c0c0084040d42c0c080c1003000030032a9052070300100e51049881c1d4001180f102482e44000303140c4000c101c3d441c0c405860500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 904713758 1250 904712508 904712513
    0x329091b0d0207080c07030503041a090901091503080406090513181103010908040801060806100812032706091905100b0a080318130207030507020d1707210507 70
    0x50941c0c40c40002101d0040e01ca0000d490b03e014140308401000466101d800703000010030200100a0040d40c1c1c3d80b03010ba0200714480a1111024000c5d2007509900c81c08000040c07040d4072881d0b02c40000c2c54240001070b24990f54a40303c030401c0e80e109802c0344e03001a045460030704c414104001d03503c40c0040400e400b040500d5080041c0c102110410500401c00d421501d21030340c581c0d07801d4002030340650f044a043e55540b81c1d94610a0f009000d00d20a401d054020540007503400014100c00c14200c0d08014040e14845203075821054203584014046200f101c000700740e4005155088004004400d19071009000c030b130614254162404060100b0000d9110030030010100140012415211400c040796020544100610000b0101c4d02e450300f20140034400440c0c1d01c15000e822018542c44c01e0402d88080f80c3c61101848413805a104504010b808100e042042c4c6005040a0001258190040c8908842c003041000c4810b9980c3c031105d000c0d20700a5503408021a540400820246842051305180b46000c0d03160b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 904715008 1250 904713758 904713811
    0x18050601170402130f020405060c100617030412062a09091a120a062415050403080315030106090b03060105060c120c0313060f0e04050705090d03032909 67
    0x4d14815240d45c0d100c00501c1e002a2958050354003600001f03050580b55014078945a9495400c0c542e401501130030f003000006c01c0d9055102c1d010742a10303401c01440c9407509259502c4207541d84054102c42080e5143c00d0444035410700f008154400e080308114240035007100794018038800b001d8004120340d82c41c0444807040c400300d000d11302e0b031418426619007a0b6610fa005040d41001850300700a81000d04242017106043c0f592a8200702601d02d540e4030007035254440f81d100113035401c500004408544200418004030f1410005194421484a4010300321002c040100742564029030150000640321004c0440501d400d000d41030140c481558242d080034040309045903a04a4504c0c500074407680040c503820401c07001e00c00c44103101408685101402d95910000781202c651102c00d10005221403503800031890a8010a0b0050b052a41e5080c281103d81c0704000410305c02c0c1d8012020b065403003aa440e030400c0440d4030b001c80c4840304440d41c0f0b440b0b04000144413280c1401403400400c40702514100034110141e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 904716258 1250 904715008 904715029
    0xc0406110f06160e1005091809030d020325020709060812040512121c05250f02070509100f060f09030f03170a0c021006030b060f0a18050601170402 65
    0x1014500f0000581040040d00e286088440c550741204028845210250704480241211001034841d40e1003d444015040c031196410340745035143e904100840014448a038005e07680020f0705040c5d00390300b480441f656549091001da03150300980c11903401007001e54000c0c803500000b03242e890060094040150068550b51150b4010310b4402e0641040070200d54104201680030010007109256603809004c80420120b4080c02c0e14640c030a04190008096018455504001e42030300c1410000d4070180c0001595194002a090303021482a440001017a640d4000400e00480707004540704203490910100d01641212900040b0500440446103041140d00201500c00c680d001038010035103c1503403034112144840c01c11000000500030741403080000a13035001708003680e619000ca62071900d000b94514207903005480040c02e401058800503040b4100a00c0706c4403030403402814150455141d099104c1c00c04401101090309a550344200705641d40c200b004c01c4280b0b0703031001d0309803940d151640c001804810b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 904717508 1250 904716258 904716271
    0x30c060e1b060705120a05040e0610121119091410090311040209150d150503030901110312010e0906070804081603090803030123090c070201050c0c04050c0406110f06 73
    0x2002400c4401d004c0c05000002006030060034495407100310308401020741e007040c0500b0302c0910101022880e10301d090020645801c0c02034940d0340102c141c0825450003802142e0b010a0107074020081108030391035428584840e54200c1d02c56401c01414001c005c4454501c0c415034502540503c00040740458001c1300060407650700c0104426406c0714140424060b01403180100d8010404e9484150703903001a102030014009a940e081010240d45103081718070400c14403d10303070560000c019805082d40700e42000860850800d04591900d182107440801a8800740d10030800c9801e0320080c0010700f0b01c0ad01c549600200030740b90004150406445084080c401c11803400a494800c0e00042d04060048208000601c40035080d04d4803136030740d000400241c494007800c8144040004454058510300f01e6006802024402c101ca410b003c3c043d0f00545441d8004851850306200c2c645140c00141d540e40109446010301c42c080740c1d251413030f068010f00340c001505907854281d04441d4100649060002e00c5a60118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 904718758 1250 904717508 904717519
    0x1050909070c0209040b0708131e030302070f05010e070603110313030e031b030c01031a01050f0408060c040501030b0d03020a03081b1303020a080a112704030c060e1b 73
    0x111541c1c010b88000c010244000d401000003410002400540b40180b441150b46407600c4505c3e540e80d981036110822074941c01001c2809095204020820352107164a000c0d110f41001403030701c1882c0c0ca49021201c000f401c202e6440e07440700c116140a00c02441141d009102c1424284006604200b44a0703881c04000d02c10b8503510702d200a140300b418451183e901a0a00c00303402c2d91818100280c28075a081060790806010b8884d079401c05005511a215802000c03800040340010182c0850046410f41d00071145114000014040807504240c2030040750701071020005030781c1e0384518043c005000c0ea6041c448c020300c130f9890804204082500464a4403000c2d038035203800041c3c1d40e00c003400f00483e5a2100e464072501c1d0004a04021200d191050303840c2524001c6404d4000302e41c1d9070301240c3d641da6071301500600b01d0780400249030b81340c1406d03d1281c2c499405845124445400710090145d400412607040d40056040350b108000d11606203c3c1c0158a42c100c0007403c409841601842200c9400440650190 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 904720008 1250 904718758 904718761
    0x3060b0d0b01123f0c0218090109020307170624040f0e0102070f0507080105100e040507090207050c1207050d2d0f15020315010c0c05031f0f0203040201050909 70
    0x1442045a4221008080c00030742843c0c124000500443d0000c4c5414021500a07500d5000034064405040c0456004040140c1c04081034080c000d00340c80500309008964032103c955006982c180704400103014480c001e60000c0e075036000040c0c40c0c44800752203544078444003290710342421001240d0904008090300c3c04198500fa400390b03000180510044034002d9440424400108000c4104001400303006104035091503490b2207045003241c2040c0c0d8031480c1c00c2d50307141003000405640803c0303d038090b01407003da400480d40d440a20050781c2c4101801c59041d000300b09011400d10f481c50f212084201c0c984001d02da150700748000f29188455101d005888070480e101845428080318403400401401484007281c000c045103030040008001600c02c035550740b42c2c0450508440f406100b920311a00714802c001d52030140ca500151000140040700b034a201c00c46610200700e9403001c10200c20b950f0400c0300200042c0c404082c42038111140302e110302ca5613500400a000160381e0100c151082d410080701e01c5c0c0c925 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 904721258 1250 904720008 904720013
    0xa0b0a051206100f0e0d08030109020c1c080601081008010f050910060b18190303021e0109030c29270703050d031d0a03031506180e07121503060b0d0b0112 68
    0x20760300c000000c07d4000000b001083c070394841e401601c548003000c4125000c0c20b06c1e10050304210329420340b03a280001e03036030030000d42c541d8406e041c500d8100c1c0c00001313003031200383d03d5000f0740b820740780714001d45451035403180c0034884400c108001982460103e507070108165820249002030920403910000e01154024005507000c3e40e80244c00c0a080707000240d00034200d07a42e031030041e4854200d0035441c20030300441401440c00a0040c0650340b251541540c03041e032210803907603591080c41c803071881020b02c1d01017174100500d07540c0c1c50000c0a40190005118801845030a00f048210402c00a440c0c070300741e82150f00100009180000c20300080038207403c021900044c03001ca40c8142003642894200c50740b10740d8100100b45038040c0c2c41518490f9045503554070994583d0002e0303507090703103c0b1030100308210b025008120051078484660b801081920b09410104445940c0c1c0040d66039015141036445660704042003086040d200702102601d0503158510244450703105c06c00c00490500c43e001c03140a9441c0ca0008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 904722508 1250 904721258 904721269
    0x70b0a02090f040608160605210c120906270304210209040606030312021c0506010e031b0a090b013203040807020907090803180a0b0a051206100f0e 65
    0x2150700000c3d0081041690310a481d6130b8508440c06000c48a098410010542c00c0c420710840d0861108074269011781200070b4071000400c4401009000c0d2182c0601c00314041901e241c0440c0d0040782d5a80080c01c0505041c17844500c02115806c05241034001c1c0350581d9002c01c804410b9030125407944158684203050001100e80300c008440009500814003c100420043c180c1e2060382036038042e6441c1070a00710725007000c1003280300d504840081c103807060701e001b101044d40d034000325071102c0103142c011566082e03040030038501400c04000081c541c0640b0540005800e044150000400058006210032806200080e0001488400002120603510601240c84540c17005446080d14040d070890360b245018100309519400c44403040f4850761071300000c00e0076548222900c2080e08c030b40d50050b41c07609510030b0706040c040d00a0203042c0e403c01c00781e40c1c0000d0401e4a40c03000d40b81d0701c6925210305954a03501540c01d90300c86401410241300306840804886480d512114409142c0c8082c2054014201e00d24001031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 904723758 1250 904722508 904722529
    0x30812090609190503130305100510050a09091a0a140903071e0318090506010e03010605031f0b0306310323090405010602070f08072301120e0105100803070b0a0209 72
    0x241c0c6c040c450100104000c1e000070b64240201094000b0030540d11918040c0e410081544181980100f100da020b001714101644445580c80c400c03090000d4030000301c9900c0040c031008a0b100d58440365140000e014900c4640400340d44900a0006145050060b036140140c2511054440400303000c1e504165080502604104003c05816280b82031055234511105000d0401111b0460018404a00e1100c0d181014020841551002000340030b800000780e41444c41d0401e290380b4001c49070788440420750562020700c051801212078940d250346600c0446c00704905404407035a0b280100b250041d010300801c0e4840500780900202d00740340280700b00744d8403956020b8080c604520794014944000011030743e400140181c02c461281e01c0c083c86c580e0742d0784452a25440d59100700e0120035140032414941703003190b40c000c0e5000e000504080d070007000544000300c21265032100c0305a00741e41d508140200159000c8403403004041d4807000394a002010750b903200300c0704030152a48000d983c02051000032940d80c1c55448 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 904725008 1250 904723758 904723777
    0xe1009050a240f09020f100906050c010b062a210307030e010c09030c1712070309030b0705030619060e0d26120c09030a140a0c030812090609190503 65
    0x3408980000f40c107082c0141011107049202c1c241c055511030250a0541011041c070740d1540f2140491031404005a425900a03058040d041d540c3e0820345403156180e05c084e0015004609101900504440f007918600420030451b480e158071800303503100d400da040c0d400c010700400b010350400d48944070180207402900c40c55445901550070019080b0341c043c1d0044400049902581d901340c840340c0d448480600b8200c0d8071411810326002051211102d800010060680c039220f803078845402c0d50f50303407203c490044042d142c1c4400207000000780a114034110000341e104021102040d02d00910b00300700580b403c515200071501400442580c00c00340592540000154001c6600c08d218003068100101c3c00360340030b898104440b0b41d5400104a04080700d030f0607103030804009401420b02d40c6840c0c07103d4070800c90b5074001001e24410184c210000403107400b04030b0003c600c80e401c01501c540104642d28071840c2d0007454201942c1c4250308000c003604001484c1d200030000703004002d030307014510b0601506520500d40351 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 904726258 1250 904725008 904725011
    0x80702040221190e120c0a1407080f070b030a0504210f0306080a0807030c081309060810051009020c070503160e15030d08061f030e1009050a24 63
    0x406021210030b0311442910414080741c45500c643d01c10000301c902919030461350754070110b840418410703081c0c02802c043c0741000c1100c042042d9503460310030640000d180000107800c014810407140c8030400140c4022a140390180203c141004c41490403408028101d60345542c4036400700b07083c80b10703c0080c038402030b0081c914403010034018000030b0542c50168401e480064600000003400c0480403e68501c150782c0060110b01d070405a44013244c0426910781d007a070f65003004100d5400610140700f0110020701407036902045003840c0c140c189013040301640c1c3c0585081c1c144010803650160b00130034042a01c03012000181c440c49103900c014603040d49a0003c03901481050b03008282c48020301180011038240390541085581c0314a0f102a001daa184c80641d0980d1094019100d5180030740300240c1d103c4400b0345103402861909240c0e00401d81c10496080209e55030700c0c0000740d0080148240344000030000820f0207420480d40d82c3d641d403085401c101410800560b100d0000b0118100145000c0c10f466000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 904727508 1250 904726258 904726297
    0x20c070603020a180b040b0a050408010504111f0c1716140d14030610030e0a0311060703110708071e08090a1208090904111e03190f0807020402 63
    0x8028000394042c0c000341c004600140740313006100c41e125100d202070381c24020410741424075100000204c0d81011054005016061102244078002446401c0c0b2960140c0034a842a0000700144010001e0f911000d1a8040700c01c0c0340c2404040e003204060707581960140c5408904111003149000d40d0083d00340c21072050ba49441c02c1800c1c8284004040c0b091020078058420104550074203840b850f9802520f901511010700015089241004d0706c080c441e040c500b00841c5141c3d8103103035a0f0400c5c070810002c078081000404046080e40013045000d500c6112401c08101002c8109102c8030f40d405095402400c17185e0008000302000104089800740e03010102079050900342601c1c0c2001e603608840e210500400c1c03258000511400140104400c1c0c0c1c0d0000c6520b031820f408001802481c0e500200281c2c5c0031070400703003d110b17552100c0d500c1e402c0d1545984010b6074400c0920040500300b02d41d007051850000f400d1905040403c0e949582240300941c402c00340790340c5000d58800f00e0003034090301214140d02e075000038 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 904728758 1250 904727508 904727519
    0x1020d0f0323010305120a0c060e12070b091c0c0b190204030807032604020d030c0203241323161503051003170c0a0609320d12020c07 59
    0x2c4501e06807032042080c0c64103d09003503100b2045019940c45000000c8000d402400410090792100c45903418400a0700c0c0060b814000c245401e41c03090780d0807900d040384c034010449a1002804802425400881039182c0c1000009004003c1303404c010002d01500181300208441d181d052002c0c08142c0c0c1c41d444295100d595a0800045070381000f2000c3c1c0214181c1c002083d0414944622040407812100c07213012503031210b4090103000e4440c03000841c10310400e2940b200160740c1c1040200c0d0714158001c0349090918400704885c1c075070301c006011018180200d91a80c8006204c00e04100c1000d840400300101440034500c65900e4a8000181004010300c03281c800300c2c1d060744420101f203c0856640f03040c080781d00c6080241d01065010721014040e102c40100000c1000d007860010214a207484080314483d10b056160f10302200c03c121003c503203810200f44500d22600c50100300400c0340d85150107610030b002004548039142c840301c501440800c00500040110100c1c25410381d110150005c007100c003401e8031007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 904730008 1250 904728758 904728821
    0x3020f0d0c0c030f08240d05072c0903250b0a050708090303150f01020a02130e07080f03090d1a04061a0301020a050f03060a120c03060f0b01020d0f03 66
    0x220b00c15400241d82e401c1d004e0050b80100c50b014000d03c11050344c030040b1400780908040f8011640b4920f41c2c0250040311583c0071401c1000a040a440c02c0d00c2c0a41080b03c0d0700201c41c17101807a00a00d09829041c10040003100800401a5403d441031094250126009485502c1a0000208004003210125230501200704056403080b40316441c42d88441400780c031030340380315582d0f400110355082a080c490210841c01d41041c2036446a9880d0600444205003426400642038082e044200600c040e070301c884000b05110704026060040c0510300107480d4040c040c108441c1c0f24420312116074010400412071008000c2848808010801584c0002040c0e0070a880c00d48050300780e18149000d01f0706c080c045c40c3c2c030500d0184225640808940ca817145003044448041c0c2035600300400745580000010400901c2c0b040310340d0311061141c49032502c1c0c246c1030300350f18050044070f01c416410847d841c6403c0d5045610307600000c0e116a03200381d604003054044003d13002200913040c0e044400b01440c0002400c1c402c010b502 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 904731258 1250 904730008 904730027
    0x30b0f06040b180a110d020c0c09220b070e040905012003010506040603051b070c0e0709031e05011e090c05310207320f0d03020f0d0c 59
    0x44506000c0c0302849000c2203c2002a07108500c070541d1035070041001c40c101c1e98001c9041d01e040810403810050004140d1080f41c01030300c03d8400700d401c1881072421624114070b030130b940404880c030342d212440b03c050090225282c11074401031113040300c0008109028011341d412058605c0040007802081c54038030340300340600341d410138a1250b4080c070000b05400010300d9054030f0580c0c0020f0403140c240782c41c06400b28003401004d40039024903c041114071000f0031003030300201102c40c05488003908107840e00441e00140c140041c29a030412221560610000365440d54144094090030005140501c0304d08101d801450280c0408203a040342003d00d900d0710995821407842140a07651a03090301b596402405420720070000380d486140100a00840640d858202c000f020300c14801006050019550314909501400c1c00d580700792003900c103550781083c0c1100851108510491000d0905020307440892036031103a20700008030900d81c000c00e103808069108002c1d40c054031403122081c01403581310503016152002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 904732508 1250 904731258 904731271
    0x503070f0b161202071a0709180c051602030c040504050705010e120c01030c180b271509010c150608010b120616090305011505010e0a060c06020c07030b0f 68
    0x18140020030940b818120100207000ca9100d0210781d103100c000d514001d62020b0070407510698000b004940089000c0e18043c403504403a202c0c1c82d030150501400e006000d110700c803180c1d595400c00c10007022442e840815a1040490511480385080151000038240307110b6803803480d081464402088140722000078501304070354080c0c940d10840031024051000e505000f2a800600350300190000210354840e0744644401002351a00d0a0205440350065031007104990100c0400c410115000003c100a080c1270041c2501e00c00c0801c003403035501000324003130010481034100440300105081c5a01d9000e0943c56881781c3c1d100238112407134500400890b000300802d006114942d07103081c40d601c403207003822401c0041d140c44c900010292507a56100f58505031402d45507200070060012000070014200b4007a181d2220b2003481d07003054042c201000100382e0b60510001610900c017121040200706d0700004991503c0b034000b1303405659400e03a010400d141038816030000f4140c0c440304080200082d060001a030103142e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 904733758 1250 904732508 904732523
    0x120507030b01110a0209220b0c04060801050a27021b03040f120209160e061b0609030a0e01080c04122301050103020609040507020f190203010509210d090503070f 71
    0x840e0082d580da0313101800c000075042011540031814000174825484600708400703098a2250b02d0311760351400b1141c02a10300d0b1802207070109081c0055504045ca882c00350000703403510340826140191042c0c05003414400302c1001066800c614040c4411760301280d111070441d0b04003519864119040035501e0780284103121140c10b503400c01040105104c18140c200903001002011140c60711441001d9624081e4409407e10000041140041e11454041c0c07007118041c00040d080380000500705410000c000304100c415070420003840c040a0381081c0210070b04003007840c4c0401c5681c0d41d400101c00c10701c520b0b08500c00011009508a0802501d41000c0c0900c0b454214072110301107003134141c5400c0c0c4030280402035000100340800ca846061a074030a9a0000d054411100c042c01c15640c041e040504e44908503043c0040040c111003541024000e481c0c00160201c010244044040c141c1004141c00400b0030024140000e000c14010b07401350032600032150040c0a607507403401e10f841c25000301c50002d14126800b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 904735008 1250 904733758 904733777
    0x203150c040311040b0a060810051e01030c0c02060d0b0102030408010905011b0e1c02061e0309010c0503010f0e04021504080610141e04091e05060f0403050d0507120507030b01 77
    0x90030280170b10084428080d0004481c00d0800c1c80940b0040d078020b19648a1444090000600703a5810598106a10801a003e154407044000041c29141080641c2d403c4c008911000d80040e21284100c6180c2211a1030028400b0003440040f4214446c035031113001e056081040d550180401036010b00a841103000d400c0e45c038025020825584020811420340d84241000304401842031504102403503548002e111503d0300a01d111207010800d542001c200c070059010040059045092080b940030045034100035055600d0044803000a00b840d00403119801d02c4c00b0080b500315103a079103014240d0030000c12440e031515101d4110694a21046440d040d41c40510b480001d10040c0f5040800045000944040c8060f456601c030f05000004c1d80311410780040c0d54248407408240e01c04818900501310300d043e15407544141c10300c035180c240040c02d41d8500340d07e1403060000081d009030440d001c0c862840030205031580d0b2a42d0075154401d0341ca07a42c1e88064240020042d20a40c543d00c8082070348400d80724031984 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 904736258 1250 904735008 904735043
    0x909110d0e0d09031b08100b010e010309080904240e04020a06080717040c090606030b040e0304081903120606080717011503090203030405060a0c06050603060408070f0203150c0403 79
    0x241c48400c1c1c0e41501081c0302403802e20110700200c040701d1510301c1d002c401c45441035460f0b84c21b6286c1000040b201c2809569004131444175079114514488a40302440c05120440807625084440d00c0340742e071000d01c01c5a540c40d0201550085004050b00d00001c1004030000710760b1891425803250084404a2150302485070104d0304070f000342c0e02540148555590840d01d515124040c100350300e070103003050702d180100d0400000d0074035143c001e0a014006695010891990b000d0600040e1405c181c0303141d445400c10b000901c126140014450400b8000e240031514185040c1420b4620320340d44c0713483c40e181e50304042c0d010658070b420042d40b50064207644e03101c4031008800342c28212448800c1c00790301d400c0303406c010302caca00e6082c4aa08104103007800142500d1425a8400c00140b40d03510030500140030849410b03c4c02e0a22413548141680b000d01a00600424a0b0955510010b4450a80000c11800e40000c200c002c0d502c0421101c01002e40c2c2d00841c00e0f107402c4c21640003002b42c00c0380c0700c21500411404a90510b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 904737508 1250 904736258 904736263
    0x209090d080915040204090201090509090c01030b0d030f1b060516111b0f010314010e181f0e01020c0601170d0c0c26191e0c14010909110d0e 62
    0x20143c90400390301c211501c41d64200009494044000e90402502040110301940e403001c8550181107100020980e01c04107500250640f1150b0340f4662080c661481c0d2140401e4100300007071101c006900e00440c0c40f450400d4040c0e1b00c02c2d813000b4082e044510706010000074002543c00400703507041c1ca0312035200b0340516400440e501e41c2030010740741e0440c101854220045c2055000119082c405060200702040c08414424003070501364001c0c03045503541402d12945040d045041103010780c00c500901040c40c0d00403424400c42c24480003070307011180d458400b101035000c02e5054800c0004058141c92241d690b070f04450704c0744401d120b800591805071910345a0410702179641081313002d45c00800300760700702e1070440205804004500010f8024004815001c2170791814400f01d02c0040340c110701803180d40c0c400e045c0b840a51480c00041102e00f00750101da40c1c04100040011411924120491403545080310300488202c906070740180d0b50a400c18100d1107210f8a031801804038500e45842c1080230903140e501941c1e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 904738758 1250 904737508 904737523
    0x1216050a170a03081504090605041b08031c09060e06061203090d0b07031b1e03060602061f12080c0d0504030f0308041e03020607031b091707030209090d0809 69
    0x85241d00c100782d20000240113000f5a075000c00c41a4a040828000e036011600b074a50140088400d42d40d200704100c200002c6081d903072007480a542c085044513042000140d030f00e100c0c00e00e40195510380700c188406900e9450300110700c0d160b4881c60034881c031004081207650310032056540c2c038030580350b18520450a00317001041d01c00b0000300409800d1113035447c1c0c0326040301c00006400ca01c2055183c0b030100c003403c0031444e2030420b40382440d0b0f07032000442214019281002d404102c420101410325104203c403a81c0000d0b80791b00144403001e0484800034000d00443c0400c2c281c0d12164503000e003140800c0600040c0b0b070191050700c00b0724081c2c0d046074115100444044c0300320700005140700810140e08020078416000e0b80d900601c94240c0e10355260001c0c0801c00c2c030005075103003100180d205400300301c220740d414061280358007074030f000d940403810403c40c0181400003140034003625484c0c200b101e942905030400628000710740203050000c207400c1c843d004a849501824601e0007061801000c5a40b0b10700005030407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 904740008 1250 904738758 904738799
    0xa06020a110d030e0d05030a2408060906011d060a0816080c090717090a0c09050a1a060a030e120c01090c150c02060a03020903010e07050a0803090a03060b1216050a 72
    0x3003206011248007a201c541001e84030b001025600c078809c03034001c0003621449012095034001e0389001e52801803134502d00a40100301e20300740e4104400400030344c4d06903544d5481e070300c00b1214074070b40a81d41d00c1c0204141d01c04590042c0b05c036106580c6c00c070928028101c1c0002c1070310b55084c195030450f694101170240302e203c00d0340c1e440700254004005546101c145440282c0155218054a8003001c080d02c0307040c0e03ca002d580004102c541e41d102032051100241c803c210480c844c020401c07466954210006006000300c00015090644486004440c0d400902410340e41c40300748400c00d62280150288140204200c140488582000300e00209141ca1b00003151404181c95550b0118100269424015550008494441815001d000054840d9001c0c001d403241d46603688010714a07245008100600880694090001c81e04100450701d41c607190158000f050300d400c12004a41070303005c0c8020070100703c07000d100300d8024090100745806096800141400b00c440031a2000301c01134459000d100c500d40d0404c00d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 904741258 1250 904740008 904740013
    0x1b0f1d0103050c270405030a03060510021b01050d3e091504150c06180f020f03070b0309030706110412030c030210021b150c040608090a06020a110d030e 67
    0x724400c502c2d01d801c603104900d10086403032036984810766813040c4940040d0381c00c581d140c20100301180c8031030b030511171b4400511084420070b400612514020b500c8890200061071031100350080031015074014800c403841614110804c01856030502e000404802c0c0071044a20204100c8c116001450505416101c41800d1020141d20709100c0c6003c103c030380208202c42110429090000284500e02031540416030005511000f210119614005048810034001c41a6034104c11404602007401e0300039003240e0039810f84200104151540000e89004520303840720205800000c02c000c14100c0c080042d1022912546091103a400f4641d061250381c0200d000702129090f5014026002c030380b1a000b100f4001e8000d0064a07020303003410103d00283da008400610860022940e886088801040310300c1a5400180b03c3d460350741803c00409105102e24415001001600c401144907000184089461170303501000c110358618601d800030f403020a43ca851250f0300d0080000e940b01282c00b17406200e8510011001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 904742508 1250 904741258 904741273
    0xc1f05100f060c15060909060b100c020607050c0a0320011d3001020a0e03070b07261204031806140f071502070b070306050303070f1b0f1d010305 64
    0x1e0850f0005200b20094540e903880d0166418000c1003445110054220781c0004900350500d42403103001d8403c90000380b8062440520144580342d41700b80b14100d095030450307540741e4a0101d803d04a150884039400e071540101c142c2d40c00800c01c20740d401e400320100761102c08400b0361102580199a80e01c08440001c1030480008600c520710310b40f600c032000d915131545120102ca110b5511a40592011070603e078a0709a50002d41c00300305a41080c810803190304100c000f014124248190501203001d6100f004000f0000d802c52703c0c54080e080c0380701e05800301450350070b2501c0710010355008024203020350341a804600b50843c4000b410440315801070030345000382c0700d8104020199002c103845038414500c94411300d400780300d608001a002c1900e40032108680f10017589411081c10800d210040180640d0281460a50100016240441500d26407a08038541035a80011400c2900c141e0780160345046a590a0940200c0c0c410786035410b280c25220b0300c901c003080000c040908070b84590402e0101130460b50040c1c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 904743758 1250 904742508 904742519
    0x61b070203150601020f150a0f0501180914030f0d0e03092803051e010506031b010507021804150507021f0c09050a0b042c07140c1f05100f 61
    0x5241ea0001010710485010141d5070000504004c4c4e244424000b0703c0305c460030b0000300d01076070090059527030b00c82004024035450503052200406da6840314040d555100c685010a0103002c45200400b0714401096903981c1d289101c0c9003209501401000c40920704e020020050440000190b4580744001341407a1800d0300c0c1060311050803000c455031400c0801e41c27840c000c000200b0078401c0821500c411100c114080104948840c01d4030030091030b42c1d000b45d200d510821342c4200d001d004122010400c0c20300741e54848a0340085200e06410003501c140b0342c600c000078401044034402204080740c9080d0381c00c01c03071070f1222102284c0340d14001c8545a104c50b01c0d45440e2202d1800b0b40c0c0f2481d600c2c03545081008001e59221f0200d0103c00b001d83c0020b005010214040000a03030780100d5000203148144c0c84009128a6103040740032010103000d00c01044002003913044419165411110030400000c11104e000181621005d442043c4e1040000c00c04d0611011503036890f141d807165402d940020440c00c002c1410030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 904745008 1250 904743758 904743793
    0x40b0f04050c03010c0201050f090f0d0f0e060a1d04180813170307030908060403122f07030e09090d050c0c3a0804050103020706090b09061b070203 65
    0x14105a40720b01441d120621250707070910400d0081c2e0810703000450346207802d000368a1001030040500d581c603084000d07498500c0102140303d010302d4406040954455030b0000049031049507042545400c00400907068070000d03000500c140d802d80007026003000e00074400701888151950075100d0940404c0d5100723060001030004e0081c00600b0300d03c641083c91141d48481c40003207079524490005040d000001d040062550102c804809811500700030060303800c2a41d00144400400c49920401d20b41e81c202d04140242d5140c2890080443c01c91402013540480036460400d40c40b0000440120350070020000280c204503002922409844002d0b040b0100180700a4619038400a08000305018011075141c0303981d103d20f692090000f000c47c21800aa5410710024000d5a04154044145d03901150031800030380c400303080b103007665404e2a02603107e440c1840d04034060907210200a1501c41c0b0441003088900b4001001072140980814444500c00c80291a20f132602c40c1d00f00103505600243c1000301c600902c0d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 904746258 1250 904745008 904745011
    0x2070e0c16021c0212010204051e030a02150c010c140403060c0203070c03080301050112090f03031a0d08030708011a09150d021809061206040b13080c011b08040b0f 72
    0x16509003850625070350700286607100b00001501544070010f16010035400c1c001008000c40d50000021440c141c10280010b03085c849a107100700c034083c0c0d0141e241103507480030f202080e031541d030103895400c1142c0e560f83d61000ca0340061008801030362804c800c44190314441d1003480e10400d454045646094199182c4c1000340c0340443c50001544400c000c01070001702d13003482c0d50340154041c80c003c540360350401000529568540e205d4182107410b0a03011404130308170041c0f040c105681424000b03202048074842c0ca00000e40020420340c00444054550144080900114815103003039440c0101a07803983c0320b80c05540100089880800c20074002d00b40035081c0a8015403603481042d04c02c0b070410140c41c0781d49e026688400c006100c5500305600750001404c0030401c150300030038104c9100c00b89809181d0b6050380c1c1c05000348043c0403402c0c901d003c00e04542104400040f044c3e000126260f540380f0450215000c0c0069800c0a0150032405213242c903518841c500d03071801154000e644003083d845442003070082410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 904747508 1250 904746258 904746277
    0xd0506040f1e11090a06050a0e060a1b021c05030c06061f0e040b1c02010914030d0c060b1009081c090501030209030c030102040f05041a031203180d170702070e0c 71
    0x1c00700113a01850341c2e00d04400e0b0050a0a0355069030704c04201800034100c0e203000c16011302034401032000c1d07004140c000e910304450408118042468004a0001510848030f2120031080f500180e060041401808801012403600b01d90895110b52107603014030800711010b0b1034000b00ca0f480c020368640c5c018402c3c0308001007400d0040c40800c1a03003400c070015044040300058200072515034541d4a0840d41c220204400504122100c03003419014900031a84812220080b601009085e4045030200802c2e54058070101070003619510700401c2c89400503000441a00481c003c920034001d00c1040c0c1c03107140500181d8030499544203240a480c010064020b034110f85072041e850f0107151040c09003602d003480038000a10002d8815055540b9180c2408210340c05805080c41210550f8900c20a0740c030006820200882c1640d4000c1d91f075070b9441030120511031800e800d99640e026030640b040c1010751000c100c41e04e840100c010760303661352034070007069903199443c0c07180c040001900f200142400b8041c4000d404c9440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 904748758 1250 904747508 904747541
    0x90209060f031e161211040b100c0302191b08030a05120411100f090503010212041212181208060f090702012711030a1518080d0506040f1e 61
    0xa00750103130b1820b81591074110b9040343c1151880002885110040c41c3d01788041902d04205003445903012580c0710000c0c10f400028442c090184c101010302c00c000c0a070643e031071101d20032202ca1540c585940c030704007001e0b0354903540c81e620440070504c2c00b4040225017901c50943c07070301442c140030418016060b940040080d038840760561204055501c0300500c0071206c010340d9a0350b042c881e199110140091805800c4240079031f20601101c505200203c40c071580140d0000c5091101400b440c030308039541c00c0700c0c802d02d41e107643c180141c8a0320481c41081140a00340b040f800095078036164101112514030440340c4951001000721228060304010311945e4101100740300102d20541d01442206406401091503d5007101c003800c042c0904c4041240b0b11002c2c0d0084014044c0000607807661a01d000100101c0005156a54602d0400454040248020790750100705a61150f10101c40c00d401807100312030090246041108000602d145449a200340302c10080040f400300106400200c0103005c1120b2001d541c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 904750008 1250 904748758 904748773
    0x82d04051908030319060b07150e011b0201050a1a090601121d0a0c0906080303070807211a040c020d05030604020d05010e0103060e0724020a15090209060f031e 70
    0x450050009511401005000d0b00100005c400c1030320843d90240d00180800e4024000c5074009070764443c04201b401491040800d030b0101d50301c2001c0c0105a184041600c0c101440700103010700350190000c5201b172454000401c03071030122030320301c01c260303012a108158010401b80005e1015806940a140300308140d2400185100200e0365680c840c2e4503141840141e50302580c201070030895201500b0000e00854142406254603004104e5a00d00003e4805024400b600000806161003520582800401c00118000c07802d41c000140c00140720000d20400440455462011681840d020300010040182e00520300c10030301031070403175098002910255102c3c1c0c0070015040030f188240281d0f40a0041c4183c2514254950318080f0101d480b48410b880c06a0850b240810000740ba254108850b1010340c80600701e0340344190740c00c80c140259100000c000320004401c0c1840d61080c1d90050440510a9801e5400d075210381042150301061105003e074140d0100550030441214066008032510b00c280484011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 904751258 1250 904750008 904750019
    0x2b110a080409060f050301020702100c0311070f0819051f0608030d020c24010b0313050105010f050f03010b150c031201150305011d01050603180a082d040519 69
    0x40354410742c0030030000398440c5400d11907040f48a01060050208400851404402d43c1c041760703e030005081c01d40c060000c4812400249401118032000940584060710303da251a00700111a8071102c3c0208002445142c08400d072480f00c0c102c65210250b0404000d04500742c212241e819400710803030006413120703280c403c000340c6980100003415200ca010000943c807501031902c8030746490003030301c40b420600d02030703050200c146200c515900c1c0c103480756a000640d8940c1c40240b80344400d400d500000b0f0a56180000008e0050038a6200000743c5100300e03600780d01500458101030aa6040180459004501246249031062010020441350081400b0703a41408036114029243c500260302c12041000100261245a036151052601509a130380e180e058410381645480860034050107002c0c01170354000049001e84000103001d100d25203802d412034107019120303d40340c10250011400c2e20030f100d200d5000b49121102c54142d10710407805014201d81400d24081c10030060370344140d00004200a081c82c04a038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 904752508 1250 904751258 904751273
    0x130f0b0c071703040b102907080c070f051e0909330c030c030f04021c1b08010506151608041e060e010e0d05011116052b110a 55
    0x350b240e80c0225a07124501070800c0d0b00360410041c40501c520070400f00c148071002c0d081042d498a003030200b01b592001144005482c983e80f042e208054400344010605442160000441405480c0c5a151002d000da50302d01c140003031083c5c80c6000c0303076200e81c0c9200c0d4800c0740c0c00e000b0f8200e5449001541101c120403100e480011000b07400d0f0400c5103501008410104103804884842604034602000d01803651400000f0301c1d40383c0c000030344000d800444080100e015036071180b070b031180e0341c00b00e042c80070400c0030640c641113003034041050789000024403200700020340403010301c10b00b481024041d2100741d1024131038a0050403035003c007400551440242c544c11020800c0c5802a00c040c00c440020340584118140f0300c1c0040801d1035102c01d013002102400d54180da640300000064140040d80c074000d44001c0d501c8c009002d4940b40c00032544489020941000b200d40306180c1404a40c0110141d03840455106091840d070401204005844a4850000d564440c410102490300010800030781e0444400355841340c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 904753758 1250 904752508 904752533
    0xe120d0b040e390904030513060f0c26030108030706180f0312020f0301150e040c2003041802070b090a0f030f022a040b060403020f2b0c030308130f0b0c07 68
    0x70700082c0301080b03280a40b111400c08001912080c1030174ac2c900e000701070004004019540008000400d0000e01c42c040340100747d90f200c50900d2640c907040d00c03582c565804690f21742200b00240da4043c2011200e0305691750840750500d803143c0004040048180c981ca05030307140e10001c020350b1803496080214242c03448042010794040d0501600ca05841540104010650342a4010051049e40742c8884156940d401414660b444042e0828001c0c808440348402400e5014540c0500c1384904588641c070204001540200b4110384241c550361526154a03000c00d070703110f480000040c80c000c4001c5503600803900810071811101054030488100c40000d581c0c21196030390700003042c1c4c0c0c98007036a0f19034041803030180124200070320b041d5240f0f400c02c4d20319000501c04590240c0c15034001c0600d65208002880d00340e0185200b82c0d2010041c032020000d03460125410f00640c0b0003600003d0400020880c41014042000040e80d084400400d6811040c0c0344c03917442440103404c101207240100140c4000540a82818 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 904755008 1250 904753758 904753763
    0x6060306060705031926090c130e0703050604020103061509030809060d1d06010618050f010903050a030c0203060c0f03060f01021c03150504020307050d0e120d0b040e390904 76
    0x1000c0070451070000045069120303040a8840c0e0b03007401c021f641c03130b0b001486502d00c10040751030390340068080880740700800c899510030446000389440402400b03030015038036008a2003070380d003040315540e10060344c1900d600f04154140010740e44041007010400c43d0010f8a100200201151714000707a000e117000407625603e1203145030f400c41c0c440c0a040710005000351401846d42e803c001c1002030a82c400030302c1811007405114440c0e200c055040381d103a48a145408059030344081241c801441904016000006101c0c1c00c03446840b03182d0000700d2403103682007560741d5003280502ca142580c540404000e08004000c00c1d6904510440c06808a0701e04280300d0680044165280001e00a1505032031b4645590b807900007502481c0100b0621000503403010884100300c0090b4000105018400c5c0d01e1828050340380080c42020340041141154814140e2110f1601c10048804001021014900946560451001d10440a86645460301441c418600c0b5003130303900c0e083d108414401030a0001800c100054405 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 904756258 1250 904755008 904755017
    0x18070309060c110c0613081905190308220602040b09040f09030c0f0501020c01092405040b0105100c0f030e03160e15010e121b0405060603060607050319 67
    0x40061081c40e00c5002039545003864031400c01d00c100c00c1c16942c1c88441082e11400780000059900a4049000100f0302507c181026650070081d51004030304403841c0a9425030359801600541c03038050303411294011000ea410385915615540740051030b1041000f088400b101c61204190007800030b142071004001916445a180d610342443c2d01c140411900d4004070a41540d1038107a0f080c020039004800842110303130019801032261100c1c9066406170003445034440c40c66080101d4503040001040303a800100c40751030714000140720001d02010641308107940140440034114010f0100c1c1c18850369501021545082c1003445d0802a80e5a00c10b80160700c1c0c080c0c00180d010543c3da110340c60300384030226440a2414001c401d69050018810a18101401c0980c01012112000e240ca900039543ca10035032400610300145510310310325054070750900d00c4c5120900403d54404c5181442c5c00d1050320300660f070107800a4207503a1242d06124003540000021b80305880305015480c1c1c6030300c81c2081c0802d40140c5070345 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 904757508 1250 904756258 904756271
    0x1021303200402031312020a17030115030507140a0e0603010e0604051311091806090f0c0a0b0d02030c09130f0b0d0b0f06010e04060605040e0c0702060307080402180703 74
    0x2414031010160700610441c0108148800601035070141288250080b080700e1000b6202d4100340d28000b00b070200241012103455000403261007210146040350002c0c21000f4052a101c0b80840481d6000c454400103e11548601698010840040d092855090419090120301036000901c036820903400706400340f0354803040000c1d5040074003420790401e400ea00e580c4034801300c0f03a4428510000c9030000714020315991001490300441c030307401c1e0308806441c44140d441c01c2c200605519240c0a10b10110407141c45204030402407420b150140400700c42820300401e0030b040b070340214071010b50320141880030182c005000c0c0400036603542840008031450148000b580c45815290030060350003044049104100c1c40a0443c0411901c0342c29a40c0a120540d4403d205d41c0e800c00145d40441b1031007295908203207400b00215429800000030300c250340c00c006110710f142e0366580740c16030301d8401c0442c02900a4012310104203494090f4a003190818401484200e64140100400380031210071200040085d84918 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 904758758 1250 904757508 904757543
    0x161b03200f07060e060417030d180c080d020309060c0c03190309060804020913060603060c0903031d06040e0a060302030d030920100e01210b0a09020310060f0201021303 74
    0xb000c140104481c0c00c2603800303031100000280c17a0b0f00991241d40703015440681003404c01d10f01401100c484035000c080070820504a032260300c07000107034988200c0303100b103c00700040b0b4a201d0004030b025500345194001c500d021131180c180003c41d042170002c0303640d5103e41c504c10740d415030302800004101c1c220b0815081c89400344e070070010266109540250188140300007404050f0b15281d000c141d20006c1150303001d203800c0c568580240245865480a060185001003503c2695071040081c0110b84c0259540075956500459864680c400720040a510030000c120411410303c46085042d4400172000340050340554070b40119081055042458001a1743d0b0171041003044020341c51f1049420b5a25840d600400000d000310f9000011000f6020034004412003d0465a122380765400d1403590820300c0020703a264925100015001c0c0000e400d2165a0781e2801090000360f510907241b2610307080400070001840e20b041942c4104c910000c01d801c41d50200880b0300300080c0e807010171000310b200d016106c07030240000c0b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 904760008 1250 904758758 904758763
    0x319110a0b0912090a050d0819090f08012a02070807080304060f030903020a17071a04120f050a08130b09071a070507050f3105161b03200f 61
    0x10702c1c041d90031500520418142d600c3e20103001d015606c050f50808030354112401d01040394041c803048258160520505225401d5014005e442255081030300d0030034031600c59034070909982400e0540510050344524041103a403000050100c1c010540c019a651603488000c03030350500006030003c811030342c400581002101c0c0c0c040003900501030781e86010008a40b0035a0020344403084004003902681c0442d040c03640c4081ca0b20202c4821540c071500d01c81c061125404400e61030b0030204c4042d0386400c80c0b5454020820300401e20311100e13840d1a40d9440c5010700201043d40d0409000c2e16103000410b610030319600103440f43c01c2c031600540f5410024603600c0d15004e88440c0011341904070f1000c0800c01e115407000100001064800d8501c12203106c44aa88024003040c204040c03440001c00341001e001602c51004050406104c414100d034205011a907281d10300e1402a64a200c2e4045c00146140c14000d03003000c1d0703a801488450712a180039460340c041500710311410220300130711503960341008010f012041c808 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 904761258 1250 904760008 904760023
    0x1202010c17090a0b040501020f0c150108011808030702150703090c0614040603020f0d1407030b010e1021020a03060602161419030807080307200319110a0b09 69
    0x321540d211626042102d540c45441e0001c0040c19044410081001c0103c00c0d0181c41c00f4011414005445002480c0615541e00a00301644034900ca1900045080300c1c060068600c03251009902207103801c0f99a96200c100d41c00184000b003140201583c0741092802c024a00d40500240c0d0790100d200d101d00d00f4400700ca407c1940c810014030a001140510180b00c5000f0b07141150b8042c140162079038980840e0001c50b08c9091005172007103207000200b41d140080045080d002d00c0b05c41e6420800484641d005640d004141c00c0b440e0fa02c4070f40d15140d0820288200780c0c140d02092140c0c581d050700d200040810069812080310a0040b0342c880034103000b280e0f81004104841030009550109451511080c5207100c040110282d001d030b110b1003192410250002114401158132454542d03586425092040260f042500e610000800000da168010304041030617208000e103aa000c0c40c41c25500008a0500740c07801d1000c0707803d120038080513401070711091000c7e4400f540100b0440380d0f40c0c90110340090420700d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 904762508 1250 904761258 904761287
    0x7020112111b1b030c0f01031b022103060112050408070c15110102030f0a0b030708100204050f0f0306190e03030f04030e010206040302060621030a091a1e07020406031202010c 77
    0x100b408010805030741c00155040c0c0c0507000c0c0c60781907400b1b03032240040380500305020f12403e900220b0050011017650000f01000c486800034005541007a01c91184142e51100b0340b1858000792030200441a078201d544d00094002e4842c010b4a840c0c002d143c0d440300d8440744250700c5020842e07000300300d4400743c41d009030301480c545104c600210324500c2d002403100d1302184090310264074076984565103400c03602c0c1041408060038807a0120317241c40710820428406907005014541c000e20071040700551904041040c0040c03064010007811140e900d10b1007071450121f0106403084620b4845681520308003003800198000d8105803214551803a2500340507000241707414440d41150310000030000441d50100e52180c0103c41100c82010110780c840060540a43e62001d20070280400281c246115800040400031100003040d0f0302074820b4008a155210b00500400b00700283c00ca00c510a07040074008018400300d8801400000c0c003d840e5299a2410b010404800d80507039541d451007140d003074122841000411 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 904763758 1250 904762508 904762543
    0xc010305010f0f030f0c080a050c011d09040b2203030f15080d0e01021608010e0f1204060e040e03040b03010e241e1905040f050c07020112111b 63
    0x51900403c03929803422032101528140a40003900d080104051480c401805a00101e449140e204e0500d1902c0340d1961a640e400b085040740c4200310051184005101003000525012295841e0b4680c4c540d41c00c0011b0241b0450303600009103086100c0c51700b8084c80e08500946c0c0029101c1d156072500c00440c0c010800c6504500c0c01d11200308070b400c00001d24411103040500e0403c00ba41d2900005078030b000700c00e450303603190b1160101d07020909620560194100007800001c40e03814200030300000c4d448501842e56000b51020800041c41070030b0203994148c41561001c2c100040900e0f03a88001ea040d500a5003200040c4000000104015803c110040341c021b40ca071940e0600182840d00c5d9035810750a403601080c0940307100002030990062070701941c00f0701035002d0036036462103020301084040036000f409501d00c124501125a03076500600e200d801e10920604541e039140030a95001991240950b0500c004501d445e80c0100100d05492000f614001d0340c0048030018004030055a0b900b04450503000e001c050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 904765008 1250 904763758 904763789
    0x70e010b04120224030c0909060f061e0702030303040c06080c120708070309020a240206060f0d080c030c07050f010516031101140903220303050405060d1d0c01030501 73
    0x14035106031801c1c402c40c3e0481d100f20b2000d0080000070200c2801150f5000b081c0d1022040001c0c0d50404402810029421903500c80036a642100700110340c042c1080d000e0700003105010070510000502440415801e98030800f0b420080283d00182c5141d200b200c0880d03010144410402003a500803d100d40c0144c0003c030001c4c10958080000350221800910100170000070101041c02c640c02079003d4400700342c01806081e002603d80354081c642c0080c9000c0b04504030901c0c0501c2c0541840400c405005510082c40989070800c248108104000c06040c2618034200401440e522010208020207882c0702e647c01a0400310305d82410010f103040c043d07241c107060150400144c001841e1001006011030303458181074560380c0c0c0502c030703050041106001f00c20700140d100d0240030501c2d200001400001c00d5103641c000c0068581c1c4c02c180840c05651200030003040042c007040c4030380d140803000f904110000d8000001c91040c0c1452400c04c60008040030446500801d07010600c40d60315000341405000e400190b068003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 904766258 1250 904765008 904765019
    0x4080d1413030f090305010f0504020102210702060d020c030301060903020307090501080d0c03030b06040e0a051602060a090f020a0b1201080708031b010b10050409060608040b07110c0909070e010b04 87
    0x51552060010308014051981024050240000c60081c582060023001300c00031908007003004000582d8268003502c03c019982c041000e2241c0d81c00342c0c4001c240c4e203890074100142d0034802160080800481c1680d001e0005082d030751020800385008040c0c1d0350f20458264903600515051a46a420001c50345040c43d0051080ca0070004450084009078907164982c0801420b08600501c1a2840301c3d42c000c0c0c000400051100c01d03a4141e9000c1c81c20300f9010071103500c4400d03e4503044400c4411640140e08a10002240c004040c1d2050182c1d078000c041180319240d6a9000500b26101c42d085510b10241c0814101c000440a55609016042c01b200034070001d410700102590702d0050030740e40c41d0301c014a400652080c20007900040d482007401741140c85540d103d8400034001f60480d000da0400c1a103002000160207110b0517200740940d03004181c40d8910f1311182000c0700c0310483c000c40d2203a40e226a1407480c1d003075100c20301c86a10030010f2a0185c4085420301034132070800d0070181c0c04030200040a00c800d118 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 904767508 1250 904766258 904766281
    0x150e0109090320070b0a0905030613121404030506040b0901050603060403020606130f02030f0412050703361502160803030c0c3316120e0102040e04080d14 68
    0x75201c0c0040c800d40b0354003501c45800b0314143c1385800015200381c0200c0c0c00e018143d0880c1041c025600700320f0984805070340d060902d40080c5107194020381804005550f5908072030045903050748059000030308524140d240d480d40c80c0340c440160360071190f4005075010005003000038410103422000c110013404050510341c070029920000a04060711581d007641e0307410b2480b10b9560080b10050098a400d40d281d10301b2040c21000124102c4040d1500d40000380f070102018419011183c1c40ca40c503485880051018400035496501e13003d1901c0300c0e207440c0e04004c0d007840c003207823003005c00420035841240c0c0b44031030b80038000f070901843c000100f5680380d030b08005005014002c4250303588111028200754841e10008290b0780750a034140303050550310b045105035002c0c92064180c00e4820044980403214103131aa0b000320f10207a1103142c081c400040c50392484410b45e0b251a002a0b0201172034000140c1016111480c081c40e40d54240c9040b9468140004c240460f00350301c0c05012440b00c0c00451080785482c01644c00c2130b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 904768758 1250 904767508 904767527
    0x108040f120c0203240c1312030507050f1020040905040812040f02031c120e1212090c06040602030d05060102211b0c0d0b090c04150e01090903 63
    0x41c03000000c07510714a806031107201c2c000c201a80082c1103801101c0c0c140c0e00445d0790070b22881d4594100307541a00041119013003804451030030008451414040d8501500c540c1000f0399a203048081004c10040310000c900c00b0401c900c01c0480410181c10380c4040303170b8001c4040358040c440384400c0b0740105c01d201c0c006e120b0b4402982c04440c070f07404003c5040e5450740303003109042c890071300008d17610040c000c1800148500310303410f04517143c400e40884180402000c0300a03001c1c0d0815401400145500d00020806051034100749540d202c640200c443c130307811214a04c0c03030540001c14041d0503031090a00b0001d443d6000c0000ea8014942510700c540b805040460094403449101190340030161254045111640708028480007440c602240d8040c030300c0b503140703a003d0641c01034441c0c510901c11480d21022a50300440c44150501e0000c00c8100b014000750b580098041c1d000b4807800c440c1c0211a200d80032610355000310301d40c126141a51841d130604040c4081081d22040e00800402e514060715003000070741005004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 904770008 1250 904768758 904768763
    0x501030b100510091206090204060f080f0114070f0212042315040e100803072a051c050f0607050901090f0b0f03090a02040e1006060212030106050a0207170303010e060108040f 77
    0x1c5400c0421b0030160090124110000d4029180c9140046c900802c00c04c040c056403040015540210104625079098800d2a0001c814420100b004100402d014466408140400d801038440b01648407c1d60a055041f076448080c1081c0042501e54a550271030195004649003111381140201540c1203c00003802180118610400c18101180041110515240c001d00620b000c0703d41d980210b1400e6801b0012107501c00c0d202500f205140c035a4800756184407800d81704060301c1400c200c1d42c8143d8803441016074140c00e0300e983c01003601d1300c0c5014000340407241c070a5465031103d554a100d800001810b0f409164403c03203004100040c01d2100303031100811101141d0b4030028a946a89604000c035041102c4030748004e500074504809680c4110700482d860141390b00021040140d03503034070300d4140d890b241803c81030707400c110f810001842041e0080d00a05034811840c41154201902c0c0c0044110901550742480010360021004211000d075050340311b40e1240c004c1c68a41914182650745d5102c200366800300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 904771258 1250 904770008 904770029
    0x13051c026c12010303020a06050f06151c0e0607140a0804030e0604080d17091207082203050a2310050a1509020702180609070c0201120501030b10051009 67
    0x900000c60700d00c064901111003003149035201d503901c0c540a90365008002085612508190009201c1048034580e14417036400980194030800d117052a000859000500d91418a102000035a00101e000e10410b240110102c00524075800c00020182401c52280042c41100e00100316003000d9a40c8041420341290703150a2820b0030080c0900017070003a00a43d04411402c0c8988084da24019a00c01044400c00c25001114100c42e1103103070089407148180c03449440c11400c208182400075014400410300040010700c5d154224038895008080e000403944140c07a01d60221f074000091248802541681c2c0b0340c1e4401c0940318070358141c03803240c444032800d203c044681d0f5180005041c500841e0410006240f4a030301c011030f05602d8901f03445c001d4014482c142d000e0508011103400c100c0302020258011000200394260035555000211388030030400c0c0f001c07810000c1c80b804800d0f52203001d004050203540f1070b00c40d901281c03900c082d491000c100c00d54001c1e80715841c2400d4025405402465a0040e5000c0c62071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 904772508 1250 904771258 904771453
    0x11209060f0b0613290f0d0b010906020d0c0c030b0403020f011416030518030307050a170723160f030305070c150b0406080d0801050913051c02 63
    0x7664808040070901c4036101c6000054019401006c08002c1920318003030402003101480c100011204c55055014103800359001c03010300009980901e0310b403d04d6511034045203011a490342d0b150240640151b904a0160f41b1500ca91142e1082c01e019145441d0700d480706508052803ea0030301a4051400f100f05000d1503600d4000c10111f0301e107950120602c02c40001105e50343c1c00d008400800507405071138004001045101100032038090581c0b1035000310450f68403041581801b1038074480d00144e1005042c12041c0070030480600d58050082880d100340100e480107080c446508000d402d42c2c0c070041c62030302040001010b940c0010f50403000c0c5840c11100c0007001581c808000042402881203811111851040a152810302980203a8050503150103442c0140545c80300c00210502c1e411100009025800c608503022501c1c00b0145610544921841100c00301d040d44c0c01c002d071000c03001125101c000e58608c50340080b2120007500ba60805004405141c40a200c40e400b40450500401c4640141c43c11000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 904773758 1250 904772508 904772549
    0x80604030801150512100518090604020622030803010e0901051e090109050303010e040c060906021f2705190b010515070203030406110118030c02010e011209060f0b0613 74
    0x3c29030310809110180d4040390b00f0001b5903d01e6140722881900c0c440e4140c48180310001d5100c100d0907001d08503000080c103280d102e9034204030b1305402115005800404000d254001151618044001180100002542c0317504005001603110001450703016140c2c1400f090040b180d010a1020100c0040ca112210306a159185941e002d041d41c2080030b0700c1c1c0d10001c0300104020030f100c445075004500c0b0701510100c0740c1e940c00c015100503500303108080260f0001505104040c00c520040004100b40000c000f8000787c1c0041804c2c01c465446000f94407a0b00c81c2c4c00741c0410490200400910003a00921440e11040c0036680d0341c1400c507050180e6809040700c190507a010412900030344000942c0201525207503a21404010501c801100304055558244290001c00303000701c24850101e160155140510b0741c040381c0043d0747d107590001a00381000b40460078040e03d18403510071003810500c200c8011428903000241c460a6900c04810702c1c2c49188108800040010545100021200c1c6d1100d41c0d04000503d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 904775008 1250 904773758 904773767
    0x40f110702221d0c030c01020d0507080904020d090614010506070f0606120b04211d0a0801110703030f0b220b060301090b033c1011090a08060403080115 67
    0x254090910b550400b25403c1c040000400c6001c3c80700129422200b40550410406a4900c81c0100903805078001078003160342c041c802c400130141c0c01c0c010300d61140742284203808071701203a100d6040511060b9403011081c0c1000518000d5a0803400b00040d60140303541800d001644610601a00030200d09076650a5001c02000d40c10040c0100f00548074046040260f0820880c6800221000c441444811802000a0b01490f001c048024070366502d560302503500c07001c00c0d101d10103600406a400120f4020018520348240120500407603030141e0203403102e006e4500603068070405044030b05030a0400b0041b408603228203003035190101c0480103554003400d50041050040403030a07035542d00010000004035402d6841d03040004c00d410103400f00c0700d0b090303084c485040c20201103803441c2d1800c1c0b210030074002100050180342007511041d9400d1318654000304110b841225040c2d84820b42e00301e404501c2d8101450302c004005d00504c000310250503036152555009298401c14090360281189ca04c00c80c6210b107106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 904776258 1250 904775008 904775059
    0x50f06030607030b130629040e0402060705010905120c0d050c030d09030909151505160b0c13081605220f060302090f0a0b06130b1b150105040f110702 66
    0x840c5c40c100038a903100e08102c804024081114454401000b5071010005c0a0074200e50496130300300ca00c000381d51070355270030048640d2203603405070307465929030141102290003848024605a01004034a46d14200e140c40c0c98100760340c2610003401d001003807290800054002c021102500c0c10040d0020701f1100700c0c602174402ca0b03803a400110b007142c80e01c11050701c1498460700700004d440724130360400c00381020544201c80c58824901e22850f0308901f03440307010000308a882c180e030f00001e9070300501c1e05081100d0b201c0c0c50410075a62018240e82d00081005201142800542d0b01401040c2c3e490440d079441d0140540d640300c40c4000780000956a00340c10600140745900807405503900511000050502030440c82c0a0f00c02920100441464003080c07681a18001c41143c0801d400030b102c0f0714190340303082501c1e40c0e290080c900354009428800c4801003400c2003071001240c00c3c240c0d2030301440c3c030394182018032003243c00d0440d000408070300d020303010550000c42e2003d84006640c1200e0551440003400810341c000d521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 904777508 1250 904776258 904776289
    0x21c0915030e100b06070f02130c050d1b020607140906040b0a020709020301081902120a0b0f07020a150b0d0602040609092906030c0c12030406050f06030607030b 71
    0xa42051201180e41c1078100380401c40310401254621000501c0c0b01084849a09905900c0300041010074006104031000308052030004024407002c500c0d205030101a6202040c2d041e0019000255803c5042c8bc540b00d0b10401c421007403010301010005100c060350b501405410305040c082c19401f00b030300340007400080703900c1c1240142031540c88070703a640c1074140e4641056500e480940291030f00420625940d2007600c0c129480c401c000c10150050f21020070320310001201c166004001e5551500540408212000a99206016010b8a890b003501d000c1c2c1201c2004d0301200864001c1d4986a0100d03180c04080d10001c84c1032440090002803180004001e0911803a00500040c00031800084003504500400121944000d090203000200c1000100720f5924100a9a4082861504405900748030000e140e20800d08080d0a2511000c054410f203048580310468441180020410041140c603004481d00501d090082ca8030505040c0c000944802c0000c040204040c0d80b00101410381c0c0d07800c0e42c860359000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 904778758 1250 904777508 904777529
    0x1091d01021905032e091406060412080412080909090318012a05060919080a08071112030613050915100f0807030311030f0403060f020d0c030b01110c01021c09 70
    0x401e445c034600d0070994038868109094980b039402c11135800c54464961181200900d0039180604240160002c8088a10140d130220001c2c0b00201c1c18141d8cc161102c021030180171f41d5a02c4849500401c20302c958014000fa1082e0000d0110340d46105140d00003d000442c242080d84600c50440a401e20201d10b000722000c80481d0800368800b44500840c0c10f034081c103e00000d035090600e0395000c4404000380360100919080040041e10841c03032191100c1600b040061400300130040008100b145001e000d4801c4480c2a04000188032040c906283e511660341d001500074070181c940110469180c5039050040c45c406020740e40007420301d824885070701014100700900c00000302c0e00c1d48407181e541c4855010842c041850076820700c1c2c1e0788900000b03a848200c02810164500f0381142e448501030105c0c6072959140079024404c03d07800300307401e0042640700042980c002030012140400146402103004c01c15046400559424141741d038040360030300c150482002d40c440700b00c040c10021200301074036074082004007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 904780008 1250 904778758 904778821
    0x180a2307080105010224040615121b09090206180303130e150d0c1536052413030f050307030221032d01091d0102190503 53
    0x1240c10018203416070750f0a03800c60b004c15a8440c160300d1846402c08081c017800c81c1290000e40060819001211300d080560320310100c803991800160003100070440211407442d000c802c450800640403d08000801c03400780144200e041c9600840c0a62050308650b403170124941402c5101510200121403c000740c00030301d03442241d1348080c0301c02d82c8013080d20340c200304d600740005408491400c108401800364004c1c81c00c2c041c3d6860101070300c079120640c429410038060501041441c003000c0040761002c81200101c01102000da0005180340506550851481a1042c1c000b229094400102c012030150100703c41d00e035a0051a4000c41a030f03c1254001007010b50020640020440088058090315109130200d038010002d440700702d113928001e5501031003030001c00e100045a5a49090a040e00d4101c180c403000b83c82d2900c51890700031201e0980218a00d15151803004090301080c01445c400c00034120021820b106001d91001100c2081507520400c00c200440480c0389460048402e040c01498031401c1c5985 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 904781258 1250 904780008 904780021
    0x30f09080c071823091002040e090606011103041412030d06030203060f130326070305160c020f280905041e1713050d050106080c180a23 60
    0x480650380030b8140058841007100b14509590300401d40001320130041030080b030035041c3c0c0d241c100000c0180011414843d140c6d962000c0d031010310003080074002105086103a4034010b001d483c500800902191f04004107801c0011300c16a020080c0c0d8107070f402425031140310b9280840024075548445c07043c0c0e039003400002035580f11204154405000c6134426000d0700c01c156981d0050104030f1500311003d0384501b62050310b440000348150790007646000448800444154076030820741d61404116900c40100b603456040c0241c0c164130210303099144010f85010244020755501141c00c0b202d050301018055609400c00b100521503480d07054940042c1d61044040d240d64401e500c0c4054a0155015a54175068166100c00038191141511207103401c4404056024a94900c1c058103510050403042249503003240421303950b8504031015440b5000b02c0000c6580b6051251a030b04040011000340d10543d040ca0f003400c1100250120254003040105001071410210000300e44d0342447c280406481c04541000c0200d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 904782508 1250 904781258 904781263
    0x1c060302030606120303060108060111100e100207030905060a030221040c14030a020108180f0709060b0a1209020103090f0602030a0b01050313021e0d20010c12030f09080c 75
    0x1124021400c03203180e038462606100d0f030b01c201c101c1320a00c1504200001001940194000c980154040c9001d50b1b0804950001d2800e0044401030031503c01c3e100e031000740d51414100303c1c0341c0c01c040c40200214900f0640760b40c060080000b0344960390180704080b40300301401c0e00a605903000e42c0f603541c2d008011081144400113400100711011500882c009101180070301002e80c2410045201030f0080c4030b842e40a40040d03804c14801004032518001c1c00c28a0132b0100c030306100981c10103040313a00a000711414046070344103842c00c60300980e11070300c3c0c00c0c00404819070f4441181600840c0d600c8000a5105280c00101c3c0070741010302d0040d01c000000d080d810100180d43c0d00542c4900c05e03890b01042081040b10044810388416aa4800352105889000c4050b140500c40c4101a00901c80c4880c0300100e180c0108948040500050700c410380c01e034a2a518440d05c6c3c4114408030103013442d021403011029542c00b000101034600d80b81c00c160380c81e0080c00074035011354010344103560812055a15003541400459 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 904783758 1250 904782508 904782521
    0x612010602061603020a0e04050a0b220b0303070b070513244509060e070206130201022d0f160503011505040213032a0611060406050c1c 60
    0x22a441c0a8540f00c08610b10030702c02d450340c0103001e40e0f641000803496070812028000c00b8015061040d07650000e0f1956907500100a400440c00e44154181303034108580c85c0b42158000040700b4001e0300208800000200003555950744040e1505041e0b44071500f0110401c1101099041100203014109043c01c8810030700d02509a82043c9a8a92416006482440084a00c421400c0c091b03240750031080200b114400041c160703080a10751382c4e50b54050380c50030044d09540c0c142c0d100050151140301403001d030039414000d1a62141c1d00e080d02410050352540005d50341c410b001c03075905014410081413010300100c1018100b0000c2010215020541e0f0300098544640343c000c214000e02c1081200010141010b0040b20400e5820910702c5203c2131034581800080c0d0300c4591200e04503550000048001040103060407800d842c00c0c5003112444024003035108140b0181e42060081c4036080e0b481000c8814001a800d51065000c940460261600b0f0707000072060055905448000060208807600c004c104d81c03010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 904785008 1250 904783758 904783771
    0x4030c060c0309110105270d061401050a050a030c0312030905061005030618030f0a0212030c2101050d03121506020619060f1211060c1c0311070b0402061201060206 72
    0x524116100c4e0041d690780c45400a6421403103141140c0340c44018030000c00c0780c0c00c8100500f20380c3c520f1425660300c404170742e011a081404200802c0c014001410705854602c0540401d50344510140d0454403400945003003444010303e00d078000947c2d401064843c2e008080115440030840e25982070500b20310341c013801d1034041c0034000d10070100050702081c00c6003103480703400201c040514605012090691815480700080c54258424080b41c44002c3c40c03407000a610a080c503a00840c1c44101e8000310301c40c2d8180c242524006400100c005002c46e0759000f1070000c803180d1506001802540d035460101c054280040e044000071340c0b584d80051080c2e00429500e10820100380380c56011400041c0d00340031990316010306210104e66010900c43d1391025001100214001d0783c0c0c6035518981c1c3c400190381c1d940000c0c40c200c426000224042024201882400300c1138179642401d001d1000c10600b000440d00a0030310190000150702c02240a545482c000c40f40580e4508a01201540e190600a540c801c01510b55 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 904786258 1250 904785008 904785023
    0x2030901020c01030606170603030f131401020c06040504020c010e190308060301053709060902010f020601030b0a02070f050d030b190509010b0306040f1a03071a07030804030c060c0309 81
    0x400c2c256210b0b1141d8429619203440c1e03100d02c10201d4546e696580002007085415100400255100c48070b440042c1a210848145595802d801c0516070900700c0d0301a00d940c0c0c10b5502090501506507074000c01e07030342500e01c1070b40e0050b241d0700320150641c05081500004106402800c9881403039a4149a007044070728041c2c3c0ba03248864561700306150032607038101c03039988503012004a1801c8001c1058481c1c0c0842c10f4040f1100b90012820140800f191680720007203030401c1e60b40818a045581040380341c890098540040e104562640c3c90341c00b0400d800a1047c510f40d64005060307810408901034485000d85c21804956846081c050068010700507041d02c0c4d845068020300b2045204000c1e0dd840099a030060110400d41c3d2030301890148075040904440d501c503440705840c003c904140d02c24200300312a804015004400b00c10145810000250405001c40d56043d04400c400e0751064111620540d2500c0e040e18a9a501d0400310b500820300700300104007d0170105101c403126803503000904120300a090 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 904787508 1250 904786258 904786273
    0xf041e0605151e09130506010605040306110a0915140315030601050904080703120b060d09110d02011e0e09130308070806091501140d02121003201c030203090102 71
    0xc001003da0b03425501e0a21080c9080d04000c00d0a00010050304449074020240e0580502c0d55040c0c10910240c00050004101042c00c1043c0103150090081c249812001c440c500850a04018031391303042c6011744101309030200c18141284d0300c1030083e0110081c146c41410f03141d00f0304010101a0401c00000b6521a100700000070800d03282014945020b20351001205103803a030307240e40944500c8680c00b80818429580c1c0054596500d882c001842c00388600007001545800501c0c00409404400481d240201c100c0840c20300180d8000c44460000c00da107110700c00319419227100480e07070001c0814034240c0100c03060041c0038044944842c10b110440c420345609289a035801d00441d2240d608840c45e545c002c442d07201064614800110b140000351043c903100d80f5030003c040c01505075500c03803003c0e400c0d51a40010301c850714042c2c0242c0707241c00c03038809032910181c145182c0320f8801460325004202d035134104a0418941a5507200703c8800d18490445982d800c0700c9880c14041e403681c04c0000010f0160140d80d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 904788758 1250 904787508 904787551
    0x10e0c040608100e0a02040906050612010b03031b030f0f0a14090d0b09070314070f140a0618080a06061805040c120609050106030c06021e060f041e0605 67
    0x191002d0303070a030b080180005441c101c94480501284d840c6a000d6000e00c05081001d600c40307008001c81d80c2d01071b0702e0101d420b00f009424030040461071042480142d140a16421803a607001c41150b507140c20030030440307501c41d0309c2d40303141d80c1103108921950350b00c82c200003045540c540090010b450040d4035610f640b00c60071240b9141440d41e2059250041d44262924002c00000e60b0003c0113a411024600c1120390407034aa070f0303448115244080d00100d1650083c1d108125040801510300040c00c4000d41103115441c0b550b003ca111404240a4442800110015104692040718000000b400100101c0d5000715031030a1140041070203003e40854a038108002e44900c82c02c0d03008281c01298003189000e1007515000219241004000c801c0b03840c0781d02e46c0c480001003202401202c000e1401881074007001c502c0d2a002902d0b181d0820350b94090100d010000c07401224003c500c25600c080940410507e581d164503100c005148030001f07240d030310b0310134205280601a40360300c801e1040c203d02074608030708160709 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 904790008 1250 904788758 904788761
    0x80615040819032304030f1a07110c040204180507110a0c0f170705010324030b060109050909070e040206040509090d0206150306130206070209040312051e041202030d0e010e0c04 78
    0x1342c0090190342010001000002c0407180039100d16405146000502000d81904003146002a566000012031050040c91104000d101c908114a001c6404502e091b1a040001041c0c000d544000b42c00c031a51100021422130007203811402c07011130f201c140c418051403458203100c1114140078003940701801e49001301d8010219000070000d0310002c0010b00090340f4210045011300300441c0a2089030000804521415150801407000740d03109018a680c40d180c50000144a00c4003503000340c3c42441107009102c182d03036000c90100181d405000c40e050031903880b8004500c5138402e030340c040c3d03402c068088100407030000080b4504029000039400d8403210341360440c01c0f4942500110859500d0b410000c0071402c10b0803162400800a0b101501c09030a01480350001480442c0866040d40812040c00b4481c403c6442486100c0c1c1c4200c04813007181000028119400d4054002000280003506422a083d800f80c0208255450203100d54018402d00c04503100940c06000c50000344051031003001030000b41840c06 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 904791258 1250 904790008 904790057
    0xd030f1d0603160e1e030f06070c1101050f0d0b011106060105041811070c03030f03060b09040207030e120a230c1003020903070608180d08061504081903 67
    0x1c0c121425500d80034030218407145a4001075040c4003907580320b8000d42d100c0b003400c4440b807624900011808444641810b041c10030040b28030043e50061801c0245180c6c00c40e0100c510b840d004040042e8488180700166182c0c455440300101014010a84000206498000081e00c003c2a611501181d01c5080e540c1c0d62810141d81b028041602408240100702c03c2c20481d00e01510342090100700d1100390720001c100ca40c00445c040d20030b41e40c0c0300303401d1003030680000fa03040801045c0e1804000103460080c00720711034016510310f184169000100ac0f010315110703081908480070014002d07a041440000616074038030707001008494102034503151100c00306038050501c07404201000075010807000c4004110320142c100d04140e06142e424800c1a040c3d4a0811540e8042c191b1511204620709003079403c6200c4d00000001c600c443e0f400aa0000141c44c5d0211800c2e401c1403042c0c1e640240138000411880c040d001e603410110083c8070f03061001504480c1541c90700c60817402502c42002d0750007620078003882800c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 904792508 1250 904791258 904791317
    0xf0203150613090201090b04061106010614090103050712110301060e030f0703110d1a01090501171506060f030f010509060130090614010801110c12070602090d030f 72
    0x84034120080c0d40442e81c3c214180b6584145040c12982e91501000b8006400c1030304a40c00040410502d05140042000207074007500440c1001c0d842081d0480c0112f80c24400c1c0340003181010b48a84c040343d0b4050250a0624a0b10094081400800742214031b401c1190024858500010115034081a403814082f4810300780d940300001801165080d91038000c0442e810000b07451704070000c0e103940c401003010300b03640c10103c0c0318441c4002502d51609400e030081c0c40068001d0b11810010411001d41c0200000da030702c1c0c203c58500030b18104d69aa80c00003800c14004c00440b030605107400030801c030075000706c0c0600c2c0303041c0c072030440d49010f642e100c06004442c100b0102444211007000900c050354612640c04c6400480b0a4240010030080d1103039071980241c0c0d44d03640050b080703d2040b400500103d4003e005411044082d95200e03400c1000d40034405984038200c3d52400000c5200280100074003d03030341c04a901c1000040e01d046c580c501d0303510b00103080041c0c289001000880715881c0400c0e14070b82000f55002c414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 904793758 1250 904792508 904792519
    0x19240216030b010504050601020c060a030b090c0408150a1b02010207121b1103011e0504050f1b0607021903080a1b03050702060c01062705010b04051f050d06030f02031506 75
    0x31309050604c401820042d0046041d4805c800300200f655403140c0042030f105081da0380c0403070042005420b101181202070840307551054244002c0c01680e00000304404010a559034401d00c50b241c0380c5d5000020200807500c041d0308169014010f41c8150150010071895200342c03005058086080011902c006900926965510500d108880407800d2030001c50140d00c0c000b000000d20075032600218101c3c031419800c0480258860f0b00304401d00900784442803081004901400c5050302803107102070008181d806641c4114004071f811070654aa20285060120071010300b0030f0241d0300d82c145042c0d51740103080e402d00014601c1c01c403215031846118820001c16030544070349040c140c00da400c1001941029950300490365075450000f4140c0085100a441050b450355804080610100c1460558070160820340c40d191080101300000d8541d501035607440c0c5405101e50070718050f411011a5a4070411039031200c56820140c001c8140000c02c03222884842c4200c08a600c0342680d052400e402c1c0900701d54640c1d128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 904795008 1250 904793758 904793761
    0x20403050309010f2706030507030e250902040314160302010e0907050903060a05150406030c0b03100e09061e160e0a080609010902180c0919240216030b 67
    0x83d40900942c2c40381010078142a000115410f120b02e58030100c603442811811840d280402c071440e014481c69812040b607140a20103182c1d510f010564034540752051079030f01d000d6040c4212400da0420030240140c4041c0c0d800303541d240c0ea6403c064049135018440d035000e500a5510003010300314120036120480390306868004007120003004202c2e041708001e0044050005c1040344e0700c1d080c0d07000e10442c0e00c503420324200000d40381442e8071036040b01c031020615a070086141140c18404140380d84004811264006c0100d40d6035580c0291548842c035603a480798030906151000d0054031100802c055128582c042001e202590f01c0350440e6480e007000307545041c80c09080c2040c15a41c0c62141c505200b100c08003810128400703a503050620b1034080c1c00c40b44070b80c035030350341d518228110719140c42d58410b5803070607514288440c10704268101c024424080e65501c104507080255051044d0f05005e03070001c283ca1120040c2141c0c13482c6c25200241801000b00005001d11b9040d80c0380850440d18480680341c1201001070039 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 904796258 1250 904795008 904795027
    0x118051203150d150b0a0f0e13050d03090318140d02120a0b0f0c0c07090905010b100e040e0d0903021314100e060d030804060b0a03020a1e090204030503 67
    0x40e90010300342000520810a404000b0b444002c410f0161501c61418071090b401030101e44012648240500c134802d05641208010b5045a600101c0035103a42d11240da444c0d03101c10741d5141e11801c002000a0a5015840e01c030050150140c1c4040c11090094440d1406c190140010a41c074100724014402480d0f000d0b03400301440e0401d4058004818405440e003400e9410500ca41d1745018a00300c0225050b03c503000400c8a0a100082101e8215150a45c4141001d07690700303071651518000e0046445c2250b07120411001d00500b50400200c00001404000c0904440c56005200550401030a4010b6040c03460f50201d0000005004881c000c040e81c0b00051542141d08010f030850b0980c9030b00040d151201c40500d44078044240003030282281d14200d10f4010701e0000c000310b5031800248030500c10020b007802c030000300380c006680c1a40715902c0240000c03982032120000f10100b038243c0019401015980001c151f00500750200c030459506903000041069990240780260722540c04010a107030004d0192802 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 904797508 1250 904796258 904796293
    0x1209090207020d140f0708010f1d19060204030803070903030815030c01050708071e1b0e0f060d23102a0203040801021912050709050f06040518010602011805 69
    0xa44140410b0f601c03070440c02605d0900d4440260044000c40e5580c2490940142052040a1f400a032843d283d15192680c148500e0311040b81030080003100d44411281c10800c482941107501856116104a40703a041c0701100905d000664001180403076540e078049003040c0e50540503001002c82c014000c005400741440115483e4200c40070841e034030702c0700744900000108061103549d1a011510688180503146042007605105c024008542842d190482408010b400c00004c5038000d200d42500001d5456003000705034101c032100409004844240b01d09481d15000b222080850300c6030320121001e036584115010f0403141e80c9040014410301c0d010070001c1281016800740d0020f5414010b6070706180d903441015099078001c0c80311081c017009801d081d80400f034115154004c3c2c54072602c402c01c0301303192051014140721058060503202d0080c00c089010650f03a52000c0b117000e0140030b00b420b410b0410208440c41842000e010307200140d420281411110980c0c21802000c107034100e0010a04200301201064 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 904798758 1250 904797508 904797533
    0x1090f02090a0e0f180d05090d14060105040e030a08130201091716090204060815150706061403010905030f032a1b0106051008130b041209090207020d 66
    0x2010240c09011091195641c124110000c0c030100058840501d800404800e2004009148500c41e1080240c80c902d841800503400c0000d80240c241266945400b80c0080c0b01c800c0f507494014016030f01450749031422031003c120306040b6a07040d0b0382481403c025810030b41e1603006440b0350000040c40d1b00001100000203125440f5180d0041c14200c1c0d66a44a01c0d02a03030641030610909002e5010713070b00100c8a2101c00d0140001801410b07411402c2505001c0001c0c89010081c0181146140c803400c440404d5660b0000507100c00d0b01c80030750b00d542c1d0b10185807a202030806072103020704107075910f04107031124103045c01090101507000300071310b02e01020144041e4458002410210200c04003902d2210b210030070045d002c00d14111060701e162074010b801d000c0c0c590302d51048120121139040c03c40401070b03603c0d50440d00c0d0340503805044c40341840c1d8482800100248000034040e00000c00d010502007070148400c40a101e81c1619600c0e00ca640740c03240040b009070f1156440c000e4000104003103201c00f0814001d07160 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 904800008 1250 904798758 904798781
    0xb100504050d1b0536040f030509031005090a061407090e0c090307060e03010b030706082d07050a0206070305040206120405030909040302070f2112110a06091112060109 74
    0x80c10401c1d1244040f9860000514091810141722002c0080d91a4942450780c46080544054862480c00360b9840304c6142d03141d20001c0c08e100d0081401c6115980501c012542c250000c1400c011600d010303650030340c0e00d0a8094041d2030307082c42c280c500341e244031f00c94000074070070340e042e40f50500c00c0f500c0d144a580e01c2080082000000c603906102800d41942c1c20300800e001041c00d9919030007003151440070542140d15020b83c1602ca40d0120008011842e00303d140e80e5404036504525920004084481e10312146a00c544141700309401c03020008001d4024000c2c0038112883d0b401c592040e0b40d5680c0950844000350344c041e52203201486843c0751143c1ca0703640c00340d0141c85001901d0400115002007124034205a9007100582c010703210500c050441100784d030380107080d802e55050103c0380c801d060170410040b40700c0103400001e102c1ca4180700d482c050140d401850f4600003c80e80c4662540c1080c0005107102041210443c188a17036034081440c100d00407412900b20180904056481d201000000b0207040c0c510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 904801258 1250 904800008 904800053
    0x151821090911310f06110a020f1e19060807020f0316020105090402070b040213022a1e0106060e060a050a0c0c1e08070e04031d0609040903030b100504050d 68
    0x4a9103c40c40d80742001c0003d0403901020b00341281403040103411400c40f903602c0b07036050f80811481c42c096a0350700541d00031503406952404500036400342806c101910749050542081e402070510814244680343c1d60102d640c5039803694066140c403038040307890f00b160340041c071801c1c2e1044c4034640d861120100c3c034007035080c41410243d2400540d0b034040340a0b600481010b580a00318241000103609003032204a003d40604641180f800d00c204501d1b07140c109140d04074a40b06111440b004d05000c00800541d1800e00050141c025025010035445010b0b244500a010000e000c10603803030104d00b03001c029520070b980700e03446041c2045010700040b00c0004900d40151740c10802060005414022580e646944020103491840e2450038800483e1408034143d0146040060110030000400e80c003800c40c5410304000c504504400c400c0d00f000035201c0c040c01140030741c4145080d92520405800d40d0010768159001d480c4611030102c0c042080d9040d01441c17040c26004409150b03030800140740c0c0c0c00c402d400d82161011 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 904802508 1250 904801258 904801327
    0xc04050a200a032702030d2a080c070b07060b222406050a0206010b0a1403100302040c0e030606010206040c2d080d1b151821090911 58
    0x4030481c603c9901c0724036000e5a900c0302094829400c0034400340b50020a070341409074a01c0c00d6a0501100c4c0c115442e41c230040c4030308544d140300804c60f41200f00c0e00c80c501e405040703400c031640f529110b02680d801070f0800c640382d07894031523405614100b00565286103440c40601c40c40740d6007043c5400f0060895603803841034440c0c0014910000303e500222500142100b56200c6464400050020349440810f8200841c00d14050209140f0160301c1034804455140501009031651500301402d120b407802e940000b075016040041071905694401d8556400e504203e003180e0150315010f0040e41c440200f90341c0a018800d00e0a03042c450700041c402803c40401e562860007200312810103c2e032486100507006040b003500000340703881905a005403c49111180c060020394400d4256650942c05c2c4206404020015103500c9840c3c60f52072019a01c21400785c0204440d01d20510407980c10540070080394030080400e0240d04085817032400c3d4840c0b11002200d01c2e184500d001c070826458810794518140710307550400700d0309 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 904803758 1250 904802508 904802531
    0x291507030c0b010f06030f0b0307140307083a020d230304080c06010509010f1e0504020706090303061e050f1c08090f0f0d030804020406170c04050a200a03 68
    0x702c14024510020065181810318030f0080a450070010b0301c42810341410030a403140d98001c500c1508450101003001e600d52500404241040c0d0300d5405200c05014100000703109100182e2070300700c0e5101004407401c0121200c141e01100340304001031940181d110300607100e101401a04000d084d04110000101350b0900510782e425140e20445081354102c4010403000f06580e000c000541c050b00040303600f00300700e41c10128142c1d00c110f818030810780501810a40381402d202442c04281c080c0502a10542da98071003428000c01400041d0f9040f80000d10700240000c2c03d4000c0e8000882c090b03040035000f044035281000b04100c01c00c142081d1360b441092105509004541c903580c0400181c440d070742894445070032004010102e5102d65495000d600d80f030500070313503d68884045550031580f5040c80101622140041401090148c2085841e15044030800c4860302c400190480100400c480a21503a0340303036601c503026105401e10412448904107840189004104060940c6441078940000c42c0103802 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 904805008 1250 904803758 904803773
    0x15180f060306061d01031e1d10140c030a020d0527010213140f060a110d1b060f0906020c0307170c1e0a05071203021627110a0201291507030c 62
    0x49071052600348d41c07440301e40e0001040c06003007928850424100201c0408035540410040000c0030826146030010000d4070154040d810741e150b0324440c071020001741ca0082030f2100d0b18800052000d003098024030140640f24014000c88403841c200c0c0001800c103070310b8a4850400c00b0071441c5580c0d071000941030091138984400001d04290b40e02565140c04d107440510402c0c7c2040d030741c04804400c00c0919540f250102043c502c1ea0399441c0e5000d0b030005000b104c07040b85540180000304004100a00001b040310304003100001424006001e0302c1a15205100c40403802160b209200b400e1030507070003041010864a9503007a20340c400c0070100d000d80d9500c2000c0e87d80c0d80d06125594111001c001e40c3c8a0742041450303810000c5c40039105114030314507003803804d1421940601c020014594541010002d10050510716600711585461144a03440d4843c1c10380a00a8041c10310740c8801024000342129902c0f007820f90b1400401c101101900140d903c0e811401400d54640c4161016002d11a2074610380000030040c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 904806258 1250 904805008 904805021
    0xc0e01080609010c0f1d091e01080312040209180706031b08041505060a0e0103080706050c09010816020f030301030c150203040303080f070905090a0e0d020f0715180f060306061d01031e 81
    0xf0a04230340d01e455034110fa0281c154406030030102c0e66034000d1050120b000b110030341d11500141c044803055035554541c7c404420701540660020018084c24400143c03864058010134240401148026118196036030111541c1e0800c03a8044c0150801c041200c40d046000d41c0a650840009004002000d40b20082442d1902d400c0e40201c8400c1c40005080c030912607a8400d945c0c0080078407005030301d00302e030b181c0008084400c05400c407151902c4030440c0c040458000c00420711280310200c00d1360b4403980d5900341600e000b021031186584800700c001c4030a10440c0301200f01d505803549a1500355180c0c03030340042040003040043c0484103000c1c0c0480040b175940e907403800321441200c45003030100d40f00f01020221070810003015403680641d4400f68000410440200d4a0401c1c2e820703000d40320a402a01c01422100300e860a03807201c4081d4090540404c41c00c0c100e480030b1090341d00d00c0d2424000250358141c226080482d0844c1c2c44440c8140200c0d40a00e98030981186124607a6240391074519458485074000b00c81c81c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 904807508 1250 904806258 904806271
    0xc061d0318010e090411040506060421050c0d03050d0c12020705060603120910230c0a051c090603090c090606020a0213020301030305160f0c0e01080609010c0f1d09 72
    0x10078a07800700351583e03c0f10000710781240030f664504807401e183d500c0f4440031014200c040e00c26512040003070300d0341c0c48038001d480c01054240c00c040d40c030400e00f4105101100c179000d01135502c0c1c040c044458103103081150902800b1640347d82c6481c035001d4070706085001850208000020450701c03802c1500400300600240568900900203403802e41850010145022543c024000b6050404d004040295845643c0070901c0103590800b00709406043c02000c00740b000c0002000781030640800c500c1f06114001907100c6d8514885c10880c2c2e0441c0c203030700c3c00901138084102620009424445d0500800d03110341c1140c07582c18805c5001201240e16103100c0010f85072a40c0020300140e201200040c00c2d0306d803111100e510b025010b0021891541540c60060041c40b981146280c01114000303444100305c0078080380708620390030000c190701c2c15407036204011900c5000c2c894240f80d0310421000c00c01030031042c4250102c4101c0c07500c4800540c03009160039548004041c00ea010500703225540403000351100d00441d48980c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 904808758 1250 904807508 904807537
    0x30c0316060b0a0611100501050f01030c050d0203040b01030506071103030a090f0507032609030c190810090303110a08180a05030d05010303020d1107030602090a08031603120c0c061d03 81
    0x10411170a440c13030001c3d101034a040103402e1074010041a22422040e10402c88280f8011a00b20790210701562180304048020340054030010400050000c190f10340b505891181c4150b50050310746a07070844101d0039980d00012150800c00102d126016542c0c41020030707a2080400001680341520745608140c03035644103444001002203000e030500600c0803030a8070105824030590400c0681ea01082e0744600101255000300140c1841c102260010310000e002007400701c1c21501042030440049021340b40c990342c11800301e1305003494108521003401c10355103d281a036890b200c00740d891610000318030103a0f94000050340100301a00c1e0228800703000815010074603043c049655459460020724110b003540101c0100990020b44030514440816024105c03030b04000c015840d560403000203040821584d0005501d803200062909007403802d010a84011406602c84000003010004011f0984190031607d100003860290b4100002d0303000c0d8400900c00e0701c4844d0149403115070b030390410724660100c501d488014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 904810008 1250 904808758 904808777
    0xe09101203080f060303040e010e090109020607151d0a2604030b150a0b0406050a030b0904050a110910030201031e11130f0e1501120507031a03030c0316060b0a06 71
    0x30107190090fa070040300aa00851401d4500300c101c0b811848107006003108a842c05000c90f1259109400c01c030001c83d001840703c0c0d034980c69880d01d031100b094226402c814690800c0d214103155100040304919260001c40a041004001e64a03100d98071961000c4281550407001103003100160100504091031280d0311000c0e01d418440307030030302c3d40794262540c184c17058403800020300000411405840864060f41029522143c41600c01d60240c42135800c15508004680d080005000c3e002035840b0310b03d030294104564401d081300034400c11000854a00100c100b0701c110410055119900004504a4500280b00c1040600c0c1145056884554400c3c0040ca808030f81120ba03840703041c0c45200101800066805028640384250680d15001010a64100b22100d4101d0059004046c1da040660100d03108101603d00480c001d00100009070800f10031032031411111200d41000011625000c0c0c00728020760400045801c0943e00f540804421a5085e03240c88003074002d6107a01d041100500b59a8542d203521 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 904811258 1250 904810008 904810021
    0x203130605010b1b160e2e050906030c0a0b0d020c011a011d0d080904021c0507020f210702060f36090109020c2d0105090307030e0910120308 62
    0x410f2442c4c034220b80b154008030400301d01c1c60543e450340d070b0840340c40c0c4043c16000c0e84c91841c0018180c03041444201705d030b1a09107061041031080301c1404182c0e40c5c00c55030b00c0301a403620350a16984014038000f03103400800000061012000c5c42c03014200940c05034002528040100071a9401e581030345004036107640c0790700645c044941c0c0240b480c04059203140802c0202c03043c0d01c8005024609000d0015000280000c0c942806445a40496481c0401ca0400761051891002e1901c01400c08440e504014010004101c00400b40401e200c89014101854862041c1c406130340340d5510380c411701c8101c0c1c2c492402c105240c01741e6409005040540818580740180600590400e54400e44d4005031101a018140d254003e980d81c0140007410354a501c00c0041e100e10713003054034511f08070101100304261600c038003031010081124a00080b48602d00c5d00244282e8071030802c26aa40d000c1d0f404000c002c5801d81c0e01034641410304042581d80944000f50030403081d03540d500648007081a803c019400107201001708808c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 904812508 1250 904811258 904811287
    0x10120617012304153215060703050306150705120702180106050a0f020708011104152d090b120405060609091e0a1a0a0c1b03030203130605010b 63
    0x41c446050b2a0751030682c40d269a8540d42840501c4041002c01e9a5845110021404902c0300614101c041062100003809001c01100c0701e00c02c5817401861300b60030304021054240201a5500e103076164984504580b01d20040000c0c0c1a20001c0526411605201200110350308126508c560004004c400d56205c959005000002505100791001c40303800e50010486994000300300c03807008045207020800304480081c228104400380c0d100141e15802c2090121036003030b4100040040741c10b190000a014000100250791100c0da0307400d400d0b008215002c4143ca41c5485040405d04d1a0140c0391150340c0e00e4550f6500240303a009005010314045007201080204403040100603004042220b01d503000340317003654500c5c1c0d5030340000c1c4803500c1060383c00d803101003003034010040800c00961150b0b03210072000c0306000086045400311451800c0d98141104045200e000d40080311541b0100002203188030b000c2e0301d066000e90b20250814a1300100c584404001c1a4148584c5000c1c00c0010509503951000590004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 904813758 1250 904812508 904812551
    0x3030522031e02010c02030708031c05070206010b030c1309020c010e0115091104091406010206010e04020108040201300b040b010503010e01052b060b0901060e1012061701 75
    0x194001148001800410300b480c40210040070940100d04481c411440102c5800700c0340403000350103100c0d0250121703d42c2408000340880036034002c01c880710785001d43c9000c81583c0c8103036840005038002030010310209846c20021680414400700003458160b81008034000c0c05c007070342d0000070401c0c2c1c0492880042c100c203000b001f4020b40400024084035403d201c40e0300054401c0e05ca910035103a6580700d041c2c0d0140021041e50020402400c0c01c20035030101050300c0018100c1103030501d0050286000100394211400039983c080d507010b035103058941d60b413980192500458071040d02c8243d844a6104001030070810f040d245e01090f10100820a00c0c001d2003070000343d5400000d02414050140018800038144014032030450780300329000b2003e42d0201804810304041e00308490b206100d0503080070184501500000c0092000b540c50f0205a82c0e24202102c1f0038500c1d00c4050792110340500701801c0e40b4480c14100300d004641000009030296a003840c1400301c4a189661402a5102c031b0303071081c00d00642032046 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 904815008 1250 904813758 904813807
    0xb070c0807031724060c01140c04090b060f0d050406090209070e010807030c08040f03090302090a090c0605040b0a110c030d17090619050405031e28091202060f04030305 74
    0x4420b0515500a40c6110450500c81314003540d008a00210202d400b50403c070b1030848800200001c1d42480f040e400d50719841805240c1400f41820181c14031410100c04031810901031400160030710303a403c498070000d00070142060301c6807519818508050707aa000c0c402030050540d0740791003041c000440009400c0c03460080082301850316150328229640e81000b10075502c2035000040c41c2c1c1c001828642075a10075aa504042e4010074103404100f80c00e45990300407140741c0d014003e004001560703400300311594812400ba80c03003881c90a010b803803606800ba00f0000900c40440f0103581005080702c01003840c1c03882c201003140c002880e001490014030986070206d90090182c1300585410301c0c02003d0030700070050107a0200101a40c620000b4140f00c400d2040e05c0b140c01980c021049801c3d041d9641007070329044422551207004803600c801a0070301c0c5510706800724494688640c03001a24041200094200090060740c108508126030b076a401103080c001e001861180e00c52540784c40400f14039940403081a07444 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 904816258 1250 904815008 904815031
    0x90103150602060a1514121519060b030c0f0310181e0902090f0403020f0105010308090909012a0e060d0203100e04050615060c120d0b090f040b070c08070317 69
    0x1400440f030352104e101e112480c140c680b11465000c64507c01e14080443c04d0001240c010755081c0025242012040c4849040000051142d240c584482081500c0191504c0450b603008105040e01c940b0307c080596804100d48481c40019a69100201080301c01d03075052100b11544c58022101541c10005402550007414004001d550541e50104008034400b600d411003c50030b00e0300007000c0500c01c00c4140503820100303000344010350750703443c1c0840c00342c04c5404e0701842a1507490001d01035240510402c0e500800909020500c80c0c2d42c00200b0381d1098101c92a4000c119003003400c10242d0b00c1d83c8000b48903101c1c0b01d50b8016503918062071441803504854016032304054015081c007000c1140019078542190081d0b82c8202d0040003240011000c0c840d110704503880340103140b00f2107403901010300500b00c0c10071402410f022660600c0204012200110359004440c03560f400840d001c6203448180039440712180c01c03d4a0319034080d4880e5012342d002888100c000407001d0300398002c144c41840da540c1d0440341c0e0341d51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 904817508 1250 904816258 904816301
    0x106180b10050c0a2909030c06160c1b08011d0307380103030809070b0f090303040f08011a040b061803100c120b010e01090605090103150602060a 64
    0x191804011001007400c000001c1410364200905114450541e58070036205121221403508000c4d5210142c4050810750300c0d80000241038120103c110340031040128064415692222000350584c2142c08040c010000e24402c64030010300800c0c1c0c2d80130441e020480d1515a1494068101d00b503c4c6800032100383d2207058041d4444680340002030b2a42140c3c0070080005501c6120300a900ca100300c1c04420119081102c0303c05600312888064030305903406a601c145945d51060781c80f5540e0b403500d02c9422290402044100010f81345030014103461803009054921303107682c5020002e13141190f50030408040e5900c04030340403082c0d5240402c100035032050700e040c041c8800c5400020403d00960820700301d070180b071088805007951b092041480100e070b050810400801c05c40c00c010a2a01141d889c0440145862005a61580241d40098000710705940d811152410500b049802d6000034000340d052685402c0f0300d4800303401c0210014090600703607008002903e850008402558241250000300861244 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 904818758 1250 904817508 904817531
    0x3140f121501172d04150507020f070501050f130f0602010f2306010e10030e06090a080415111027020f01031d030705070f0b0a1704021f02010618 64
    0x34441e60000340e40300c50030034130380c1d5661400c48504c68550010900e01803071020001004611001191590b107102020400d03550303600c606a070780341e01c40d03500c0c0700040c0d1100300104801c1d03201c0d00040c480c10b600740c0d10311410490041010003071440c03190014218003110450034004a60309104610416501c100305120481c00844241c0c02602c802c5403030680000024001a183d074040d200d4054140740103054100004c140340e00c000e000703003882507800c41640a80c0c0d011542c2c140c400901c0414050700000d03100c1c5400d240c605e02030b0500e101c0302d0125091161481400c5c62480080c042111100000c81020030303088850403411810080c0d100041a048604207120000340c0c90700e000d414003494080c20002010007803103805003020300302e0041e1100c5602c000a1490108000452458101d6030010f1501100688601090509004418203040090844a031054603503820624803500540050881518201c1003205104000604490003025070345526041000080401c02904580b15083c0200503010405 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 904820008 1250 904818758 904818797
    0x504030b042103110702060d140a02031e0609071116030b15011d0609010e060c0102131d0703180506071e0306050303030c07140604051b04020c060403140f121501 71
    0x501700640684e002180303481450b41d46500c03184214616510700c10943c0340520111000c0e500c101c03821546030000d0360540440144000c102ca016620041141c209945d440c03000b151007003684240c0c0300c0d4034481c6c07600009091040c12605006580a280d42c1c0c8200d18044071803c5c8051a1002180d04014158603103164040076000c1c452603084007100e00f10303907603800381c4012540c500001d6211a4803910010700c0d0140510154001d0255420141c0346c80c00d0306030b07114510310343e0401c00b051a111000603080081c9d04a0712a074020159075400d510700c1c007160030071511082c1c079200c0119540b9003c51003145001005440c0c9500d40040101b10b441c3c184a840e0801003c02d488e40006860f00c0c210703400204902e410003070681c00c400c5044c1080c004071891458282405951510143c00e01c04007000d0b170030038807074090409008444140a000d0020100340d100d0b980e08035205012004c08101c1d1903018403141082002d00c1d03004010750580320050b00920f05040b00d80c8603008507000207a5040c0451a5440300b1081c0c4407 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 904821258 1250 904820008 904820017
    0xe07170613080f1b07090507050d0209040617010c140406090e0c210406151203050c0a0c330905060f070501060f140a03021c030504030b04210311 64
    0x1550081d14410094076099081e801419503011410101056001d403008000224030160102c4500704c2c0c18141e96140d441d01200c00541c1d0480000300200043e61100e58240c00420758140c026000107107040d520324080303480708030022098005944480b0315107181a40045110306117403c00c28090b00e406c0c90984094041c5c1000c0c40342c842145000000200710540a00c15142d9010302000480410688007440d52440502105c08541c05880d000c1c60b113043e00d00e04d66001042d10104481600d09001507102500d0075008000c0d104010312034194400001103018000d0001456204002c2c00e41c0000803407140103801180c0b84603022400260a200c1c56154004400c40c120f45013070391840d95410398030843c3c0d02d02d84a00031011b030180d800c0c40c000040c400303441e2031303d41e088a50007440840c913005d41104024108400d444003035401480081043d1407115441a10302e5602d100741045032400303903260380d00f4a102c2c108840966a00c00f00c0d04c03000000c6803c41c611032000098500c0c040009404c220b07038080c0340c1d006c2e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 904822508 1250 904821258 904821271
    0x6080316020d02120a0b0903090a170118080c0c062a120a021506030c10030b18161b0f0f0312180201090b0705100911130e071706 57
    0x400d01040540d1220010160b50300d8010700201299000e5584841c1d650007107440455025400000003042110040150340c45480010102e200040c0b0b008000d40350751980e15011143d9546c0c1c0c0e0741c1441c2100c1407031100d6050074030640b0203940354140003403024101503681d0b9686014140801c0014800d0900c1004081100d81041502c0241e14040540c60302d0b14120101110705d01c1c82c0090740f07000e40c50700007489a441203a0310700141c40707035642d041c00c2c16200e002858419030400c5901d8a000d448902030f40002c501d518020380050841e0b9400380803613070300b0b840075941c0d4034140280038000ba05082c0d00c040c4c00e100190740b038030211028a41c0c6596000b0705e400001d2000d401c00c1d000450440070035216850107440d4a8441109018284141d0040501e03020f1084089010030b44074000052800b1a00702902d500c0382d0007401802801d0400300704200136040094044840700e00482e10380e0866610110303603c00306081e01a0000341c03880c0341d115003882d08406130172030b5402045211807004540400194994001c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 904823758 1250 904822508 904822537
    0x180a0614010533120709050406060507030206161e0504050406090203161b0204050708060f09012904030c0305100b060316030e1615030f020331021903060f060803 71
    0x20302e43d440764505010b0707507080c0c41c0292140307004d028001b035100c80b07290151401268200b255540c0da1000f80e441d841641e9000b8050780050300000d1402c0b41c40ca51402c3c10b10882d08200460114143c24035403092000c83c50300001c2080440c003441780c0c1c18a48540c401074041c010045142d4103061640e41158071501c81e024041000d0550b40d4102006c40307012a0000c60350103002070045040841020308190b8044410f2801840e00c848240c0d410321340945503030304036452003603035400402124130031f40710894a905043c24103201c201b0001001a41e8800b0b150000c50241c000381a072510f140340101c2c00d480780c424049209005c20300601800045e07072030303401b05100040d0400086c02d07070b219950ba038101480c400898105501d5840c0c001800720000c4c1003030a40d04507a55080040d0003010362190101e00003076415405101c1d00c094a00801c034805900c0107500c90b9030a02d00d40705d00ac503542c0024000b0600d501c0701403418900754030800130410180a039020000d0018070a01c6003904000c0040d5983c00b46841c69030400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 904825008 1250 904823758 904823839
    0x1c05091003061e050325120327051302040312051b01060923100b0703120606020d0e010e010807030b0a030218070f09080d0305180a06140105 62
    0x54002d42c00314004101c01c04035140052064403015107440e40b2480784c140a4092215141c5000c4080640e001300215554a080c940302c2c01c0960356503052101e00002c4080c000c13440c00d80000c9075511b8400c18050f00400625070b0031141800180550300420013400c0c82601c0c018401400001d0b03581901c044c0b400c599180c1245c0f00c50a008411012240d20042d00c500c551a051002c00c0030300c0d10b03802506180f03016140901000700710503c068000d800c1100c0724444e61110f07501c01d1044e88103510080c50b10318002c0c685104070002d50b003502c80886403036501c0f0310050307482000c15544150b003010b002c1e88208000d003021380350120000000b0b010b441000745001d0403d55940c0c2c0a902941d1140f160101640d0007812606071000d900e0340c0000e0b100b00543e494000714a0140703540380b1031481409000e0584a0440280181e19655641a00541405011111855559a1b042c4000d900401071424198000e10010600d0090403040060884041c0c0111380560700c0559a1200d0261a9407031100c0c0031401248800f09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 904826258 1250 904825008 904825039
    0x21c020d12020423090105060906041205010b0316140d1e0206160507050925031a0405090d030c1103040b0d090f1505010504090218060102010e030f0c1c0509 69
    0xd22850b000100c8410340d01142003442d1004d92400c00d00010199000504c82e601c4008015450084100155224004000602427620081c00510800d0720610000c1408c6105d0b800003030500b83d0001c07000d03044081340320f001c00c414000002314100b481007e490b031000d0040c003501c03220907803040840c840b840e00d031a84ca858411900c07010304942030304807d8003020140580030705e044c0b0b4440b9158401e07144204842008603401c2c00c2c030410410b000310100e10f900701401018010580c068000b900c0c008504c1410382200c1d0203d03454a00a8030b1281071040054084454007210240131102c04010b40400c015450380b60282628002088406445c480c014140e22058080003c1015204040008010442c041c1c2e41c0002c21101c035442c0b05c20350700a28410b01083c3c2e21182070004403440c84502a50000148081000006141002980007481880049180c54170003c01a103180d12124030304501c0200000c2d102079088041c0950000400d88418046800118220042c02401229203a603c00c0000c16000242c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 904827508 1250 904826258 904826261
    0xf190804090b030f030a0306060207080c01092601060303050306030d030605010917070b040e09100b01053405101404050a1b0e0405070911090a0b0c011d0706021c020d12 74
    0xc58124107011070b0340c1da007032486d030040107402c080c4524030240c0314500c400310745100301240701c148001043e501d50401915100c000202982c3c8a02d10355a10a400c440383c6210034400e016480265000303444c2c60340c1e43d05144003450300e0144561211010185000c200303010f02d0780e01030a4001125040003003c070482c464441098101400d65005041903c000100050084100e020685c8610303501425101c21844108485090300d2840144034000740c002c02c42d80d044238450744007100c0c1500b0400c40040c00b19a802c0d00c43c0801500d030340015103039a0f00c28440d110010000740100701404600300c94000141c10a592507503034800c03200d0700003131400702c008030b0780c0a82d1049070800c00c005010580c0340c0c505500341400c080361500c80e40d004250309241480d00c030f1101884000c0480750032940207003130740c3c20461400d1360f0034034541c00c5145070002d55500c0d060700e1401d6141c1440c11501c038810b4074020300300c60b918050003e0f00e02880c0b4580d4403410344d050142ca1418640200c0c0b1000e0654240c1020f0b100e507495120042e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 904828758 1250 904827508 904827523
    0x90a030f030b0301050a0b12030f0904020a0306090c090314070e130501090b130b0c2505030c0a03030e070f080d05030717180c010306050a05010302090418050f190804090b03 76
    0x243c042d880c240400c03184541c65088450340c0301e025110780c08030200070180261284a00c450000703102d0b60800406119082c2680103001200b020301d0002003103529804040162040302c0307200390004008540c01d1091000113801c0041410303114000704069032405110300410080144075036944607004038260140a001c0d00801d490540c0000d4203140761402a05030700c03894208400c00c0d03850011130400070309526203c80c00c60304501c190311304d6410341002e00f01c103641d1101051203044819020900217480920300c10403542880034400d8801041104000302030324a0041154043e85507003c03024420088480e000c80c106402c1c0780c861030030966958075480701703030349070b03003000e80c00b0100516a6010060804018070100e000300004105640e0706840c580011826203056005240c0d01c0086080200002c0d80030f42d00805084101030000300f000291500a013410303c12001081c0c03070310740040718a00410681801201c04407600e44240d45100c1c9103a072100005800b0701d028000301e96543c0e00c0020015a030410151 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 904830008 1250 904828758 904828781
    0x309011518090c0b040815070504030f0b19051302010e03010510032307060c030f170a0c030615030c020f0105100b03070e032a120a030503060d0f03020c01090b03090a030f03 76
    0x495465031b03210402d40c0d0302e540284440c0d858180620100748180d00c507000310b0f0300b02e07030b0420402e290302c442507120032140040142c90680c585045420344000d4941900510f8030514841780540381e100c81c10300024002820010303060b840399240200700144d800c06180b030f40d03050300d41040280000303030300900c0080403110b1280c00c40c9c400b1744200c0d0f0700005c4040c0d00c43c071850708a03131081e911845407600b4030005030390750340402140c5119031100100040341040a82e102c10001c040303d1a02264159a4464403481d066105260304006038841800c10101ca404011440e45001000002c1020703141000c140a8aca560302c2c00707402032008000000c00c9015210b450303490340e032840050503200314140b08050504650902445034603020003050769142640f800d1a0080007242c1d43d80081c00b603000080e44e00b202d86600c01080030780c0c0a4024181c11010410501049014500c40c0c1c004040c42c00102001501c202c00316400101140320410800c000018081201d4010300d0b07140c105509002d00c440e105901401d9003074450b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 904831258 1250 904830008 904830029
    0x313060e122419092d15050601090306050907030b0f0c07080d060915050405150127080f100f0603030e01081518061f2717030309011518090c 62
    0x8000520022a5450140d05060401728500301c0c104e080801c2d098040001c080d000095024488a006596401171a80314005241102c90b0b15125501c0708100c4505482e00c007001d5006140038410428440c0845401c4422281c110005140c0004030043d04e1013848801040500045886a654500c40d04001d0282010200030b10641e09500400000041c46e0300ca10b074811303401c040200340d18018906002c20860f106950340c00005203080008001501d0042c1501041d41107000005000c21041c8000410307210084050440d400048002e481901c02100714000f440d480e01074100000380d008400c0c03506804080c04c0240039a9604c0c0c2000f2a06038416401982020110010703429500c03d41090521070721040b10741c107130104d0042130310100911031081110007003404070781c41103280100040c1d44c40c0d01c8807000c0d5205242540301c10000c8480c001070103000001c1c0c2d10110500c94101000c0c02079911450541818942a91505000d0303c1031007160082c1c48895a969465a410b004070024204060444520f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 904832508 1250 904831258 904831271
    0x308040608071e0e15090315090f1f0e070906090603171608160206070c14100828090b070f0305131101020313060e122419 54
    0x15100d00340807500b041c0094200010030000d0141410100c8400866580e0a40742e0f403600003d0096121061098201c055014440310420707036010480204070f500b02540341401401c5c410401840d1501c24000214550410700241032074441c01003204116119405010620070007503a101130924160760403041c1c0c41d504080e40421002003e400c41d1040383c3c45090301c1040030701044140301035030103660083d00c226035100800c0c00c00700e4280c030302608250050440c01c05081e0000d50000741703282d212aa04a0b104010031404100a2a03c0381031070300003041c1a20305503084a41d2a0703000f04110001821a040b0b17070401090194032003003201581e070751401d01350010003441030507080c810b00b80b00e4119408400a1810402a6406842b07401541d00500941c0106007904820345ea501d1200502c0c21061030461000b4012510060300a45804c0000e0000d500c42c14600c070441800d0000800c00102c01e00505d9000d5546451524400e100c5803074411150803161001c1d40b205156540907148604035192018140301 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 904833758 1250 904832508 904832519
    0xd050324030609030406021516140c061003021002010e060609070201140a1d0f0316030c06050f0702010b1c06050402030c090412021603050c13061802040e060108100311030106030804 80
    0x100f00742d90058007220103160001002060364071080715043c0d26510030000c00100e0702c2c001d103450720072b80d62561501c81c107001642d002c562900800b2203c20503280a410010019400e01d80030724011854544001e000c0031956002c031656034800a85424007641d04a800921010700c02c1d400320019000c4002c0214450800400c2036003d081c240b05809042e0042d840654041c0070b001038000401400c040242d41400d0760b2040740504d04100b42400d80500880007909000110540704081c8100702e8959030f802c0504102100038210340c024640d00d4010903604a154020380405040c0075615544148049800c1c0e640d4808079052607000707501e00303810413010001d010810003404641d1400c013410ba8205d404800c020030407240a45241d01c000b42c45500003950040c00c60424189880c40403480481c0401d007190340e1003055103000b0f03d2941e480103041d8007140c140000c006003141070340c0103142480d01c411070341483d140d45000c80095100c010481e0340144010100e5441c2900310304011508414016156039841 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 904835008 1250 904833758 904833763
    0x8042303100c12090602040504020304051609110d15030501090c06021c05040b3108010501120b0c0c010b090703050601110106061409010c050607020d0801080d050324030609 76
    0x15046984640201424202030a059100e400000540d5940310140300030300e42c00300e9005203140802510116001c000109807511180020b42c0141d20450091002d1401c00003030714449400d82d0086d61206080413034451100c801d1005a80f80605c3d09100040d0103d4076014000c00b1703000940c0000d01550800b80300324180090b07250039804030355041e000d64030480060100443c00e96070071441e810109200b80410f001c507103680c1020b415441000c0d19100d104030440c29260b000b4124140030310009001c5040c0a200d51032081c040c203401090121242c880f40540356441d002c00100041403002c8600c008100d420380b41c4025007152030041070281c209403c1d41011113000f40507090440d506404170b001030b00d074002c00b20b00c148902012640315507030b103030074140e18580100d403541d10444515040080b400e0340300c400b046041c091103020f214250010007a5169842c4083d01c0c1c0001640209400e401070018482d03100e420000712a404005404599014040d04000c0c2c104110511a201d170984281c104000a90000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 904836258 1250 904835008 904835069
    0x20721050f0d14180a0e09010e0303150d03140315010314040c060f201005100e0c0313050f0114060609010e0f0a150305150a120f0804 59
    0x100c054407100d000a1a03495a20310703154403010001245054483e80c0b1401c4900034003003011001d503100040c81401d0000488140c081d800c00c1d001d001141c01070180da410240b08503580144810051810b40ca0405000b051403800100c07124010329060034644101445140082044070658010381d0300c80c102101d1043c107198103100d5a5021901e03203600c1c84085081d241046200325403100f000760b00c55090000486416001540503c140b18018110080050b41c0f070b80c004445010794001040300451802200d403d40d0b070041d0000d070f50115440320901c090030581d14400d5200104d40d81e540e5036515121103011203518241006070080c0210005204903c4040d0006a8010710f6040c1080554a44104025040c410f030803946021038002d200500c0d0a09083c9002d4038851030040c203c4940f02e03616010100c140000c05d1000700040d985400300b04064107030b1500104c250740165500c2d0800d6060142c0001e242480c031078040e00000e2170510034001c024000044602401c1c003003108200c000c1b044c01c00071640940 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 904837508 1250 904836258 904836263
    0x4171f02120105060306060d0f0605030312040204060b0f1e1306020a0b0106032708070209100f150806060d110a02031b0105040c05130b0301140406050a0b0303030703020a020721 78
    0x30700c0000290500d80001568041c040040880d0b142001d0108800c00a080c0f0000039110182c548a00080c15a418801362808407a0051006c10901d003d2040100b12000ca4000b9406400280440d941400c8883d06454015450348181000c00310511542896400703000b0542100b031074400b60120707144c3d5000c10a0908240303c0e606000e02179880300d030300b0360640d442605400d2b0b004900700d00040c4458200b8a0781e070065805030488030714004032a008100e43c000c04484441c04c0e482880001c102d810405920030008010a0944140c911030102008100741c8000c1d1020b8420f000100d880f044101d125400765143c0810150480c1d9500e400080281d102d401034480e4071810010100342c9007442c00103008240c8141e511a0710b4076005814942000701c3c0d52401d0000070f03409580c0b10440d00c0642c03000d115480c80e2212002c7d03108131524051a1100c03e0390001046005180d04011118031980c82c0002520b401180600300542c9a0b0212403040313240c40410760000262100421000c1c3c082007034040054000790 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 904838758 1250 904837508 904837537
    0x705011803170612120f090d050606012c010c1505040b0105040c0c08040510050c010c020303150f0a03140a0b25180b03040602070b16020601080a0804171f02 69
    0x10f407080c041190460a60b142129a43c00c200a81c0e501405042c00401c21081c000c05e1144c184100310340841c0c000c49940c4400c503104d501c8241400301c9d40d80c01c540d0f8014a410100c40d441c09456841c0340108060700340e05002410700c000716054404200c4880440000401804803c221900c0c05003041043d20f802032141c40e0041c0c2c41c040a41d21801e11a0304074140840d00800424030f414900001d101048175540504000c0103130512021070800c6003806940301400c042d0303000310740301e00b006200c100e800001070100e03a210360048105d28a0a444000003001281e801c140c1c03001c01c110034070b03c1440c18541e5211001300404041700400c20886d00c0321a901e84507013109810a0154454403009448a0300149a40d80400031070640420001c44840300450f8010312600001d030420205a0303c42078413507800d641c885480385840c9848644258100005801000004010b0515400700d4036442e4840c4642c1c000d182000c0b01290300016040703003c1017056403d044009031008101481143c140094110801681d0040c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 904840008 1250 904838758 904838761
    0x11041809021c0b27060f0601021903021b06090d030c03050c07230103020a020601090b04090804032402031302010305042d030f0906120e100501060306030c2405070501180317 76
    0x4d00310303041c1d0014100040c900501003920741520030380010100429403811807003051300d2000300d11000824120074a00c81d130001c0169044410b0b450880c0300000c04650300800d030610a403011a65440e48010507243c05003015826070f003484c1801c9400e4400c0032820071291103032180008100460403420154446114800150183c100004406a100307040706180103038804001442203080c0356200046c842c600810004809007990340e14081c0760441e41c0161350b04451100000701000381c0002030301c250036440404520b5842e080740c0a203010120144041c0c1003542c1c89001808200100800240e602d03200b107801d41c03078440401d051139a142c6042c03000b20006a0003180100c0c481c4e01440680d82503d0b2a42c91712030b03c03030002d0040303c0d0050104031040c00305441807290f550304003447c03481703400d000c1c011302d40d000b20704107046042040c01202c160f80800001d540e00b4000c0c02183e02c0404440b1000401c500d08903036140f0791401e100d0301400e46051500002c000111f100020150441d5000300007688a680e00c1d1041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 904841258 1250 904840008 904840051
    0x10c110a0816090b210705041406040507020c0112181a06120d020c28240c080a1407150b010e03010b100f020f03160611041809021c0b 59
    0xa07141311000094004204000c180896200c000003010505824000c41d009599944000f400342c42511101c80f00213445801407100311b081a0207001e90000e843e000900380c03159424002400100045180c1202a56855190050f480d0013820032025039045000c114440083e4482446403010944940b0b11407103c000d400403c0307507404250301d003140c9155000381c2b015030501418400b5805982081d00c41a6056400d20410300306007151110250111400200001c1030b1005c4030180401014800703020301c50800c0924001800102c02c03503805a8641c503180e80704034100141041a03014035000204140720404030b1069400341d660000500b160300342d03a0020403170f01c1c0205150032924401c6215410011105c80f00d150680a29404692851648100c1f05e4490015201c2410340d000901480c00e10385183e101c51060107954080c0203e0700e81c0350609640341c40c1c40c3ca00e1704030803040c85c03c1b0001100d0b500c0d064030500b03560302c003034074410030300d9041c5030011411240d403501400c1d401044861b11100c400035000c0601 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 904842508 1250 904841258 904841261
    0x280509100b090402030a0e25080a0803011a120c03040213091109060a210506070302040501020d1b15150824090a14070306050606030c0405010c110a081609 68
    0x46490a4001c5442c2c490307210240700107075000408218105445d240c448100210400603400a8002d441c003104d41080c5001d0300c028404525480900198004e0f42074401044440341260304684000c11180d10110420034050168001c2d001111805406c4100b0003450700c03070900c02148142d20031200340020075400c4100780c08540c04401c3c0038218442d4140003c55030305044000c25003100303004054040c0141e48070710a20b1880c01840c6000000d08242841e0743c100602040b080c1d8001d8060304056040030305200c0000c1d500c1c0800b8805d03004100e042070030a0014074071070704031030700c1b40b03410460891700300301310920b10340c00341c044001d54642010030040002422200494120307140c0d500d5070841016030084078000040c00d400900359541c0c900614040100180c010ba01c460000f0002c140035280c2c05145081802c01c0711002810f2500a18080041001c080c84e0300b4116401e0350700c00d0814407200c124078200504030303c1030f012003160030440c2c801001c03a05210004003d40c0c040c1800300c25800707007a105c10301c01c0e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 904843758 1250 904842508 904842541
    0x7090c0e01030b01030609150501030e0c030a020d031e0306080c09060907030b0a0e040609051b011e17150a080a20220615050306130506280509 63
    0x2800210000380401107503100750807200c40503d05140c042280354540748004221441c0c0c00a0703006170f2180410811003540c050050900441c0c4001c00307002140c3c0310300e01194503280a020000d118420500c4000d0815001c0c810000c1c0013034000c554a00e011035034440240080045000741c0e540791007548046011407804c480c4c1d140c0b242d60040d14400c042e841d402c030103601429000f01002e60064183c0300c007050405c02014400c1c86103004000100b0100104e06103d4103040320301044002104403070621251a9030403255203150046084100000c1180c00701c0125102540c04007002c681c09401824001c0e501c04072059000c403054110fa0300d44145694000700b41ea5241d800f4401819010b171807800500710080074a981d006490040e0401d55504000c134135a8139400c4400084804561340e0301c10500c03c041d007c4100700c082801908226140d424450700140d1148412240c40072001d89076000140c80f6242d0b42010b0408a62103d005611000000c2204161100e24064980104062000541014090714140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 904845008 1250 904843758 904843781
    0x18180f04150c020c1320091903080304230a140d020318040f110a1d091504090c0f0e0a0e060103121101110c060a1b09050d110907050a020709 62
    0x2000251420340910004240031002505e40581d81c1034980c0c907459084243c0d10f502014901c11030780c2d4481d0f6a003085450525900c89480d5190004002e100140702c000442c0e4016400820b418801c021160941216001804181000c3d0242080c070000b040031042900c00400040400e550068400c0b00049941e4020700080740710b07a039118000e00c265403c1c02c0e84030581c00010b200d400315401244620381075065020000b08000a06441112041034002c090021406001114209035500306002c440100c00004201d4a12850307481c0004010820401184002071814404140c0b460f41d450004040503541203d05c00741107402d007580f000704d4100118950b81640d034040910060403207690b000701e82c2c48594074002013143d962070380d4010514030400041c0c0b00c07000011009280514014406034140c1e50103011110b0004201d42c0e00000302d5800100034026140250380104100405017403a038000682e2210541d0040905418410180d90100041446d40040e40880741c0d0140c0d00c421300c100315000301512 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 904846258 1250 904845008 904845013
    0xb090d0e01021518120d0e070f03031b02130b09010f0b0f1c09140c040b010801090e0a0b27071230020d0f08040818180f04150c02 57
    0x21806188002a45181c01600d604500403021000b410f240f417521046002c1100001d4012420013503070012401102c0403000000060080e051801c0b80f0490f501032907010060511214030000641d202042c1036034070b03003944c000b407a04200c010022000002440d04440060181c51854004101a5614a01c2d0811030341d4050b851841c046200e0707407016494015007101e401440568200c00e40422444c02514002c502500001c1c4100f101c2c042c501b460306103d1020140902e0401001d80600d030380110700c81c0c2c1150007011004c104419140c1d8201d081c070401401c010b105000d00030034400044110700758054091240034040400c808000f040981e503011501c5220110302c0e8184414000692451151030b54003a08a0440b0080081c9510100b8400040c02c100b801640103055884c2516881307100c4042d4443d0b281007030100350400d921070b11000c3c4a04401603118040408038070310103441d00c1003c450b41d00d008807500707501d40c10a00f1494454803002d07203099a005442611a03c41d0902621484803255400d400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 904847508 1250 904846258 904846273
    0x1e20090f010311060403050f061915140f03011e140903071e0503030a0e0705060903100b01020304050a08010903030c0e010e010c0201120908030108060702070b0f030c090d0b090d0e0102 81
    0xe6207165640f4154005410100070b0000000041d000c129810050040b180504850b15114480c1e00400c6106182c0002071818850203001940340780003841d080e030f03440b80d2800783d5000c13000c0c0124542c01c0c0a01a919050761070031260b081c5001021001c1680c55401c00ca05200c94258140344803089942542d420070a0382040007040000b82c9041590180504200d030321b207800c042151502c0c0e0130b54100305c0b6110788080e120501844445400d02c541d1010781012039107107044c000c1020200341d4800d03900440c0701d64544d5401906e0340c2030b0b0080040c1d40c01403c0c02040760b4641c6480c1c2e80c80502801c00d1540807400300c0d0801010440c484d0240074201d09809040c0d440c0c503401c41512004440249009200f41c0c18003030711100004202080d40a204080c60103040210b075a540340c240014a0014010400b0b800c54011030018003400c88503800315041c06074042c0040343c494507014a038180074410890810341c40240002d48034200f080f1410310798859000803041c0c582403002210181d03420442034a11a006820048 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 904848758 1250 904847508 904847513
    0x18030c01020708120d0b12030c0105071103040b0d0b0a03051c020c090c0307090e090a1b0b030c030a0e01060e01031a0f011203030f0513050628091e20090f0103 70
    0x5840d24200480c00860703501148400314001c9441c07547c40407038036040000c4010207010240a030f07075040065031401000301d103031685441d6140d01560081c402d0907800054000110178064020040303014005200481041d602c1c50201daa81e9513041300104c01c801c80748400b42c008da001066403420750708090100d4807560707540000c600e41640001d08079024071400c0000840c0280d4900f0b001403090407580e0042c0034014050600d4103036075584120741900d181c906841840303a8490f200969030060400090ba6440c1c1e02c4030304910018220040440d810f6618100001500c1031902440d94100c034010000003240c0796403034034110f01002003142c841c10050010001000300c0b03c65040e030a21414040d10f00000c605284181400584005880041400c0014100c0c42c080c480300f8000240c1140c41c0040c5694800a460019621143c080103e081407541d80c604007400d02a00402481c81c42204c203124500d031410a1500c148401182500f221030044030808800c81400c041d0001c1c2d020341b1495840741d50980c80e56 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 904850008 1250 904848758 904848793
    0x3020414060a03020d060b130e090a060518100621030c1103010908040305030703030e0609060a0c0c0f0c0e060d0c090207080417033f07050f18030c01020708 69
    0x142d4110405070b0030003034407090701e00034400c050140c0000712840740c1d41c0194503210300d80314016400031000c0003041000d00410090010f80c001c40740d54490808541e50341c441c02c10902c1d03c05150cd00124074060701183c08040e6085078400c43c25900c103a0169038464049a40307907954062400402404120031070313200e10100b64120b054170180c200040010420489541e0b500c0d100ea0011f0b403040300c2c00c3c1e001046040c2019090700541c8100c26450000780154a002d1a19583e03c1c00054407000140f956141c00e0000280300e6038000e00003540126440600c440686002540180c0302e100c0c1c2d03203e6890351742c0410183c1c03414180d052285500002e001014071f0911300e07080000d500c61031045030f030305c0d20070000000c0c43c0285440c520b2008400307601454a0701c01640c50303036142080050a00c40c10410016501c1071400441e14254203521052483c00d01551b945803081d0344074401c0c111851012a0007040c9615106920b40d001282c400095041d100994442001641d80b44003c0c000c401554100581001c02044417 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 904851258 1250 904850008 904850017
    0xc0610050f091009020708040e070e09010306020705072d151d030c030a2619080a09080408010b1513060c03030b220b100e12010902180402100302041406 67
    0x641c543c502200c1d6034150040c12071784541d404503080c1c080840c0030000b020445c0211a0702c20402d0400503541c24003400024080c0300140802001140e020460b001404420080140902200c1008894036100d41182c0ca440c240e4003c0152a407100412020481610000e00344849004c03544840c5c5405000550700010201025882e030307014400e40103085c000359000c015441f1210700401c1d20a00d01200c10322420102000c58564a826030801c004c907110305009a008040e06011910b86402d03a51107540841c400303407440b000c000c0c1091001040c0030545940640c814043d52400721000c002d44484460200441d000300701c0c0d111032042e44e240c02082954060803600c44480d210386400181c45001a0000340c100180036a21030813405003801807e10004281720ba403910580807542c50040007003100c0c008010951990002e4002c203260800c07050f90764001d4001c120381030b0b4010910503880c4c1000d550340034120400c80701640f141c00c01d040c820600602038401c803002d40b1482800b984140610f0024000240e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 904852508 1250 904851258 904851271
    0x180c030c04020c1c030504050f06070906080903160528081206011107030c0f140904030e011101021215062110080319020d03020a0e120a05120c0610050f09 68
    0x26000c415034050382c5400903a0700c101303907624002038509090401c2840d2050f0120051520360102c4103020801d60441c911a040340c51500c2d01700110795803021094294000c0035295080b03071104080f0030003002000318444500d0101d804400841c0040e10300b009030f0072029560b020340203c10800092003080c5003a65896481001814a0038a151407400020b14001c0c060f4029908082c6040040c0950b409040c1100c0052820344d0a07554200f070804000340d40340b00083e0005040c80384146844600b6405086640344104c0031900841d1a8280c6c2c0403801c0640d0b5048400e2644030110038400c0c2d40501c0c150301a282c454254645409111841c041c84200c001c1d4050490b5100000400c00010540d400300b000300210380c40380340e0039152445581c0b0040d15000b4581504824980184001220280d21001906207914200c51302522009042102414410b44400140c118040c600b845400c00240c01c006181c079407088001c562456582004200325138516008059000c901140d00548600c1c200c054180c1005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 904853758 1250 904852508 904852513
    0x20901090209120d0e0406050109080318040e010606020114060603040c03080d0912200303010b092103161506030b040b060a17070503011d030a1b0204050708180c030c04020c 76
    0x282c51079000d528041c80c0c0c00813480001e8010348203d40b00e05080c050040242401e003820b410880c01c1454443c0c40c0e00850210f00c0c0c90303c0740500d05903d40d40d9140c0000103d03507400c40081001e41c0c5c507808024003030021118503150410a10000c1641760a010044a1103a900800718869450a550302d9500c20751147c0b02200c0150746a039030600c0418035110015450810076159510003054520402c07109903510807002032203400500042040c1c200710030440784140d004542005101d512982c041c800301407000300e12420303840003040c03942d500c004c0e407a2004003580c09011055a1503c44004084c01e580090200820541d440004240040d59221070701e41c00c164010f00100c030050f192502c0c441442d1106030201c20513030007150104004d082c28418825070390b0b00070800354500190134184a60346d100310708500080101000c504014901c0f5002002c00741c03076000300107100d10304010300000e041010030345240d158601500c0008400e680d00140340c480d120360181c040c21f0070a42d40c904000094010401c810340d40d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 904855008 1250 904853758 904853779
    0xc060a05180910180903120b03121912090f02040f09020301150915050906010c020111010e060a0e1507030203090102040302090c0d05010519150509120106031e020901090209 76
    0x640c1c84050580c403c0004070301c0b0820701d80c645102c0b10004107400c0c4240c1c0c002454115082c02007030b4407012a0450101c0c07a9404244081c070203010a242403411403124148010104021461082620f10040800c4082c1e40f0030b6204c01c40102d0910461f00752a000a00002401e483d9400500342604038403510203822600103040318942d0007107401c1d280d50725400c4012040d0306c402449621254407508400c2c01c1d990560360070f0581000c02054851101078801c50621248070001e00c1160b101300c10301484800c0c5035000340040c03400780c0481a500c900646400702c0041c200f500c6019a110001403000b4070040f60411005d16896044080c0c0007235202818440d107a540810010000d80c03600000c260041b910018200e43c1c8100302040d0302d00f00c40040c0c202c1031080091a4507020041d802190b47c0c000d171041c2200108410048090644051244440107900301102c800c2c041140c2106600610449000d00c41e000811b03405803e51540d441d20080b0000e50046085005200b08903903507024180c042009460307481d02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 904856115 1107 904855008 904855057
    0x3020307090209030a0f0b041514162714060405030303150607210f092114250914160e06030a1d0c060a05 47
    0x1901d8020601d42000c0c2d1301030110000340756102010007046116468180059002110f098441c0036200c0c0e81002d0000250046408010082041079519600d00340e4025080300c0b8001c861041080391400380c0f5901080500545000244c1d800030100c0603d40501c01210075041d001d00c5c1c0c05a0824081007046407130000070307a600312400c140c28080c0c00207583d01141e8540600d080107008044003e282c1a01003007900690f174203594041d52001c010900d03039902966640c0180c0b142e0b030744182c80300c00700094188002100b094120312403050b560181c5201c0346100d18204c10102e0711300e050440000c00c425520103200741c100051059480c140032017541c0008611214000521944d150f90f6030300107540f40c0303d100302481032101000514107512030424410180c02041c5901c004402690040c2c0d5000100b840001e40c0d2040c0d0f44000c0000e4581604003400312102c0e0044030704c07070516520345c0084d01c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 904676258 904856115 := by
  have h0 := BRFrame.cov_init 904676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 904676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 904676258 ≤ n) (h2 : n < 904856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
