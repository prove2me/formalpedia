-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5537
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:11:06.16999+00:00
-- url     : https://prove2.me/submissions/d7e6be58-3f2f-4063-a03d-46da07525f1f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 995683453 ≤ n < 995863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 995684703 1250 995683453 995683457
    0xd0f02010e0913060e030730050a17040c0504151d06090105010810091406130e072606070c020901080f070905070203090301060305011e0b13090201170c04091803 71
    0x100f80b200055041e60110741c40b40805421a410140750f540c64000d582041c121503040c044000d864001030015480d8040b100c1d105a003861800c00c07210301c2c1c00410307081c001107070000582c1e0f400c004103080c0682c0ba0000310241070050802e2000000904d00c0c800d460096202c0c2641141c1a40541d0b0000e41c40c00e00401d008900090400f10b0326440c06004581094019003030340220140c43d040080c41c280244136518100d8058030140301e0a1818500304480e82c82d2043c2c05032a900d0920b4140e07083c1403004108242584c10320b40d00b000b8038070003000708410841c0c141c00c2820300505c900d030b0038440c40ca500102c41340d804600c204d441036450fa0300c5001142c3c6402c802d56801701140e000740000e118080d0990401640b00d086441220b0a00c0e070210b001074207481c0316900981b0b580e595034494144116a0071942c10b190164000c051080c0760b0113201080302591900d40400565a8400d104000c680c8140481d1000c000d40181a01140c02c1058907002258814070441c08858070b4940c032542d18540d08801d040d80c1d00c0d059 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 995685953 1250 995684703 995684731
    0x1150608040203030313021201020c010518160905100807140f0a0b0a030b040207050d09030c170604020609060910030608100504030c020f040b0a0305030d1109100f0e0d0f02010e09 79
    0x10001b00309120040340c80482c0e0201c654294880e04c00784c2440984601224180040b410b424200c040c0513032070600300e00070f0109420070761042c560714a42a1428049465002000030aa80c856010308240c80c1c107500080d449000301c1d180043c0c0004c1c1049010b2030340f0422140304152810120402c85d030143c840c0300e012003114040c8001d9102d0382c040c0e030001c4101400940094505a02980d90728201540040503002007500c90342c0500070b1100303811960010300121081c0342c408000c3ca10341c02d035a680e00188024807071000001d4135022a01e0b0306090300e000050190455104a1240101602030b08280c040d020f042c0c8202030308901c4440007405140d0080d50192903410410352a9028070588112a10780150443d4441c40c0042c503035102c10b00b14600543c007400c05980c88411604410f01035410056516080703007410302800310b03140c1d1410042e540300d28450802c40e001c81c5551200703035400d001e02c60030755a011603001c1900d4107100c5c2801c100b188051003645d9072a41703124000c08020141d8000d5503100d1a100c20 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 995687203 1250 995685953 995685961
    0x2120a1128090b04090c02100b0f1903120507060c0206040f020609040b030303090f010617150709090618050f0103080d0b0d080310170d0807120b0a08011506080402030303 75
    0x801814400401c6280780c10700c401520341c401501180c2c443c0d4820321401c1e0f5104100303480141c2c140300741c01d503201e080c04040c444c44080c000022807030a91440140c0c4104000d000744401c061180c0b10640c01036a003e130404010300c05840003c1c1003a040603009480c00c90500c12070450a51010450303078031456014080c0ca43c00a10f580038401c6641018400310b420a03520548d240700c540c4c080000d184144039010050201e403800c0200b49007941c8280e4031078150401078070110485c020000c10300301090303002d80e0b842d0302d44c0b039840c040200d0744040b490b4000040c0b02d240c11400705249842c940215401d012621051080391102d0421540c054402d10015117481c0c400c0c003643c0a04c400c039410500240308003c208800701242c0e0380300c00c0b401c1d80c8107a80721600d801d8510004c102c40070310860190810381c4424040c02200103001c0c0c003e04010002400d0400700900519003084c20246940b0803052030310041d0400305056100d1684074000e140a4482c100c00410b112800500d46115020891044e0750107800340d821611 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 995688453 1250 995687203 995687257
    0x1203140a0210020702041e060609140604050105090109030f0b0106031d06040201030e030c070e0a0b0d0317221a0a020901170c0708031e0708061f020c0402120a11 71
    0x50038100d038047d0301d505a0000d952401c282102c140021800e0009043d860190058070300449a445030240c003190401d01d181503900d00c81078a0403200e0a00300166200c209400403500b00901d504001c044c001a00302d15400e110102c182c15042c1d070707160744003040111040c1c03030703030a0f103d4540f030f4140078559001000280040d40320b034004015040e241000c0340d081c02d1140c0e000301e00708150b0b900310090060000003009079506050040100144050b108101040c10a031401070507a02154098664100b00034045005000e20740c0340031011084804219014481a14090107406824400e100303828001da13001c00e10b800e115108075045414142c5444900700903034070034891410401424110580018060240819154401035115520301907081c146004000400143d407000909020104140241080101d449080410300e049840d60310f0000c2d00e1882c001d04911304a10100142d41007400801c06100c90b0a540c00620300034000c58200780a00e1400030741c045100e02404089000b04402c0004813403c9030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 995689703 1250 995688453 995688457
    0x6062e1202192c03030403060b0619030f0e0715080405100e0f070b0a200c061c1413030f050f12040303150807060f030b0a1203140a021002 61
    0x804100016042c1200040e42c00d005040b03046428021503407026500034064540500c1c1010250b4002c203615000c0c009201103562801140030082c00c055840d05280215070302d500c10340343d424542c00164400441c0300000140a050f415040d020740c0c50410014401080020500d0340544c1c00129400b00c102c11428011203248001400907034840c02407101004c40208207004042143d030580d03006003600000006031f107142c08900d034004840000103002501c03c0710390240d03050402c078905091688800381550300040c10092201d1006902210008500c81d01d1071101c9408405503188220801005400a405c41030b111004c54140900f5020a000348000070b000701c000040c084010300c0c10606104038010991040e82c00020940c0c400c081000c104010154940034444403c820109040c09180c50030044503070319080c5000f1441441036007030704a0f0f01c55101e07511144010b00010020a5556030b0380c0e64200049051750011383c000740300b0006826181d0903103c02c440919480754000c048804034609c0240c029 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 995690953 1250 995689703 995689727
    0x90b0604092303130b03060609040b0609210709092d12180929130f090311030715052203020c0f030c13052706062e 51
    0x10501004212140c0d1240b6144441201d682c000c66550302e88003800c5240440e242d104000046041042003039a131501c2003a1f0700615020b440214000800b5070005249000f90020150440300c00e000c117216603080b0b840c004400b04000c80a84004503101e9030080300f95000c074074018046010010202d80b0740f40707440e8032000d000c901e131034500c05c0900c80c1695040c2d03001400d503006034001051203452502146900016070f0091060800070010700c60010710010020b0f0907041c010104d0b0704044103a80700fa40b5030304452002d03000040010040440c1c0811202c00a100301c601c2500014202010207803007000001c1180d10998206040710341450003030426201400006050010024060000745030341e50700c01919403107080c4030b900a4030b04e01035200c0a1080003183d11183d9842980308082c0c3c440c80d40c644d0300c1594001000100042041d41c0e0300c0303101c9450301184e00c0c10000300120356920864412030103d802c0740a0482150980e001540300e28518030350001540404500543c13401c1007054240c003c100b10111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 995692203 1250 995690953 995690963
    0x60c080c030a0f2703021915050307020601150c0f1707080c060a021201120c0302120c010f091a0f1603090326040b030402030a06060f050a0b07111201140c04051201090b060409 77
    0x70040e125066440408c4540c030000c004030302d0110610800d941c061011601601f11185186a080f403d410f0051003c2818180034103035642c61030400e0180841c5241400c030082004081c0c95440d5113502c2d00400350707804520b51010a00900f000301b000d000302c90007183d030748a442c80c145242903400c0030882141c0c1d03201d9071804c4074200c24404000005032540c50710300801302e1a540140101045e414000b40c2211200e030340318410882c00607401d20842d585080c1c800c1c9140380b00b00c40141c850010000300c1d5035500c1512a08040c5020144041c07042540c400700d03072010780c1c0c410002415803a1400458081110036085483c00c040401c1c00103000203030756000a140e001d80010b080340e841c010962244c030100c3c0c805030014890250324040134011403c0c10f60b1024002c02006642c0c0345070180d03036210040340340ea5800303006200b03020f401000c2d003c00409400c000c80520f034a910a028a041000450703290380d01034400e0b6405020007112880094406102d820203040c1c00030380c018616a02c0e1004c002c020010320004980c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 995693453 1250 995692203 995692249
    0x10510050c010e060f0103021806060307030b0f0a150215010f17100906020d060e13170f0c1b0103020c07140103060f090e0f0303040c060c080c030a0f270302 69
    0x31102c3e00c1045a18040d40340c20700e6805680d4198010301614a0392081e007007008641910078004940c0f00c07502120350100c918540001c1044008001452600d091000c01c2d512241c41a008034100c409642c4e40001c0304115021200203a06130840c0d11000d600c2442611501310070100d081001c0c07040180070030fa01d103581c08283c840c080d00d0251002c084600e058000d4400690200e071030b1622172128850303071014011489120307040d40750040d1b40310b42d020241503005140e034189410f8841502c50840540c0c0c442c94030404501d460381c1e14009e0203030381d0381c0e003c0d542c01a4980440c001c1e61034035406442100c4c9600c4840c000b4102d003074145031892101c01c0200e1003d904041e6141d0002403060152078440000e01700d1300c0e401084100e204041e0798038006603d007507010603030410011f200010f4542260b0a08556a6040440c080c05090401204500a0070664415800b0014480c1c48040d030081d0101c0e42d003a526140e4002c3e841651140040c3d10010460403c60917a0306103007800589010108083c10040801c1985 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 995694703 1250 995693453 995693471
    0x411040801021809060f0a050d020f0d150b06120a0e100c020105060310020c0d0e030109020a06020a14030c19060906020c06070e030604110904050c120c03060f010510050c01 76
    0x25003264040b021840c00c054418800707081900d807600240317400c82d1007220265260100e5500041508219216039407080100c21521011510347c4010b103010741d0002840b8141034002030601c581c078410400c0f00007850301e1a142400100d443c0480a807120380c2e0b00d802c1d20a0841d912400007900400402c0f40842c1c503441507840078103544080340240071117501340394004540f508009003071516000304001134a107180d0041c0109000ca600004a402c0e0301c1046103085031032149200080303801094202c034080d400030140200480d150f0b4001a110f68464400d00103070240407000c40040f80c0300d005084040c8039503000000c099001e172031100040c08070103009040c000f503860542c1e9251800ca9100c00740550b4036400c180b0403c0550390b0000d40c4500c00460540161405141582c4e61a05128135480414407512040700401d003889020048000c8030003019041096203031424084564440d8a8102140b00c0e100301c01c001000f4450407280d4904903040604201144800113000f66481c1d0002e00180909660f90b503000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 995695953 1250 995694703 995694719
    0x409080319050c0901020a08071b0f15020d0e010e0f0307031b0b04030f1e14010204050325060509011206090902040c0f020c06090f040608030c010e0a0f02041104 71
    0x46000303203024080c51100c0c0d07060200d480d064a0008040840c200c005000b11041030341c0200304681500d51010449a840c0010714010090040742000035078401011000420000c1001c00c02d84241d030f810420b2000760b45042201280d4400d206400d0b1000500c41200141030ba50090320740303600ba0117008102c5601c0420a402103443c02186900666600d03552142040015400e0240007018081b010201c616150840e01c9800c803085405500809260300c0c05411188046610b240551040e1720145442456116904d0907010b90000c0c06903130301c42d01405c4181e181d02c0014005603410344049025a5046070301d4040c040d9441d07001303a01441c1c144202d9450314071443e48288110800341c20311060014802000e801400100c0750841d054000344688180380050198000034030014010044917a07030b071782e44c4050001c1000400c014850740c0c1c12a09201004c46c1201300480641000c04140c0000c003c0801c1c5006010798401c0307000e0014052202c0d00c1d040c140541030680200003250480c0410301e203020750f52021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 995697203 1250 995695953 995695957
    0x122a0905090309040605330d0906060504050606040f150309140619090b1807050301090c17030906030a090201090302090115030606050309100b0d1a0f071b060209040908 74
    0x1030800d99080081d5190b020302c2c1510810703004c3e2100765403070301c0a1901da400d019094584030b91381d02c0001040d44010a030a0307d0030012101803440e59101800301031000d19045000d000075025040c0f20310b003000005000781c2021019581200c5490007a400324074902410b60048024501c0c4d158101915a8851401b085c00b10b000b0f10816000c1100510007032800c1d03042c00010803107002c01d800000e400c0c441040d0120f05030b15030303042c0c100704c80703100154812a64800c05450095103900c1660107508003030840d01401aa007050704211501480c2c0f001d0700591060303000351280f107950f0820b54400c90600102c0c0900d5025030000c2d400b6031044c10500341c3c1d00c0d01e030340010310b100809901c01c681c1503c0f20301c1d40c0c41306a580350203084010022400c285046007000e46a01d5240d10040c00213000680d9290141c230500e6031514080301d16241c001001402802d0940c1010306221800c641a4003031240b014040707000c80d4031518183c0304188000035807945190700f40d0351344000783d48580100c680c45919a1415000702c0c4030080 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 995698453 1250 995697203 995697211
    0x91b060306040f1e0b011b110a081014010f050904080304080903161404090201020d0e030a081216050c0606210d050c190512210907060306122a0905 65
    0x20708004001c60301142005170f940d0004101d042280044040d00c8024a444580c1c90303055105031000e1030210800c0119640c0c220962040c0c98500c03400c121808400aa94010748d0900d00301d441d080084e80e00d40c02115051040d0340702e0b0b540c00c44680400a00803481c0d0102075908203101c1d440042c0b420591a000a03d030100302540f1100341e000f2443d04009c800d02c0021081c0300c40e03c00ba40c1c00e00600c20240c00103920b0b1804030346c0e00406c1c4944810409034681d0107104108106500c0107100da00ca80002c3d040c2c1c000410122500d008004039142d0090300d4900070000d0f282903504110040c0240e41e0740500388440d24603d40300c0c00c600c004180001144a020501034494010b5072079503030903110698811183d1501c42d1181c40103200140d040c08400c080740d0041642c00203950102d980e0f566804070428000c071a9007801c5480f09081103000240509100081501740c1140d2305075800344030080d1580b07000c140002c2e0242001b040c4041e03264a80e48021052000b4640e20b102415103044207c2d0b40300c2c04002990300460f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 995699703 1250 995698453 995698481
    0xf0714070803071a071b110f0423010b1c090c05040207030e1e01021c2303010e0c09012118030809060108010c02060a020919080d08091b060306040f 65
    0x8040f940c1141104c200e80c89085460100e80502c2c44444540ca415200207001c1d0031884001250325058854020500b403155014004002c0c020802c50303200d03401c02080e4103035107103600d20350300010b281a020707030580b601e48845800c650f8030200ea0400242c028401c0e000b0403907040c10503080000b040d07501d92000e818000d0103911210403096034101049074002001c1c24080c0100d00d80002a8900d90f4005004046400d8540c485042ea4060500c1135441418140080d9101d4002c86901c80c0710080301d001442c1258a40b9030600000d4072000c4601c140c5020b614141400a4109050004012a40800e610b40002c50200025140c3c0c04840504c421088120301580072880c10300a01c0b00d24002040001d00400f51203000f0040d1004800b40252a020050000c0510f941c005c40c10090a507189072036088410380c0c4001003104582d9406c0704684441c104400038001c0703442c000c0000e40380ca40201e811060801061b294528100c504410854550005040a034200c2e58a40d2503d2801c14903100d100f80c03142c00c2c8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 995700953 1250 995699703 995699723
    0x90105090c180d02130203090c01050a0f03021305040615031503031b060f0f0221010503120c1501121407320d0c030b221205120c0405030705060f071407080307 70
    0x44103807460003004107407481c10800f00700040c06006512010dc151807240074603000da590742c049004590301583c0e98200352741c001e140140c0001d00b8440307898802c64040c40c42c0c806016501038100d0a00c4000143d12006c0e0101c0c26500c3c10001d412142003a81141031f20420000600b003941605d07040846000c4500703401e00316800680717034007150000c007005c03000d40c18098500781c900d40c10300020070788444280b064480350710408181010401c90a1183d4180b940c0a00419841c940c0e641455a0410315102e8080c0d6a40f25140714021104078040740324419030b120923021411001c103c4a0003602c092900c40000718481c5254104205680e40341d0001c15045d01a404211507503065052029410101a03c0700c441c43c04200103c56100024000d091415078104071066091402c0c020141e43d00e04c40c2e046032455901200c1d04110400400360050015a03d0650484030241c1d10f50040c00107911411004500700a01032088a0010300b1000d1a01d503c1c0315094103a03000356944982952450700402c2c0c04079001016 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 995702203 1250 995700953 995700961
    0x10614030c3001170303100b030c1603090603050a091a0a09050f06040209070f080610090509040b15040b1e040e0d02010c080a050423011e020306090105090c180d02130203 75
    0x1400c1d100001c132100e00030207107165040030b00c002c2c910020f03031303210303880c08000b0200000300d43d07001d0768003a510700c9030603aa01030020070030343d00d80100010010f0044802203071a050201c0c100c89130f14818aa0001d0703009040180e03640103910050b011140052070b1642c0d4680b01c80c07000000400a01404501f600c10500401c95801c1c11301c1003005090004242d08100b01c1c0808c1003100142e400001582c11603c1507810303100303440381800200c80d52409500200e800450301014041042002c60a19224008011032072020008000c104019103100081850340860200c4128994500c801d1610003010801040050076442c09414981420001e50558004d83d65640210301510340040519a0090040c0e904000a10b0f042c1e44410000388460010f40d500c0c84020b03c0c5541020095200c0c0d14201d140302c61010351840c40002e1800654001c070b0b0024010f8406200000c1c041c249541e10500078840400c1d8a42007000c1215400c1c90311914549140d80010090181c001580314100c401617204000b610240ea0380c90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 995703453 1250 995702203 995702219
    0x320d09080f0d08010b0a0207030812101710241d0106030b221d0a03020f1501050d03020c0402070b01050111070b040603023708010614030c3001 63
    0x3901141d400c0240c100468022030710354058210340c1515980e0b462181c9a40000038100d1901c0c0168000401503a800101902420500366403980308442d000101100c032a200da401091810401030140216403210309000f03914084c1d6040440a01c00c0030744420345080c00050030b0f24003008140c0c41802c802c220a03100d07480c0c030310f0281080c50140080d03080500290050300c0108803c2410100b050180c07210700104c05208503101c1e008840400c24940c40c2d601d14880341c52250707840d014804000c0303025124219903c1404400440d005952007848040401141c0c60002805401c14007020110114020b83c03c3ca01301651700c510140100b14050b0700d00d600d0540c1068009040c212202d020381d4040d5201000400c500c0c1c03030740740480d02554a41c2c6000343e120700c401c840124825002d011001030020070380501029100f110b84000490280039071300d06c0541c1c1d07682d1605980e459101030400b1780968040001481c18280a4010880500c2e011320644021000d41d2094542c440200f0900302070700c0e007100c01081400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 995704703 1250 995703453 995703463
    0xb1e0a031e0606080c0a110d02071706090c04021c0504030507020f180c090a0e090a0c05150f090607060203190506060a080103021002030c030d050702070b0403320d0908 74
    0x30075032400700301003403c103031018110b40700c010104900201c00043c410f46051150851030034126462040b07071040140203802a444984500600b020354400e144415188100040d8190103102e00d50082d15105280e401444080c1d44074600e903888042c0a00d01c14400c0304264450188540d0080e0385030340d2190b04500c104600c44030b40c003080e20701c00c0e402c01f0b000d4480f100380008200d40103140104083c3e5a030142c000842c020700000c0d8081981d00d950b690070440c0c850408110900102d2107410000e01454a1f075082041041e05c0c015800c40d510070a12000714209170410081c03a10000003882282400542d580d05010f9a0085841203055511031403850071441441c013070a90448001c03540c0c1420110150300081426905100181c17090040608a09109000b80704a802002d4107030160b035600c0706003084c0100034200c01c0d6004001482410307400142c02076214103036829a0307400369159520007600d0451520012002c0c07861440421561017000d074042c010001c2e9040049141c0307036104407900c0c103190a4280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 995705953 1250 995704703 995704751
    0xd020d080406020a031b150522060516080906010b0711060a02010b03010b01030b060d18081b06010806040305270406080c24040509130f140607030c090b1e0a03 70
    0x3180c07810321b0a5001400c0313404c0700c07807030301c940080f00103880d1703540c5214814400c80b08440c460607105000800024410302d50015845201c00c0c0d040e1540c00505000300315000f030821668422903800120061007089100e9000b840c00900a40c11300700701498803c0001e0003640144000c20150307541c0e02981c41c66090a0040d00218042402c0c02c20038224158042038851050030130450803c0e5036401000040e40c800104a0300c50390b001246c9035120304160804407150103503070011460700d10503940005402c100000f59240b280d030389513030f40f903062600c42c000c0d0400c4180900c40041120b07089000a80302074607140320348802070800c4002005c0170800501444021800402d11161403034070400383c1940780d1003d00407101115000d0381c0c0100d06980d000d4000000d0001e00c080140460003010128080c0b200b038100d04000340520304184c0d007090700c928006504940e058090080461000300d4100802400c90300a4890710286002c0356200d071056440b1108581e2002d18400003107690f48240d101d6000c1c5407078001c801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 995707203 1250 995705953 995705987
    0x102060106180302092d0c090d020307090c030204050915010f032a0810121101050f2206031a010207050f06090405160f05070b16032405090c0a08060d020d080406020a03 74
    0x3982007c440b9010103100b014aa5401001e004c04d6510854804010050003480d01d40e40410000081c820020040c1d803103840b495114628000105d03103003100d1440188003542e0141c40b42154485203a000ba00909401003407103920300f9400c0101a404007110702d5000d002c0503d0755590b2054501560040240b40854200f01c12403013031072810360000f072070300e83d00c40c1801c25007400c4c0252540d042441001c840e200c1c04000c0b040c01800740c5048110003c01100c56030607101a601c0601500c0c07041c0c0210500c12100003c00e07070059000410070015414004002d00440b40c002d480c2d207107404d4103c808107060b0381c03042c0c82c00b040340c609600e500a0810b90010503000b2400703151508518010301e607150f40704040b03405031904800c2c603482034401200074001ea020101e1010100b002c807400a041a00010700002c840c8101c074040c4070380c4000102c4d102c004004a03100841c807525901910303116503092100b00c0d10001c800b240c02203600e084180203c0c454101400003803489074000c0c440d1407058600100480000008555 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 995708453 1250 995707203 995707291
    0x3050a0c0c11120f030403050a0203101107020d061130010503030a08090703060e0d080105150d0506060702190f0b130b07050c090c07060b06030105010206010618030209 74
    0x1001611000100728080b000719072080364040a500001c0c2401e485400b85a16840001030002c2000008580340081e01d00032810341d4180c070f1110003140181d4403907000c0f41ca103000d02004101c0041c50031881c07654260340151000100740340306240d00084c4e039105807400c840211a490001c200386030401c000c43c640792042000018075515103000b10b503403402030383c0c001c405000d40500040c013039420800140c7c005541082d07013800242d400d41c1a040d01c888441d00c000d80011800b00012403141004143c0c00651040035069614100480000400502001e800c1903800082004400056a02c400c3c4607406500e41e8a0010303121071400010080c2c2c0c0141d584103165001d4203002e403018800c05800380c4001c4681d03810030305507106514a045402c1040c4188126407005551007031103800403070b440c05402c1d0180300b09820404c0000340380070801140424468240103038081c0c00140321480c8034244e420032240d804c8026522554807540000d05c02c250880c3c0c031480129104400601c80640d08044880c41412055001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 995709703 1250 995708453 995708477
    0x902041505090402060c0a0c0303170a0e03090609060d05010807060f080609130f0f0831150507051b130c09150512011403010c080118270303050a0c 65
    0x280b0601c80100041d108410110701d000703d80a040c49018809030340050300588542c0c5a107805404031040d07000346100c8160f0800052042c80407889a40c441c280b09100850034142804104480c99001010341ca411480c184000a40310540d4016140604610b0002d402d61a0421380014800401c0e106000100040001406101d4450b00d22a07900b0800d0000702d40c0b240806410718003e61603003060002c02030030201d0948820300645201038112102401c01506000c42440240c06000d82500307600420078120300d0081280c5a2100e49030000d45c0e030a03045c154208940c0c0d880b101e0801c43c0540068903140c00c44400314009181400400401015514081041078002070f0000d1124829018801c2c18581b41b4600c03024450040c0103441102c003820b00d0a44082d0b0b1580380c00340d4610400c94003240a5801e180071842041d0061030418140d492441104002c00340700b800b060084c10104030011700d03003209212040003441042c2652a042d5000b520082990309108405004840610000e41c081200c1c200e03104c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 995710953 1250 995709703 995709709
    0x1207081302130e1605010206090c090a0225050736050402011e0c02031234060f0209010e03010606021b040f090507450e01020d0902041505 61
    0x40141d015515030040025904a81e401445a011032440354070407040c00c440780b8000510480e0558100fa4240e52064039200100340e40c520f0340320b41003030380021644001801034081d60b01901001e4a800102c0c201c45903403542c0e910882c07943c100305035815080010103103e1303080b60300120341700442039004114001c40c0c48558041082c9910381c0d0003074004d8950001c20250780c4501a078005008071045442005134910030050302071010500120f000f40240c1034103e004941c0d036410f13154200c9401c50008440801642c0c203416010034207034415031201000d007803800400d01500c100b41d4000401480140e941c09504000740420003500b1001d84660704010050204541c04101c01c0c01001c0c20464040281390024002400f501e0061101d1044034901043d060a2001c000340036011101d000e40c0790314103501ca401c90040400c0d182c60110800704151890003070324403005082c40124001c0d2020000d41e40c2d0480d041242681c0c0700c00040c1c05800d0711070501400750702d00791140c03d640d200d008405034805480c09000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 995712203 1250 995710953 995710981
    0xf0f3003030509010b090903090a09021911120304150f0e10020a11011a150310061110060b0307021203091203091f02180f280503070902120708 63
    0x10040c01c054850010a140c003030250480c142c298001003081c3c0113844c080881d680d407900000030b410321651603010000f0744042e41d4800c840300c900c4e84034420b1125100c4ea02c416101c000020074654234510420303da07066018041409140110b02c1601e4075520a044510030b61700365030b1040058100039140040005003404000380c000c1c0c513040a42405a100c0d0380550f4141c0d03c042028000c0750783c9500380040031100d800d80701031070b0340012000c880c1051011005080c002c0725020031107602c00c0d500302d581760a01c4030351702400e11106184a00c500f15407007104207100030f0703003070354825880381c0d00d84c040110a011038103405000e04482e940b01200303500d003549040d80c90656244da404886a0120800001282004c0800e100f60891088602c454440000b071808103140254007505c2e00e02101840e1030a41c51091a19819400c20420b0003050341403400465004080004040d20035107803408004040011191014841c0c40002c4c02001c60040c2c9600103100714410f01c40b0002e00ba81304012155081061040040304 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 995713453 1250 995712203 995712299
    0x6090706140d02041e0e0f0c1612020a0201080105030a0c05191d0a18050312060a1214010509070605030103110307090204122d021201060f0f 62
    0x1411000c1c0740681c1070120158400c4500800d07405000040110306100040d032040c42c00441ca0040b50805a0341e54104c40004005840e00840036004601048003220300f44083e10990008625100700c00940b65521008003400350f4084016800c10b000040035980c10441a0380104000d40c083c0101144650342ea2103061a24055140b04245139003140c2d02c00701085207250054108a00050450880354001290408040301d1981100d4105035030440002480310f605129079078000003c2d800e040e0a03c0d8014038841000b84040d03081620b00c400000c0c03503080e08002e5980c16018840450b003511080003400c3c00e40d0001407003038031141e010305010480c01e030b44442105d044a8014089a00000000c0c0019040c1030550b404014400c1c00842c0114100340e41c3c200c54118540f14608500d000c1d0345030b049500403007a05601d0b07441d0b0a0403e0a500026003801646a01072101110002a1064980c02a0880031851741c001071100411210180892820a24680d45c18258801d040c00c07030094807111300d04011345400e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 995714703 1250 995713453 995713457
    0x30702010318051218060702060301123206060f0a05010809010618020405010f08091b030304030f030f02060106080c07140327011215030f1410050f060306090706 71
    0x1034105418070500e6034141080d40c1e40303c402e81d11510006a410925600544101504801d00300c15402d041e02c0c05034200c40d003c43e406410241960b00c0e0003600080580a2581501c0c1e891149000200030300c0c0100705c00c43c4600c84842c00c020049900354500c0d01d01407004044c240550f0303004240c80d83c165910180c003012194246010703d041da4810f900c02d409072003d44d0051140798107100c0420b202e403c5540180041d103100f031b42e52034581c0a00041c22a98120305659407001508201c0310070f0701040746a60701c00d418010150889207015600d07500c0005181040c0d80c2640041c004423440315481d0350501a5034010451494000418140764a20b8500b5124814004140155081e000d00c00040f0171300c183c801000d4141e2080c904500c130461400d071540304a000c02070003c0c036242140f00f40a035841c441c01088010080460718500c1c119510798400512010064504502c00b102d070444c0310604001c03542801d10001400725071410400c82c000c000c0c00015000e18401c1d0889020000c120000240d10001ca99844c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 995715953 1250 995714703 995714711
    0x30807081c0203071e1701150207230111060123010309060c180b040803030c071b0f08010b04090803130c170616050901020a0305091914090a0b030307020103 69
    0x1d5008119003a15002001c040035001000700600a41c01011903005007280220003952401007170400c551100030440410702c440310141c010b00940d40101004050311180d0f00484d0b90094650401c62a00235901403001060b02448041d103100c1d580c4481d2800d06246244020003055040103082c49081d941c001400031000c90703001940c0c0060b8466000b100d031490b040f16080100d200c00e180d00030102c1d14000404040ca5000440000301c1d8203800084504487e0120055030840c1c55049a0208030342c070000d010744000d182c10005035601e440124850780146140d450328403129141401d13903401d6a0400c40d40c50720942c540785004011071080c00440b41e1225409138540180d001d540303040c0f030b03921042d138101c02c5128040d030b03817500d03120781000400e20301a00c400880950400e055035001c817028400d610032030303005070000018a000070340a0340c0074217011040244030314070803540705104903050704140d4000d00c3d2017a0300300c04941e0117040a0641a40040b8a17160071701c8002e40001c00700350359105112009040580e9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 995717203 1250 995715953 995715967
    0x515030a060609080d0509150a030f0c18030f06090b070507140111070303180503180111060106092315071a011406090d0f230705010c06020307120e010c09090603080708 74
    0x624034017448c4030105042917500c03000e1400c4014010601d05174040c1000d86400e207006015800b464161003150251100d50401034190360380c2d0711007149144012509180c5a4564030009121075401e248264071a59a941d11600241000c2d2085080c5203081c40741a4034059084080000c03080840c0d4030f46815080128400d06110441c1080018011024045000102c1e286070141d1a03000320395050282681c4414808008041e6140c42c1d803020b20628002c2040400c0402052480f0140b401d26003000d602800303807610500011886480c1041d0310f5404010b0300240365002c1124114005284406a4003038131081d6040c044500100c0d00420520b0b84a01c001180800b52036031801040b82c2101d0b841070603115010b6145c6014204800710300384481c1c03082c0035040114050600081c8510454005942d100c00210b075030344030000203620162194080002246034000390f007003180903200c0d80c0c191070400050f40c00158500284034000b5034000d50040340c1010810000302d035940c0c0a554010390040ba405940c0c800e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 995718453 1250 995717203 995717209
    0x120b030a02120615040203160e060c010c0c1515030213020705010f021306050313110f030a12030e0708070308030a02160507030b0f040b0703150515030a060609080d0509 74
    0x801400035400500c00482050121000c41c0d0b8902800303540d501a0010303107134442000207030f0100301c1e28030300403507151840540c41d60302c00c03150244e2450002d01010b01d410603c1214a082d180d00c112100c5c01710300300e84914070030400703102500e242d02d6040c0901000721003003102c1ba41240c12020b20000c1c0c03042e00c01c40d02040000c80c0d2581103030b10310f9500100810802a8040170340010b500a44002c00400403000c0c070005607940160b0444e48030784505004d8000f080155580d83c4006900c3c10160340d040100104005001c0d10108616203135280a50b140250001050b01c0050070303540409001c4810b9041a14108240031000411009682d44106426101d030380f10390b0310760020700a410240201003203412030b0505211010810740f007564010581c6140d190f982e658040681441503a000b0912801e480011310603500c00e91110311138030001510304a0325540c900c00118104013407940c0fa10b00b50400024486070704510301c03600c0300500b040d00302911010320b044c00d881c2d210210b1210038002e014000030f0450607a6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995719703 1250 995718453 995718463
    0x2010e0f03030c070e090709090c0b070606030b0c030a0f0c0516170f0c060c090108060d11060f0901081605030f1306020d06060f031104170a050a14061006120b03 71
    0x254110485a0301079568183c0420f1003011b5a2000c440d00888002180988060040c00da07065041081c1c080a24038002d0b22000542c481441641c0b04c40d030f900d00100006009040c814002d0404101d001e031a42001c044410032609554412039103145008698900b83d500241036502c1c040950284200c1003087d82401d201c0d141d07986c4c3ca02000380034001b403264100d0080070050074901c03040c00129106581d6807280c0b8a07051291000c52400702e0203450004500c6e10700015810700c0c007031080442c00f040f80e420f2404070320245c0050092902c030326404a49400c0381d5900580c0641d101421b480c0705010134406020203881440081c01c12240350347c0740d4000442d9140d01a848d400740d5948102c0466480013280603403001400940950400604000c503035001d4603119000d010002c01c58110024901440c00071001c640617071041450045000e031010420200c1c0c424030219400368011241110741d044038428045c203000c030081c880b104141404201f80403542e8400300a11a05c0100540003807411002c1d40000d01d05 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995720953 1250 995719703 995719717
    0xc0a020a051204030b0906060d081b060403110114190203092103100503030901171009110316020303091c09080607030c0210060503060a090c0f030302060114010c02010e0f0303 77
    0x18403900c1121841040c0a900070300442e401090001c0d015190703001b00c50380340c0030142c0f1000e0f400034008444101007080d050090070f248854281e403003141d02c480640c1d14141501142d0590206904d5403002034012401c0c010100e2205900299071b1007480d004802596840350076141d0400e1540c040000741c1c1d052020091981d50200403041459011025020414164011900c41c035540d4000380300014030b4200003050341c1075640d058442801c04070180c030784406c1e240c10003010200e0f0715484003000030385803c0c54421498060418488243d0303a00d0316401d02910440031070091800c5505c104200202100c011801169407007080b40011119981c024048800c00320741d4102031b0060050340280701020782c041d0303ca00407400b66034082c0e481d21004070100d80120780c0300b441019059000b903000102019407030352003486494401c1d4006040c964480b090306860454540044000d64002c40040c010f01d6800048220406000d00e001020103025a000030007280c01a200e00d406510500070049490307030103105070380030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995722203 1250 995720953 995720963
    0x3040507051e010f0905010e090a02040b0f04140901180c02030f121015020d180b0a020d080604020304020f060703020a02190609081c050309030f1603031b02060c0a020a 74
    0x1803248078804508000ba0041e81c482c0800c402c0e90011070581c0c011040702080f203005844901407180d1f24401d0002c400801007292500c0b60707007004041000f81d9414082c1c0060707102e211200340c94500380a4805500c0c0038082c500fa10a0807100b004110611040700040c4042e450b6103008191035202080c00d9255020351101d440c4030510214011070341e84030004105115164103818103801540e00c81c42010001001004100140c2047c00c00d80d0985005d641c0d8080d903943e0340c824011445aa400c2503100642140d0001d1005070401c408008107140d0004413660000c0313080742c0461550803d580012004450703440100c0c00754801003041000d25000340b000c2102150013600100640040f409000c07000c6100e40910000b04086000c0410a50400a100300c45005503500d45e680c003005005003995103400080103c20780e071004000c3c0000c02401500a4191300306210b60040342c4500d28500035003540c0c1c005040c58150310380d0780b10011030180d00281d003036040940442003940d0364210b400d0490410f8640880909 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995723453 1250 995722203 995722219
    0xc1207081917031905070c030f0f0207030b0106030207051c0e100201020d050118140c09150f040b0a080108160e22051e07030c1a0d050a0b1507170304050705 69
    0xc020180d84d5035902d440b0002c480c2008107650301001038413050081c4d0030240004141d481300d1002680120108011901503004456009075280e8036840119400d070804400a50003251143c1000801c0100158103140c17030102182c6103000700c2c001098540403200d11407045124100f010304480c001e504540020340303801028010340d0785070091b940444001118000555103030110746983e031700e084862240140f40d055044c1e4580103601080202c0804490541c6080200130881c42c0b0003420548000c000500c007514040e43c03510f0039207602414040c0140d11580c0150001c0800e81014844c1c0c02c401400e403583d1a00c00c1065894104644990007038528420140c0041c0c0c080c65024040009204007a01d0000a0640e80e8420b0b150202c68544c5854032009003801d80802c82400001112801c0035049206d414145040000512605082d21020f8070034050960755050600d40c02d0078802568591400740c3c0c0e03480c03407a2450b42d548107040490540021204d8013400710114040200a0114100810005209003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995724703 1250 995723453 995723461
    0x51e0c0a06050f25140f0a0807151e060f0f061e03061706010317040e0c07022214010b030c16020411310f0b13090606020c120708191703 60
    0x1210602030008171110754864030003204a00040011890384165200705441d08246582d6104e615482e01c416007170101035210002520322440d4a03642c00c07040c90130041c000c0340b013920342036500c07600350190380004001d030800480c00d00901c3d42000d40c000c0e0b2100404103001c0c802940c1a030440040415070840ca05030000800e8120312070740009020f0781130701d003c4d152a5200021080403c071041c0f01d030f07218079030b1407050b220002400308491501914011340060130020000204010504c2c10020201c0113641842c2e80300d0300c0164580000d100f460241400545c65469402c05c014160142c1c0241104038961241851483c0e0071900d450b00f0110010071541402c0341c41e0800307100804240c400c15481d00304000260340600c8a107240d2458003104032001000c08420705400c00806001540c051340714100c031070b4401200010314103924800c60004007400d40c0600481042081008404144904c40035611b900106051211400108030f11040032040c114070100b0038038920b880e40544e0300030f0344910003449000c4200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995725953 1250 995724703 995724713
    0xf0d090804091a03030c1e030904020f0d0b030d05091009030f0b180c06030a090f020a0602030307480b0c0315010815010e0d051e0c0a06050f25 63
    0x7640249100c2500500c1d2401520f0a140d941d0203894030310b00040c0e024500c041c90181c540160f03416040180d07401da81c034144104012130266030106030202003a40c80052140d100f11020b03c80d4001c00841240503003410403c804004100c2c0c054480a2841880d4004014511501070701c00d06c00296030111080c1c1d5060000c1c100007000032811110324002d21550104a5154030b00400c02445004000f01080d0451305c50309160390081c1403402084602c16440e0755500c0250396064140401032180358021940ca223842400140980401c41c020320201b0012040e114801d5402000c001071407401800002c06440b2461400300305900341880a0401c103000000d1003040000e40c001507200d1140100b02201d00e0484c1c0c0b004440d118000c0303440c94022810322015004643c402e01d03500901050080084110280e01c2d22078504245000c00280b01141200c003074407109100c140a20080340c1c0e0201c40346440d0a03c4c10384040c001e0f1080c90702145803410f0005082000c04a0050310441d090440300114a03464040d20745 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995727203 1250 995725953 995725961
    0x605070c061a031c0914270402210601092003160801060c03051b010e030c0606091503060703051f062106060e010516063602060f0d09080409 62
    0x60b06001c1d0042101030980342c4030310b0007148a442ca803a0354048106180c58810518428400c4089520080804600c080043ca6800544005488090603126410584100803803034241b4441d42c1c11907200c844880380c1c50080807500c1411100342050100d52000080c140c80c00c00319659501e0900400040107004070f001d9605003114075208c0c1501c6500030390f40c8070342090305c900104000060001d44104000fa80d8100952041020401000004510301140311035043c01c2d50000407042c43c26500a50800c0881e10b1311285240d0032000c04602400d101d407017440404e44801e0014103e20074151214040380c1080001e8050b19000a45410345500e55600c4010003130050703861400810100e1000808080784032460710940c02140c01980720304960043c941d0054035036400a10301d200d0700040c0e4041d818046000d500510041468600bd41c0580b0820510140c854810010400c0c0d0035003c1d00d403000005880e41011035034040484103c03070340c0340c0380d4a5459502520007150f008000307040104000901d2100c6401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995728453 1250 995727203 995727251
    0x20a0803040e01050f10030e1204090c02120a0c0201051b0d050306042415090b12010515071e06021303060507030f09020f0103240609030c0518040605070c06 69
    0x40c00074944d99034030820518050310481298422500201480303118060786c814064a02d0130402d890242e16100540b10f900e8005501c2035100c3c50702c50465110460f030511205800020300c0101c07e050003d100790013426407102c140c0003818080001400741103038100301111041c43d0380020480d800754502800041850300284c4406003e83d0800b42c1d0b20400c0440804200308420508200f80031491a0805040d01400040502d07003d2215013400404d40503a26001480e48e00382254500a040d45454144010825071082c8500440c8081c09003800003414072808080b0450f401000c03212120150900d100244102c50090440200e140c00000400c1180e400a500c69007440d20304204c52102071002006031003100303070000e5020b2208854044075601950107008613090500800f08802d4005445055080058219401003100c402d001c0041198040411019200a94480c0c44410501407110036482c00900020017158403100002c140e03a11038296481702c9508080c080c407034a04100d11140024040c05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995729703 1250 995728453 995728469
    0x80c010b0405280f140f04030e0312030118060e280e030f0307022103040b010f080c0d0203030903010c0c0c060507050d1101090f061a040b100c020d020a080304 70
    0x100004281800204214980045400a032402044803483d118000d12441001c80365030b070b9a0343c1440d0105004100d070244250280e00d80403070f0030b003000d08018140090040d181c5109600c208640d1854910340b0b001c3da41101c0f4072012540443c154808900041c20f000d030000e620854002040121080c602c4331501c0d103041b40450311820551100c407044080c2e40480c06254503a603c03c00c0740090140440000350b6100300f5610640341c0d464092604004c003005e0602043c81e2641020040c002030151090000e8010460030b400e51042520348180103445114200700d95104800140080c015501c0c14401c07591040c60060080016801d41000640398161180081d601e2202903c80071500c10f000742c003120900d5400c0002001026030b507000485040d140301e094400907540f1000040c00082d03d0502d140741e900d1140d0404a03a89404480ca01d83e50409002d030b881c0301d58100040745a590721a86a030340b1241040b0700e080510440c3c1c83c00403801d000c1400f10000c0d008040720340c00050501011016000740e801e04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995730953 1250 995729703 995729711
    0x1a09040c02010515120a02090c04120b0109140411060913050108031b0d08190f0f0e0f0c090106030903050f0301030807020a060302030f151305072006040b160c080c010b04 75
    0x10f130f400d2040d941142c040c404003c1e8020405600545800c100c030304d038440886c900d0f1038501500c8506422030091114000c450f1000b40701d00510540c100c41c001c5500102e0080e00c4581c580c070701070b21a00c0d4458603c0004500500c3d000030000131070b460765444980c5007860082c2c180560b503034914245a80360300c21030f01d0072400800180e81d282d1b0220042042040c60800380e40300156515a000c40c5444240c4100c28014142e507240c54206145c030250164100d4890417010002d0a03100340d40c1c545007810303644142000103402001c0c2c0e170100c41d03440c140300c141540d4480c0390004510680f440c054646204816160080300b00c0440000200007106009000c024420b0300d400032915540d60b000d50036808280c4114ad000801d00c0005400c3c0c80813070804501080f00100b10340781d00b0b400000301b402210800e50304040000e1409820110311407484229000c1c0d06116802004107207042d485107651101d01400010642c44a10914040180305416103000c0d00c0d0050b505654440c2d4540c4100d000380010344910f4029428 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995732203 1250 995730953 995730991
    0x3040206161514070f1403060402090a15031401090e070b090613080d020d020d09050607030e061c0605030c150903150c03070801060c1505040201022a150f041a09040c020105 76
    0x1060460b828580c1d6084451b0b41181c55240402020350000600d09130410a6010000740b00703134078442c551006403490f071000100700301d075203010440280c1d05821030030b0303280e040c5034110140b03003c00525801210b050084507030701da20f00040028010300c900c005070000d852071080302040445000c15410000f41541d02100d40120303404406070b89881101c010760000c54094002017206041140040103124403a19040319815031690009201e5002982035078424813082200c4915080c10f40728080c00742108800414800e00520009204980c003600c0c485034080f0003281121643d2000c000f0101c022810240011680c0b4081145540d00d400803030f000c000003845900006400c0e80a03200303403411a90000c103840724408000c400c000c050031010303104070b045101c0c2250310752090204203040d603450210310b054100200d0107001003200c00c0140f980c0c0c034450307600108054031a807101c003411102140c46407803900d4002e10300c041c108441801030a44060300a07003402d02803000741d40d040d803007244a010005c841440f9069 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995733453 1250 995732203 995732207
    0x204050a06020106090e0a05150601020a06021803010e0c03030906090a0905070c03090501030c0801121b120c1a1e0c060f04061407050d0b040b03010e0d020d0503040206161514070f 79
    0x15211f82c080c040d0382091074021001c0c11615139940d840141030048880540265664608903031044000b4000d20b4007018800c01240380a000b8070040c859580e0061100010f60070000c1c0c0c583c81460328481c031810000400f40481c0d26400400e000800e0b0410042100340b902c0000500b041d07415003011400038201010208042d806031103440840345040e5111201b40e030030710700c000c0030541a03a44240d480b0303241e85c940711034402c00304034248000d0066415400f54682041c606460000100e03008000c03d004402512102100d04005444090350b010141d00ea00850b910800c800510864030790b100c084c00303084100480c000b4030140c81805035200e0502000103441040c000ca4407103c003070311034900261040002c41d00e00e000d03a8000010089008000080000400340004d00315146031034030794001e41110215070461750301440394085000c2d03a818084d10b11b141680c0042d810f4402c00290711070320795140a41400f80041c0c03205c01038600305120300402c3700040c0e44444a145502c00c6444c100092440c90825880324 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995734703 1250 995733453 995733463
    0x908120a020406051e07050703051e071a0a09150302180301020a080f0901060b07050607020d0504031104050a0915140a0902030c09060334171009060204050a06020106090e 75
    0xf1059901e050800003500700c00011850360b210764450b444810300c4403c2c0032640c103000c284001e602c500024803400144501e001e0b8249002c1007800010f03041454100103010303170f00615103044c000c281c442e182d44003c200f0040d100d4801503002904415814048403140c03503015070080048101100c3c3c040c101c00d0701c0c08101402d030721802c0c2d240b500281007a40801d955500021000b604002d41e4400803445030703251258100e10744c210303000c1520982d004074240a04580c0511040720206940d10f4050316060854860790b506030f510400701400703169690300081d0b50b400c4580c0716203180c6070700801e108103100c80c140180b00504121388040d61840c100c000071589146861150100059000e03000d040070480c282c040080d04140104207641500030041e80d4400004807404078484110048000c49004501520720103031007059801503a0042228521032940403c00900c503c0d500000e428081000ea40511b42400a0300030b592145400030000d40001c500b480d0113400403400d84102e800304019007181000303196a11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995735953 1250 995734703 995734709
    0x5331303380604022b05010905010f03260403030509010905060307270e07090e0f042a030203030a030f0b06130b0d18140c030a1707060f0908120a0204 66
    0x204580007650070414070075100b58004801000141403107021004a8940c0c44c101c281000d2003401c0e4403103908503c103c0c1c4a413a01404020408020139810b080b42d07800144030a0001070146c0c01c45c000e54804403800400101412080315038020307100c6030340340b5010f00103810940003640030030700c06100841d0342c0c00d0003400d40b0300c10801581d41044000000036400c10210310b0066a050a0910b8840491040308400006000303000030b60701c07030b02042d01d00108621103d00c003800d10300c514407001c0f05200119070110b103c2c820460f100703003101410741040902c1d00003240351030744000c0d014000072482c0221503415602c00302c0c030310315401000d01c40f8262480c01c000307062107040c51241001041c41411b002c0c0c8016480900032002a003d000070302c40001e12041a00300030307000b0045801c1d07203c220034010901428820301c450b80c0d50940c01014500b40554074150b0240588080c034144210209158043c802c00d5001107440140300802001a80c40030b081020103540042c5000840d08403800204040c0010b40c0700312030803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995737203 1250 995735953 995736023
    0x70807020606040f18081c09050a022b0506160903020303180d3002030705210706020309030c060105030a120e0402071406010504110405331303 63
    0x1c0d0b0724141007000814810880d03100311552200581942900704980c43c031254010a00c59488083c1c403000e918030343c000400302c46040341c02d000d0440001400090f40c0c240050341115890090301852000c0c410000c00300003540c01d0032a401e00c00c40d05204010447c40e009042085000541103080c0800791051100c52100070f400d135200b0000c00c0d04418403c01032808403140103001d401c56841d0790b100d450740c20000054180740000740080d407200c1040c03818407006822103140065070510a00361601501d402d11910100c10418070704520780ea40c0d41015089414090340550308540341d041010340183d40f500841e2203803440e4480c000012420f403034001040c812b0250700c55101c0c410000010300482e900041c2c425042e412540900c16500060741d4068a0708404010310000c003000d42c90300c0300300403d0381c0d0414010b0400304070410091010340c81d071850801803d4120250074803940c88110840c5484030310080348418440000c2103c4401100103a0640e084a01483c1c0788110388182d400b0103028190160100d6030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995738453 1250 995737203 995737213
    0x11d010207181d0115050a050f040902030c030d09050906010804052e0e0a1a0108150402060d0c0c030905180612070b0a03021312170315210607080702 66
    0x81d0000550102c03038810b102c60008900d50780482070800b0040000110030708165160080500d298010030040c400a190840b14242c2051602005c10306802d0507070000780c0500d495454007403c0d0340b020052030007805005001c036842c0c0c1214203801031109403036000d80c40c400d06600001c1102903109c0c0c000381d030040c0e40020185c10f1070040d5003419580c040c1d8600e000e0380c024184181c56505042c144c840c002c0b00a00000141400c07581701e18200c3e4890121342d01c4580720821075401440341c1e41c800210b1808044202101d00d0054565000151490107852448202c00742006549024640c0c41001c03444403a10a0f00d9840205486500300700043d0b0425201080003081c64002503994549070a140780c1884d160020348034625228007186409a00410000d070100750002030165036030b040b01c0c1c022001403c4840c0c91704e400e800c4590350b403400102c41014100040e0700c04400304920707d50707400641c10040c00040c00c3d041c030380601413000d00d0303204c103c11001d0b6058003031640019906070203912003600c0344a995000d80 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995739703 1250 995738453 995738459
    0xb06030303060916091503020301060f030c1d011b0807140c0d0b060d0f031d1807030209120709050105010f360f0b04030210050a050d050604230402011d010207 70
    0x511950703460700c60108202c1140001c0c103460091b80b4803204070780c00c0e0780260381c83d81454400741191104a8071101010b1a0241c02500540d0000c0c0340e01040c41601c10901000d00840c1c01283e1011103550b07241d51600041040004010300c0c20028101948250700d18500c160080a1098403000801c0d591500700799052074440000700703807948460740b180e00102000c1d13140000b0788034001110907130407040b00401c21401c40b5030100903003051180180e0104941080080f9034101c2e00840c1c00c0d0001d02a00103140d004503402220b5a80d107a400c1c4c81c000d0314a411100b8465583d01080054142031280b240892102e4840c090024803c401281c00780148100b080d580c1114440d002d0a220a80300100e00700c00314a1602142003064102604000c1c4282c6a80645890540c0100000302358418252024001c0811409450503049429200c1d00c4000460000c0c0c40d0f51082d000c5405444802c121260f400b6160310b0b0351000c040410b803c0c600450003a42c0e074665602d05000740480f0143e02c1210a40580d000b00703020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995740953 1250 995739703 995739721
    0xc090f0f031101050c010f0603050124090216290c030412081504141e040b0a052a03071706030309090405011409060103151802100216120b060303030609 67
    0x40107191810304d421882c01c3c2c4100620750846251050409032140c50708000c1003842424007400c603400ba100c2d062024003d20f882d40501407800c3c2c2d44111040b494000c100c08100541324401d0000880d00025103e1203912a40d0700d5080104281e0203030750441041c8000725046800300d1083c0c030703c01c2d540004e030b1402030000c094061b50802401400000003000180c0c00c3c8900f6104c80c0681d0500a882400c81501030501a005c808090324003060342d080140040100804141c048400d0b5400c407800030f400098030748801c880460000c490103410300c004004002c208960f00d501800841c0300360f445036500141910b0041c00d0143c203423420384400350303d980188184101031034140c1c00540c101c1d100310000100f821411303042041c000d0080310203082541240f0010024440c1d1340940448d041030000c003c20000c048540c0340820130020701c0020380507a03d811020700090b8003c108101c0e100c1c240701002c500070390762507603002103042d0305c400304640c3e4441441c003044440c00c00009880c05107070b004019501990f903501030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995742203 1250 995740953 995740973
    0xc0d03091a0901060b22050613030b090a0204150e090c010f030b0409060e030405100206090706050a051b010e0c0603090703060504050709051906060c020108040210170a0c090f0f03 79
    0x80b203620755610440000c0c01c118081c010300819415021074280c40b041044140d080e0005075100c00c3c00380d003041001d00c07152000c6000500076030b60312203698050f58681008080c540308001100035081803030501c03c04206404411003038100ca905840007101d541d1110286c50711000c01e0106075010481c0110b00280c0680a0340200746001ca000d040060300054940305c41054400c00c01021009400c000383c180082d0070721741c0203034403082400d0009203080c2c1004590207a4a040a120b00400c03c000810b903104901c0c841c801b1980300c101c600d6119030508403100c410500a10590030245c0180c46140301c00319182c00d04d074095900c200741c2040603080040c950780300c81024200c010800c6415010744580407481b04418454540a4640600d0391000b5000c2c03030901208442950300107070180401851110300513079000d2081c6500641c16100701c000c030808845d094801c80202c046450984000d1f004000e46000f03240e0000340315000329950440840e940301076540800009000f80305402c0c041c00e0050010a03007a0207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995743453 1250 995742203 995742211
    0x20a03110c0315062b060b130507031a0d08271005070b180303150a0911070615081b03150103061d010218010305101a0c0d03091a 57
    0xc240d800c0e491007040000d0038501c68406401e0703552a6042032049600304001c01c861800505242054010140003045803c0f01844100500c01a00c0c0c4c0d03900f14081d20b0307410b00051600002030040c011303803c182c40064050f08440307404080541d07001a041e055460700001c0900445c0d0840c6407149004088200144902c51b1124040c01d00c00140340c8107005c68403000003a510b10001903849a8907555640b504000080c0041d0000750303c2c8040000c21001104003008803900801c461442d000315100400103c3c8480040b42e21603a03007285420103541d2010034480c000d00c4114031407401000540b00300290750a00300441d00a100280e84007030410780001602006000c0040c0000b030031104a0328020b03140b1110300c80c0c00d070000c580140c0c6034130010080c440d0000d00500482c81010007581051803d4640c03801c9011041c0c07105040640701c0c00407805d02c0654036100e1001d400d410000950400d070b594007100a40e4090043d0010030f00c00c01144540d600d219100340c1107400c0d802000c0c59510303036a0502079040e0f204050 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995744703 1250 995743453 995743487
    0x11031b0906032d0c01030c0f0e0a03170408240c0c01022206030e0105010b0a18240f0c0b010e07120606020d0201111321062415020a03 59
    0x1d45441c400c0c0c03e180c0c0066030000400040040224035004403820004030102c09030505041c46200008550030400100308004603240c60341c681c21103000018440740c42640050300308448035040354860b1034040300800640e41c81034126009401c2c20b10041e203a040001c094049040343c0030006ca0344200d09075000700b498013010340c0003509044100641c0040043c1110500e040040c144400300400340d014082c4507859001c5500810036585844091032191103415251010000c0c85013140c1c05000a11606170080c2c040c0003001400041541c81c11860785480101c000c0124081c8a2070b800070500c81c0c00c9045405920000c1e604403646010705942d15500c010f064a424000c00c00440c0240424600c1220002d1075241d005007150708940e40f0190071910104100c01c2d030104c040201c49650075008140500b00c1d041c0d00003408042205440b400b0500c0111940140b21500f015034883c1c1815155100340c0003840d00c60700c0c01300e404d42d13521440100c030454407070700ba000f60300030703898080100e4000d0141c100310464074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995745953 1250 995744703 995744713
    0xb0103030c1a0123041e050712020c03030109050609090c04110c0f1e03090f0d03020a12080f010f060c0201031518020408010e01020f04030f060212040f11031b090603 73
    0x10b42103408805400340c02c138441c0c02c4100340030740400720341c1c54070311020940b0195001c20070701d0344400c458541c600c0c0e03003012420308a4a41d804115010305c2015980703a00b44050b0382c110b44603001b00b4446a00ca51080c4a40c0003881c0c20314010070b000d40b074100002c600a40e00000148280000c0c4401d10001d4504410300c4000c41c5420301c010b2000b910240032242600c40c01d0000703003c4454a03034070664982c1110700400c48195101340840040c607114810100100002210140e51105452400728504108040002c006000800c0700c40002d6402c565014001c00c02181c50141d5a0303280c82002404103d644200d02c000f603031503013408004d07500035401040c00c0c40b500084004c410381c440201d02245504d0031441420744c3c0d0f001904011318982031007007014040d105070081d45020b6a8405c492080d0190303000103014102480806403c1104c17644c121110b0310030003990b8203e1894a402d003c1c0010121000558070241103003808a000d140208890f425000060b010060b03030b4032200b09100900d64018100b50f014412 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995747203 1250 995745953 995745983
    0xb0a031a04110a121b121d0709110306060f090a030602190201051003050601031205091e01030c0c0803130507030f050c150a0c0b0703020912010507020c06070b0103030c 74
    0x6940500402034540c0c0c2d58159581d084280000d00400b4001d00c2d881c9038500d05020400c1180f07102d103220100b81e18600d098901c2200140c0e090009242c42241c0e15613482d0000c16002121101080079011140c060108010340d00040450780003c0c44121501036108208000e025070509200d07000c0d100018020b04107081071a100d5440e9000c0b43c2c071840c14064400040c2440c049680c2e424041c031503000c401324510b510b106142d551000d60710301d0180801000c0c1012080800c00240c882c070700345d40103142c00600703110b40d02c0e8181300303c02c03405889116080d0000b8200380061011034000d40300740c0c00d9070b40e000c0d48240c9142e0b6803800c1c40c0c034654030414007258180601640000411a00700e22030104c20b0280c000f50626500c2c0c02c041081d01909040e10000d0140107010881c14190000f1030741c040140c00120200341c070369400d00100e0003446a040495130102c1801166185800150b00c030601c1840b05400321030744160100b08114040c01a08002003100814000610000740316005a0800c184078403451b04e0040c1d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995748453 1250 995747203 995747209
    0x8070503061c0606030b010f08030f1206030f120a0f0f080c0c07120605091606020303160c05030c0f0f12040326040e0609010b07030c02090714040b04050f0102070b0a031a 75
    0x1085c1d80150703840b0313540d00018410300658a207904014200c2d5002103160005074102250a409243e0740c0003106010400054020340781480049001d0545c2402d49503a4417054a030808290041094000022038901c8203c106900031a16180c101000381c40b000720913600c0007401c415aa10109141d9500e000e4058006032030840c0a84018035a0711a00b000300e00c519040b0107282c5001302110000c00c0d01e1400f210200850b58020003113a8100d1805008410011000d08050742c4030820b010300108248400913000744542c402240704050151600c082d50802e0b581140c031655101d14503104020015400c100c00c20000340760b062200082c1164164140f19450b04c017024041c181c00a9100d1843c03140c0450400c030301d40c9800550103016090841c10607050050070346005201c1d84198900900034100d00d0041401240142a80103008200811183c0d84903240c0740174424541062044a0044090700540800d0758004203607201a1424003000038140b00f09804101c015180302020804210050001000152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995749703 1250 995748453 995748461
    0x1311190e01030213181506050616020928091b1e0e040f020f03120a02030901030b090103080f181003060315050c0405040e0c0d0c031208070503061c06 66
    0x4044410203489614500600c202c002c100d92101c20214902040c002e0346003000000f0a25003908200c14100a0000b00e220f440108003a40086510072804100d4442403020100c0c10104a403080d65040925102c428107000b00f06d00c014500600d841038440c10340c0c03503a0100d6000c1081207020352094121040b130f2401d0b1445551881c1c102945030346030035905410740260300e0110380c010300c401058540f19141645940b034005805590003845440e00a035141d00540e0300300800c0b00036030702c058910307951060341f4000039640e070344510071160109090010701e60861801c21841412640c014018528000d21014010116448070040ca4070081000c0c000e4103080c1c9550280e20142000c0361000a20903041d801c250743c1444d0f404a008542d20300784010032211501c035070b040c4c8003110015500481c104e48007201080c00c090110520079004200c0c80f9840050091080c031803412640959040c01181c50ba4010132942d400c3c00300e40d9180031401c00c001064503402c180c80110340702000300c2d84150804049a942105407 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995750953 1250 995749703 995749709
    0x909050c09030f161203032c1603050a060b0a080f100605240d1e0f0c020604112b0309050a050102010e1207171b011103131119 56
    0xd4140420010140d0800708090850303900072600510700100e500c0050156001c00d802082451a10503400364200350280c0c0120303851402030301d00e0402c0f443c1c1e0f40c01202d6000343d08200845c1c040c480d0141e080d090801c0c1c10802410340c3c0e0400090840000a070312250054114030701040c1c4c00400400e00000c007914103100c030309a6951220b001e0458055401c2040040d6500780c1c012501c1044881002c920742894114418400c400d132001458640042c00010402801c500f0030241d8884102c5660000c00700381076102080c4d001c0305d02010050b518101008030ba13144400c50f00180b050f101410b60701ea081c80c00059201d58041c0d4580c2e49880010f030f0003000302c1120301c0f80404030041000403400748440c1c40d03e0100d00f0050f142c00c2c4000c00104021082e00ca69808540d2034003058104000b80b6202846806480e81d01403c3e11111a550340f640822011040d01130401052649546062020104405081c1c1140d00800500c054149210342584034241c2c20304070140015403040070080100c3c500903480141e03c0017 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995752203 1250 995750953 995750971
    0xc030605070e090609061306051005090406060e06071b1d040c271d030406020f0c0d1101111507030b031603030f1b060612020f09100504020901090905 66
    0x9081c01040900500b81ca0406148a07001450401c122502d80c144607540c03180c0c04075683c4410400c0080342400030700d099040650040106803203d180950480c00074020403030140c3c0c0400000750381c0c440c100c5005420030042c03507000c0803c0003480c01241c81c20020400007002c82d981791307401d55901c034900036041418094060b01d0900c101c007004240200150001c00505500c50041d8807030320310f10741c0c10780c1c9603201c6054107010a64806412480d00d000028011005400c030003100d0f61a40c468101a54035010707109100568480c009505415007494a000f03089243d0121a501c0350000300b2005441c1c2200103020b070400ca00c0340c903851480e00900426400c1c000c4a03a502e00082d141205401d0500380800e100e030107070300c1c4580440e0400010790b008903550345050b5540780070300c000d06001168140404001e5000b40499042100101e4900c0040c54042089403084664011101c40070302071100555046030001100742a0900030081c50a25400820b11403a051401070501900e8440d21002c4850030f461840c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995753453 1250 995752203 995752211
    0x522080f04230102010b030607030905010b090703062303030909040521042603070b0c040b12151c06020f0705030301080d030e03070c0312200a1e0309050405060604030c0306 76
    0xc0c81c00c8420b82003040d0303040038402802450b0503040402daa40102a02100405544441f00e400380170007075201801c8002d005040030500d0402420007000380640d80910010900c0c0100340b40004c119552019840c0c03000600030718141048002003244032000240283d815000300704018005445025146414205080c04140ca03141002c41000c00c40008900c201c140c0c038405540341c0a020000003c0e80c1342e00364421a44949980c0308414503403180100e40c041e002c040b0300480c040e041c0c0c2c000390300302901c04e403e03000505a580040c00d0070084820039010648a0b2002007040903030101d859600200004800030940d07900e030408075910245942c1c001d80c00241c07590080395410360b000d945401030690f400b0b1080700450030b0600949440105004038400104181d0b400b22008a1040c09010840202100c07006900b21103002c1442c1a6101d0a200c2c40880e038010003420740318000c1021041c00140c090b016510510500c0c00d04092100505002c0d080a82c819405d00000000903600740c6204055441110045 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995754703 1250 995753453 995753489
    0x30b150319030f030c14030402010c020d050105010503190b19060807080f010b010c08181504030f120207081009060e030c0a0308090d0e010e010309020907170a0522080f04 75
    0x43c41a00303500c404408140c02d20000c0078045601081c0d4100c014610484183d030b036100e03131005079080c0c1e03c10040290480f50101c1142d09000d0194010b904a502c00e80c155041c80e922603050b16200041c07030400a01760740c0d0310004204101115445126020042000000d0701610b4901c1e01d03240491680c80080c1ea076011075031b02000c810f800c0c0120303550b0311020b08250071b181c8040e40c3c40d11428000c900c1c0e11022000030640c4684180d0720640c070325034070a40d0041c1540c1e030741d034807414450310243c41003100b520241418024403211510008902c02290740441c05020644d0107000a00c01514005500340c4c1c0351030326050350101412050000f081114114001000b25000318503003c1c04401000301030b0390031034100b2220720000d10740007211202d8550307007460f0110010400c3c4006034000c00f12502c1c0a504084560f0401c54840d8101400c0c0810120403078a0342c0d01c0c2e03a00d100c4100d055841c03c90704e0050756044d0009468a1820811003c070501e4458441d0b2414100b2039481b40d905c6801075403010528611541800c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995755953 1250 995754703 995754707
    0xd021c0302010609180f0f0b252c0303190f0206070309050604060518070303050a1805180601090305010c0c0c0506270402090a03050c011b0c030b15031903 68
    0x143d0000c16034507206129115200c40110322105540101900d100d03c0380c95040700304490044000d0318503034818038460007800c00364032004490341e80c0d0608900620142d581c3c0f041c0e050013207000c4070305040c4006c4030072840ba00c555a200c01407150401140d400d403000b404001d9415490703c40202040002d5607441840c071591010080c60114040c00b14030a1501c1c0c4800311011803400301d08241d0140d0400307030108041d280d103000c41c4004000318080c1c40d160300a03070340c0c04020190302000070f01d421401d960f24007407101034030910420008400d11076582d0040720900000036039030403c07800307e5000f0b4050404c201070555903180c90707095075240c500e098000f40b07015038400200030312030300800040c1506927030302070404c1804090142c40b880140e4001840d9405e01d03846c0030807039030749804070b44ea1541c000e00310fa11166641e207850b646d5194401c4507140442e45070300982c25410f2130303280039256031904104681e13603a0f440d540358201100d6020380404808003641d44115a207807001c01180720310180380030f8a404156140c0c140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995757203 1250 995755953 995755961
    0x3150402120c270726060d1203060503070504111e09060406080610050c1f150906051807020703060f0b0916110f0a060b0301021303081e04150e0d021c030201 69
    0xa180706101c00c02160320101c80e58548000c1c3c0c2030305d6142c008070954541c2400501165000900209214640580c2c03001c055816081001116001d90881301115103900070001a10300e400c501090b09201480005440243c0040d0b050513400e8006580345132a82c84070110311603a019400010110303040a0521000e070601c420018203a0b400f81c504613091850403a4090b48600d180c03101180740d090328003040410040c0b00e6014500a221002104070501d955042c0700c0c0140165100e1244130700d1a000d0400305007800c121095100d502c0302c0e8060041a03082da82c3e40e200801c24210704c0181d685d9a0040c15180740c484540850040c541c0c01410301c42c2d01147c1c44d004000390101c00b010107482c0c009030346000700318400207010303819946e00c60404140c070509a8003203030090103801c2194076003454071807000081c4110340008000d0082c3c2c2e10b264804880101d11040480d1280344901001c0400034215041d81d180300c2d003c0c640c4070031001854000b5000560700002c130303038000d40f01c02113019480c00c1d1821010140c09200f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995758453 1250 995757203 995757211
    0x11160c0807081c110c09090c01030509030405060304080d230402190f06050f1210080f0109030509010e030f0a05030a0f0908031603050418150503150402120c27 70
    0x402406845000016020103c0100c03001d60700707211302c03c04440384100d0f040c01001d07000400a04404020b1a040e9402d036965030b000034a09010902d0000860702038600030089400307503007010702520301e0b6490b25036890a4035030088034032803080ca507a40403100c44038110030380d40000c8032000c58000803641000e0040101d4591100c008610008000e0000c01c419a40c60399141d0444049046c011303101d540c0f0017002042d030700c115800c912080340004100001059041452800d40e0b090700c048074030083c40b0026050032140c4e0343c000907002c11000d00030003101d98805d8800c02d1004d40040c060f103c0320121640103c2c038002c4420b004617a60342000ca000d03409a50701c2003010448031540e10704081b20300e180c0b02249403030b4031840842c080300e040d02a100e402454000c1044800a00c4101c40c0f400324601e52082c5007005008180b08042e145852041c0060325150014681007e80359200031046552619030070400c600200204021443c00b0f50082c5110303903a10400b4079600c131107844c1c6180b004814030313003002e05007040010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995759703 1250 995758453 995758469
    0x102121c14040b0610200d09050108092107060f0b0103050c07081e09190302041b0f030b0a0803040306090c050d0b0f041e050319030509030d11160c0807 67
    0x410403000c1141200c08641040c130a950011411403080780880b00d003640c180e407040c094038441035045001140010071501c0b151441e50303190b00183d1920011203040c10182c0f9034146690082a56003114003900340002099010301c40e121f4a8050a50750b40310688600c401d80c1445195225a9101296018062268403000e40300b6001d117008804d95400c00c050003124503541c00d0704602401d15003148843c00c11141c1c01c0d0300080542003c88140e081d140c0b602000c501049001d203080c6203400d4010782e0841000841c0c0c0482e034075000004803100c1d808400612034034240b542d020b100140001041da81c14070080001d51702456001c02d1034040e50520541c00d22190b4041070103110144006c10110341090704680e04000410061452901c0f41c1c2401040c203403000803100c0c0c2080b00c42440d00204100000204401e02c6200008107240310300410650403150100c840081a400070400185101075503402400c1461800c0d54290800c080c0038a000e01c1001c90f100200d62403141c1b00420301a40d0000c0040800a15243e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995760953 1250 995759703 995759741
    0x140109020c0307031b05010509030711030601031a130b01173c0c21010506150d0e0319050403050f07060905090429070905060306100e0102121c 63
    0x1e140403666071095000c060300b004407406800003d0300700000b01070300c519080303402840181004c0c4c0c0402e440707030f02a640c200d902010440c2c40301114203020580c4e038100c03038004c0300d00c10030420100100e0469203401800f00b064154607180c0c0030005401c100c00c0c0341c0a40041080c41607000f4400009a21f40f107000441290303503c4008050580c00302c0031103c03014260803040048090020212025458210303088580c0c0d03800800302200a0507010b17450b40ca9069409030800030b004070b45a010502155060680b0102c03e0f0a05c00c00080c1041d5007183c0003914103000401c03c580c94104401e441d02c0e019a5010f82e40800160002820828070174100b110011718400040600364407450900f0140520101d44540c6000c2d8881c20700040030f004a0364a000880c2103400c21000150103a1898040d140c281121000f01050010401044a040503010f8a10400025029401200300d0443c20b4800c1c494243d40385045108101080408500f070001400311044408070300d900300700c051035041c4250355014990403188918 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995762203 1250 995760953 995760967
    0x30d081e010311361909111e09010b070302010c05031005040b0f1c170406050912010b0d03020f0c011b0201080601090911040e07030c0816090905070314010902 70
    0x544440007458201144c894486051200c1c0d00013920b0390105249200d82d69601090350084501186548149a006054048611410b0300101103400c00d01000e803840d80f00c0400c40031542404039a03241103138000401e5401100311320000070300314802600400c100c010041041c0040540900a102013112141402800e40c940088880c41d1f0710228402d080c40b170303521101d0181712612a50541c002c8044003420b141480c4c00c50044142220000d8030084450380c0c5411004d400c024800c6003610203a41041d580c0302d203003a0748141000b01034070041d80380c00290356a94084842d55034401d6904680140300f1f4000c0c081c00c5102030b02c55070604264842d07990520a003040368540358000348029001055090074000815100c03440100d55082464101004203441c044400303c404040c000134000301c03400d080420105513640c91040303094582a420705408504980701040441249610600d8070059600d07203880e883d039071801c50005881c0103642c0d00d00400e54402201c48101d540000031400b5224400e015841c15072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995763453 1250 995762203 995762213
    0xf0309090708070c030f12050726071706130204080a0c08010c0e01030c09051012050a090305040509190510080d090612020d0204030512040509150924030d081e0103 72
    0x3804c0350000e0812500c200320703071180b502800f01c0360000c8801c2c06003080180303054030014140e41c1c64507000c09140b85020718910100e03030000e08a43d01c140c9540c2c1d20072003105811144400b03445005410580e010b068000700801c1c25081c2c1c4058002081c1b104001c101d400c3d07050814102c0304e182c6800c03c14081e41001c04800ca103903000350340d44c2da41d140e00307103000180d11082c01c5084074249103540050780d202c401200c0ba08810380e401218685c51a0440b41d04004030380310301148100319000e55800030003081d414002003100d40f500c80c3c0410b81c404448906410341c0100b08241504440007203504220b4440c40c0b0100b40090741d000c010841d00440281020201c1e10f04240d0040c1000d016402c14408041d000980039100810a8040d60000d6030322208844291a81d10004c01c0c2982203030041070300620002d400202007280304a5030181c2a40060001403091700c84c50008210400180c1c1034002c1500e190302410a036031401c100c072404034900750b56908158109040c1070048a0003d40c40001400b070200010320200d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995764703 1250 995763453 995763467
    0x602071a060a170d050f070b0f090123060103090f1b0e0105010206091507020a08040b0714071a160b09072306160c0f06080603010f0204080a0b15030f030909070807 72
    0x40c0c2d950170416120511201c2d4450715228041c0002c010740d004905000e002401304ea40e241c000e00c8804000d0080704e89030718000c607058803000c01003982034010001044407540240e00913500f05000e0382000c94140181d885241601c840704030300c1e261844030f04108011b849200b462040c050a024805044e503400d1105201c1e0b5207117032400740d44041080701004608058020041700349000c1c0d000c0c10740c6854698603030311400b46400084040d24400305090040100f150041680300680305103c4011590554140c509125a080400c1c5011b5080858140902007251401c000c0d10035900702e0000c0c06a181001180c00c04411040c1c2004122403030301d40720903000e980700410740c1e6082c9541c0c85482c0010955043c520094191039200b880c1d01072803040081081988500d07007a11407031f800d8000f404141c0001c0079600c1240b04a128442440d00400342410000e9181114982c00c0002103201039085030030600003e00380003845044c00c8541d0300014040d003850414500e46d84e4058050309081c400d5247c000da018105e5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995765953 1250 995764703 995764723
    0x105010e092419081f05090607030c0e0603090c0a0b0a17043f081b0306010905130902030c120309010c2906010e0405010303020d0c0602071a060a17 65
    0x541e81c040310a02c03581c81d51403090340c05003440d0a000c1c408030394411513542c0b1180c0c0da00007000314141c0c0d4035100c00381e60601c0c05160701600c0d0f2100108a01e941d204412001000d81c204440204170607071141c080d465036244040c5010300e1091002d4291880c0b002c0800c40210629402400000000d0200c5980700e600a0100727451680452840042c0e640c40e480c00118000e051070941d1f08156035081191400c2680004010f1012010707500c1064480810000362034004040707035400c000701c2001103043c2091088602a541040f010b04014109940f1040000d00016050241c6d2903001e40d05c107001415490100006119828141c1d01c003114903040b1025191a84507100c507440c18028140285002c00c0b001c40108100d20401d2450022550460032030301004031020745d509070000c0d9861880442d10305c3c042c400c2c0e504a0b540350b0020600004000000d440703c0328121002d44105d40e0a0100102042c12100c1e03480d0b201d07041c0318014105140050400030f80030b400b0340103a01e0040c0034500500074080001002401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995767203 1250 995765953 995766001
    0xc090b0a0e0a05030307060b03060907080c040e0f0703060203070905060715090c0308040b0406140a1710350a0507180b10030902030d230c010905150105010e09 70
    0x411154207022900d142d1441c1e01268051000142110601c41b00d82e01c00d81e50310b5400c038140c0d2596104c5141304e550390b00c1c40740920000b80d0003603000c549107032500313074444031307201d104041070303071030400190220605103c0541e0050307030718640010800c100c50313a100c85c6010191108071402d6040c0203450701c0342c441180c0880c400c0c0d41c80700d40d5030011806102c0840c021200455010101c2d40c0d03103607180c0d0060030301504980b142c80e000c80c0307840310220b00c40000e800c1510402c504075682c8000008243c0f143e0312304400050300d1969000c952400120701d0b010f1015100354106c0200c044649601c0d41640210304400c095480d140d1190090040d0f03100055003c507a050403551019500d2103904804203030a0020002d074110301d54000f0b05405044c0d002a0150000d000c030354001c405803004441c20440c29141c035100003c886104980051340d4a9105400c100900248586080000341c202c2541e03071510f00c1c203064055159488115640104425a4010400090b003039081d01c45c034440c1c0c00c100c01c0e401c010756912410019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995768453 1250 995767203 995767217
    0xb030f0a12020f061b1c09062316030f3210090f0b120609010605010305010810200c0a05061006120209010c021314011409040b07030e150601030c090b0a 67
    0x590640170010755005192110610b140e0007003144600340285680300782150084d0074100701c401c0141381c40c0c0d041c000082d050607003d0300d20b40d528034615421100480b0464149541ca80d5241506501442418545003145640342107a007140c41d0340519803c403840f20079075080850400c1043d01042079168804840e811500071850100211201008d082240c000c01c0c8c005414200d580d1100c00002003003401040144001c00c03071691180011816142c09000c0d003402d40d0300c07412142000741c0556200042e8005144203118000150000d40e403400e40c44465906401d900c0020a02c003804010b02c201c1d5044926800301c030301c842d0710344040a41400030b402c11454005501180f0f40c4130310b0f40034248841049a000786402d038005416150031004211800351111403106003000411004080510f0300c02120f40144600840c1d9110f655442c2c141c41c000381050209500d510f95003034143c108024081d16114550b58403412807409400041c00c4941b007860030030400070311140c10000c00b1114821542484590300e0440 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995769703 1250 995768453 995768491
    0x10612021008071b080a08070c11010f050f0403060213060302120121050607021f06080c060901090b03010806040611070c030b13050f0601050f010c0c06050d0b030f0a12020f06 77
    0xd40d01c18a2500c1001110a80c130b240c040030030000e500100000d4070706071100401070316014002c4844c07801c0b1100003000920b15010b5002a51302503810491920190725146240400018004030180c0140e403040300d90a03000721f540345004901000100c080c0c8070604d07003181054031400390230030902d0b41132051a0164465000c0741c210030300d11240b610000c6070420b00310307059400d008400a60715800d03111102c200613842256404101c2e0180550380807151194003c200d6040040104081c40c0d000c40c540e01d0602040788800204221102c01650082c85003e0140640c0c1c40c0500b000d009031459600300780b010981c10083d10b000161490103070b40549400811019480d0380301c51440301c90100d4031a015046200d00b4004211035040000d889050b102c0c16106200c107001408010344c8d0248411070010200e40502c4d900340015440b40d005054441c3c0210f0022584e107013506c0110b0f0401c0d491700c11542c007503040218040284404000c121080c0d60b002d100900e84071028809040c0c854402410804e140c40341c603d122 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995770953 1250 995769703 995769707
    0x1a0d0f06050603040b010510021603080a1b080d0c05040e04060e120c0610050a0609060507061506030504020406050312070f0507030203070b0a02060a020a05310b0c01061202100807 79
    0x20005080007401065403030905080031703400c540092080902c289901481302c8140b5101080e2441c0030301c2586907101e410b500319a510440340c3c10441c40c410800c94009101d5080410003d070500303ea82c0039094040d0303110588807151090702c037001070100030710604020410a03101d1030b000700c590003a000400015100042d803003aa043c1002c450b150b000000010420074901e2001251542c022181159140101c41d0b0b40c000b4802c0320921403003401d001c50096942001410302600040c64003c2c880c08002902c00d04c0180207401c0a002034106c00d0001c3d503900204021170505104274030181c50100c1c010700c140980301c1e0a038a12845150f0004103214000e50040c2c0800c2800c101600165500500752140c01e5203074012011690042c0c1041801403144002040300c02c5410b1088030440311903940c40c50300c0c14040c000706040d131280f038140300d004000805100d12482540404c18102030305180c0000c45d50b8640f4840d4030b40c00c1d07608075000705006440003e5810016070711402004240e4901d8141594155680e10381 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995772203 1250 995770953 995770961
    0x30403020a0803010f06020f0c2b02030628090804050d03110114040317010e15060714010204060f0306050310111603050a030c1e05130f0306151a0d0f 66
    0x40140305550200000c907061700c101c1040410f0b600b495003124004584400e6540c3e54450100030b03250400090340c2c01e48100849c050a0698501c0e0981400440d9102503010920700301c0200c0b07100540465840c82e80351951300c3d2200c114401516000140641c0445444030147ca101d148611849192030501d0322007014080c2002c0002140c800e0b00070092080480050072040d074007202d04800041903030b213801040640402080f8107850342681c00c2d040e150350307040c10b04d080c580391502402d500c13a0041c0130010004022001c1c1e1102d0015000015031150710b0150082c0c21168200740034010306042c28028031036601c002403025401e03c1d46403008144220780b82100c2c0e03414810401c50703009071068400075009040d0442c0050a50b0030003a40c040018480d8600b007144c0591000130b04511104240e6501c000303007407042001c2c00f44a03c0f036850101440c0c0e0b4800700c04906401035402114015250b5180d04400800584103100400d462540c080d04000c0703040000480340f03e480e2005005075991000c1c0c8402d1485940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995773453 1250 995772203 995772223
    0x6030d180308040e06270703020306010c051c0f0c1e0c120308010317180f0102030d1a04050c030c0403082503080906061c2a030308041412040b03040302 67
    0x81d1542d83d035142d940c5958144000c4601a001d1411103184920004900f00c440d0030780d01420601030115100c02d0300c124044c0d072001d8007070340c100300d124001203001c074001784800d10f200e039256900202c0080380d04001420781805240d80c041400b0920002002041c41e00e140c180c03405021400500c1d100e58145810060031440e50090900d044034400f07403008050b00301982c24140c80c002c0c0032a0301001e14010f0170000c035100d0a61051302c00800c03140784034802d00b40f50f0440841580e050042c0c03820461501c0544085071100e0440744081c0c071842e04403201a040600c03a180d00700031039120072840d502d003410340c0694a1040348001070681400050365030910104000201d41d4040443e40c0341a00d2a03682002030030150180d4049956003d80f01c0407924500e004000f8207400c0d64001c40d04800c0c80c0140d01c03510f5003172401e0814092101544102102e013510062480800345d0301c20b8880318030b2400d181c2443c00c00c4459041c62550302d98001044a140000c0f100107a8044600100546a8139901c6140480c18004404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995774703 1250 995773453 995773463
    0xd021908071a070318080406050304150510180903090b031f090c1b11010509030f0d081e011404020d020d0e0f0c09190e1e0304031a06030d1803 63
    0x110b44402148140c1140502658299405024517414100035564046240034020302c884000c0004002c0280104041c60f03110307024001c1d40100e04002d61910055620458201d50722003035907403040c407402c800307800c016500080c179010803c000c840c990390143c55503002d4000e0500d100c10100001e484180c1c1d083d03525619038840c2c00c00078070f25680d81c10740802915030100c66101140e03000c120080000c0c00c0a41d11030201c5e0300b012b003452070740300504015642030f070021141075054000d0440c4240040410040d41696060b15038500711a07240c4a0504040810703c070b0021540e0540030700040103000454880480728403000c90700140c0c1c07068009400d00091213005100c0881504180900f00014404100454540001300588070030b1000f4030f0400c01c00a00440300b1507050542030200303035200801540010641e0199404541c845482030a810318008170140e03840915a100040c10700800034480007070345041a00701d00c078852078240724000a4a5101e13030451041048255691440000c407104441c3c0000c54001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995775953 1250 995774703 995774723
    0x40b030421030c091d0a1e140a060b0403050c0f0609041a090109060503070911070b0c0706060902160b0726040b130807240204080109140d02190807 65
    0x801c00a0054900c4515000114054041c00207a00161400081c99541e40389003000543d03490180150041c81d8241c0c1ca203500032080000c000304074010b48282000c10740b41444220300703442c001a042c030603207507180c11405d245401404108009180014202c101c06c1e0100d449510100603c40400e5941c014011620f600030304242d80c041280ca0503042c5d0340210101652843c0181c0e0b04c0741102026074100f0b104807900759001c08010401e1009a03800072001102074054285800740c0c4da1154120342d2416554820701402c0006c1080403c802c2e4400d500041405480550800e450b0302010840d4078118000a00820031160004500c80e104180c006e245020f2440031030b1b100703480ea82405002c2c290458007101c03641107503c0440c40c0081a102e2030390010758001d007094501101680ca00b0085051a00d501c1c507401c0c0c0380354034a180c8010358005000500804000001c50f18036034209130924624240c0040143d030843c1c2c410908865000c02d261411003403d04481c1c0500103546444200c510a00001820701c80300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995777203 1250 995775953 995776013
    0x41512060e070e03010e0d050f040b0f1305030106030308040b060a1502030c160305120d060e04030e13090c170a0605040515090c030d08090c040c030c03060e0c040b0304 74
    0x780e402440c011070056560481d02c070160010315089966008082e1711540c4180b1040840c1442070000b03101210f07803620304c10700301a556015040343e85c000b2005d1818544002c118400d403a648800d0480c000d1908500034400c0d1740c40c40d10068007140001d80050425214040001d480342c64020701c003c010201b1044055207550070840082d242d1b00b04000f91086809540440c1d000034851180354401c4c0c0e5081400780c8402089001c0055059100361001d40c2e440c0d40300d00b4000f4404070141c0d03c0b0792207103000703880303400709514414204501d1907080c074034400100d0302c0c4c12040004902002c0e500400e9030110980110645050543c1c14546848110300405482c1090200010407401240d4000002c0c10881c8965075034a0b0b401c00b0540301e24960b9951501984042050480c861080c503501d0741047d0820281c03100000303214086025651060081400b01744c4520300e040585da4588654801045001d0180c944c03030805640300b07030795445280704604030b5100100118060141c80850050120000c036110006801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995778453 1250 995777203 995777219
    0x70504150c050a1410110f04140d0506040b060a150f030b040b1c0c05060720120613050c0102070f03020d0302030f041404050c03040b060103271113090804151206 71
    0xd50792170b19000d0750070051030b07141181c0044241d0303000c0d0340c0c2401028203140c00c0003c0591044511030015503c25861494400424001e0100030f000e0741c0990b08400440c030f080400d112888645a000c030101611419a40300c0d0580e101481d140309120503d004500c100d4150b0000b0058520740a01591080c1c0088070301582e04420911440343e50300c60030340e244405d99a4000c11009000c2e1602c0035107900483c00201c000044050801004880c0003401850010b00007c07155103014030480c2c0c81442801c22032203c006224081140c40101c0009100610500341000c1c2c0c0d11080540c207100c002e00880d203180016003018000d0083e02d40c035030007464206840e290344100308040c2a45c40c509641c0a035103404003007141241400100ca11460300300c2c0c3c06004a4032058011001050700c00000204d03500011001d01500901d00f00c04440640244d4000b400159510108140c050306c08071509912480e00340110b00144800701550700700d5084d01400c0c2c00a458400301655040d941258821095140500c0410040 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995779703 1250 995778453 995778463
    0x1121506021011040f0b090406090e01050711300c0a2105091806030f0f031b030910050c070810020d0c08090c0f01030209100201050906070504150c050a14 68
    0x2c0d9801e07014486041d089107201100d104e28002c131210120003080070b1103003201c5100100f00b0160003810004401d9950980ca10481e6031209000b9600e9440f00c0601c00c40c02c3d4030601e9007480d503460340e002d054154003000c00c0003905240c5400444502850041024440c0d40620030b0742c0d01e452404e010b4801c001d02500c3c214030080c1180540c0a1010310b16290450300ea8418002e85506600240180d03086480b0b058045c20160740007090598035104a00e40c1360040c40c424013060082d451013000558950f403103605201c0000070710a0001030158024407101c0020342c0d940c041e600028101d4105160f48030740511041e81005d446030001c05061180f190082200710140e401000d070800100020080c0032100c14045520f40401d484600e01079210040c8604946045051a044120141001443c0000c00000b180e244005807400b02c0141c1d654204001c2458018800350780d000d02c1c18030782a49050f0a215016030820140c48003c020000c03600101c90070400208050060181c0280900f1303080c0542859840d618 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995780953 1250 995779703 995779723
    0x309050306010801111e070507090203060f0d020f090618040b071d03070501051c0e01090c0e07020304060e0f030a05010615230d0b100e0301050c0909060112150602 72
    0x3038428a000000c03000f1041c0b1403194040b910b01252483c0004c0c40e240100040000301100c3c80349101007100200050042142c900104046000942c80c0d103403800c104020004c10301e000e140a9600c1800120041e038601c1340150000c40c003250540701c140c071080b01080c1604500b01c0220f100e00d205105100500c07a801c44030910035a11581c40303400b2903101c6014a01280c4c260406203400d584588410304c0700f58003500c09005410202d01308040c008608480e498140c620313070246555141d40d0391440009100c00501c800010b0314003185130002505107608021754a00c164480d480030040e00405550310395071100702e100710000000707003141c1c0e91500740e0070a41e0080c4040d1140c00c2d0b40030710305214040c4580c0244140400c2002000071f03514880c0d284c416402c801c0d4000c00c40c02981036501d0300310074402e40e54031403a442e0040640e925400100004030a16003120b002418400d10000b040c4400e0240340e54440340c460f0f0081013031801c02e0603a0042000a4040d005250012a0342d940082c404030b00e1503070000e200400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995782203 1250 995780953 995780959
    0x7140303060a120f060c05091c0b060312030f1302090a0c0e010e010f030e24040308070302090d0224220f08070b031801050a0b010e03060c09010309050a060603030905 73
    0x20b080e9844440a882a4084200810b05a004103103240480c50a5126030b4014025041c500d1800140b240005c00e4025040c03111009036003000049000e011001a0040d80954107500919103001841c00f00105404020009411081c06000080700d20507010b02c604610ba03401742080000342880300d0200e0103000c41c0f006000000740083c443c075550b03600c9071004003504003043c0c41c1c01446481c008011070140580700711012851150041545500415900c1c0c40b03d00305e0b1083c064519400c19240c003c00700f40c00504a0002c05005000003100c0c1e81d20810440c002a0741242c103005205103604071307040b1080e4016562a007c12010270a038810444110950305210000f01c1808405070319130740c0b4041c000010703018510342c80d44034000c1444400742202c01140c002c3c10081e000382011580c1e0800a081d988104c400700d0b41d0980343e81400d1225600030b011120070b25411000360200d86070980402a1030700880036070318105900c4440510500205200031620070f84c11000610415480e07050141c4503e00611580d40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995783453 1250 995782203 995782219
    0xd0521030115080105011b0c080303041410020304080d051302120c03071a0405011404090e0709064703040606150f02121c020d1505010512011a0714030306 68
    0x10b0814032407900141179400503192410040025121040401c51401c422104005c8800b408504d441d02040034520480c03062055080212002c03081030300307104036001140c88403030060080c440042c0e0104150340303120707a0325840014607607104002034184035641d04d8041d400c8200700e0748040c000680800c0b55841d80800381d08999100b80c1ea2000300d032014400b09041000b07000c3c1030100380000e601c24900b1411181074400010304103903c072040202290b0310356403011240c1d4400102000925070a002d840c0007003000d1008080c001000b80f001c0e00d0544046000d45207000107400d460111840c0103c0c0d007102c3d03d840510003130349a25003440c102d0020b2505014082c4002420076400c04600e124400c03a6030404c1056001d860744240901c0444040e800c501022504c0951000c0e0742c00c80c0055520142c158540b07011008160243e0241d001080c00c001d030b8022038101700041060304108000c04030560304403107105441c811003990481c2001c1203070140081c0100f014682c03450440a00354008051401030308211100c203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995784703 1250 995783453 995783489
    0x30e040e0f1c090302130207081207140703050a0327080403060b090c0a081306050a1d0706021213240806180403030203090f010c05220f03020d05210301 67
    0xc800e50b145001c100010700c01410500040c107101c02007000c0c84a180f8409802c1200640d0740d4480c42d04400e0180d00117510002c100203890b030344032075101d4000b003141785094900809a20024903920031020180c0032b05885044500541d20b05900030741042401110605680c0744514095040f94030601c01554581d0526a404055181c8012458081c40c0b02d0166103103000c02408040c2c0e52100020841074200800340c8078100410094060795100d21441c110004000c1000340e8400003d90b00d00c5e1800d0b195a100306400e208454000504865800e0036058160301c0d5140901c40440c107549a4101c3e00711229a80f8403d40c101c022030200c03ca011200352070710360b015955442400a201c9400310440102c40401000c5008079000e54002c40c0c020726610285d0302e40c007654034000707801c0d43c080c411507400103200083d5001c10180d501c250301e03a00f9031210008004141c5880460500d01d4410b010191207a15195208001c02038100591340d40545e030800000b0010000c0003081c000d43c3c10901c0f070341c000c906e1140d20780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995785953 1250 995784703 995784733
    0x2130c0e03061e010b09030307020904080d02030a09060e0c03030301060e0d020307150906030e0d08070c210e030a020907081003121827050a02090402041206060e0f040807030e040e0f 80
    0x246d139118102400450a0040790340800102400c0030300166250720f81000381c41101c12550000b507100700c0e06600c0204140c052450710000b241c1514181c1403180e00801c0a0341400c0e5404001c8a04481861600041204144c400030b1104040d0701002903040c07046440004000d07410001c10207501a0a444940e0001e030358080503801d0740c4401811007403034bc00c9004007101244c00b071303003141d50402c8039403500e81c02180c2d5940c1c5208508514912503808241050304d0250f400d030348007485030b94109050303014062000103940448e56003c0050840c4040c40380040001300c0041c800c440d400c6c0150380103440c20080550b442c1d0042c054030038030200c0e0b8040c0b581c481c03001310301030482101001d0290508036480d00710380180c4148100605018200c10713840b0340c0801c030b8100c0c19034032070024002501400020b40116405417030034031304807503042e1300410321240888100112489082034540c0c1c4140c00c03150300344c0e54138a01e140460340c000380c14040742d51240c03400207100038400000810003005141c0c041229400b140c41c07541 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995787203 1250 995785953 995785957
    0x40216060b01050f070b13020d060608010f200705010e03030a050f16080604150b0703081e070909050a0204050405040f03030614060901050c030c0604200d02130c0e03061e010b 77
    0x44004404000c0003d100010001090b81c0e038001c2c090b00c1840347c202c20907400034100c442524010340c3d05948a2409026200082c03003132032110f2400d21800c01020000c400c0ea9240c420f14000702c0915807001040c10002e00c2001e4100c2545c441c4807400340c03641c80c5040409c00c0e00415055400681140481001448845000003426008040383d2a558117650390b01c1c1c1004050b005941418030394014100c000540c640c1a030014207003052081d1605202840c1c59103803403030f12141000003540907035403041c00e001c601900075400f042658100c082c046072943e582c0f00c104c0d000c0c1c425a8440d541003480e10040109105283e40079003500f5110399018441a940d0f802e860b0b0364041d03040c0c50b503584448104001c42040d0302800041c011a0b16031810350b1b0821380341200503400c0140c11070f810380e1001c285502c1c60012114031f21010384503c4049924002d2041180c010505c010a07015102c0855076840c3c5112005a01400c100c00007560001e0880d00140b41c800c20b03005034030145440c0340c82e142c2c80100c004541e038451b54023 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995788453 1250 995787203 995787217
    0xc06040b070512011733150a030807030309051506030c0307060807050a0909050a050718030c12050a210e0301060e0604200406031e0b0a0306020a02010605040216060b0105 75
    0x50b940241e908110a00001024446000e070f1113115416414116013515200c101c00c24400c0042088080c0c0c1b8416001d01c811001001251f403401c0000241c1d100303035103541410042e00e4001030880e1310340301146004d40081100712405000c03031150305c095070981d600b400007071481180d0603410f0720b400c1f000c03000925a4404230b500803000881c80010028824610907800b0307000000c81da00d0701a00f916a24080901161402d841102e68640c640e410048090342144980a29005c030494224482d465030701c4400c4d0751080c81c019280d011050103060010701c1000c000d4149010381101b00d8034903140b032a20f10000c980150716404008900f100c42c0f079104902d01031085030211083c401704404550707074440800c401401219025565400c0f000c4c80c1ca00c0c4100f5901c0500080c05c59514005142c00b028080190000b161140d4918a00d04101550311191075100c60001100c0d404000540c459505500607409840c05810064000340301107450341c0151416038200700d038240200000c220071080c00303004407100d1150035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995789703 1250 995788453 995788477
    0x40905060403110102090a0e04030f090e0f0a2304021201020f04120620040501120b03100c0905100c020f09070206181c08150906031b150c06040b0705 66
    0x40300140200f402040c0e00c54003101c100d8001450300414000061010049030001140d02903404108010140c00c0280095070360401d01307101e042e90f890480e140004c00c0004110000e2142100c010030741080c8a9040800c0501181020506000804541c601d01c003d0880d0164400d500d400c40d0143e1050341842140c0d442d141a2004601c1c0600b090110f036040d202542c41210001c0e561141c0c1820100c00c4552600c500d0440e50b41d565465103070500041c02035503c0724a9911103407900c952180c143d5000620743c1d44048410030f0110f82425a901c0a68040d91243e000942110300003100e0108560300480085416100b2601150b4001e036200904c83c6041040340e150015070f00c080003154220341c145242c02d03044480c050886030490031540e0001c010204c00d05c40b07038001c24002c0c014022070140400000089060648032215076140040c0000e6031003a4032103d200303120180b2013050507561200104401000301164400d0f60b1080c2210800d40c0c1c5950858081d0f400e2100c1c42e000c40c0300399100e1012290504119 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995790953 1250 995789703 995789713
    0xe01020a09232407080301080c0f0108041e060e0304090f05040309050910050d0803090c0d0209340203090310020a0503180c0907180605030f0a110f1305010905040905 73
    0x14a0a0200c0c5042d03031440f03280e0281c003071094482004207030f2000300442e03845031110507241e51501c45103618200000c064644101d94440c0308012699020f040329510681101d04a019408014103921400c02e01585c00b410060802030b40307461401000004100b1948025402c109941014405104664055600500041511004110910b0a4117a054000c480d18000c0384030503507500c00180d0407030300601044070101d20200c20401c1507035060020040b030131426686100103001580c0060b41e803540040941031980d03a60100700c0087c407110002402c1c810340c4000000b001070081000a0340d20740001992500c203210701000503500a0350390084e68a04200e9803211811621604000d6142d2500c2d8101c0d10a6446403c134881c1e156559030800a004220684409894100100d401c082c90452500150140001081400014a00040181e510100104000130058400700b0b400e00315118003404108510008200141c0051002d5810b1046034000d898101c08140e0300c1342480f040e60300f88900a001c0d9040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995792203 1250 995790953 995791019
    0x50d0809070501020f1b0a0e01080604030306051c060507021519050c04180c260a05060103180b040f02030f1b09040f0303090219030609120c0803011502100e01020a09 73
    0x9031800300c00606c4c40200411425900c07901c001941800c26072007180c0c81d43c024014002850307014401c4901401096900418411106400c0c0d816540724a00040003156a00006420300b8401c1c0003600c901c2c07003034422034800c500780020710700c036013100c0c8034800c1c126280392101141d001038921007142c08441c0f8000c100c02d1407244405824004100345150030043c081c0d006040b412004a5441205076006042c50712070850805503660800c4170340080841d81414503001d62010214100e0b20320710a11584405011203503562840c0200d17050b109000d0003905031050851a801d055804035902c1a1049450b942e203445045001c108080c81c40280e40140c489940d001c88000070034070940050f1480fa0000c1d004802c41da00500c1d501c40341c07414035442541c075a6942c0030034200700702c007460512209199501c2e0180e0340000c0c0d030300d60504911040c4120800b1103203080d41d000c001802801000748030341c8501c2041101d070341500540e9010303500c5a9101d0380042c1000c00041030312941d8031042c0c1e0711200c01c2d080c00802102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995793453 1250 995792203 995792233
    0x9030a02120a2a172502030f0f1e0c21070b03100306180b190f0507030b10020d0917030f340f06020a0c050d0809070501020f 55
    0x40116070420800086043c10103403421a000402e425141503030300c401e84070403203003000020b80b2241c8024403040e000410020222201000e85001d03450284041d00f0b502100da803001901d424410941c0344c0d031500803407400c9603843c1c40c080b50341b16101d485015020050601511038540795400e0200003035118062541180c00c8510b42800e011501940700200c400c0e4503200c61445034950030486803060030710040714092080110b2809294107000f407100c00c02c5118803150362804904400205140301b2100030521003100038050790420941401c011341d08001900380340750000e0107401039500c074500034141c0e03000c95205248001000e118038503c5550b200225810f155007482c0030348540f00002c1961105000c1c00141d804d16034010868030343d803040802007030140701340e0310059210a42c030340b481c010121031074200c0401c144400901810341e0180380185e84d14414901520007040b90741c0c01800520400402c40910703500012828003624040c412500c2850356200126515a104c2c00f80c0c00f02500441d0996a09a03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995794703 1250 995793453 995793457
    0x402210703110d1a06030d030e07031403040e040f060501060c0512090a0f080607091a0a0f090b030405010504020a09090c050d080721140c151f03030203030a0509030a0212 75
    0x1450080c009100c00000d03480d03070204601e03185202c058554180c01446017500e0108203240400c0c1d4203003014000110280580d81d01c8100030f02c005401c05110301c0c0248c03c0e0000510458000e070a040d4089842410581841311400d1245441200d20500c0c07c800841e507580284280e103a138660180041c4000e1495058000c20703900072030801a0000045100407614202500016016242603401011680352408004100c46255840288808482d07444e2245e40c41805040360380080003814815806d01c0707020400ca4100f10310350701030912a00c010040c0010090190000e0b80180e00072241c44038803588a200700e4040320040c00000700b20248001c000c10950414120303016000340520000c07410070800d9104e141c044400030003a0140b582040d11100800c07074015089020008048850904008200a07030f02e641d00b072120104d90208034008002a41030008019890000d1200103143c0f0b0021f82c0c82c034020750f407a002699403901031810040041c4d507810b1b0000c1078034481c003000e43c001c0131045454a907400481d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995795953 1250 995794703 995794733
    0x30906062218150c0f0315121412032202040207020d0312110301050109031113020a2a0c03030507080c013603020c040f0f060e0402210703 61
    0x980400e40184007208584903580810125072411100315005140c60b4603003800c15501180c0711450205400701d00d03640006030811442c800c2c140003074a2144182680d041c00703d00c1e80170045c403910074800310041003440c2c56100f0b510121441250703110b031b00e42d02181c41a400111005406020100c4819003c0028495814492800907000602d020800c2c4c0108100c0311705404240c0204200703800341d46031920288580c4445111103980b01d4110750410000030100d80740c0740300c040c00c0281ea0100c0c0140a6660601103245407800f03000841d51401c1914001d0a40c0e04c11400f824241189800e0340f03c245103201c01c0040c02e480c0d02c0004209840d00759503050340d4230341264200b81c50054003804100d01488003441201c181048400f00c80301400d02151464491440d844420041408411280400207400083e036080c0e400d0300300d5010a40300f00402c01100104206000c0304541c0381001d00c000307001005d400d09540600d0085c0c0c2d29040300c0c81c2c080c40e000c005414180c10407030340b940200020008074800042c0c074070300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995797203 1250 995795953 995795989
    0x60b0319020c0102030c0318010606020303040f0515040b011703130333021201091b0e011403040c0501030b06040e04121e1106060a120b09070b04080f010b010503090606 74
    0x180555590510f0881e00708542401c0030349800824400807a8078402d01d907a006a000d0000c1c4142420007100a44900028200030700415940601cbc0e010807109120500c2803510b21040320b0703100c0c0f0b0642404e240005003842070000ca00721240d802d603005034000c82181c814404c0c1922a07000380349550b82e10301f11404140c0705584041600c08080159003070f40a40010060703080e00f000342e214000d403014400c0c600010380c02044483c0c80e00e01c24076030340b0300451908124043c0d83d00b01140c0d5071550314010303582c1800007a14118031200000c10001002000030304142503440a03a0100520383c0c0c03081c01d100d858400ca000b0340c0c1800768820002000200c03031024070304111499180c00081142c140040380702200290410ba00032070700309149040d007028104515944540121040c031203d500e0011104094542808050400703500d440c0003c10840c003c00c140c000a02c03941c1c1c203580d50380d5030ba8a00142c860318500700a402a508080c0844081c0d8401c0c4140c0b801031400001510003030b12900100454805150340c1d240c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995798453 1250 995797203 995797207
    0x402060d02090d050d030507031415040e0111190f0c08280305150402270d0507030c060908012d0b0319110a06210b31060b031902 57
    0xc0c1a480f00c40301100418416401440705030304008010b404d940d40104060300b010700c5c2c5842581411001381301d2381c2c1c0150030442c880c0c42e10413442001c03401502e14180b50420540c24901c070541c81c02c490400401d000c0944507801020561012811550344254103403100c0020441540c24000c83e121000400e81e4044058109030078081801071411500f00d4004204042544c0d030040054606031030b01c03007006184d006c84085142c0a8a0642d0034240c84800607080c0003040c103003001c1c040545900b1032003002203030040c080780d02d0640d40c5c0c80c080c114079896026904c00290072020026007800c0c14050541007101405201c855001000e5911160b5602400b440824070f8541599006684051010b0b505c02071000302c0030f010782e0b5440e05000c4200b05046510038041c0a08140402c5110f500241c3c901c1c00f186203081001c07240e1100c9604070090504201d1280e801100d100b0040703039200d0040e0100b400c0819450035600d201200d100c14200700c54991050394801e41381040091000c5003918004270b90000d180c00014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995799703 1250 995798453 995798467
    0xc071e0f0c03110906030714040b040204030c0510050a17040510090c052107060c140d170a0203040f24060f030303140910050c04091a01030e0c01080402060d02 70
    0x3400084810015940508030a1003032040c41002d0000c078a0301e460640705081e49040042c082966a8000e00c1001142a000301c107400c1030351303143d07007080c07824000081065460b40c2c1ca80c02c0c5903e0a44c401e101321441109500505486140680190340b8044c030113846500031000001015903845000400c121142d001d100c5c0c408201d481284140ca00b25809284849100d41c01d02c0c0030f02801c0b0b00c0c01180c0c03404003c004180500c011000117001820b07a151803034580740c01005840c02c21200c0daa4000143d6203801020440c0c014180d008200e0b1241010302c4a0340c00054850915050880c0b00640d0058100c5015040010100d80e00904500b581c1030401910007215800003200d5040300c0e201d03000058190785a00f000c00c00e0540c103024144840940a291403c00e080c52280386594507003243c0d444203129103c600059484c070990098070000c0c070900400b0f10054400d00100c3c403211010040c120b0200c0d180000321241c03204009038020541e48103840720316081d20b880e020061650400f98140b06025003c00c105 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995800953 1250 995799703 995799713
    0xb0604020403021804120c0b22082107110a170c0f0618072403020405041e110406050a0311070f03180b030c030109020a111e10050c071e 60
    0xc801e01a44041c46442d103040030300e003164100703180c4181c6000700481a4041c00100d010660100e801111488641280d0b0f141e82c0390300e00c4030784840b50001c1c02070400801c801a08003800c0b928201d4104e41e0bc51a80c4041d0342d00e54003a11050100c0c03803450041c0d0700a0030a100082d4040403c405184c012044180c1415020740e045450300c111022409201e03088042031113204221240e804190b020b01c1809409224148805503e20480382501c110140100c0e55090401da8000d0b81250044e11015105103c5c0c41d14008280c46044c030240804020989005040e00324140d414090320243c554543e6124034004c400d210440150038000411104041d04001c1c11000581700e100d80704c601e0b071007621441e9a0084900d4000010b20483d81302c1c00c1c0c0c0071000c1081090b81c000e0441201d054861000303005032210044074044039202d00d0020340428074030800740064544024001c1c80c1c106904228110360654003070440000a4400a0b541016114024802c0400181c40540400c40441c402601d010081e6019111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995802203 1250 995800953 995800969
    0x711010e0d24050a0b0f090c070804060905010210110a0e060c0d0c051005060a0501080403050d0c080a0f0b060706050405030f07030e090109090203150a0b1302090301060f0e040b060402040302 84
    0x2002c003400c52030300005051100034080c241d408a200e0200308202038501010849848101c0c45062098001e60300103000076400405681900750000078403510380d40c642001514609850155a015110f644420203100e6940d0003203d40702000c400e601410302d4072000098a21403000c8400740e5000b2824820030b40c0c0680104900c008803100c65a503045a801c45082c130b9800c0400e0008100c82050802c0c0822601e900d0b9000c00000b114028680028a5a51802c0441e268060040e685000350304155040442a038000042c134080c0c0248201002005a503034000e0089480c0072a1154000d0000c5c800d500214040e9030203554030601a806032841c00701c03a08484010355101500403400300380001251041ca01700350f03041a024240d00e0740208070803956500002c3c1ea403880b40d09044d000d01822000200101125045401115405843c1110b40d1240307110348400381d004080341a0080d803030180000303250210080fa64080318000c2d40038a01c1070b00ca5449004004500400842e002902044004010303110104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995803453 1250 995802203 995802233
    0xa020a1a30010b19050a14120105010206011706130206040b070305070308010909050a0f03030605040c02030706050f13060f090b071215052d0303040803030910020711010e0d 76
    0x1c8140085100c0c000c070000400010707000950351180500c00040c3c014030151072500512100e040980e2107299400c0100c5076980001c04103c079581005c6120b035101ca8103001e0190580e24240c00380e4501e46c0c0c84211081010280c614460901d501c20000302d4040c480048403126418009841c0b58941a11425844a143d0081e075048000840015540041c140d005044074050001030500384040302a680f0b40d21340d560201d00c0003808070b2001c02066020140258880c04c020800a40207001c2070111500180d01ca40042d4000c0d0362503130403c00041d810005034082d42d84a010b0030420a036080c00c941e05d81030010300c1c0011010b40da60765103449003004500c2c2c8114080c0708034800c0c1d43d445061110590781d1400e442110a81c000b00c040d00c0b04041c0925926031410844213802031110250050b00300f007042c1891070f0507074401c0e078141c00001408100010080011403007030402d0000c450004075441d55610403881440c01c080c014a030b00c104101c40705c2d8402c89442c4082030b80140406015010394480c011441c47c010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995804703 1250 995803453 995803507
    0x60e150301180605010e01050403060c0905030105070c05011103010323070e0c041401090612110403080412120e060f0d140903180603150d020109080a03020d080105030a020a1a 77
    0xc0750380300251900303000f000003501c42031904588600412001920030f01440c00010086c17502e4a828111092007400c4060003440001c001f8480f130708101c0b001810600003444203886950030500d041946664000480307049951212a1400d00d40c0190f038102c00f54181e0b1a5881450302440318002288692225894001e010403000160746c0c600c1c042c400d04802c9040301084d414030041c6a01000304a4005007000b40341c428210010417841c500d4442404203200d1f6400c001d2991101050118622030b605020b802d01c3c52284c00490030f240c408042c10399604e6640b02955900c20b0b810402013800900340c0340602410200150b010405210302d005080c4419400c03504505603a0000c104c20742c05640d958145001c04005403110385c650705050400e0012403107903051850080c106840e4a6086910400c610001000d50b2003d5079201c0001d850000d494480c482003c07000503000400224580c6404614050080d40c0100850501403030030540102c600c42c002503a403400407043c0150321202c04104076581c08001c880c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995805953 1250 995804703 995804729
    0x20a0e2d070801050d05060a05180a080406081b0319091e03140c0715050c030d090b060a050d0f030e0a09060e0703062601020702130203091015060e150301 68
    0x164200600c2d1010580c0010300c40c3c15a2212070010400c041100d5400c80880d000200d046d50f1050a80400d4006040002c0ca1510803030041c201804445000307002951807554030b800c3ca5884098203082d0103032401d20034146d08202040451010201002101182c0541c0900450003100035155000c0c00048411030510200300703001154200750b400101615413507000a410360402901c1d1140e10384d0780019002e80601c2d010000804031f80c45000e5020b0360f00b0382e083e200869560f49003200101018040502c0200d0791001c400c0e01180e2140b0300060314806450024020781c00401c45a20380c0b9200d41d65140090b01400346212004032561280b6105038081c000240703012030654038014401042d05402400302c000c1503d044e405014500407201400c1e2082e40800440d079040d8000c0d85900e009200e0f40c0d00003075003c02901e844a02c00032080c0c020314401d0700942d00740c80c00c0810003034100d41541d100a02c05143c901d035240040c00700c60701820a14500c1140940170000c041d001d03021120040d0f00a820005030a212 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995807203 1250 995805953 995805961
    0x607030507350c03070501020301080708071a03044d041103070804030908060a0b190b090d080d09050102190e09010b03090a02130b030c0a03020a0e2d 66
    0x20b024101c40404000b107800c10141c10b0808030044150418030b044100c071080003071220000b040c10010340d1003090300440210342d41e503591800c03103558504034440c01d1401e02400b08006400c1401d140e103401e0203c42522560303d55961652100b02003000040d01c2440310b0001c101c2601c1c840880351030b01045080708203210085030800300014500500d06140a849035007007168005651041000740e0342c0000f01400c01c00c2d01c5454600c2c1c00e54410103181c201c4e5030303944102c1c41044010603441e000805824402e40d12100800a01442a80c013441e850040303190482d81040907000c141071000c080c0400b070b4041c5e0030302810f2024665801081d9040f4400030b80d41a900451444026543d003003002c1c07001030890500c0c0301e80c2c1507a80c0200361011014070510400d0b100100004201190600c0004003031030b070007003940c0256640800d86038010240480100d0003803045100e000424100560a44141ca80050048601a282c40070180c00300d0b100510003d9066081840340c5c1984030344642d42550701c5450440c044d0980b0b0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995808453 1250 995807203 995807213
    0x20c0105090601090e03180f0a03170304170307090315291807021015170601031106040602280c03111c0201120b03030912030301080d210c0309020607030507 69
    0x2c000300c4105242d0410445095040c82250750080303840c0042e40e51046c880d541c940000c4003d42d275540080c00c0e21310f0403940d40c000c8400540041d03204922643d0361140d059600f020503081804221448404030b02c8001040c030104480014a07007a000c001e040206541c13039000d80203441d2101c94101e010004003c40c0c0001ca0328600b200d20460400f141101843d62403a2088000390345801e040b04c10030a041d980c42200e5110403000e03c841c00501840c10240621101c40261140e44400901c0b094031140c2d013080b0303c820140340000c1140c080300c07180da0052440300303c44800303032903043c412001c55400c684034038001d9000900940c03800001035006402e01e00c60b0b548807a003030001a14501071a17071a0241d086010a00507030b0041521a424518980c002a4002c5624046850343c81850f0603294800340744030048410020000065069800003415900b4200b0700d01c1065415802e41544a030540300c0d13205401e447c24403076501400d1a150302d480c020a090b0712580104800383d0100b2070980001e0030000741202408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995809703 1250 995808453 995808461
    0xf1908030717070804170a0210080f0105090c0703050309250306110f0d0f1d070504150302221104030c080d2c030109050609011b0c050c040e01020c010509060109 71
    0x1044540b1503031818409a5448207240310358040d40c42d46158241000341080300070010749552aa0180546110f030403134150141032150100c4416001080e0300c400071505080c0300c40703014042c40709071000d2410444283d8081c0c420b5000104240c01520a22600140c15202030000d44a803c003c0d15048007014154208002520101084c1d2901013030200007410819150340121005a100703881c00141d164813600700c4a000c1c0c4140c8210142080c041c8403d4041c484003c220700e411644101d0307080003495030940c2907940e4000d840c80b0181d4442c01555a511014800c4440d108000b820942d0002e1a80802c085030b075841e0304507810540341a08038000030b020540b010800c45016103a1424040340c00c5402c400b60300708041d40180508801105009040c81c20b4900f5003200071b0f1940e102c826540c0341d150058005000706502a41c001c5032041102d0010740b80d43c05600c1400c000ca4016014104208240c0b081c48040d200e8501c07543e240d50750820042d103421200b03109444c05111564058521545440e415406039 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995810953 1250 995809703 995809733
    0x206091906020f0d050a0e060c060c1308060c09192d080c03100b03151f1e0e040206042403050a0216021e0d082502030c0f19080307 58
    0x5584441000c1c03503050341190a6508088551407d034405aa41c0e0011681c0b6000d125980182c2c0d10a0800307201c160040c2d00081c009102421a0054505503540d0899070345a80075120300c070350841d081164410909103035018040045112040c110010340c0c5034403140c40026400380b040c0444000c00da04012050914400d40e00400112008101d40010280001d803180e4103e801c1c1601c076552040d8002c2d41e42c9050040b5800c0c200c03204100d0105241c80014009400c45041c20b48200541038140414840b06000c07242c0c4c201c40000004004c118200b8807000100d0380d02074002d9a10800502c00000d1440c8181c24032694855500300c08040900c1854008d41540c8001d4500714866006115803500c03c81e004c00c146407940c0d011a10341000768070311700303076a007000c03100d8247c0c140c000b01c80708200d10500018500914202e441e0703240d2416019464a01e80d902681e4494009505800aa060060520700740309017010085006001400c0c0c81303801c0d1001840d04899a101080d02c0c1c01c007282c081c040c0703d014001c410003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995812203 1250 995810953 995810983
    0x3140708070f0f0207050a06030608010e01060b0313020406031217060a2d0906081b0402040f050607051204081501050315060603042a030209060a08030412020609190602 74
    0x1140c20501c0001d804640420b001100b0401c8412082841910800008004040c083d00d4610140d031a003e005001d00349034001c4599640c00e200480030b01c90701c144586d8003100e180a031400c0c00d584406000d000180c0064409a074084e8440c00088007040d00640032580d40b031041e0300c4004214040417000b503400305000301041e11960350800700300450448546d003000c1d1503201c85243c0e181210070900c095403003d4030742c0202602c0391902801103404400010410000305038654428440f181000401080c0d103d503000742100d80b0410342c000c120a0030314002070007020748a102a544090034845812080c0e400690080c13131a0f6011444400765002c1e040440d0303000d044160301501c01e0880101000c0d040e01c0c80a03126a000b42000000181842058409041351401c001c850803103031401d89940b40d15946160009a11502010000c10110f1070407161000440f030f64171010314146450a1010b4001d101c019500740e030408402c0101c2c8415590380042858041000b040300c1c071703d4905180c0000d2800c04c0400d01d24070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995813453 1250 995812203 995812217
    0x5090601060e120a080c0106080f06060a03060203040302010b18010501030b012a1a04050304090c0c0c05011b1401020d05180703080f0d050f070f020a0221030408030406031407 77
    0x84010340c40707002e4041151050303e03110b003c10518410a4030340340c0c0000b400362112601180349420b0240640081048a9101e4211229404880c54550b15400c040d81c040d5848040043d00700b0000b000d94004c5c40d4014002c0c0000904058284081600c8aa218001c0003001d031503c001401650b07050f10031013103034070400c0c40c001050a03a5030051808ac4880703100710710040f0400101c80e900300480c0310200c0700b941c00b10301d48032100e0f41030914000b07075650058010001b035241042c0c1008030f6a4460f62007010100e8001c01c800401030b1810005452000c0a89c028100c01d207080a00c02c008104c4140c0035004100307a11000581e1009c101d604a4102c83c0302500c502c4803000b0351240e4200c0b0f42d00c001039605c2544e402103e040c2d50ba80c2e680c01c0d608840c0c4246064818000d0a0000704800d80380f40e1620365114810688031400c00014042080340c8403814140001c2d44040b8904001005101921803240046200e0341101e20789a01c40e044140385810650046c0000b0740c803072051201c0c5000e2021080d070040f0782810101 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995814703 1250 995813453 995813459
    0x30d06091811060d0204030210020610061b03081504140103050d03020c030a0f030b0a030f14010c20070302030a050d140909060603151f11030406230f030703060905090601 75
    0xc801c0b900104105440740d803020400c80c050811030340c102d400640c0e004150803681d0540000194642c4c2007100ea80403032b02d07075002001421900400e81000203039003a051032040340a90340c3d002e54805401030703d00b41c80c0c44003010a1aa16071076503c6050003201c6c45904d410229803441c07400340d00e0f160f61912440b003014010b21016182640000c1642d04040190900743c64603029640704400408014401b00d80c0100c0e80c03500001803007281c00100388454081d0f4902c0d4800412080700301e00384c4280401d80800201c5501680242c8410000c1e21010035030a581900d100301c0e52600081d1418400311001c1d51070350081080c00715510380145042032105001700030385042c030044100003802e10300020010b500514000001403484804008040403001c80105804100c1410700e81480da03401c0c0310310140003c214188194440d074400007040e80c08070b0341d00e03a40d58002400440ba580c4111002030030300c107140b210180710301c0020750b1010000d1f51050b111a41d00280e071a00e02510f03c0c068400c00380030340700603801540040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995815953 1250 995814703 995814713
    0x130e06091b120a02130b061305030114090601091104080615031b0607022101110d14090703020d140706050d1d0d1812081206100509040c11030d060918 66
    0x700c0491601180c800428050381d00c105c1d80035042c841086540204005100380c0c003440e02c038551100b9200700b900200b06044585006d039450060549241640e60720000040040c01d2182c0c210008642c843e21102e410617555825442c50940140c82886401070303c00807101c1c403030508010300303511601e083c0c00078411206940f001c42c0c100d220341040030340600f182e03640203840c59941c6915038030040a550020022006d184d40020b032a9082210040340060804035101da2401c5801c100d24021710041024001e410310759420414080b0040d84125020b1980424240820200f840107800401080c0c071185d0b03072000200c811a00b11340600d14410105100352040140300e8100080c0c100b8021058145003010210311340c1c840710000c00c994810900d08a0150005080100540c05841210841c5003816060b848000400c0403072003018401c64000360f030500860009140a42100e1f9404000d13040401c0d00754100440141140d220310b61140075241c6400080001d06814413440028075000b00e040c8500e51415522 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995817203 1250 995815953 995815963
    0x6040c0518100308091f0306210203150403030b0910060206010504020a051c062114010501061707050403062d020a0903020d0c050a32060702130e06091b12 68
    0x4080c02c2600045901102c41e26908208100701c4151441c6d5100708190b00320040282070940507440310801c800401425080c4c0700418102002c0e40200a803075017103510007045c148002c00030300903400c04d038903409100d60742d4036130040d158000ea01c004c1c48015440d080140103440c00c441a4481c0e402544100700030320950754041d0554071091501e8110b1240801c4250b40c01001c0c2403680c00000f12851010703076402c009031100000d900c405200c2c109860303030b1a11005c0f0300d40c2290000d02c1800b001c540d9185c0c51070b0242c0714203003000f94080300a0030708504054494440d50704130765207840b00356403968220b12020841003032440c00e65a1810400070541c509128643c00501c0c41a00e40f00c0240220440352600081000000c566005801c02420b5000030743d42c1c81c825600040412481510f01c1ca401c6901c4e240f4040030540360810824000c1d044c603191010a6082c003030710f0341c10f03031000302c0c410781e510f8024003180002072154130301900da10002000712411760422088001c0d11802001d01c101c100311584510080f001c0740d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995818453 1250 995817203 995817209
    0xa08030c060915150d17120c09102d08041b051e12030307020105060a0b090604051c051b0f0a18110f0a02100b04090312020c0f06040c051810 62
    0x1261000d13a8000c000814080e02d01c191000302a500c10101ca645171520120180044450f1640714030784d1501c44401907001440745e044c0054001c85091032800126005460901c04410000401d003c0420220240714261007980c070600c00042c8410140010302500115040a10341c00d075100151440ca01302c002880024081c4d9010000b43c049099040590386407e160380c1c1649610091b0f07550391030100c100900a001c00c43c2c2041c4075014038100845c80101500a441c402c48001e004249007a09182c01c2200500300340d81c0f480e0509642c0c00c0e40c4400900240800404105420704580f036141e5142c080002e401a0300f6640c90049556800c1041011102700300d0305d020802c00b0100050392a08603078942602d03c1002248401c90030009072441040b0f500103803103e13013a07021b8007080010644440c20070081c2c0720401c0c00500000c201441100044d041c0703900810f4100240d2048178904a80130702d0080c01e041e01102c0030381e14444445401c01c514104030b00b8210b00440c05c8070242d901032604000c14550421640 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995819703 1250 995818453 995818471
    0x703060e030c030705060129090d0f061e0b0409021804020a240306140d111909020304020306130203060408071e0f0c09050903090114090a08030c060915 67
    0x119411159400a00031140b640b02890140c940c2e400113418060360b504801e2190080d00c03082c3c111b0604240e0740e010f9000800e0042e0810140c0f42410040404c00d40181d03254041c1c0d951407500d1800d400140141c4101003490340001c083c1c4062208141424003100c6c0840307180740c011400c0850303036030040e655031103240d180881e1705d841880c0075161390010400110250700038501050340080510415808600c403540b03041e42d140c2c0c0c240a4640c603185903040520b8043c00d400c1e00308144961640c0001c0700c8001103181a00050401e00e1000446d0b00c0c0c0400007440d13540045800d42c0c3c008140000d5040c18000b00d548410a000b40030b5a1340c07280d501003661410010805822200003040400400c43c509100c98083e44140c0c50704c80f000e1007181402a24058070780e01c115445880450002601000c60148034419403403003002d141041c00220040d079052500403207000240c881003284c1d40c40c599030f005199001c2c1401500854413114600c00e4a0318120000d410405142e0020a80303c030349000242156038800d61038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 995820953 1250 995819703 995819711
    0x2010e0a151506050d0b01090f0b0901210609060f0f050108130b0a0c02060a09080316030b0a090222030b011a0c062d0f0c16330e070306 60
    0x305048030010720901d81202d04050180000007596603202001e0901d2022880f410882c00d07111000554095529100300c14540000176000c00844400030050440700806051082031403000c10540c00541d00c01c00003402c0c036035641d0300701440414554429030000d854040c140d0300710181065507000325100c06108850400c2102070009101680001c3c41090740395000e00b60544506107245850094046102503800600c100c100094407400c00e40100901603400c104051329503219002a000c2d621000c0a800382896140d240000c10358a80c0c0381000d00030300d4070420068035441d481c044420f007558040000249106400014404110122202070440d42c100904182c0500140307090355490060340350301c4d4207600071b43c0704114101500059a1050200c5844440c100c03103403e0302c07040504901650180c141903004400914101c0300d40000b4804040716020400c4d0694140d0303988190030005c00c030110080907400041c004101400042d01d010780da940700d82402212140092280d85200c10321014004580b2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 995822203 1250 995820953 995820983
    0x62d0e0c04080105010b0706050c03070e060d0902030601030b16080709210501020a1701050d11040902010c0b0c0406030c05040503151021120302130905100506180405010602010e0a 79
    0x80c001100c004055000003408550396031144074100303030001041651030608090000e0f442c0400c20040303038400c03038694840d21600b40d405070520100d9000600446150380d40c03001c0310302c050390381002024000c52103400d80103d9440d00d50501c440a20740c404981007804a603806115401c0d801420541c251500c6102c100589506607408910801280d000600304d03500c00110761032140c2c0e1100038407201a20f0124426101c0e607840c414010030702c1400d040034040504030100c1428500e040d81041d4101e60051500305820314040d150b0842d103942c10380f600d290a0000180801125401d03000d00d000c00d00250905904041c0307420007081e1100f100c204040484510030000401045501080343e020b003420741c64114444003c494801c10102865809541401c10421400741342803003030007252081810a078078102503a02d052001b0014000140c401c000701440410b0102d141d450b04400382c8540301482d0596621fa40b100d000344002ca45c1c068020100f103904212040b94483c50004440c00c10310381c0030042c2c084040c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 995823453 1250 995822203 995822221
    0x4080d1b081303170d1506020c190306110a020f01110409051b13030b0606310b12070f020606010f0f0c081908010605030f0f1513062d0e 60
    0x4000c0d08001c1080e0b13141c989a88510710108060007640300c16540400c26079018042d42040d060362840b41c0d00040e40701200e505141d04000501c10545030021148080d443d46958848040d500300c101854119040406c081070543d5040040d20b40082015008000e0160b42e880c0214140c491ba0250200b00b40d110700108540902c070419060b82c0420005500c0c4e2034075610207200d001c420780352200303580300c81c0c0c1d80011851625000080b107083d0f6035005044003414003e290b415034071058807040121380704041d00001070000000e50090112450010340b22a051400340e0001e0211600c1da0440e10840d407000f8200440f6980280707003000710021501303204808111042045450300d48134500186018070100c0c045044002c01c04085a1144642e10b818035542e89601d8125101d020441d0f8100003100748001041001000c0c00006401402d0b02150700201e0186070041982ca41300c1c1038102069a0ba40e510400540c040c2e04042d8110645264a61880719281c030422420040580a00300701e1800001c040b42c0551 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 995824703 1250 995823453 995823487
    0x52116050304050f1e0106240f02072705180a0209090c0a0e10060c1a040204090f050615101205222a06050d0504080c07030804080d1b08 60
    0x10450341151081c0056080c00c544034181c9017a088941c3d170030300390003140c03201005200c0400302006e8030401d025001400012559141012040d10640c02413034004600d2803400c5020000d280e80700005101140050000380d400c64000030000c1619041c080380d1041555030100e00c02100c550119500001512204280703824050054003040d4000000a000140c40364940012446000e002d43c100800301e66400054170700c8504182e009011603c0d41c0d03145490f001c0c59408140d0410300203800050310200c0f544d41d078045041140820366641c1c2c00325040010301c580c0c2e0000ca0f80300c14000c1c0c64100d034190003c0c40c0500755983d0b40c00070b05802c0e5100d2001800220340e00000950707444104040b000e1050302400e00e2550140c101d452005201041620455a40c007584880c0b011a045035035a0303031800810704041401044042c204407841401017044102c4100c0c1040000069802980825611440d0540c0c85140081c2c4654200c1401501600c20000d660255181e440d2550058021030381e0b4192024015442 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 995825953 1250 995824703 995824723
    0x140f0d0f0b040825050c0a0b1209011514041109130b04200d0c021c1211040603060806061f1407080d0504050c010201052814010605211605030405 64
    0x9612002d40322807000000600360380300c05000c0e10540305078003075517024820100c4c11402380600b91a000c1101010b841c0420306001d50045148000250901d0340591160005070654041e66102c6a0310340f032a000b030b14062042c00d400000c500500b03480d184464010403840d44180d400710300b61079034a5a482502e0307100c41d0003481d5000c0c8284028400c3c0000211000d2030364100700c4400300780918000030004803a000254000b0401d107120803c0084003800340c0c0031502048600c1221010903241e0b031414904800750390142c400340c9078a4a0204095007842003240c80c2800c000c00040c481c07030320078030b458800d41c0d0404070f0018001c40da4030f000f250070300036040f61804521401000400d51280020799251602c1982c0c4050300540c4244199800168150012401c0c1c41092f2002d5501c106984400b8010300300001c0d005609001103140032492048000a01c00c804809a028070045400040c001242c08404841d541b24442041554103ca05000c209040c0ca40d81131a003000a110f40040400e080c030804010309220 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 995827203 1250 995825953 995825977
    0x1103060a2028031b030905030d0b0f1503180703020f3a020f01020d0806040510050402033405040303080a180606050306100303020c0f0118140f0d0f0b0408 68
    0xc04003000400400424100300d100c020740741c1d04058a13850a109000e540b8100c4c0d0004029424030780003480f81c8004120400d03125500518003600e03d10036071124440e590078000c00c4842c0c4c03500c07071900e807812500d800700d80e104104e50303500f003910113100581d140240f1009103007056812085203482c003140030440c1d425071100502560a0725494848a01380714003082c41451087d0341010380300c400e60005a070307241a00c84440021400d07050008085091545c40250710a607803139a00c11a480e0742d000414100d901c10369403413103901982c09a1a0309911072a085200e0315a015060031503247e071500c8010454000ea01008007002504400306245081d140c0000e020391000b084450031103003041c580200100094821740d80a400b6000009010002c4107107010101ea0b010b4014020011002c010880b02900b0400c501d07040c0558000c412001460006e01e00000d07110744c12803905000c510b84104078001d10500ca41da4030812260306901c0019200d881c1c0e407023034294046000c9001d0745440c5080e0005000b81489010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 995828453 1250 995827203 995827267
    0x70b07020322030510060b031503071206060e01060503060d150603150905070902040522180302160b03070e0607060f051603050109020702010509090403090807031103060a20 76
    0x90010074155042200e1185086420341651805c0010a80300f0f03600c40c24950030703028400211210580b01c0d03108980103006090b101c0e055144e0610125540030241c00307884280d6107080c107000915071101c0d5a40500b00c2c505110b03081d85003141c002030001e01c0d83c01e8000d0001c0080c1100c0300c41d4a08a80040001e140d1040815241d40c2207500000000c20800c1000d0303a4611805500040040c5e5a00c01c460541c1c401902408002908008a03005502a40c4000c58103540c0c4201004600f031540a148103800e02c42d901410f020140e403e41e907241c040302d541100e0404002001440031079070700b080750f2081040c010343e0a55240c9400d03040101c01004a050350425280c20701303040010380b0000e20311000c0c210705c9a840030010390362164120401c03409020802804198100003680c4246000c5401c02d9000388a4508141000d40320a409820b001030365200315030b17110040350490b426103028403000398020101c84040003004081c61441e012507a8209080e09a90b5000988801225000c03000c15021b004c503180d114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 995829703 1250 995828453 995828497
    0xf1b0c01090816030e040b010237052b0807030e1911030d020a0503030601030216080d050403030b03010c0212090315271b1302190215100b070b070203 66
    0x800341c3c003c03010480015a564204940a20300761160003041a01a030050500032201040e840f29940c400c8940d81100b90b40c00314250a900710a00020040362050010300b003070501c0200ba03810203400b0121500702d90741440041d050040d921121550344070100740303800714003803400402c550b082100420320145240d5010081d00c083c4182a100785040328819412200a0000703040c0072a252050720714000c289030400c2000c80d840398481c2e00034104070100703400c1202c885040b940d00e408c016481145070a0100c0e85803400c00c0b0906806204404031082d00f50300a00405081c1040207446251346219940c11010104086415840400440b816214240c400c42e505042001e540f517017051003505010007550007070000c1d5400f66000b0070b07103030301082d0b03807990007410484020b04002801003c21a80c4241325400d024400e4402c00c5000f8191000c0ca964010780b00c044c04244040340d59013402841c907601129101420041e0210500480e050960000c402c00b2258440800880c150301c103004503650101c598401c02c0d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 995830953 1250 995829703 995829727
    0x3142e12060e0c030312011401020715020c0301051b0328060e1b12010b030903070b0408120108071a13080703031823040c020c090106170f1b0c010908 66
    0x200000c00c2d91004944510058038105541c03071141005420444124200400ca145e444031030388449040140140d50006840b00c0312006440040400400180c0c802201c80a01d0705003880340e290880c488031070358401080c00d803ca01e034003440003a06103d00c00c110215021041d001221990302e10240c003000c14041c15586d10f41b4800000d0040e00c0382d1003050301100410302c070110b2a00440310314000101c1010303596031070300c456803416810003008251180010410301d0002103116107143c0c030507445001690303100c040c00c19128010f0501600001c01e198000e5000b8041e0074124a104503120b107a518180f83d0351450b014065a1503801503124403141e104218010081503042007803c4500041181517010351580e6142d01007030503910b4138816410301030500c680c690030b0805070005000c041143c01240c200034002408208440000d0b840040090381c000e40e00140c02c240103184680001c0c4449200e491420700000c2c7c02c201b40400d00c080c20405d5400118000a680290062107405c2c0e0130003070050700c4075108412 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 995832203 1250 995830953 995830961
    0x203071a070b010b07020306070f090f06051c0605061801030e0d0f0f03020306180606072a090e03040b09031603030e0405010e1003140115140103142e1206 68
    0x4115800e8018000100384c0300320704c00540745641e4009004100c140c44000c0c05407011040d000002c402c0050102010805081d89502c403801003031165109680c48456038400000001c0c05000d2202550034039a00704050344e40c810507500e9600e6000302d64000d21075204011380050800b107840002038001c40300400c082a41190220044000c81d80b1428027076251444100d0403403000700d403030741e41c0120000c250292008040c2041903210f48060901e03890902039444208003960303140107070803a10041d28844040410a007911a009041c010402c0c81000030000000707407a409580100d075190540410b0201c8036a500b003140c000c90f840304c640620390301902c80c14010149024a0b1050b80101d0070b20380001101010800c071584685c0518020002c1c4904607911a20341445101178181c1564803006007042904034840c0740b9008084074000b031740021561200240036039040c400e0280c07000a4000401c030f540071000d0760b07003c1041c020480503491345800540aa110103003d030403005c0f116030011195420000300d940 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 995833453 1250 995832203 995832217
    0x130203010e0f040b0f04140a050c011808030904051302090106030906060f030302060601030903120e07080d090e160201201b1f3303030e0301091a040203071a 69
    0x8000515680b24500301c00d44a1041d0f9005101c452803c0000d07814044080129030854400c010740340c40c0404c000483d624025104000780c03540c1c0c0010b10403150759070f0080c0e42090009035500d151440c03d031800e440c80c0e45a000e03894241d4069030315580050700315405508010b0b01d90703500405520003940c440b0401001015100c00880714546058808900000c0e0104441c0841e41d1540c0180429a101d50044000e80f0b0850740440034401105000f140520ba68080e08221510840060982c00d10f084500352038023600b41424414020850401e110050086668941c422210b405000620b00e2082d81280100109400d00411449085000352416810f40042c1244002c10b02034481100c100b080190321180d01c40800d2a2861022240d2200c0e2110760b00030104540b82c01c00859000000c9090809000c02e040f00e02da0659040c0c15000e008240e0440711220503810140c1c000c01c10b0010790f41c0c1c3c0281891903010091240c0007404c0001c1c085507001c12424003d0b00d503642c046d540c0c00b400b18009074000d0308100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 995834703 1250 995833453 995833469
    0xd02060a02120115110118060f0e0d0f120f09050c0f030d0c06060504180b09070b07020405091e0304050111061e1306050c040f1203120f0b13020301 65
    0x200d1000805802507820b41d110030142c085035646008282c1260303050701d100000c203214500c0c4000c601c501c401c2c0701d003180e03601784003142c3e002d240f14a00c1c1101c2200c4ca001c0019641d41d2400c0520401c0d098000f814600e036a4503401c041400b1071591400341c45c0d5180041e102d1319808e09041e4494002411504280c00c0d280c440c40071aaa41c00841080000013400e60310740c1070f05544410323024002c6e14420b401c1030200a02400001998075100d80c049002e40d86d03251401e01201242c1607100c020444107031040c650048008000d0b14460f41860502007240c41440c6001c0e03c00c94554010502282080c02a4000812080b80c00f0000425404035586c69030020301c41d450100300c01c01318042c2d01c1140842c81034803c00c1e000e034441004554103108a841c0381000f624500d0303c0c1c030f0708010860001f6074511030103025803003110803a511586881115415502550008034110301d820480c00006900560700101918030241c0c041140c094030b45104005107410064142e1008403421303280c091540ea03034011b5050315844 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 995835953 1250 995834703 995834713
    0x161118160f020d020d0f21060f050a2106020c1f050c0408060406090c1805010e07211a0310021e1e0a0e0a080303060102060f13111306080d02 62
    0x1028141c0c2c44000c4080b1000141e005414540300b0141b26034414803030358010303080520004401c01c15800d2504082e40c0d4030404d85070f07510780078400c0352080c858000060104a070b044031007a0801c4020b041072184000c0d04a4811000e0702d240c001c0180c642c0541d0b030100c0c505e004032620544c4010b00400821102461070707542c1460b0502003070084440e08100c0d816501d09800803c985c1d1200d60745c03400204820201990304503034902c00441c09124000ca40071206100300030100e00f40d4100b004080c186000584240c05008414101c003200e5280c0e0442898501105000043d0012282c2c2c00101d006a9040119900d40100f0f00c5101d80b03d0742070b901400f00c407440600060868802d58001c41282d1244000303a8420580c030707030b01c884840302e41c10b0300410442280c0d10301004820f81210120b50b050308581c01000c4141c0000c02000240c3d42d040221076070201c1003c80c9140241451110001c48488000c070107080f0009a00100f03000c0d4413500c41c005540303a142802089070399a0341c468983c03181640704c030000042c024 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 995837203 1250 995835953 995835977
    0x31707150213170a14030c0f0d1b05070b030108030c0606030109030c0b0406020f0a0306050f0a0513020a020f0d0c0b07020f03030a02030a18060501061416111816 71
    0x36910035104039000c0000140e2000307090070b08007070106007100280d82d02481680f41110018400920314600d21003948020358403102c02c0e1540d5401d1200700d0010384440da218500088a095100008412084920b62001300003000da0030102e06103800c03600a241c0100f000000010100030000c004d0403460f60384070030344a103911590101801d80e0a07107000030300001c9445007000042442c4403452600b0500c00c08d4014584001c0400c20f80e00c0740c00003a1301c58046a5140c0c0200143d0609544a058801044031000031603420040000c4003002100341c94451554007003841146207000f000311b2809e940c1e14404170740c40c3c1515034400030b02000010004032008a01d402c00304030010300001e00c9011000904000d10b04580c0c91443d04402900f00500504221ba102c1580c085030711641907080308480d0240401042940c101040a0310486c8030b02c40d1030300c40700c1081105848100501405030900c03030f4889020075101e401a000104980c9104401104141040c0c0c10300007015058021000301e03031001c1e200c400760418 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 995838453 1250 995837203 995837243
    0x20c1e0306040209060613030f0303051608070e060904110d111c090201090e1e0c040503030706022110080c121b06130915080a0206041806031707 64
    0x1810509682607031040c004640140742ca000e0780d45c0e110030701500d080e0401c1c000d1a075010905a540e172082e40c90850314807500c000c0c5580742c0501c541c002c070041002a0150002500100010402001d00c0d007000030001c000c0c0c40b40c0e51102c003221820f6000604c28402c10040348803511181e1711800386000c1c02445c01c00e1b0030711344d003116000361040c050680c1c80c007103000406045404007800001c030080741000054032020410704980c03100c8030300030030b028140c079004c2204020005201c104c0107080c001888005010410240e40d00100320340c4400c0d40001c007d61141d1144088035480b42c100070007031050200309410828082003030201c000445075000104c0b1082c51102c014000708a031144024803a6030030500304981580c25001d045000141c010301094038110b401074414994100c140c102100300394032000c5003a40e0740d200070b15101c080d02802010b001203403110b9002030040e1281d840748401059501c1410391404103039070310880065400c8016042d8a0100800290712030740b081d1000ca5220502070040000340d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 995839703 1250 995838453 995838499
    0x1031e0b131e020705120406020f0f07050d02191203050d050a060f0302040902180c040504060b0325050c07030c081e0d03020c330c0304050709050403030b030d020c 72
    0x2c001010701c2a0503260b1241500042d50002009844174400c40001100c0203020300010002000315074068640822180070542c1084030004610807c2d41c84800103100541e00c809100002c02e904031509585050203a905044010040e40451010f4124040c010181a0884000c1000c0d03a0a41c1e41001260b803001131541c200c40080c0601d9100700300403e428401400d080d848010560b0006200c942e1843c40c80c141c80164200484042c0480080490200200d0800b402500098031000a101d03003545815003c440c40e030004100499040705a800000c08014081d0088410b00d896078026640c1c02500c0742007214540c1c11030300c1802000d109843e180c0d0980a00030000e0a4940b10301e4001c1c0000c0c540e00e51046019401044005005024044000e02050240840720f03400d4911041d1030013483c0c105014000e600b0034024990054000100104000035901007201020348070500000501ca0300c41d410210000d04012903029094450352607691380d000e4002854030344404084071034411151800307000300626 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 995840953 1250 995839703 995839721
    0x503040308070207080d050c1005010303110d0c08030705031e0403020303010e01060c210e04020403050a05010c0f02150c091201051f08060a110909010605030402130605010e0f01031e0b13 82
    0x5e40c01c07002070711240c00d205400078480100790304c00321007020b000d0300c82c0002260400e0b4000c0f40420150548210607500c203001032800354070103080c07070b040b420f01d1521541300c503110003000a01007003000000124001d007103803035408000301e01d01c403500c106d460980340103541c07a03000b0301410500220a100014040f441014486220b5902c0492070008400e180041c00f54944c2180001050228007807140c40161190300c00740c001103006000400d00c120485c10320b6801c40d15908010000c020b4030f0303448002c3c41500000d132298000f040304030850742a940c102c0304041c10302405e1000c2c2d03170020500d04c400c4d100000c15040700c1d0041002c2001c0b022641c0c40700e404401c0012440c41400000d8102400003100e0400035406102d00d0940c0710b1200d407400702d14000180c00c1090980040340890300c088140300c15800c00003807201488807081c1c4100720701800c1000107400d002d2040c003035a01c00d00d00c520001c0040e902c41d400801988808004070303080e801c0100c0d02000900b00d2018598040c1f4941e00322103540320341174000d140310 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 995842203 1250 995840953 995840969
    0x2010206100b0901030f06092a05031e06040f0504030503040b010807062c060a0906030f06120f020d0506070f12090b010b0c030403020a03080a12140c280503040308070207 75
    0x5840f2003580190050b22995501c480c07003a644010028035001d841c05580200c403499103075205140da002025982c086520041903007000403e00410446190480516410500c03540b00e608860f0b844100090184c0329614091a4060900c030a00c0704054001c4051805244038400c690616a210010a60348100a100d58800903199200d83d1062248034003454126160844404000344540c03000304825503c04100d02000411044040040c29414400c0a005c503038450030034010b89103441042038140e480480050a03600c0d10420400c110358403d1401030500390b00000b612031500d01a10082d01d107070342608407140403a0510340b0324031002400d03101d51403406903c409012416406d01d00814425002a1803117860f92204000100260b603617210254021803142c20015a40c00303803070100500e030f01781d84030900040320b0174804e034440c05094008503142d00c04a0f9014072603d072017103024005004134641c00d40c48095203040030500519030784a0000d40c4114000d484d0035000303031559982207a0b12040da10900103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 995843453 1250 995842203 995842207
    0x10020c0603130302120705030a09290a020115170709052509170d0e191802120115030506180c030403090b0a092d0905100810050402010206100b 63
    0x909002c0880d030650340307020b8811200d01c031019400e0f0020f0b070f078002c41c0e05407443e500104144000703990041d44603000d045160b550103550b014400c80320000d9004082c65080403c004502c0e0b140f064800d610010000c06000c4841102030b0751101030b08070100e0f04941d0404d69000380c45e8007013803900d02405607074020361a0200c6000c100003050859400a5204c02c4002c00f0084200000074409100782071038030305051120098610381240c090050701402030305042a0107401c818a8003185c05081c08140700c2103501114000d007001d0a00851003009104103410b100140034080300100e1042402a1403a030310603d0780d10100f00c01c1c1c40b5242000740c00954004813129080301030000031301070401d100140da080fa12a0a1450029031a200c03141c269822407400c0e0800101c09910030050299491908a420b43c0e005280c440480c01c001c441c200756454038061101c9480e2500046a140d00810420400034401003059890701410445500040c080903a01a4010300c40c2c8804104405c810100860840701503044680c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 995844703 1250 995843453 995843461
    0x3050105040c0e240a0933080a020c1f051e0403030207150c031410060f230c100f020307050909100305160302011403010501140c070306021810020c0603 67
    0x400408000c0c1d40e1000d60030b0080b8104c00c600f9040c00a131030b0003183c580b50080d481d0b0800d0204540d4050480c07860030201c110080742101d43c000d060f05c100e070b80ca0f118a00380f40a6640c2440e000080d10a0502c40e016510a107400c2c80c080c0d888a107441244040b01c0001480380b62200340c281c80d1610f443d8240e16402c1c030034440c00301e80040e00035401002168400c800c402c4a4410202c407040813a0710305903900700402e8030f03013481a9034031904011041d40101c0c000d0030b0300401410702c0c0b801009a0400440d010500113040750044486403400e1021113100b010000350703591801d503081525224030b04810841222802c112501c9001c6800d4000e5a10a004943d2418200740c003600800103d030101802041004000460200110fa01400a8081c1c822085025005a45544001080c60048550088032181d05100510880ea03204980f00d0110180316040e031b4880003840f0b03031203040071300c2a4002414503100150541804030148106644c001e4111106100e00c03180320002d9848284684006601c080200005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 995845953 1250 995844703 995844709
    0x607020109050603040c030c09021b0109050304121403030901021209391918050103211119140a0c0b030c1c020d051003080f1c021303020103050105040c0e 68
    0x4d15071060241840c450140d580342c0340c0442a0b5500d070064500c19030001001a4440c5040389803921b54041000200030f03079172868034de05403170f8041c90041b407a144c0b01c400c00b04800d0140c0301401a514040e000c0a980c0d0380d04000002034002d5221000f0382203100542000103080540118405800c007030f01c91540d60541e10800c1440c40c845020b40b07200300e0203010a24014029840381c1c56403070b10322070744141074207070341c1d420500c200740301425000741014203905240060000948684c01c485071003009404540c208411031605884000b00d903401c02505100f01c11031900c40402c44580074414502810094402001450b0742e0b40d100c1a48010282402c8c0482c0d038108240c64141c00159413150700c0f0200c090400c030151000f96983c841344038094500680100d10f005030320490b88030780f64000c80c400b1442c10344d25145a58640039400380040c420480840031030310032181c1d1210740a07070781000341301c0d1000c55071110014010f0303c003600700d800141e0020f8500000030a03981481d10030344010b840c5686420705208100e50130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 995847203 1250 995845953 995845957
    0x30032812110d0c0809060a0603020d0605090c032e09050c010e03010e030409050f0f061311190c0b010801020c0c12100207150c0e100f02072c010506070201090506 71
    0x80310400c002000601e01d40d4125120302090307184250389031340c401d04140c071040b0301d0507001403c0c50022130328008007040107075503106100866590183c0041019511552000d041007803d100903a014000d850550601003400741c101854049042c881e030001d41107214001d8120750b41003034001c10365071003040100da0541c000e0240d401d8010000780041140d070554904035043d900305a1052810340d4840003888881c0c0c090b180420790000c440c4e401d00031549400400210f0122040064200c044d95540004e2500c81c40d50080301c50650080c03940104080c222080244001004441540c845040000118200d030b010700071241611103400c000c19030010312204218065000b4610030615218884035078003540043e0024003900c0e8011403140030800c03d1982c03100305481e09110200100000e134030310000346946031103605884021500e0180302d603940e010020f034588481500010300c50186041644000038414041c81c0300018000c40f071030340c20f907038410a1007550700820300d009000c110314a0040c081030500c100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 995848453 1250 995847203 995847221
    0x131b0e0f010e0f040c033f080c3901110703020d090501270806010906081b0d031b02090a020a1d1c051c051801051830032812 55
    0x7050032150300f095078451150b4a041078451000c2c0b0002480c2d640d940c10110751540001c180c4109032508001c0c8265241524010085050131102d050703145031a024030301c950ac40c010758668000c02051060880144240d00404800c8005200d0000e0444a20348111805d20440d501038540660321400c00d0a11038100d10100801c1e008103044a50004001d141041018001d0625100014100c1e0801d04281c0c203140c0244032b001601c404892820503141c8600007084019601482c4c080710b40900405443c03608a0b0840000c1c2d404001441400510940c60380203200441140e02ca41030032015091040e10640519854294008070009400c00007040e500d05d555080b509c10b5090340c140354009110325011010b850500400501d01145440c1d41101040041c1d81604007402d02030b04081304a40e042c69002101124140100741c12410140c00d002000305503240040180111665034100d51552980c0740c2000156150868844007400c0040442c8404020841d0b52907640d500000000b440320740141c003002e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 995849703 1250 995848453 995848493
    0x30c0a330b040905060a09050f06040b1902070807060b040b120c0607110307030506060312040e15010e0402040b07210f0305061c150f05131b0e0f010e0f040c03 70
    0x5110f000228180200c0d4072900105000148000c1981007141c50f000f0f000d0b0203840035500079810700000c14580100c06600101d001c031000306940d1840d00e42d001a003d0480b004201140c041241c00c10440e041e0810200e4540656040100c40300d00020401031501940da10880354021040590490801400a01c1081d008503212040b5803107240100f85010860f6005680c950400d90612410780741c03c0c01001c40e80c0d45c02e80285401e050408007440800e00d0040c0124800602c52114088203034003802c0b06c21140c01c0c00500c11912141d5502d068900c03070740074080460f5011a28035807105840240428204509000e94030382e000805450405c1d002410081c1800307500c40c41944807220b20003058281d001c4c07181d00c0790315030441201a4000b032606445185841807865400d00c03040080410a00c030b0300c4860940c01070001c41c940005000e0070070314061150000c56110382c42030104035089140001039412601d01c22800c54550f0b0700e211020070642c800762001054124220420800b286500f0411300c1c0e40b004103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 995850953 1250 995849703 995849711
    0x7090b070605060d080a050309120306013501152a1b03060501141206070f2001110703020f0d050315010302160521121b0408030c0a330b04 61
    0x1900c45e44c0854102c0420600002d41c00820010008414464910711030110208207046041c9000040d00403501d08543e50b5442e01c0c24508085240020411880c8030352040003a8405541c407450940b008a80c070580b6080803620040c601d41c88582c44810f0702c80700d000300b50030010f0084980c2c0d49680c44203100102942540d10f4400000c03010801601c0380c0340c000c1611030328582c81c01d90300c0020f006291110550200d000d4100c1e00c00c0181c0300350012b0b0288000240b0b854902c4604400003882821030404581180f21503203082803800308000e4480080c040d0300d010341c0807a404100d071945041e98079440c118081c40010024400f00701c25403d0101e2141c07000744141005800c1400e441d1f0103a0294520050a407030b41c3d03018a41d2110a0585640100a02c200801d0300c2c9140000c5194007210091000c0c1c200c10340719842d40c07200302002050340f09450250041900b40d0740d43da10001e0580350361720300c0e01c00140d400030709041c070f40c070710b220f01282c85420200b0044d0034402400d0f0100124000801442035029046030300d1f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 995852203 1250 995850953 995850979
    0x91c0909060905010e090c01090308130e090703021f09150306080a0b04020a06030903140c0715121b1d041d100e030306090f040f0204090602030f07090b07060506 71
    0x1080c010000039142c0020300241d10361400761144400a4054101000d0b0b400000c1c0d1103842d40da200504009a039000400d59950f5080400b60140c00ca00541c05080014900000d00c0070b10303000032950303200700d81c003c440551012120700c0f048090440d08441c07500208404403020852105001000c060654440c10005090b07552100080e007040e6200000b12a8100804100300851a0602c02d84010b4460340ca0100b141008540e00904000340381d00100b01400c0002c164100e46003c204520b001400a4581c500f007400c0720003401030260b0002d10b0486150602f081050b00e0006011200d1081040681d602d480035119140c102c07500c52010b204906810907101d041410000d50300e421061001e044e80002454281111003c12086607100c407166040ba4004200b480426502e1114450b00449814900c400580b21072800040b80105040e00940140c01e289800003800420b90107103218107500c043c4a0195901c1c40c02c12601240980204c2102c0c02d000d01108001c00ca0550060b43e200d140a00300c0e400e1115 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 995853453 1250 995852203 995852219
    0xf150d0b0c0d0c0203090109090e03070804121202010b0f09070e03191b050d021905040f020a08070c051b011202120105191a0c100c0801060215091c09 66
    0x1a040390001c820720700000e0b6042e08402c0310701c5100b0001000303101039802d148a01c2c000a12041951203009d4045840c0c0160348801007060040380c480c603a21059082e9506d0b40e86410102c0d0580801095680718040010034202c107006020f052081b4800402c029180940700c41040112080039081d80200b04031143c484c4403030744040010541010091420060161451070940200c0300090180d030054100c0801c2040325498410003001603030f6046990079020100c00342d02c0c103600419580300f103502a003084110340659030540d000f4006680030780c0d20420950395808058031a114900e4008200781d000380500703180d04030030340079000030560149460b0402075070400d1080166041205940c20001075400100a14641140d140000d0170003c01c4091180746400c081520344c1403000d038050b0303800c1ea0004001c3c1e0442d4084c002c4440c581d40c40302e004c100c0c7c25202c2100400c40030090203458090711031a031000c4010303095065214420b5107000300400306460560b24001c002040d0306002c40500c802d100d40450200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 995854703 1250 995853453 995853473
    0x12180405040b0603010c03020c03040317070606090b1003020a0e0613081228050904050a0902040f0b012a120c120302180d02090f060a12030e0411030f150d 68
    0x760094685085038201042003501b1070700034108400602d0b1040124510003040803054504885d00120261340803c10352401c0f200e58460010000d043d54034104000c24203284039030110740001415128426480301d1100d00390200d12848281d032011454035410310380c0d50320b48100205402080e4a000301007060f9540380b910724004441100960507040441c40c0600340e00030070b6020b01c601e4001c181c9560903c00d07020700a032103441002c2041d0b0013540c4032000a00da998440e0403002c1c8075940500104045c400124240004010740c4142c107000484050800030b08040d41041080310200e0102015100c941030b540d44c10541f0f5804051006000c4454035000110380140e40410140100d91005685da40c88104100301580f60071010921a01141c1503180258503002d01c240c1e4885010000c00c84c498489000080b44510740782d029114170000e0101e4403040503440982101c2c040030030345082c010306000107502140c901080700c03451110280c0100213803400441e50301c0c010200340082c00201132412280c4403102c1030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 995855953 1250 995854703 995854711
    0x6050d031d130c050309010c031b05030717040f031205011a0d06031a070f090f2106060807050310050103120f05070204020313050610030b010902070309080601030302160b070512180405 81
    0x201c0c0002c010004480c1b802e0041c6130400000745000c0205146040560840c1c1280340001000c010000c000100d17954082c01141154254032820000c02d89080e240040001806080c2200010500c980006015009008590681d8a42040e030903001c00c041881035103e422100e210100940c98500000204000070200e07180d50302e009541d05154a443c90020303141c182022001000c00c01106030800003450114804003e440390100880c42681c03112044003c41d85c40d40d40c01070405032400c00700080d03182d00083d0910132603109400340c41088002c1a10a02214424070005d014050300d95607801055200e0941500038401c6d034145103040c8015500072404a03001100e221750080d103070502000030f000c2d08016855001030a02d2144400d1825542c440c0140c0c1e6040c8643c090300c40d00130030301100b0140500300320b1014105060440e6459a528180203681342d80711503100100d003100e40c40100e50b0200794400c030b50020f0b402000602140b46407200302d000540c012100b04050b50514032403101d036075403a03000b00360017 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 995857203 1250 995855953 995855957
    0x905100e09010e19020d1506120b030105130602090d1e02013b0303071b090c09060f260a0504031e02150705130b0d06050d031d130c 58
    0x40c445102070244040040e009044500303082c0c01004111070064140d424201c0315403a0251311652003030b10350009050038200c0d0300e01a802901c1301046030303a071191980320741c25080310302031040764035484c2030500b01c5009a45010012982e424250302040490300100300c031410191404012103001d13207505080c520103010101060a079403245100b076692000c155107903002e100101ca40c4924112011f00c4140006102000101c2c0b21047d5000240c1c4c0e0900030307030710b04642085203003134002100896507680309501c0c0580a400791a10840e2448140f041c00740d0015900280c88072441200804029076038100c1c03207a44200c01000200d0b0102041e00c080c0c9001d4062040341c0000715040c10300e0701d00941a50000a440b1501f098150418251664005540316640000c000801b80548510728206e80b00d01c107441000e00c0c41030500720f00089880c4e80c98010215096031400c2000030a0306c0c2c10401c180104201c50160020b4105c6401805a0221181c044400c9100802107400038044002e0001030703d034001001c0b00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 995858453 1250 995857203 995857217
    0x4080f2a0f07122a05061801090b0301120209060102011d0102030412260a09021203030402240a08040615080a0b01061e030b040609150e0117060106320301031208010b030a0c090510 79
    0x1f400b96000300381071005d03007400d4695508660404407802140508c0040207440f90100d03034041000c5d40d00030b40c490030000d0040902c0364405401101914041e41c001e4500b10740d0002c6090260300858800c0c1c9c00b00384900c245090241e40b140791000008184d0394054003100c141036941d00d00800583da00c00ba680303002034100c405541c4030b1500e4010001b402e0302d80000303403010b100400511b007a84101d000c1251b5580031141030121141c2ca50f03082c072074000d0030180c081e000d6902912a000c030701c2480010b04802450320503120016940c2c0c0300c500854402c2c00c2c0c100600c6501c041c0801c00850740c2c1c000d4200c100304041c0640700042040d9680c51101c00c0ea0300780244c0602c0080016800d106059910f41c800303001d440b10003c0d00c8010700007581c800c0c1e03654170140700d54010002161402002c920b01340d00e280349001c8024031220000e0001442103840d0342e00c2807008031440060702e00d100000702d0007200c03200c0c12100007050450650340c880d2a107802820800d09860b04219004001164030781d40d403d0f100c000311803141c0e2905 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 995859703 1250 995858453 995858497
    0x90f0708060411040603020c01090c0311031e030d09030c170301140604050d020409081210050f010c1a09030d0e0d020c030604080f2a0f07122a0506 65
    0xa010030001400141c0070b81d00b09141e040c080903c04088900301c803010703d001a9503500c500301050050200c0480102010060f40001051100c06081c040c3c9146048040d10088101403c42c01c0740300300260400c0d0090b4200380038240340340d0350305c1e07000825450003410510349055540d50303101c80341c1c00b17a2001603403034210210051084c1c03c000760f07240508040c16280710389081d06040000d43c00c1050594001d1150b504c408180c41040001c40035144801c6000101d241a41008010140f03c1e5000c4e000f482e0190507045801840c41d0710580c210261590003c10820382034000f50f6141541e86002085e0f40f0f06840704019407550b2580c540304c2c07451001c0307000010346000601c0e0280203081c05004084c9a01caa4480340920001c1014501242e8040707000f81300d910f558440b02400481d140016031019803007181e40c4405000d07401008641607061102c1c0d441503461054850061001110b4500707005052035086441100030b1301030000b116048121014040e110313013a40c403000240b066218951210001c01d80207142 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 995860953 1250 995859703 995859707
    0xa0201060618180c051c0212070503040f0210020118050c03060106080108120d14040303092a140609030d0c1a13021003110f18030601270b090f07 64
    0xb2024008035180c0b00c580180740103181400e0441e00ca000240c41503680700c0c40381600b4000d030112070200d0300b81d0f0351001040c980701d00d005000f0340000c84502590041100081c2c5003510880c100ca21603648030703c1074894844150207110a0102c0543e504080d907580b100c074241728092688511080b90f100700021305214101d003042c0340c10404180d22000034400c120005100c0d000c0080350310b078600300c0600c11140e20340d20025a03000191159080781150031400e441840185640364220a040d01d0091b2500203050b120075000c8840c410303c0c02005024510501d600b40101159185030b2004401d000741228104240d12000a05001c00c1411030400b1031400700030703030040012001c03d03059110a15001111f4618044cd003108040b81d40210003841102c00c0380c01c10820600031f038080d0a45806044010b529581808403100e56680703c0d020082d500025490b09808520340003860340d05071822503006c0c4801c80001c4884111807510700314828555a2035541d0020a40c0358526a01e1152150080501c0982000080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 995862203 1250 995860953 995860967
    0x90c08010e100b010813290916140118150e09070e0306010302061c050a0609060503010203090d03051801051f050418080f040b0301031a100f03080f0c01020a02010606 73
    0x34180b40305090142c800d12680e040020154011404583e02c203403016186004403005500505400c415004d0005000c200540381260078400c00000017150081c0105001700280d1024078072441d1404202c01d6103010995100d18048100400f00b0800a6203298446819079050030381c1810090014500080565440c0f500e002e800790088224200340b414441841c02290729420140000b9015070400100c5003a40400c03460000034280c01e0050420860034090703803007000752207284100120070f070511401144c24901807084900503800ea8004003064040d030b11003940a014018400409a41d052040321241030080c001c06200b9000d2000c200d04400030a0700681c4102030316001540140c4ca0300c20304001d151083c0c03110300c0d100c4e034010312000d8803840743c2d01000c0c030740d4400e0781c010142081011000008204007940310701c00f00001e000810f03000f80d0760810000a0102140729000c5603550608040000c544107400404460f00d4004c0b20074582060090800c1c01c1e0380c00b8a48030703030050b9540d0f842048410b0f40098 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 995863309 1106 995862203 995862223
    0x151b0717030c0d1a0a08150a2004090b04050c03130f02060d0908040315050903040621050123220506180903030405071401120b0103090c08010e 63
    0x200d564800d0a00313101d00c1d0152001ca003000c90b0140d80841c81440d52a18143d418000e42e80e03403101a0068940c0301d003a05207402c1d130f90120281c2412078200500113006410008240b2a585005000c11110001d20b4000c206d070051080c0300c200d03415050b440480c290800c903403901d85501800000e03024445c5400c9045001e103002c0500041050701c0010340216801503840d075104040700c021510585e4011511040e854004110901940e401614103000607441c0c4a004181c504074149044200c034001e03008207004030200504000c008008c40008121417100f03030741e40e4000c00980d54a114000000c02d50000750503407070b040040c000317890f072045c01d03107007554958428a0541400300348942c90754025a03081d60103015014011270011060a40c109a00d036060f9100d54803c4050804000106a0004864100343c0c4854130240800d10084c07003200509410000060000c0410100d1440d00340c1c4a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 995683453 995863309 := by
  have h0 := BRFrame.cov_init 995683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 995683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 995683453 ≤ n) (h2 : n < 995863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
