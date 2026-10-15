-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:10:17.88766+00:00
-- url     : https://prove2.me/submissions/eaea7c36-cd7f-4822-96f1-5e12b8ce2fe7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 994964028 ≤ n < 995143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 994965278 1250 994964028 994964053
    0xe03210118110711030a060203090c090c0711060903070503071520100b0402041d011a0906030c090a12060204180c050a0f0207050307080a14060403120c121d 69
    0x4034541c0e00c0e60040014a451003e0703450030111200c520031a609800391b42c0c8000c000c00c0c1c403880518812007110f009407000650314070421040340c00c020541c010100d400e016641c0070803810096203a1a08007920541d540381c400c40e0019203030010790f51005a00d8480c2c010045090441101001c0303104c091a250408074030908030240391806240c4400c0e07411030781f091194030750825154129200401e405030005180584908a10741c2036040320781c09683c443c03242001046900c148041c10002103102c4071441d400e0240b0700002407510b12001c1c0c1080c804101c081a241c040c0e03a10b40c103a0310002d00b080001c20300180d00c03034600040a074005100741424010182d030a0818040c080c00385004142c40381e40c0e041d1420081080c03d407032600c2d03d501144214490400049450380b420088203029141d00340043c208900326144c101c000101074500036202c0d0700039100348800641c02000342140c04141c41c10220b1000800340381281c44240640351140402d0030315400d4041c034500d01403480848201e060564a000701c1c2107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 994966528 1250 994965278 994965281
    0x5010e10020c0a1205070b160f180b030a020c0d090f0b040506121503031b01150303020d11011404140c0f1e0a05190609060206040203060a0e03210118 66
    0x64185459400950f005800a0508a03400141c91924104907090801c1510b40b8034200c0c404a5450b01040c00c00c3c02501c140a4100003070249209070740c0b43c01051198041a48074031000310b445480040c40d400b1011600c0b03c900c90301903072000c0044208540c50040340c4140148111f2452003041d015959049000c070303118051204480554102070305551a10258103981200e480c00142048203c0c4501e8080d12403a40c4e06000500005400d05001502e04841a084508503100b4480c0406010141c0300208002a000700f03441841072114241850f4004080e240103024100b020300200c0c880040c0d600300070800101f03048000c2c200b1002c0046501e001070b803100744809480c440102562010b4101d21090711000046889110f6840250050a260366104086911a0702d60480c40d0560311080d5010b0200d10340c0120024024050740c4010240e0303042c00d0b0082901e171040600142079850300ca490030000a030b0100300320340303500b01c0c2e10410903202c4803045102c005118082c041c9900a10903200b1604a01d05903 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 994967778 1250 994966528 994966537
    0x915060f170c010e0102150a1d0115030b04030207120b071d0a09181a0915130b0403090308070b0106031118060702180f0603010f111b0304090905010e1002 68
    0x46030010310854040500640d0810403a0341c240f4114841e0381c40c00e11074205070b141c8290023164104400310700203030004018030400c2da00c90004580e0740e150030b58808180e8008085101140e406c00d501129686841c02c0480c01c20b040f41e004148540c0400b0700150801c41c401030350f40c0c481c400c55512042c60511040201301c40d80c1018200c0c560044078104240082600c650045400b40a40e444203111300489a9400c0f40204d030411084140780410001c028648c1c0060120039450501c480000040745030400c1100d0000550b5a4081e0500006400103000c00d405010010702940d00020702c1070303c840d41d40c80c02800c440424005c403070019013000399802c1c0c7c1030311103416103070542c3c4800c448181e0003440c070341400442c1d002440700ba6440608500003010a8841000c030034058038080300c56088a00d0400e0500d4292480341d41005a0a440d00244800100e0841e080e01c0240c41503110940222401100540c50742c0620f8005e9580e00b464240704004219055100004c01305558040c0d40ba2450181c2178034089008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 994969028 1250 994967778 994967819
    0x30c1507080613020d15080d0e030d080a0f0509060604060e10060c0804320f0f04090309081903020f0a02090f100801020f040302090f0907120203010915060f 69
    0x1500350200300b1a24080d0410039901d60800c00c01401c00c0b0300725560030261850000c4040015202c003905004100341401400c0b40d4a0550402840400120020a54403100032081804002200c00412060803003500301001104501c0d80a11983c10941125a254942610007a21a618003000065020034440c4820310800040040030a214600502070300c44070984542110441c20411000c00d031030740c03151280c0d40001d50b030703c0c040b4030703100ca1391444401c90031100e00d8401d101e0f01c007007104000d00b80e6803d00300d04840f00b010303100488ea517031591034181c03900c15070750304070034402d000301815218481c48400600e92018040c0c3d08a404040080d0011500c9150201002c0e40084031540042c008000c4445041d42003c40d02004644045c2e80e102070508a8204082040000340006810419446e01030072044d00030f6280090068107092080909a44401e81d00c1598080105a48000195903083d03209282003a04088504080f611451240c0c0c0181110700903002c42010071440810180d20f4a84070319152003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 994970278 1250 994969028 994969037
    0xa02060306040b041b020a0510180311150c090f010e0904030c050a0b070206010e01060305060f0f01181404060e07020c1c2103110702061603050408030309030c1507 72
    0x445820902020f04841580e10340c005032116041c07140c040840c02c41c1c0c5071300310142d8051701c504007481c0703000e80c1080c201c2c5030003107082030038404066503155a5074070200e04c0d181e060600880117011003100a00388154600032403441c01e540303410440b03c0380d0008004c1081c488110745001030002c070880103540700c0181c001001d0301300b0305075800a80024054084210043d0107031040780d6a121640c0d80d1845200c1040301c0301001030b086600100a2900507030300c0c41e409451ba508040c4001d10307044010606000b0489002d610402007480da0803183e0340502c000516180099220f03181c0991101200007003004541e00090040346420310024064180e98403c43c0203008640c040d103840f040368000c01116940d120441c404d5540384000e540c00140080c52614241d4281c0c154103c0c00020b00340024040725481440c0c0140300300e0802010700184d5600003220910300448034622210340540c28125010f0140d604100c6207440000103002400c040000039000001c5c8860441d1002c00008640660b040c1e029659000408c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 994971528 1250 994970278 994970281
    0x10e04020a080406020f1b0114070e0d060c1229011b0f0213020d09050d2f0a1a010f12110105180a0609080c06030c031605040f03060203010e090a020603 67
    0x282454005003c140841e98041f41081c05c092108101c1c40903c540b02e022aa6561560b5081340c000f1180190b441810307420301c00064800d51021038200c59103048010095980c2d42130b006030480c01011200380b4004e9640c0c04100a69010100e80d200a42840200c03040f000711f038803094250361203000c4c840050880340d0342610b10b43e480341d6a941411000160101c1c3c1c00045448144503943d0248090304041c280c0b418082200f04650a1950411101075500c004004035214103019a01145d80b50307103401104000b0340901900d01e0320207642080d000e844020302e50031007408491203040c41e10350258182c4614040703103002c8656a0b0b1000c0d2082102401c001c0c14440480c858203003a40c05000a0300c142412240031640004410700084c855a184d904981c010034488542444a00b0b020083d80c5c0a941040c0c5042d45103007064009200e031404024190b11070080d0180b4031940711881602035400400d600000f803030042e500c80c40e01c00040e400c24000d4020445000c000078005010001e00d8608564010708480d265 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 994972778 1250 994971528 994971533
    0x1c051308010213150905030d030605120a030f1206030c030b0403080c1e03190e0d110604021e03100c1d03030702090f0a0b12100b120c0f2d010e04020a0804 68
    0x6130710b01e2200901444100b550010706500d00307204064040341a0742e40042d10906007401c0000c0079119600d4120b05909c1a99580002900810006202c4015040000640d04500c01c038001a001ca500001e00032640620000104840032400d80c0c060352090311107210503500c00410b101d11f4050b007a503d0031010610102142c100c80303110000c42d0400c066682e080c1c000d207130f1381c40c0310030070b0f1815581d0040c0203600c20100342d47c6581d40300400301041400c1130040c10903800e003900080d02c84030880050201c240c42540c440c4035aa40c04000a402c0800c48560034423030310790004000fa214036140c001e00c044014440d510302403181f80110071140c4441d802084045079803512401d81c06000c5005180b007020f00e98500140340c41d642c500321506440c1208000828800180d81481410741d814480380e00d00648008861007034442c1c0203d05117171844e50648241000354031401c000380340e010184070340f17120000310b00704001800d0100c41c02d80d400c80e0b00c082c1c84210500d8203810131b0104034850242e407100040c1100020500 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 994974028 1250 994972778 994972799
    0x426151e0403090e1014061303060509010225020312040302010818010221061905030a030c0201050d291207120c0e010b030f010b0906030103080a021c051308010213 72
    0x1c0150191a01401050b10703030703103c28440002592560b001c071980e0101001010f0542070091801e0f40140d403594107103000a0082c4030380c031500d4000105010b48070300c0022070740802541920034203070610000c41d81c1028903004ca0200041004030507070003402501c0b4190361514140b0200e0342280c0e4180c1d5a110559036160891901e0a449a00d07180c07655001c0050403049002e0380b0410798082070018214069041490800260440f031700c0060b0032070313074030504104071075500455a50102c1c0c0c1c00d800c0030032501c516840125428401c80d00d00d05889072030102c0b0114000218514400001a001e5080c40036134001020000c524800c0070b02003210742d010711401c4c007070541d41c2c0200515031403040343c1c2d0850f101e40700d00400030301440903081001c002c10084108480107004680e00c9005003202d4032039031f142402030000318801d48014000902589030005034030444a00c2041031405030b10504810340010309401800400380c0d4015141450414003105001ca61400103100300e882901100002c101481d2600070480c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 994975278 1250 994974028 994974031
    0x20913050604200a1106071707021501170d0311160809040c1106010909030504270c020705030c010203130303200105010e01170613030e03030426151e 66
    0x1908540c07100c1c00d000da01003030b0015506aa00041c0c43c5240c40b000e114900030242842c0d02240c082d1580240d09110519800000d401e00c417188804410495a07a11407080e890100a010082c0075050140000544001506400229100c050003030312207900104100310140d0f0b100c0540544508020408861040c00407815028914032808050303003080003120000f42150129901100455009a141714104005110643c0907100a03c0200246403840c1c40040003401940500f1042c2001402d09451940050f00d804a12940b403045c140085030071010001e4454800d0f110316802842540c080c05c000b98004001e407001d600700b2020f0346a42e5855628200d44d030550703001f604a08103a0020701c4003681c890a0103007502800d01c0541003172055152042034a00e182c00c2c103025010f00d0b006041441085909071401c104d003036405142c00000034142e207000a080d407045034008401410303039101684404032400d00200f40c110725071007074442c0100c622804540c000d070111031070f030000e0002c040510b10414a410b1841e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 994976528 1250 994975278 994975291
    0xa0207051201141807030602071103120a0203030c09011b0f060606210c050c06090d02070f0b030703090501020c031c05011a2709010620120a2a0317060402091305 71
    0x2071782c10301d90f00d4841c0e00490788001c5060b25042c145003041c68443c00e08019030b4000040c110340441c9407040041000b5120f0002030101e50413600005264040c0d030f0b12070003030f0f1440036a22901c0e4403850802c901d071034038800303149103004c881d042d040c13002c000350090280844400440d410348500d03400309040200303040103042194281d4240f000500c49000b00c03c40c00c01c0080d10440c0900001c042d8103d609801a160008a5000290010101005010403801401900e800a5032030401046030384c140d141c02406400780041f42802c3d0301c400b007140f40c002440f01c0044074590b901d03104204000e98940ca08a038108110081c655088e160030064075080d034107541c4501403182c03400140012f8150302d0ba00040c541420a0340f100700068051b000034129030058182c00e110318a1198028110142c14105070075032806260045002e00118412014100345884011405824580465483e0b5100b030314000d012426812220313103081c1c0b80031000a210381054801c440d40390300000d051111092130380e240c8002512000f000c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 994977778 1250 994976528 994976533
    0x221010f140a0b070b01080105060603070c0605090f1f0f15030209130204051303120c020d1b120203040602070f050f06071109091f090c0302240a02070512011418 71
    0x3075100f2011000e00b1046201d007400030207a5140901c13035803e40e04007400803071203090b0800c140b044c0d06030020405062583c0c00800495295035035031401d4100254201e10114a01622080c070754044120308219140c1000c18404002d42e043d100868012540854540450108158070074009490460203180e80079003402200c40d000f00c4039501080c01c1d10070a4445410525652441c5e004240d0000c03060490b0854402003000744282107480290340e10040e0101c1c400380b225400c1d0300001183c0c0b008614080c260041d200c0170040808420082d940d5000d40703c0c00006004118002c1545401c0c000751000711000200000a10307600982044515400304008569442c5000c8144a0755140c982007140b10b440c1d00c401502d43c82d11254810142240780394002c03a2064604080040010000e80c217000607250140d8002c0d031500540c46030200100c01c14080c000300f030400480c152400c0d640c00600e980644000761511032010b07500d1001c603800e0320200312201400628100008898080b0340e08480d064a100404 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 994979028 1250 994977778 994977799
    0x60e1e030a0f030206040201030c0503042d06051e01060203040b120604091208010e090a020604030b0901090c0b0d150501121515081f0515070f0212010221010f14 71
    0x181d00020b0b10548000f1809030304000f08000940d0b806109160415089081c241d10b5498656520a9128080c0c008090720504000008a00c000140307059401c0682c8240100454102000c21340e01c0070300d1070200750b00008a01c0001190311803020064600315400801c5450800c2e48407001740e02a100010503454002c3e545001c080081890b80030480c214075010786605141d9411f1101d0b81d0078504000b00900c4043e84034001d80c200603160b540468084031303007026607002503444980b902809000c0c1480c0241007004002c2c00418064007042c001c00c0000d001a0081100c2c681180d1081800d1400f441454045082c980e0307801c0440c1c244ee001180111a000103d00500d91661081401e4502d1260780707c001524034401c0000c500250b100581d40c06540c0c202042555280c03c0005003500c04204108481c02c0011074001c040110a8010714041ca600510401c4c09000404006000b90440000862240c08100d1480010032505074482d059512a0b10603000300d40c203010700c1005011180a026800012068 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 994980278 1250 994979028 994979033
    0x6010f12090201120c210c050406123210030b0f25031a040203060f1e0406180b0a05030d050a0e03030f0a08100f120609210306060e1e030a 61
    0x1103074504440c0c0584501980c6c5e000000d25102d5800c07440108584e940c50718020025891300101598200e42507450705038181c80003445014090100c10108020a40d0192a00901401c242c09074a50025a06440325856511030807100c944614521019000d009a000403c0c4c11418031030786181e000d141004070500408581c0100410a04101c3d00319000a41d101504c40d000312400c04012400341e0121825419403c0510002c1d07266100c00c10f00521030024541051891162460b0981e041e100c01001081019900c0000a40246804080d424103034076001201c155460440300c84402d9075030107402882c0d80a03500c07034292000e91054000c0303014410031640044032541c1c10401000000e40000110352501007070300e8090800300300035080c142c4198080a007884400d1982c800202281c045d161000550300c1ea50901500400c0e07110000740803403e02200340c85514840e00780050300502c213a03400b00300d81d555900e401c444030103030009526480921900c008100c0b10002040d070b860b041000b0252109450b4a9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 994981528 1250 994980278 994980281
    0x1030216060518010203010f0e180111090f0603192c071707080a031202120a05040209060d15021b0717060f071b0303060f0806040b06010f1209020112 66
    0xc00c812180c45803940104000f8540a01c4055a80b07080d4000039411541030407030482e201901c5008032010a000d640000b420100c480304589440c1340d1000082051600c51040c00c84180e00c1202c0c018080d40140c02d40d942141030580440b0712034900e20609000c00940301c98007801401e1141c0e080c0e0301d0144c4003500c655520001c16000500d401c0c804005200c06031a1918540120030301c007034581d203207810002040080e010041603104230168145456074400700340b050b064000303000712103e0f00003558010b420003a401c14190720050040d8000c4683c401384d0780c0d0714410401c0034083c204009181c80810102c80310403980c21740240c202407411031060410400707406411031400c00d807988010035001a2001c150b101c50001e0000a0b0010034101412100f031600840c0900641198500c0042c3c1c1d050503c00801858402d81c4180090070080c012102c0265a4003007240e0341d64002c2d2030035140411858049005c40d03010f084169410041c9482e5020f80c1d402c1a522072006200407170003a41417142001c1c6149078030703146 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 994982778 1250 994981528 994981567
    0x150e13060608120301030b0c0436020a030b01230405120703060203040f060605010905010804150b03030a090503070504150b07060b040c111c02120f0c070f08190f020d02010302 77
    0x60f1610584940c0b441c2821000c2c0b820240000c0c0c0110420072051101881e40000440742280e04c2c5161144c52408069101218070000c130f002c81180d10100c0c13009032559154200001c0400e0036030340c0c0c0c503081d180b10503c029400e220825102c150b070030030007040260f07007002c5108500954a80e001e4400180ea280c941030141c4e44125070840304020041d403008100b10941c46020054242031800000050030000081d040140c0030380b014102e07910012825641e52121b400c0b40030100c00203000d590719a5080003001c1c0c0f040545001d240d11a000f44203010520b410244202c180507900d080c202c9007002d140189a00055000c050295502c0b900c52044100e40e441e92f00840c0600c2c82d940d0350705400c241c40d08070494248074855035943d480340da814007010b2403241d000400132249100f07040410350351f00c0103507580030f99841041c0e441d80d40e6000b001b00004000120684034402c40d2030040540740000c106142c0c2c140b0510090400402d1001d440481d480542040041403042c240b06040061400108101c070365205181c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 994984028 1250 994982778 994982803
    0x72105010303090e0a0501050108180307201e030c0f0111010c0e0906060307021203132f060301080d1202040504021605100c020a060903020a02061c150e13060608 71
    0x40c80c610400954140c49140e603030028405c1000c000030350500000903d800341c05801021800c03c07280400b05014070900807030341c0c0d141c1d01c10202e0f0307048100414201400a60380600500c50070050b406243d0100c81c6490043c0d110100401600703151800104103c1414442000e080c100400140f407808421000d00c1503816008658440c0c0722a29089400c02c4452a80100401d0140b0001d0050004030394001540f6003048001002403500c1c0d0740d0381e00345174a16000c1d180000d45580d1502176402031080f07010b4102c15504e500403800c10a01c02445081c80381600c820310421409034011301c540c0180340c1c41880c3d800d03c022050140586410303610000038082c2c0c2c02603007011002d042849800da08003c02000701420304081028240000c040c041406500c8800341807010f030203162103030540402c25100340088060203174000d0415031031300d0008046040c0b402482c0c001040c0c15252190312020894000c1100007100e89521810855603251326004000d039600d9142202d0b10341d1241c401184461081c0f0080c0e54001b07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 994985278 1250 994984028 994984037
    0x5150703051030050f010c030e07050d02010807050703090f03110a0e070e0607230604121b1b1715061f1416121115072105010303 57
    0x901d004880c0102c00301d980050540000c00205504900d6150306505520440141d1280c40a04500b449030900c0c004514210381075181c0201210815010391001c280c0b840c40d04200c4810b261103405000c4660000c82010703011400501c00110300612510050071260320078031f000200f132541c032490621561043d81040300c0c002d450325051a140c0c10708400761401400542c41025550410302000b5018502d440c8485001e000c0001c0c40c8401d1146c880d00f03444071443e050400c00307403c803180d03414681ca41d00c06031412100ea0001c071282a5a03544034455081d0260201079200b50000300c9580c3e00c0458000c840c0c038031014031030032500000c0c40d0000c0c4640800c6050700000501b07807810305954001c2c0050b00042c005446120030002480b00c0e800707507290804042c007190800d41200d01e01070701d2401050044403d0301c542070b94490510810445c038640d0b0f1104254184e2510300c144840020103640704c105020082611070b1541c00041d00083c4214000061180042150b465681800101c1c1081ea1401d80054000c0b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 994986528 1250 994985278 994985281
    0xa060914040b0709060e0409020d0506010611070e09060609070e031e15011404020c1912080105011b031407050610051f0c02040902011b0614100503190515070305 71
    0x20b409020741e40c08032003460140c81090820700080c128040100b00140960f664034408400c546a880f02210050782040441d030166949000040c41d0121542100c5214020b10f100055a50b040400d034501900140010302640d640e042c05111480c0c070010314110402c00040500c8142d6101030100c02c030740803100403402074031400c1200140d2400d094803039104045400340004200f80d0681c600c84040a2004803000359590740f11036491490030341d071640038030302251441400301c0030031140d114995103003025500d030f40c40b282c0c0c0d072200151078a860142d48500c5901c1c6590107040083d10540c0009140383c1030a00950420300713a9140c2d649020012107034408007010f00c2d1814481032a141c45e00748410349144035180c8403c4002c101c01000040702c0000240125120445c01d000c6a000d03c0030307020420190071900c5452030751070034090040d00320f50015501c10310302c40c0d012945c0c003003500240d00241c0d0800307001801d00b045400b0f900c0d51007151020707054885001c1c13040840207071101000b406006441559002c40c00d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 994987778 1250 994986528 994986533
    0x108190c02150105030a02011b030e03070605070c120305091003020f070506010509010b1e0a02071802190e03031c110a09060e0a14010c0302100204080a060b030303011d0a06091404 79
    0x9840061300304611a51103c040c075030050380e100140c45600d840040140303000180078901540d41c28008188c855050142d550013162413540007000e04051802000b059120302e548044160102082900240002d01d00b00005881818100d82240801c0001e103001441d00c048407640c4281a0401d940c1111303250040c6004104074500403500c2c50250114408080ca0a500604d2865011f0110010205582400710310842000e00a10002c4024001c0221013013120600c160305030025806035122001c03991501e20020744162141481c2c07802a9000780c019868078104101015170f0106028442a007030383c40d05585500c0d80c080d04080d01c01c2c4141d54030b402c400c0da81850000380401194694882c040c07c0d4418040020a445001380c244003442805c000a02c42050304049043c00440c1000315011800090006200c00c000240a4071f17181c061401084865048002c0540b244420300c6030400184050000c801140f140b01ea070550802c1c51102d0000302c06a46d84820404da607020b4040c0c80c4500300c050104001d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 994989028 1250 994987778 994987813
    0xc0d1a1c1106360303030f07080f07140f0904020d050415020702090a1805120a030c0201090506010618173301140d1e110303040f03020108190c02 64
    0x1004034122032442c00c20b1004100e850400c59007440008a014008428011200d8900c211104045018040e04d55031f01c3c1c1074020904034035041e0f80720300c0041d81c0c41c0700040d00c528006107041e0103004070355100c250f41c514201c003102c1c07a41c00500300c201032a64200501c812942d10b92005103441d0030004004100c1d841e1500f8809458008101d001c9101d9004200d4680185d449401c0154003180c02400050b44a2100d030740d0314445050244024182e200386801c24003401072000251040d14003569082c040744030103080c124262010520010881d500100040c003119020703100c40e011070802c03000ca00d003400796134035584030314801038074114203c2d5000418030300400100024418021008000010f25054032490350107220181441003001503043c00d9036404031551095030483c103907a0081c1c1000d81340b03000510490139200725858211550041018071440d0b030304001c0240c50441d4019032101c040c0d02e2031900151109080240514210703868030808442034107052080c5001880b403a8010400e030f160840d031111 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 994990278 1250 994989028 994989053
    0x30103051c0f080a091410060302121501092a050408060c4305071d09060f04020301060f03030201020d2a0e120618060f0c0d1a1c 57
    0x1040b102e0604151165008145240c001314415400138000c1068108072030461000504a6064001c202c2000120b91b0350340c0005040ea4000c40e6510380c030f241c0260603196140302c3c10b00c10815120100c0700401c1105d00603071200200c0c0c0c40b80e0700102104403145402d4206440c03003010020200d00042820300480c14100301541c2e00000c41c0560501d801c44080808500200e40c0c40e44610a59501c00e02c0d1502000303008c3ca069000c4420301041c0e00305005490555104e04881c026810b9040207079156205042d007178200e59004d0001980a040b040e1074400702401c040200400c00c2c0d82540d20f60100240d80203361042c10010742c0642c0c00144c0b6210303888103400039039584041c10040d02680b070280d03030342c04000c10300382c80e80105080c181500d08140d00d002143e074541d00d000f071719000b034001c0300304100103140014101c5550b5114841510b40980c1e03030311654003448d0010b9900d4100d608040c04190100c66950380072011040100101516880342400064000e0b100120040d868045040d9258208114102d604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 994991528 1250 994990278 994990333
    0xb090708010f0510050d050a06030b0c1b06131209081e011503050d0509010903022e020118080307121d070b1e130b04060e21070e09010b0603010305 65
    0x100303500c004e00b80000b81a405000c1401d02c0c0d003075070b80000c40c000c081281c1c454001035610410f00c40c8986811260058150080602c1303000d680c0800103040c0c2c40c00400700b0700350712948800b40070707100041003500d401e039121645a105200780203203000c011500000030031102601054a414548441e038500340014291050880c41004146508070244005640410144458242850900d45504144004a4050704a03510182d04a044c204072110b04061445403180101d00520301c0a400c0e9003c400d0480c201c0300003040a111580d1210700800c0002d40400041d6048101454400c4013100e51400c010100c0310005400c65207403044424052101c001403005100070550205180c0c208945d0003101605c1c203101e00f402d400380f02c800152845c1c00402400e820005010340c00d00042c2ca03613032144c00140c14140f010341580e11074500941c5200060014518150380303468000c0180c0085854072450208100b0050100f411654850404038410f4070b91001441c000c0d0b01540041240c0303900b0261480c00001d4a01c1d48 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 994992778 1250 994991528 994991539
    0x30605060a0c0605072609060c042405120f04050601050d0309050907021507080402040506060412020405180a030c1203060f061110060b22080d0e040b090708010f05 72
    0x862220350b0040c40c0b440c0c609800c43d83c00b249a0340d03074640464159095828080d45016a85044001c13903200000c458810f49004088a80949800a0030a51030045216103107400321400c40d000c4014078207604070340303451130743e4280541040f0214210400c41c54045542c664068045010401802401c00103940100007c1d180d030b1031406055240200f4415450007801d020b00c05810200703043d1031003000030094100c0c42200800d0681803501c5c00901141d01990145d1040381031201040c11840c02c0c03001c4070704445130b2030106110b84a40780d0902c009004024004004030b00552440a4682d50912030015414800ea981c007100c0345062820324911020100300104262400d81c0c14490410b6103119032003510040d0500305802500b01010130316002c201c559680c0d00500f40f80c40010007030241c2028003105621882c0380010300f48a0021280e003905944201c00244d40310300c2003d40301c1401198003160003503014202080da40101d402061001405444140000e01d032640104003901c40502e00d4009000120b40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 994994028 1250 994992778 994992787
    0x110d05190b011d210d02030d0c0504142709070303030e0627030c0d032702010e13090501051303080709030b042a0f06110105060604090b21070603060506 67
    0x80c50964011030f01003860192001075940c00704100200080d89002c208901100c0b184041504020345a410217607402c2c0d40b00e41442000702c40c0c80c1c0900260381c00d03621311509400d01c00f50005e040125550342d480ca44030340b1503109802d03030103c4460501e081e88510f407070741c00500c001c9113185001400c469050161421540004050250710b10020441d03105000120600c400340140c02941c036410b51081d1440800c5600c9031401402c02542c041d00300002040394810101c44ca2654489a00c2404d007084000034001580c6c198011030503e8942a041c2e0074038581c86000807000d50035500c05086810a03103494071741c0c0c40032a18200c00c040c1d21055042d17000406190180c030880c07459854180504016200030070b00d03802542084000e8404030301902c8102040d90203000c5095076501d40c02908906030150400050b04a0145842104140280e0f40640c8001d041c140c6000e2628040000402c2c4003e501640128800b42c0c41c000050015902000003d0800103098030924018001d4201c500650056001d81024030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 994995278 1250 994994028 994994057
    0x6020102210f01032a06020c090601030c0f0315030602030a02071103160515070204090b0a0606050f0702120a1a061305091b0a05182e09110d05190b01 66
    0x8410f03045a52181e17401542c0c1e00c50380c03440542a850707810b10715182c070f9081e800014441e5000641c140e0304d50041d1881c021a803951001142543e524040003008a8429550141e13440d00c250f11640f0182c070100c26041c452078480e61440d040ea03200783c507414500303074021800005005080c0460319140b030303040f4002d011905606076420400103252043e0341c841d00d46c8a03070f400c0e21005801c0450f512207a000b88100140d03081842e1890640c40d055451401880c81c000020a0245c001d0301221002c100c0107075040d041c01029401c11103940701c4020035489501035400d90100281520010310f003002d0f41403030704031024501a002c1c00343d6420f203e108080366500384010300076451000324041041254028050000e034580340c020480b0484a43d00090b0000c10400c0c40c02c00e10245a2482d5002e0980300e088510700c4e201c14402c2500103c244001d0080e080750782c6004006014450780500b04103e80140609d040094140c010000c031807040740e9408a04212800e459410407441c81800b01c542803d0800720000391000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 994996528 1250 994995278 994995301
    0x10213090c030209180406060e0406050403030b0402180925110f070b09091f0b0918060a1217031005090604050f060d0204020c1207021f0f140903070602010221 70
    0x10300645c1d4a010403401045c1800601d400c540b028000f107038904941801d1902d0074400a0004a07401c0d00001d103040d9a0040d641b515008403600010110300c00800000b50808104454001070400c0c3d0804503140c909820700c202e03003072820101d070b00113454a002000780e4011003420b04804288004a40d040107600340891110b28094072007964050714010215500c600742040d5000a10a1061900021901c00940000030000611143c3c0080d0740a5084210301680d28a101109a07a59540300384010824840302900c0c14040310320600031100580304940c0d680251080c0d503c295540071143c0680d1b2020301c0103081020b45a5006241942c04025614200c9980d4442c4680a0100f42c800c0601e181e1820643d50703141c059814105414007910940700148444007020740c800c0030124040c00c01024100c4203980604804800903085468440419400600c11125000c0110390b2104001c001c0c488005551020401035015042540005a40ea0035004a5507000e0403c00d9a00d42c4401e0342c00b0402455030801d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 994997778 1250 994996528 994996549
    0x3020a090b0706021215040e03030408030c0a020a1b0609290a03111810020a15021303050d0306030506010909081b010b12010c1409101808010213090c030209 69
    0xa5084980b42c40309480c141000c3e2003402c811110320030aa20902819080302608083e10082c211000c20402800048554981c00100d07405003255400344000346d40c0d076803440000c10010000d48103495503548640c2e181c9110b0798400b00c2c111410483c65909002030b54001e44110058119441c0021248060220040100c802110200400f1001050810401d4007913040303090010b80031840c046e222251900c000542081c07600300107200707803200e005842c43c05002003050460103030451452034801d00f11041410107984003064000420303a503884000082441403004004420391341c1d8010449500d103051a40c94842c043e009032104a00c1d051801c40024000c00c00c50320940b013040004d00007092000405401051444001608a00500c103000c01701c071010341c0300700302000302921052010074040100540c103020301d01900307802804030340c4107444072400b0354081d4070300c0400a52120300c102d444609603403e981081209040b0703040d61040c24014103c0c540114034000c0103d20b000c50404000a002034100910f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 994999028 1250 994997778 994997789
    0x90a02010f0203130801090501182f0901060302070c051c03030f020c070303020a120215010b070f02060c010603050105060d08030705032e060215091b0409020d0f03080703020a09 78
    0x104409000c00c050700a00607113941c0d50403501d844011954603801030303003c1d04078200c7c1102e01d0751a20b861000e0313000b25210025103181e0050000f441d40300014089070900181180d4035207a484003981c101c0c0e925a02c5212983c060115030360096112401c5142c184001c01440d04a24841e00102001c8030015045441c0d060b070144d010300e004903e0803001b091000091045c1c111001d064064540c01000341500000e07592203862043e800c030b5104001900089803240744800d28051244d000e140100940030740c4e0340207020402d029049184146c2450b0380002c07c030b940041004026070351038040400a1250a1142580c0b0075400d17921000d030404a9642c01e4010310006040500f07001d008000708405105c12150004a03004103103202d8800d5007215507442d52003030a0321400e401441041d5200030030380c1c14815124040c40b0650010b0490121051000302c2d01264900c215410640d10032071040903998540e41c0ba00344501900f03c3c0030400c0c1b03d03420f00034007280b801000c1c0424035004000d140750312030744a00e25000b100c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 995000278 1250 994999028 994999037
    0x102161509020f010e1305041406010b04060507060c0e1008060f01080f04081e0a18080c10080a180b040b071d21030d050901050114060d020d060f090507020d0305090a0201 75
    0x950076000150703509030254407050807d14010400c41080703041080d84201050a03021954070b680e130b814115a440c0b18074000c0c03100103034013031041707000141c02c0c1d0304200d101d02610704102c6ca400002001240790120700c4021940002c050701c01703002c8a0f0030b00c2d6402c6a4245004e281518103850100810400840d01078802006040d000a40001c402c40e0300141c10741d285104400d56030348001e01030000300755101e01e0742654078080f192100051043e40000308400940c5028080c14031041c0c4c440d40641d401c07a801440107039074075101c0c407502e002c294240e83c0740c030b01440c4a4500500f1604060800038030350b01d00109207078140b068030b1202e541c140c03042d4083e800a005049804402861030000e011140e901c0003046070010340f01c040b43e1204515102d402075482003007900000c01c1181e9807070408500b01e820088206070854010404101500d45a0300105072210008101161003a0364040000c079405066201046107a521030900c20b5030355040c00390004500c1145001e01082c105821f405441d000d220320001e0500c0f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 995001528 1250 995000278 995000297
    0x120705011b081810024b0d020c041e111629010f0b0f040b070b060405100b1c0b0d0812010608040210030b04241809031b0f050102161509020f01 63
    0x7241c4880701071b16062400100000044020700074642d02d800341d07408a409030180b01e104088a082c103100d605c1011000e07428a00b001c6a6a44040d00240a01240c000070500c3c200007030900c0750f40060068000707238814509510b003000038440c06517440c0e007805810003180380b40708010041342156110103003d4400801c14070780e42d0b4240111411481c41030343d00010260201040c1c0c0410b22041c0c42a40f807180505850520496444001c0401c0c0520790380604080d410003030114039260794103001400c0b01400e00c0311000510071401000a503103c400e000c4111013404c0000b49540c5040000c0304014014074140c184100c0c035080550004030882c2c41c03411000c041607a20a032803ca0360741c5507001082104040108880341900136800f003003820401d17001d4010302030349420301001c19036594070406011a0b01641d540c03000b1400d07020407105903400d244081c1c035030845407404080800c50a00c0200426032110300c520445107694034110019520702c02c04440d2140c070300042d0344050b0720b4424200031268801d280440f00c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 995002778 1250 995001528 995001613
    0x10f060f0905100f0506131d04020f040e030a031d0601080a03120606050f0c030702090406021e0715110c0114180f1b0a09020c06010311120705011b08181002 69
    0xb09519401046a04603100c0c003058640308c2d582056008500070744030400d1603680d030010302007610743c0090f5111080d0700800000d034005200ba0302404800c448600131111003004001124545802a00916070540085020004140e08100c0c5040003404007241030109034075011002c3c0132400f44e0151891051400a0f5170810040c050040700c00301980103040361118101814203100039004061800c54040c1000300e01000c054012040d5503416520046412503440200300c07410181c1150b014000003a0400c0c803281c08500340a01034a22007a222100c1e081842c940103d008841845100e10200e035500582500701403c5004510a019204800c10a250001d0300001040c10a03089500c44c0070302901c0460039400c0080037103180b81c102ea014082202054501004200f80b40c11203160680c050342c80075808101c9940991011003000e1782c3c02000c203410304c500c0d80352401c44d03a026414200b4040006540c414107403404018bc42c1740f4101d00d10003001940601a2500002440103820000c15040d8032550402c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 995004028 1250 995002778 995002807
    0x18222417210d051005030d0f08130b1b0702030f03070b06090105011d1c0c0e0604051003060504030318060903090b0c120309030c010e0d0e030c0918010f060f0905100f0506 75
    0x2d10700a42100d00c1c02182410040030300448c41300d0040001c2d41840801d4075081c0d00c500b001042900000c8030b8115845001d81c0502c007010a000f2084460303000e1242c2c3c40036960510000c4c0c4801d021101550390f80e14280f41400220704001c000764441c0c42090f0060150f41d902100b01901c50340d015803408525160200006d4040c0050440508100c0203c1c50400402030410f40020491724a43c04800703841e200d010401c8241d910444094848140002040000c602141c211540050290400080c0c916680b100c603001140c4c001416281d0f181c03034141c035604040d840301c80031006160929171103080040540c4900d495072010303e0030343c07040d000201c0410078000042c4110350010002038002c1060b9544000d0043d250485c3d01c409601044000c00010f03031a04020918600d80340000b0201c10883e46c4812240240001140c0405510340da207044510019005100b00000707048180380042088e460810300350f003900c0b0000c0503501d454051400810001d6900000c0f4011388204031641c64a4200e60400c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 995005278 1250 995004028 995004061
    0xb0d11120f04171b010509030405030d2109080715050402010203092403010f150c12030504260301051525020102160b18222417210d05 59
    0x20004000040c42040c18030041349080182c80d6450700034482a0b031b0382480d6545030b00551140c1034050b040b1a00d800240c2d4400c1030b0402c69041000c5204044c1c4280643d100119084480221806e03d80000c011040c040001c1005800301143c000a2000e131074243c0c0002c4d168001c0301e9002d40140300d501080e20150628142400100080140017502d030f40c1d54100d0201e0b081d005214004c42c01008401d4030380468441d24481041c1904088051600c2c130384024114020701c0c0c02007040c0c5040a5035a0614403081c1ca008802500560a810030f507220b504000402071500101c1e1852060450100142c503d13141000010645240c0018002030b2505058001070f81060241001c1d462501010200800c600c3c0c4024081c0c80c003507c0501241e1850311100090001140051410443e500348801e420110070860741c004a44e234401011b10b450384807015a466040782e90090b0132001002d81c442040b4811080e0070801e4003018260742880e0082041c12180301e4819200d507500c00d107201c944510000c0c110001034502c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 995006528 1250 995005278 995005313
    0x3170304022d06161a070f0806120a03020105090c01180b0a0c02030a0c1806060219240501140604180e01150305030c06011413021308070b0d11120f04 66
    0x1d9a03188034011201c6402400090100c03031040284e121032085d205400768082c4659001d45400511184c81141a280914000c0c000ca43c0030880c42d80c600d040074028040f000400b44203400101f05814039151190802ca05104d045040203d414a0b01001110001c07070315089424082c91150340e03111702c11007120030814080011350944070361842101040205e1701460221000440040c901d043e1007894074060318094420540181c0c04040600c40d1503000c4201e01d141c00d803060810001d5280f40c645000364500c15401c2e00b1540f03613030301c0f001000307608200322039542e110b002115030b14030340f50510005400e004940c00410398050703a40c0c020118100025844184460000400c7c000b42e1541c03840e00c1c42d503952101c0e4140540d0b006000001540050001c3c10300400d0400504950038500d444a490b4020342160680314041c0d180000001504a018080c0b50301505810042607030301c42e040e4400d0720681c2ca400f0005d80c014002040742c9c007203100150407100c0d0043e03801481804c4a8549061002c00d40c680784101 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 995007778 1250 995006528 995006539
    0xe0f040501082b0c060b1815040621080a0903020a120311070e070c0204060b13031e0503091314360c150c010504060603170304022d 58
    0x424100d00c00601c02d01c1c0042c0f03c400c0c40200e61420b00004004054043c07031400440c800f02080c900045007508003441007030020f001410752104201d861100f610050320034008082c885202d8910905040c0110009007102085401407048140701c0e003031443d500e00501410404022075401c088034070414a42d801160010a204542503c0380c000900702c6101040403004290a59440b104038040414200112513140c10b241d01c03241d58818064880f046140c1b8126485941d52074003144206602015014004d000b43c0c46071411815481d003004124850742c80c48096903100c0c01034400042c4000202e03980b1160903104030f40b0058510001c500544082d944001c40d01a6a1040154240708405200c00f110111a03031050b10039404020380c1080509401115a6500080030040190400c110404c44003840c40460034984181d803a00d035402c4400642c0c007101d079183c0b241d00030810300c0440d45514041501819000749075003007503400501e011200b412525550268618407a40c48101200c1c50108044050300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 995009028 1250 995007778 995007781
    0x30601210203061e130c050904020c01050108060106080903190908010507020a17040303050904090c0f15020d050a391406070206041a06150408010c080a0b100e0f0405 73
    0x10004007030b40040301c030140502201c0b00b454070400e00c15150034600c4080603007802044503020030303024081c003005203024051040800c00800e0a803a144010140411014000100d550410441c07a040c139106034000310402c801e150501140c3e036004801c40703000b50340080ca05440c25901e40030989810103d40d200d22000d51a16003081032903030b0086054080c9500c100411507010785000045002c5020f18000980050400c0c424401c4a0030694082e01c006800f03000c041403070641e52981c2803101c2e0415004040d21202c5064900001501080450581d80c1c10f418034505208100b070b002801c004100340380c1c10403207800500c1c031441203215070101e14040542c0103014011042c5402c1028059608510360344140c82580c0010310701c10700c08a0800e00481c0c0c400320942000241c01ca50380c500c1000034121540c4001150500c00314000160000c00003020400008a07a0944da10405440301358028100301a050801038962901e5640103291455000d944c100494809494000705002005d08113416400078517190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 995010278 1250 995009028 995009087
    0x118020102070909030e040e10050c160206090d050601151205060f10030603081603170106021e07150e030607080613020f0409020d0b120a260d050f06030d020a080f030601 75
    0x10300400002700074109000545030b52010b44103e100d00038020300c20030902104d0b100149041c0c4020903602c0d0009080701c9036555980c5982c0d0400c4807ea014200c0002c00113030b00b80b4819001440c4104000c04040c0412907881e207a4042254440c55019840c4900c80e82420b0000350303030095018601654125100702d440e0b12101c107907010540c24038002600401c2591071414400034245a2090603140c40303170b01030303d4800141070030803028690101c41fa00310341c017400d8000f1400c1c45402d0940481081160750300d5030003c01d4407003814180340014003d0001c0020b0141040016110a20440c1c0c2c4101e1811006a50b9041150314910381d00460704124000c40c000185202c40c00ca80d900554070720300088032121140341c7d13182000c035a50300f007004005081c0800070070011074051182e410b00c6a0301208184580ca00030038460b01408070343c0111402081c03000042c050100a05040140c044103011302d00041c68045210380790603170340e409018001c40e480c001c000009034151b4401c6e02d80301e10000c0030104150741001c960 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 995011528 1250 995010278 995010283
    0x30f0e010c17010b0901260c0d0b06030f19020705011517150c0d0f15090b0102032104050106080601080a0b280b032802030118020102070909030e040e 66
    0x58408000203503040405519084400c141c0c2da0480e4021204180380c00007503401510854460691120325030000140540803d103541c030282d11400803400801e23a56264692000100c900c28100140218014010460105c0584a00c2e5400c8144940150502c102c0343d0403100c040d228507040203080d5400d06210900608580c030b00c5a00f03031208402c1e01401081d22110042d075940500013891a04506840418080d4401000070810980c5018001c44e4031222482c054040e00d540055007010340c2122441081611a948204410900244065850030020220b03110242003168401c0400162500c00305080010960040d4011f0403400d0a0700c8071503949944c2141c407450301030000c0e65501e01c2400080d282e0050710051144c040c02409415100d4800344698400401007007a80c25014803400d016468004003588030002d10b41842e48480c005204c46106250a45014414129401d58010142c0340180c2c0c02050b40e005071048880300048911741400c04654104005d0f0b403042d08103150001c3d280c0020b902 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 995012778 1250 995011528 995011541
    0xe0d09080d02010507090e06150f0c160b07020f0a0e1801061d161205090f150705030c031b03070c030e0109030b1906080304060e130921030f0e01 64
    0x681500c05410840c0c01c1a03080e51822140d42d400181c40300c4060241c0a1070502c3c141e0000000740607038000c401c0072050361071140c0c048480002c1d0004041440c8545850401c041084004c0420f100d00c00c803442c000d41ca900c1e81c014064003d2182280d14007524a544038a000790000300000e203103010441c100b07014444858454131100111a5080c200c0114906812484103c180416032601501503620704442840203041404c0c00d108010301200c481840358001c1c040d140c0030308200310140008238065145646045403141054140c49900c3c0204080d8035040700c10b480c3c0c40481440710f26902e58811000242c0c510180032143e1501201005120141d0392209a02071410310944844150342842e03001944d03034003440e00c401031583d800b001c002900b480c2011100d510040c4d0003200815090340b07501d0103c0c15604030b40c004200181e02d03041440010b14000c60050241c0b184100f00300701629007078807690010708481300c200380f81d200e020080c03001691007680721414003070088034200440074901d47e089010301f01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 995014028 1250 995012778 995012789
    0x31b12120a03021c060f090c260a1401080a03140c01060605130e060d02040b030c03030f1312050703020402030c07020d0f0203010c0513090e03040b0307030c0318030c02040f0e0d09 79
    0x4940104e14100f1a0f1840760005440070011030903080f619221400b8007810501400100b04003460720b08402c00e50b00d2010280100080c0307241e0504900d4903600902c2154071102c15483c028030b40e800100800e203030120320515001d82614090346920448a00c0b080f4900c20121805110740c0b074a84000f900c103070301c84054040c4042840302480301c2a6a001740c22605e04054640c10b5000680380c1e6440b00600c2e0a43c4040280c110190558001035841c1c000207056800c000c51605d8110800130344d8070b5104901c4402c2a001d841801c802190403035043e183d03141c2d0f400207404000c0c019640000400d030039400800546500a80c028901c89441d0000d02c0c002c2000000c2e071130124003940c2400d46101801d03005205855001600450f0b00307171480d00e0704030307102d0241008802031000e9002c100030105d4403913401401141700b6029a00d01003044107494200a0484042031a18000700001030106800030707601c0f6141c0100b203501242c0100f00103800d07042c408001c01170b054442182e0721641c90741c902429080a00740040b140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 995015278 1250 995014028 995014057
    0x41d07090603050f071817032109030714010615170609010605120a090215070c120c031211010f0603021503060a120f15050114031b12120a0302 63
    0x954841c410303410340703409454800c4c406010350b0014202034483c3c41c0428510f80c041c4841e520145d41c40d200c010b8600040d00e42d0181c95000041c0c1600421010140c07a070150740113041c00c6d5882d01c0d20003052900d0f800385100c02889045a200703602491398094104d20050b02d43c0282c0d120881c50340400c05000c51194540b2800d4038202d240000d041e0303240c0307007a6a90485071540c4405191151034150f40d010044010010240070360f507145a580903844022040c00b00c03000030081c0e160780e000203003030a10b901100e660103a100154044c1c160b0340081c0f0140342c40130850358400d0f0725000ca00320220003610040300030419a05558a40215241c0b941215003000c021a0b0003540c24103070b4041c000c9605281444121051500321a4000c0c0c20491501800c2072080260301400c400114820785540f0710703007640d00c0309140000503901d400044c0580c5c02100030b00e40c2c102500b20003e043c2c0100c14214140c4055110140030710031450514240b900e25424000e044d441c0c043c05081c00d03910500c0110240083d04a08210003e20 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 995016528 1250 995015278 995015297
    0x300319050310091508011d0d2007091d120d1d060903030a0c1d010503040201051b0d0813030c290124110307021e040f1a0d0b130503041d07 61
    0x20f18500a00c5540750740c40080c141e081141c00081e101e0105034168013200f001040009081c003181070000d01c1c00b804042f07901088500960700e90250300403200100d03041d6a000419007100c07600090046030b01b6100395020109086d9050fa484541e401000c41385048a0300445040101c0b03400003000451240d0700070301003040501500303031084803003035103000c01c420910b000d040014099600031006161f20a105140c190b29003044c0291031085208804044121b5500500404040c1500320307141e503038803142c00d8a281c1c0c41e40c502500c000708034400c0e0080180182c81c505010528605840c0c401c604007480040211506585d9001031120040441c08410070071040314181c504000c0c410560180100c1c0340000850504000390200041e025507500e0059864260350442c0700740e03031203c2c020512015012100020111261820701c1d0603a51150502c3e1300c10541079041d1000281c2c1c21601c283c010301c038410701407900c0005107040c6103944143d40081c2c07401c03c9d4001403c6a0507010707102403841481d060340e5000b1720 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 995017778 1250 995016528 995016551
    0xe030a0c03121802120f03040b0403170f070f02040e0115050a0e06031c03021e12010b030c04091814061519091a30031905031009150801 60
    0x2101c1c0d070f1403409804403490401e02070151a020440002c074030100c1007510030910007079508a01c4c43d0b0043d0301ca0144100c0c0801c0070400c0c4102c004081c811000f07041031941c901413500c0c50044c0584280c0b0002802d410441c0d0307400381552105d43c090701506030600d0003000341c0e05e038403891441415604d2103068814680307003030040b41c500d400904090003000060b00904101851152a2000c0e000300c1003c5c80c00c041e401c0c00344019400c5070650070080005002d000c00c1d40c600b0798140c0600ea000d4140c2040c24110340c10003c0c001d401c05468115407c403003031140002810300360403102080031900b40310050110038203000d540b03144940c0841c15a004805d404924800750a00006101d224190b0b151128405120031804000c03984594005032580303254444440c16542e11703200002e288941701c0d070108000144440039002119140e1138040144940a401503007041440c00c0c808030350100030044e40e000c009001c004105081ca01000990207060030078014000d0048d103007461101c107841e500ca440d070a5070803d51080d41 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 995019028 1250 995017778 995017781
    0x603150b0f030d0e010c050c152a0d0f140301030803060a120302030a0f0c0c06090602100b090103240c0c1106090f010e01090801020d02090a0503121204060e030a0c0312 74
    0x15a6041d5803502c0d00800120001500c9411040009454600481d00880303256962740452981c0690309012441c1c85a404101c1c080e4161109041031300b100072828040070418400240301440c1d111107140c5200d134915251070845040000c611044a042c60100010007007002c01c6025510491003a115000e0103075503144c10184030f07001400d0140150300100a42007400e4410540c0d50280141c608100340c4100c081d5549100000140d4007440000d840014280500b5a0500400c0c0c16818100030900511a1100000300e03c2103047c880240b08c3e410641991542d50403228245814010802080000c4124039002030254030105004032a20300000d04106040e00c3c5c03080a5818590f07016107000d5400c003140b070041d41d804410351182e90501016a00010b10b14000340020118821413450250b10f440a40c0c00b4030102a40a40040d1700c2600480306000d1101801e4040e6510360310764510030059522241418801000f42d070b009125030b07000000b10010440d8001481f0a1954800d582c0d8aa00c540d0300c008040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 995020278 1250 995019028 995019043
    0xb1b1f051f0e060402070f0501050405010c0905150a180f0302010f210518030a030b0907080103030519030b060c060601080f060f0603180a03170709270603150b0f03 72
    0x401000010340c0900000d6030b45041c00d54480b0300500010b241941545038440c914882c15002c60345691038038100001c203c0e00703001703516650915041036a41302e0700b000300203114140b0180c0d061024650101d00031a44a109113540c07074400007800000540c1a85900c06500e00456500050b0b000c9008600c4d280c020b00e02c140350a82240250f0b111136018004c048002002504020709081c006419021608941d10b00c14801848008025140001c200c80c81d88107102e08000c00400035401d0203010001000400c0d0410110380c0b0152910400000e41011a40d043d0f00501c1d0a100c00c40e0400c90124a4207000000000c0050081c8c13400d0b29a81800d58171640001d40010088803040d80021043d548000141000d4000e9134004c1c03103501030886200070341c804143c6000c002c44010740c0000d46108402d5a1000540340340c541115003482d0410700c0d503003800c003d48401000820340000c0e081203c21130b6000060958082340c081c540c0400407000020000f902c0c41d001c2c020103c0114401c0c00c0d03110418105140008410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 995021528 1250 995020278 995020321
    0x31504032003040f18150807050f090603070611070b04030803010501020c03070302032508061509090a030c122318060913091e0516120c0b1b1f05 64
    0x1818131410448180d40c20000e2080c4088016103030010340c01007900f0310342c2d0040030b0900036004110243c41c080c00c0000c461148520a0300452002c01445a181c074082031420a85803a800d19080414160074410719000c540c0d48003121801c0003280120802080e140250304840d0300741c0c2114040a056010181c4404061100a52561007100c1c1c2c0302c025104a240c0b4140e0f000b4003079500d60003680e42d4400700e061480441318a150300c003a0a03851079903491304039031079a08485268000c003040c1c000765601801020803180054011051040040382d1039109108001c00da68920b010781d03003203600d40c010580f143d411003001d5440c0d080100f210040d543c00d0480554007000c0c0001e0030036000d10919903844d07005143c045410344001e50300c013070f940150600d641041a01c0721312030001442c2c01003c0b0003c0302c05103100358100645030080351204001140d0b49203c6941500c0d250182c0c0c41d518403001d004141c0e400b042c1d100d42e5800b8050b514115082e81c0344265800c01000100c0001d1001e580e17400e01c00f0b11021030500c0c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 995022778 1250 995021528 995021549
    0x30306100f0c12120e010b04150b040501081504090c03020f060c0606060903011413030e09090d030b1926030406022503060f0e07050f0609040b03150403200304 70
    0xc0e400820803090030303082140000e00b003c0c01140701c43d290f0f501c207580021783c0d03805a90703448084503441da0405101790340e03001c0003062441d89130505002c5802014403c52040741d0422019102040081d503580280000b042002807040210308407500d4404602a1184401c1c3c0c4240300e1800a40964101074044aa50041c0c3d200941740d143d58031002c2042507003096001d00e803d0340d6079104c4100035509218885000d400c1045541c0443c01107842c004100240250000b4010f55001040c00152030300000c8030b1a00c400300e406d002c96420780400200c0c9111b075540019201c000040c0c40001108101d201c014a001007203a030788800440140b00c85640ea911580c45000c00590002d070f0300140c0e0419040c5000118040c02c54170382e0300c0e180d980d141d0728203651048050402055540503150303ea58030170002400140000d849100c99070703901a0000c3e100d030103101c0032280640d40760b41c0407511550703080c0845016031550301010310443c01c00303060052000e4072a4071040510000d01e0758491401078004152022500000c11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 995024028 1250 995022778 995022797
    0x2030a050a14071406090c041503060f110f070302010f140f181516030905060a15030507030305191704230105011806060e06030402090423030306100f 66
    0xd046400b42c003070301c0300e41c04079403020300403034000030740c10459120a55016402410309003400c81d80a070520302d0a0108a100358501921008030300100d100c48030499400503000501110313140886005400840143c1600c0040003800003102034110000d013051500a81c02000000e03403821f81038003151802c13004030400c04180c0b0009003400b144c00c28202d81c0101e145036420643c000030400a071904076040c1030010a40c90010411800030044e40b0208910b03026883d06000103440e60b105c0e075455501c080c101e0000240c40300300c424403202503c124000216442412904895603030f01b00200300b608a480c214121945416485103010b11448040c0c400032000c80382002640c403280d840401a02c11100d0101c540c4141400f80101001c2c00e03c00c440c000d04011a0401c0005030340101041103c02c690020414081407699420b1203440b00020760380d2069050b25150056200c0307007449500b14500302c054040c10b01d2450f9160241e9080400958006c800590340c02031114001d0740c06441482c3d289640c2000210031f8030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 995025278 1250 995024028 995024047
    0x7060309050717250303080a051009020f09030609010501030606120507060c031b1101080c1c020d1401060c0c0f03051b010e0a260c150304030306180e0c0102030a05 72
    0x1825803000c0c2a0314021183d0f02a103e4034541e5030510352104e42c10502e065a1070400905070480c203140e6002d031030b1441c10000d52078882b141c281501d009024042040754085107059084100204541c1d2004e00102103400358035000718028043d110034003080f07a075181481c0000a564503280382e280c0c0d20b142e1100c003030180745003020800c0b0386003249600c059040001500c00d8000c1c3e590689000000e084c01000c00c10302c1d03115014005041000081c00110700d6030703400c0000a8030080d4100f0810456568580090ba81c2e0000c440800c0249c44410030f10b02d94101084000039007181c0001d1881c50b2640711b01c070500056956080340d0f0301c4107800c0c0e21004e0007540084501e54000d08903182e050040c0c0d101410a060707115140d00226200141640280307818002441010020000d502d220400018054000388655901100441c800f0084148090004480030012030300b0107010fa0060005001500300e0110211520f4644c6000b800300d0020a0f80c180c0103c41070607000b54070100c01c462008800b900c03101e00d40701200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 995026528 1250 995025278 995025299
    0x70c060815060d050a05070504051e040f05010e100b040605040902072d020f040c0c0f060b0402070c0914040803130c03080c06071106010e040605060d02040914070603090507 76
    0x104034495000c400084070109035a440301034484100c900c81e002030580f0b00501184101c0300e010b0300c1c41040c04000c1c402005955564280c01c05c80d172204c841c9802440c820f003000314014008450304180420308010000c241b65001d07072401445203038440828115255034041124146c441d50140f900003a01c2048240701402e06500148040c9225101805a03101d098948a0308150700c07460703407280e0315002c540250940c1b402051213034119004850070080707184581d40c050107891007420010240744410540205108c0305522903010004042c0007999a031405182840001d0304a004003403819140030007d00040c0d01c0c011500d4461a400b00c032443c507589800f0701c5010b20031007000f0b04039250010403d020001550341c002070300308105040002c10b201d003450200035000c40079070a112640b541c001c50040107001c08980441d50496000000001c040d103408011803203101280310080c0d0010305003803050081003d10340406207590304507001d40b0701081d2201c80407000c3e0b900c0d405019100e80e210180601060190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 995027778 1250 995026528 995026531
    0xa1716051e0912240108030a0804080c0105270303090a1b03020a09061403030f0d021b03130f0503010b06090f040212010b030f061206040b220602031b070c0608 70
    0x4981c102d090a03010000555074890101402502c0c0c2c0041c00c015a1400d200f4100760310b0705200c031580390320720360510415a9132806141e0b600350822245030046428805039800b1120300b00c1c0ea41000307021621f004406041c000484004440302e40b2a0041080903401005c016240109507031b8014025450180c0c60345018000040e00114603815400307000001a034880d44440014000042c0c041070091501c82000e981615040000c1e00a800400600400341c1d20103003143d00f11005802c0c0162504d8040d8981341d10f4000440d800c10b858400001c141c0c40f1503080c03503090030840e07001215922000e9212000e040c02d07078154804194120b201801584520310b0020b90440025402034030040c10405500e0520062034000c0c1d00883c140f045c0042440a0180d0704011640e1044091318400300000492103616661280104094006150140440c0c4070104103152125101618841650b488101c0d0030940c009600542c1d243d031540021188590130201365005035042140c104501c410103900d00001690001c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 995029028 1250 995027778 995027827
    0x61b0201050417100608010216080706140c07052104030303020d14040f0303050c090a05040e0f060c0c0105060a15050f131508060d0b13060209060a171605 68
    0x14440030503101c00624503c1d2520b58014014070f202c00350b032143c03201210103030303003000200d6401001640106881000c503813800c564000b00142d075a8103182464001000b86005010303415256805101c0000201005000014001c40640d145007054030316201480d0300320905685108010302c4100086030080d80589030501d83d4507808984680c685400c9034021104540890b41078010010150506d40e152252640c4404020001c0345050b00003400143c0d022000c0c4074551046403030b2007190003b690180b10301904002054122200c82c01c0c04000074034284c0001c40c84031030380d61900340014407928000c02c00d01c080726200011030072440500703501104c180e400444d4224540004003c065252035601d12000300914081d8032901520255200090808001601551050901c01d0303400012607072005d0707404d402003400064003500c4500d40c50400007901459035175076440f0202103411f900da541c1145120400c4000c444800e4003c0d40e42c0d5044022601c00b010415001030424003440c10070448450304025a5407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 995030278 1250 995029028 995029037
    0xa180b18070c03110604121d010507111906030e0c01020601051305100305030d0203010f1e05091b0403120206010608070e090403120e01240303140d06030c060f020c0a061b0201 77
    0x303134403507202e43c540740066804650740d01906004003c450740c090042d01c483c03c2115903280d04c521034040001e00380d001d81a000380001501800c154296610090340801c4070501c481103004440d40c03050064004c0c01082c00c0c021481c0941400d0003881e6202140b9103041c0c07038000700080410803049030310600030300700100260a00305c4101c4010004c10702c200007615522880301c10150b0303298109141d0410788001640001200142100400000c1000130605d9040d540701343c90360a81c0ea980c5281d401003440800164048403000020040280445030104804000180c0c00319000c90b40c2e82c0e10100ca4607002298600e000613940000d05840d45068860b00790003d0007840c04290880d00d5285580440c0c40821800300c440c0e554035106400c01c00d442d00044048205001e200342d0507491070b200607020b01503032003003072403095800108905c2d15001540300e40099504030b0f84150025880c0e11010b03100806850f01030000d481885101e60306460281e0044050319016aa0000b4030000303403c804209010f2510100d0512 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 995031528 1250 995030278 995030297
    0x60f0903070804150e0f221803030e01050105010c0803011202130e0109060e0607170a021e12011a0a050c01140a14010807060207060807030603020a180b18070c03 71
    0x56851000c3c101030410f000c902810500121400780c407060401608600481c0240d002c10220350724040d14403030762481030303d04161400207112114001c0610800140c0b0310700142c0d00b00c80074103a056002940b1460144002c21840c2d0300c6000540701070030a110010040d1500b0001072107640c00d0205103421103071001d401e140c994408010310200392507a0081c10b031200ea64030641c200600406005002000300b400700688064109900d00900720b01d52000c60111010b04400841c9a02115504550652040c6048107105054004070960540e02c10403101005050000000c02d400e800d449a4407000c5032000030880c0b911070741c070100361400d4004120400c6a55030300e20558458040e02d00c0c08134400c0e8040000024248600512000c0041e410b80014129074455041404066000100e21043c0e86843c10a0340c27480d61507040031000f800319504001c0d000185000300181c04070700c1c2000d41c1c06246504a0a200d000512810b004070040c0400c008003440726010003240d52240281d01015410b8040c0c544400c52 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 995032778 1250 995031528 995031533
    0xa08100e0621030a080a050a0905100b0111060f0f070806130c0c06051005040606020c030d03240321050a09030611070807080406082202011214160e010908060f090307 73
    0x45030094980b204c0802c2c040d00800c0316141c810f01c269540280880410030010109440b46c0d9602c3e04290b01c10861955101d14076640344e03004008864180e400f090456680740342035650218091403d4843d41031038424000401e2041d0300450b1854852800500b0354000c00c54680c1c1c120002e401d03101c2c030b01c1c01848010400180405c0540c01001e1280c0c0300044821102885c0a040c402200e8103540f000e0110341100c8a045844d0782c0c0031880c04604001440c0106c0d080010341c112040c0c80110761038000f401c05200c0000000c000e40d035044010941c1c000f90404102610101701070b5014804e0491100c0000c0c08141c041c00000d4896000d01c1d00e020412800c6801c046060756010901e901c11007080e0380fa12004030307080090503030107607030030f58010b44820003140ba1a14240e14510300d20a00d4030024107000858a03c404004d5559012030007404c001011940103080402c4502103407501a4403030000500600022040f070350040000000f16642c0030000c01042d56185504211aa80038003040030302c4c001007140402 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 995034028 1250 995032778 995032783
    0x307030f062607060f05120711061501090f0b1207090f06120b040905060c070602090a03140d030e0705150702060a170109050402010c030c050c04110a08100e0621 71
    0x407080c4000340350145030400d80002918042d00c55104c0360800c40c021845541d000d034807005980500301d018925414070f0315030707010656a9011900d8195011f22404042080130038000346601c0c04080280ca46d0039410b030b101c0b1000f620b0644071f8000c0c280d41c200304100350f00c640c940c0c107004164005010324115a00e207444900c6c0442c84003103a072004000a01000c425a11002d41c0e1003416020324046904024001d400d9988680754800140400d845000100d446400d01070b443e0102c0e090800020322080c0d4060b00da180c407282c44680c80429982d18410f25114208690003481400141d58181c0001c00c503885c503100804c00c3c122079402a00d502480c044c1704120040e19000094151002c0301d40b0350690f403a0039a01c5140c2c65a6050b489401d0341d41c1408288805130f600800301150854051a11507603c03c0e0a040941c40e1418505160360424a0041001040c82c803200182c9210f4070036640350919500c5550301440c0700d0003030780145101d10007071354003040c0c030345c0b41ca14812011000c5050f182d00540c140c04100b1030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 995035278 1250 995034028 995034059
    0x105070318090e12070c15170a0204090b032a0607060f0b1009121217010803040513051005060c070f06080403031b02060403080c0f0d0905060603070b0307030f06 71
    0xb1a40d803038a0075859040001d010b41c0305104c07100c0c90030908000d00ca450780c02081e8014804c1134451803d0b0008030306610722495846a20081c401c11103512170174422003000c002d6225108a04074036143c074000c0705e00303841d0210b9151802040c45201c560340c0d4003c100c1d415114414a45450351101b410010400001e10f02e00804131480e42c4060b000604d03103007032004d004040c0c0705090404100080d407c4d01b0700102d00420a40040181c1044d50001c0c22154100d042c0e0b014021130818050f80c607041400042d203000c000006000b40c40b025150840050100c0c106a8107960741a00c0b06501d20403046014000d03400d020014180c44012003040303580e071b00c1e6a1100604181084d800c03010000d400c0c0c2c0c080005154142c020301c0c20401010030b07841d100e4800b141000303443c0d03003000d80020100a142000b141d011400032068484220034400a213554180100e0500000c00c0504011507039401004005216460702044402c229240000700030b00c0c503610400101c004107072001510600903601c0001141d54a0074200c800d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 995036528 1250 995035278 995035289
    0x50a02071a090a1b1d10050d0c0e04080909070806091b09010f021e0a020a0902040b0a0c1e0f020102011b0507030e15070c140303030c090105070318 65
    0x598400090901c50010075805081521006045090207280d4a0001e101c45000350805441ea41c03640c0d490643c0c4510003a981c0c0200f80c0c420030640641d65061a0508842c0540701e01c48804112981c2c403814000d803a031800c4809010440003030401c20041c40503114a80d0300038801d950182c80c0001d908001451a602542c040c400074140d00100860350418210381a0070881c8003d05a0380c01440c51003441e0944100001c640c1089204410002d04500800440d90389407003061000402103800c07003945c2d0703846104180c1030384034110036900056105400e01c2283d09542d100c1a00d10716151078200140d4501c8800c140c211410f01c004804c801b403802004081a0500744241107403007031210345000080c01e4070380800d581650111205140060903030400d040741e60079641800d100900514100010360400c43c4108503d00c078440025100c2c0c1080300c00403107803040d228104242c0d41110880020b040d6240400c40b442598010f0401041480d58041c2010f0034030f152081c0303043da00061480500d41c25418499004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 995037778 1250 995036528 995036531
    0x50901180c06121406040b0315011d100302090c070f0206120a23191e0902031b09011214070303180e090c060f0409050702150c07022809050a 62
    0x50016680c481e1031900e0f00c0765000700c203200c2529000755070588808007074505841940d039050511203d48081c0488035500b0b41c0105d60100ca5079550000d040303260300c400901682c480030b80c400901c0101c0140007031000e40390043c02d603d0305a0744014035265a030340001021758224108401107001a0b070360340003d114035000205030111508244602e5410744480c00d1056082c440d012900355204961000c0e01ca9104034070500a40155600480007002009140d4100f1851004d4072040e0311603601075005000490710030303400c441301240017542240d246822031140d5a40803c04c000100b0080422000040d00503010ba0035140040850796170031481c100043c0c1c1b04a0104113115925000310820200200c02801003018000a40c64071040d51074503110b0000040c0e11032440450708070031850f01d440665002c0c0070f820400300030600300b42901075030f41c00707250217406100e800e43c9001031440072411054800d1681d0240906a61400e4024079443c00188a117011080d8401e0b0b44000601c2000c5004141c0900000d820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 995039028 1250 995037778 995037803
    0x18060204150905010e1003050c13030c151d010e01050d02180f040b06091005070f03080f07170402100e030712110a080d05130b0703080709141305090118 67
    0x5016181c10040e901c002e040c0007812281540c0b9446d2080362000d060524900001d1582d80e00c8890090750245100411001c149004040100070306c106100b01030f2145130780741190320920181c04441407091071414082c0003410610f040c00c030394001c5005049000050403c2030402209508880881e00400300002069100031491612404c08800038504140c00b41c1c3c0078055001c0072800708005101d2216180c0c0112035194032809070f42d125400396030000381d111303503125103003241401c00504080c0d013901c900d4201440c20011450607070048094041000c5003484082d40e55541c2e80810100004505050049c410601840300c51a54140b0400300030b856210b0000000010600306541481c1010000c01c0c05822401000e0200010018101504c114a1b140130380e070790f400846100071024110391007a0103d41001c10300c40708050b001360307000d840f5940550315240e1300d0f81d6611131460b42c0203d01c2035103500b245400401065191240c1c22107036102d00aa00003040e6103050300d041c180c54075008101039500551480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 995040278 1250 995039028 995039069
    0x60f09030b041101031a061608070611030a05090a0f0201051e130f0905010302010203040e0405010b060a170702060c092e02010902011101062402010b100f0201060e0f010918060204 79
    0x3182c0c0030346c41c2280c00e641c840381d89210b02144591142240110880c241c0036031560820000c8000c5441b240c1d40b1072402e02c10b80e02c0c0d02c140c070046a0800c1d0746440065050200007a00e00d08005034042610790030042c000ca050b250340e0015145540180d00b908481d501c17041c00c4040e56045c2900034407032095002c0c500a0002d2134036001b010a0006504038400603030612004001603a030010603a01580c0034500b200c18941c59918283c3d0040401d003400503001034003c108440000e420810b0440030040d00c3c1d00b0f80d541640c800c1c4e03040b0307101c81044035138151014050042e00d1036402d105c0121b22150200440d0400c510841c01801031500d052904290010f0703454900c0d00c01103582c030000c030f89940441c0d50300901c10300b0304206408017003c5603140645040d0b80d41d8101c07403034030354400d401c020306000c000380410441c0e10034034030b00420b1400d2130f0030703030030059820901c000584160091910b44510501910840310340d080c0a034481c090080e86008a80344050395404c0c1001c201144000c1c0010050400c5440e5181480c4 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 995041528 1250 995040278 995040281
    0xa060e1c0c080405060a090909050d0e0f0d060b01051303110a0617150609101101060b07021e010212030108011a01032d0609090f06140907060f09030b04110103 70
    0x10400e001c00c81c039012480300042801050f102a80c0303040b1241520ba44c00300320200c0f04240c103540010304086c104590417003407090210703d0441003103c1f540c8404040e10004244040040302c9244c594004550341a014049a101d900c10640158140b4215142016200292103c000140c005640240d080c0c54403040741e2822924100003800c0b00d00303112481c2000d040c0e040c000190001c0c00d1104100c5284000001596100d048420441c0c0041c40b8800d8498240d00080c020840c4102c0c0c2c0c80290300c0c111021a244641c081501c11107640100100802e01d10a0815006ca481c280c400505510034103000350300800c1ca80c0b0146005c0c0c0380460002801428070000701e81042d0740030b240c050505250400e480f05040100c0310702041e40c030000c02440e910b854cc5003004802001d82da448041807500d02204402040402c4e42190006c80c0130308003e0042074504100c07201b4560040d0ba0318007103a80925010007000d8040d00341243c0d03540306130500520b81541c070340b24207548900403141150794008190401c0b10f1503805 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 995042778 1250 995041528 995041573
    0x60b0a0303111009122615130506030a0204020904020904020703120b1c030804030e130603030e060301050a03170c030708090301150e07030e0c0d0303140a11040311030a060e 76
    0x90781018020250700781c0b1138024100004517141d04000c2000d403180344070440710400803044450a100d01c41140f90807045c2c2034141e1388011240f0300c6040c4c04d9043da91700081781d0144a000da0002000340c840301c05a9070801c0025405043c0ca1504950244050f1029070340c0e91002d00310b8a406602d440d03000a900c29040c10846100d210140e02c651303100d8440b074191801c8042400385042c0d05040699154076903044c00d582c105030411805a201824204e1400c012504e0b0f08090100ca01c83d803500351444850b0410440e540c0024041c10350440b82148040000c00c8103062450191000030138210328011110300c035103085910160040d22003130000500050b03d400d003445100403500c3c008090b00012030a11090500d510800380070101010f0711441c034010f90310000d01000b009124001d20505000740c0914024024000c1904200060480c50000038800c240c0d600800352a0b4030b4210405241c907045a407543c52500d00504040c0e01482080a0b00c1c0c0003c92511540001e58120401010051a40748040403210030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 995044028 1250 995042778 995042803
    0x61f1b2622030b0703090816080415020106080303070c020607050303040c03020f09091c0e19090b030a0807030f03060302090f09190c170f0304060e01021c1b060b0a030311 75
    0xc41c80d0003000070401120302c1a41003440c1d03240100c2c1c0d450075410b00c24503d010307001c400d0143c910504107007400c2240035401001122428601d4500701d04c0b644100740d00722001845048001d800402c002441d0b688250546040184002c044a0a000050f00c03030303034910b810854048404001e0800c061081d45007120820100403011504064036241071b07d011034584c030031342c807403071384030800054100350514082c0b0901d250082025007035011a903419005078445120500c141c085403407410004152a040114044034415004100c0b246800c040d03690440f00c01e00400c036000c0c01c159071800040f00507070702c80302070314040c0c0300b081c0d0304507210b0a20500003820902104031203400d900c3c0c50035401c0c00080c02800d00c0b808448082407581e907109003641450f404d044000001e880a07000018001c0b4045421400761940d0003000c7e401c980304061142c9400101d41c05210302a0082201504010702032441c50b80680b40007031003a0000301d81008000040340100768190012070214070a0780070305402030010840c50f0100032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 995045278 1250 995044028 995044087
    0x2100b041e0b0301020405131407020c06040605030c040902270901060e060c070e040c140603040f080310080d020309090a0218120a080d05061f1b26 65
    0x1c4820300e050328525010300c040c00d03629111000050255020340c1542c0007008040d016240a01c044c501d00d9004180e007910b4054604202004510010310005001410000c06085145030034240002034940d600700421103140c1ca1020400410f10070b141e0f0010b085041c900038007082400d040c83c4503d40059151140c03842c042c950000c010014240e00944000401c0003c1e100c0030307500c488040b001390411109800404d210900f00c0b0901040180c004448421101080d180c2c0c80110286010802c0341d01c405d990107031231880002400000320b07c4070802507400c612003010240c441640c0d02d1307546051105408165001d84c0010500c02080c0c141a00390907441f0400c02411031401e101036400140d070780c42060450703004907510007040c40b1700141004103000c941c0d040780b0400e803110394889502c805010300312210f501030150024a440e203125816118007121030b01d038594018000c60900684019031500d20140e90515144640b06104c10840c1e50701e802c00c1001281f00c030350311507141405500b200b0301d1110051212 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 995046528 1250 995045278 995045291
    0x90e0c0105040603020d14070804171c0c110601030303050907050f03071208160501090309060f080105010f17040b0f010b27150c070905090106080606060304140d02100b04 75
    0xd0303a00904440964103103080041e00e80090003000001800ca400a101c1c80680800520401c0d541210045105520a440719001c500f003482520740d81d0301450107140488018a018041c6009841d0003062850425140104542c01c2c480c0c10580b07020006c0e40103030086540c61050141c0c2d40c1007400810701402055030108481442580401da80c1c402e5441a40500403050348104104917a1300300712004520034580b50001d52085042032402810804030490202d403000c0d400140c554050703403228040c282030392182002a880c003001500c21041508030701d004c0121800c60190b982d00c0701c0e4a1075000f1070243d443d01c0d116150401101c10b610310181c21400c02e480c000d210b4907001009030001c02030b041c1c80342442c410300c1c2d0840750080783c0001069507681098400108035648101000206041110203003101800341e511400d420a00322180e40c000c0c500c3c2034000e02c00080d940e0511000442d001031107485640c11604100c951705040c919915116001604030100b400b469403141d003c1c2401c0f1807030444081010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 995047778 1250 995046528 995046553
    0x201020d020a11130b03030d0b030c0a180e0c0312090f0f0303271309170414060912010e07060e03011109131407050a180311060309070305070f090e 65
    0x500f02001c0c46148244440004008441207a82041d200040e010b82120f4807001c600380004050411001d1090003032040003042c0c6840c0ca800164602150003801600e021084d042003480050309111a8200b800e1003280c000f0300712910104078401402101076442c4c3e071507000840801c141400b40c605010701c030b400940001002c5030fa0100444444c844a40c0c200000001080103a680b038003001c00240c0c2d440b00d488803103071400780500d0700070704132070b5100752709020341203c4481c0000968060740c00b6100120b003a40da81c48005081c00401050101d1000385810945203030402c0460943d152038540741c0450708400d03410001c154211100003403803001200203104071501c00c841d6041350b0064111441c8500126112401444d41a5001d410301402180d400c5141d494113580180240e0b0040c05480000340841c0806080013240007500e00c1070703a0b40f00c4a0800d2040b00300041040c681c10103041c206482c0a01080000080c408001480090010b00c0e540d0744402d00d06240d00c41260302c0c9007006c4140d034100e0300c000170a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 995049028 1250 995047778 995047793
    0xa0b09090f07050a0813050d21110d150e0109090c06050c06040b0717040503040512010b090601140412050a1217060603090f0717010c0c0c060c1415040201020d020a 72
    0x5913040d281c507240f18260342c2c0c0c0f134004c0384409094801400038095226103050741e5900001c05c002041842c030b00b41084c000340f040080c04075444107803454503041e400c0c070501e00f04001300c0d00104014030300d4100303800460b52564a0b03085827090a9200513502650303110304c072007000010f8184030010036060402e18108074400031101d403100001080108090007000000d0310203400f50b059801007000109030035241c0e00e040d1401560360b80c85405018402c060001582c0c03006101401004940342003d081c07001c50340c45550040d640003030181b007030100c007030014400030450800c42401122507600410050440e00b0300fa0908011a4800c1714400701003042d18482c903900000c440b16903603001401941c0349070f62607581c0340c09603042441280032030140e40070348607001650004c0901c0a5107910091030080108946c2d50005036003030801c40304010081003081c001003020b540502c001885050190700548500e500c1101020308041031344031180240f9544400340015564104600d0421b6451800244081d4040751148171 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 995050278 1250 995049028 995049037
    0x2030403150504060906050a06090e0d0c1106090d125a0c02090c04152304080a030e0603060a03170904060303020607140307080103110a050a0b09090f0705 68
    0x40d40680b0780012a0130400c1170781c0302082840d0008820012401c0ca903040c60060074181c0f140484040c101181c0d000502800b040030405071070940c8611441403031681d50171590001c1d641110303a01c080300340000f40090710b400090403a0030303104000c220001150070001421401040d1a00c1d45001c20704010b01c0810f202c407003140c0541441d60280e89200201c5d1205070250081400551003480042034030049020790082d181c105054400c40c0d0352941592118011070241c0201d10a2a180e422104071040d00c05000d00040c46440c50542d107950501c1e68210046000f90b4020741c001e01d4554011410070091680c0a070a814400c10100c4265107907080c0240019440286400080c115442c000310030090312404001b2545e01050140c81440f803a560b81c00c0c007941780c104c00c0b60b82c0300c0820f684841c008081c0c0c2c0d00d1801c132031040240351601d090f60b03400d546807142b03100c04086169801004101000c00c156841c000203500070005a000b03180e40e481c01d14140881214060710498041010340300707110310150814240c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 995051528 1250 995050278 995050313
    0xa0512070c081c0b06180405063304030206030f06040c03090210030c0504030b01080606130615050f0d060b04140409051b0a030b090129130e01020c010f06031202030403 74
    0x302c1d00f48110b610400c004168040d01140d10400c0091180c0c2c408403243c0500440700c00441d403c0000ba601d10041c4a06805905103598009480c0300d090645035141c8921412503542c1889100d00f01a101c6d80840c00355030003900c034101c001c2074520803c115444d040c051004207410030b2a0500035511140e001c21500c0c04a054280249a1070382221b55409100c0d005480055803c12082400c0396920400076841c0c131030943e911401a404400200d40c00040c5008441c00c03200c1c103446190310501c2c1020100c616420030364102000d903504016102d0642002c3c010880540814880347d56520701d007958985d50744d500c88c2c4045004508103040c000100308046034150082e4502c3c9004241c4800c1c1000150903d030035900010800c030340900a00c8500e410551044800245003000c02400121495003421550700292401d41e00409200c0800300245003500841d00143d40c000026081a0b0310303211107400d5500e1070703009040b0715076940010400d0101c054503007106075a060016515240c1907031a0700f200da51940307909 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 995052778 1250 995051528 995051557
    0x16080703110c0712030906110c150d0504060b3102161a0f100b1c0615020322060903110105070b07030504110109050f240a0512070c08 59
    0xa4401c04440e10115400c00e03400070141c8103d1a01c81240c03004082034030b8804d07000622251000b0428501600918050f100c50340c0081103401142c00401c10613241c4501c01c3d803e00c5da000e204110a80596004180c000d9110310000b0610145600c24010f02030000d000381219501609030035200214900120381031030002840140c0c1e5040c0e4050802c04159000a00902ca2440c0c0180c2011403a45030031154002c40c402d02a110031510b64030001d10050140c0d004120303032042e04000800340c10311003c8100d00d010b8a034200c08a00260b4400400210220b0240e8550141c2c000040c0112480c0c40360b10703000340e07109404603100500f500b040700052000d00203020003400c08660a1820031070360300500613944002d51041d00e20b040d07460044c4004000c9c00091350111010040f0100c40800381d80141890401d03681c0c00b503c190040c805a0302001105009022a10110399041c01c240403100e004100030b04000a854075207a035642281c1c04403142d4070000400f00c508005c0c0f00288940011018800c881070318011000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 995054028 1250 995052778 995052791
    0x261b032403070e0405060106320706060510030606140408060c07051203100303031a01081b0705012d060f0e0a1506090807050906090c21090a0b16080703 67
    0x407a2074400180c0100e58076030114001c000422030005000c0f4140e520b00e80d6202e162442c2c9055030069100111900144d044c0391302d0b40c40000c0540b240c060300b00c45000c0e41000c24110b03540c0c40868038101d0007410190020352602814010507402c190f5031640031146a240915191401c810136440c0c81020701200348000d0009006030a01c8401c00c1611030f0140b100b81d000d5600d00f0400c100065460031440120003183c01c00751042203c00c240b411110041070180c5030005503903039211510f80b0019403418030040b9100e0900810003c03440911034000c0700c03842c803c42046000d01d0a00ca000f4802d40030340c03040c280f442c1050010301c0381c01801c1c201c0e5000c031541e010412800d0b44030551074101071300c0070b10345411900381d10800c0000c81d550f01180140490340194290758100d0707142c1e03080c802d441c0011119641c00c01d071803001007160404400020041d201200c1c40382d403801c2a2256407581800000c0c1d6194015a103c440d1480905c1010003103c0d8103c02c41081c200030000968034058a1408006c2c01c85043c5907032543c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 995055278 1250 995054028 995054101
    0x607081305030427020c0d0e0a17010906060f0303050f090d060e0a030909061a0d18030810150c02010e15070b01031106040b0f070201261b03 62
    0x10341541900d0780801929111078480c0407101d14800c00300c0d40b5100094a00c40c051030290703900d01c200c540188410000d004d82c1030400d0b906642400070f00080310b402961a1030b0009540300014600e0f14101182000032407200c1c190305140301525a10340280490300b0602c0740400c000780c0c02804903460300d240200c40b00e813140d00b8040000d2041d00c09840181006041c07000280c102213020498055591003a243c40481c2521081e07000c2c1260064000e042e10070b42d03440d03549454403a03601c0103000710341410310021924140c07400b07a440c20b581004100714041b614110030301c40c50900d01100000500700c64008440c0440c10100020300042c1c0000c0c010303051207034128204000b0786909008121002a0010803a40c40f1700900d400c070f404503024030083d43c0c480640a0307042c056141c124110382c21109484103ca0078646100704c0b040c40c0d9400054100c2c10302c030224032360004003988003070702c0c0811070a035401c01d064070301c0c12400390641000032010760003180008004201e0001e9482c4158000e40c035400307112007094103201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 995056528 1250 995055278 995055301
    0x215070c0209070503060102061f0608100918140d05030c1815070615050117090705040501030309050915010503180a0b04080702031b031e010b1905150705060708 71
    0x20316020350007142c494100030301c05400c400254003c01c022390841c2c041c0c0d91107680701043c48015000340409140b04490401040e03114091042d04248170b0000a041180c0e00e44030300007190220040d050401c0a040070301b100707015403d07404823028882c40b0040d08003001c0803d8002d11520004003107046040012480c0441c12001c440c20540b24000034150103075251010448803541c0d0000721088400504028a42d00d001031450902c80c100d070f9060311500000030b004070081d0350000c402001c807001c0b1310405038001901c0e0303198084d1034021070081d11030210050400301481500e171001080e485454001e035104008903648074040320303808281c121003420010350703042415041c82d40b0090003a251800724000d001c00d00c10340364001c0240314400c50445140c41d5103252070303d046110501003558590405440042200d0010340b40d201f1361482040000740001c003c400141c0e41c00000d07002078040000b2000b051020b414a86c0003460700701c041d4440e150516116549859941000a01e8a4100102040401c640c03141c2ea = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 995057778 1250 995056528 995056547
    0x14040819030e1503100b0c0601050d0812040c05040507020309090c09031204031b05031c03020702010c0b070801080f12160503090a1d010b030402030a0f050709060603051602030a021507 81
    0x4001d003d14641c102c400d81c046820036a022411548060000283e84860204954030700a80001a1030329031310b00390411113000b80d007400c00d86058000704500a25031030940549407003240b0034800c0314480ca080c5400e00003100c0c8000c0803d81076500c00c20050006603283c0e201d5a50254400f10034650311645180070038107140b903002e92805c0414010070080308200c60481105401c10085900d502030300d545a080594544a0b121003103102021b5014001400d48207400034809940113040000d0000c0303035035070351002c04001102d505000403840001807011150a00140115280d00c10040c080d2064980c2c6008040c421280e14200140003c0203100401034240282c1d0100903008001141403030340c401d02e2034003000c3d0f1803e00360908803203a40085404041e100c1902c2c003458014000b42603240e0f031551640300fa80d40d20b030b001f0b032124820320034000303000300b0103000b03240103007045680208040c24210042610114241e080780195041401a003a1a642c0051065845003000d0301188040e11401c0c000d0703d00792070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 995059028 1250 995057778 995057807
    0x4110d050f0d050c1504031409030a150209100206013f050a140a1713180c02010b0d0302030a050d02070609080a1701030503030c0a200606011404081903 67
    0x28040601c2c0c68940c00401034000a801c036010b40302d8901000c4581d1034100802c99000b07010980c074240c51021200c1540150404543c00341c2210f03000400d81e04d0300300b02198203150f024030494002924140301d003000040281501d881d40003c098550400116240b100d42000b03055603503908640030f0b07a00c170343c20302040c0346010210400c5440c618811810125101c51240501b5100003088e541d8200300000009801c00b002e5410203404e0990006900c8507603116071010013181c17403500080d2004250002800e802d5220110860300006e0708038401400a829612155560392203201d9075035001010a40110403145910043e24266a503980f00b1000c9200174020503030701601c2c4034605600001004021001031000254544400f260070304601d40e0581104800d010040454005201280d008075158000c0c01071040703641082d030000d11503a10a503400508480101e48964094400d120065801445100c082c41141d66014a001e041c06103269842c03103116030101c11840303070403845c001f8076200d4207408a2030716 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 995060278 1250 995059028 995059033
    0x2203020a0b0703200304150e0108160314190f0207020f04020702030a1704030c0e1302400b060313020f1305100f050d0b0a051b1303050d0804110d050f 66
    0x3000648405d98941290003821441403046580642042c002d9100d800c03640c0050703640c0c0d451507035030300d207002c400c000e002c0c29103c2455219810404980e403528502841040f16808001e40301041c8081507054501192464202510401100000d43c480c01e008529195003698003581d074a41d03610101c2e20308052803002414114240c41001c020b410001d00400890340100d0039000c56580b10a0140120301003075071032241d80d1980a19803401801c203000d5503030b02513001c880861100a8041b50100c1c0c0c1c8c20401c0700f5000405441144909212000d01c90760702909811703140307a8194501030200320901401c00398007030b12030402c880d6a05650381e1201c1c444c0f01c8940c0203074000e000504046d502d510444050380562903480c01c401c24041480c0c2000f5501643e00364210004120540310402500700404c2c02521a840034280d41c0101d8008400340c2000300135840d002c03203182009070301d141001800c00d081c08610340c0803c0442c40511000c240078082e4034100c04400c40d10001032003420301d001c0389400c0843c0c1c17001e555030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 995061528 1250 995060278 995060327
    0x15070812010b03061801081c05130b13060302090a030b1003020402071202010608030c10020913090804031104020906030a0c030b0a080d02251e050a09022203020a0b0703 74
    0x5211440614050740045d5202c0c10058420210f002c110802401030484580c00080041c60180f020507101d08220450b00b8054034103051903980244500700c6400c814907410000452800040141200800030309107490114100a680300006800c00352900c0080c0c0030b129250045280c00142444c440c1c011036004204554446140c940314901c00710004815001d94a0248001580503011085a80311400400901005a86400c91800075000b010742c1f5604185440341714096195036200b03d141030b80c000c1c030406031501d1039441c0171300711029400c0440340200c2c01880145420307254001625040607401001041d402c4281c40204c0c01041480481c542c4030106c400c0018000c1c2000c5103600703070f8000715402d0b60f041914000c2d840001d81d0416540240100c0d1114003005415500505034080240d241142d6001e6550340e00002c00c440c4003a0040c10200fa80025046c1c401651601403510a040e95080c0e501c5461940d00042c02e02602841140602c1100080001c201072140d1410314103642c0900c951000c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 995062778 1250 995061528 995061539
    0x20d0c0e030607020f030a18050613080d030c050703030209041e0b010318020603070f0219030314090c0d02040b04020c010504080a030c0801080d05160b090a05010f0b1507081201 78
    0x4180040034618080d0003514041249a031010030118000351040c0c004500e80501c0760b20403280d070110040a0b48449520b0900801d4583c4c41000410040321030b81c80c0c0348083c3d070901b0201814000c881d2a090103040c68040032129454100003520340302c81e00341c1001600d84030f5100101c0e016140101d460901c8072840c05a03580c2940e21079001c200405005c0ea001c0124605440f00f03241c02e01031840c0040d40c042e200784000b4030740e1440f079038603094205d4152040c0c428605c000b0038a0b040e0034158080c00c602107a00c2da80c2e8504207140300701e0502d0b4804c80a0000300713181c12002d80490140100c1e000081e019a8492107040b043d916950115840e070189040208800d203821b0070402980d411010f00e01001071305100c000a50180701300e0409040e2800e010190054aa414400743d84540c4015613175003001404015080120740000401c80c41001c40340b01419200103d40b404600b1101c0064101c0a03092404c143d800d104d44a0308101c02040094410040c4d80795018109010706014801610550600801c0046075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 995064028 1250 995062778 995062787
    0x309150309060507020d0c080309120d020301030b2d091603050309030c0409150b130f140c0c1005090304030209100311090c070305070c0306150602060a0e06061201020d0c 75
    0x640c007032241000b058842c10b030100d854181b03c015400005240704038182c041407024006581001084c01110ba03d10841e0300070030441d800c4210a800310300c2e400b00c0100240450005465071125021130703075001e555070412a075905a852031468840c0101050000b44d10008200960301d03d1a81880f2180c101d01e03940d1912076960307485942d40c07074024041e146002c81d007414280164102c0e983d10020507226910703000e203041e0007000c200507141e911401c0141c030680203200300d1240c201580e440b9100131440d41c80c603006e0b00005641c05407205034560410020b40da032046000c03030b044a20310200d500100d4a9202d40aa06203140265013001e0751011625003803041c00e00590140904507031265011307220700f500c114100603400000b15a07504103103000304551400244110002c121540c490360b50b9640075512911039504442600d0b614034008070121409100f0a0340400c14981c2c05001d0302c40500054000041d00c50700e07040041c1c2142e0040c40c0641c104c081c422802e4050f03c070307142c070117020400212114034002407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 995065278 1250 995064028 995064041
    0x28121b12200f1b071410030b0904120f0f020d0e01050d0f060806100e0a0c260a0b091620010e010c0f0f0215090c0909010c110a05100903091503 63
    0x10350010340001c2c401d60701d82c004031300360040715209000c4241c11500340c803e0044050113105001c00f0107a5500705201350382d0321b42c0c174124000d40c00307034903415585556058090220340b00e0a905070305020700c03490100d02060b40000d0343c012040091426042603081c400040e40d0900500b655120850b00b0151200b14400d11a03110b402100c039800c0407103600d0b449102d00110007600c3d500079020750303041c020002400300c456a041842c51490518000c0603444c040c914104125000003244505402c6481c02d020700d0a101d40a0700704622070469122031541010034902c3e25130b50743c0046000034420b00c0d003d01c140808840501140d03004005000f0701c6406103034159036000b001001801000b14101440b40340000744100400102019640c000701f80001d000d0303031440c1400c24020003089241c41101c0d0f461542c0d440b900140d60140c00e801e00080781d0070300454000340860b00c0a0b1442200303580092811808618005034048914547c1d80000801080c507040440306c00000307420001e00e00410701003440e4180d9059000c0d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 995066528 1250 995065278 995065297
    0x4020723072715090e0f21030a091a04060501080d09060806040504150e1e0c180405070302090f0403030518030f28121b12200f 56
    0x4078500c90b1039210212203100c6100d0082d01d11401e40b8041a01c030140c5a00103810701c0c020580001d01103a030303644080b00f40c6035604034682281d04a1a5151300c40c8200304070610030301c6010030351801c410030101c01b001d5050000610405925441d0140c00c0700b130080c2c1d10501502c0d5a5006007030401031805d4109040039050a00c240e441a208100844507082d10501d8040c0c261041c070382c0d0b02c031070f80e031264030412001d001d02800c00d4481070314103030000d29450303c140b0030001071100040103828481b05660707140e00c83c05081210001e09411880d00b101f8182d4484a000c9210b258100700184035480320300340a8070742480f03504000d400103a0f41050100c078491020f82184640d120f60340c18401d650312900b21011480c144c03143c01c6011303403090020380030841e0f0440c0600740900c540703025165448205410302903440e95140568010507125080c00001c5503d03401107040c04480e6110f6200a60b0814000818040080d40c42c414480d640d4542e008040c0e1000d600c1c080b0b10704100345210b89480c0010b2804000d170f4003a9511 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 995067778 1250 995066528 995066533
    0xe01030b010e1e0402010c0c080706030b01080c07260c1603021c05060601321c110307030f09050d0f17010803030f1e040809090903070b011404020723 66
    0x180c3c08540d00c0141c451210321154a01840352940d03401500c40c1941600304030344440d42c04501107034440042021000500301c50381c0101d500400d0500141549202030000e00c883c5004000340c0010440025401c02c0300d8001010640009949200b4500303107000f0070903407843e20301070200031030070741c2d00c11200340025640200da1440c1c240c42c40388441240070182502c0280f850308810b0015101d07600412041d44200001071a2070b902d000c00c0305050900302220b04841e10791040220f80c441e80340140b044c040e00420f149240c02c000016000d800c402c42070000074842000c250726003010660000a9403c01001258024102d441c64100d03140050800404a0420000135802060141229402d04800c60407103003408003451550301e801c4c030034100d420380043c503401c0170305214004211240d040c0d103c0c40344141d0040250507100d10a0030200507954401403c58000b43e401484128080f4000d2460b690440e0440003407142072103000b0011401030700031140040c04240c4d29407108080c1800f2038500303a401300203100c01e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 995069028 1250 995067778 995067781
    0x30601090f0302150a09080304060819021315050d090507080601081506060f0f0c0a110316090b0402041d010f0e0123012a06060611150919200f01050a080606040e01030b010e 76
    0xa0741ccc0c100c0c028852035001840340710004105820302c16501d2200001e141c50070342d00e0701d02481c450301c0503200c2e5200221031b2a4000142001342d0b1909000035400b501c1c496010301848514070501d410041c20142000388110000121008941c3c0b600c42211001e080d05090700e41c0707920400001d20f0311281855825242619084043c035043d1502041c44070790039683c0c241440e0107904001320704008103c030b0030502c2d8019900f00300100300d9214001980750400c4407414840699070408180ca2184021903111100344100000103002250600441c002c599100c2d0451648104200e07004980004208035180d40d11602d041c00010500907184403032040c81d00a000500205030703201030485950b800342c0203412213a003140380e21003481000703101c0c400c1c0c2005001085840484c4005000c54181180b180b040f900c1581040840112403011000d034964014211a4150350442d080d001070458421003900b001080201400143c00303030b8500c000c0e18050002d242d00982207686a01d8015071040c7c1c00e0042a0000c4080310 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 995070278 1250 995069028 995069071
    0x80a0c060f023f0405150904020d090b1605070b010b0c07090f06032303030c030405100c0507060b09010503030904020a02010e0604051e0a03091203110f03030601090f0302150a090803040608 83
    0xc104c2d01100c4020340124000e840301d0803540e940d608410081e80e8096006c0108003e156611f015600c4e4103800385104a0b002d0034015905445400c11010950500c003042c0a44004038a15804260444080024107650b0b078030310006c06401c0c80010340020b04418500010491003151a038040815a03110300d0303080030440e07005036000d4043c41000b14061038582c410000140e100850101840c2c219100b030045400410b509401c1c1004d881081e40e810300000d0001c5070850600511303000f00400e146060358604030341d50420021a03140c1c86013400841c00307950001a82c10440b4800d43c050002d5640c0c100c1a91018149441c01c40d0321006510031607600813084241400c0d2443c40402c200d065194940c40303082c00c0900c0c01e000325419941c290020b9040c844043c80300702e8550402d003d6107040160703c2002e540d07030703141610014014200580213200c9050400000f800140c03036103149003080708003c4075150b803070b1801749600312448951608a0410385c00042800034a4540265543d03002d207200d01142000400301703c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 995071528 1250 995070278 995070403
    0x31f1a011403011202030307050303070305040c0b180105181c02011812060b010509040f0516091d0411060d0609050105090412181e050a080a0c060f02 66
    0x2907041015180802c010041541c640d04581c106601c05001c0e24102401c545072541035402c1200d005010949a90802c400c00c0540b80040c0040c0c507061070420704188006880310040e1481d0500d0b0350510400280c201c800c03000c2e07071300c0580701c84400804e0043d0100c8518188688045814022404981c100c2e1421041e0b000e881a0f013810787e00300c0e190350344a41c0300c036860703031805455045000b506114081000c020103440d54042d00f08460021a008941410700d17000e0708031008034140702141084015441400303100a04050701a4942c10203e110101e41c959003840f55010030820a0b03594400300004947c1100036064002c4011554800c500304980d84ea61028003941000c11a00244514a01c49406400d1780c090020b245030564070000590115440e02c061401290400d658510340c005800010030081ca070006111000d000b043d4041c00e81d00b042c6c4e59030f0a0000c1c4050140c0c50900441d120390900c1d0074820025840b401e620b40e09a81d0454200b0160603519030480c1c1440030500203180d41007520b40d03594 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 995072778 1250 995071528 995071547
    0x8010e0a0512250305040e0109020903070801020a05090402030c0d02031906150e12070807140a12021507050c100f080f042409050a05030309070e15040b031f1a01 71
    0x38540407080c01c0f6110048040740800c0503904906001081c4808a10310701c1484045002e003c4051005030f039050300c4010149840f50640c810741880c0e004004c042d08050344402031759010308042e0760240c1c4945518001e282c2d03e000f00090b05d0340f45032020080288040500b6480b255a0341c80c103074200700702ca80301e900d8240b01106850030440030406489900c1c3c2d0700e0038056140000081c910341071720b0015445222403801c00406601260460082510400041c605130100300020403443c04031621448840e0301003601c120788030710105d0a10402042d083e003444000d00c00148406001460010200d40304800580005900501d400008005800290071011100c445600a030f0f080451400c1c80000c041e22441c1c0e41c54403820201a0366100c02c0c40308005001003050182d030b03a200340051516450241310756407400300c013503010800d0602090184a01e140047c1203010810b038098501040156030707507005c2450181d080361440604045001c060324048940e9002d00d9040940300c0645200280c000c0044a05421 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 995074028 1250 995072778 995072797
    0x8040b091513110301090c05121507030b150708040f0603140606090301110708070308070c031d0a0314070e0a0b09060405100e010303030f0501063608010e0a0512 71
    0x14058045140071a00001e604251031054140c12103e5000d400801d00b9100004004c072544c1c50800b005101c245004006280907805c214004d000106032880002452036014144105141e0385000113600c54543d81d0040181c29222450155990480d14001c0c403168070500c514507006103007010100c0d00380d01c02c2c000c04680301d5072690101e00c81c2e2589020001c176030f4001039260b9419940c4d40c0b00e40070b20070721400140840d180201010780e2100c2d02410040c158501c01840c910410a0500e00480044e1b00310302005c0f044000c02d040703d42c8841d1500301040380d0708000c3d00042c0c01c15a2641c048203040800090600540d0386486c1e034040242c54000500040e00c54444460350f1001404001861500f071580c03003240d03c00401000d104071160707a0341c1c0d00100d6813404e8000780d0002e600d0348182103c45400f4081d040c01800703d89019141200051450750381e500c1910003105200914200804481c003405020740041c1015000030040040074543c0903994080d1940d00312618020480c004012420300b005035503074404d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 995075278 1250 995074028 995074063
    0x90b0103050f07180f0605210f040b0406060b04080d02070801052208090d200306010f030809040e0f030405030601211415131109070509040207050a050a0308040b09 72
    0x203c819000707a40c526003c9400b114440a4103100041036064484184028030722a04c420381c2e0360072400801d442c3d000e11841900369035448c000900500019118050741e05c680c110942c0c07002e58440d480d04201802d455400040c4450f004280814004404180403036200b0030350f02181c941564070340c145821703100211072010968418100e480b2641d44202181e004151040c9140c41ca410b45180000f1400d943c024400d03070b142810b80809101c2024440c0500b040c0d40d100b14000c04075585004c1c03052404100b50300004000100c041840c0392191115001019403e00880c169804100381e02d01035030f980d4000e4070400f40320f0301c1280c00014500c0c0c03114a080c03e800301c11100890001081c0d888800000c4080c04140030705129140341e0503440c22810360b1081c02072a44502200c010742490620003501da6070f0b120003a202c1d41000b81800500f03034000c411204460001e65001d41c6880e00340c10a00e0510b20040b4010344140920b60720b4604041d4810b0a1038400c0d0f202c1c180c4c480c416140e400143d544c5921b034820f2800400c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 995076528 1250 995075278 995075281
    0x5011106100b0a0c08121006030212040204020d380d120507030c06051f090209101b02040906020901202104031e060507030b03070e0604091209090b0103050f 69
    0x84607640091030030442c84d0500301c06001884d5101030003984801c0d02c1e000c2c100000c0003400303180001051114002c1ca036615007503080c0300c0c3c6070700b41416022021380000e204a0340020520801e0782690403904590703a040c0200e82d0b0080164620818048200c0b91000785255890110411490000190a54550010310346080744074650b0040c1c03071300e9110b10801d40900080b03990301070000b602401640d1003003440f03d01d21014100005c40449030090681c00691280d801800894603035103a0114a20074055039103040c81d4504002040c2500d01c0510b000042d410a00f44480d900a004841e00202006242030340d0361070740b80208802c64440503002484003005508034620684030341c20001410100d0b0813030b403107a140ca8580e032951403e0300361107520190340000d020f00c4240418449280b180e5a407103807031424240907002031800007036242c10150060240590070480843c0094691303a01514849501c90310786041800303c0c0b00003400c08001031003151302031400d003102032409500c2170050a00940d04200c02c0c4816 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 995077778 1250 995076528 995076539
    0x8010504050405010605030f01062c060f1f0908120703050417031b010b03070f180f14243a050115050418050d050c01150f0501110610 59
    0x203040050803d41d02503403908000304050f07405000c0032845200a200000d03c0d1480c1010003506c1d001814144020300c81031102d40105040c00800d204d5110308111400c170f0340000104009040e810000c00a41150350085a0840380d003a0442400016034ac0788030f0131200f250b40001e40340e10484c0300b184002000118288810441c1d00c00d600070303048200e5031002c2500e09020b0542d0000b1510900d48140c041980c0d10380c200c69185040c10700254025101e51026080c000d428003541030004401400c12010041e65403000403c0c1d072205038081f40305401c0c1d01640781e403541061000d14101010401010803d0f4600c007100e010f661074001451408000d80054174003005004c0c202c04880c82410b5140c04c0e40d854070000454002540c20703c0b60403810164040810890743c10130051008a074110003402150080c107005282c0030680008403070b09841814074009d43e60308a01000140074246a1846041001e50b2050100f00400040c1e4410140e030350a0342c80205d44028a624a540c962096591003404041c8200a110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 995079028 1250 995077778 995077781
    0x1d07091e1802011d15071406091b031501030602070b07030213030b09031c05011a07020d110a0e070903030809010c0c02060f0c030f0315030a0317060409080d0902030106050a0608010504 81
    0x114124140700144c07a1091500c0407499013603141e201c51107401c2002502804000d922800619100344031001001d181c6840c0b10070b6641c45224001308003445040b007008890607541046680c41d920070107040004103594918004c006504140000c0721800a24030018000e40c1c4640b00f0303182c0071481d030b0412800c4c26155868140704a000900704041901041040052410082060b410680008040020030b9803511241e1144603640b0015241c9c8000d0800116000d43d0f208000c1d80011600402012491406000080c100340e1603a130000605810403070402001c0d036040a9000200ca000791600700056503600c001134202d60109850324049154a0b2148016040800c068000c4086015000b4900795000302c003140b668008034041541004000100202e0b0a8403074015906900207a004080920499801072302115002c1c580d00d00c104502000901241d8564000038000b6400c0a5402e940fa036102d4904ca020702101c4806a0081d800c0440001c0c0c0f82c1410151a0101c4281d5076a2503280e034213005c00c020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 995080278 1250 995079028 995079047
    0x5030105150904150608010f0308180d1403090f040203040209041104020d090501090210030509060f1f03110103061703070308090c0316090507020705010c0201031d07091e180201 78
    0x1d99481050103180303429221486010039000d4441c0780b8542c010f00e8a0700040c120403058003c0c400d11211070704100005154041941da540343c0440c43d1104140140000c00d004400c0d02c00064500303c1411800010690084024611440140c1c1c6030001e082403042480181d12003520000d400c07406410000317002c030390300d00403410006800900241c075010a8040b42000d490701d1100a0b10240d65550300c410451410360b50b40480c54005040511240c502030f2252500d410005141070410804107000685222000c00d90b9101444102c0c20a00c8041d04e03030400d5403020304085d01c841e0100e841d00c280841c403000d0101c50110700e00315502c0211704d0711074103607000ca89980000c0e1507500244580000d1a486030f405021854038403001203080c2500328541000c0a06440d4090a00d0701550030450090086991000c41c06240c60b40a0a01080100501c1c0700140001c40360080ac003080c5c0911a804112880e5a40011140082000341003000c1d9070b001e41c081084a07003e5460350348500b601c00d50300700154001c81070700 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 995081528 1250 995080278 995080309
    0x60903060b040f110408100b0d0210120f05060f0102150c371701050108040f05100609050105010210110d0e0709140f0915060613080f0709060b0a05030105 68
    0x42001c1e07040c0d001c00b9095070394001350744031950000300d0140485c0c0800c00044040c40f030100c0023403000c201d503400891081984000f020340a0944e2005944440e030003104c0c08001124401d40800a1a0588907d20002e040230b481940c4250764003612001c10b503100103004a50b001c185161060162039490740c0c03003034550082c0c0c1c82500315480c1410b0040240f43c00c030782c200f08021003c0709154085a00040050204007143c03102c240c14101c200041c041070340d004004540c000d5100c0100c0801e0511030809510303000700a1f86180019082c081c0126071094180c00460485a082e000c4070150360002d4220015190020044041020b0034031800c54815410b8001d1118144004150340304251500c02c5407041e20001c0d02450841c0c0c0d2200e003806a2007017400310090388100908003800e00109100043c400c01c9101070300c40c0c1c0c8a007030301203840d1801014014001300201404d90856000311400800c05465400600c5000d810030700d0020f00103100700c15101120800f50460307403820300d507a08010800603d04000e202c42c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 995082778 1250 995081528 995081531
    0x90d0f0207091e11131404021b01091403070809090a0902031915050603030a0e0a05180f1b030103060e0304030f0602030414010b0d02012303040b09070609060903060b04 74
    0x5030120b0980325841d0325a14096243c1d50b0100881001c40c02c0c0e0340311071040c441d101030400094620303a540c0c00004050307a501003150b141444072100054042e010b4001601801070b142c140c240102d607015445032420500c00c044550400c00780010081d117900804030050301c500400c0200003210300e481c1e6000c5600956201c40018280e580e030b00480c1c035020090842c00150180024110280419103001680d020042a0107001c1c1d803802c04046a22405075603c0c80041c0aa0306e403400005955404400e03002c0c0c0fa0140c0210312256000a00248100c0e00f81e80c5d000f0000305113030110740c00714940b07155120880180d0400d0342ca1a4610340d240c10052151142c100264002400044005140d20300082086800703003001603101c3c03d1074101241a15950b24200303402d03030305d0080b000b0195103030300500f840c1041e02400c2c444081c1c400d02c4440d4043c1001c41c0310140c42d40301d00200304400c03c004240c01a01400c1780354100e44200351a50003e65810300c481c068600811800740c0200002080c0d50060003080302d01910 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 995084028 1250 995082778 995082793
    0x50904050907080105010b0d061a12070e091512070f05060309150c0702100801030309051c0203030403050a12021b040504060b090103080d0c0203072a0e1f0806090d0f02 74
    0x84803401c5176806c0e0462800c0e05000917404130b100000780100f8014040a0384020080fa103400b400e84001c0c0705412030180080e81c544000348a040c003071302c0301102c402e2024000040a2a000c1500c0782e003007401251088c46200302c00306030950954001281c800b1b50340013002c8000da50b814081001a66080103004413114441c0c5030303007048040003001020340503030ba001d501c0b20780720482c510420007200900841c5500b04030900b001000429030005040080361800d40384040382c0c0b0740b1030300500071020742194065003603c4001800020000b0002d806074610340262031600e4034000c8420100c2e2900d170010240d0400e81a02c842030031541c42d182d0310003900325105000016456154101098604c076090b442036030720800200344107100703800b00c0c050385420b040c05201851905445640343c0356503080d000d0b200c0180340c4242d401060b100d9940800600035081301d9502c03183c84e15014008200307002d10405100702d400d18112000442d07000c001500c9010325841000303000341403010602240d546210741c2520701180f06012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 995085278 1250 995084028 995084039
    0x1b0309072907120e01020a1208090312130606050603040b070e12010c020601030506010819080901091a0405040f0e0309010e15161e050a1209091103150f01050904050907 74
    0x14010050b03184a5020280d0400b070310b84025000c2003041d103085040d0b40299180c0c1e00003595144146030080740324141001c1070780740c440d80704d4034601400c0c070480c0407801004180700480591400d0104490300c1100280500364a41082c0080c23800260750041410380c5c0e5001049039240100102e80420201030401170310002650051401c0d1030480c1c0300300016070840801030060080c1402000d0140c1280743c01044880c40d040c2a00304040560b007030142c40719130b0114001000341e110b0801c510007000c9501035003201200d00b00c0d2901290317000d441360b0b40c82a40b90000903141608c1c0c03400303403e040503003001c040c6041c0080d0350f0064904c8424224401d43c000f05000d6030b034412450103c0a0328120b004140340030840c900515041c0c2021184800c0710340c202d10041e01480010324001760030b0000d251321840a01140391091002c0d41c015405822160003a420003d41010388007185000d103110b84074100c60580f48221540030b00c40c4421600c6800750002d0381c00c001d045114103246c0c0005400015400c210350b08a41ea92 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 995086528 1250 995085278 995085359
    0x71115040f02090a09060b0604050d080d020c0303012c040309060305061201020307021515030316060623030d0810091512032607091404020d060e1b030907 68
    0x4540ca1001325641704000e905200c140d00c920040100241c821514090030b00700000d003070342c1c6c400c0001092050b0020344040c003400d154050b42d600790111402ca81e12942c41c0c540c0010320400120f04455a803030800700d10302c5207141c0c0d00e81441c0540d4154852441c0c007400e044007180500401031030540c000b1080c1240c0a00345901748021803044140740e000d41a12240d400e82031b0300c0008060078000d20400c94280f5207925a9020084171010074607245040c0d1000382c6c926058001d0b009507404211504001c0c0542900c3c07600321400300074844411820390b14540d0340c00e035007500c2c000810b845002e070700c0c00031000503c142c5a03150320035070101201c124a0802e00380d462103a020040c1c03107410105e002038890901100b0b500b42c0a10402c1c600340a50880c802207203082d4200a2507640d980c85421020400b0348504a02c40e00c0302c1d0f04443c0d91070007045003032000703d8170f401c1c80103140703402602c489254030f80c407501000f0b090b004081901e0280c01c800002d401c04510b0440040e408a0a803d4400d05800081c0408415030508 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 995087778 1250 995086528 995086531
    0xc17090303070f0b0613060518190903020a0209180607110a080d021b06010305060c130b0c0d0801050604050a050d0206250519120c1e05060f071115040f0209 69
    0x15103400c2d04c152911905219070381000301d031400310f102c0c1050000e2090359601c6110b441181132541c0d6030441580c0740c299001600c0c5803003c2031021945402e9a242c140756012503c2940d560098401e03c3c07075501c0d000704150b0005405442400c6c2d50f04035030003055207188a40c624401d4505180201e80031100b25844603078641d80a813044a03d40c580c0003d034464801112030071842038081c4000070b044107616548480f501c0d480c0040c8011111800000c07064040c40c41d40d00d140000e0288800032a0310b402010342555561904141d10b580405c041d07100024a61411504503400c2d0742c800382699506501e88800c0c0901c121500c40101c3c5e10034400e10015140c00a646455250b1300c0d16010000c02c001d00750f081080c01c0c01d40d480341c4c07002d240203e0100500030031544001442c0041d07075840e0500c0300703581d0790400e0b00c24030340c480d15040c8200c240c282d49403050110001c1c41c40d00409a801142ca22500e54450a42d445110107844c102d0075040014211140101c070202c465209000305404006442c0360750000300c5d1102c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 995089028 1250 995087778 995087783
    0x1302130213060809010f0606050d0b0a0f060201020324030709090809060c0a060e0604020105030c0304030e031006081612120903020a230f03100218040504030c02010f0c17090303070f 80
    0xc88000300700d03404c4024060340000b001184010840e03035003000701c02070040c8a2000c040c070009071500c0c00744403103031110014900240301a484c070b41c01179500c421000b4080d50058880b020054991041c92000510840400102080c001c004102c040d00d0704101402900c2d6050302942c10f090240705441442c0c5407200200071ba1148d0002811242c0c500c0d00c0c0c020202e9410b04c4501002c0da10100800c00180d800100307c1c1e40180c07072200c200b901c0b0307660b61808423080b01c51103518170f4041c050491802001c3c011038125009650f502c00070356080740e80700620002d19041602c01d00442284200301c00002c50a040302001000c0ba00749009030203030385c407034001c00c01020444e445486041505c010300300b000711400320844065a4200c400d4541c180a40c7c0010341d50303d040010714000540d00060360f00b1101840080400c4180001d4014840c0785000c5c00c1c081c1240300d000d0303026404201c40c2200300c0380d024480c1c010b4224040c2d1100b602c11030032824107405a0300d90850320079240c161008201e00c002060003e0300c0700e00202e2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 995090278 1250 995089028 995089037
    0x120c0a03050a031d010507060f1e0614010c0b13020a08030c060412020318220e010204081908180112021b010b010912080a0302132309130213021306 65
    0x48a4500205050485684070a0140d284c1040c2040c684c0d10100f11030442d6000000410003450980c0984000c042d5407803020015004103c070171602e02d110303030016821a003a0403503100c081001c101c01076600c3d009040740100301e080ca10b800501907003028010b4000c90b0b1700107400c1242264071808040e00e964414003c1c01d0043c0e20a50401c02000141014140f00c116148003940c101000d9982401203010310004e064440e00b41b440c0d0740000388182c401e501c61b501803103100601005c41c0e18081036000358083e010310303100c3d4000c5c140150701d84a500c0c144007030700c0b56204005614000e8048000526101420b01007410031003e08008100302c10b080c00941240d20083d0ba96001c040b02401c175481c00c4803010710245045c003c1e42070342040400315680860741c0c840c0e00900c2003a0f94040702c0c0b0048000b03210f4440b580c0030851040d00d02140312004002103d010401030500440c14000982c100311213807008845180c40d940100a40d5001400c03c4920800c8040c0c00f4240942800e440c0b200f801540c4440b83c00440004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 995091528 1250 995090278 995090293
    0x5120403060e0d09053001022206090302061e0f0f190e06070303200408060f0109050114010c1b09090b0c12010509040c09020a0509040f0515120c0a0305 67
    0x8401d0012003c0d0030000d0601d10101d601c1c20303000c00c162002884581680c100b0403903103141910441c0f055525800503820086503500c0280d0311040403030061443c100350100940d000810503501034800c1e0815030350004e18050074242a08150342c0700014000c00710080308014000c4254821000002d84440054812026161451000c1588141080e4000d0f841080091080e07040c154071200100c03010700350580780101e664800e01249403c3c0880c0c105c40d01d0b4007150002000079070b1010102e4080d001d0b0700300c41081782d4140d03a10040079007580c50a004803c0074038a01c4210400c158000d0803c0240c00388034001d40c0c80b50b0005414034031164909648049102c54603003044030108042100b20b581e00c0042c0b5030555081100444190780d50400c14040c1c0c5000351011400320302805083d0001700010008200195650f00e0100402407468003c0d002c0d440c0940d01341108040c441e5418024184100e4030854000100119042000f403c001d04924001550040c1c0c40c1b0320030281c542540050181d80104000c0441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 995092778 1250 995091528 995091551
    0xf0b040b13020f04020c15072307030905010c15050c0d0c020a050606010c26040e09011407031a0307150f08040b06010e0a08151501030b0a120512040306 67
    0x820354000c000000880d07a101011006954040444010b0803050f2030041c1c498101031101490038240400039044101c0090411a540d43c3c000446080303ca5031400c0c00110040b91380034625240940680103010600e0000140300c554801e586422000780906030000302640756032003000450388261074404c0781100000f000030303605541c0d0281400042c094401890b005c030041d100c47d5107505c4050503080c10451030f41c0d4448140038000110b40d2492021050440c80c5089030b1320b41020b15805407044150040440e80080d141c0030707040c0300d2180b4007480c8803240220356803542812001808202c1c6403070000007040295403a40c0d01e04100380800703042150032210607214030702c030040d002c1c501280361001086091010000054000e00d100c0d500010282800103001c0c405c6800210240859000b445841c420019060304a14210b041c46e80202024141c0d903000324139603001113055582100d281600301c01580380400c900030003250a0310380b0350f0042d425140c50300c0c5194680030703144d4040d500640d2150b4952038100718 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 995094028 1250 995092778 995092793
    0x40e010e0f03040501120c090506030f0603070b16110a120c0509180a06020a14190e060f1602040f020a050d0e0318041d01060b120a022805070f0b04 65
    0x40e451208010b41c101407800d800240040c1c07103042205c0d40b258031914509140c90103001420040c1100800068892070050180001d922048a60a100e880780c10000a00345d61184d04031044030030360182c040b00e40c126a40741c00804003403a00301140c100e003d0000010703d02d64a090100e080610408034211558a000100406413801614140707141390b201d480d00019600004405a8071a0b00940240e1521001d0750251001b122400d604001f0300400074106030900d25141e948c9107418203d40b241c1490b1490a0300740401ea000302c1d0741600e540d00003005040499041101407400d035610040020915402540c1c1203001c3c0e8204580c42000300b107011408001c101c42500034402c4048045000310700b08400040c0d5000a0055003091501496a0300301d2181f2600c02d022040740c2500b0340c00700900000b5501c0c02d89252582c071140c4a0b107122080300c00440c4050180c5d008903507604440240b00d203011038004000a076426100000c03103080c00002c000000000b000e00403010f03022806015503a0451800707081c25031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 995095278 1250 995094028 995094043
    0x6020d120b0307031e0b1005041802090106030e0709061403100b0108060108130b07091e030f0816200a0e070f080910021602010e1c0b15040e010e 64
    0x1411036051008002580d10005090f400b205d0b000700440c005000004013000f411041c201c000303000080080c04016800c07000caa4808119030342650700700031031005124140d01100d15808000c4d4481428001008030b140300360040940c00b01c408007030f00c00c420f581320303000e01c1151340035444111808810500407800e45002e12030030040010003401400b41c0710050000070030a050003042c0f2811b00c940c10740818105000d148406000e99441070b02090107080900002e41b52141a10607403580811f002c01c0b1016400000e00c05c00100c90388620224120304060703459400720b80000407450082514400d1031004070f10a104540750010b000e82c0d10f42c1d0135482c4841070048442454000206e20800340c000d00c090103500082d031500e4000d05190801c41c03500d540742458280795404403e0031015001140d1000e00166542514203084d00c00d0f04e85e414010200d40600541540d0301e08400c0b46180807400400200d00d0189100b60301c680385c41e8242d511002580700003000c4841a044d58a4103070340da803444c1c1340540710801c00390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 995096528 1250 995095278 995095307
    0x1e03022106010e13080706060e0a0b03070b070303110d0605030705060f09151303060515030a0b0403050304050102072012030f0702060f070501240501080f060907020a02030706020d 79
    0x59000d80050154907a00e04040c461400480c01c0c035000a02009903880103c070000d039020000c159240c1c1c1d1402c0c050060291070003103400040e9400042020700b03845210708030000001501402001e8508100b51405130044601507003890f40f5003003209100040fa800906c41003840c0c01c0001340e20707810b160a141c0f800ca41c640015001e1401041070080c0d00c80e1140542d01c00c0e0000321002c440e101d0303803103602c44003d0162240305820038114100201c01c2010503000300748034200d40c0c0520030000354540101030350b0740f40100c006001c0070303141004940417921400003998868000c40000d0329100455440c2045007442c0400c581e0030a01052880c0718a280c90800700aea001051001103043c003401e54511b140522031544002e00ca054001507c1c90707420500000d0341c40550f00f01000700100e002c60100000c882a000140a940200880c000320f80b039800f580c4444c0c0074801110b00712030a0f65400381842620b0704050503020551084008000040c2d80400081d406004144e0203000380c0e040c48a0f0113032000c101c0b2520f8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 995097778 1250 995096528 995096569
    0x120612050a150b0a032012011e020403170a0306080319030c020601260708121c020c06060111030702040c050a0e04050c03130804120632150402041e0302 67
    0x8001c284d99801402801303a0303810008030b40c9400b8214031990300d00100e89070030940042040304c0c00c3c2030f130760750652118041c0380500b00c1400d0324a0350036510100324450b50000512a60402e541503904490b800043e00c441c5003d410000707100c7e0345805500b440d43c0c10000883d105950001e551606917070381030048d808001000d00003811b555041060449a44403603600c02685940071681d00150300c1004c00050004040305001d55845980c4494042d040d94040c0d01d081e20b9a4801120b041c840e40c4d010300c206d900301100d400c0540b000303881346001119500c3c49018002001d20052141201580e258415000315010b5900c503580d60307500249018003a141c20020080c802c5181100b080100110201240c1d4082e985041c1c0742ca21600c1c501e070940709805660841ca03540e0654819060030452154007468142c1000c2d02854a05129000290f078240e4040851134560030010000c21440e46410005814801e801030025080585842c0250b40c80c82104100750f41035112401d0420035410621960300c8600c20031b80c00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 995099028 1250 995097778 995097791
    0x20a0804092016030e0118090501030209061e06030a020f210912090f0a080d020307230c0f0105040506070f1106070519030309080a0f02060106050301060f120612050a15 74
    0x150050408254070040c0a0119910203c41c881e8890a407001e500b2803d1f030705104501e45c0340c0c00014001d2409020481c000c0080d034010881c0361402206403a08400c0407000b50003050080c40500a40c0d030006804a82c20b66000d1000101d040081806001550f180c4406540c031400b604058a032070032005459001d40790400c0850714a0106c1100464a90b040141c40f003a0a5441803c0841c1083c442c50b031065800d030241c9161128001c0e0f01100400c005401080224080d4400400d00b55080110401c503441d00d0340040c800e142030741082c00f0012088801410183e0400e036032100411101d03401034404551500240248a04000910003800401c1c0002d44019003407156694500c0c0d40c1c1c3c0000401c00721503407625010300c1d0401d48290080302d94590302010a540b16981c1d408083c14050141e404500507020740000800e42d18400c41c1540d04880780c0e66070b0b40300e0362044450151901e80384100102d4803e92250320104070b105604149400c114404c0e4020245040c0d5402c0c130143c0c8000182c100701c4070505051 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 995100278 1250 995099028 995099047
    0xf06011a0f070f020303070f140c0a260d1211070c0b0c16030b091005040302070603090c0510180e01030b06130e010504050102041a09060f0a020a08040920 68
    0x80c159000d040c0354560482d5603031218246100d440e085a50000d5040c480056090100900038076031280051250455003000c0e9043e00001d0703203c140c0100b0503900042078807410007951300c003000340f81c03c070031075001d03003411a28441c2030301d01d040401ca9284800419003000726143d00301914440c2e4041981007210560416445650389105902c5600c2200070508000c512508a42000e102c03031010b20083e03811400c00c5503a41e15000001d41d4040340c00d608039004480548000078401c2c01003a21132179061340900412800d02e6011381c01868100c00a0b9001240c144000c0f0b4640c40348100e41c44030b0001c50725803046564121241050412464100708030400c1444010000225006410780e0020b00c00c81340040500c0034040b0500040805903088445076003480144428020103600030400d43d02c10341c00981c0d0940185c0e100101521403d4002a000101040003810040764003024000154952040c1d4450100507110005550020b4202d41025580d80b1102144105009503104c81c113000b507200c07981040c05d00d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 995101528 1250 995100278 995100329
    0x5070f02070605040b1b0709090b040b01140109150c060608030c07080f06070302070f02041a0a050105091503090712151d1b0a051903150228050702120f0601 69
    0x102e061500c4088100f40d4406e01c600d0a1040d01c01404031000200a0502c040c10200000301c0151000c0d43c09428402c0003254070130300b01200391701c85034040e140c4e0341c81c080c0780c4100070304c042c800c221300300c010000100d44440002d10309000d49002400c03504000c58a902502c2d502030b0078000b90798004001c503030064254113a5424003240a540c0040c9904005850314001d0400b2280c3d4500c02d04000e6010f803510214056034000700c0080c08101c1c0b0306907110f481054070380005503004d01c034202d00540c3c0494081c5110540c074244000541c2d20903100419944241da446a45040c21803120404a913445000803201100310501c1c841c0c000c0160607100089504182200c243d82c50b20a003503006035214107143e550a01e00d4031228160002840050068500404411700030310000311b00d40011580105824450800c442403030081e00c3c049800046820000318802c240b8212514410300702009102043c468100503940b40303814030000399003440103004590240c44429090103016003010050300940c0c02d5407514070084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 995102778 1250 995101528 995101537
    0x1020702131b0e030106090e1c0201020310051e042c0a020a030212011413030206090d05040b03070201180b010e0709180f02133506070813020405070f02070605040b 72
    0x3410314401c3c0c0764403a00400d015004a40003c01020304007040030055060000b42e2140300c03407600c20443e6501c820181e0482c00d030b1100303031804c5015440101c01400185800129035071550104010591a8201c5201040c2956164500c42208001100803201e40d0000c151800e2489030350301d005456a4819513002030924241e0b40800390144181c0c4c0c0c100104075a095020b00d1614600da0340c003001e603240c4440000759180d81d00c00e0490042c0205808208070030b40002d42e041c110021516402e090906040d00040c0e15003004001c1c108644d00e0388646a0080200c0b00c1820300c9034098181c1c00c800e036042c01c0010120700c1000d0158000c000c982c40c0100000d003013000300a0aa250510000710b490386906c002c0102078000c9000d130032040c0e0b8248100040f00580111500720002109600310001c1022038400c005014450104d80919005400040d40061080010070b600001c2c01502515140f4690041001c0710821202c040209981d91740000da22601002000010401894040d20f00fa040411000243c000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 995104028 1250 995102778 995102831
    0x151e080a03120f140906070215060607060209030a060c05041505090102120903070302130f050c07120804080d050a0c1b080d1a0d0803010509240904060b060c0102070213 74
    0x20385454a103100c0f9469005440c0c0704840701021065405d100c02901d40f111015030b98000544140803207501242083d1511620505d001491139007001d6440c3c40701c801030760089645c140e040c003900743e40900080031403084200c407006654559880b82e0801d00ca41c9294100604603070248641802514650383e400a03403000d10008030b45206445841201c00700b841c2174100d4200130351001d2000680c00f41c500c003e81c450300b11203003803000610175a101e41c03005801a114070a00a824501c14810a89603180a88085508184100609413614060000000c11540180da1140c455a03c8804030300074a5405222a104030701c9000e0f5030748a1005d00d42d502d4020f441010719031048aa21448407421100190040308916480900b081c030700551070345041603856100340a0580714000d02e0000c0303109512003004e2710041e010280c40c98003119004c0010401018002041110a60b840304c0c03003120305480303100c054200c3c005210300150b01d0307505034810018040101c0d1f03e110306051800c40c1d0b5003244a642e9240c880c8994 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 995105278 1250 995104028 995104031
    0xf04020f0a360c081e010807061815050a030e01051003110f09090706110c220b06040f0305060f060f090c0c070f0501171005040f151e080a0312 63
    0x4040c10504140d00c65400c20041c01600d825100e41410b60001c0400b03101c0c00030017180c0c21424044500b801d684080078041d0b90000d81c800e00d003d1048600695195105850301c207500c1c400d01e5a1903200c20102c03c0d0a03920b0000107200400c5000080750580030340b00107148500004d1009180c00000441000030601c805007003500e042900e4511600c0340341c441e18907100090500249403400442003540c2d0802c0c0e10802d80040c503d0b08503680400c1c030104070101d1648000f4140406203003c1c40089001140c0780009203c6940d84040d40d21850f40d8550091008080c14007a4903401403860500d181403040080000c0510107c1e0030822001e555010a000c0443d5011a06c981107a101c05d000314256003d0020f05c0e8000e0f02c160b500100e01c000200c815801210000d80c0c03107050b0445880e500c071202072402c0e2003442121802590900552406402c1703922030601000000603c07011150841c1e40406036648201d11420038001c0d0b000403c09000d610b00080d00b001d0340142811040d40c0c0c2c0c000c05008043c0a80f01c4104e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 995106528 1250 995105278 995105339
    0x12090c0a031406100e1315181e3917010e0106080705040e03040e0408030a05070e0d03110a020604030803010602010b010906020604031b0602070c060e040e06010b070303020f030f04020f0a 82
    0x80190303040481205e00801c4c2c20486071440205851803a0f034840400da907001e424540d0580c200f1270320240552070a51262800a411410000d4144074226440c4409900358009884e448201c140c50702c00c00051024000d41d0040380c41c114902c0307007140e10858078040b440c0d041240070700200d0b0000507190119141990001100038010f14101e0a600840d008001c15206410a000034464400c002e5030107030040300401c018640701d4110598000b40d6092405812462484c40400424040c0660350807140d0384900303407080b0b00c881e9400501a81c0c03007038004941314007021005001059091142a104250038203080100c2c40c10090040c0d07071020001c10040801580c0c21003102c0a80700f404000c4903d0364000d10a6498215900c0d10100e460074500079000002d10341c1881d11514a03181c040c0183c02800343c0c014240c16400e00f03008600c103a010300300a4050540800c0b009802e80d152500461007007003001c1c0f4681c080e0030700e4410030400304a0b40043e03610410603a0f41c244900c109000c08140d0b0340e19501448200c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 995107778 1250 995106528 995106533
    0xf0f0105042c0c030f0102040305060a2c0c0424050f031b0d0f030c170405130f090203030309061e0c0306100207050402031014100512090c0a031406100e13 68
    0x141451a400f260300360040c0c00c411003901c41d0540140c41900c0c4144103845240c0d80d42e440b184c08440c2017098045a292404201c0c010100590144031030703480d041002d079040441940046405d50300b103a8946400140c040d14144005950800401301400040780c011440b182c040000035074420700b040781c81603001040c001c001055038855101c1d0248c3c0d0391107010f06103261442c1c14054900040c3c1e1105952815442145c0d18400030080304881c04d90f907000704084840d40c91581c13103000400301c41001054866031100c0c0203015a0b0108041c500c02d80c040f800500b05480d10784074160f158441e030320000c480700c240c040502c80d0300f41030281980c0c1c2c0074400b980c85c1d000040340d03948200c0c90034640350701c003030f030410700c00070611a0003108000d80d903065442d004820a0b98142000c1030003060900880fa607070004030180300c920f004502c0e045d40e0680200c400c20490381c001081c0c2c0005802600240e0045400d8070740d68400015210707080c03040c3c640c050300032401e0700c0d4954540300e8054003080c402840840351103440c003015000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 995109028 1250 995107778 995107783
    0x140307030e07090203040605150303180114040308041a090307270c0509040605010c050c091806270a050616030e060c0408070f150c080d050f0f0105042c 67
    0x1c41e0041142203982d06980d48030008029402524151b60141c1010001105030360014595456444050025864480350300307454411744000d840f00f24100310700034040301d144080f01400361020794041c03040d05075114540400c603042600070740c004284025051105030240d607000305008044462034680410b160344002c00210b01e440c041340013001c2c01803034500e0400d0881d6006010b0208042c040d40c0401c405c1ba21000152124041d442c1d00074030390f80c00480746030b4003814a40d1603680c004403440c140314009608402e182d400e083c4101c40b04894407000c0c4000540d000e42c0706a8400080c0000d0018103041112600c440f52a217030002c1118040e803121120640c10700717101364401a0040000410390740a810004116844ca034098840c12030304c0c1c420600007240700401c0d02401e0080703854902e003040d0001030221064694811a11080c1d4010b0014001c288580e00203001e03240c820072203009410014505190b00c0c16580308181c0040340154501080c01c01c0e009001c1d0004025180e0b600d1010840c8441e1001091 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 995110278 1250 995109028 995109041
    0x7081b0913020723191e020d080a0201140105060703080711012a140a081e1302040f2d0f180302060702031315020f0d051c060614030703 60
    0x2051620008480080c003030f0844508280c110101c4c1c41480424180c00d800d50360301100c008200328000c2c0a00e81c03034002030f46910315941c542c1c0d1058148071039185035000196491003551040d0fa5910300044e500c0c00c550360a10904140c0d0800c034081d0302c0d41d5410000840d8890240000c001c0a000841d0301107020035015a02080e03001000c0c1d40240320000c510300050000144101ca4801101b2a00c0d58005602d4010400100303500d001303007007450404503442e0003103e00b2040902030f040005c0c5154140c15010551403001c5103d20b072900e6100c01c400c445441030008450380554900f482a24004d0350109020351a01c0071030400c105801076024070400001c01000402035001454011440c01e81c0d00105445041c102c4a10380c0e003c4c0d0241d17103169071080b401341e0b10382c0300e40c19070040c010100e040c003842284001c500200e50b0400c2481104d0fa4038594a80e55480d00400d07500fa44080b92001c525540704040b0f10400f91100345c0e8110f002d0000600d041c2020f00b00309007200c0021402e400200c002804503110f6030212 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 995111528 1250 995110278 995110309
    0x20607170408030d06080102190f0e0907090618060e13020c061305160302030705150c0615040c030e150c070c060c030905031606051309091a07081b09 66
    0x8036907460b40c070386015949500c10740054841504000000440d8103061003a00c3e8950a0a4010428107200203401c64414600403c80e10503c059080c1c020f60a03100c0c21049031252038651030310880305080140103401280900174900b60154199810701400b50f11010890340703010141caa902c10084c00f0040c24010b8095104d00f07030264410b0788100301c201080c1280950100780108141c0b0404a400d0b46540800081c2c0d00000e50541d0028004100c0d80c200310740f00e000040c444010407420b0420200d81181024806e07500902801101810f0042c185050303c074881204040341000c02c0b2841c41d008182d038541180000040424501100252003a18150119000c6130f520803076007160036440c1e2201800700e004e407400680c001119150f01190b60b0400040314550303141c9010200c0c602500c1c2c03d404550b9030348400081003070310740010400075086280d8000e12480d5403245a507141181e1031038070b14019042000b0500360400c05650300748058410043d07a1003200100614403036030303a1503265011952050074a00300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 995112778 1250 995111528 995111573
    0x120e0310020d06050901050a08030304080d021c050108070603020c190c05060a08190204081b030106080a111e090c07022d0a050603160c0f0b04030810150507020607 72
    0x840c40b00c55150302c500191074080f920410180d8844040c00340d0300d513140c0143d00307081e44104080b074042440c8602404840c11a0f6101519041805001025040d5103075080704100d40c8650040c080c04806000e01d4003d00120700c2c3c21400c004c4260440c650725040303680884140160341101c00305101c0140040405094041c10607a07a0700c410003801418a40116000c1e0003801000078403004401d0b542c02190100e42c030036002069100030107800c0c20705121075582400d07131665840400003806130050002140303c070701440c42c050600c4049000d0094403c09207070b5400c1d00e0300c034020020030203079140000309400c0f0f403660320003a032600081c0c808103100d0481034009203059190b100c4032502410032190500b2420174241c480c0d051007a40c1310203020350785c0001d46d801010280e030110000c880c903126800c0c0040b040c3c003c1703c5c12030840755103480c0c030900d83c0310603603080d4001000c0074100074440c407420705414010100142c45050094000303d00410320b000742000284140000070740402440b0452001c2200000000c0c50f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 995114028 1250 995112778 995112787
    0x8041407180c05071101030b0111010e010c11060112150e100b010e0d0201050901230c060403090806193305010e0402030f01290304080702040b0607120e031002 70
    0x15210401c44826840403050303003082c10041d0168400d40995038400da00030803c00101c00907400641c0a00400c030380d12410806c001c0c00703206050509000e803184c032028032000014141c0a074480240341035003071180349083d0ba10440042050300c500700b00000307c0c1508810628a074840100300c00002c6c1c4519418403019104006000d11440c4183d80200440c030402d88688084d00303860014401039046410020b40419007d0000450f036500900c08603400442500496550b54421107444a0710b810820386c0034000d50200d82048201038104d0007610186c003c1ca4014411850700151900b5881502c0445202550712207000c0d070103501883c04555040b02514004407050280c03480469040c055510440d030006141840c0c25170b03142400e05c204c0b400340c644d0805445130382e0b09000400b110317600004d40c4a41c1c903031140d41d10503458003240405035004910a09899030b8451084c0108000e4484d2400b15a2094500301b06480010b03200400408210b0311300d0070040c04503c8044002820070315807100003002d40c0d00014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 995115278 1250 995114028 995114039
    0x62b0c0e060a0f11150708060916110a0c09090c0b0c070501050904020c0f0f06010f08030910020a080f030907050a121b050a08010212011406041a130320090705070308041407 76
    0x140c5c2500c2a2070b00d96a1405079994181081012403064030414446403210003405e01e0b02e4407030110100c20000d6070040b6003103660344d541e03000b1610400d82d000107440341d03881255801b04080681c1840081002e026403d0402d00340c020040c1d20b5410170b03c180b50602000281441446d11550155450000550140d034180c0010f0320000c2c0e01c2c1c0a40078105100787c051803001091882e000041e030703800e455021b0300035800c06400f00240001034007088a004150f2117004101000a92040300419030704145218982d10380c280006114a455125085036100b41c40c1443c0030300920403100c0d0180100790b0018000401d000381043c0651002074150420f580003001b080e804200c2c000705400500c00e98140340124070303044ea662420b05110301d460340340480d4090b004100030040804401c03600c4140c442115501803500100c0e41c1c903c12032132031a0307208440d2940140d01c9014495030720424540140d1b000c0d50b4034249442d000d40000c0591045250040c148403c0e040840e090042056035405208280000c0704e101c1500c0700e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 995116528 1250 995115278 995115313
    0xe15030106020f0d021908130f0b04031505060906041503170711040b01020c10170403030c180b0306061303290c0a0210020306062b0c0e060a0f11 64
    0x10000c280c240d04c641450540e0183c40081c0209000e0000380c00445c481d8402c0d940d48400d9441000020091070300103501180c20005141894005c0c1504040030b0759403071171403810310302e0000c1c051900703149079251408018094640c0442564480d00807100040d521161b1440a8003c111681001e40f0040c1088480c00c00802d03400010b00b0741d07900070070403001200318800402056840c422903650058002009040707407418021841c03146103800d8141620000d011158000400750304440503000240c80b442c0c0c0b141c6a50b00181d031913520100c829640300d1114181001114a844050716241c06198000341084440c401003195902560313000c80510b00070f40c0080b0301e0020b8100b103540900e40b107004140114408800c2007044400001c01364000e0840c01d41c0105503c0000c1d040140800e81101d010001038201341c801d840c603210308098002000f0603040c9101d010501b2945044464400d000c0c00c80903010039503881406940303421080d407612b6142490102411170381c5840704046603070302d48640c1e07241c0300b2001d404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 995117778 1250 995116528 995116543
    0x131721041e1b1406090405071112070b07110703080c15040b060405130302150411030d030c0305090d140d0b06040f05010f0f0f0e0f030f010f0e03040f060e1503010602 73
    0x2c111071840250b1108070040105200312055035000c441040075541c14201a08038961200d000d040800c02c0d5001e100c4444c2c20100c03900798900c4844800100141000f0b00e1101e072035000140740c1f42a61410002c003010700c1c0da0b0303200d6000207015100b0200305110031060811200c00d100c402d0503922a09400c252900c207180020036141944698104000174142054107808004103542550040ca40301561181c840180903004d001681d0140049204410319102000351b41c5d41e1814554000800c015402c2000b070031548042c20a05950300f0050382d0350100c5600c1100e4900b000c01031070038a5079030f400005c440130007044002c841035000300010400040c118010005078007154000c0c0ca5200041c901c0f0b0381d00302d0301000f43d4115400030441110780c00701c1d2140305020030206540080e04600f221701c51703003000920380700c0280580e0405070345490008204004034003d510b010364007400114141030400c40320031642045400380c2005c00c0601074100c0743c681d442c00070221059240034082d650741c1d6100e0034000c5d181e10700c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 995119028 1250 995117778 995117813
    0x1b0c030c010522050325080417070603050106020a2019090c030207170a03060306180c05030a050a30030b09100305030414010512131721041e 62
    0xc1c01d500e030101c030219003010f074501a034000c001d03503d8a14488040015044001294103491403582442c1000a14540040004c2d08816140c2e000f90030940e0011407800390300fa04880d08250904004000282e00010001ea1076a803100c0751a500851151502400710050364080d84e004031790740d01c0c0c0e5015a04140040064640400041c40751070702c80c600640c142d10030000c0007481c198500d075480443c00748007000b500064804d46000714042d41e0341c3d10342c5401e460f0029512070f5841c0c0070b040054100078500710504000d000980203007010091644880f500d516044502030442c44d000c06954900c0000d103106032072120503805107036240c2c052159004005000450360b160250f0341c0ca0004c280c40d290000e440c0d104403648480194502810160607070f03a110480d0250a041c00818040261048040402070303101300313855801503551030520f0614000401111401000280c01003000b90703400306942400011411003010210300c5915240780c80b02c03038810542c420044483c8020842c50801400e0100140c0480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 995120278 1250 995119028 995119051
    0xd0f0f0c050703030e2403010b0c10050c0c10110d05090a12021e010b150a0219080309150903040915030501020c0114010902130e040303200307180e1b0c030c0105 71
    0x388003481c1646181d0704074449003000f50040c8010840041c09d1780081c40326040480075602850010018041500d40599091080120204106140724000c002d2604441d1100f50140000314103800d09080c10701c1080d04244000f40c0380c0000501043d803c10001c040c00303900c442c00d03600d10404072400039210302c8060032541c4107680b030400f07000000c0414020908040f0b0020300200700c0307110b01001c40d4010340c04082a02d0a5004003000170000d940101041070843c2e000b0445184e407441e00d20162410084c06402280d40e0201007000d102007090000140c0e810744e03100903030020b4181c2d8803180781d0740c04401603407005200790300020305200c050b0019042404404501040c0c800c45903294110707401030f030240d402c1c0f11512182c01d03281045040c81d130564541d0002c0c02070034001210031080c1e058140300d007904000b80060680002c140f114441d40a40000d1881240481c24020941022080c121011024001c5204000c8011491051110480c1240c0c4600c0e240e0040f640d480c04003011084c042c1030115a40c0c84e800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 995121528 1250 995120278 995120299
    0xf0e093610050a05010602151f1403120a1202030405030f1803120a0f0302400f0f09052509050f03010c080105010c060b03070303031d0d0f0f0c050703030e 68
    0x1c10f194028607068604980240c955009620084505040004d05a0500c045111000c42d11052006410000f901a188130319400356141010705141a5900f200100c012208008402040e50700c04c2c400304640218504c05079894480d814114558000c13290203c07208900001c103800000e050489001c1c000005601345d81c1e01442c482d503039421500458026001049528149983d907070710a50090040000500c024a440300421640101c80010382c4802c2091500c8050300110f00c420441d440b01c000c240b0107540111440c100441c641029045218400703000752a4000300c0c100010150105010018140000016515050f001004100c01e44a0640214a100740400140c06e040c018130902940f10303120000644d20349401190441100c4105443da01c0c0e03100c409410580d0107200840065000343d4000c41e1600030052092040c0d55590b81340c20441e0301402200020315044448c031407291149060240040810107400c6d2a004607982004009024642c1d000c810560444c55980704110b0503034031650503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 995122778 1250 995121528 995121541
    0xb040f0501030201050d020a0306030807050601030c08030c0c0618152a0c360105010e06071709040f0e0f01050c120610050c01020315010f0e09361005 66
    0x3214401e0101030f001450030840c16039030a0303060700145014030702d0b8075001030b540b69603440b10300c100e0b004181c0032511500058010001c0c006124171080241132020040c1d0b18200302c04500a03070b10100c21004a018072804200341d0703001c1408402c0085856009820800144c2c548001852540d200009100c990740041a03000500506000700d81024044079000340400c542e15000c00824004800398842d9005400f20450502c48110408142d144094240c0071501e5041000240200802c50309c249e026140510141f004141c495140303140f982c0c1800946583d0f20550780102e40944803544411641d5400c00c404c440e0600e600080c2e80c420f1a007044001c000d80d0301c40c00708450042c890203844807100c101c2c5001080c124a0f0480a480c2c02268900b40245000301b100041d609980084070741d0310302040311004100031075030000d04502940840e40342c05841264207074000ac04111001d0051a01e600b106101c034000d03544a01001c44c1c942091131980c410304030318800c480f0343d99840c001030400000d0070300020505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 995124028 1250 995122778 995122781
    0x1b0f05010e07141e181e0c070b0a06090c0806090606090d1e0c150807020d1209060905030f041e0b040603020304030c02190f082e06090f0b040f 63
    0x50311207400b0411100640300c3d0030084030b00d800d198011500d00e42c0e0080714a2980d100450b01c01d000f5141c0682d80074628144603013115042011181103010f0742c3c20310130446c2807030b07600e170480d802c650b40b01e2044001600c0311081e900c010082e41d004034603200c0c90500824501030700a044984030b031208942d1f00300e540e518801402058000c040b80550050f5510041c100082c6104c0e030107811007101001c40000031845602c40c41d5001506030710400b401c84030703048a43d41855104000d168030000a00040580b107102290041c0720040e00084540c6469480364403200704021b540098404a42081c00c6075107c00c01201c0d5102d03140d110b07100d85a06000030081d8001c00f180340d01060303400ca99401d0002400c081c0f80c0141a0040d510040c0700f14100400702e80503000503903030403601050700480e00c43c5107804139091480400e0818030a810020031980050f80512100c250049409800322240900119150f0b5544114025115030b400a500c03084c10320701d483c182988154001741903e40d040328180441d4419608020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 995125278 1250 995124028 995124043
    0x1081204030f05030715061805220201110607111b0603013008090301111e0f0d050903090a05270606070609060e06100f060f1b0f05010e 60
    0x45a5040900c81000403800428000d404140140309032807514082c0c2d501c40e0f02000d0214451441c1d81c0d52070704207019500c403c0c00c2080c1410400c40d001c00a0707086c02c4003000c0b540c140c040d030310940719030411400c402164800e030f100001c03c50446040750450304140b200a80020760802c40015584560007941d424480d1140d040002d5110252010f45964203220f6051224000700e0707108501c003405020341686044d601888081120f0248400035240e00c0c03650109429180d6400c00d0030058441401811300c3d1504200c81124501007001050fa9a00d881c5180c001450240d51300c0c102c40d051604d0204400345034040f000380011407007290420984c83d00c0e0400c20082c094034503000022254602c00c040d000c103010444c0c0c0c40c2c008500403c41760030720006603100342c10754080742c404492064032020b1501143d2000c118542d040000c51800721951410f0003103120418455120b56010061717400001c00d05907010785001d1000c403000c265880c000580c581040313030014411031421075081d0b1030610f04a00d00070000c80e502 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 995126528 1250 995125278 995125303
    0x40c1706041728020a020901090e03040b0d0b03030a020c2e0f02010e01020c1018080d02030c0405041103060a0602030315060d0b100c050105010b04030201050714070e07090e0108 78
    0x244482e5004014182c0d82041006000160f1021480c2400388004075002050000d56030007071440d40142c1c4140324104106a010000da02d0510000b00801c0a001c4240e40a0b900c56a0b1415103d410700c10b00302016090701c1000701d0705400000380c070407802603011505a003240b801b624100c01811b06666010741c01d2a8400405130b00740384a08000b002c540c4146140c25445c1c4403440003291031510300d01d18908913441070212003025800225a0400002d440c06951405050004a203079040f5003521480c4c2d0510405215408455000001642c00030b103100980d0301600c406481004108034274004c0120941c01075800c0d0f407040f852080c00068142c0300101b168810301d1a096084454040c200600900340c2200c120140340c80c0d15044030a00d0390329000035100441307801c0c1e62954050101400c00d03508548040c0c104100d00e107400c20040c00544d800c1422078200c507030300411680340440300802041c10020b042d00101290210300c010b012100c2c1d07001d060082500c55408801d40282da80e071841c03581e0340d550525072 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 995127778 1250 995126528 995126543
    0xa1406060d110109170d020609010905031608070606060c03020f1c0c080d14070f140306060d1e1a01110a0303090507090e01020d06141806010903020405040c170604 72
    0x7003900085008246466048042c140b854100d0b4403140042e000118010310b02c225640603504100d181d640c1040f055800c079012100030807940300152200c545912481e001078040d011f018010004103c441802c8609150300b0407010899144c0310480108089c1c0e510348143d00501c500c9141c0540141d001c50070120300704410f0040e29100c3c1b00d001043e1104620a0010350321801c00744800001502c540c040d0403078500d044d000000c032a150550303016050070034902122040000500304112182007680449401900c02c8070020740b030795880610423018241000ca54400e4680c3c0e44c030304103401156a00f100c0444406843d03089411100000115a00105031400c4005540049024030100780171303a00c4008058002d009039500300341c840f451007080d1070300b1884080260b9070005003017850101a200f80c01c0900a207408803005078084000080fa0040355807241c854a401c0b00002c10080e80c06003000c01c0045038060002e00861a140c2007c0d408800140302c1c002c7c020025440f01c07081440301098041c440c0c0d071b0242c030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 995129028 1250 995127778 995127799
    0x60309070314010b0d0609140708030a030b0d021c0212031e0d020405031507090b12060f01090801110301090c0c02030a06090303140903070302070602031c0e0102070f050a140606 78
    0x1107140c007100b0703014001d060039584e50043e1002d40e120210110821800b49001040043c51460642d4401840d80d082501e44d80051005000c47d40000c0f00701c44214402c0e1a011403501076034400503018840320b440c0254880c5c0748020360314040b00754156174101c1078001c913504030f00c665101e40754940302d2050300300c10f40d101c00c001003142e0520702905011f090184403e1000508150700d8070007081c0340050b03242d2030070310b803048007002c0000b4160300410312006001c50608640c00c10394050407143c20000e02404640c4600300c0d2a07202c680c540d06c60186040100b6005009220290010440c81c010703510038059501c20505012a5041050046a002c2c0801364007030001c00c441065a15660300400807401c00b2005c0503118000c107400c414a84245902600c2d0035405190341c1c030020b2402903e0301d241c980c4190255002848106000420808181e02c0a20841000710f1880000e569140c02032180060080555540444903828040d0006072004400e2240e040d0001c00502c09101995484048980950040c548903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 995130278 1250 995129028 995129033
    0xf0e030403021908010e060a05070903020a03020907020a060606110f0d02060402060304080c010f0219030507050d0207060b040203181603170f12090c18010b030c0a0513230603090703 80
    0x41903e40c0150254220002a40c0c03903016503030035502a891050301560050060000e0040540b003000c2e00704142c4e0501c0c4004d0b91031030f80400c082100d0391201078031861442d80002e80240c0240724032008241c1c0148108010b03611000c0241014040940c100980c1c410b01c88800711000002a020148002c1c1e50000c1825070b032107508010b9503500003001250900b80900109185090901905080001440d000350f101ca054030010340003100f0315100d0b030003010304110030321483c1d0390440c1c1103891008a028001d40c2c1d030407550500402a08007a5079680d0020b10000821603183d000c0c0d0b004418200c07281069584003490a030000050002602002c0c05040005a0382c407a10414100102031140b140d2000c10b081c522130300c501d4940450102d0320b1040c5030f0000100b0b00041e14100d40c2d200c0210ba60700041448950504001071094000100303000103180c0d00003034400e5620700400654101c00600c081c400d403107546941014084407151210780808562200c101a0140307411400d40f80319107841d50090417200d01c0d64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 995131528 1250 995130278 995130289
    0x4090606171614060d050c0a08061903060f09170d0e0d02190309080a030c0b070201141330030501090b031005220605060306010e090717030910030f0f0e03040302 71
    0x8000240e8004130800000c600c2c01c2060181030b200b400034003112070320380304122005460014001c00442c41100404090103070b221080c9011019681c03c003030001645401811050014030142c040903000c40c509504a0609544010040100b5050506c7c144800c1e030080c0c080c42c9d9154075641c92007002d82c01c4a580c0b103021803105074104451030300a00c0c11411550344c51030100c0c00c00061410540c0003ca20700d910405001e40f4000603504544584000c00c502c0320088558101a03601031320b40c1034000c808004035001d20a0354032003c030741d1101a4001208411070b4440019440e0000303155000440c1c10400005400c01043c40385040c1e2150240190001516030b509a03002400d00134a501c2c240b01280000d4030710190340f0a1035101b0144941070010303603410200201460054141d0100464101c0768081201000010407040c04850420340e000c962202420b5000f4114014080385580141c41d003101e40c0076041c0e040e00900c054130b041c444100417100448032883d040d9062061b00e03240d180d00030841000141400e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 995132778 1250 995131528 995131559
    0x3180d08040321020c0a030311040609060309320c1f050d0e010203070f030509010501120b04080c0321060d0210050f1606090308070c150c0e040906061716 68
    0xe802443d9600386080c079074080707800c0b211070180680d05c0020b03803004050b0035218070841d021241000f54280340c40d2590042400f0900d00a05081545500710241081400038640742e02c101110380848090003000740000c980700c42c81d1007240092103a4000e6007203600b131420008400131010b03600e0580d2420707240e005942a42c0034800d0001d240b0381d241e18000c03078140b0a202443c02603490781d80d00340f040d8400c0000141507071000b0b800841284d1410b001048083c0c0700c40d606240d15a804008815a1307990ba040001c61401061000c50540c00001000240b2918040c03084401150f00301c0b103450b16868010500008042c0003400035008416031695084090044014003200e50a0303501d05407520010b0342d04080e280c1c6418104a03101034403000d49030f08064010f1034145d03008101d403400b03034407800d0140c840c1012104200d000540c6695180d48110740c5911032540401c6881024100b48000007003803601100400c124450780d107807948005000d10120701c2c0450b0085405a5860001041c02d0910003035109005c07a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 995134028 1250 995132778 995132807
    0x90f0803060117040309150806090402100c05150a0f290d080d0c020c060a050d0504030c060509060403030c1809053c0a290a050a030803180d080403 65
    0x9078110000c3d51000e040c10701c60b120b00c1c800e0755065800752500c1490380c2ca01f9030f0310400000307001e40f213030402000d81c03138520310385911075011621171a0700c1d07d44000c141c4000300b079008041d01d41d006200a065070401d03011040c60044204035000c02030981050022001c44102d1901014002c514448820f624100d080c01b1101840c030050010b83c0f00c00866a40d108164003800c038001c030864496200404468040c8a20062000103483c0a881c0010303071000108103114010103400d1103956840810203061080d200e01e0b800030b134040c5040015081044400daa10f0004071011000241000701d040c0c0340c0c6202c1c4210900f000300740c81784079071494148104000501001071403009000780c00d40c022500007503500c00340c2819100c2000300404000b04152040c4036003030000c210b60240303030500c48101070304844c80c0e08180803075482d601225400c0c81440009200d400c0907500c515801200290b000c01171103a40303c001c60040b00d900000c0342017403034100c0742941c480034035040e22804200c2c0c210004010038000e4900040004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 995135278 1250 995134028 995134037
    0x30e0103090503090a0305150106080103051203091606020f0105010b1305060702040209100801060807020a0f0813500603130812041e05070506090a031a0415090f08030601 75
    0x4004c40c0c0071405441c01c80d070060301d10354440b2468114940e00c007201580980780c0c40c5080136040d07045407581680c3d1207400161624074100040020010803092202e030007850b000300c40b07013002d00c0e5aa0400941d202e41c0c000d5030803c69464000005081440301c001c41c2c2c204403011084500c281c0ca00010451031b23820120080c0d82107502008290311680e2212004864807005858544d02541400002003035048001c1102c803d55001b005000c012920304003d606156a01c0031a00d580e402404a0740085540d81d40d0103200e1114000710151140500c0340e84081200001d0f94101280e03199840c102200e40c04616404100b04040320800da20900385180210b5021080300d00f80510341c0316a5490782c400fa801412151603850108081c8010800840c3c078032480725900c6006003612104030f4407442d8a40140d80301e410300c60400007594403035a40314100d03400001d42d01f00141d070a10070709030070410030304040844007181d140202245907203200c119032141c540354540000e13584031310290581d1064902c1d44050300250510 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 995136528 1250 995135278 995135287
    0xe030309030a0b0f0a09050a120320030106021b0607110d0b190506031f0e070801050405030a0e012102030604060302060304060b100309021e0607080d0b03070909030e0103090503 78
    0xe44041140c9071400b441402c20443ca881e108500c041c0d240d0000e0680c0301c8a0f030421a0810100300001202e2112980015485800d2100c180341680100301084205514484003000070a001d1800c40145040341c83c036409444d4841e034044030051103021005011035124400340315078404603615121620700e80101505441c54072160f516002d80c104800c48102c1d04500109120031741d980340c58080c40760001c1003076004003901c0e00b000c00c41e5560405c600300382c6e0030b8842d0744010311200e07800c0400c0050001c0c9504002045039003403900380035449600151018004c504444c3c1c03040b680c0e510400c5e81e000c1c110a050201c20001c50102d010401a5002410340381e030190301c451021015036615001540100d110b01400599144088207201c105455918010141172600d9103900150b152000702000ea907039401800d10f60701484c1ca000170142d010348040a08595000304042014400340d50101541b11001c50407160190ba4400c80c280c1543c00861008000962403c0002e200303501a40240c2c031418401d0382582d052 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 995137778 1250 995136528 995136547
    0x6021f0213090603020a140d20041409060c0304120305070207091a0102011d0a141c1107050628140f041a03010302030303010b07030c0614010314010b030606010e0303 73
    0x1c000c400e8005080440d0388010400451903d030b540c140060412000744c06131b240c070400c0003500516100708007812100d800d0f8035104442260b03038009007440b000200200480c420240c1c2245d44031100700c03044001c1d44500004680c0300400e540c180c1e8421640f04590751140f4020300404c50280101814140c1076228081c030101e0514414058802d0015440c400d043e0f03043e41d820002829150b090003503c040c0341420356138011b818408550441c40d6604103002e6005c119002000500e440002c848131441300507140302c580180da40c4000c0c1445046181070440d8803040d100c0c0d04002892044285440e00315006406d50f0302401468100c00200c440c5038140303d05102111504c24941e0760058100c1070700713024009010310155640105401100d02400b030100d05540c10f56022990b01e21040c020351041c043c0c0820325404240c810f00d0480b5030700da80064103215215290710247c160b11802e000484510042c0b290600f400c410509c590314202e11300174001d1010b51103d10040d50b80c5924a5600da40600041000554 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 995139028 1250 995137778 995137807
    0x1206060d0e15090d11100e1011040509091917130308040f0b040b030105010c02060d0608060402100302071101050a0c140d020c0d050d0e130903171006021f02 69
    0x400700d0300100381020f02d0300e411114140000f040d5058288030b00005440100310700012044910042000300280b407086240000d0b00e007102d8030190201507400e000020021500000180c401c440b010380d01c04c00c1e5a00c6808585885942d20450b03500148801d0704080045000341040e8100e0002c1003011510340505e8000300d11850b50142c00130381d6040c00026041041d0708002250078014007204003802e08060412000c41803a11061042c0ea0400501c0034689065594290803201801504841044126a107513561601d41c0da0455069120701e00b0f072a0712401141c080d000b01c0e858244d0080419002c5150840103644c0c60700284818020010500711150001d03845812040c51000080c0061210b51031040e00249401500060140564501c0b845100022400200141d94208a05141181d00c0300340e0b020403801054203035441e181504120012003890f070010b8050002651001980d00c5a6071401042d401c296014880c400050703224440c80e5400c06043c04441420300315410000d171078018036070034551 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 995140278 1250 995139028 995139043
    0x803130c0e160921080904271104020c030d09033605180708070212031302191214010209090408040806160c030c060b06031306060b1206060d0e 63
    0x74525441c41403244030242e000f801c02c0300203007101303401800341c41009076018040d040040402001c03040085406059036580e030700003450501d062400141504109140507450a0041c501511500c10f40c49180c105410f140c02180c8a18110f0001503240c00c9a80d40d030310008203500c05c0c040e41000b500d404440b50b0000000c40e2041144108003c026a1180c20003035006416610340c0403522600300074100c10454030100f10415071104150502d86043d81c0d134810182e003000220039801d5000c0e4000010800e00c60792508032000c4450081d90300e540c0c00c4201a07000c0400d10618016603003502001098400060f210b02da4219900c0074400002d402c028102002c1825510191000c03205990041001e00809004100c035a91013000301d2440d507004010454081c04058000102508000541c580d1100740b0049070040c40e29150003500c0c0b42d940c0c0c900301c146011001c103855821607400b8242000020f8406484080da1101485201004030a49171030342000380550205009601c5940c0711800d40c2041c010621000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 995141528 1250 995140278 995140291
    0x1003080c0706030f090b0103301e021f2705060603060c09011b050109050706031b0203035b050d0c27020f040501090608040803130c0e 59
    0x4101d02810030320094103403202414400011407424241d80d0208001000a0341100c2e0440010860710040c920380004081404d107505581110901d07100d11069888641002d1083c082c14520142c040b0741c03442242c40d0750110001901140304076020004144184e07004521000c06030381e0417900b0504542e84030952201e01041074030325030046002c0015034101400304a82c45030308401054038044103080007070007820b0400070302c03d000442c0809640c1045001d50001c001a50000101c4d4551555000010041c1c0740300000f11101d80c000120300300303410f4000000d4a0050b0050941d150007117070085180c691750031710800c010200000c0c810002140800b0051090b02844946110207140a075903550dc013114482513010034000e82074554100c0206603150400c909440d405802c00c1030440400c4203005099548004061300c2520019100300b00f02d0142c4010021600281ca03054515039071544140ca4049045602170801c400400001d404200050700c805090352203188100d4a103901d80481d00c8800400f104da0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 995142778 1250 995141528 995141533
    0x50c13090f0507210c21200408150403021915060f060c201917010b0d06090303020d060611012f09030a050604050a1103010c171003080c 60
    0x2038034641c980d001d026406035160405034040851501c03405907903076205943c0b28a941e643c1c82c8407400d07548504422001c0c1781440400d0f00e8042e0308251100010b08100107403085044c42040c1c052407040090064404807201c040c064844a445e00b5248621548000c1007241107006d0101c400d500b200c40c100b445081540900b4180009140c003200a1040350404e801001076080d000f0030400110303601800050000b5400244204030007110340181d083c60b2000d40e5000d9021500a5441c032506105402500485198800d0001c420104d45030041c01c80b10710b280709580009907529550301040c2c540d00b105169902c0f901d0010700d00604a006201104c520307411000002d600b000b40054944401d010744140c6070b024102e102038000c40c00704e00841109101e402c840790083c0106412409650905c0a081419040010369002d8a0301c0e00c6d00640b1681e180204403101160305003110120b0a051290b0b003010312003511946024100102a4011100d00134181050300112030300110002c1c910380060901c40c10712500 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 995143884 1106 995142778 995142791
    0x709050103330e0c0a080a052205120f091002060106080a0b0d02130e0f0d051c1d0d09080105060f0d081b070302040506010206090709050c1309 63
    0x809052460741d0000c004110010034005d105030b40f100d40c1c4881c16961012041800c8482c152401d90b04100322191550303101c062441e010f01064040e42c1261421000001510000d030300485101c40b01c0300e07010401c0d17401800d01400c40182040705001070b198542c1003140042c540b001c0182949401c84e165000304050740c03560070110b01d8103900a002d500741002d907041030038060300502c03da0030560700c520300004100d24004100b41d1504aa950b07500703407906882e1505852403080c103482d102c4516550302c03c0216a18001140ca815401182025090034048080042d04000e220740c810000369040004111030399441130404410000102c4200406641e1400c003031885000d00c020601900e03843c0003c6e694110303c0022401c080300e200322428007181d40c2e107a004907103880b4241c480c80d4040e031101105104820150700015448501d501040341400c03103030040d000b60f0701d400b6442690200d41d00c1e030 = true := by decide +kernel

theorem cover : BRFrame.Cov 994964028 995143884 := by
  have h0 := BRFrame.cov_init 994964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 994964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 994964028 ≤ n) (h2 : n < 995143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
