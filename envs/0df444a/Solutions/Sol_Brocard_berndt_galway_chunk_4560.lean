-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4560
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:00:57.721123+00:00
-- url     : https://prove2.me/submissions/c7b2697a-b9f4-440d-97b2-e5058ed69475

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 819964028 ≤ n < 820143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 819965278 1250 819964028 819964051
    0xb03070b09040b040209040c230702010c02091e0c0a18030507030311070509010b09040c1d040c09051002030a090605070b0105120a060903080603011a0901030b072d090905040506 78
    0x815030303c0481d003e07105541c0359540c030901e00030030401016080110807118280c000e06860000300012240c0d441481000b0b40a40401c40c8004100d0040c83c00580d001c4d0312000500884260144190460270049001e803002c48070904013040d4111750365442030084148603182502c440155185840e0a40c40310104e000280c100525660718408178034040042d00003c2101910721019580c1d191080c2c1169008411b10710b01c10303400d003130340343c0300c0700f440385059018102040300f0503094887c2d26020000101002460745007800005840028a1796501c4420010800c580d0042c0d5915140244010590fa90903048441072160610503000807075495140c41d415540c0943e4400b000c51a120720080ca00340159000404580c1801c2096040540c001c1d40c071402080c00b5802484002e000384070120368484d1440303030540c2004000004002040f601d4036620f8100c01c060414154030780b1139040800f4080044c004403610305400380902044c03203a001007c4001090038030820040c6040079980c1075115036010f040c0341e940c0c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 819966528 1250 819965278 819965291
    0x11b03140c0306181609090920030c0d0b1807081911090a06080706020703020d121e02070e0a0507051c060b13090e0102070308071b06060311040b03070b0904 69
    0x6444120302d000c0214505400800241780c0304910615220b0114070200018144010000f81482c40d406a440c205078008400b00000140c0d00314000400031340c0701c480d03505100c0e400203590b0075120000d54100e0540200c85081440c0360041c103a00c5117a0580d0014003095000304410002d00c4004504007211201c1140340f5004d109050070300f012076200d507560380350b80058004c05111218502d580104202c4d2443c0040c0d403181c0e0b9a901e020381e11180b80b440040d400842d0048580000f074084803007201b5140710741c1400540b5440684006402c100303000b03106d10140c0d00c0028280030fa0b19608409603405500c01c82d0602141c0340c0000010850b000748404004400313200c81d0740840c80c200d0354000c01c000d00b004010b116140c1c208442c0207110300d501e40c81211041c0b031400400d00304c0400180202d491071034054440e60016200d4000803074500da008910000088035640d401400641d04d809850001d501445611809114202c100401c40d400c80512611a911129081143c059080300707482000c07008880c00200c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 819967778 1250 819966528 819966541
    0x6090f060117091b060c100207051504030c05071a071b050909070314030906030c070f080f0406110c030721020d03180906031104050c1209011b03140c03 67
    0x1544802030180c0e40c81c030007400c03c20403480780000f040c141c01e400c50260122080000d0342800124403072186400199005031280c078605c0385a9400500d406c81c0304200b01c84101128040303002844900f51401c4000403080d0380fa040500200b000b419001e0800d02c101140340000340315170791b9018452010020b03c0c0e0260200c00c03520a509100c628070051501810301c84c81761130120646074036444603000403a407151110b050489100070000540700c0d442806050249140c481e02c6078005141c03c08102190380c00c241c0c10b0400f000038124005000f040862446840d103417410300d40040d00785210030560020325408001010f48a0360001015000c880c0012081c0c09284505501d01c80030b440030b124042d400558107036008081681c041016071b4404880400201043e85807000384003916450311001d088564802c180140d54038280e030090381c0004e0310380340f890700d03081d0420084680040212105005655200d907018500d20348525a407921000501d020000206a07a9402c00e42400140042c2044180480011403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 819969028 1250 819967778 819967787
    0x906010306050403110d020d1d1003020f0d0212240d03030203130503070c031a1603180609110a060e0109140109230109090c0806101b03031407050306090f0601 70
    0x203541c81c1c41006d45420818416019640700f0348080380400003448128a0241210b20903841c2c01c0f803200042070440004801c3c0340c11406500020002c4821444c1009001780f807081c1c40c4002d11000e2a040d00c5003051307140c812154150f070446040880380013840002040002c1d9214034509071555410300b001601e9071240400c4001030441c01c40010400d202c00100c030700600a40e14441021a44181d00e60b5108a0b80d038919030030554419243c201869491820030041d86000703400070111050b1214000034039106680703981d01600c05050b02658040d91424100c0d070301d4100354840c60080e14903400c111000642e44c60000340340c3d0006210304654048010410811a8401c0d1002402455600103036800140d100000c0d852200b680380c0e020b4080b641c1c1003070000b158006801500c0500d112901c40d0500c40d5900c00a024100c404120104100b150607000d260000c4080449946124040e44e8000740f40598440300b1031030ba00c0047c1c09041400710600c10007045990341010b41758858a00c07002610306884903070058a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 819970278 1250 819969028 819969047
    0xc0a0e190f0f090209060f0d03030e0c091609090b06041703070204020a051201080a02220b04060b07060b06190f0c06020a1d09270f011506080f0906010306050403 71
    0xc000e1420a0004900b01002e6001408028021079882855403620000c100700e080e2081d41090b000401c00d0500070109009071300c02ea07041619402590008034220001621030301c0d0488565440d01000706400c58500d42c407500200190401d800c1c100303c005080d100251241c010741c0300d600102e141810782d16010030824015510007070380c0503000355100c1751003900141441d0032030102c800720f41c841c0a0000945180009407861035940291801d4030b034040008802c01c06c42881c0403611022034403a11a012161240d01c04c940c0200284c9001c9600c2d00900d1904100356804840000d20420041c80001141d9254203801d0100710b0715400d00c0484912050800d4510120141001c2e040600c0072814114080c0c00181240b5a5462071000320070b0f800180781000401002507400c0018009544a4000d04050002ca00c0c1c922808000c101c44070030101511660944010714185403141811280c2001069000202c0d250000100ea40885092410101c081e80e6044144009010980c803040450300385400748203001e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 819971528 1250 819970278 819970301
    0x2a1f14041a1506030a050a0e2e060f1e0308030c04060e0628050405040e01150b040e060103020706020910020a03020c010c0b0114040615110c0a0e19 65
    0x151946014100700d04001040140d807940c1e40c1c000d00000380030041c1c00300403604160006140d142540c9800981600520005117511801c541c0c610351002c0f108401c01445214100c040062042d0840810381c450300c4409100310846d01c6414104140704202001c07101a0039596120700c07940b800d0012182100b440c40741a880641000e900200340500548004000e1099a006803640d40d41c46a8590a0107603074803511a50046054080d4200700291500c440b105201d07041c0307854524102511071000030125416803601d0b0200e69900c894034003841b0209680c0070700030820400d500e410240b800032400c0000000820b074604042d800200e84040102c240c0c1964481c400242039101c61520440b0003030358071403150105a02501c01e840808a0a40c801c00e403002503254000d0000600303901c2c0c2514448032090424403554020744131000410540e038290300502500f04955503941010104505460400c1940e1210030701400e034181081c02440c5ca440c070402d030848000f18102c1a401d8030011040018803001228 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 819972778 1250 819971528 819971561
    0x9011503061806050414070519020f0d031b0e03070611010609020a0c0501050117070b0309250e07020a1707050a0204020d0605040b0415030305031305122a1f 69
    0x152000b10307007039400300003038a03820342d800c0084a20085103090b420900700d9441c80001c01c01c01100d10890076505205503030704a24011204d031001c511002c5820042400281400641c0d545841065086070340f912500c901c02324105112090030f61004240c45a50074044c000600003030900018421109502000080c103111804540799922800010101d0102a00c141d9983d0b092200100b4103101d84109180350510b140000c0c2102864a600005203410040c0030007064000c1c0001144950071010380300401242d080c000260283c04c0c50913a204003031024224034215808100351a00044c0c00b2810001400d000d402069114070700d910b0450718107a0190f4009400c14004a0081005d00c11500245e041e10011541480a009a00140000c46a5075180e0030903806c03903000104042800f56005540150031070445a00c0c0070b00c581c6031a894002c98900b11460003000040b820fa03224190904c07200d480d100d14800862a0882d0410180c0e69984e613a070480034040c40d0306042c641d544156200810820041c0344 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 819974028 1250 819972778 819972809
    0xd0302070c09050c1b071521290103060e0903070b01060f02061321121805060106080601050708030f0117190201080a020c0f01051608070f0e0409050303042f0901150306 74
    0x1002344450100840c880c0789038070950307141c3e208403981e0041c40642c1c140c054442c4a11160040c8400c8040c0c00351a1140c18503603546004160900c49041c400d12030a0404029582d510302403030074811800c4140e018030100400a041030409a0740810120340101a40c1400452030000b400c140a40303103080d01181207250508030798918441d80003803c0018141d6900303410000f100c0095207031100c01d941040014004c2d0025001406000c4c0600301c01908100b041c036109003069104e82d00c6003507940c000e881c400d01140380100104503c080c43c50f01440401034202c0648034402c0c83e001200389500030740340300a050004a60020f012004036030f05464105c0e84e031030100c0320681800c07200c2c20300034a4107480c0348483d080001081d024a074042d8030054003403901951145085042d40380100e030362001988026502a8907030b038402010541c1000618000c07402450448010030003000d580c00b50442021341c1c44041a01c00401450704d580d01d014490440e82c140c8100c0052005c045001c41c018074903500086802d000030103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 819975278 1250 819974028 819974069
    0xc0304062c160807050108042003100920030c09070302270321040608070e1203090f040e0d030e030c0613060f02030115120e0d0302070c09050c1b07 65
    0x3502d02c916152091150100984508840d0380701c600b5402041d0115107400301140014056100032001440050002c1140084000020f4182400786450151403912914000c05100704800114030301040c0400c0280a4410140403d45845080301c101c0d1040c0450b50000b140315021340c0450385042c00c0032500c0110106031841c00885001a104414003a10501c1d0119060001e1503000280040004242c14109441d003101203c0264006048404000042c880803074913840e098101d0480203110382c0510f03203903070407181800034084401105030b1180e4140702c0500350f00341000c60043c16441039850007264425070300d0015450740c4181810401c3d54400c0404010741400140d41004d031141c8205014084810f9003100403040e4002030140c408044504820a0780c02c0d1f01440b00003e40405000000ca00c511302c4030b00c16800d10221b03040180c046070300080d18404001c03805058802400724544204241d080080505d071450044d070b030742c1c400c004203c281170003030300c410400030301e4000e18000d801000b1000b10070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 819976528 1250 819975278 819975283
    0xf060c051e011e0b0603040b0705041d180106031115130603050108060c070506010e06030a0c060f020d2105090f030304030e0a050d350f04031a0c0304062c 68
    0x442043c50303210b48020782007030141060301907000886401410b0340c0c25510340b91900c00b4103880141c00c603c2400400c110015081c007001c105540c0300048a4406d40d41441c002c1d4080a21124942d10048a6403400009000240340c0c5801a02c0c0d330345060301c07041c1410b40d181e2003a000501c030b518a508868094030900007803103941b5400c21810b81c1c0002084d01c0f616201c442c8041c0c9640211071001309203400140050000072500071501e54003441c001c0840300a41501c0e21545048030b4150498000614a0102c540304d8035010804825038114918102400c1599180c66054608866001c80c100f2a200c4005c50f00c901d40070480d91074042401c0e01035075134074242441c0180000c1204a0b4281c05250030b01d000090314603214841000058019002c005031a54120403404900c0341e194444200180c0650302c0c0342c54060700c0e8080d00c00c51101e454065681c5055081c0b800240c1c0360041140d0328404c0b00c1e010804201940340690b034209902c01004540103a0b154506c80500c10810351a90340704d1102d038030100c11040300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 819977778 1250 819976528 819976541
    0x203070207050904050d08040f02060a0306060207080a1e0302070f0b0d0b060901170c16050a06050a0209100c03020709141005010207140f040b0306040b150a0f060c051e01 75
    0xa6000c552246581e203042c000c00c414100c40180407078000f45000031400c1d000340e24a590040c8250102c54144c2042d60000b01c99822141031000001e03610f19080c0174a6404120f014042c01600c001040c0c0112190740348040004a007400da88510380e070b0072210003014020030803c409820410003603143c4030340700d100300d1070749402a0703604007000c0d4184400c21419041c4402103070005034043e984c1c0da01c6003200120a0806400262020032142810482c1c0003aa0b00c000c6000d244240c460006800100520f0030108140d90b4060902c40d031091041003100c0301e40d80d4a6500882100840c10404d15681403170406904056031075001004c480e0400903c0000e2045c0c1d449400e11a4080c23110030400551034800480c3d42d0003039400780045185094a0000780d51900c00c20f4048480300c000d0000c02c801c090740d000300f4109201034400300ea040c0b04100038066500302160780e110072504251009008a89401d10303c14540609215403010b01282d102d03041c06024007484010b07168000280b003813803440701ea01c880a009058 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 819979028 1250 819977778 819977791
    0xd08070b011d1005010e010509010c051c02061f030f05100203011202120a0b1b040302030f0d09060c0c121115090111070344091503090a260c010203 65
    0x2c0010025121003151070300c1000359101a951007842c50480d01c01900d83d58040d02c03000381801041c101c1d44001070701c108000c014140c0b8600c00003142100c0744102a10b0428040c1100302ca00820b5007121081000c20301b030300c40403030b0782121223025a40b19600301203061080c0c007120307000500e00001c008542144000045207400d4820354466031600101001d080d01c03140c1071000101402420004580c1d0940024507001148200c3c0c602145000c2d41c9500080ca0242540d49040741608802d44400255801c0303100240200300038240f0312203400300c0e692061910101c501030000c01d154003001400511990001014075000040c0140000c1500407980b041e064114101e0355002610003007042e4203401001c2260021613a0024121907402c4c40480c06605980600c054032801c003208000000c255a28264842c600c002000141030ba9444000b0602c1840004113240340d8000d5001c205000c00e8150001e5440041908260f1000e10b501300c0d502c4d10700d078100500c0e0a40c20700c0340022910140c4524198025409500d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 819980278 1250 819979028 819979079
    0x110106032108042102100f06051513030f0602040503160302280308070f05070b0c16050d0201270e0108010609090312050709030b09060405060f150d08070b01 69
    0x105925401c50b005042100d0042c414105020300c0041800500c007411140821401507485004210f5203101c101c1c6c8201154982c603a4850701d04006604100b04040403160114540503c0c00c02500c42e04c19602949100c0142401c904203070090502044c0d606490140100a00380c95620100d00e900500541981c081a4800c507040701444000d00601c0344402c0c95a6071343d00b012960140381d620340e440b46401680e82624602d661200704800540d060280c1e00107861101d030250745503600c1c18269450f0010300c1c510750200d0110306006100640d0703010540d084460382441e0054500442c1c0d51900441414101000310320a50207401056801d4900f40c410b040c0c525240003044099074a12a400560b55040c04c050b02151101d0150420100290401d5038498640e082ca000b01d20f6072640d4428450030225413030a80d0f5000003091004116040c40401c1d04070141a0408d0040d0801d000707220b031500c3d00c4040781ca100b41e01d9940400c08101c1980c043c0c0780b905400c500b0904582da500c5c0c0340442c0c3c01c41030960071281d80 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 819981528 1250 819980278 819980333
    0x40f03080a020331080a0503011a0315130605121b03060103081611131a2e03060b0a0e18090607050d09060c2318010f11010603 56
    0x1c0c003180c4252441040c02051015003040340412201e104019040d038816240140b04900f00400c444400400c468075003507907004e0f81ca42c505107100001a24011020386100b0081007844002c400d14185603900d0340c4204c17000c1c10802e03503481c500c400074000380e440319800449003044140a400701284001001100300c1c3c1180310700301c4060400d1b0711030ba000d02004054010a01601003540001c461082441c3d10800001c4400750824002555004070303100380052040c2c07104c48242d000d80300c0c0a002001428203440d00001165418402644403c4012044100c9020741c040c00c0403541c07090b00000c00801039001116039600141c0c1c4000c1060703c00c5a1f03524000d8158064004010804080480c0710300d81100140c600c50304e41000854072640800e501215182c0c9aa03070719408101640308039403800015454040d84001140d440c403406850388e503c040444802440081002e000003402c0b0b03904070a007460b1120b0301d2118500265041091050340072095881e024020040020300e0946146103035102d01001d504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 819982778 1250 819981528 819981541
    0x7110109030f090e1308071a2508060109170a0c031b060507080a200d020a0b0702010b060d0c0512010314070b21040c051801090e07060c1b0b03040f0308 67
    0x121205035999401d45c4040400800842c2c00705001e006040e1040c8200484164203c422002101c0c056a4164074a60708815460341c5e02c1138040c0c20000d00b41d040c105201c02c0d107000f03800a84180d106105803103200c540d01c607508035810414040110b44903803180b108001183ca9041030401302c5001c580303918400401100101d9031600440c142c450050b0b0001d0341c1c6141032001c035401c81c0c80c01a4124440e1610009481c60500810b05010079050101b103540181940f40403820840c80702c280142052040d640f4111000146444100444854490b00384003c59614007961781100e8901c1207015004c5007420b46000407040000303032190310581c00080c40886a50b541c40b0000100386107e00e2030f150340d1000f0600f16a0620324511001260320500500e491540e2f507030b036100400c41000ca60072564451450800051184100b03520034452280d0b5000c000344061420808050440000b02c8405441140d401080c207000c4c030041c40700c0401034817045400c5626401e061410f1007032050710b29000c030045503040001a28 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 819984028 1250 819982778 819982799
    0x5210c1501030507120213050109050907060f2309060406021b0406060e040902010306181d060f04170c100501031a04020310020d09140c010f03200307110109030f09 72
    0x141ca0704000a031030400c0c58001114030011191401b280c10002c400f40c0c0300032101042c41514002c1020f2200031401d403074101e0360282003c50b43e17009402845800344860000d00c1d03100c42500300400041c0c40e00c640360140e0f006080441d00810510aa0120000401044040e80070483c030f003d13a41c0003c481020412030008000603140c20b40901400688403049003402407405401401910b80103040c001a400d4903284444c401ca4054007480400c1c0d51100700c072010445482c82d4001d22044041c019100d682040c3d10255052071000d040600040d905442514820100c00300701ca0040ca400001c42d50303100a94400345014100c00d100c10f50300382604000c07043d004a0944038580c4150b82c003c010f4000c1c080d021344400001c3d04046006281c65545200900000c2d00c008040008001d002c0010040640c07100b0005040c55002c40d8444101801c203508045034001640c0300740c03400e5107100c40e10394a03690342c0b10b0221000030b46940146000c1d82000c2010042c55080110b01241030095540c03900030f6625001c0c41e10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 819985278 1250 819984028 819984031
    0xc08060a020414130e010f1b02030304080304063c0c020f0c04050a06182c0a030813150c1d090a02211005010806090702150405210c15 59
    0x5401894443c1c180019250040030f0400c4141c030b0800c0040d0701c840b201485400c485509411040304e5548040c842000a211361415295612a00c01140b8626041c0c2e59112903000c003410040000c2c0d103841c8000c4802c40103c2ca182c80700310b1840d1a0740e1107840260f207029400c0c040300d540f401e02c0514007485d240f003680c400f040440c0134000c0480203000520781d49003440001c00009200d448499914400440c0224189103011081c1c25011404902d0101c0c881e080d0b050340003045032007640b200301580c1c01410a1340106d258407281d9054100741007583d6603010b04140e41400004014260554100c04504c0690b84d50300c982408142c0d603980c8030801c1040c04004803414906241f05600c5600c84000030036100454004110800c03c0504105107508035000c203458400382500d0080c40014904424003407560310401c0540c0c000710460319041d403410403c6019490300d5003440c03000d0702060100d0024007446001c00c80c00321130500002c0014841004442403414640028a0461a074098545100340f410060200c0a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 819986528 1250 819985278 819985289
    0xa020f010311030f09031b0f0705010e010804170f0a050315010807020a2a081f0504021804030311041508010f0812160c0e06120703230a050a0c08060a0204 68
    0x191441c2c8942481d1359002c1001000c00c90544030030001804d035442ca210801c80001c80c080028031214868031307005414000e82d508a141004202d0a201300306aa205107001d40081d0845801120000501c540087c2c0740300c2d050560b5080840054601140c40c2d208000314400c000c00121302c001d60a0a000440300010180d84690041c3d000e0046030000c40e40c900070711503c0700091800d00342203513076414404603900d005501c50b0240ea003041c52948022110011001c4c0509048030040000b854550300003001c1a0b05042e503030481300000c100050801d80a80d021411081504155986440d541c070890b08414002d001d819000844213400016411040a107040540c2c1100c4040e00c0351020fa202240903a07007004504404070041d0440d500003042c1c0d0041d42c030380034041c00555002c03546800400c3c480211180140c04009502100003080071410510904031103115021045c102c902031404654a4844d4628015005005002c400c10030880c151254200f180c01f014180d5899680d50f109000c224021413080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 819987778 1250 819986528 819986561
    0x5030403020a032009070827060a020307080906070c0807151a15030f01092f120c160305030a020c030c010203060405060a1406030c1c05040611090a05060c0a12020a020f0103 76
    0x2080072401060342004200046003c07074075001c06850300b424039103040ad44515070600da001080c0100c95a001e22555170024040004107424108900001c001280b0900f000d07050700808240d44c020401550108540d001e6030801c1031182a100c442c00d000910344c0c0c0d845651044811041840007420000700b40c9216141800c1e41c03a4490f0705e02101007020b1700c10080f1008080d56490040000c10020107030700b20a20310b80c400e40644a034149004a074003224080d11040da100303024403040303442d01c00c0c1c2ca041c1c004103079040c13a0180e200d8448540400c00380c0a55800804107002c04181e81c04114070545c055071041c00120340034001900c4103c180820000d0380e019482a031040303800d591050b41004002160855240101c0b5494400c0e402d01e0084080040f1a2500e00f0a803160180010b1250501880c806008030100b1140f41044101c0066004907c5100f054020040480da84072158800e101d8003a20035004001d0610030b05085500944401c00d000080f84034071044400415036510a100d003582030703c0301c50741 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 819989028 1250 819987778 819987781
    0x7030c180b19020708030a05180a050d030f050904020705010b04140f010303050a0c06050a0e07170c090405030d0e0a0b010e0f0c0c1608031c0c0f0c05030403020a0320090708 76
    0xc01d440c00d803042c05000c1503124110002038501020001007070052000e6444a480301c181c0211411400010f9042070303c1400c04450070721495890307116003094a0342c9400c1903050104003050684440c0540004e0390b82c414030106aa00034010190000000003400f12000c000c60200502c41509240d4103a524000313007240392005000003400745008100420301814104036011440d640d850070f8400c21643c00403425250b20441d40da00100300690b9000d031140d0300c80310701c0306004108010740d2000b646016038400c841c184080307014484144210b071040f500300341c4144510103140f58000c1d910303c00401d0880f010040800000342600b8018403e42c02040a00d4603242e45488000c59800142c2003200703000b07114001c5070125001c4841c012407000003410b042004c0d40c0c031000c141e940d0500000d182c0c0040382e0402c2c10001d43c0f1020030340c040710768017800c4081e0030412840c0403e820f00d0b9246001d160802904128640804014003808000110f00b0001c007410440107841c18200780650302405803200c9010034544e60 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 819990278 1250 819989028 819989047
    0xe0d022b210c2409060207020405071e1b080a0206070f090e0106030c11100b0f011e210c0302030a110a02150618010902070b0f040c03170405040507030c180b 69
    0x4403d40050912422561140d40d512850441250b10310030040340e850754009460b00440c1890702805a000d19103040201d000c40c56a403003a07213081d401d401640b040084400b60040b520240c1841c002c01590400e00540e00c48440c80c50113981d441c81070361428085001070b90344000c880c1c45068540701b40c50b150312010602d41d1030000154007401c1d0380d0640c0c42c24011101541500c0c00c41c100b22100c1c2080c0101d03000714140010320184516580c04041080c1006442d400418011203178400c8041060b5440c94603200035a91131501007a0701b1f0142001c089502e0800100075171840e0b0517000ba6000b0603400f0020809044804001d030000d2041074031140158202d0f40f200421005184500ca0f0f02c00d50140050300c1070036440041e000101d60980100c400e2940c046100270a00203441b04581c1d02050410115100b0b0406881d0001c500e0142d11000f085551083c404000b008040820368002708070140060127603060070900a0083d10000c103101c0d0016840380020303440c8440c40c00e180006c42d010010b26500c0d042045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 819991528 1250 819990278 819990293
    0x30301150e01030b031b0a05040209030318190f060212031509060f0a090609060b071502030702010b0d1103120414060706060302031501030c0b0a0e0d022b210c 70
    0x7203a0032414180d03228102034180d24244080c2c48030742c0c010401c1c004010a00030400540403003980041c2c0c0a40c1c8140048003058800004460f03800c410b0110642c43c11500d080018001400304010640b0103c01040000d4030150031010042560200d400361098641c100e0500085800100d881540c6644d041440d4007103418107410761034200b40701600792001c0c0c110080205410810941c031581205a603883c040140b01a5032140b08054800007000e00e191492135107503680441d1000c0c500905071640040800c42082c000d5009000f00d0601504101e26001241010025a08003410040c000e001d545940000d8001c040116015901682000c48000a02c1402d0202a800049045600a50701c62000c405079804110f08030710f4542152556800707604525103660701d0030a035840f034101e188040c402c1550694200740402205501a40e02071020240c5000240e00548e41c51803114201c503d00030318294405068810f04420350245a070240c1200814819506610700e03400484001030841003580000b9000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 819992778 1250 819991528 819991547
    0xd0506060f0306042a0513140303041e030501140601030b18070e040f0509060601091e0909050109210f09050f10091a040614070b0c03060d0803091b0303030115 70
    0x415110217a04d103210340c1115446404242d000c00495004580d80c49442130200c00c4001900154007004100789501000c40e0340c90103540242c48080712201040070080501003004001190040002c0c411441c08140700700c01210180e51090000e070412502101500b0a886490002070801e8010b4200395200c500843e144850240d9542d8019150400f10201c8070b454001c50f4050091800030348207030b05002c0e002400e40e00065028000300140018003140c44482d80900340d0445180c0c075030218030074540f494a1070040154640050190301030f072441e40c08800009030f030324100c008a40c40c1d002d100c801486082d20b03140050301c119070303000400e45110011802c209032a00345410345030074001e07201629070650000d2000780c9007180b5140f10b00801e04004039940110400344078850950002d02d80040f03501c840c03a50b844010051054010008003040c06915440300b940c0b0b1041c0c22079080d544a05112034180d80300e5843c1c1640000d03181c0000c02080c01450f000c400c40e0304076421003044036a504400071003903d00424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 819994028 1250 819992778 819992801
    0xb0109020c0f0604110907180b1c020a0f090909051011041d06010f1409150405060a03020405040b01050a050d050a1803020f0f0d0e060c0a020d05030d0506060f030604 73
    0x81d0840c482c0781080100400340c02603110b40e001000b801110010711015410041880e810483d00e9103a50601c00d684020b039000380c0d0400007041d6510200404c20b035406031132403000fa045181c03000039682000303544444544900c400c96500c5400b1265100d0001080d01e41c05000a003d0f50030000b04010f07022200ea00c00d000e04180d1b50103072410250f0300e06103552109440c220b2002c40003d04000c02016603488449200c15114130304008009424084031200a40199561640a0f0480d00c1c610320b088000001514000c1a0081045a445829080060203034119210304e6004509142d00205158080c1c415900c141c3d2042d91000d045c04e4107400700310007034400688552a0f442d503d00001e00c012140d00070b40d90103140243c00800d000604404080d1503c680c4c0444c092103904481c0581c00119031140b4580d070f484a044a58640728000c0340144e40c100220945e000350b0100904000100300074000c40070300505804280b00308480d42d28a800e000680c45200e00952590808000194003454140d004140701e90 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 819995278 1250 819994028 819994033
    0xa030203062107060f082202030717010c120b030c091005100f0809070b1603140712080c3f390a03051b07030503040b010605070b0109020c 61
    0xc820901070707000d003020b25a801546402ca08814400a40c006100c102841c0052030300c41c3e190f1500030b10034081c01b49207060b41400042182c0494084d543c2c10803180d070103400741c414803a203903150b20301031a0b00034600c0d0540c1b6004110501500200a0100c0c400c40c9403002002e0040c0c10900d411100300032007440001c0c80b0824100c0e0212011641d52a40d031825a04038896071100325051400040290038680010b01000c900ea018520903c4640c4120003500c4280130b41842c403403521589450180c0c0c8144400310700d1032000402080c40000d201d11a09244415010b5889080940c7c43d4400880810721a0700c140c680700e888030552410482c112100c00c1c6154162140005102d08107105072070086180542d0304c0e07a030b50b0914401d05008661721400141c0c040e60000c00002c0d40c1d000e4010340c1410703401010f1001e0145507680b00020a45c007960020b80381030381241000b031a0389812514024120381c000707440568070191007070b00224442d0f00660844500f6030b00205001c80680ca403031b445001950010002c0550ba0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 819996528 1250 819995278 819995299
    0x10e01050d1401050f100e06030a111201090813060203030f0c07060204081f0501211103010915020706050609061e010e130624091a19030b03010b04110a03020306 71
    0x11804e200d00e0780a00701140351410281841a0301114403411a045040c0d22804102440b003140d07000a41040c1541e44890600c8802c490640083d00701c07050004500803650a0552a00c200441c6100410290120401410a00e07480d07941c12039a80c0002c64002c5052112080410b050352500000380072094803414000d841d264640f41c0907420540020a19808003c41e0700e000c1d400c41b0454020680940b03a83c4803041c0500c1c280603003804a030102e01d41c1c09000c81013030303594003811614290400700e101900715500b88186510707030400c00025400040c042da4014500004610700d894402d203560f000f1400100244601c803031012143c81c00e0560310708600e041c480c600181c0c10094807134a101d40b00355014000b0014551f46005175007212002190705004881407070304107042105401800c0340040c0c4404498299900ea441e46214082d40305410030300c820140250b80c46a00c0560640242c00845810350082c4104d03550501800191805c0c3d050030004480148072800c03031148a54007460b40020000c00c220b240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 819997778 1250 819996528 819996563
    0x70c03031b0602040e07020d02010c0e0114070f1a0907030305070209100509150312091809010e190201021506011d130f05010f0f0315090203100c091502010203010e01050d 75
    0x8136800b5601ca0f080d0300c40513030f0070006095018408100101c51600090290340c4ca200c800030600d0a02401d13450510910010a20b039000c180c09c01d40d00c0383c6501c412096580b00490074040103800c501d1089001c2c0c04c4140f0005030700c02d01c020410b2002c80364552507903810700d00f0741d50030000d100340d008011120886e001c0130300013255600e041c00030b4014400014226001c2c0d41e4642031604015090300c0d4030490200412400c0450384a010440f05440310200c503913506600c845c5074244c05050302106450507413145030a400800b448501e030103420306200360201e400c0b00f00b00034064446600b040380c1a81c04646a80c0e0306a103845400c0b9003020161030021701c0200c07411419130400d422280410007200c0e510350f40d00300500c5a043d01e5a164009800c40005401c002860f50b980e0200b181c0450701a01d1486403509082401c5441c10010301100700d803003800034800c907400304000421042e030900c14404291000000e1101c540c2c018801c40b81a5007030a01000d610fa8200001d00543c40c040306c0c01115504465141c4610 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 819999028 1250 819997778 819997781
    0x806040b0d150e0723060d0c05120f061e01030b0303070506040c0b130b160f1103060c13030f020f150405010816080708070e030a05100e0102070c03031b06 68
    0x805a01c035540c40b82c04025080c20807400c66001d8000c0500070380c452102800306007001c0101d0020000e50702d40b400390025036000030a90745e00844d0314569a8034202440c0c0c24034a50000083c0202403074000030134034156500c1c0c1003101801019a031040d0001105a407001507101c0b80000309000c8481030402085000b82900400e10719403100000359005d411040612080008660301c0800070405941d032641040c80b440c0003907102809a104174a44c003400000d581c10260001000050103540210711021000598141010f0300c14107668541d121b8060117001170580100181070741c0c029100c00c82d0309102e450559031004607032583c02405903400420500e0346481d0340e03507400000c540ca49202e030382d20791190300e403100140ca0200b01515041030300c0360307003440000001e6000000341d51210407480d000c43c440c0c590650584603542400201500b500500200d8001d102000407845441390122008010302140c00c2071407404c074000d41ca001403480410100400200b40308216009603801290002070000b07203660381d44070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820000278 1250 819999028 819999049
    0x50c01030c050315030f0706082a0f0d0b0a14030706081e0606091009060e01170a051003140d020c091611030d02030115120504050706180905010e19110403030806040b 73
    0x3810380400c1210b50402b0410103413508a0700c4c03039800d002d03039840881101d0b00c0c0120060f0389410351000ca540030715030000743c014118480c00500403040362615aa600468403074991500340c00f80c494000e00080f03039071050f00000c1c0320700d190140d022100030030780e9071149003108040d003015848001804850310a0340d814400010401d181e8842c4481d4516103100030b000b0410032180c503070621110440754a02c418240440b15442211504001030350303a28031015001d4461581c00c050f10501018103180d400300c4000404642118607a000c41b0783c50110700003001150042229032002c080c0e4011b03d2900307582c0c0140110310341703075900c1401d40307040255244a10f0121b8209034440c2010312000d204d01407845070409007100003500b41c6441800345d1b1806881c0c0941c1ca4003a4070444003000840c5007400307640003003026050090700e440d0303409122030350303454202412400050b00c1c2c00c3c86000107910b9514640140c1d200e484000b202907420030782001c0c40c0da1000d45200200a000075042602c611420710700d56035451441 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820001528 1250 820000278 820000289
    0x71106040e041401050103231905070f0e1006050f040e15150c0c090c0d09050106150903031e1709010c0e030c090c0a02071e03050c01030c050315030f07 67
    0x101c540e00e050300384145804500d200e40035035a49400c1c014004074000150314031030294107090681080d40240034541c0340c412008410118110607083c1a010888080b0b152811140d0b5403071040c44a035211170710106901800e030748607448008080b40400145016038050079042c502c0d108a2400d2607951034600c1000c1d002118580c501d07000403002c540c42468900c03412104c58072018910b6040c6904211803655400303000350b1092103441600c0010b01c019080070201c400c4000b2614050000d03000d90700e0518040c00c0c02d8041c8a8800351400384c01000580b0803c0c40302c08403030b0140d6501814084070710030103804445075450002080500226103e01e440c641d00c40c24000e009c0940001030f181d400300c034000d0030b407000d10b0600c40c442d400444003035207076603900d00105030001141c10b01c0c20b640c0c0350000c0c026460180d9550054800c001d089400b20401242ca40e401c204590003a0b060320001540040110125080a8240c4000c201c1c180f011071201501c50100d130740020ba0240840d0450700c00d070325001d464408250b008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820002778 1250 820001528 820001549
    0xa0e1c0507050d0906080a0515041401051503060312030a020f0a0c0203010507141c1d0604030806041b03020d09050615040b0303090d032114040201020d08090c0607110604 75
    0x755040060030000d442101600e498400e03c032609018008280080107042c1d280115100ca020601003500c5035050800d91100400c1000724180500b5045c0e082c0741c0901c9164811030300d60400d20a42d41260040b04e1141d18014040c0080380000e48206803190030142c14282e81030390a00c0b280c100320700c0310300081c43c1030350454a0700f90354901c4a104140c00d480c03004000a042024898803032840c6095001691040050000440d01500d12295040e0080c10480014a80031281c2c4120340d00820010030194082c0d030207559190115907421041c007041d56804c05120b002e105000ba4070f01c030501c2c0320b5800341960501070300c008100081c09440312860001c090b43e01840c044d40d801503404c000c0c5018801c032503024200360055401d00001c0400280129182c0801405010394081e002407004024002c87d6491800648204402201c00d40c052614001c1100c0813400351103540304030941b25000c1c40c40b10380300e07100490080510610500510096403c09001142e05050541e10071042e6174803240500081c0c94102513 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820004028 1250 820002778 820002787
    0x300c01060810051501390c0b300f091f0222080703020d0c0e070206160c020a0519081c091203020c010305040c08030309012c060a0e1c05 60
    0x38115200f200c412132241408075403190100c58404041c1d082200308003d90102c200841301d14400d684601c03002000400303500030080003007030320003454000d05030003100c1001c601c195400e440d034150b1040c80c4003009001003600c0c110003d40d2003514090361079030080604007030364109000c0c91060f1038004440c05403612256008070f80d5011420034407444517880001028007030281460040344035180c0245010181c05580980c2100003440345031801000103241e50381840c0346524001c2002907c43c0390644200b28102da044e03005941c224401c90254407040e170018903032256140351008010b0321104450306800200ca0180000481140a100803c1c0500f44101440ca981f180007800502000554201000024001c500b6001280e40064842c0c0950300a00f80020280c54500340304041c100c05501900085c8000030401c00d080c401034000f004c80200c00b080d54107000c401000065114004103c03200215880315000480480040d0400880d80c41100241c0300020492080855512180c030512000f2940018 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820005278 1250 820004028 820004041
    0x6180717151806062206031103041221230f040b0114011e02100e010203090a0f1e051501060e090402041d1e300c0106081005 55
    0x419a9800007071440c500300c1d1a2039900c0020201032540100740001c5154400154483e10b4050448004412070a4403401c03400089a00c07020120081c01000b00090034610300412400c00401664010355118549140380f503402c01c000c9800101078421482c000f02002c0301907400708200c0c8552003115180110895260b103100400340c403441c0000e0244180c5084d4481080041070301c45041c03605458540428041090307031100121080d184403450815409101800882000c3d00000c00c1401c44481480c00e002485246042c1400c0b400100c40d041e2080d00a82403a80002c2c0c0b10740e40001c0d83c14030030006100c0703042607600703aa0a0a0020304d42110f103030b806100520219000c0802050040c54249080c828198800c0042a01c890020703000030f02864540000d580b15840d10303c2208011300c141e01c1107a4800d0a5140440c20610345000e0344451405100354201110001000f041710b80d88072000304e82030300a81403001028640c001c50110f00b4556030b072070b00071561030710602c24030a00d0420200c0101c0c240c100f59 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820006528 1250 820005278 820005317
    0x2070b0c07020102061308040906260a030516060e010507030b090916030b1810020901030b0a0e0c0f120108010b0f0909210d150306050c0a05070b061807 67
    0x3500400a1403400e210140c01030303078002207803503100700984d50185070509649441802401242c000c0c240860605e407010500416209640c4403034490317140302207080c0d80a4071929840d18000c00d0b010b80043c1041007000d03203051426200f018418031468000840115500140c1d00b100c000f0348075000040e031101d00d0801180340c920342c601e0301716082c40301a04441440e201da10712140592b12004000120503400a28045002c660f00011100c0300f00035590311310b00c030000305402540188062030100b4a0400450650700f41101c41805980700d40d58140100d4503100504c1c1c03000d400010b0b08901c10710040005003014191040d1242c000c1a8520011a49010100400161101320003040d8068540c5600f0445003000c002800b00302110500d0219000c180300c4100444070b40f05032116250b102e420716101c02124203003c847c3c0001c0380e00500041110341c6800000c111103220384d9100a0008506000e01404110303100000c0f6080b6900404400400d000c1144403504100111481070100d00180c0c00c400b1940c588 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820007778 1250 820006528 820006531
    0x7051e150910051506070b040203061e132613122109092c010608060c0d0f0906150b2a01140c0a020d0804080d0f1e02070b 54
    0x2500c0051816150544100340c1d148039140c44158859110342c0030034280c4c0100d40c5084110301024002c180c0da82501d0503c00e1300307090141c40481c081d00c40ca8000541d11250114481740491401c900c50001e501c1d0500489000d09d030440c016a1000b039901c01a41c2c2c029040306444a900003d03100701c9403503d005132498240d2010380e500001280760440c0900000801f0300000042c5600c241d0114050841c1d5600203c80080c06500201c02c1c0d10300d060803028003280c250403a000b40c3c1d00140740800958a030100450f0aa82d04c40c420303400d4036070041012032004403811010f407a00700361103131002889807509000001900e805c45019182c0c5942c640002040032401c280003800307415186510703440c01503008002080d80d5941c01c0301d145541340c442c0c05c0e08270180d000e4101100c08450094a03040c08d0900c04c40105182e4868041030026200380c24100b002540903407030f124462908a0400c174100420718248501904080c19000791083d40d402006940c4d00b401040701d000e04184c1d0100580b80d4415240c45000c20303c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820009028 1250 820007778 820007803
    0x14180c012624011e03020a0e060c010207060509030a0f231303060b03060601120905010e120306030d03050c0904021c05161b020a0308070f150213050609030d0302030c07051e 76
    0x40f20782800300101c000d4020149201c41c07407600507950407040744122354043e4000920b60340b00c40005107904040c8815000341101c1405603104100071345a0003401a5648038070802480466a488440b00300b1502400012040034034070b443c80c90003c1c000b00c4012906da8800000c20002c00d200360000d1080c840b462044000e051001c2d40208038a00381f26001030944200a0715000707041c0d40320401141048070a4100c03080b010700820403078040c4000343d040340000b500101c4545000b032041200c00c842c140e02ca03000d400e010b0a02c5d140110302c0c004800d42804041d41c49106640031441e6000d1002000240920866101e0300d18559040242504850010040302d0082c190301308181410250402581d103e01c8940b0807203038400a25640c9500c589020321083e440160017600808580c10302070180718040d0014945186940240525a41c440c0e040000d10300031011007030742503170140c40e125102c3da0199004503000740310b481d082c0f403d00035680c0e00c052501c03030038902c440c625001e8880020541e0004204210069a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820010278 1250 820009028 820009037
    0x6090608070215070e061c14070905100e09070809060705040503100c030605061303060b01030e150a060b0403051c02010624030204050a030614180c01262401 69
    0xa0441c0300960303d2481c26182049000e142020a0986019458001c0700b03000c09010941c944100e4003c1095489080801c000c0050a00402d10301c0800700841d880d10500c0030ba150401018108070a020400140c04c00701c03024880011255403456036180d48a40c1308039041d84c0d139411a4900078100c1800c05501405480900a05110604c0569404190110100c1c0100c00009142040340c0048000e092280c0c0069005000011003000d00c003010510744082d00e00841040c000b80c0c0000004404070f07040810714a00b075030450f8070341c2c2c100b030110743c0b003400d4100400307200105019032101140742e0b241c0e0080e4000c460a521008507030660425440503920b22541301d00007042603078900a0891840c10390904040754403120000303085001c81c06941078a01a09000d0103100545440f46800e1005061002628651400c40d20011b541c41c4001800d8080b503060b010042c14500201400554180d2441c41d003102c80d10860f2090941c100b0850104644600c00000040410039440320000c10b0640c502d400290411 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820011528 1250 820010278 820010281
    0x330705101b0e01210513140c090c1e031f150801030305031b0301090e2109060a0e03010e030a0f0c0206040311130c02031305090f0609040f060e0706090608 68
    0x15000704204008401c2801c055507894407240c10301205207400d04e40f04800e40e15040501c0311070324084201034040c0d4812851071902000d0508002c0d501c0c4e200d0030129501494000008965881c0302d03000e022050488114072804d00c900701401781454208407040c509050383c6054a040e032294250008005040041c1d0080c86c0c8440410020290241408080d0032b10000101184540c85d401031381c0c000da081c10b20700c220f884e9610355910348007404039442154214410004420300d1440c04004082d00d41c0c44000c0c1c03035031a2480d0780d4180045070704001440b20921450750405042c030744007170145110344c0286034082c50351040020b03c007410354424030f03551804225012803000c00503200c000c02c42e0280c0307402418180070410400d0000b50070702500ca401180304c0e4281110220159000000750104d425a000702e85000c588902c03c2c0007060200711011540450329401090b81400d0200c0003c0c1c200b03001c3c8140c8030800c0c103151120b1003500c221201c031001c9680601d10030003000d944010400042c2c14545040700c1030307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820012778 1250 820011528 820011581
    0x1e0510050d020a032904230c0f010f09080303150a0b07030e040b36090a021302070309052107060309031d120106060302030912040533070510 62
    0xf000650000512481c0d446016030840302c45000310014841041084e050729140603d0640319901c5800300d403842c02259606080301c1e943d8085180e0750420406808021300280c540c00449840541d85c800f0414440130301340100b120742090004506c40e50f02c02c04900c00d8104c5940c1400704894507980006184001400a200000d038040603264650408403000300700e4240c0400021500c081d000200c0a40b08440c0103411045c01130080012340200c0032242800e103136a601000c45840e10780100d40258071061f104880c0c507070703155254050440c440c00ba182031100e02c0e840b6404210290301c544000d85150011000500410034100300920242019240c248044170b42a070300608944042503d4402e021201900840a501c2e095041d000d03120b4100001e002e11544c4000144c000d50043da10321009024403190030404802c500100c500711080608a0319000c200c1519030306a0007000407506800f0003403c40740d1052101858027602000340a00085e20301c00ca1240141011111584d02115921924801c034a04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820014028 1250 820012778 820012789
    0xf030304031703100e16021b0d0221121c0908031801090206030a020d0b1804140f0313082b0e0303070b090c130e19061e0510050d02 58
    0x315482c40b480d140e40741e494001050360982c0098005c084112070a034200805050480100c109682c00e035020740302c101c48845a55900264801c0304160040418001180141072400003902c03440d13800c0d04815940e5941c6608141040640d140c0314150040207e4a44e01c0601c07030682c1c1c0420211125001c0020403100c0c1c1d1850b00d9400010300c2031000254007168a018040c0c00e40158200c2a40140f110b90741c0e02d00303510f07018029000144035403d03151a00740d048a65050500c105051a407400d495101c15503915924011450070030307020403915000b24110800350000400c040c102d5002d40c2c4404012031030810045070315101c40440043d01302d00d544c0c0d10301102c00da14907413901070503005440c10628980749080443e285104440b4020000103c480c00c1000d0070a0100d06500820421190882405488549601503d41c180104203698118084206400c5400c80c5200c00c094480c42c0f0201d403010903244400c03000d10000604a0156444004004004000d00c4108018000407a0506e1003604560003058 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820015278 1250 820014028 820014053
    0x5090c010509061306091e0308030c0306120708010903121514032e0b10090905060a0b070302010b1203041208070c0b0f1809060f090403030e0106080307020f03030403 73
    0x103050220000e1014019254402181c104d0364940b11041d214654801c001400218188901300021224890140304002031040d01400c685c0c0040065080d902c034021603062650000c1e1810f90f100469080860600c2c009014010090400300000200c02040d410042e242d003001c181d03a622007030b20b081c581d035810b04500804101510400002002c4c842518001313b4030f017480e50704480585c80c065048401d9107440b100002c10b800c820180062000784c04400030301c0f0810401000c5500800c2c1d5004003408180d0060340300d283d104400908507808141e9400e02c500e0705034800501540143d4440c40d0103459814080d020440c2c0000d0b48000714903080c03070403607106040018a030004085200008030321013031040780904003000d0400c0002041c0c0e10901c00540c0340180d072120043d0380014002400a00c158644546030a200c7c210140c00301500c80c800404106018100034012800d259407071108500d4404240b151038007608035580255070340d2006004115060410000140c4240d000300001d0000654402501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820016528 1250 820015278 820015303
    0xb0d060e01110705070321091205011413060615021011130b03071d0d060905250806010807030804270c050a11060c0405010c1506030803090f010509 65
    0x15021450450a501605601d442e0380601c1c24003242c110300740000800c031001200d12a200f041c80c004c40f101550007000c03214016990104a045c401002060454000000c01502c1800000b507071036518494902441c0055551024405004075103401f0406588a00340141080803103180307459807030f040c000b07546100103400404c100d511901398a19400003c020394030320800d6100354001082d181c8100b03211a400840d03901c0005031044c10100300602100e0000d0740d020002902c8880030004988464024042801d0116094803846000c0d218013070010468034642140009060103003031410582d01d14007074040e00701c41c40790b0b00160420400101e014003100e0407140c4416840790317002c2074517030900a0741903548101520a41031165803906a513024004003403a06140c0c807042c42e8620041a00740e5114002c594088841100308802c1c41598000c50132042c40314450044c600c01200c506032a83c06440b11a070040b551800c01005120100c3e4080c4803d030701303020a41c0000c00640c913041041036503401d41034050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820017778 1250 820016528 820016531
    0xc01091a0f150f0d02120d020105070f031b030903050d05040b07110f061506040308070b0f0c0703020d3e0c030f07180e1e01180f06020f1308030a0201060501030b0d06 73
    0x50086480703002c07001034104a06c0003514a03046400714068080c180488102d800103c0d1051190b440500078440d40d010403c92200f800402011544280c0c020820704406400b406000d000001e10040300d40145032080d48034136611042ca0800d6000541346204511364000c40744c0100ca812064034000103465503000343c120354030075291191200841c01d103102e203070000381840780001008000e10003c0c420f814054244140b101c00969035220f02000e440c0614030008005811000811203260312800c2981d41400f04400150b60100941d5041400c0700c00030000a00f032805104403132111042c003804503c20f10141a0b028040004030859030315210304103401548400c80c2c45000b40c17500880103a00039218914444200e4861004200082c44042c000e00c2e08280c856080c03030b2010004030315114540000f280e00440322051007000340d0b0b07110041c0d000f54004409443c01481540341c3d030941040b2440040c1440405142d45240c0842e000b030944004d600141d06250401c59441b003036031a00d041a034421a0040d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820019028 1250 820017778 820017799
    0x9050f01110f0f09180a09030806010c050303070336050105060414012108041d0604060f0e0604020c06010f091406010f08042604230a0b0c01091a0f150f 67
    0x7a05c40e44100b044003400311845c4041001907103244e4401c8040301c1c082c2c5c40fa12059aa01401155a000340d5803004040703410a0000c50070440c003d4206c0d1601103007400501c20340406a0004c180324525240700b010514001ca41e010040c40028402d02c1d400c40c00684007031125180191b10014054818031418110865414842e020040d80100d2440066880080203946540e035500c0108040c081e0700f108402c080c80e49020600034a8144105400c4442c2c40000000c2c5d14034005180c641204000d0990b40c00c5034081040b0520a0414000580608006001111040d08007280c2600f1108124104031403c8140c405003c2207a0300b0407200503200c1181d2030642c1051b41c031031610504401030301e2100340110100c0d0f4140d45d007180715640070f84151402d81c0c2500180026036840d1031400d05500322903507002086150f090041d003a820005011140d00c1900100d070009084c0e8946980c000d1089190003150071400a20180c0380c404002c060308100f00000404003d800240042e41156800c0d140c91b114192010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820020278 1250 820019028 820019047
    0x2211809162303011413151a19020601081b0d060504030e030604060b030c0307030c06050702060f0f0421020f010e2b030e03150402010305070905030109050f01110f0f 73
    0x403800e42c0700c10510746251656500c3c4005850190b500324070303a110700d045010341d916000711842012040004260001d1390030f454410342114110b04290181c0310102c00308490309510340b100d0f84d21591404541e009001a6240a9089003007889800c1020484d6150120314070155031803810300804960402c80000300c43d11189025605806202504c94040c0204c004110034443c13907502009079101e00742c05885036804050100b507152001400010940750381d50005200c03582c40703100606201440917128501e400f403000d00080c16a00210419254544009001c1c401d000d20540c080320200c5035003a0a0105e0025680051002011285018100904203116400c01e65a62030544111004400d108002050071052108401d00020017070f00800c1c9000f03401841c90900060341031412203c13807000b4a40d900c0e40c1d801180581000f43c00d01082007a412408a0265420303c9031091b038074400c20041004207199004c403829644420360445d010b881c18403060480384000000c0701c1d41c10201107415030342c0381140b8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820021528 1250 820020278 820020317
    0x90907030b161b140601060c0b0103230708010b030d080124020c0d0309140607080706020307020a0b0c12010e01050609060702040906020a090f0503190f030221180916 73
    0x83c1e01c203504680d0301101d8a0034000001507103081422080c054440503a01c40d0415500b4a04080d001450b0158030030040010920030440c0c5040c4030000442c2444200a8280c00d41c5021802c0d0401030350350759101060382e01490f0400c8849844032041c00c1041ca550701d01070075a4105403036207040c06481402212440e100754400e10000f41d00301c00050000c070300d402c03050070001c100004078003640d558070319840c001c9422840c10500380c416299100807501c0c80e0448a0341c03004041e4202a003e401503200d01085d81c00040d1040a10500c103803495482140c44140c541d101070541401a40301c2082040d0700401030100352100401c83e011031406480041d510044c40c0702280050551000c0130340800d10101d40c4103109a8424002c03011100e0030550840c12039250310030543c03a1100b00300340c40880240d031409031002408120404404034000c0c0140c42d40781e42d000c00218611894023030341603100a000600d040308010821070310700710030006444d1300c0c50300e203003044650364910a41416001070003681051829080160b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820022778 1250 820021528 820021547
    0xd0b030c091f051002010f0501050d111e0405251112070215041205070611030912241602010b13020708040b0403031206050f0f12010e06090c090907030b16 68
    0x140190f6071395140910001d00030400326210318201030078200002200d1400c0c042c0600700f140c00030310f44174125001b4004c12034280070100502d060240b840341091840d07612071103214420f02220704801c070340d10124052171078500d90f5141d01d102845447c000c1041401c200081d1480b0480480d0911703a903821040c0000340e4249540480b000384180002000720b480351040d0b206070a0b0500c5a821503c8494456905642100051054034410350081c01010841d14000d40c0d4040b480c1300e030200f0b541ea90b07a41e00316034a1320416024646c1504e01d085005102c2a00000114810959960700c020800d000c45ca02c0081c050049411001c1b20840d0003044040501c0200300485004005140c000fa0f90f49541e841c016001310020f0529000d107e14000001909061504440c0704002c8010003480c40340d40c042d42006a80700d001000c1d035450b50359802800d20204810020580209400801041c40403a80403c200301503400a0540070560031400701000020011842641c02a055070f21822807404400011900d4121 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820024028 1250 820022778 820022789
    0x1c09090c080f01120f060e0a080706140f0f13080f0a090303120204061e0912031205011406030a09050106120b0f0604090206300109020d05090c030d05180409080d0b030c091f 76
    0x2d0880c100f151652061907000803158a15101ea80d89002500000e8dc08441c101403030002100054101c013141c03510000f015100d508001d08103400c495030b844e840d1700841c6480d004100720300c10070300c24107410044c1e4542c00b01040c0301c107614150808800410000a42d00c60814410318184868a040d0007284042d018000f0780100d240d2455803410000c2080e201c514032035081d0742c80d040010415143d0b0107a0516081000b42ca82d030715588602c9001070091072408815034240d540c0325000704804040110900006010b2061002d003800c0000c40b04030380c110041c040c0b83c8124600030039000181c88a000f034640303800191444500318019100c8102c20304540705280a0640c41c52000419090f01d654090800120207031000c0009036030340309009940d445402d055645c90303808078040100b864801c50080c02c0e8114441c010f1099000541d0102d029a01d484c901240c11003804140ca071807500851040c6072805000b203008024186141c030200f144518003901e03804002c02d5281c600103086401400d510000d11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820025278 1250 820024028 820024043
    0x90a17120f1603120f020a0c0201050d0f0204081b0405090c13020c0307030c03020c0102060603100f0b0d03020a03020f010c080c09032a04060b030105031c09090c080f01120f060e0a 79
    0x211510300141000d481044d2a08504d25001038035031950a5842900d0300010740d0780b9002000b20340d0340c00544058003c640081c0c03020783c46035048800c03561280064001003620600400c0c8040721801c4000c80c84092186482c0900d25000403c00c29001c001001c0136004005c0e00c0440c00040b500700c042d400f9204144404096210000d402010154003440c000c035201d002c1d074280c82c040c101240c01240c5400d02540c0c040e605610180c44d0b02181d20440d800309688140e510000a026100304004c1007081c2e900c0a01500960080e48080e02410b405200440103903090320000c12400c01c80150180c40707482c7c00b0f0304800001c180802c0d0008a600d04001d00380c1e804a0800c00701c00c03190310301404c0c01c1b80c48241210450042e8106070b4001120040641a02d06a941c010080c0c404418a000a15040f17040c1010050411040301c40015240030144a04c5060000c0b45ea00c08010f0b1404501d20181d001c1c040c1e000036010f1a0b1460500c1c046541854642c032aa54840401305218811840303140c43d14040860103042e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820026528 1250 820025278 820025317
    0x4020a11060c130909020a050105180409110901080304082805010f1a0f0306041b031502041e031a0c0d0e0304050f01140304171905090a17120f 63
    0x1460b640c1c05006002040d8042d210a507855105000c141c2d010050700a4002c5682c840c1800345600500161140c0b0f04040d0f143c440303892500c1c0000d03007a6054000182c80074004100e41a5090403c425002d01500c3d18200944c41c092500c610716542d01058030090400c01c5000f40700c2c00c190481c0d0742c0c004000e2600800240041700240607240010712600c5580c1c03d168001094042190620301c80d41826420020040c00407550345031502596007051403413600ca515041d1030040f00040401d400c2e00e2581d92014001a2101d040580219911035094100c94070008900c200b000000d40c0b00240c00c1c6449030b0584840c9031511401c9840071140902013450b0111400e06c1180ca801c664000054401c450007180c40d03c00511425006564241c008c1004404260003000000d0105001e071231300340d42c0707011800c401c140f805900d1515007601c0f010382c2c50301400080b0700050034559490833104420117401c02d2552002815140d0342815502c3c0d0040c0c2081e00805804298a41a084000140c9030b13060a2203150701d006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820027778 1250 820026528 820026541
    0x381c020637021204090b0d050609060a0608070b0a0c06111803120f040e1315050103061a0a140a030c090b0102120c0304091a03071e0605031504020a1106 67
    0x5442440c00c110709181a000c10851203100003980ba80065a154040307140a003008000c00241c042c40c00c40d070350807141c0302145200141040007854800ca1742c0380082d120300d0410003050401e880300b80c0c0c48510b8540c00500f0a010062a50040380d01580180c01c080035000464500300d4003900701c0e8820130504980c00702e1041c85402e00d1003c0111a40800c9040d2070201107092507400c81800782000001c1d600c1000e12007880300b409500005600405001c0d00c400446595664a0011030951040c440c2401c0e124401042005010300170328800840e40d10381e081c203041515000c681211524429954031021000328080c10f902c4580b508000746811050311a5100c0c1c80e1402c81005c0c00c001d4000c03d00500c40d82d50961104428a4180c81d44000381a01441c6021f18160340c41000c2c2000b1091282469440744074480d244d9000c0014100510150b5040e03284aa003407440050003040940c000018442d04204000a024944c000402035507001c0301e005840340f108480440300740b2000b0310b0759606480f8440a0082 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820029028 1250 820027778 820027837
    0x90608060f10020709110f030a09021903080415050304020904020f010c350406050f070215120a0f020a02070e0c0f03070e030c040b010c060f0e01381c0206 68
    0x16501910010f10180c200103503006c1141c8211034266100303106c00d20109610322010741140b1841d60004040903131040842401021366900c07548111079400c0001010400840a02c1d402c0301441c2030b5003030070ac0c214680340d000705500c004d00510091183c19160102d035102e0380104500101543c21040429840602501110680203c98003131284c40040602c0c901d811050036040303409480466640750700704108070a0242642e00f1104080340c1c010300d101c4800402650f04000781040c080c40c86038859140c103103444076404a03803101d07058800003801005040042600040c4440c115504034031a904c040d91407513402d0a4a01404454800b501000002e00c48c4550340049582c0000400714140c8800141403810403085501e191042d902003400490940040340c841d0344940c4500f40000c0e070104440c40820081421128086c070013600d180e070340c03c15403c0200181c8542c0b6019a941c0b54130788800200b5400054103e42d12211101500304d80c11030300204540b103000617203030302c951000381c0340340944950303c1c0109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820030278 1250 820029028 820029043
    0x609021504230a0f0e19050c0a12050106091a0405030f0601030b0709120605100512010c0314010815040501020913050402191401050c16030515090607090608060f1002 73
    0x640c0091402c4989450072400c003500311607420308483d000b6850043c99402200c40100b03902490101d50041080046803406114450380b00b805c2c0565554620381c80c05400c800e202110b101c0b00030b18100043c040142c20140360000e403640344104401a0242024180c442d200e2604606c3c2c25010f40d00c04020075290000d80700d816203100390f103d580159249082148c880850344a184450460b1150080110f40e46511054000381d4207040c03110f106495034042680e9011411103882180c0d5100c82503800c40d03a140c40744040200d41d142c03002d4080e52500c0341440da1110203131010f20349141c04002040400900b58102c4d440c000c005012542002d0170b0500f040000c10044806a00454010003219094500368241006480e81d141c04007107025130b50720045603541c00011852826120324120304941d01491507101c03006503c604001c113201c1d08055482c40b98404040c0400740741d6480142440084d07a007194600003580d000380303001039040d03030f030480003e0984045c1c0842d280c011400c1420780b000c050f808074001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820031528 1250 820030278 820030319
    0x610181b231201050a0b0307052712071703030402060702010f0c0b0f01030c08060603100c02070e09030a021e0303010b090619020109022d0f040e071211090408070609021504 76
    0x1208560344614006d00da120403a009000101d040080c10841404041d0301281130088441d5580c007902e1301408204090040171068001d50701c426002c103c040700030b031078040d2002008406103055052540c007007003c500410380c009041c800c0c1c03408242e4a080c4603800310001c40350000f5070013543d41040341010340040800c4c0415143c16440f17800100d0b5944000445601600000e0700404500304038074040ea00402d054007051046008105001075046106000a402084008061640c0c0d034501c102c083c2c1761004240141c220705108160301a4024404401d90341100d0141514550741c400003400540e01c0d2242e401010307220645054007580b8551305500140080344240e40344511300603900d050b1115080c0400c4a60b0b846204003950300d0359424802c40e05169401c1c040c2011031002e170300011903070070007009410a40030f00082c400749106000600101084c503141c29200d20a0740d0605884030754042c49100400780c84180c40d41160340841d240c00305841c1241c08800e00c031645a82c2c5840148140d5001d1643d035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820032778 1250 820031528 820031539
    0xa200a09031e030e0409050c0315011508010e42090a0e19060e0a030c03020c0625030e060a09051203030106020d1209050610181b23120105 61
    0xb62906241100c0020311101d40580319a02004252420040903040700003003141c090140703802084290b04c04000c90540c02021908110196060455000361040c428143c2020408440c00400c02199208a840e4100040d4402e403c620340e8142201c8983c261001c402202c18805046100181c07400d400c10140045411034210700183c4030116840213659840d1020344468011584042880901520300b0050030311503000403030000300010300d660502070720785815404945d003020000e080541c1030080c05c10b810030485181c2e082000c480310403e4004121075076401e608008012203014540a0011218148030040445940394241c0800400503800c83c421603000311051807003007164207004800d9a042e0f50180c1c1c000c0c0841c0010303060460f41400803580b46c03201e1560701c0498501003002884010b100d01e600c5c00307000c0f130304034030b04644950020f9640b811940d02d9454140461244482001043c0c12040e00b841c004618030b40307a440316029800e00301300fa08151000040d0b4048403606841d9020b0485400321407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820034028 1250 820032778 820032803
    0x200d05071e052a06040807080609150703091b150306270506010917030403120305040f030f090f08060105031c0e1e0402070308060301180b0a200a0903 66
    0x4070031265802110020801c1d0002e41010794103044446201c2c4426190380030644002610101142031940310780c20071140d5030072019051101100400816800c0745104004103460344015509980c00c0700c02070946010191100d10b001c092203c00b845812607c100c0030140a030303075030751400100d00f44904070b590100880e003842c00024100144980300f205807038044045c0800d140303440d003840c3d00401008100c5418031413044ca01041e4640d00d40c03400311114410000030341d42c0b14154140125030100204000c4201814401000000b03000507600c005100d0f81760034001500d091000050311000e10b44e4124610000040c0000162804001000c504807107051701500c00f80c02c1405501090080051400c10200d846503145400700e0400620400c0c141c030b01d06242c1c4604544a000160a0b41d110260540000d204101400100c0c503080c8161003440741885005d80200c0303065039a21204070402055025125961888140b211442803031500d01d940d8000d024590b90906410081c0001c04180070541d850b07a00b449 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820035278 1250 820034028 820034063
    0x130b0405070e0a140117130c09050103061a06071104271101090f060c020607021c11190b160f0f12020601062c030d030b12011803200d0507 61
    0x8140d00340f40e074010303940d0309a92000c90507080c19400000c0d0200c0603109440707e0840104d0141c200e608050100e2142c0440d4552441c00c0280a8884150070748249440025692200c0c0c6e43c0c8900316064198041d5040c0108140d980014005042c0c0d504074445071542c0c04e4024071301f00e0ba00c40d440d1141500c100c006645052011004490740350441c080d4036914040c042091207038030301400c003060500d880100314516001a075404030300d852043d84191010300c400101120204280d00c804071800c0c280640742d86100b030b91150070202030410244a24221408002240001552030101d448034803030f0041491444031002d407400d05a1000c00c60000e460480c5107940107003007140301054140c100d4a09a0303440c21003023011418421845c4544000c1e004100018164201544062150348085840703500d0000302c82008405201100c5000b82800003580d2400000080d500f5803001d0780700c3ca072501840d013240c1c02440d0b450200d130501b60030401c49000703229540300f0341ca4040e405001800440d00c9603403504903000418 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820036528 1250 820035278 820035299
    0x11040219030e1504020913081206031009020f2709060115080f0f09010e010c1211090a140a030c091505010f02061f05120a030329130b0405070e0a 64
    0x80003080b0440a00c00040341c00746c42c2c031860013a0000e240112004200d08280c0e6210041c0c1d100c0b4001c400031184040c100203843c90b080c031455440309003042c4180040419903000814440004241c1c0e4800c0d42400c0740710407060303840d0041d84889900d403102113041d0300b001540e4981d240024821414001481c84494561a00c6030425600400a07145451626220840c0c8010b9500008141c01410b42d0f9950f0800070050703003402058071412203500d94074089500d004072401070320036011000300440410040300007103440300702208003201c2c2403088201c48080d40600082441410340d2010308ad000f280440803d0310540340d40720035042d41007611080f06003642c071070065442d2000301034044090b8100600103200c140040c110ba500320645091041d6400d621400010302c403c20704070f138242c01030f80301000d10340c100f6400d44540f1041c00b03400e00d4a1111014540400c003015045450301900600311130740ca045140c4119081118256401002840a403814400050000b54055a0700d84100840d140000307446500 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820037778 1250 820036528 820036543
    0x80c21030f090402120703060f12080f090301060506030403081e2205031308060f0903130603020c01092004050f13030503061c12020c030c0a05090411040219030e 71
    0x922024508024660003940d9080d0840c4103a0780d0000c2d0200b200403007a0000107000d920440c0700d030320000f6506082c6030f54413a02520540110345090929000d89002c100f589066900c00440c08150300c0c0d0750a40100803e0241c522684003540044010090008064020422070f03c200b0580162400c408802002031002640070f640c994230290844040e02a0311f20144500101c45025804607071504402020b40402c03000140d001c0700040e04503609100c683c5444201c0150001e218000540c14144000044081d02225119080a050740040c003008070300c100790407252205030040c0c2881c94041c09035405403d40300304210040e20503441d03d00050481425420824000c070082221880403510326503045e0340c55171018203203a42c4201d09480600e11680300d403401c110000c1c425800401e4404c104d0b00301030b1520400503030044c42508003581c0c415071341e1100c3d141c000855008449071086034842d070500348195100c1c001c070f043d0801d00001da0100340da0795001c0281d800010543d010030130040140215519001e2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820039028 1250 820037778 820037839
    0x201110406080112030908060c07050c060c060712060e0c0d0f090c06050f0702040c0c0b010e1303030906140403051305030109020a03020f120f1605030c030a03030e16080c 75
    0x40750006110b540c4015a520010601c80d08100f031020f40c5601245148c00070445011904041c0002d0480410a00b0f0100024000c0c0558016040c100c008400b0741d220b84004082c0341c100b0540e03196140316944180c1244d801400e80301c448200034108020300e020f00b98405080c600c0e040c0d0500400c400c20301030a100c0d07020314507000006904210304100048a0607403001e1401c4640407818000200035a4442c4140584032105071500800c120f100e01d0480281201640800743c100040303004c200000c0495981e550700d8640c90700d000200c40505107400801401d41040c41c00f09824400104020540c200c1300030640303000d028040c0c580071640c4408160a1360041000290010120f000c104010308103007086a409803001040d0501401000101c2440c001040c00b00c12805e504c11800c030750092030780c0c890080c094141a40603018609280011a40c2c603501240014101a07940c008400c3c01c200c24031900c83d40d101c100010201c00f07a03503a40e8042d42c54641c618814420031006211418450001111600422 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820040278 1250 820039028 820039037
    0xf120e0a0320100b060d0203090a0212030406050304060f02190924140a0c02030a0b010905070504080d0f02071215050c0702100c0c09060e0f0702011503020904110a08030a0201110406 80
    0x8943c00c0841018142450030960800d02c1400360008050032400a184174118040041044541c58010825500c1c0040000c6490390000c000c01e00c85181c1c4032040f44e40c40794000380040756101e0340742600802845150500c190041c030340c1512004030f030342c0a482801150311015041802240c5022000415108885a20081030144000103120400301c8091704050300281002002c02c200c0c0e8010a00788202d444044074404c0c3c60a00500140101c0d10031284c100308180b810b1820603040c030300f03e6a540e00c424400c202c140070303031720500038040b034800c0202d88007500d00711120b500c00382c5281c80c04450b034090f4403a4401c4070300e003804006a1494025010703036001e260010004a80b8200346202030760b100b1445142907642903055a0089030081d40307805103000801000d048440c240c6040d80c400c0c240070f600600030000b1641885400940c524040350343c0015260100c3d00921591558908840c003daa4480c00541000d62000001030650011000e4110070650350000d1151101d00303620140c07244151b000382400305 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820041528 1250 820040278 820040293
    0x90b010e1f030f06150e06040f150f02010908040b0714100f05010e0c190315030309030b1e01091802030f06011e05010c031b052e06080309010f120e0a0320 68
    0xd911034000707a28601b101502c0759141545540700c0c911981541e800c540c1c00410612006103980c3d501000c18011001a8030081226000303558035803005200e1445028004034000c24807030140301c003400105c48038107914030485881044009001c400380c040505d910a4143c50500009107500a4682c228400c500717801e4814030300b03004001d660007107400205c5c02004041c0c1d24200510988048880762000e907003e40c88450b001461403801c0564080e0041400c070030401000c0f00c485060641e06d0006055a500400104403540d40d1421340c3c900110400010758148203e410403804d4000c082390043c10386501d50200e032040d042418038072a030f0401174441c0500091001c01d403880887d1103103c210854020400054004182945031a45004641034038a6480651b121000d51081c41000400320042851901030000131720308041c0301d449020f4214041e05008400c040000014072460090b210824038250401000b14414240e550b034410210007180030405a0740c251080048807100840203500180c01480304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820042778 1250 820041528 820041569
    0x31b0a0902090f2e1808010209010e060f13031406011a25050307051b0111071712030a0f0507140d1104051005090a050118090b010e1f030f06 62
    0xc01c1d030325000c9440340c4003c920b150718909070003aa01340c0c44144039944119501c10380069158a000c00f55000341103a80c41000341d18103e076006400b01e00c007418102d82e403940368030130800c00e5102131080c86942c0f0107001d4000c1c4040708103c031200d409401c0d40c2e8540201c03070441c3c2e00c030008440c00c88038184032000b9140050040030f0000c40c10717686801800344591005003c140c9140d50381c0d85503412480040710641c000211a000f02600c482105201030024a0039401c1ea590031100a0384403020707802603810311b40044150300d214071030401c8003901411028260703550f68500300307008200030034054822030441810507000c034000500c00e0181420f08030b01c5501c40c501e02031100152400420b04600000080b003418400003410369a0a0218201b0000c00c2d02d907599030b00c410a081050795042030b04800d0500907001005003252070f000d560385d001c3e2041070308000348000e49980160b076017840134054a50b0101c0c00c21030005428040b2502641300b100c132034400303000c459800d200c88825281c43e80500d10070b00c030003004100700 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820044028 1250 820042778 820042789
    0x30106090e061903031e02060105130e070e0c041a340b0a091407030f032304030305070501050609040510020d0216030e150304050607050a0e031b0a0902090f 69
    0x2c2140c0014658498208100107041101e00203600a4011034580850020498585011014003d0451000e09510341c10100007550301c1925042d820922917480210000c01502088000092710040e1000c0040b441c29030380309001c5034454001c4440c5240143d900d50380004404058030000c8036070b02010309404070300d58900c2e0441e0701140001074105500c0d04034a008079200040403401080c07103071404078101c203080c01c0c212400307030300356522042c15444108100042520201e054038078652502e410600098210500c6038040800d00480e02c41500c0050300004258119004014192040000b03000c81e85ea22000c104005404440c054019000083d1107020721030564014504c20080e00300c010b0820f180c450444000500120044010a415282d096010b141c0300700b01403400c01c6e140b48054034500d000d5440e41c0d00d03900701032702a409018001c1040c0e54100d0082c1d8055a00120103421622000c110400d054066040740312035501650720000007007082901030089900b0090042c0812000300781075001c0c8035 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820045278 1250 820044028 820044031
    0x50c19020d02040f021b0c130c211b0206070e0402090102070e010e0906090a03020d03050c090915100207060921020d060f0506040603200103110408160b030106090e 72
    0xa0740318401d5294000141e84521071420400c40c5107500580310040c01c21010f2044003465100c00c0c0660002c0d60007012640e800350458102c03503000c0d0300864409070245054074481800d007100e0496440c1c100310340a080210340d03c07966000c0e4941180031840c17201e05500740d80b201c80503030381e050009082034034110190900b90014451518188115000a5526800a01100b00a810440c1e0316020001031090503102007000c00d42081b41d42c00a422070700001c6d900a940c4000035002c50003416101c100040c00b0b056500180d5411070000781400304185009001d060f0807a884141c0310384115051403c044c4280c2c800078010064034a41c2e15100c4210f0f0600103d010200008025100d4a130308282d90707640103032150440420028890440482e9203900c0030500015200014000b5004916081e402c2011401021414200c0c3c03800c64648864801c5460040340078001606003440340d15000a000912008005041300c40c4007541401134140540fa5595003000348020310403031002070100c0784103000b40303145040341d21b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820046528 1250 820045278 820045283
    0x1c170606091210060303110609010209060d0b040f0207062c0304060311071a04300305071403100f080114011a1908070816050316020a0f0503070c06050c19 68
    0x190f40c0f418a9a1140f400d03181182c00403000200b07041190b4005103800c01100e47c201c0010b00c02581000c5052700410703160300030020f0362910107403142c1540d00740d07441c1c0d5401040d00700c0c59440150340c1c0319860306000014003c1d10740d803a4001030030301200c05200101100c0d908d841403d040d02850ae41444c12030b044010302010640000018001c1151400260040c54211002c0981615090766072425051100510445890711041d2450254207600d509040182241b05030245080c001085d44450fa01101c00113031103490b46c0c0d64600700000703000c110313014400e505044a0300f282c01c0c1019261251100c80c240d404d0007451140312202c1400500c0344440111681c4c41e0400c442c0b4840b03041107080c2c0c203a03003040300000300e495020a005c6001d00496690000ca000d6100d24045100f07800e05c1c00d110b10052030f82c84010541440c5241c4a15010b504502c01e001c41d20704030360000c08500501160b8101b96032070f5444810104c4140000d0030002a019000d00195076400400a01410718a00080010202c540c0703400c2c1c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820047778 1250 820046528 820046533
    0x12060f09191b08070909060b0d020f0706090b1b070c06031e02030a050105010801060e030a0222020d05310b070309061e0c140f070809031c1706060912 66
    0x918440142200640e1050146035100030b00c50524000160005c8001c0e048a04100d04040090103207043e003900722880300032240030050fa03d50a80700130403240c0c0210407008165270b0800d10030720b09101d01c1c4040d41d800340c034030b41d07503621031080c0344541111852160140080503000403103820480d860103980991150052695044030000c00d00ca103080491780102d814a0140755200300511040d6480319006001d4504c504242c00e03002000310009079038809900d8024800e81c14808810008a100301d81d138071001c2d00b050b400b0754640c036207641c00c10040d1404680400400070700d044009a440d030200a07918200403243c0c00c0d22202c44490f15014040708000f0101814151a1402c00300000c145105480d9400034001403050300e03504001c1600240c1d400c0d00a19010007080e62a0303441c032a0328800c211354220500b40160b40e40e5140b13614085410307000741410141c0c54000e400003000f2401380462072500340b50743c80e900e41c400410310401c180304601096a2142e0003c3c418444c841d014200190b603030344985d01a004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820049028 1250 820047778 820047791
    0x5070207050607123b0f040606030e01112802031201150f050f090609032404030311031603020702240a08160c12050c01020f12060f0919 60
    0x11810740e0344181012600081a03011506803071340d00040e807640c5e200a41140c83c2d00c8007003214901003580c88050754286080500c1400c0764003603403040d402c0103010b0000b82c000c0c4100356076140d0240051002002154040d42001110444480500c0c121094510501c440f603a00000921651380001c8600300c2c0f41065100810000903143d443d03214080c0200309000074111210010315008040c8042c1040380802e011080c04004500100c202c2a11a45141942c0090b00d940c40c1c580064075208ac6094000e44242426194100190401101c0345c030440c0a524148840285111103c00c50301c022281c294421608501816460b031081d0000c01c1c83c0c600041001000b5010b0b009013415001c13032806855240840002e042081035040011a0351000c040c03406030809103407400b4094803400c40d01078000c1490070341c41e810b0121140140159039482d07400b4002113445421003660001f50b60f2000684080b4104688005500c51a2101000b8010000a031040ea0281c9448090480c080010340c000d0719125114407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820050278 1250 820049028 820049039
    0x120506012c1e0132010206072304090b010809070315050a0923010f090c0b0705030705030a020c04060e0603282907080c0a0f0e060c07090506030307020a050405070207 73
    0x8a0941c060180c4d03045202c10201d28041e1440001001e540b03030348500000b100404101ea802268442e400b1401e41401d800340240b503c030400d242c2080501000640c48003080200b050180795205d440340b050280c80e4044242c07224000f69545018a100003006050b0899182c0b40d40b00c825002a60425101e1101160811003680ca45983c0010b072580c1c6c8400c4010700b4101c00e0005424041c2481001c9400303810417112095460b07607c8008507502801001e00c01c00590501040380400450f0080342d000026030340c581011160080d1102d031414074280c0f0450510ba400706038544420f2800d03024101c020003c280d0856148500760b06c8211040390f58400700c4c190482c40707001c6004c0702c441c0a503010032407070030101400804d4004545a04060000e80400451a0411a1800191044030600c84250600054401d0b141ca41180c0091034080015000000440d581034428000034855041c1d60000f01c041c04542d43d00024195280902d0101a500500800e820021410247d0001d40c1000040c41503d143c951181d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820051528 1250 820050278 820050331
    0x190b0d05010c080f010f14101e030e070e090d0c03180b09130207030804030c020a0f0e04020909030a0e040b030f1e070509040f0204020c070f120506012c 67
    0x242c8210200d01d10b2410041011015048540076010000c0c2c180c1e2035900340405120340d14490f140c0320f4010900c1c20031030180a80102e10384055840c4c602d8030096126049000100072305152920748149100358000031030140c01d4500d1061154001000906e681362064070704032106c5989840039414005200c54001e00c80d0303107004240000d0203200d405e07250b4480054062060491810340f41144482c410712900c0e00084d486400203401c142c261401d6140e041d40c9000080c2151525444048030950900000481012550308035100391b00840d0010314036600d54002946078070880c000340001a403c0b8540c51f0251070294083c0c180e002c009821604441300e010809032406100041090b00d1a403410005012203d00304643c8003e0042507450202d40d0406640e03140d007110600c803001344500d80101d000c40b450481000b416008140000545c600380742d4584440d008804200d000b540d150003000e0020460000701c0d885208a161402441d0041c000070000e90790ba28180601032203888284542c0d01d2392401c040713 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820052778 1250 820051528 820051541
    0x180506010f081908090112060504090b01031101020705100f11160312090806010e092b0e011701171911090f0601140f0d050408040501080c03190b0d0501 67
    0x3007544410050404079081e00e85155049aa460280740c122030400149640c0140c8802100030b007087c1032038003000c5600e440074204a4101540161a12000c50107110041281e281228000c0c00f810200b0340414004a8941c0500d01801c3c0e0044030000c4e070880690b11a10a880f2a15151b282614031b00560107246420031040040d0210070382400300040c02071000c184251540000365080c8600042c0c42c1c49560b07912018140708041e0701110180004da03030b42c0400c1c4100080c460b400e4120b22145110b060039540040341e000300c4000090000010f0305115406644542031701b124881f90218140c0ca42110503050304003421103018203014110380543c6a8803241001090b00384203e00b40041c49101000784445090700404030004506000d0900c0034507600400f6901d101c8901030465903482c124142c960545201c0d40c2c03e5110aa4540700030031062041800c050010369500741e8032080300d034407009440001400203407203000f502080801118001c004648c404a0381c00c0000e0401c540c0c074075968640c2421a541c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820054028 1250 820052778 820052789
    0x7030b07050d020c0105010329070507030507050616081e150a030b090a1b0b031504150e161103190212031f0905150906041404050a110103020703050d18050601 70
    0x45406c0103008000c2e404100c40d4051141c0390b001c4128040c86203203000c81c010080e09000074046c000541d103050600c140c0c00c9448068000d001c462660903c0c42000071004403104501000030031030b6011407420004005041d07010001020000d0880c0c40e2035140c030700743c0c2031400d000d103a10a01006e400000120303401502803080d158480038000000c2e0f03074201807400e206c03441c0503403240e640544814840c003850401a240c12083c40c0740c0e040188000c040200b0018104005050420306842400041002c03034009001c1c402c08956820140405d0010700c2a0354640c40a1040300070354009200740d072040801840340076146640f0344126000e2440844164009a0007524a100100c40039001e4500b0000c01d40030075002040031213030030802464803a80030044a40d581840c140b24030000702c0811035076030b100d0700011140034580c05034403482d081c1454190b039141030f14102160704102005442c0001c7d8002c1c03082d00d91103601500c9440c030b0407a0100c2070030000c0070382000c41d404000324540000c0c04a1010000d2038041c08 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820055278 1250 820054028 820054031
    0x5040507020d2607120914010e0106140d02060c0a0206040b03070305100f23030d051b01020403020603010515070b07360e0603031e0a080a0e07030b07050d020c01 71
    0x4240010081080c0c903010010040d40140c44a03e007941c042009074542d120660b8945509003040000c1241301412500b000a40b142400860b40c400700c0c4419448181502c02030750003004a01c0d40e514080c00308904481d01c0a920040020005025080100042807545940030507501d60040590004400390040d40080c00c0e10180801040700d480d8243c402c0c80e40040b110114010510b01e03100c1c980725854160b0040c2d01c10024940e141c4528100c104c0441d4030040c10080c162840140228001092504008052100c1403400d40003600c040c130040c421141a660050043c904d540e00304014044242901d00d80544640003c00088010030303d580d4005024510b580d645a00101101251050350b501d6610001e820000012151101c5840c0b0810b0b81d08485000b030904106a90301d000090450280729176078005142c60701ca600704240440c20040039001040c1d1a002d000e61540407008003155561007407403829600c505020b00c0400c0e500400d0303e6106645183c5140340c10b1002019900f60780100300014000da = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820056528 1250 820055278 820055293
    0xb04020406091820040e061b0c060a0b060403200a050301141602010b0d060219080610080603161410171501141912020408031e040504050702 62
    0x145803a0066000800e004401888001c2441000242001400e000140700000183c1e420f14860035aa0840d8540d240c010401c1000c0d0400c2c810a80d2a62000c84041c1c0c24980f4500348000b0241e2848243c80f404e6034500d00828460b036901c251074006140034002994005024440000011640c610354401c089000c200890071880640a00189405540220b8842d90601c0c10300d032245004c2000403503004d440b040707901540160b07003034045c1d006180000340306800c0403d11555509110081e0018642c4140100e078016a41e1210001201d01036400d46049500034109200c44009910920171240c10100040c103840c5401c0700544401c4080883c3d52203240a01680480404117141608814a04054a062010314614512a0b0601000c8014a40252401d240b44021007591240707003403400614800d0b0350190b4440c83c9805090464043d5245480014900840b02c00c1025950007075904481703111000b0360901e0b61140c00e201c0000c400d2050303844204e40600001a6580e180c0c05000d0048100d5000340200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820057778 1250 820056528 820056533
    0x24031512050c01110c090a020408010212040b0105090606030601180b0a1214010b04030b0a0e0d050d0b0d03050d0c0e130912080105030705090a0e010603050d0e18070c02030304120b04 80
    0x20100c00c0b108841c1805200070050001d08004507490120f9a4100d410080381e80d07420110100138000c1d5040b8004940c40494a6821001d212041c64043c5000b84034800050f80c0c2c0e603040240000742214031725000386040c000b01d038007540184070f80090b1074801240301009503280e81aa0b425600211b544000140e202c13009140110ba01d80710b501030405060b92301c0506036061000e0320001c0d00c5148801011754122000292200f243c903400350240e2001401a10a01c80c0c41c230100806580042101070500d83c90a0b41a00c15072914814500c145075040d12503e0070846501c00f807000030043c0b02c80b008217004007600f050f0200d6a5a03519403d840368a0712000407150b41a00b010400350111035541424049140f0040c841550300040843c1142c0040b9034414003542c2d9900b8850150880200390412503007003400100401802050414030344200da5924000707a05840d0030400d00c150000c070a60100400d000104088900c182040204140080c0480b0300c0c159680124010315070358081c2c00d417141c1c0404d0051204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820059028 1250 820057778 820057783
    0xe0f030d050a0314220507080303040c030c05061801121503060221131b090e07030213020703120518060c0a080c0a050904050619030f06050901062403151205 69
    0x313544a41c070a0030078803440c0c200340e030a1200c007469420050510410241c00204001000080098100c0105890300da003070600c0c2030f003101181c81c00203d0b91b1050801011411341042c1060b070319100b4803004600442920304005442c0b040d903014601c80403540782d8625420803068200c241d4000c1d8401e41d0016503030040c8028080c41d071a50803a4407170411221300d0038040c03660700c0b04280001c0550885070721040003032244045518484981d100040350b50810321744110118021845000316030080d161411104510100601244a81240140805d0307001c440c1c2ea24400b155400300d644a603d000302d140c101d23511a101c0c249080421035550301409070001e84a0041a0f1108010303070480d0320006150706040c41024060300324062621502d00450752440010304995031800403d151501007c2e401485a40700d041c6403a401c00283c0090700e000e820007011440b101c80512074401110089462200300c22080d403032000401e43c2a40e1190b040645074549040780e08c0750461544000e1280982146181e15507280050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820060278 1250 820059028 820059041
    0xb070503030906060f0619051e070c0509190b0d021914090f0106030b28080c060c07150507061503022403010605070507080f010605010908010213060e0f030d050a03 72
    0x11700441c14504908450340702d050644400c4124103126452481400d00100c4080c0103030110714582080024003150424054001441428042c070488001103803184144035542505a403802002c021445101e642c1860590101080d0b14009100100702251900062906450300284110842c61000c080286100c0c000ca6080f40b00c8041e07400620500d0034000840705100140315031001d1548aa03101092980e0303032010705590715840c02580d910301c410080304030143c4809004400d024840e01c10040303110715122060b1000c0482590041c07424608007020581074a0703490070040140001400034200080050080c000a40c0c03245280304481ca146004004420701d80b01800c2e40000d20346500d01c0140800c640171a41916100c0c1020340c3c0e1452589800740c54401d0030340c086440342c00345070160001103106404c450b0454000366034580d20161560704203070803440740301054001c2117840c800c1084818051301038246040001131007110702218800110303051102040042000a00009160b03130325139054130880 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820061528 1250 820060278 820060291
    0x1b060907050d080c1606080709060207080d0c02190b0d0609020703090504150909121404060804020d020d02040212070224010b070807080a0302070507090b06030a150b070503030906 79
    0x3026494901000305440d4a00050003a2860724002040784407080300b082225a160240d41e500380d0107540d9104000c2c0080340c140c5402000942840d00011070520000d0460142d840c80d40c06001c0c1022040425500d920f048107080b41c0080241d0140b0805104165460000f000c0510003159101588106075044a00681080d0001481888200d020a620580007420340c0c005480014101c210905c101040304c3c1c0e1a48030400792400d20010104002810b4003204030401251100001c081c3d19074602e0a8038081c9001c0d00c070000d408080082d0151500c40a04030403030707001030000c20065803160042001da9000c40728004c41c4591880a009c40c00740c0c10803003c10242e03101400210103000341e0300c00d080503100612510001d2040032402c64240000305080782c4005038401c4d41d050b81d400240d040980070b900001c4c002d64040c001c01c1d40008035410340d4010030841c20170080c092461a0b0b03d81514000404032058941c4403d5a48400031920320080001810014000d03802941c4900d01216060703c0c211009010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820062778 1250 820061528 820061533
    0x1101020d030c1e02210c070f0b0d0c1404082a03150402060906040f0807050d03090e0403120e01020d1508030702060705191424010b0c01020f1b0609 65
    0x2442d40b540c2e00065420305083e8140150059003005202240350155921030f09508504201e189100500b00400502502c600704c41507403401640c0381541d84003d0024031814603044c1d401c0007450101502a48044900b40302410040100700f991550f010450f04583c0040382340341d0103414071922079a01c14101c0380084414680358044002d134200443d45071480101e03218000b00d82400800e00f1561100280c0c5c00d18900170b08840d440d40d0355001d4854081d500c0e48502d2006025412001c900d40c103121862001e00750301740e200c08804c94a84980c0d180e85180041c03042d410016100c4000d99003101c03a02030007003550641d40000d6201c00e8046925400c039102c03d250300700e40003400c2a080008080203c141e8450940444950380c07070301a5070030b00340d0070034040c191441011218101154104108040800300b40400c01e4100e07080040510307044031b4203410300621450200d5400d00104214024103001389241c0802400141c1011800880030000e80c0108810350348220343c40ca00c2c89100401040019031000d50f4800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820064028 1250 820062778 820062791
    0x18151a03030412051923010c020d14071a061002030c0703121709010c1403040b04150608030d02090411130308070c030b09010c02060a06050102101d07031101020d03 72
    0x203503a4840d51244003c01e060500d04842441424801c1029105807140d1090800910749000748090002e403681d0025a08131401c080607110b414803075410384401940003007281c0b1b0811402a900c0d003850b40d000540c400f80400400000070711039184002d1018105000c1c0030103040400402c41405a0300e203201c030440d030003401070100703002001620100f12508641e01d06c0c410314000200700c5141c044179680417143c028180c180800141c0561090301502c10701da440200e18203e52109040e170f44010784002d0034130903900c070106010a00e0302d9404220415031260001d0100d0b0b550384d8082c2103801c24080c11004c01da002c91034440c142030500441c1c112400c00c3d8240d501e402160f480c1002c034800d032404041c021480210b14802041602c12580000c1c540181070455203251090206018061100840c0014081c00010945030b22050140e182506c0058011302180c4080c5070b0780d42c5c002c182d10a801c21410380f41040044500509100c94806107009144151100042c440007a25042c0d80009520070580f8114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820065278 1250 820064028 820064081
    0x280e01080618040809030307020a06020f060106110a0201080718030f050d0c080d021e0309030717030c09011404050a080f01060f0f060f03090503030a09050705060f0f0304061815 78
    0x1070b40154480d0b07000408580303034104200464614001d90700000e400c41044940426115000070700e04000b09410b0044901503038039400c0c100d4038121a10703c405410380c41103030450300540c094580147d0003039091910711072512542005201c1410554010750300350309450700400c144a010b01c42ca600c000748504118007084010307540d4111501c200c00c116203d41c5d5000c502c0c22040c002c05600398105452508005840341014004c0030f440394400c81c01100e090044582c1d0034407009201041d41d201d03a00300b0345620f040214000056510b5100304c5104004100100804240c030f41e50321a01d1000341401034020080000b000303110703608407a0356821100c1d070111110000c210141d1039200c004141c2e80203281020030081d2456042c4d010b0850004001c01d1400f000c0200720716810203501c401612405001103074036440d90f9405100d000c0c8600da02c600b00031542081001d4140070b041d4000c0d600184520000180c40c04d01d08964507081604200450341090401e0440c400381e01c00e80a14020b0a04850140900d2290304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820066528 1250 820065278 820065319
    0x9170a020c0f280e0103120f030b030d0c02060c0d03021c0608070302010e19060305100f120212150c07020f04330801020f0712020607050f280e010806 66
    0x8010b01645004a000601045003461502c08014401c1c1070620f0f8065869250501c607440e47e110704000020303001203004c2911031080c0a03510000101030050072207d0006401290110910314040ea00b00720100f001d800148010490034108015030b076801a00c80740d0807122a80400307500040c00e030340981400d03000c4c4403034000414680d00b1283d09003020108144e10401061114682c0b00c560440c0380c01c076110000c2c0903600b540149126074013106006004580700c6139002004810743c0174140020143d014844014245480c0103448045004201e80104041c00e014240d0b0314803c441c12848100c02017088011420700d524249652174089905101c0303034040b480d01120114819842c0304110180d4030b011031100c01000c20784009801c03014001e41d95214640801c0400303600865048800c84460300f50b94020a1000c60340c0ca014102356900c1390700d0000c0d59034110550350440702140340e068080b0350581c01c0b100401c03520301030b03940c07529115440081192030014080c1603005100d14000d40c2252040356442d80907 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820067778 1250 820066528 820066549
    0x10b040807120f02100306050f030a08270621010b0405010e04090809040e0309100e06041406091305090105010602010204060f20120d06060e0f090a09170a020c0f 71
    0x545100400d64040d410803220f26014108040c4d0800c512821980318a54503401c05801e0320300030f5a0404004030118245903881082070380140030740005101418143c0c0309650403000c0c00c03040d2444041c0e82420341e4000307500c079400820031270906040301480082c00e00240d00c846004107449000c00342402d241c1800a0301c030340e12105003144115a00e103507403030030011070000303032482034501600810441104028841d503951100604900c0b0310400c60030710300782611a120b05c0002c1e01c00078014a00301850b2454980102e5114015940d2040b014080f81c1e4407520f49074007400c10100c0341100859103041c025410f44c21190180c02410469004010a00500d90480e00c17005002a00b03141801c10034851000380d24502d181c0320241c0040d80510302c200d00b5007241752400380c058000e40b00c01c100180d0341c0d03a08041d02c11500000e0401c0d0030040d106101c84091400110455128501000104e180c020036641e501c221002c074030b000000b16001140f505080ca41c10095410068030a950107a03401ca611400100800d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820069028 1250 820067778 820067789
    0x10c090303051605060a061a03010302012120072001140d0204091a120114010e0a0f051008012004091d0303040305041502160b091207030b0609010b040807 68
    0x29003910080700382c841c0c202071a400400340c945e641062103002d000f078102441400e9960703d8902040ea1034401000850b4100c1354140c4031014507000e81460f000342043c2801c2200052039540c80c10400c0140504603209600c0c0c0807501c280ea44102501d05007901d0404600143c822070164441002c2e6640c0083c030303042c6403030511801251102004560f0038040c1c82a604266907550038080c422410b940d4580b00401548000c4440172842d030740c0350502d51f08841d07021503900039401740c0000400030103148400c039076086054100e01240c00384c1880c03030070700503500299280e85011000300d500304400d03602132095040220244102c0e840c03c2c0c80c1c4100ea60210702650081d0f0040d40c1d07884d84c0411f41441805119054a04c01e40250703038a900d42401c4c00741c5240c209114880100c0c0030003603140c205034400b01d82ca281400c20101c1074182c6504040702c0140c00d0300314401d40c3e904454200241d030314022041040b0b500a520801c150341c2c2501e40901440082001030703019066039007040c0810b00c002c139070110340d0209594 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820070278 1250 820069028 820069037
    0x4110609040b04020f0901030509030307091503182102031305061837082a060c0a110a0303021c020a170306030606090717060a0f06021e010c090303 65
    0x80e0032000400800d115284194400d01c000786001c08800280050448818244c0341041a981d98203c01c0340c8030712045512000189084005100180c1c0c14680180d040300f003450009036950740010b5588014500c50004d8610074440903001d101d298680c500562854440e101860412040100c0603103c41700b00d014051040c000881c0325a00200d080c00c1110b00f041000b000700c03580d100d0748080302d50b100700294011804210402c40b10301c00e041c80b090154003221448001030028184142e926034445000c103105041101c110a80307266183e80e410085c01508131a24041c1c28411110f02d88000e03a2860403900714040da07035240d800c2020a4001c074541780d01800c100c4d070070404641326080c02c074140500c4850040100d40c401d60f60040c2c050045c0e0156104480c198121030040d1515400c010444204803443c0c000154660a0f40c1700800b00585860b80020f0302030040c0305000d49070600315030f0079420794100740d00690010078480c010f91340b0000d031541e050f14254001c208480c4080703802802c040e0390340000382c00d11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820071528 1250 820070278 820070287
    0x1060e090a150311030f060112030314070c020f040b03030c030d1a0108061509091009050a090b06060a11121312121b241416080403050712200105041106 67
    0x3503e003400111b01c10b0107100c041e14200c2da101c1030b84070305030f40b880d001c150f0000f8a003906003d420181221040e020346541e40fa95039034000d40341d0030030403910516400c0c5900320361980b4489005840c104050524859200e01030b503100d0304440d242c50100d400036116a41c142a006042ca130b02e40c0d8102440c107421031419104594010740da41c40c2004a407003020a039541028461042080214040c00060284c2d2044002440a0f0726018003e0065403240c85020f008024544003250b043d140000c02402d2084d2641000c003140c90250110904142c083d43d09880780810005000a075040d00c0e41c1940094aa8000001104840b035140c00c403a0406100001d010301062440702004140300460b0004140d40c0805c1c000792000d0700018030140c441c5d0580941060904000117a40e1141089654510540500700308002d0b0343c0200305c1c01c44000301c0140c410307030610800f04103100110b081c2d4281100c500b041500c60325100b50402d80c0485000114040b5090540d2400042c040042e665040081c3c420320f0841e41d50791035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820072778 1250 820071528 820071563
    0x120b0f0f060a09120f0b01080d120e0a06050a05040210110309040506150319050105100c080a03060e100e06040c0203030a050603030405060a0207090f0207050d050304150501060e090a1503 82
    0x1101c00d103400c0350020b00c0c0076011030b1040005c07800320448858410180310030580d903582d1110317aa81d0b20400e0300343c01060080310102001c98165001c044010700c0d01044594405094859004903841a80c684040640780d900300300c08e50400703030000d140c10191454111605520801e5450304c0b13010360034085200b00c0c1c946020801a07550086603412655000340025500c2c140008480d15240203044802569802d21000141514014a00480c0903490f91604941c10801d5a24400941d1105400c402455a038880c0495175041810040b8401d80c07d0703c2c030302c0008a050918480d80c800300100700328412824100c18081c51580441a250001714a080114943c1c0700c01c3d00181c154044c50700620740014000c242c00c0d00ca0782d40000c0c6a0100c0302c0242d402c004880c07031001c1c0e81041e441000405480342d400044420441440303080210340c8140103070b2002c1002c0034a0300480096800c00e078000c0d0b002a021041c150840c0c07030110a16500a0000407080003058001d6003030030900d0f002d0340b001500403081d60f41071010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820074028 1250 820072778 820072787
    0x30313060b0f040e10060f0f050118150c030822082b0902090114060304172104060c09081b0f0a091b1d09090f0a03120b0f0f060a 57
    0x968440051044c00408000c02180d65917011460050704503d00300720b8001800c004c0701c4403590581da90407070b0382c201907810603006480400320504a0f1081d1381a030400080c00011198034a030001c2203550307904e16040801d042c020100d282c080d005030f102c1894440210031410010615400d041d50140d15651a010300402070582d440c80c40341801141d64903250418000d400b9036025605051080383c0d917001c281d0b00e070000e8050131002c0c80c0c1201e800200c10400300c0c010412803083e00e100d105024003404e14080c1c04026074a00740700c94a0390010408291824042009014000d4019058403444e001568514011040383e880c00c00c1d544805134a40100a00d240607114031a0380c00709071780d014049880d5070b540c4400c07200041c9002c1c03800d0743d6044058888030560314410b01105500710b68100d220380500e840141044500640034203441e01c140b02d60807421510100911000760100d0090320380700080c40c01c1030300c0c000c00c1d61500b071942d40c452002c1e00d01740b49103503407070b0b145203035001c03009844080c2c03100058041a80c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820075278 1250 820074028 820074049
    0x3150709120602120109061805240d0c0603020d0c03090f110a05040e03030a0b402c010204030206030a09030311180f0a03051902130e0f0f030313060b 66
    0x413600460000040f95000c402d41108045441c07070410030a440581d42c3c00079084031415503240e2540c040d040c0e0381c065000e08581c0040320649004115045500341a5160600703056a50303c00b1000c25004240303c000c0842c01d10030450800f0316414280603011a40d0740305856060030301c80c020700c03c0c02c85911021094681c02c00040107400003600c1040590001c516140d600e800841c0c500ca001428091645200d0a001c071040401c0030720b020607101c0c01c1000200203540c0d0950110800640200d1400c400c107140c4c4c20b8010421051410180840944989400c4c2d5034094030704a20039146078010881080140c1b2070400b1254080c1030013034000f40c80840d615085010303107000c17481e8505e01c030380100e1041c064030b10101e120010b181c4d0440d400c8078600881e00034004440c03142c0c880600b40b0380140000c8400d4902c41c42002801500c010b10052004ea0202d5072642100d40c2c603101a00c03103034008900e00c982c0040c100000c0142c0200a801107003035150040c04015080e0300264020280f988a1b0b51000721a1954030141 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820076528 1250 820075278 820075297
    0x90c1e090718090617010b060304060207260306100809121309060e09060a0911040f0b0a081b1207290703081509060102071505070b0103050c03150709120602 69
    0x81c0a60f590301403602c040d02450041c80e0a2081c4100880c0254905111f81d80c843c01d8050450760031650795899a00082d04604002e0f80c0e001e500d261540180b010329a000800250118012600ca040120074068040c24454880091101c0482130019816000400c0c60b0340da44203a42640e9a012204181051842117900c06048130f07003000700c0403c007082d00310079052050b1183c8089800c01d0b5108041708050318a80a005080400203041801c0316040a82080808034642507021401e00380c0c1c8404280d28011690180c00c55400c00219464000002422540b55840480d46507c3d07603264681c1c140c0c2c44440034440c082c201070340650f208040e1505a500640594203a046d81511307111142005002d8800c11500900d00100352491a02d0034035159100c58000d840c183c0c018080d150800c0c40150b0b1a6213a56086406e1060030700002d03000a5010040c140078500c654090030f0300308201d00501d13260450098119030703110242c10401c480c60b6403055400c0225441d1500030b103074186160802000903c2100c011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820077778 1250 820076528 820076567
    0x2010902060c0d1106100302040f2415110c04090c030c0605040f2909060f030103051e1b01082d090d030204060e1e09040b090c1e0907 59
    0x54800403031022424100082c100c0d04c1e01382c4401040c141e02521898100e852403000100c0716010302c0075040070360190742c1250900b1400549a0002c00d808580d25a010411000c102d0460720188001051200881d4840180b0305050307030422500103100c0d4540301110b4066029554842e0844103122902c15003030011500301d080201540d44405008180e903025000e080ca4182d491000000c02481e111884641d03c0310b452401141030100704034011007580b040004c1544254144407401301074120a00840c0210b1040c00101903854038100880701e2550450031010317840d0800c401d118147c8102c449903102c0e400013480d004401d55030708401454070940c029903a0b9017000243d000452701400014410740140f00d400112060004807401c02c9060b8891030117010009030704000340007200d00300728000b0114090f9203101c15108654503800301e406580b0483e001c1d03420581040500c004034005102201c240c22047d6a09001c6010f2004041240e50690401d18010409040040c002c2d44c809c0044007443c400e8180c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820079028 1250 820077778 820077787
    0x60a090b13030c060c05060a05061909150b0c1b130516080f010b22090e030a1b0b01050618030712060641030102030c1801020a02011407030201090206 66
    0x825203010040c0b400122101c0c1d00101004c14030500440380c0c105810b0b40103000303040e1582c40081760805404003805a0707820441003c0454245003166440b280500a1104000b90718542c0c0e401d0300c04807100c2a440f070f40b01c02c4c008101d400c40c0f0910204960302560070301d100d201e2600e040000440d207000100c1c41099000c6144c48188162070006944102c00e041184d65018505c1d05e0f90300000a610400f0b20805804803010070080342c2c42c449107041d2660b1200141c25145110f41d4408124080e142c1095000d178090308000ba40c1550345402004171455044010300f440c1c00034a079a5075030b240c44201801040e01c190804240b041c01151002110b002846024050703070170b080e555a802c0304842a60740011141d05041a00100b10840c60035000c8908000d401c8500003180c4070048580600da81c1c00301000c150402d0400640d44039142400103500038205400802c1c0e48646144520040c2200d0820080c110340110841c04d0160f80e2114101890b40d54180301d90303076640700b6442d00781d0040940102c002c0d008440481c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820080278 1250 820079028 820079047
    0x909050a09020102010b0111280501021317010209010504030209060f0a030c0501020118050607110304031b05010e030a0b0403080606040504111201080f061f09050a0605010905100e060a090b 83
    0x300409078040c03003130700203216031000c580065400c0c10004040781b82e207078802010580072042c0103166400d94084129000030100540e202d017400d90303100d02d05042c03500e003e4240401000c4024958101c070068480000c6040c9a1000c0c0000d245e482a4030019201b18002030102c2e0807552041a40301c044140100000b4038941d8034034010580d00300c1c9102d8140594a0f0414955121000342012094541d0040c00b03080280d4a40ca01606c0f03076404c280810080c4d00c42404040005400384410307400400d0b5840400202c1c501e0701c0001840e0b0551050168000e4021515500000c1d808810f0250002d605d400c10ba2255910700000c6001801280c4c8519030240c00c002416610034203040003001181504201c7c02c0142e80c85088180d954419004100d4499105400040c10b044041000c180060951902c2450703142c0d98051400c00d9400c00d4950f00340c5e0650700d1808000a40c0c101d422200144802d40f81511040e1401101401050380c07125802d003d0b4000041c2c0700704c0c580c419141d42c001b0b002c0c41112b10342c4561294 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820081528 1250 820080278 820080281
    0xc1b21070312090311100201020702090a052a0a0c0501020c030a05070b150307060509060d050712140903040b0d022b06080606150a140307111002040b090603070909050a 74
    0x41c442681d1018081d5078003100a44200110001d0340c0d002099a06000c10007000d000049058501c000300b155401e001c0400140e41e0156158082c80400801140342e0400311200300c1a41c903d03030841e607030b4484132045081880c0800c00c00d8035100002e40c144010f0320600390410394060f104031820000980400145e000c583c030b4114015180340760103003d01c8400c0c0c0e070b10001c1c030380c0001c182e80680c80da2541c0420410400a44960020a50810041c1503103017024010350170700060b50026a10700001c141a403070b590004049910503000c0024220450603210300b0702c9100300e5141e01c0740e4015841d038802c00091340f8811030825012551104d1080415640c08040c0e0740503840090401c2e16000c0d84e2384e042020003d50f41d10000380050042600425400c807901d24114102c6c09940102813400c1448481c0040948210321030000e544610565160b22444d85070068000d0b007400700080000c40c040f403043c4400d200c0001c4000c1500c01c9800255065542c030740b070b500d90036500c82009a12180d0160f00b000c08110b8800da29 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820082778 1250 820081528 820081543
    0xf02031c0c02250e0a110301180e0601090905060f042a0f0b0a110601060f080402240d1d060a111303080d0f140a0c0314040b04170c1b21 60
    0x34442c1130089504d5405400b02503c00d0300c15042e480c01010700042c003415012a4018a0714001c80f1400074086402841c882d040110990007130800c075560b01054001c0c00170902503954000300715904801145846e0382e5029984400500c000c03d58400080544280c2205940340d4000d040d0042c0c03c1a6a2030303035402c3e40b0600e540001080d1001959590052698400003d4000e060f070303010362224540c00309024001ca40080005005903409420b842c2000303d0181680d80007005180d0f1000e00503501c00b100007510003500c3d80700d54014071030280f800c641d0800e40e4000c40c0098004035410070100d022440940d900b8058041e4504580f440701c200040041080300c1032005000c401842c0c40c061051600b100702140c00c5818901c034002d00ca500220000b0982d8002d64800d18140341242400615000c222120101621040b1411225400000140030501c0688103030840c0012260420510300b030800d4451580718a41c03441c0700b50302420061026070995807492800203154440c902c200d141b41030241289a6642c02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820084028 1250 820082778 820082789
    0x10e10260f09070b030106050405040207020a120b01050915090103060f0e0610051801150f090801020f130b0421111503161d09150904080403030f02031c0c0225 70
    0x5090400603040c1440c0064031b049410715211030341003a142a040c00080e43c07122108a0340079600300c03408502e5a02c20140c04108038042d5113900304941c10881445404500a01404c441c0e0400c0e0380082034a80d01c2c564400d0540b5848080410a4000403c040e0b003d0701030783d0032a00940c001d500c2008000440040b1080840740100c81c02d8080102c2a400012414028040c00c1c100840c0d5040340052507000d800d90207040c650a00c0c09114144e681c840060890f00611198802100c0008201d83c00342a183c0100b005071020800a07072400c0c0c6040690301d400ba12100340e50107589031040b0130030b060040f804441d262180c009031150803070a2b600f5200205aa10454098030401500c41e61414190304c16002c2d0a0b0702c01c01120b6000c2410174020800254080040c42c114003d000b1052031001c60319001046801144100d001030748840c210719000c0c00700f040012003042154000e1001165030a0303003c03900fa0b8405000917001421080301e55089050840c1d01032914170008088a01e611001c0920080100b02c68 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820085278 1250 820084028 820084033
    0x7060b1002031905031b0a0210020f09040e07050120150a0e010f05090309041e090311061506040b030a0e0a080a02150c0307081312030603060b010e10260f09 69
    0x80700f004040e9020701003540c03400c511000c9010101400c55104005101103450342c01100c40041c17032008250141d900001030b0641594000c10000c02c1c505040c002c10041e040b104001e0003603603080c14002032003c8103500520150500c0e5140090700000140800c08411320740614200e210b05c0c04903034460103043c196421034a250b00c0c0c180d4201881c401d5120b4103010f030300d181015514200038802000060524142c2c030a2205283c80c0c0c4150340c41c1001c0c824241840e10907180c2e42103038031041d1a114184540101200d480b40ca5404280c1050780c4c5800c11a4107a60200c1c01d22622626036003402c0b4024220010b12200601c0741e4540101030100c0322000d4200da01c910350889543c442c80098402c01545c0075a50320002000501c00b080ca810300030045103a00c001c00265119900c05540c48080100c4019940c000120381d440606005200310390282e0140b085007820030720b42e09401d07040400c040102c0d00009104000102d40e5400800308003401d400041401c107070a04100c0d090180c010094843c0c00e80300a403192 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820086528 1250 820085278 820085317
    0x30408042312160e09070e10030c0e130609080c010203190f09020102150a09020a0605030f0c031519050607080d0b0906090109090c1502030c07081b010507060b100203 73
    0x605400d10701c1200150343c800702c0c0f4000b091180351101411103078480c040c0381d4002c1500002155880e1055140390701006240d03203075041ca03c445141c2c0c0d4100d9002c8034000000c01c1202c035201c08004003682e90207280091011490f0400c0d9440c1e019070007115180307500000502240403078400310700040720f1900108101c074041c0c01e5140c0040b59070503d4000c0c00f41c1c102c070202031000d03c400c80c0079070b6119100038400b06501c84d03141d0004999860582011010070b03004000c0c03140c0303a00c00a0010364040791003080d5600d141051000c2070141c00b40e80c10700600c01c0100c1410940b0b80007103980c8090040401900e9030f41c8891091402c94540d411000742e002c45640f40000c2c21090346040e003034486c003038038020b82002003d900f07000303100014041c4894103480245040100080701c581e80d0443c04040b46c040e5018584170745091440c203080440c20f84c4242c800d984050103062014180070050070500409080180d518406071402e50042e0548a00495105041c44140041d01da00030000b4801080c4c80004610fa1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820087778 1250 820086528 820086559
    0x120702070b090a0b0c010905012a080415050714030106091715040f051f0603020103051f0618080706030912030204030c0905071205090f100204080d050304080423 71
    0x1409546541a400214020b0400113452020700408140c85002c0001c181c6c2042d5480381401e40710040000792600040c203024040c0049419111407204e44145001000780c101a10303491750305652004404001c03503507100450509400740039403c1c10302108900d03844d11b82da595600909110854031a01400003240c00361030903006008070304070246d0004800b0003201031300c0f03544542600c8024803104441a10800ca00b00460701c100004e4407868009046003c1040c070700310f10004098910203403145551010401860030b1107141e060032041030301d076240f82c40c509110440c140101c0c1010b403a40400b071a401800d07404108654540c20a281560080d54114146100e03a002107049100c1c1d488043c004d082c4550084c411281d154201580040c0300e1301d040031100400007074000450342c0580b90703602036600c61150032455420a0005001ca82d62134513045062a00e409481915507104d11003c0307080150002c0050308100100081e01c1c0602203a551500c15002e6415040b140c400301041441e1080e0000100003d0303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820089028 1250 820087778 820087799
    0x907060809120a0207030501090b180a030e100c02150415020a030e010c151d07080316020d0201090e09010203090118120e010908010908180301061a090a0b12070207 72
    0x1c44120004241d400c45060507400140c01103030354502140a00c404c0000458000d0180e007114902802c2c00d0b07201803c001030103220900b1580c0000080b90084030020010039081a4074910031641590603d0308801e41020446103244c01d048000d501070b0703a85071484084041d10002d401551261690202a409950700a03030340c07450040742c0100040d00c000c8c0684000e52055425803032142c402d05c0340d925540600302000096403007004200d41407019010b000003402e0b0301000120000d2005601a5182100b90005440100e490881c040e00070b482ea41c14150840e440384116070300038800720010001c40d003003107500c09010350300030f5400f561258242400303805804801c00041c5c1c51258810320142d070003071486005448038000701c48641e0600084000c00200c0304001e0081004035407081030b61075603850004141c04034480d4181c245a001c2e80c03400105000582c0c86407003602c200c0030010380752615003503440c002488160345134210340220070300446c4e2180c0e4030509c0c05645004047d907400389c41c00c81e52a0202e450 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820090278 1250 820089028 820089031
    0x91603050c100801050a06180b03090c040b0103020a050d111207080f010509070507060c030b12032208070512030705161d071d01030f0203131e0803150d120809070608 73
    0x82d404403601b0002c01c0003070b0041248070138201403d07480c0f000d01607a818081090750400c80b1400c2e826000181c01041c1c42c50b20348181040070009007001c40c10718841c90f00051881c0079100007010490350742c1e4541d98084144d2801d86038807110101c8030390110701d04004002c02441e400d607081124078031f0520011030640350408039940310700a103559440c103041007500c4010181c4071940c4d40205055032590707484041c0d190350961054915441008555401d1078050401e40c3d59510001101c00c881d05210134000c0340d0012569408495040b0f584412003903103141d046003140b041d5400103040703108801b0742030301e044031078030580d822180ca036002d0410042d2020880004020304481100001c0c503011107041d641108041441e4402c0410b25000a0586011451108030f03072080c1d4100c0c0c0c240001036a07150400008010008004500503180781da048000e550b0300c0860702000e4010400d80c00e01c08810301090f2100900400d41c40c1d0004002d4200d55502c0001600b42041601c001d45030740184040824907a0003101c0b100d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820091528 1250 820090278 820090289
    0x30209030a030818060906090f01050c070809130603060906060e06030a02210f060a0c0215070305060607050613021e0a0506070302031908060a1d040b091603050c100801 74
    0x41c40c540c2126601180c058400800000d506580450407014448080103d030b40b0500d03400d001080c41d41403410084e40717882607001030601035078180800c01880b00c260f4015501110391100c50980c40740e40d40740001e0030070364020f049003802034a403120020510000d03401c132203681402001d0030000e8645030b0b0b800e2610a4400c40340140c240c0e0040880d4001410525a88400300f0b42c84401c0d094101801c40c012800c122460b580d02c901980003200b03101596050388900000000c90740000c04035114044101e07406540006c110f002810f55032070001e027083d02d031031048600403980541680d105103800092002d903405007003000d034001e2040c443c04134448040e03178140201903580200001d40c214944001c020240d4490740089007140428000d140900c508100011100c0c50141c940d078100b49011002d110b4440b40790b13031000121215149000c900c04e91280102c0da0440c5d0400120681c2d90f89000e180e41c603140b03604240003d0403504500010a002001c038201c0f051082c1202c0f0209c8503402040121008002802403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820092778 1250 820091528 820091533
    0x4050103020603161b03091a0702031507030f14070905090c070f05010b0d0506041703010b04060f03110a18050909031b0703120e10091802090112020f07050d03020903 73
    0x450b000402c104d945070b00304900c514140c1004d008005e100b80c0500d150603001c8001c103402d00c1b0240480f0485400e4205592941082c20f800d2404c0c680000340e0f5046140c0905846008034808130310f0705417003a000841704000b010b1003030101e001c8201030508040004c440d2080040c105040104041c540907050a0140c0c010048450508044c1e0711140034107034408200f216159030328681c0003025200c0348004000c3c140910040c0c41140380c10706240f03c01360302590003c640780e0020001070045100110555043e81c00ca0f1400d01841e0a44000a80017048007200181c00c82030003040039007100350700407141d0100c0307003c041d02079010070307913500a0181c00c24040e40d464409420611402007060700a040c41c0008152110442d2029542d03034407148200081d6801080004541244c0c11029007004091240c0301001413801940c02c074a844a0341000c180d00249860216800091014191b032040700031650400e041e0404640e1004454809900c0b41c1c09000120740501402035480c132241d0207031003a5140414050701 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820094028 1250 820092778 820092781
    0x30d0c060c08191e050c03070813030503040b09030702150301140a03050c06130b0a031b110604140a140307110d030f14070609110301051605270d0f0303050604050103020603 76
    0x1c0f0503010b0300310614034040b101c180422030000a4840e0081c0c40c059030130b0041159a070b00f44090018490f9100802c5088000903020b00c00d00000d91040407213500540007203811025458030510142540304e4900041e500c03d9281070087c0311000d45000442c100c480ca0514000a2201759091088152813480040c009800c041251400f505055004100304000c0c0955842c0f61500c40c0e1103040141c01c410681c3c00040c0d42c40091500e600b1561107850800308031400c0c604039400002d0006903680e03400410040c142c02e80e40d400c00b0f804005c204417034581c01d0360000c0c05400301c80c44968190340daa0440e0038241c66035250b81403040a1070500504c0200c18076015078a84420b1050840e042e2040009090100d20321402048484041407440c0714031038400d0710844080401035401000c05085d10300240c0040c40030516200c0c080107094104045400c1c840d103060345588803100d4500303013014140c1c80c03154454005461112040410611004600314180f107905d0030051515100107000840d0424000250030400810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820095278 1250 820094028 820094071
    0x6010b09040e0d0306050f0103140714090a080c100804081603090509010306051503010209180406020408120712023c0709021209030a081311030d0c060c08 68
    0x50092103058809840401c500c6855401949080c048026510010381d48120900c4186400781031444000424641480f03a4103008510342641d44000d0200b40612003441a0290708000e084217403025003000810507429256124180d80c2c0710401074421512404401c40f02d40d080c54080d9160501941d0402c0540d41000718001c28107011440c1c001c0142c2c14081d022000040300d036107c400b981d018521498001c40c06040a4a80d0925142c40c81d0300c1c01e100780d00500960080ba00c3e200618810403100c2204081d19840f00d05000000f44a2600f094609009809800311503c0c40340c4000c0403030314410304503d600c003041d45c00100d0f107036034101580c410680519200311604980341d5948200d800f498151904c642ea0002c0f80c01d62500c0041e0344094103854000c00c0d0705141d01c40004141d5400000d5801039817800d0400100205101402072441402030000d0990b0002d10011400c89a801c00001e021540175032403281c00540007081600c0119101400c00c030310060301e81c2c810100315009804070b00070100c0044405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820096528 1250 820095278 820095299
    0x40914160f0c0c060e010e010f320c0304081006030506180312010f0f080303040b041707050a1b12050601050103020a0201020f1b07050901121101090b0c1b120601 71
    0xa03042080101a0803002c02084011a101005101c0d40d12407112241110001402c11500c00c51864144114142c03441e003510341003c02e4844141f0394991a003001080302e80c40d103458000c075220307503421450b000c00d03600ea107050008014000d64450004071039071100f104141d901a03c8841c0801009134100401144a1a170480290000680c28000340c034140300400b85856040c0c00c090707010041038030410030100080200c040007000030f00f120102841c554034103501d0360300558001410092800a451002c00b90010800c41621020340d0b101c01a62012811030a0030001e0040c0070701c003999600c4080b000020704044460804220f1070744030000e030803a0303032810005400940204240c401503540810071a86080403034001010002044040c01000080d611003107481d00380c4580115015490a20041c8a0801e4005619200c0390b07024042e029043d0801004a82c901866440070040c0c0c0c40c007141d500443d030000b00b807a5011340c0141c9100f40d4001c5e100410445000306039a041000c80d04038000500c05907408 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820097778 1250 820096528 820096547
    0xd0804030b1312020a0b0a09050606210609060a1805060417130314010e0f120906070803040b160905130b190f0306050c0703090e070c02040e0304091416 67
    0x8008658103840d0440d29034580400f841200c0a0050b006020403108018041e0900c41c1c02c0f1001c404200501026980c03003c3c2d0700c90002d4034075441001080000d800c14600c5951181815140c0c4041e07030150f04020121560340e0800b5184d014010b81442035005400f0003007403483d445650003000800c541e450710744800c4480325030900c1c20740300640300304081142c1c41d1404040c038004601c619a46528079040b10b1015003114403400c480f070041e4000ea04a5450154001807440c0e04048508000c0d036500101000200c00c3c0c483c0d201c0082448001000300300621840c41da655100c1d0301da000304040c09030804081100c03600c0f018080d680d0300100e40c0b01c43c18a06a01076010407001080a004450005618441100034103455400020500b42c4510705104001c00ca00a4a8120300c580e005241804445e94016040306440d000e4940900200c00008400c240f182d00c60045003600a0f000304007403601038942c10b03107d60041c082e00e00f0306402c0c9148159104000b501042c45109106a0f8007942c10f50a5800c4a01d480c8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820099028 1250 820097778 820097791
    0x2b03111c060801051003060e06010e01060810081b010323070e062106010f0e0d02061c0504111c08040b0f0d0c05041409190509030c01020d050402010e0d0804030b 71
    0x5440e0400302d42140240b16441c000c10044d4000e61486195141a81c140c1d070240c4489003490700944010001c4094601b007090558015090040d0070761703203190160015111550207003849106254402c0c0600f850440c0030101403200703980a100c80410b41803031421001001415207803003070030240020012407080f81c006050b450001c012030300d00001c3e40301981500c01a2140315a00300594424051190380110548a088070705041c21080b07411303110001603e0008904000e4040c0c000001d00300304a088401e800754990b031a00700c0401442c24030381002000100c07801e045900405c6440c217003100804101c2c0c4030b0840c035035201400e68502411318424000b16081054281c910340d20034080100c1d0816075000d01e0038038182c16030b60103072a64034010540c804070f00700d101000c0c011a030500034009094144050400150780c164404102c1ea155442c480345548507201d850940d03548041014203260455400c010300482c000d903140002c604d840410054054000d0308002c1898000700300400c0003580480c0311580c8041c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820100278 1250 820099028 820099031
    0x30c0c05010f0215061c050729032206050f09010507090503030412080910081b0c2a06042301020309011d0114030103050d030e0f0304060e030f2b03111c 67
    0x185250399488003004c0c000e071b088405800c68402401a14440c68020140480c0b00c02c109603000400424220140710103041003c4543c141601034902507245201c0314a00d5611031070810041c90708180b070000c144c0701900c1c1400715509140210704850f10511500055a4000300a10320303062400c01c241c0107520802500721044041440344a04030356a5903090194102c642c0c07642841c600d001202d411480d400030b1f808408440041c09a194001d000040120900100d00e003000042041d410f40c6280c1008a02c0c511a80700c0c1e8002000f080f4200c1c1c0348064085420260201e03003440a0700d40069071a8003070102c00b0750000303022008250610564840c18048a070040c1007840d0f0b0040d880f4007569030b0768004d8109458640c0500c02070306888c2ea1621600c60074405440c0500b0141d00e5018600380c0724031562040c0c3c0208100ca040b003104c0d070b50f010710094002c850b080040303500d10440b255480d01200f80184100c00219200d03039000b0420b80c000d000d0607064000d40a54140b42054a8014005014800100720a00c0d0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 820101528 1250 820100278 820100299
    0xc0c030d08090727051815040b0601051305120d02060a05090a0b040804151e09050105041e090c03140903040302240d0f150f21080c0604030c0c05010f021506 69
    0x2003042e881000d006680340c8a15540b440c42104040c0e103041e01c01e81c10749220031f12030000c02003c00d16665000da048030003482c10780c2c0d503000c2d1081051107040d01034000342c3c1c0c8070070182d030300644811000070003440e241015025280113944004504040320000c0f01c080c0b0603504041c0b40c5200181441a4196120340f050070300b903003000d44a000036a003900311100508040b4a0000d00c1035510321001ea81d03c002000c480c0b0301120514100000245503010328854140c0ca50b402d022030409207180c030040c0c0b07405800c1042c82001070b0042c00400a01805d802c94007024400c2864021840c44031000c8112019070b60042c21719502c400c0b40d11000074600c3d4600040e5441040c0902600007440c0c1070b030140d03c001121548011480125580c1403c0314508a68480044503400100821003030048860781400d40c000b030000c4c0c245010490134001d01d10b11400041c0c0d416030284d141040109a004039084011034010b018440b0540d4946006403042280c2c0e070307030140240e4041c03500800702d1701c00509096408013000d0710380f4100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 820102778 1250 820101528 820101599
    0xa060905030c01150f15120c03020c190b0705031e10240e0103020a1409042c010b060a051803100f0b150403031b0303020f0c0c030d080907 61
    0x2158101c240a0f9082942400d0070008021034100c003d02411000f141407120745450b1b540039004408103007d20101c2038941440c04240f034040d40c151100380c0d1007030041c0d403030203040d24254141d40ca0b0111800c990035800040411b4040d4490360a0303912980317040000402c0700d840c1840380c501100000301201480e0050350300100c0e0040300b540940628401203003510182e2420a100a032030385100481ea68105841404103400180d4480495540b034260500619510160b03840858007421505c440384805041c804641c17044280e001d0b041010707164101c0300800080071101e0400216124035005032002645c14031405000e020704035540f901040b00241114001211001c400c1d0640366a4206d10b50a60307654079405401c1e041600402982ea480c1310700c854038040c210f41d0054005862640c03c0f260050600e1310705801c02d8000d5049400541c4e1502c0d085440d4241034284990320001400401e001e40a89503003000c2e0103025200c00e40c050f648040240040b09d041c0314000c2110b1300c0200251450000002d080450b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 820104028 1250 820102778 820102781
    0x51c180314040b071a0105150d0203040606080109030233010b09010c1203020706051b030c1308010603111908120a031503050c09010605030c030712020d060f0612020c0a060905030c01 80
    0x4d403885511001904203900d007485c8102d12059006500450700071309078808000c00c51044aa1a80b5000390041c0c40361141e0404000401035908640115844c101c1d041052640000e80c0f03481d040e610b0080d2041040c000f002400704108807a00900000407036800611690017824040c0280304e8061602034850310503511128681c03c81030b81d030033022a5000031004c052159178000e10345d1001c80c030310880540903404071310030300c0e140300c0101654000d5001003044090003084030b200c207005080c0840203000040d280e040034484050410341c0e4520402d407088509003e0311148420703200325441c91018103180403540300a50541d038071003000d14040650ba4035044c40515600175041e0061400355000b400e40d075074248144001641c06130070100a111082c400c000c2c0c01d8260741f049070f5010005143c5481844031032010032000c1e0040c65100e03080c40c0d08100380401c0800840110030200d41d09079a9040b800c50828030b25204034442d402c0c0d1801e10703420903600540800c81c1500405401d03441281140c1c80e00c8810401e850 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 820105278 1250 820104028 820104037
    0x3051204110a0b03040b04030f1709280c0603050a060b041d0c160609082a1b0a030611040f080604031806020c012d051c180314040b 58
    0xa81c0102018216001420181090700c050304140c2c09452460609803540f458282c03000340003c08008020180c40c0e0524410701705d10310043d0312201c95440c181031580c1c00d60b03241e604d40d160725020009454034102400f00d0910a0180c907613008501c3c01c2d101810940c4c12806050700901c02e060742a15880005803201004000300020419103001440c540f481005184e00c1d51005420040100382c00c2c0079404503407101c01260f4850716448400000d0300640c0b803500400d80d02070411900380c00c2500300161045aaa0070780b650006004240595040100402d2020300d141c900401b0703181c00803405c1e10148002201c0ea0301070040e44220405075405c1c0f5603181c0031b140c1605060382005070590085820b010415410045406000c00c40160f180305c501d00303140000703503a100c148403014104545101c0c45191b152a41900303884041141c0c002d907162a140c034901502c59032240c0961103104521800c080000381c51403045114403544441c007500500f507541c40442e0501d00150103c800b8500421001a951540700d0061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 820106528 1250 820105278 820105283
    0x15010e092206090b01080d090902391203090304031506091104030506070c1e030c020a091505090705032e060f11120d020a0e03010513050601081c0c03051204 69
    0xc103030f8820030714050741040c2d01a0b001d100e859105800401281c0e40145001050b122440c0005880e1408900e0b52b5038180c1c2d6421030510082106240c243c100100c20040441c80034074082181c8010110565210081c03104a9034180075400502c000e200044002c406440321140e103102c003040384ca448903c214215203240070b0ba00d4003000c00003002c20070410b090001652103040390810401c1060f5544460b00070402c2070f8540741401d1003500c040d608250254144004032900989440002520b84070040010b10102400c40344241c00c841d0300184c5450140300e0130344a00700320317a12a8256190712441c00c1c4000c51003028184011443d90301901c91b000c0340031018005212580d42c0c00d00c1007075800000340244445c049480c40581000a418400440110880d41d4041c6490001a03640501010440c0c080746401340740b41d85542010203014443d89841120720382c15005200341c41c1d40d84d0341c500005540d0703c0480001c0c040010540204000035004035440300c1041d0003400c0c290314020342d045c8116101c11045404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 820107778 1250 820106528 820106531
    0x1521030a02070f080a1104140415180812070504030f0c23010e100306080102040b1b06040b040f0303110d0504051b0a0512010b2715010e092206 63
    0x35503404950401007140240102c40740c8192203810900043d444a001070750181c801c4041214082c0d40d038840394085101c042d448501803a075820a40342070458a110071480090183c1040040103c04544031084580c4036401310000d4504008900d5614005000602640500c03000f84000804140710801801c0003d208070200000c075400e00e10351200503640d510b0300d01c1403000c40c0c00b441d440907600945d155140010460359466a904038a008070b000d4641c40c1c010701c0d40c0b9400414005228078282d0054456507070303d210b210342044070b12582503680c1e00c1c007110040c00d021140e90114000c00c01c04220201494000e2801040d000c0c408004825280d01c5110404c0f01d00d65183c1c01c000c14010706008003810384030002d0300f41c00c4a540040001d5080c203182d0242d14442d95034003031a60149030003548050541039028000c9100400c00041001c40d8001c031b2506888291000340c00240580300c60080000c880d00141c43e021203501003030040c400c250303000410250803103540e590044c00e000d841d1842c0c5141c191080e00c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 820109028 1250 820107778 820107787
    0x9070302060a11010c09180e01060503010c0305011526091920030d0914030a060e031c0606050d0207111f140307201005010e0103111008152103 63
    0xa0f4211171100884008100b62417038203002000b0890304244200984030310216401d25a40d80e41401820113038042903143d843c1c1181c4041c103581541040307040701c5044401d42c01c507050182d426281c81c0042c80b0f801d01c51042c80351003c9154000013001c1608001c1c4402100c041150040014001e445c8403031054601e1280350054203080c4002000420308148150058902d0300402400588503542c14061203000140d40401c00f92691002c1001100d02030704000203021410f00c0000c1c25443c1d602450b030041d0500340341c1005840d048080d005a1003140d010b0380d2014580f80100d420000207402242044958601259072000980c0e5103032103540c2c1101c81120100f01c0c070500070b42c1c040d1628030300d09405005940c0c1403040140640e00803030315024411809448220003940d03001450b0514002d40101050280b0703000002c03400a41c2e2180c480c0c1603034800c0520038070034080001003201c0039240207030942c005821080000d1110b1402040f51a051501500c05148000b801040c0c5101c103075904800b0f20582c1c070104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 820110278 1250 820109028 820109057
    0xc0402180906010e090721061e09020403320d0206160201061203080c040305030313020111060f01030314040e24010801120b070512070c05121201050909070302060a 72
    0x45182e0007007000d0070a181070400318004600c141400070004000d0040c1a1184243c4905d1520001600f003007001b010040740d030312101110404012007500b02019040c0107000300e03030b0341361510844081e01e401c10030b0300c00c0026000005001000c03640c108028012080103145181c01c00c00c2250300800e08658001c0c101c1854098609021114840c50b041d0071a0b06189003009581058002c030385085405143c1254969200c4404122078030072948010b0440c4000400c100500000340c1181010303034405d81c3d48076a90140e411502766651019100e44140c10408001040064003032040d903a4030012000c8060304156440606544015084403504020741c0040217030311000d800c0c00e010038115402404c140c00d1950400920b410380b85142e181c004c0001750241c0101d480d00c4d004400342e80c0c0c0004403d10a4165160003d070040140f448c5030001c07603091080303202c4411250a498107031a0071010040c2c000324141e10f07100030000c000307101a040f1041c0740154400800540c03603074402408100e0b00e50721030201035540701 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 820111528 1250 820110278 820110289
    0x721080a0309110a0b032706010801090302192001030e0f03030a050a0c08240409080904141302011b0611071214160204060503060a09111906110c040218 67
    0x54103450301c0791382180c50501490b1070001c00d40707400c070880d448000c540400111000501d14030110302d40c0150720504000013281001508030150103031081d030944240041c404c0256131200c900120003051003d40c1d00d161031454049029404074200c05140c00710f502200700844909000b090b03500030406810001c10060784003514002e10790080a0504104003030300d0310010003081d000000c2d1038441103c080028403070114401205281d100c2c80010410406016079280203440c2c1d13400f082c00107000d1410910340c0c14070800303181c0032144180e040c5aa44003d00080350300440d0440005008a0030081d4041e1501001c60301c4c0d0310400c104149111002076540580d42440c00818845501d49804c02014400d017903400f841c10419280c00c00d103850b584620107105e620006014042c0754014640501c5524100b0448403c590421004640100701342196090b00c44244108065030f1002d42184890000e420000107208000354028030040d04140c0f0b43c03120640380020142d0703004400508401c0c2481c2a13160007403924 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 820112778 1250 820111528 820111553
    0x1e1b0c07051509010c12030608031215030a03090b0c240601090f0609121104320402091b0c030a0e0f03060f0f0c04081e0115080721080a0309 62
    0x807250101e04100d01107000a00140d074108005000346c0707407160f014014074002d80000015003580b03010b50f6101c901f144070645824000b1101180b2510b412112410541004a02400c0080d01a5600c070020382c10f00c0c0c442e180036440729680b502c0314401d1000441c092210000c0030034400d1910300300d02d1503d00749040010000700e030641050440d8200e1010410842c1c1d0081d14144c12500700990070a10750f0100c0c20304034a1550005140ca82150910b100311600d80d001e4001d100d10754000d03282e0a4110302c0fa4880401000c6030403503000750007419060200780d21190071246c10f0f51000b598041c203490b051014404074150341282c50ba00020030a0300358850801d191900400500314010382c01040e640c540b00844103001c04000d444158145405404160300d8254402120090090f0744100c48440d00303a011444415140980740c40440e520388500701150609905044003103901800003411042d0819010185480301c03100d0a410022044502c100000e82900240940b00b401d920001040c2d02c1a04006076903504 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 820114028 1250 820112778 820112809
    0x807080706021b09070e10021f06081509030c0a0b0a05070509100f050d0213090501050a0312080621060702010c0306120f0204090c1e05091e1b0c0705 66
    0x2180441c0300c00b00c1c0b91040001c0540760f0803101180113445030981502e0307500044c0481604001035028161000b0340000b4045290615070346280d0281000803c841e044a1441c0600812a005440721503038454042150580103030091059901c2c00c0f1108074820300c0d003842c181080315401484000c00a001c0218401c10394406171b1410b2203898203454100084a61411010100c140980b003889001c0349842102610400500e0b044115540c0340340c503108280e6440c0520801282c181024008a1242000440081100d5102c444404003040da5442542d0b081c1c2c0081030560402c3c1c2e07800070705900419030401083c4400d00d1a02825080c01c2031100207081d2081010400241803d0a0301002442e420b107544141c0d45802101201225200c1c0c400100500f06810010b03041d00341d25600032600c86445032498034980c8400380e064440e20364600c14051a0901110812014001040080e90411310b41e40d050340c2c48010000c003c01c00310940d520550458102007008095a40700000600c2a418034803209004000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 820115278 1250 820114028 820114033
    0xd050f0f060a12020d050111030106020705040f181509060f0915060602030a0302070309080a0c05100c170d0207060906020306011d09010b1b0a0f0c1e1419080708070602 74
    0x80c1420343c41200100204002801540303111810000d00c08203510404c4518480b10380640d0342d594540c030080d903a04241c06698861031a100e040e80d00c01c151440f50669100880611600c1c01d210b84c8c0700c50a9419445807405d04903911607090a0005142e1300c22401c09541c070420018409006041c40e002000ca0741110100551502000780034a0340c0000c1581c0c280061881e0150341c41c1d0f028541103480c404150301c10700083c8035407141c10341000250341c120f50649800b9550030140e418201800c5072689060f9902824040b050740181c213500143c4001001e408400e440c0251030481141d880204441c1812015141d195000c024403813103682c049685400c40b254070301c0c490008160b030400039803241010b1184409400000411407585c0f00641c0c410610300780b5200a0382c0d111081801c100e0744140850108490000c1309520114891049800d03441800d1b01544113903080d58180540f00a0481485003080e6103e11680c00100e00c8550780c402c0315004e032965030050310000d445c0802c02c81c41d241d401d421510654 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 820116528 1250 820115278 820115299
    0x41a06060c120c070e09240c07031803200301050a0204140d02010908030703020607020106050111100c120204090f0621120507060908030f10060c0b0c0d050f0f06 71
    0x41000880c4031a0038080007041e030380c0b0783d40764a8003840d00700d141c1d0040004000341810054181000b0806406482520103184c000501c80c05284100850031900c00306480340510044000c02d01c909401208032248401180a4907140c2e2640b410500280201510700c00038601e029a9600303083c00382980188004c00d056040c5820041030b5110090688241c034060543e0303842c1e040c00c0da88162020001499000152561074000303040094907040700321505405582048400141540b2461070031240e40018805861000388442c4618003924502154401700302220302c4040c0034020340e10041c0005d0006040c00603900b000c800e80201a100160f001d42101100c0d1518984082c1034040450700341039029800003442c2406500a45d41d0f4020043d002d010646018111000c202e8407500540c00341c0f240141009690380c400101551148243c0600b0000036041d038a09400201c1c4040f9550304040101200340c10314040c4200d10341101c1341210090031210791081448241307030114200d550486001e60310180f44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 820117778 1250 820116528 820116547
    0xa0609050109032603040f050705010e060409022d0a02150f040f150516030b090405071a0705010212010e01060e03030403020906030a0f030e280e060a0806041a0606 72
    0x180440c40c80060100b201d60240d45048290000c0302c8402c1d02840501c1036164242410111842c7e601440111198843c424000c681503000d0640250b40d0400101781c00d1500b402d0000d4a000380d0008007550030380d89005041c50390991002c0002110003200c500945864081c41c0754024501880768160055203540041405508403240d45460340c41508400040d00040c2140740a415034110301c074144c583c061525092103443d1010300c600d0a11000319640502291800e4000c2000042e019640104607a0004504201c010881c0904645004500c03588a0500680f130700d13400d007a80d1000c1c400c20800690800140540600c24503070307074007410352460030b505d2402e10741c000303c2c0c0e5a1045003c064810a2440b001500c070703030360801201079800d030301c4000441c6008481c58080c0291b6101c995091058042c0b140c3c20151369480281c03062003440000d000004071b0701c5c0c00c0d82294034400141460760030500303c050120714020f0800c90640a58446c7e00402d0b5015124000384c06c0f4400301800482c0724001c01c0146408 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 820119028 1250 820117778 820117787
    0x31a0a1509091109060f040911040e22030e150d020d060b0403050d08060a181409010b0108010905060307050901170712030c0303050c16140d02030301060f08091e06060a06090501 78
    0x10888181d40c100e039100d46d0b101311440d16001d02d41c00404440c0c04e107242a0f05c0002ca107c080c0040b41e682d008981843d4845000c18042490041c002020703105a0380c000801080c0306180c6048008006031407806100100c2114410035400b440310440e041c0d07000200341f658007466201c2c000082c00b000f680c50341002e081d691070a440d0900f0044120400c07941c1004030f109545e0300c81c4104003e04187c140314161902201c00320303003e8207103000000741c2e8000550000f080c1d030a060003044100801650350b482c00d07a0038001030308000c0ca03000d40000e404d40308280d000b0403540c689040036030213040c081420000282075540b406203403000903001181400e00c201c0a400000307402450102c02c49a2604000c100c50303840d0a100b070443c1c0a41849810381c2d950304a4180c050044045100210b20001026200d40e020314030016039503071000f031250700d00284c0c4c40d41d0041101441800543d410035030b42c070107941e198000e2002c4603840d2500c1038000c240030381000051000303a2a0503000ca40080039541448801d140c90800040c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 820120278 1250 820119028 820119037
    0x20c0d0e030f0c1f030f050a0906060902090d080d020c0303070c0b1518060d1205040807090e1c020c04051e0f010e0c0a11070e07080a02120403031a0a15090911 70
    0x40f1850030003007640100300c0c06a0481b0705050142e24041080d4600142c8810242c0102441a507a4525020012460340054000c0b110300ca00060b000d40001d807680c0e981d095540d84031105010384c050742031002d1080300506100540c00703052990343e5045140ba42d410000da060710050490b071000411082c0554031307a20344c1d96100402075103600b076139225035a40c030010a1858054080082c03882d8011540b03002c140d6040000f074025103204d4000c0707994103a1501d20349400c81d0002d405a1500d0360288601c3c0c0803140c03c40c2c00b0410003030b6092055901512084000c80c0c10313948181c80400720003032500c0d02640c901c2280384096074040f10001ca045025494894070030800200a060030100c440700054686440d4090424140e50200340801c452003940c2c0c51000101c0b0b0307031701074a1550029102c480070a1200c5820300076100000504a4010781544541d94182c00910240d112055448081c00c4040d5603a5510300c208002481100c000301c1a26000c81401045189142c1200c0080c915142c86042c00300584821348 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 820121528 1250 820120278 820120309
    0x3050f130f0b04231f06051c0c030b0c0301060e0607111509180105090612031c11070f120c0302280b070201020403050106050a030201120b04020c0d0e030f0c 69
    0x300e5551034908155018003011038004d83d5001c0c440080b0811604001030910180c0c1d160103101d400007103940380030000e88490344501071b07024081c221554410b01c560b000c54031915105121105099a0320390780e000880400704c45901a550f0702100400c0740c15004100c4001042c021281203191035415515542c1044100038158010f448401082485642d0241140c00d01c1c00f000b0500303400e051103644858022034090180500607551407000c00c906050036820303081202c00150146080c0000301c4480c20500c0130050381481c0d9240c0f980340d00c10001c44003000902d40c0e00d000362003000c00086d0f10300700603013201c8181500100b04850380c208400400d40c04200c4a0002e140c502201c240e2051079031003050020b920701009060000c6c4202442010340d01580200b041300d01c1000240000c50b551020400210740d9840085c2c007240b10f50a6000741d0b4905503100c01d1007204000d00060400d490301d02c00510740032030302140700c002c039804441034045454104981e40181d04100003e155450101c00132517020100d40d200d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 820122778 1250 820121528 820121543
    0x60329040b04020105090319051228050d0903020616080610050c10021234180b03090102090a08010c0509100c020d080306090f0105030d140403050d03050f130f 70
    0x125003103a02c504100d46d00b0480040484401a003130201121200c092007008655506c0f4241034503000030340117000d449060000d005002203100850003c0240180440000c0d1304006003000045c3d02c0012070b1061030401341c0617500a29407032400d80700204040080124240901038040104a4596160000000c03052000d02e012516841a101c00900c1d01c10111030038000c2d203002080d800c03444420f0a000314400e4406240c0c40301640300c003992211381c400325800f80c0d04038100760f00c02c1566000c0c01041c1c0c40034504d0300c01a560b0b2250703649407001c00207034000f55002c01340c42e500020340b03aa49103404084603000e01a1440200460030703901c2c4000d481c80c4103140800380142c03048440070550310700a804c140011134000c2d1181e100c401c061b20380b08105500403220203204001c1d900c08181140382c500500c134180d81024000300b11003429010295002958000001c203c003c04000c0440061014005542c0d08241e039200440d490030149072444c08180d0041043d0000608501864040740d5406444000d05820405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 820124028 1250 820122778 820122781
    0x150305010f0603090204020d1d061b040e04020d050d0e040f0b030d08070507050601032108060a03032316030905091b07020a0e0f160e010c06050a1806060329040b 71
    0x8500640690a04004220b1410319124500a4148009c00c9043c0007582560380c41c1c0c2c0e56020b86201c02d00196420340350300b0780a10040c00741d0000c01305001d421a00040139a86080481d03a91189800003d48400b000208d50b204440f48504180c0a11580c15290942c14804c0c0385580c1c001c83c0d66400340c0030800c4100302c041d101281c0c1c040d004104460440c1e070401d00756441581c503804c00203c0c401401c014030349200400520f90310200e210394142e0380107500040c107600b48180b03140c8003140e121403440c0c0d410400213240da00240d010081400202410468501d0507903c180c000d04024000c60072a510031401010401700301b21901d18000d03080c003040380c0c00c124100d488114500104508020680242d46d142c044002848680d40b052542940b092076295403040f0303076a100340c00440c0e25988011280740422078051440c000140c45400a5500c80b01600c4005105a201003d0401441c00c651080d165142d50304010310601091006014000b60b0019030b24038a0041e0620071011007038020b001034007640c5002e0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 820125278 1250 820124028 820124033
    0xf030f01090b390702151c022502010318050f100e120a1b061a04020408070b030405010b0a0e07020d08010b0a05070201090b1314030c0d020d1a10150305010f060309 72
    0x81a180301170340190000320458003c10503101c0170350105524940000d90100c0030250745849008948403842d038007103038140100141020444422003400104c4c145a180c115070fa00f080030b40007101808034044d0005100c4041016902c5003044008010000c241d410700c006801d01c068001203105403001005549542d409814404440e0890b00850500c00c19400c000144207014236038001e000a03454402402e04c540c103070001000201d10441c8120216908500010000b005c04400a15032180c003600000c2141128640007450070704440d040907020b400381805100000d0303810013980c00060018105140194100029160940a902c144c60100000010b00d00110791003a041c040003000d000701c02549800c038050808102c4441d50080030100c800100901c001441c00040e200001c110162800740c1e82c10079902484501603c03c0401d41d00c0041c0309a01603015260300301460711420410400140705400d00d01241510090303000c1e800101400e0030014800300e007200800508403076103404c00062070001c0e031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 820126528 1250 820125278 820125391
    0x120c0503070f06051510080a0b0118030321021e0306030f011a01030b010302030c07030825020607090909020907030507090b07060b0f0a1202040203060f030f01090b 72
    0xd0300800e0100b502488204020094000e103020703000d000d582c800d20b1802481840080c3c40e15078220000034106202017400c50070598081c84100b00c1c107150051464030a00402004984250f10031000034008d12400510380125036541070012418040640c41d05c2c6041c2095003640496160750001440c00001060140e6400c20401061b200b070b540017449910f042c1111030241e141c40c4003000f4003007400e0016041d41907109100300d0780310700500c10304182080b003140c41c11650b00318001d00c2c2c18200790b800e0114104003407142080704040203542e4001d000d58640280028590241076000204444c1850740b01401640c0d1840e040340d0101440c03900260607500c0900c200e40f814003581c030910010b40001021801d2040039081301841d1041503407901c449c000750500f4003038065480e1091305070072030b00002244010320b4150003c6804c41d4000745610071240e90040002d0a101c4846030105540c0c0d50b40100710300304224005895031007010003500f802e0b144600b51a20100380b40c0c40800c0c8901c3c0c416001c2145548044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 820127778 1250 820126528 820126537
    0x4080901211506020f07150c08122406030a0b300105091c03150509010617160e010c1403030c1c112b1b0813120c0503 52
    0x81010728440c010904802005016410115001c05210400031400f180006404400741c030000f00140324091412903d1a603c013124148071007007140138008900440d404902501c40c84111800c43c0c4018200040c5035070440007511903039030401c42c0c6c440b9000980d5072030000b502c0e030010b0400c802040c0e10341403100103044090302040015107564010b00c01d1915100d840304845111442500030801901d41c1e0301920307070b00d80e09640c0c401100301990401c504154465005042c2040075501220503990300d42c800900c03096000d82040000070740340000385030800c45900109421221a212400c03034a8558000100b0005c1c00c51080c606020744103801c1800c1041c8104095042180c00003a25203a00789401200301703c0d840703a80300c8a2a90a550098124000e45100c1c103c5d40c41c00c40140a40b4160050200100c140b02c40001c81c803c0c034044d00d07040c1005404074051484108200c000c00a008610000c0282c0284c1d00034022032264140915080e0002c3c2c00c0402d0910001c0c1d903404c0c656442c490b0b0f494024550f208 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 820129028 1250 820127778 820127807
    0x2061b0a120e06090307051504170a052802010c0f0807050915160b09070b1207030e120d140f010b0705120c1b0105070f080d06120506040b1e04080901 66
    0x703c2e010040070220200280040c948a401500c80d000503003803008482c0c007410364001d801001088114010b00c0340c2c1c0e80080c4502c21031401e116080c001d6608a000c0e0b0a8048a91780403ea45109841e1400c160b0a104030403a2a08500b00710540741072002004120b4034004012500344030000807140703003550781e00d11380e0100708117070440556071400e1000701c49108a1000c00101c4a2030000c4c001700c1c00c2d0380008a201410340341540e9282e0306020400014221a4002414041c2407603a1034001c2031100c0020701c4000756014003003201c5a640c06084d007078401214602010081940030704010300c12040400014941103402840d00180c841880f800c0c203034100b6000b80c0e100c0c1040100003840c441410800306034420101c00c071500c500c1c9000001070064490b032040090080c50500c000381e03200000350341322003d8440d030b900c0d850340090055180c03c0304912041039401c050f13955034402070030002001004208160302020315040380e001212034a56068000c900904001c0820b0750105481c0d045034464000c1100604 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 820130278 1250 820129028 820129033
    0xc0b1305091008010e0c0a05180c18100e030f0304050108061002190c1401050f03060108281b1404121506141e060d150b0403080a02061b0a120e 63
    0x310380c0c49201c6c0d6605030700500f43c2c02040c103a200041d0f149414005110541018030303501c4415606c00701903800a50040c035400389030f419130b1f101101c0c481d12003040d0f1540302c0b82c5030307250701032900041c40c1050324011601504d21403560007040b042c016640d009040603000308041d150144000804501031b0704201a00c50000922070131600d1500238441141180c1080710012400034400c4c0e490400119614801d00006414140041021604a501c112800350788040d003400580c0f0454100c9501c206000e660503c0c03403003850340300c03a11511704038448465400c0000e16401c104038100c00c04422482a8015441a09004103580095800380700240e005c141000810100800c012034450113040000d00400340c0103030144c10303003006042c003d0310600c0e10072558084c018146400c09503200030600c060801c8080040402100c0309001030780300500c10240c40598452030f40b564850044c0b110092801c10014091070003203c540d42c10301040d01e0080d00710f898003045407402c030030200c080c0d00070b070400b91600407000f02c0c131807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 820131528 1250 820130278 820130291
    0x61813020f0f030703140c0a1d0319110f0f010f1407060204180b090627101a090d06020a021f0b01020c010c050c1012180c0b130509100801 61
    0x40b280b000c000d62003841d81da00c0c2001a0030007184031410a000c00c0705c034150007000c00c11017a50074500400380034071201d00007603180880d4080500400d042000100c010454040c02e1910344080202c06000102c0000e400e43e009209d101c1070000007144c041d24410114180400c4c4288030410f14440e401035200c9031080402265510881c0c5011402903105200d0050365100558401d9604120fa010b1480354040003000d0108545070681006020003040510703400700c0710943c000340c000c644a10756041c8151031004c0d250070045d14243c01c001c041c22086140c0e4001100400200e00304d5a030782900c140341300340c00010041e01e40b440e626082c0e00d4800003030352105940c400150307000450105904200c00c602000e03401e03141c144d11804010f6403201e040e000014840d8024a01c4d08065040c1496180c40403c0740b1f2400b00700da035000c00410411100340000c441c4405030388c0c5209400f80040e90104100602030210403501d82500c189454101c0c4056000300d03849107200c803000c10799800f4400e002d80c01074014000200040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 820132778 1250 820131528 820131547
    0x40e07091b0807030b090601030e0f010f0509010b01140a030213080f0631110406171507080402010804020405040c0b04260f030301151e05090f061813020f 68
    0x10020915410002000b032400110311070b00c00d010703042c0440800360004065454032801500170304100c42c50403407a842800017200c4120024001c03032105c5105040c001500c1c1c2000c0140c01e00b910100605181031214140d070070b001103860801140c644503500c1c5001a250b021242c0411a940b1072507100402c0d034070500281024441c00818014041d60592203500c070180d035801140000c1c1260172598001a0201e1095580487c000f031f11485c05840008000060285d115040f410035451141c0e01c0d100e840c1e0000b41500d6502d09584252030f0010241d0030141401d01d001d500091641c81700610003070083d03403107038082801c20841181c4200a801e862800f640c8507a200d4200d050010580c80c4400c0e09650710134024030b110bd501040c01080b88038040e000d1460b6a0800042c0414407900615900c104003107080c1c5204480420050280300304140d551f15690b0f608088200b02d024480e00a0b60b41c4101000c10941c044410425805800d801003550300084402910784018002d01518860406000000694442 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 820134028 1250 820132778 820132811
    0x507090e0c0904080a122f0c07120b0f010f03120215150f0616080a020f030a0309060c1409010c02060912070608070207151101022b18020303040302040e0709 69
    0x10603242d103946404050021180720010f80c1c0b8000d00c03000c04103100096680c3d407907001c1c0b51100c11412603040d61f285002e000c000c2103841d0a00c2d50384213040c2054910319110070808005185600311400e140d45401e9035040c210a1700a04100d8480109180f18182c0301c03800582c000e100b4074260ba40b05203504880b514242d10041c041c01c58851855220301c032001b2074100289020820b868035442e45255108070824565240d002c3c680c41403864406503c65040c4096a134081000203150a00c842d0f6004140f200c040d00e1301c0002e5403058101c1030203200608491207501c98058060b5010100c0902e0008240a55400031610610603d10b2b082c1c0c000910250329403c070340000541e401190042d41d240045a42c6e0341400b2a02c480850280d010030700c40d055410f00b41644103514580d202032446000500d8140001c400d0f03902c0ba03d8040b003440b07402e20900ca0b64020800c00b4071810700c4031050803030100c5070741c0c4007980084c1e203a02c10b5000c002e00c1182c1d10808a03107500303401c003c2d010207003180e00c80400103411074502004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 820135278 1250 820134028 820134037
    0x220f0204050123040e0a0210021203101502010506031c050418090b0106020a030e151b010c020c0604030203031909050a030303020c0d090e0f0402041e0e10090507090e0c090408 77
    0x300ea00e8201c40f80340e01c40342000d208054442403602c0140144450030b40c200424103414000b4801144240c0885581044409000314052403504064001d06890b2005113840351848603444025a49040108603080e100801d01c4000844ca4514000e503c1d100d040c815181c130b00a070381014009404103000700b6a420120781c000c0074418041c03c554500741e83d80d0001240c0d6140e145100600044a00c0d009444608040e610000003850b0585042d0074510302e01c4004450000301c04243d81140c1d16202d082808980500c00760b20603c00683c1d015180a01310b4000c80e03038a10036044040c0f03802d01050711280d1403038820403248018041c010011042c503030340c3e030030001e000c0e4105010500d2140510b0902140c91405101c1d4034044400e031411224995659030110111100018401d0f42c0140c0c8441c8441440e01703862504150000d0120340000c2c041d0001d103056403401d9075410504008514060000022031300c001110402c40b29814004102510400c0c220f42c101038462a00a81085840f024482000303440c00140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 820136528 1250 820135278 820135319
    0x60b0406180803070201120203060d060507020109020f010807200c03010c05030f1311130e0102030907080601091a0d030c0c0308121003020f19030c030f0c0b03220f02040501 76
    0xc00440d221112682c0b03074813420800034041030240250309003c84498002d5640100b00400ca03a038050307003a84a51081d40c00c00c942450050355103040810440c030348000d40c0944040d0070711b8041860b02e042c20025100a15075203c196003019440400c2010071402c10801c0044000030b40248034031030803c007016141ea041070703030741090341080c40c40000c400ca140100e050ba0f140d5004698045100c014409014407040842043ea003039688844036940d82180034002176014054060052400ca454201d200d410444185c00c11400141403c4160400340d072170084040017624111007401c01c0400324170341515022116007005060100001000041c44096805459940040c603442030384ca55408415158140c1c040c08000c0d4403008100c24482c0c0b40c188055604054542c250180030f900752251110210a6110352084900030041002a010000c201c0300000040c1255040b203400c6040c096200c411003059982501250800281008140300d0441081d28030300742c014004010558440c9607000701c2300300c4107401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 820137778 1250 820136528 820136567
    0x360108030a0c02060a020a1b05010f0302030411040e390f1003020a050f072a0e010b03250c050124030b0c0c07060f020105070c030e01080406060b0406 66
    0x90050000c000c64989000941c1c8903040d1007429400c20100e60040d01200b4114804c090000002614225298180305c92100403d0406443c102c00100100710091079002050300500910000504a40d450114000304880205003032802c80134241c50840380b00011101088155840c0a048800600d8461011101c0394810909042d080038808080150420260009007042102d08c025110ba805003001204038074051380b81211100781e4004a4004c1c580964003c0070b00500b00c01a40d00104803060003210200e060802035107000c000d000325100500c03034400050070000c0050480d40c008201443c090910780c000494151103140028034900409074200c94a61901c092021030170350040310030341d24001101c6156092401c41c1d035207148845025007800c2804006214002d5966403d00281e1702400d070070340d115000c1e240c07030540003070940b02d000d41202c09000c2d01c01520804640e0141300540c2c0c4907003c2c01d181c007003a100c074642170000b0b2517a54401c4100e400085000300d100340d406030380c1101c00101c1c00c02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 820139028 1250 820137778 820137781
    0xf03021c02180f1b120f0a0b0303040810050106210b03340503120901030905030409290a050a0e090f0d020f10022b020903030301060306080d02070510030b36 69
    0x16a204c441c0f0076415124038417007000c0c00003502c884194442d240c2c466080703000440d0341c07004c6101003440d542154104007000d402c44500d401c140f03100b503c1214010409450b010300e1300e461080c80d2800214080031001085500c5c0c041184003a202040f130603002141109075441001d41100d1001c00005038503240303103000e24040f2400140c9180007d0543d680481e0306804510f804011030056006140440b0300302caa500080c0320005000ea903503c00c28007804001201241420214080352452440161816102e03840c3c091060010742c0b9002841700550f49800c6e681a0ba42d1038400c1c80c40d01d0708a41900000c00b6100c0c1c0c07090320b40c84aa021034a51070180d105000c4501166501005005074010800403164801000702e03440c1c501c00c40414001c0d54180030080052404002d038000ca41140c0c400d0b0031100219440d00300030848004100b0149030801d109201618180d400c0100095511800d50326580405480d0300d00008203036641c04a8100c0c45032003440b854200a58520703041e443e07520728041020000171010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 820140278 1250 820139028 820139071
    0xa1202031b0f010309110603090f0d03020c0703030311070b0705191106060907142b0203090c04020d0204080a0b1e0c12071b1b0f03021c02180f 63
    0x50700280000040800c00348401c2980110018070800609030b400c04905450320200340c039000c0042d0b00415050f800307015a40c00a5058034a040421130545080510400130440401c4020802d00c0c16254940340100e02200b520b1311880c124060798030b015184250136424000d0068220f0020320101c0e8403904458106442040250780580e09019540c006800840010740140f5000d5081a440555800c0c4001c042c0202500c44900750400c4411030701e041c111110114010b04298010580600590f0042d4a5490910303800c81d00d4013000300585004680100d0b0030340411900c2c0d01550f02402070141203500d01c640c01d085c00106001c040d188004040d1111100607201560302d2012031060400070f14091030019600240d003401d400c0208014100300c0311040900309a2460001c04011500440e1b507404d81d5880c085409020075070340c1d40030703040000c3e00c1413003040180c1300c80c6800c49503811080200da148803030302d0012410042c04030307003c010030802a2040204080d01d41d000a070080601425031032101c1800e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 820141528 1250 820140278 820140313
    0x60d150911030a05280506010e0d050d11120a1d0d030504030f0507150c052503021509060a08010e0a020313020409141c02150106050703080903090a120203 68
    0x3403110142410030800600420495000117401c0795414035668100d45103529183c0f185000d18000c00c0000b500e900038881130390f0f4002c403240690380d411a40506d486005a8909903140c00c0705110300d062016291900b0040d820074481c1000c1d401e440061a80e99522401008156003111100c50824a0090031201e40b81d040c1140b0052080354146c075460700e0181507444030800078548010403940352251040204040e8258003003c0c11a515135102c0c031801000c03e103030050900005c040c441080d0000300d658103064011b005034a0007266010b48440c102d050440c01c7c90803a038130458400395009030000866243c046d81c0a5400c070304955901101041d143c4590001c0416403000380d85020010446030b00c9000549000c1d400095400c0c0f10302c158030100b075101c403c0b0504001308421001c04041910640140030303501401035030003040c0c001c161401c441d8101040a4020301a14070090b00700400c840005070304140410441300c0744100100000081c40d03035104a08041d2280007401c138000d0050b080d4950000c50354 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 820142778 1250 820141528 820141541
    0x90a090803061c15020307020c012d02010f050106050715060b0a140705010e1609060f1a0f0c030d0f020703090e0a0b0d0501090209091906150302060d1509 68
    0x882845451070b19410104880400310320344071000200d500b02840002292950480c0c10080d00b03120141e124039004001900f40b104209130a030502041c4408041c0c0840f1b0441041340100743d403403031f050807058020710803030042c400c00b2909031013a0301d40000030030804c1c3c00001a040f114400c0610303000b46c402c82142901541c0042c42044070030344051200c851190f00541c10388009603a0014000d04103040c5880700e5007541d03d0007981c41641d4100850940713448150f031f1b8a0b103018007000e103024060245410121005a042841030301c0b01c01441080d1015113070708681c11900040111a06240c503002e9080300b4a460703601c03030840c00e680c05141001012080740c90780242c69095406490300c4194610304048062120341c000e01943c1c41c00d554200118a540d00c0e2010f1060443c003601c00006d64025030710520000c0d000150040803c5c0d0700c9110342c0e000140d81c070034a00c040703503600103004900880c9108800d00000c00c00d40000b54422008110703100748289d154440186060300c065255507880d5200300c00c4048651 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 820143884 1106 820142778 820142783
    0xf0b0a05210f04140f03090f0d0f0c05030601060906020a02040b030f0a0803010302030d09030b04290a0f050c09010203162613060e0901030b0613020a030b090a09 71
    0x5100c0c06100351444107030001c00b0303492100c1171007a940380031b007121861040050684100d002e4031140018501d46502641c11003d0344501c0c681884041e4503406542c1c0070713220301c0000040640c4203030120000c607400c0c0d8015101070138040e028080036003074884445406210310101c241d1000030801200030300c0c60052000584a50440c4101405e201f00c0d409180300308140442e0910200780e01803105070300b059000c075642c90200c0188050350302400f40c21910b101c014500c0d104020303550405810400c001505505e0030009aa02c1c07110381842401510707403480c0141d006010300418152424085224103005868100010000707030740d081456009002900e0360080301140007a02c0302051146a405030220342805010403e60f600440c50507801440b01525222403440420002d8aa00c3c50300072848209400940d502e0300b0354031016000d0b1800100c4107005111100c000780141855100b01c074051035 = true := by decide +kernel

theorem cover : BRFrame.Cov 819964028 820143884 := by
  have h0 := BRFrame.cov_init 819964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 819964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 819964028 ≤ n) (h2 : n < 820143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
