-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:49:06.211209+00:00
-- url     : https://prove2.me/submissions/bbc4465f-7eb2-40af-b9f1-d18df16d82dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 752877697 ≤ n < 753057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 752878947 1250 752877697 752877703
    0x1e060601020d0c0b04140a0b0f0a0605180a200702100527060d050903030a050907120201050d060f06080108060f130b180f0c01030f060506070f080415050a080702 71
    0x20320b8180d941e2040300000c1e40c41c0c00c202d941020340b0440f0259410550000d01410501602d010f0f1803045058a0a41c10301c0c0024034400704014060b07000e11445d1040400c030310381e0382c403640b04840741c0000c14401950760340a05140051801042580501000001e00d880c00c03142e0130700070202c1324800c0321840c030443d002c210700f1221030190342450f03500195000c0c041c034110360050351080440c1c13000801b643c1c0b6048003035200e5029102e05a800600a41c800300501030050070a00407264800310480041880340d250024890816002500107030500000050f84602064242c001030040c150817404502c800d0f03507441000f0007032202403051050a0050001040c102d40e151031555010310007043c01020420402c0d1902140c0800c0502001c100864041e22000902001c1c02403070041680c06c0054145010030500250540304035098564819141c01d40a10081c1d03203000c1610300080d080361003000c0192092034401d9051144d42c2083d81d1f4148500030304003150394040300408503496030f5907030f002c800c0d120284140d035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 752880197 1250 752878947 752878963
    0xe0301060f05150a14030a020405150a0305060f0102100209030304170721240b1002010501061209080307030b0a1a130902090f011206230a080d091503020c1e06060102 73
    0x10001e854124104242c01880011b5500b01c2c181680062a282d5120001031136100179401500301690007054030202e082d0507214103580500143c44021000410000007511035000000384035046034003040b40c1070551010810703200504508001f01c0c4440f218400000c0d0b940c4014410b507440711440e842000481814580c031681d0203913021601c03070f41d850b8540400421500da24031144005aa6400c10800036584409000c9a80c10700c41e000081d00754149080100000520038010000c4c1d410136003c080020364035011250b21501a18001540d00f02880c0001c0140f00a1b80c03100d8808110840d000d80111513090042c010800c22440c80d09641c1c0c0c0e03855041d01a40038210030ba80d4400346400e5144025401a80da031007684c0100b80c00082c21685440d10403c0300c2040c42c03c0b2098080703c81c0c00c0d600d81402d01d448a280901986002414814003a0b00c005000d401540101c4100200840c2000c40150194040c0d8a018131850150745044480301f07036080210300034050b400c64038800c0c00c000c69203550000c14400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 752881447 1250 752880197 752880217
    0xf0c1e260901050f0d05570c03030406141302030604110a17070503010b0a0e0711010914010c09060816230705031b0712060c0e0301060f0515 62
    0x54180a11140152600c0d08070107600a9102400c00440c5489142032248510405a44100f10703114201c03040303842d140744050a01a07484102854010b100352900b04940c1f901d152481c00c428041c80c50030081c051482c040c0300504046440080180400c010070354100400001c44e481e02d600d07156503003010341044001000406034058025a010030082a1300c011102902240034022614041e070b00c40e000702d01c0701c00203116030800d50005107042c046440c00b07000d100c2d14207004580311001e035810502c1003015004060403600a1060142d02d0702107025081d00055602a0441c9003103207078051803d681c9019040d00703100c03140024011030700440c40724040ea00050160124030b0103110942e8040205a41000b400d6800c0c03a0b00c0000c600181c41460b6200e0000c120f0240b250002d55203036055840176004076021420b11800c0c940044900380a686042e1110654450704001d01007021098808d0583d02014104030964065080401c00b050645480d0680c3c1304940d816200543c11000721740c035164940c003800c1091 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 752882697 1250 752881447 752881523
    0xc0e06010503100e1b0406030603031209080301060c050c040218010e030d05040b0705010b19030317010311090c12161220090303210a0f020c06070f0c1e 67
    0x5010304044500c04c19404107101811000300e58a000aa10340360300541c1c81200002e488400c24070415521090086048207a250107000130b502c0c41c0e82e855224041409007404000d40b640e07001092240801440041502c090011907448418034400194804403d4070680481c00c2c01d1964511801c00203002c01e601910f56581e2801c26007030180702c40c03065107d000b044d40e50390b4868018030400c0e92056601e10f200203400c0b0a05c0c25031484c51501801c00c81f001100002003101c1d0300010000b14000c607a203020b15101c1111009129542c172003000300b181c0229a1150384c5101a00c04002c0540c4114a00c0400e0000359101d8541420f6501c44a0055a000f1402c44055a501c40c4001d00d0205014020702400407000301541d0610035074014030214120b54003030944580c1c04d04000c0c04115451032003050f40c0f810380c2e00c0d015894072900010042c0d03aa4006040c02080000c03416001f02442d00c01c0307100e1003880758000c40950030101c50480c01050060035110a03243c1540f2811020f58a1500c00e032012803801c40ea00003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 752883947 1250 752882697 752882699
    0x51e1612020c01021005060105090307090605010207080d080703021b06040c06020c3a17040906060905030a1407080f03071b08070915050907020f1513080f070204090c0e0601050310 79
    0x1480b0b020f0500070746031b241400b405002b251015603061007024082c00310080c0c0012154900800249001c3c41035004513100c3d0881140805210350054003e903200005082c0942e4554101030074070300c0c4c0c07201c44188007154080e44050004016101c070301038040b561079900329558200b0200400074022a04c140f0950001d0034140040c400803d00038080540e510b1001411000000e41d460b00700200f240c000e0b15100c00f1000050134822540588038040c064030503031500d04407150800b00070035030350303084030f08054025018460340c0c2854203800c0107090090a1800c05482020503100e42e00b5980e90030440c8101c65010442031400c40344074584107420b0440d0785090040c1040c030b02c0c14900600500240b03a6803030f01600030b0480441c40e030300d83d282e184d8000c14540e8014100d040101003607505000703055002e03855106840050203c0c0d03c54802401c4207036500b102e28250755801a50710000c5a1146802c000d41050411030902e0501c60200180011a01c85600074240c03a6694801108d003840101d030301c500744402c2940 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 752885197 1250 752883947 752883973
    0x2405100e010210143709080904050405071707270b1f140c0703021003060e0c07020118060905060c010f05010b03091c080a0f2003070f110706051e1612020c0102 70
    0x1101c86c849015964861900081e040407905460040b80d0694050340903240400c040700004c03a13000300c2d003440080074180442c2007005410b10a4040d09242070103881015103803808403540e030f2140c075080a00a0010ba4503c80948402803414602d201c41130101d585850480d05020701d1000310351052074420080c041550460f03080003010130880c4441410141d40d11404561000030321040c43c0500004c0702291f86032500340c4001859222041d00c605020b01859108102c1c00e5003001e050810f4400458410313485059040c1038500400c5c4000148a10b54140000000c4a84e1501d000394081d00c40d1006803060b411181d00c00c2e8083d100c15036080400100c0382d80000740d007103d03a03900c01042c50300c0d41e601c04100e94900c484200d800350411b070940d0800400010a012045400c803803031a9501900d0b0600300100b075401540582c80745414400e420070710000048910b010700c1c28103020030084041c0e0300c5080e00c820821290341c0325102d290400712034610891300384600d814000144000a00c00581c02040c1c2850151 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 752886447 1250 752885197 752885201
    0x911010e0d0b01031707060629190f02010e072301110309211527030d050901060f09020c16260c0d0302012405100e0102101437 56
    0x90700303a240c040051003258001890b07130123100c004040c10140038013081025000401c4804205110701117610702004640740750800040d003203d4403082c1d0700f042d4500341da2024050340906509011110309016100e00800e8440b024406640d600c00c00c80d40d22064002004015284520b0070102c64100c1d92050010280e5850b0502c0340c1e080090701804085a007100150806107030242c241081c0003e40c0145040007500d6078001e8207511440d04084000d0310345218a180c0c1d58983c4038801505100da901c1303000280120030250807143c02044c0191001c48550783d1016604000d410030b081c814043e00070001042d00e0221000c44040039a0604200f04000450401078104400582d20b6078000328002c40320225069920003c0841d4403034002d40010450303800f0418100300305010103c0d10ba49100c01d001c0140820b4844034000845200c1d14280840110312020050b40303400094421001c1306403c0c0b4090303400d04410418084d00030b42e401e59030f1181e01803440c551000c1803030003403100207a01e50240394207040d140955 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 752887697 1250 752886447 752886473
    0x10816081905120a120e06060109141807020f01060f0509060d0609051f06090606140304110a030602071b03170901030b0901080a05060903030403051b100911010e0d0b0103 75
    0x81e8003200c6800d00c80c19580d5055030014101e01d130108804c1300300840003e0f42409075480320000031001d080d4900d407601c000b1700410700074015805240421200210180c60f02c010342582070365261a82c815070f20f0b18100c02569166401c580034241e5090040014000705052605c109648004203110b4059869109100c461050440c4c00d40b0440d45881d483c4020400c148840510940c8070b440e1007200d071400303032111015204964040140b161130007208101c1d05070301403103d440880303c005a040d0742c1c0e02c60b03050803100165010810f6038884092800002002120350003400d446204220103003504076400f0740344c05458990710000c1e040b440e142203043c3c400041070380249150541414000307a105030110106207103180c00d810119041d80065002c40903c641007154960080e80c0c00011403540ca01a03400401c14014030f40003151803885c2541403025890300b8000c0040443d0721100c200301d02c02050a0150109003010402c5020070840c548017102d43c01d2032960010030b0390700099103141603440c543c1c420042001c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 752888947 1250 752887697 752887703
    0x3300903022e12110309060109090507081504061407020a2607110306103005150709151409010e130e060a05060d0b04081603080108160819 61
    0xd14001020b201c07040450714080802c0caa44102c0d100720410081d008544441d60703464000c0340180304021034290b0005036203065070074142010526044514041d8644600b5801000b428058500001103141622031002d1103070307010320024084641d00c0040c206000e1000c0c2c7e0f1020041c4c0000c4801804900d0482c0a14180d0181091038441c46640b46413401e425084008112010003000b0005002c41c40c0c20842c443d08410403040074446145001c0d0303210030282c00c140740090361040c0030540c500030022408915040325004415940001c80900c01180001012110200854800311002c240500320618907464100c8a89690010030344400c0d0320141508142091810000e400001f1022a00d80c2c014040f000302c108880447d501652071007441c1080c00040078044800d20b04820000c2e01d950742c01a03100c04a821904560300f54a45003052161031045c001d020410400341c070381c610308055008040c1812030300e4605c1615842050744210000e51203951144141c00e030300c20944011a01d009296003054648 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 752890197 1250 752888947 752888989
    0x1120507050c0f1621060b01020a021509040e0705030a030309060603020d0f0b06060a09060c02010e06030c040503071a070201110c09070905270c160501060330090302 73
    0x203500d4a03400d1600c00c00602c0f40501e0741022031907140703413501c0000400141041012107007001420181c03034001d01100e040003614294440d41d1540d01c2c4d0340240000c5101540282401c480b0414011481d0016446042c02034002d924000307003864808008180740b802c2e00d00007400742261040a1300d040307014185808081e07450980e07130303a03000005a40701202ca0408603c03503642e000040e8032a0400820028009120302d0007002c0410000d00c0d040d9011911805944507414426001c0c402400100e6a14000e40c40d06031308040300005100500c0002c45c003900880d84114111031041e600c0d4000c0b01041d440e02184006000705c01e1142100660155850f60400000c080c211a041a10134001a04100b810354a420101d10302c0136050241781801c4141030845c3c8030010b10401140700b052034030202d900005101409000000c9030b0705064400c3c0036104021560040000d00480f41c6904002d410000070104003100c8001c0d03200c1d260711009003007294403064401030f12007401c6245142c082c8620f00b07d00d5082c10364602 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 752891447 1250 752890197 752890207
    0x21060a1a0d020d1407091202010c110d06020c0c030a021305220305071103031c051302061210062c13020c010614041103010909051f020304060f02090112050705 70
    0x40761020b014000f1014074042010700043c150240020f4001e0100c10400202d01820701880922401a0407041c0d07081c40d00318880ea01c107003007104500c1c44030003801e9070100c81218141c091010300d4000c0c000e028880400c0d12403420004040681d101b010380c0d00203402c10843d1850a01c0001e442c0d0210340e10484030117040c0c20251442c01201071a20100400301c0200c2d2012078200c0900040341404445901c0079001140341542854081041e446001c06800d4110713116000120680d203510010b00c50658003410b500d4443c1010f404441003810200d4403080821890300002a549125002c00ca504050f040c090300c40784508110b4910007100070444150708100300d002c1c0003044602c103100038400f0f4011600001005c40c140b0f0b807102c0b0400344581c0598421402d01e12840c1c1056001d40480b81103e01ca003030005104d8409180c09410200400101780d15110714038101c034907460068009500c83e61007084104000001d00c2410f10482c014901c405001036020003406103118095400280c0150607414403600705 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 752892697 1250 752891447 752891467
    0x2e180b1009030b0c09090609370c05130306050907180507030507020303100501230a0f080601020d0c030e19060507030806040605010f230a0521060a1a 66
    0x1490044103800001d101c07800070024815a0803002da044010781409a1802030000005400341d103029180030301c540f00280204140703190f81c4407220b03080c4420307605251074081001b48415400e03041e401c050994a00f040c40320200b0b01d02ca8401c499841c0c544039001c0802c0b43c11030701e803c8020040144030913014030413040c002c500f5519002d440c5000d9074200380c02065900c3c280c0310003801d07101d01030045030a43d4414001d110060004103425400c0c2d407420720700703680700c8580d1b800011201c0c0311480249258880004081c8601a8007100d020310300c800e0354032401c103142c903044012a503072403020f10540d00083c0322925400010344250b070b461f50329600040c0241a511141c4070a02c070340e40c0c81350780104042000040c8940c20143c000d0015640014110307001c10001d860500060b00240a903540c240400038003542d40c4060350500b401070414403044080306901d40800d4240035202c0d5101d484d42500b000c042c001c1c05843c00000303c80081c4122005021240f83c20b2401303506d4016040e01020300446000c00740184096 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 752893947 1250 752892697 752892709
    0x10b0f0a091e1401092108120c03060907081303080a091b0f0504050c12070212040303170a0510091a06030406050103060e0d050906030c0c0609062e180b 67
    0xe04400c1907502e002c0d4624041007920a00c041e0b000b524180014810104130304898000c1d0210340e460301a60b003140d04d40c81444d00d0306041c4100b40c40b80e8540c1d4208000e210b440c2c0600c1c805036100e464140c800103015140d000040d50b0b400070850300d144c030b94010b4110140000344510f01031070300501044408141d4015903a034100c6c2c440b070b1000b14254078000010080100344c080d1326000008040545082051307083c003030001200361180c052024110203910b00410b802034400c221050f030804054502c9511942c03203180040c21104110b6030f680040d00f440d004980011080c0c45001e00540112501106541c64606030f10b0180c655692041802e040e10102d180c1262100c2000358482c1740729032000101c1c1d60552034044215841400d820084c0e5220741100c001c1550000211031200c4412a1032945030341e50022003031000c1c0324840b1349004c1409580c00b4043d0310200000c045000c1c0319080c040c202440654542107040714035400ea009001c5000394030401c500a6440c40b00c0d112040411000710300400c0d42c50204134 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 752895197 1250 752893947 752893979
    0x1602061315060b160506180c06030621030a02060109052214010c08060a0b0903030d020d0f0c0203090312130608040503070602030c030712050103080304061d1b0f0306010b0f0a09 78
    0x3150151180d001d8003000018408182d11039407034040080c01599420046a03614030f0234003094014007000010520540c1c403034031f59400e1a55031400d941c1042840c05003031038590300b0540c42c42015102c1c00e0000b06000503d40281132180c06012510003c890004414410100041070b043d604044050581d0070307080f03002c1c05078410400399a15070040341d003403550a120b4007000aa201c21030140003130020704001e07075010080f20058003070408050707110301e08200384400904052100700c011030301d8010000d0700c07150040058481c110701101690040300e01101d8410440c03091400e45480050306140900550b8000c0741500c2d0000d00400803a42803000942e105022030b0f206070f6440c0410030010042000071940440302600444084000b4080ba5140d80e03103800c9076020141c40140216103a4035444500c440b03171428090403010040071a0004420910010081524406464098023040e900f9014034100010900d04807215410f125280161500500a003034202c1c182020404c6030354100086d00104480c0851 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 752896447 1250 752895197 752895217
    0x190c02030a020c0306010503060f18010903110c041a0d0503091305012c070309020112050a0c18030c062106080303010f14010c080906040b121602061315060b 69
    0xd03035034030354a940103031070100c8003000c0c20704c0fa9000384014003480d100850f020750072009c402c0c42c2c0c2c581380c3c550f071071117034181c4060040300c0c83c1a41ca0217505001b4568001c2025412103104415660409031315000d100558610404080403280400082c04aa0901e03101d4454400c1c01034083d45e05141d103020001d00312320710085000d419141c4031401441040c04419400120b9000d003420b07000003108440c030b0500304910041c41541410340c0d40f0110019a40601e0b0030503840d2010310020405803601c0c6910f0740c020305880700c03650002740e445500300860890307000d0641c066039001801c0300c000b1464508215030306030380c03c5403030b011150741c13043c9440e5100f0841c06080041e004002c09180c8a60405040a0703454800b0f5002c140001c01200b120500c50340c0144520030f1050300700d885684d0750050040400c2140c0700d580c1c0b004a1014000401c00342580160000324025240c54404840c80040c43d002284da400e8166007141e807000d407a40a0b030000401807084060040c140300c0f8007203400d81e0b640000c03006541044501e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 752897697 1250 752896447 752896453
    0x1509070513060e0105010518100c051014240411040b0a020a030806010e1f05040f0603020d060605030c0a0c170304060b0307051005040302242b09030e0603190c02 71
    0x28000e07520450f0000b80500700078a4454240080304031031403002c001e00f1f41a44d02406449803480700c42849200401c0d00c298100045511080400300e200000700311f4030384000f8414007684080707100c11300801540701180c42000340c0010821040c10400005081992000c520b1400c200000101410760b100071305008100e42d00940444005030801501400340145690304102903858044030319a681c02910710341062201c020b09001404079400e032a10b101d02d400182d83c200c545000040d403164150010803090b178188405000c4c0560b5500c00384c0d903600055550240030340080c03004040e400e104580d842c0c0c9140c000c40300c070040032461501c06006079005560540381280c9404030008582001c014250050000340c5001c2e00c2c0a1040303030010094029800003c1c49070340844a9000744a0928841c2a400c1c60780045042d550039075500101c00c14618041001001c0300401c2c1a40c4c03d891152146040094054a07464054102c90003044890340c0001e0088080c9440700e0854540d4442c42d110749904a0001c1d001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 752898947 1250 752897697 752897699
    0x15012a2108011a1603030908271e060c0106120317180c1002011512030f0207180c1b0b0a0b030102041d100b0c150901050603150907051306 61
    0x4010441d03001608405422180d803e02400e03600368103011500044100c1108002900441c43c04402500c8083c3c0c020304109004180d03241b080c002e8400403800281e00507a2100a024000c0030300c10b1540508c46200030300401c0c1001030790a42131640007898800c44440000507410f444000d1180345c200d0098081c0c0000b10881e10406003040c0c042480d6801c400e40543c01440b01201e410130303665400c0c41140950007840c0c062022503046000350864450f4202042401300c0d0262a140b000c00c0b00c01c4081c05c140c000507c0040e142626a00100d013140554000c5043c1d20401581000300401410060003880100305c5c082c00c0c2948040c400604d0218943c2c0301d90280710031400e10741000d209490015032814800e0748104800c105a450982c4994607281172040d2060b0296520303c40b1010000c2542e0180c4211540010a4044044045000350326844143d800402a845180c640d07400c031003040700d605801d54040048001210840c00d45140d03c41d60b91411200b1464840001c00c0340f0040300321400003119251a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752900197 1250 752898947 752899013
    0x70303050405151804020d0e030d0c02010b0a1212120f0501051306051c020418150f11030a051503160e091603080306060d090f0b15012a 60
    0x1e0f10205200400c0d070024246550302c064050f030310b60724402d414072480d800103500560038120b070050000a4040d405070307074403040900c50303400145c001c03a0045d00c015444d151440e1000c0c90004506e03c140c40c084021680e88109981c1c80d2030349640c051080340203003c001d0003680700c010114000c1543e0184132103c003140e50352509084c40740084d0101440d20646007040c0003480380d519803603406419003292203d9440036444074000310b401070000c1d2180200c42c0d00d45011607070611509500c1070035041c2d41104204000910314521404803070080c140042c0045007000420380305d000302d4002d190080c295141614004070a00002480c120021a41e0a000c1440d242c08002026034a10b00c1e5501c1202c640c0a042403503d912480d6a40c6180360200a01d43d00e004004240180c861206607030780c1190101c82000415483c1c200341d0303e1207403c0c802c01c40f480302c00f450008c2c015244035a0400044c100685810b903040a6440315042c0c0b180f2200041404500001c9080700410088101050124034000c02000c000c0c015003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752901447 1250 752900197 752900209
    0x12090b040323031b0f0f0c070e0a11040b0a02070e070207031406060609010f11011a130608060a02070f050a061e02090a060e0607140c0a0e1504090201090305070303050405 75
    0x30350b604090303a0061040100350803052020340760801c0c4000c1a540d65100311005483c20340903e811038040c5c8074011500040c040c0c40064090141c07615409821a00d5959012610540701c80b0144e0001701700050004103c194240d401605175080305006465400da1986c0340015a41e10803105200140e120520400901400340078040e03140910700060005850304101040041c403840e0446810000400440ca90492048840e040f0010341c80c0020f1042000300c0002a280e40c2d10811541c0c0b0440c00d034001056913460500c00c85080701c02e5000500103a0b95004140c1c070081d00301c0807040ea001042c040c13081000860502405081500c11076000444103240601c4441400390191100c8840384100100314555440b00381400890f2070350720705149102c600f20040f4a19001700c1600400c40220000448141200440d40001c0c5140c1515070b50310700d9a0f61120398140c90303000d4135000a408100012040642056008101c1490060400d03e00d038545d00e0766100d1030415560b1056001410215041c480b501e440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752902697 1250 752901447 752901497
    0x102f071806151803050105073f0f1e1506110a0803040303060e15010807050906030118090510090308100501120c0e1206090c01050408070612090b0403 66
    0xa0004001160820481900c20081d11801d80184407100540c800a0a414032100f000b45138840300078012828200c0e0090714a0300b28071081040390045c840807030b60328403505a00040002607001c818452400c0440003200408080b01d07680fa4440d00c44d84144011204000c0c00c000e4440241c0340050854680b01d040c0b005051580c2201c810041da00c9044005110300040c0200e401e0b800207580c694030344861400794020502d41c0d1002008020318400c000c0b55500e0343e071200c40c648000381c80e80c1c80d06503079141c4204c0d0360748100d5014a45c800010f00040c000d641c0c22540c0440b1a07144024000317500141511000d1900300364200c0601007a0302d54040c0d800701580071140640040c00c0d0582d4500880c101400a001480609030701d60005940b242c02d50074180c41041e0740c40050002900204a4907141494591109000c4400340068810000e00d00101d5201e6030407a0104d90303070080a40000c9082101c110740000d000401c00740e1150f143c148bc0800710300000b48441c003070340c1300c1e80790601d165280303c6004000f070ba15 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752903947 1250 752902697 752902739
    0x903021c0203030301030b091c0819060f030311251502191104270b010b040b07030f050409021902011b120b030f010608010b190302102f07 61
    0x1500c00d0403801030701c0c0001034905590384071910b041c8a650708440b151034810b503010701d12608510174488a0304140c1100c0114001c9604601002c9200180c000000c1070350704038403071000c8601000c50204013080c03044a80c0c9480c4c000d180c00b80c9440b5000702140e070091034080040000d40394400320042191405e001c6108000c071b21140042c0584003180d40c05903100d00d40f00c403409084160002e001c10a1642c40c0e41c072102c00c090f2404070343c03000c401510001c07c0c039044161408031170240d139010020406032684401e0b2800c95180c0800079183c000e09a13801c66031f00c40c40c0c031820014402e0600012840d04882d0026054803038291660300035441500200a007500c1000e208244040e01d60302c0c00d140e501390f1010b4220010100c500000c5040315000b4082854641c42c0b100481040d4a4018040355450040d044410508002c481401420001115407841610b091000940c4a44000c01c2c1d43c10781d60091180c0417034040c000d8a55469284c484000c0d411140c0340840b400000d4001040034020116011050014101 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752905197 1250 752903947 752903989
    0xf02070e0a0e03190503160c050a02100909090f030306140d0809010c0615030614010e010e06010c080a0c0501051005031b03010207080414030628050903041203090302 73
    0x2140100038140004003070600d0085586603103020481250420488001c0c900d09032501c0e100c00c1884100610300d41050764480030740130080010740c80c400d2244c2030069050360000c0c060714240340d0a40c20813040c07941111002083c04083c40c8002011807503841050a1140034102603400c2c0d040610380203088403c15045600380384110600c08482e6240c01c4800c00c880c80d440004181d441054100503100c04210441c01000a400c1140450610000c0d50015040300c0c030806060148402d4100c4c04000c002d000d001c4e100c11a03014100422001e010880e0071a0454010b041941d20744000e41c48298465002d1062100491080c4100d0001c00c1000d11aa0760b00c04403101c017190401e030403c00002d07181d00040c248440c460030002098640750ba020f504036500280e000d06141d40d0b07181d0741c2060341340c0c680218903114428040d920020b11741d081c0e5560048240441a04201c944040c0030004400070300001d46400614403040c000803e40306819801034401a0003a20766400262840c8104503040e44415408403002c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752906447 1250 752905197 752905199
    0xc0a08030702030d03060b0a0e0f0a0609050a080d020a120c0b04030f0f020106080d03023001080c040902010507020915060a030e101802010f14030c1b3c0102040807060f0207 76
    0x14803d40d00780c508c56011851724000c10031020340051281c2c240030710305681c070001452002450541180241003214019284030141507555160303030b0303201d02181701c071030f00940c00400f8510b0000e81c070104c290321543d4150816041540194452130800d0f2070484085010a26186210241c5078000c601400d245001d4030084c05154101448240c5500303d06028000345900031500b8400d01c4a00e05074607e41300d0021403501c000d205c50440484281c54207110700203850252281400040c01e01e4000d0000d000d4040e11440d2500f0459070134440c00001c01800a1440120f0507052a07240d65004002e00c0380ea03901c3d41c0e012074903041524049050199140c03000103814a4038036410340e00000c45008000660302401c150070850b118940540f00c618026240c0c0286400c00810008030090b13050191030303511444040e80282c106500b25450ba43d61196591000707040244951107808917507204c0c2d6980ca40c205020040c40000c00881c102d00360381081c1c10262154101382e0051206036840201028002d5851008140032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752907697 1250 752906447 752906459
    0x1c080603010618090c170d1e0e090604020904050411030d110a030e190801090c050105120c250b1e0c0405010309020609060d05040c0519170c0a08030702030d0306 71
    0x1145915440d410660301c80c02c4080502403c40125001000343c0041841002c682d50b440ba1f84810305150390b50b01040702c031144000000b91025002910070001c0e160851020858401c201d01c10800030003450707010341c0801a111042d01c640c058075001b81e00c030f02c69008401c8036440401d4104503800321960100715010200568242e0300180400110b501424000403011228011808d1502254880d210440f183d80000074019015070004c0744260107156110403464071100111518450406c2401000d0001c01c042404803181e1b40041050060b481c0b038414100c1c400301d0800d120100641d40603a40341001c5070820045034000300700000d04402d000e2900e0705502c0e01c2091415240904d00905041603952180070003151215400c4407d030200041016840b01c0901294502401007142d0403686d41300460400038490a0a40d6500202080443d09084990404680703415032041441e459002d4842d60740f103d96075442d0481241c0c060320303207000911f5881d015401410701d40411602c6c4c600400d450003008000d4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752908947 1250 752907697 752907719
    0x8030903060a0f110f040807090608031207030b04230105090c0a140f0c0309010f050901050403152307141201030308041401050a06050f15071b081c0806030106 70
    0xb000001c52000600001c5190514008200b03200c141120f030b903000900800e040d018540034000310755450b0b0845a2482c0c0300e0b4000c0701624074621424403690710500295240c2c9110310f4480d41e2010540c5400124a00d819000405842581c40701000d0340e200d070590b4010002145000d03072b025220607a0103003914140010481414451403980c00d0404c03408444210f00c2035180f008031400b0002c940065900c500c19211b00d503881794003c6591070302254002030720001250003501500d500310016154582064619225600c40001d920300403062a5550036610880c6086155a00c3c2d001d40c0d581844103503860400009400c0001d101d01c3c00300040018462400e8030000011410304dd242e1620744800c05445516088407007820700c50141d802542072000708041a215a8003c0080f500203d4541c0d4041800d00705000103060302e2001c0200035001003140201148024004500d0081444503800c1099a204640c9080815514941da4540003512101c400741d64080d17100c0e5040b4808400804c0010b15040c05461 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752910197 1250 752908947 752908951
    0x80415032007140703211e26010f060e04020f0c0c0118030f03050c0a0b04060b010f080903031602190b0411120c0906030a0614010e0c0c0303130c0b0a030e070803090306 74
    0x18007075081c4806c584172501c240f0204d84044406030011000b0300a1040141020f403040321b280201c41c0c101045c1e13092050f17024983e98101c40c1c4ea000711071145801c00038122410310040c07a619800a03004c00100d640301e405203005080100111000e002c0804001d0001400d040b0b01581c0c080101c40d45480500c04075025107040c11060f070b49414140e50703070b400c0918140d0030540000c2c4082e2040c803040080005100d0760360851049090301740d0fa415403100c0c0d010001da81580c4296030040b8903038828000a0940360720510402c40d40d1050380100e80113407051000e40341109112180c115401000441840300b0030840c0c1d4205000741d44121b890284a00440983d50369500c0700160321441100d080c00403e415480a016202019800610601c4644603200e200c1400d090280703e03084620070b00b60001441e03070900d201940d805642d8076000c4d61441c0c40321703a4118844071500300d003694410a031010020b813694411006111802c05620003103102c2c41c8001c206400c200d0710b40d01c450030030b4000300100203a90b40c0c0420225 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752911447 1250 752910197 752910233
    0x50106021b01050d0b061812030a4a04050604270c080109030816081303080403030213140102070f060207051201021e0c010506040603080415032007140703 68
    0x203500d5146400046014081120000c1d42003040010903604147c803c030a1282d412005582040003d25030300c004130703600e119210705000010141c076000c2032024078408201d0081c4540400c550101c410400200c0c2c84900702103074400c0100503000101000e82045d004055005c1e0007200c0c20007882c2c021098202d071204c04001e42d10078040311024620b04104d0b40303003101c00107005650300070030900c03030b0354130b0050b0801c0000d44074088080088088450420300c1400781c544600000d0600c1c2c580400c1e0780c0c2c0d0590b0f001c40058001c4090640906c003080c8030030340d01c440000080140b1103801000b0300c608000a4141407454000400500d0944014130840e5000201d040c125072007a00c0b52941c000000c1c0310f050080c0908120340041403014803051071030000c19009094120440c1c0e000700020384400d000c02044540c5488010002c1c0c4080c0020080b40c034044200c45544071080c03c002c11a0a80301540d01c901010b0021801440030001c14041d042c0074044034000703400c0b4409401003200908544030b02c802140002101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752912697 1250 752911447 752911457
    0x70b09030c241522020d060e13020d030c060c1d03060f010b07030909140105012607050a03020c0109210306050d290f150906010e041d0609010f050106021b01 69
    0x220100e138403540352144100310360800c10900d03030f41241810000303540a61804031149040c4003010854500307000c00640034240c0e03100c050203441056800cac40302031482c440068003031044004000700466024061180d0104040e611107000301340c010048101201c0503c441c1d4000e03840801004603075940407041d181501e42003103c064544040749421101d01580350042c00805041062031198528110005ca040e558240c81d803031481008000071008254004070100300040d44a000b04800c1400fa00041c00801124a009403525031080711080c2502c4600c0400c0310021245d144084d001e0785007205102415549207000d02036985488000b8480c00802c001c05415907440d48080420700c1c2082c002c2d0300e000e9602822a890030300d400380c0d821401d55001c07035407840b41c1007000004502500d0001c0341c9501c5104d050311076035403541c0d0010a010091046540075401c1550407016000c1e40c0b03100b001440d100351042030000c98058483d001d03c40075500d0680c0701d10700750362140c003d0b81c01404500408940710340c401e1800f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752913947 1250 752912697 752912731
    0x9010f0f0216060b22020301060207150f180909030207031407080a0b0a150e0103050c0402090d11060d062601110415170a0e070515040e0a02070b09030c24 68
    0x203041c1000712000c09420302c08040c41c000c12000b60340280d2304031800f5809407089036503038110701d07403084600d41d031a80001900741d0340c0341a11300d00078000000c651403800c011290042e110408442203c0140303a0a81c056070040c4010002c00000c99502182069424040c01c4220b140124055031041e1100f130042c01c0049450020b10020340d40e5200203000c80012416401180e5201404d500303002e0280003d076521b0061842d0010365042c0760084410600001c1d2910405403001e840f800000c0d102c051110f46e10107420070418803401010301945015056a1000c000b0f40e401e80c1554492445982c41c0d01e034540d034100b0460803c5001090140c40440f1200c081d1040c0131102107200702c40c5d841d200b500088072410b09900703002001c506640a1103401c441c0f0401c0782ca8442d25803080000c450a4604482c680203406c00090085e0300c4101e08a0360492240503000d030401c481c1c1d9a03103c000e15030031510403040381d10101e89842d440400b00160b1035520700200c440000e40351030360f045a01040300100086044500703d90 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752915197 1250 752913947 752913949
    0xa0905060c250f0302130b0301091211070f0b0702010e10180e0f18011413030824060f0904020714071401050a112e06170a030807140309010f0f0216060b 67
    0x94087c601c80100204404112071420711000c0603a1044540054011030f031107404100300048060613a0700d00c28031301c0501c80c5826542c1c2500c1c0e0180310102d0400140650704005500c811981140c0d00700c0c6030711340138944100c10034280700f240029032100100781c2c10038061040950329400000c0d0004076941001d40131100404e9001d0150212154420142c0059800c01401408410300550458031039914000980c4a12140c4450761080031040107072021029415031840c90b000700240702080790002100d0034440c0b0071380010121b8000d00b8050b03415404803424000c64903414080f00020f08441c0c152101c10641e0000000c1650041400c51414007468190100c210402002480c2d21101a016214030407034001d014103c8042c9a80c90f01c0100701d040c4000441c02040c0080340c0e40001420600610160f41d40b61021181c00c0301c0905520706100c2d0001a541e0340343e4482008603c513007095000843c828910002400440703002603c1e0420b81481801010026040707101c1122402e40c02c80b10228185200e00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752916447 1250 752915197 752915201
    0xb0c0708040315050a1a060306150d020a030b030609060f0a06080303070c03020d031e1a09090a1b051c020307090906050a1805030f0a0905060c250f030213 68
    0x141000d0240c0c2000704001080210040d241d1216252040c1c3c01c0c0101d498441d6200c0c240c1d010416901c44031000074641503054104007001c1e5500c00d400800482640e0031800200d525a4896110980c6550f00024032000880c1c06000f01110164254000d08052030000012a2162400307030194003111801c0b40803a0303101a654000c40e01500099050b25030303a0a00c070102800d00300e5243e0049004d4015865000d11680c043e10600c0d0100c2c41c50f00503240c010000c039190364000d0801040241804088100d1601c094450784074984c401c5c051075004150000d0242032030b2804031880c840ca00102030303201c05e0501c80d17912080340c07100100d8010b0280070345442d0284002400c0030541e4101d20146440c0103080742c1401200e030441802070000540c1040040b0b2030300d440401d14841c0540c054203c1e40100200111400c122000b42500192843c109402c2a00c41000805a41c045000200c996105061b2000e101040c01c0b48000703801001c582c1d0001c2c1da4600703e80c1d007441c00c41620000c1c3c030641c02584840b410100d42e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752917697 1250 752916447 752916457
    0xf150c030406021306050702090a1a0f03160314063d0305010c0e040e032b090f03050304060b01020a0c090b03012c0d1404090518100204090b0117040b0c 67
    0x75010340701e1030b6254900240b4680100344248e10460030b440c00300d02c40b51103d124080b40700485075030030585a039100f00ce02c481c1c14080b501c143d0f094401e040744a20310012407111240a18424040c3c02c0a0200d0114000d00e8090050005280f56041304100c15540e0b07034a02083c4c522440e4900e402100c1c0000441c60380b000135440e800034005d0f500380811144a589d01510100c00700504075403c000000d00d0300c0407982d5a0240410310385099000038814901e070007001c60003810070341d1850300100d0024115600d0740c802d00030a4070100c0c040ba50200501003080300ba030144048034102131004154401140e00d07840b4449000d0712074080f14513601c141242c0a91000e4001c001c001600455844d14105034003900d02c94100742401501c00c40c004c14848584a610a540c2014074034641d18a560030b150500915800411019121400d090b072020144192084c0c00d0214655000610400503100c0346055140b00c141c03001c1500c220304101d801481c1e0301c801c5503042c1c806ea402903003110b0004141d544074821090035200d6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752918947 1250 752917697 752917717
    0x9030d0c2306090106060903021309170705030a0f030911040509030d15090b1008043f0f050f03041b0302030316111e0103050411040f0603050f150c03040602 69
    0x29601c00700841c0380c009070351800340c0b0181000300700d5035a4800d0116010f000e5404002c1d4000003090300200e540d0340350b07004448954001c000c4400380d071080c2120111700da400004115010341020581001050304503000c2c5103444601e0506100140b11695940d076801c403100c1d43c03a0311540d5901c0108888200030403d49004180031001080362001594850059070640e1042c007161900f1710a03002d016080c800042d9204101580714151b241d1926540c580d420070510160a181d000801707420320401e000e440c0c075540721100704410f800f05050100d0004100566065444040c440104600041804250304880c1d2150f00800d1220300d034a80e684151410910a0340081d5052001140c22108030314800c00000300c16210707600124070507a8000622400d001600310f014444c1c809800100b50039400394000c01c1e8458410340c41c994008524900180854416140c045805644c03101c0a0041200070080204022101c40c014000c00a82500c0500c5032140104007108a02c0080b01113000c204a5405640540740c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752920197 1250 752918947 752918993
    0x60a050703060f1811040602060a020a180b2107201e1e07030f12120e07062d0f05070b010b09190b190c020301050a0b100509030d0c 58
    0x5a0b4070030421030940c441481300340c12407601070700c48281200501120201d9003031703401404c1141e49107840d150003034101044810031300c511210700c03481000d0b02001c0c000140440041e0f083d201c03081030500c0011400e980f0202d0b504c402c80107050100c075a401c031424441901d0f04808003100000101c10381814030908004200440044250789a2501c50100742c4000b50340c008000d400081800d4107441e40c3e00d444c184030242142c0001c00450004c90045001c07094282c00e60709101171101940162107049078004001001c1c02d4000b0b140a1021341d070310050400311060000e200c1e240e401281184054025400007084007840400281482058000c00960b481943c1005410701c0303d41e55900860310f6a4012507015100e02103413a9441810154008444203075800c040b45241400c0301c90410f013401811941c0d0110901010201e101d00590f02406014410000040007282600952003806603004101c2d0a400c18040d0920440785103440c002411044200d0310f280400b823600042c1084c0f81002d05400c1e805121070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752921447 1250 752920197 752920199
    0x301020f1605060709031106030702012a020f03040f1e03120215060603100e0c0423030d050f03060108191b020c04020a05030f07030204120b061908060a050703060f 72
    0x1800d00c00712407011a0160060754000c0e81c500c0c00450301c041013070000420782c060390480004d081c01c00030007560b407240c1980000100704010003e10007501043c550300766101010300c40c08501003a4140000040c00c2d1000c001103050900700754100740703400003602035070300c2054481d6458040d212400004900a5402c480044c81001140000a4071292002c54201941c440700700400d8031820a9011070744500a009440c90040e410700303148800f5100d0150503202c40d50018030001c12502c1640e00f920b0702032720300300b00d1210446d0714820600d418904015171013410310405105440081411004480c1c1c0842c0901c1c2102607542d6480d021340c400032120039801103185c0b42c583c2e50031148100040c100c0180c0080e4080b101001d0494040000744d1003603044010002d1818404150241801109103800001500f800340c1001d4a40160b07503034100c0b0301001503561410000c140b01c824100180304500c105075880c400c030f007220304106003240c0d03840021700480002e958400001f070066200b45e1004026040709407e1800303c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752922697 1250 752921447 752921467
    0x51c020702031f0203240d110a080f030705010e0109030203070609030c080309101410051e100f081b12060f060d0b0922080309010f112206050906090301020f 69
    0x1e4004942c1c000139050310401d5650403160031b0b1103411203000020700c0d107030401c202555048505181c400c07860f604060600800b194880303080c03022102030b10000005644800c4142481c030f00751040c02102c072100764541008503021031390100c2100c00032600080301190b03003102450105d401036165203002c0d0032404040244187c0c03075401308108520101a00052155406c0c00170120b183c00c90582d00e5002078401d048041040781072084081800342001201c42011090f080c0c0410580000e41094000113030f03064072405c0215401402094100d50b4448200000c0480e50100721a207100c3e645020300090150400030706603903215000d0081812001c0c1c820b039183c150320525103020f4400c0e00c500034845c600900000c0c0c1d441503203640202d242070a001c0e01c02c54410f80c1d9224690341d0703400034041174669521203404500ca5075480c01441175180304c0307004165488100e400010184000611400401d9205c001c0c1040550f41c803a05a07000c03010225a0595101c03445000280244203125403161009004281e801382 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752923947 1250 752922697 752922701
    0x20d2d0c05061b0315010e0316031a0705030103030e0f03100203012912041406040f020a0b1305100e180703150303140d02040e040b09010606051c020702031f 69
    0x285a20074401c861580c3c9541c26854482c280d41c24000e0007408082c030000d1320b21140001e1490000c10181045003500c0c1110700442d00700340001400c10141041541c2c20010441b0507201d40c47c010714030307804d0489a0308009000400500c018400a800c015004c0b0060b2000d82d202d0f924085240b100501311141004200b4000b40039410912640d4159501d404040d000c01c0151801c8403190f02200b01e5036880c0a680d0940c8105000c005442510030b0000310581d10840740c0304100060140b07000300c41100d08001280304028403a00300f9041501d00700c40500c000080811800c4441c41558802c17181980300c200f411804980305242c00e01d605c3d9022100c42201031410a040000502906ca256814400020100c649040504641c800200020f030022100d00b040c3c1d64207009004010341080c1c0240c5426980c200101d2800019941621407a400100b403041003e800d1103840c00400c110b08281d81441d501c0180240d050401d240c0d0b42c03542c00c2d00040d040c0700319038003440b0b48109582e152503500c1601c5004e044000c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752925197 1250 752923947 752923967
    0xf0605031f0c09121203061d0a050c09310212090714100c0c0b0f090102060a051515070b0903030403021621020d02120f010516020d2d 59
    0x1e854039198692402e14450040c0d44151620b440900c440c0400d43d81d07907a50b101d903c030400c50301010781c2d070140420103050040030700115009499603c1c0d65401c20001c03000c1100c0c006840140b00500420000c040340e01c03906501c114042d1607000380c01c0c04c9158a001d114400541038500c29802e031002804000c50807406203118010504076084801c03036511902d40f22165501d08a030b05070310142144102c5501d5104100042c0d6086c0309120742801c01d40d0f100840c1280760042d04a40e101c02601103660f00351540d04020700b644c401003000d03090019082400c203400013040110031031405840304412802000380000115030440b544866030722040d00d48440201e80342d410681d822001400340043d10b0b203d55030301c854100150b90381c0000004d5808118440003400c00c4650710126044004201c400f80507903550710700e8018280800024001114100a04600f103600041480068002031003940103e0f0b5400a42007a1140540c01d1044400750315801038138070700f00f28040040c258200b250140003404d81c0004005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752926447 1250 752925197 752925253
    0xa0b0d0914070927200301020d02030402011205160507060b0a0806010f0b03090715110105070818060f0f060307030b0124030e061605120f06091b0d0f060503 69
    0x806003d14030200e040c01d42c01c1d1140c1c100e94280d0528031130b0200d002c0c404c4800d401d604003214010788050700c9002c030b4203981006103000b0115501204000541d40c00c0400310041d00c90340e0904008030310703040b2000f4040e103082072a024104100410500d040164903800458a0329004000d10511662000240d41e81c15003402000e0300c8a04207180025420680c5066074084c82006019002030360a02d481c2460740c10010b2841e2042004e1007a241a030b42d5028071905010340700540e00d40c0e801b8600030302202c0a40c40d5400b124546d81d48040b0800255048800146070041d9a01c10400d405880b0032002a00d040200d4001401700340b0410000188545502c2d14140d5290305401e2100d482d40d8048400e80484994074a805010740140b800609030b017032805485031025186050560074180403281810030842c0440300070791b8101c40f00041c4070303c41c030b440d205440e4821038040c5001d030000c110006c145118040c800c1d83d40c00581c0c4440c0582256401034000c540501070203800c031100c504c02d41c1020030307180580c0003c103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752927697 1250 752926447 752926451
    0x406020702010201180302060411060f0a0201060609051507110a15090302030613050d08061513050307080d09060c061d030702040606030b0a290f0403140a020a0b0d09140709 76
    0x25003402e45c0e5442004020f02d825030040c100607621511800760030828400380640c882020045505640c070181c014041180700d690000034050705000700907044542c2504042d1003a03615085180f032001c1b601e02240c4510f50700041806004041c800070856200c1075400242596204155001c00c4030390161080080f01c0c0203c045a0f29030310344014550b00d0300001203000d04150004001e003c4614081c1500b10b8018102500c020140c66035524454001d0700055400324035080c030b0100c1040301d0314007001401c2c0a00000c801600d982d10000700082e1035110742d4410348042c0002042264144a0141e110301113012507080c00710900c03410079a050340c0365401480100c3c800c07881c02f107004c01c6d024480d00c0380c2c265100003d80000c0103a810407400a0300e50881380f2101499540c00c448891107a030070700307018240400040308041c1e143c904500c2c2c81e05400c40440c1d1220100c0d0f0050081c0d4000d80c2d01c030180b090440b11200c040554806010786010058942c6110240490303040350280a02501d00144071411a0109a01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752928947 1250 752927697 752927711
    0x80405120f0304080703020c04050a0e100507021f0b041401230306070c150c05040303080108061015030f0c180603060e04030e0a03151b0c020a0e09030d050406020702010201 76
    0x84003240541e60740000032200034030024000540200c010b2480500a00484800020250009060700c004035200302e0410746840654071108020000301c2c0e00e20000000c00d20061600c910002e590754145806c0300410003400e241498484003e41c094040801c01400521000085107401d100004d07081c89441501e502020150004080074000901802e000034050003e40c1c41d010001c80e88100c003ca030603104010900e54040d41040c03035104509004005072592500d482c40c504025010060503800009039400c0202004891007000b0b80b100d042e2a4500c0c040e020300f80302c42e14103c009061369103070114502e01e0303d002e41d000203802005485004221800c1c400000313071200d01c12000c0d0741071481000043c8041c81c0100740000e0052000401004000d0102c160482c1c0d2a2188001d00b1741c801c1c220702030551344041c40c504072118a0001c1082200c5400c000c00b504440b1750226518640b00d100b0b101100c00320a01040d208081407049412468070501e007440b56080500304100207500c0540c0c1280076619040c8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752930197 1250 752928947 752928973
    0x170a05061203090f041104122001020601031a0a06080303090a0c080d08041e0b0c0d05010603052719030e100c151505120d0f0e03120904110a080405 65
    0x84400d6180040c0c8000d0011a8180170300015240066101016540600010034503a60950842040c1800351b480c60942032259111180e0450b4503040884c11034101c03400520100b048000110600c0444200b00c000a9a60340085c00041440e03401c080b015000010074000400f00c002002001c450042050700210b554900070f8664581182d044500030a0b0100f0000700483c41c82ca48010180303d503418001080702041c0d031103c01c4c0b03413011070781d000c1800c4006c01e02080000241c420030f805010f4600b020071240c00c00c11811001c00200390101d044a800c0000c500082c0c4600344840c00084c641400e501c091092249806010b0a0002070614060f2105040c8407035928030402000300c100ea04610040554204243c00502414200700800212080100000303116203e9040900341403054402138103404103603c0e801420010249100d004200c84121021022380c0c0202d407564a460741c025280d40e982c0080004100500300741030b40210030b42e6000c141d01126a070401c040078400e510034404d6a0701524010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752931447 1250 752930197 752930203
    0xf0d0c080f18100f1401030803010314010603030e0603091e0a1b06210204030b0f090613120302090a050a0902040e070203040f381305060309030910170a050612 70
    0x1401c808039501c03c02c4a400d0507401d0f42d0000b02041055038020170080c0d00c801803880c5141080c1d104403400310002004100b40113025132102c503504050740007808071500d142c4004000044000d01c143c8104400008211007402c20042c490990f41401220340303510400d0f504c981d485014081082c2d51205980310b981012540303000106045c3d0700c940c4c6810b40c100441c0c4640703d1602840c1d00344094031030350802c0080082400503020a01c0713a021104405485d180012159042101c0a0590050903003071009100c002413154800e0b5109940b6490010b8440944800180d002400f40d0703ca0307600070395413041c04210240e1b290010000d88003540c10a0700943c0396800b0885c1d0760700c26031192090002c9000014021003408040a1000100c03d40902d61040da40150801010341d4401c10500d07402000150840a822024011002170504407081c9065103880702c00d4a89a206508420744103c080503443e0008034001e100c1030401028440c0204260311b040a5200024001a0b441c02e00c07400013085201c510040c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752932697 1250 752931447 752931481
    0xc0102061b0a1115041118040314070b01031a0907030f240e15010b091302160b0415061a0a0f050f0c1014010b07080f0d0c080f 56
    0x803101401c010000d40381e40600d01d800c168086402c00000411029030b043e020482c4070040800720881160506040c0b9184c021410184101d60190b021341441180365426058026031007130309424814030700464804030b00d0151043c500c0080056141100102c144010003001014206195800085a4991117105540c078002444002c095081c1e0100860004405841c062a07080e82c0b100f080d5500101843c0e8076043d1100d010040700140d109014200a2500c8500b00c180108003402c240c6107407218100128003200c0c510140400540d40018156943e5402c040160906c282c03c0f50031030b0000d04207403800b100e16425580150240e54105800440c45200c11000510701d071501040c190b00d0301104003400e40d5540c0541d41510140a01840b08000a1070410000d00c9110f0624014101544039241c141c0d0480c1d0b8060030300244244070100600c644500d420807038501e103800a440707688a1880904001552081004c1c001a01d42070860b280100d503000051240a80300e0b124881c03005540d40d03041880b8042d24 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752933947 1250 752932697 752932711
    0x717100f02030f01030807231606111011190507060501060206070806120f0f03130e0103030212160c0e09010f1104120201050904141b071110032405030c010206 70
    0x5043d00400004000900034001644140d81040701d0f000424104400304641c15081c04050308101c1c84075000d034081d1030f040c078003801c900d040c030b9804900380544440d600c0c86200c0c815203030640d880c0f040d0100141d041041c2c91400e20384501d41119000c0020380140702c0c1d00000c2048902500b0f120010607a5030010801c1d82c0b14500303a44c2c50148503520b203003c0100300701100d407030f10805014240080c0103160301801803601c10450310004603514158001004048240c6500016003e840100140300083c1d01262031005261600d91885d03c41004a1486c0d00c0041031000007080c100040c4400124841007024107445084000c0080001c010003010680584081140031104002e080000303020380c600e02c928802c55036006152640c10b040f00d50b0045401c40d048000703080c500f84009001c0100040040b0011a0b00022014a15003070a2107961001030400520b500e80e4850041403000a103030310721a502903c80e0102ca10090380501100f400143e25140240c06168000e029019040b0320039400010124000d1039 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752935197 1250 752933947 752933971
    0x2070906060f0302031f0b091e03030406080408040f031b050609090105060a020a05060a061e15030f020c030d0b03010f0212150103020f04030506011e0608060108090717100f0203 78
    0x341c4100b04030004d510060151442e41c14000d005441c50080c1b54089000c1c14203c1d5401e80d80e03d591000300003114000450f20000601a401095500d441c08820303141210840d0400102c42e448501d004c20f11401190017560040e80c03000b40000a0003102c940c680094050003c3c524146600c030001e00c415441080a80c2d40c0120050b801040706050107401801c0103c41441601c000c049283d071030905207441a01c41d880e1007511403c080c01280c0c070340c05100f1895203141c80016401480c1681c0f007061503401b8001407040c15510030001000030559012601901000004d59540f044061401001010840102d600941c81c0009509031100036100f11608105045100f509a543e0242c00c6c500c03100f005000c90741055024000c035998009a1409400030314031600c0a072081c0c1d0304140100400c003c0f42d00f100c4c2d48400381e404d0100705075074100d106280c00030360a00e03010041d81d80301210b9920f001c0e844c4d800340424600c007500d409090040810440c00000d002034044c0a02c81008880c8016404140d80103080d00d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752936447 1250 752935197 752935217
    0x303030610020f07140906030c01021005100312030c08090606031f06030b0126031c0905070b04090f0b030a031e17010f17010c080606071b06030209010207090606 71
    0x118181003801e107020400c0c0b044682115180540b6418203c095100090b20130000000d1191481e00c01c1205500c41405d900a100041110000030b41e070340340c60701d00d0203842c6a0f1580840c1c00080001106070156802840b180c015205201000300207208032555540000c03409000b19400c45008619039015075001001030402d48400c400002d1807038613114900204642c0d81d0070000014914095440c024812003660703c80800030103840e01c046008280304075036541c10800059803140100d01821000b000d6007030001401603081d00d40180303000035170740000f1a0514042800100800150003e201e2803581a9052094005100c18140d0714826014002c1c0880d07002808254020750190030003c0318030f031616040d1810a031440401a5040c82078210301104d0303400010a00544500000070f100c810710400082000041c82c11005150000c081c100500c110800030341c070000e1068400d0820943ca00c0c0d80e00a41605689030005030096210f11032480c003500035030000140c401c690303106000803a002c946400c2010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752937697 1250 752936447 752936449
    0xf090803091201060512160f1208031305010906020408070b090a091806060311010e0d050d0f2015060105070506010504090f08131e08031602011106070203030103021e03030306 77
    0x2e01039419520318190740e03404000902e6907451452111180b40d1802501d84107401c00c0f0b01c20441c00b019040303040003a0051204010307402c1c20004600130b99401580750b588030f0b02d8542d62242441160700016010b98201118035040c0040c2d0b60061084604500c12180c180740d0343c41c4d070041c40d40981e01925500c00d81404040010407180d41248096a04107100d00500e2209551039104481072600190360002d650300000d051541c1200044424501c11103060a1078200d41d46d403195140031405107001004041d410b02c801c40360094282900701421100e213000120750640d08143d541c480590807451000b40c038004100c86500440445140e02d820401428103a03003440c090101905a4002c100c03220b18008040001041c0480003a208584070385c019081a217103003030220015041041c0c4140d00c2c0c41d801040400a040b0b000040303d5540b0941c002c2000c40301ca60b400180c0c0d1100c4440c0c103400d4a80203c50400c800c40c1d602100550603a44200e4020760340c07150701c94401d50a104203015580e090ba001700007003045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752938947 1250 752937697 752937709
    0x40b030a0b060913020a090c030c0c1515090906140705030402010206070c080f040305160803090303122a030f07030b1c060623130213031707060212070f09080309 71
    0x84a6181d100c04189800710350b01051b96030356a83c2c0304089141e0303200d0300448000d5160003401411801c07440d044016592a48805401117500000082001e43d43d203000e40034400140c42c000700400e00b210003000625254102413018040c45046158409150310004402c24011030641e0f010341d8041c0e0050000e03940d07034481035444e0039414a064a44200038080c0300c0004801a0041c0041c5106d18058154003040c902a034074031034011707000b0103590703001880340c1175443d10008181d5040240b00c01c10b220b03c5850342007440d500500c04514000d80b0704448280019102e404800035800f032079448074100130a40d01d0000450841d11940444e503030002550754042c6e20041c0181a8440c094020640060000c0e0f44403801c01d01c02056045010b02001c03811840c04641c6403d50007100400302e04802945803291400740140c05c84a5400010001e25448035107200d041c0d000b00c255290954008000c540e01c401c0c80c2c0e05224044002c6440314000b42102e17031004005449503220a0844008000031070500f0350307540c10008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752940197 1250 752938947 752938951
    0x5090d050304051512131205090f0a0b120f010b0301090209030f0a03110c060309070b0a171f170a12050c011a0406062c0f031b040b030a0b0609 63
    0x303041c030080c0404503031030303444c84496500d100c03041503035650ba180720305010681010000c00d09a0214000398445c80415070150310200d8650041c6416565080010700080c180c0d07a01c4807105400201c103104c082030b1100214000c00e48d41042d010300c500b240d40c0b000151840d00d5024001d581c880801440104a0010300380c014010044000b0143e50064140f1560507140040054086d0005103121078000224002840444542d06094030003034a149080312000340d40c2e040e1403240d0300074035000184100c0d00301d12541402c40c501f0f0240000140c0f030708140e90525101d400004103500c0c001c8506000161000540c0341e04408503e8202c054041004a51900c035504a144500e030418081f04101c1c0803440d010030f00c6421191209103441240e90014041407100721040ca800410a00400444240110109680c1c0310380040241c02405881d080c0c00340071a13200201c58001030340520401d00280b10004510030502c1d80c03400159410800200700208155032101002c5001c0c0903280d21700c001c601c10f8280b0014581d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752941447 1250 752940197 752940203
    0x11404110f0f090a150801020a0c1209080d08060f0d0203100b0a08120c010b030c1f021e0c0415150513170a0c060f0f2001020a050a080105030d05090d 66
    0x200780c0d15100d00110f1284201168010041952040c692040d00340d4484690007411060008504205101c1e0000c0c01c5101c50500146c40c0603102014003440c0ca00c280d813900040c2800c40c0aa5040d01410078014054490a41d40c161050040e0415240710717050001c005194240c000f40240059444240000000d0000f110380c180c1141d00180042a6100e08025450f01036402d0000d103941c500c08010b4842c210350480f07805511a4001d40400c80b07803030b612009440717030075401d40886a102d040940c106a151043c100e4500c02400d100f140e11039107418020455040038403040c0e0b8180441140d055500480a405002e0f102c2414110400706400611078400742030901061003604480a031a8000e05201c5285101200b9a60784a070442d0820400c3c1c8a05075801048542448841080000405440c2c00690780000d81002003000804c810450050a0b038603c04040c0c500843d9281328800008080f0340c8400c00c1203002c138440100015031030078001070384444602c280ea1800c1c00c14181c00100400d400800c0700075 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752942697 1250 752941447 752941459
    0xf1e050f03040f1e17011803030b01020c010c03050d0b0613121a0c070b150a061e0512060411070b0f0613051b0307020a0b0f0405011404110f 62
    0x111002900400180310020003800096480380e1070400e0480030780010340c0011110302614581d0f003a108031130740030703c2c03080e111017401c4c0d4903410075030541d214014119507441c01d640a0800c1072000506805030b0250741001e4081c1d0a44400019000055a50103a45c0c00c0080014a0410105040400c2644000c000c90700c006d00c1c0c03902e840703503020020f2031f0b1035015003103001c0300381ca0840359004100703401d41a00d2650a540d00ca040003844c2082da06880c030301501101a1484481c0d80000710418066880740701940802094a031240c0d444000003014922824803068002c03100d8048416000e00500644042e02c80d0a8034000440d40c6010900020b028200b1554146c03500c14003080c400224400d05040c844c1d80c00305c080c0c025900c1c2800c20821101030711102003080c585042c0510500084148555001b90710001c50582d503902e030705070200d292606118003d0b185407800c400b071000320444c034031800303028600440007800780d1100701285125840003030b900200703101c031400ca501209040c050041440104000d200c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752943947 1250 752942697 752942753
    0x12090806160201150807060c030e04020c01090b0a092a080303010603020a2307060504110a120b0106020f030301030b150901030614090123061201092105070f 69
    0x10091500c0c40550311030450240090358031603101d909100c0c0e00f40401d06041510b200901d4545500d4403441e01c0d0041104020303403040e0200625000e519800c4082d94080c10441d80c8501c1900094003c0000c0c0c1400c903208040f80c00440c82c0310016001e01c1c90440c0e0007031400b1000d00740280107420a201850301e00c50040494080010b8a61024806035008102c0307500c0169942c14070000040c8200945007640c6805400d02610f42101840c000c251034204d0340c810000110b0b9159400d1100c1d10040c101541da50100c050705010035185c01c08440da0051600c151084000c13039032035960a0b80c44041d2030041e4002603206000400202d1112094590410311003049980d402c1c3d8200042070b10300384240c005a61050721f84607901020f400c01c4d011198800c00c074900070414582c501c6400d942030010302a0b414205078481c00031840a9a40840209003a00c4540080080f4005842c1404942c03180c0c0e40303800801800e1b4007502d1640b90040e0203c9411030760001c44460941965070b41c6516206400d100143d5882048107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752945197 1250 752943947 752943959
    0x30e100e0114070206011e0e06060c0f01020c07170c03120307030b0409030804050d02010c090b0d0b102706140a030e0a050609010f06050607080f071b09060501020c010801031209 78
    0x44030314002d50f40c950181107158108010b00d41c12103a165607a0040e1100d604040000307001c00021a40c00510488010340c1d5519030b07060382450129080d44500203540b0000701b02c41c401800040c060100c1e51074000c0341101c42441030105484142c8861703115050b0f04001c6070b8800e0311700350000441e030000843c20005181c038407034004501107540d141c03400ca020030498410b05c818060208420000040b082c4028070600c181b15034002c051700201c1c03041c95212800071070301e52004000d41d0046040c43c0c0000d4070a22103056001d0307000300b1068840041c00307200d480d42c0304500b09440814210354262103407503e80e0300100b00f030642c0b030552942c0034034006d0081540c0c800100e000d01e00c0034803d10070081d00030380040115040c041c41840c2190180c04900041c1849c001e0100700945500303096400894024861070b8a86841850a100610a41d040101b050a0b203498090054051500034410348030440000c101c510740703510059941303121104900b8040740c215001000041c03482106590416214030785000c803a40e90310 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752946447 1250 752945197 752945231
    0x4020a0b03010801090308090303100314031b0c04200f070c051c030e041a0d050717010207030e01030606050d320405160e070f26090607030e100e01 65
    0x2801c00c01ea81c4e51a0401c01c0145640302950035000300d8020081c51450500049184590215102c0200340701640b403501041600c0034020f4072280407000b400d65401010718018541c4070300069210340e10440c40d24030301c94000704511310843d0140324a021032070300d0040001e21030801a040101c00712682d00c48800301007504e072240006095610ba081414126907070b00e620f006064180c44030b03041d90003030f854041d0f55190138541c40e59001c4080c80c180d070321403005141c40c00d007207061807402c0d0040701e00045000e0012101c0e560560003808e803503000755607100d04451040c0044050310750741d20481c0c1c0000c40511441c603100130303298403180c170713402c0543da00c0310109800c4154009280d0201005182c800c40c0b8030b00700014098284180061000b0707880007205c40078100f824241559501801900c100000c1c40366485c02c550060102c080d12484104858000000d0091181522401103d2803a607901410f40420001ea0103401010500300044000c4d012001801c008400105402c85062005c0d45d00c5000b0000007240c0c034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752947697 1250 752946447 752946449
    0x40803131b03120e0405090c0114210103050607050a2f011a04050c0f07150902030a060218010e150f13030b040506070c020603041709100509130207080a0804020a0b0301 74
    0x24410f4030304030400c03440b400f4011140109641e0300840c185000c10000410220300c162103140c003400c0c01d01c1d941d4800d20300032120f400f6003c402c8141060070ba140e036a10060a1038158105c903c03e80884155546525085800f8042c0c510742401080402c03600c0110072141d41609c042110300481c200107141c1c2e891642500f035a5420202c41d1040668540c54101400c050280c281e1180c040d1140d1450074031303080c10915561042c030f8400381110b002e0012899642201c0e401401c50650000d00311411101e203805d10100a40c092001c60403482040c490086180d4000c448405003454010490040000c034101a030010f0352003e19680c807413890400452000e89500d44800d40a135009034610001c0380b4080c41c00500d0710b180a0810303001c0c00101d0303c949006a680c4001c1303d6005900c0802011400d202034000107460250304a25944903400c40c6245100703991102c0a041140005c40317a482c681d51020481004a100d42403000c3d02001e010802c241c241c60080f000e103034010384090b00820b00b1958a0700b145140f41c0003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752948947 1250 752947697 752947703
    0x130501050c0c071208070b0402060f0309010f0b0f10200604060e15130f1a0717010f05010c1b0305030711040605120c1203130f0e0c03040803131b03 65
    0x8049900002c200c0c0400003400a401e0740c400038500e0007400c0e20385100d00e001d00b0000800b803603140c100140441d22040c0c2503130460454000741c02d440b41401003560303010380402000c1004182ca46441681c9614100d2048580a07002030700c0d0480915500340c04507400a100000d0780342241c02140850910401080600e00c618010500001c040c9880c10019040115203040300d1a2641c4100500030200042b4162981c243e41c01605209000303c54540080342130410042e81d490401c00900704506290001d0090b039540044101c04407180c0e0301d6821078850703803a10303000d107a000640d200300c2d10002403200198000319080410f600c4200700e99030b650713440c035503440220211403c2d440069100c9090506001e180c001e840d00300e8107003200c014605101580c407110340d420144504850a0001c04180d02442116a20300200c1a01041c0540320702c1030400381c038014802c07201c002c000d40b4001070a00e080e0a09490140d50301072812459502e035441d1880d5120b4800f03109481c4410100341002d00141c204900300003c0d44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752950197 1250 752948947 752948971
    0xb1f0c02030c100513090c1e090f2603160809041407050c01060f03080a08041515050109151710080703151a1005210a09140d02060f13050105 62
    0xc1202000d6800002c5076106c0c1131400e007484440b0b481c0e2a0005111004810010102000b808002c1e80440d1450000d50224a010140e110041448503084500580c0303410703a5031650050741240e05689a4900c10b08000140440c81d445185000034a01001003030808030041011030602020400000c3d240000d56030400481c0d000608903c2e010740a004070707001401201348151030107245440e81d108a21460301104100b0000600050030082800a05018046413210800490404440c1010280c1d128051107022500f0440c0001c0e0085448501c000d81d0109a5500403581c500201d41c8003050384060410215120203003408640034400b0085d240003980500c9112201400c07444101c0f007124045c1c3e15505200c00800c110021a880f2078403c01c3c0780400c280381035a66904600e802502c1d8150b82c46030010450009000e000c0f250490b40c000883c218003031084042d0f900403280d40d441e17079a5804c0c01c07040e01580103200015282170724004081c0d400070030a410965046110782d13078942101c20441d41850811 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752951447 1250 752950197 752950207
    0x301080604150c1211390102031306200f04170a0c0e100503010e03070203151003080a1b06150801141f0305030301090f0b1f0c02030c1005 61
    0xc00d814441c0b002c1e940c0c01c0c810403419040100042485004d00c03114215142c5481c1c814040c011207900b1107400c0c0028442090614883d6100313909006844002c04125083c540611601c0030b00c18422603010365500d212040c2800c0701740d0b98040213000c4042011404a11400c110140120400300902e0039202c1c030541650340d070313081280380104c034130512000a4140c0e100c0c241e06400104842d81000594030251906450366840d10310256518840740c10440e019424101640202e410010161240034400c82c1a40c603c102801c0360f0b11120b020844804002140d100010404500d400b002040031403a103282103031040c4908150300b4042c0052034400c545c041e980c0c1c40142c5400d00031403d2034000c1d081c200000d1191308a005100582c10402811100400c201c0e0003910100c00000c0d04104001d6a101303040ea0344960b52060000c0080100059042d00c02e8142001c02440e80b0b803056604c00e00103190018169500c20001c0e0458410101c28412a0544114001d00f9015030799460841d4055240f659059992 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752952697 1250 752951447 752951453
    0x12130f1a01180b0f0f0a0b070302031c0507050d0b0d080408030304053309030c010e1c05040f0e060f0604260601050108040f1b3002061c0608030301080604 68
    0x5410440048a0460f01d4851000015541e0150300c8900a40803241e000080c1e000030b000620001e519404040813100c006801000c0540200c060040c20852180c2195030038802000d5a050390812a82800060000c00158040420681c003240c41c42d5009001001110086d580b50029507115402880040d4404002c000801c9020030002580c107480221001e084880504e062140791044d516180018a0702000101140c004005543c99004858000d0050065858142d5102c000311950980c0d1000c6a1015654950180040f41c045030511403498000510300f0020340d41c40d0102030029980800c2081038a12241e903404007800140c041c000c907903203d0100b5400001140d015441c451106034000f000104050383e0803841159119030001080032113420a850010041040c080c0341c032403c031050440102d12141003d031101c1d03421003030a40180b0034940030441c210300002002c04c025072182013004403180003040031040d112800d0b04203001007141034454080f5429500260405480ba501042c01c10041c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752953947 1250 752952697 752952719
    0xc050f0103090209060d03030e06070512090d0f0e03030d0c020304050a0608010f05060a0210060305150f1005060a090306290612040209070c0f0308160512130f1a01 72
    0x424202401c081008403060390100b200500001c003950321038070701107405009242c020342050a00070072200556046103820340015081d80c00c201c004c604210728101c001034110000091140b00c1c08099100d220103190740c4503003111411510046c040d010b0006210b032650002850040c8401c40c00c80340c002d1511241042d05002c08150b07994400c804025134480100141002c8021541c16140306803900783d51459072030b03001e03880c11030300c4c1e08030f0000d130740ca00900001400804034500750040c840132510840780d00c804400382d05600068455961740140c0720350030491450300c0710003400c07030b15118142000f2080d505c1c0ca800c01110f00400070007501032581a4140c004d03400710145583c01e404102c030030608060300103a4640a0060040009029020480c0803400312800740e0f000b803100540c008440c5036000054940204441030940d429000c10120851810345240140d060b11018030713014502c9072283c1d403068130725411140d05940542e001c2c8103004414001c284480210b607040d9114540700382c11549800c0e01d02407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752955197 1250 752953947 752953969
    0x307030e190c0b0f0f1602040605013f0603050c0f1804030509040f0f140a02040815040204090b07050a020c03151801110307020a030e0a050102190614040c05 69
    0x9484071400c60000040c241c1e82404041e500c014007180e4807680441691350f2907101e410944d207902c00010a40031090461410500645442900c0034001e460392800192951051824008502c7d801185844c030b03c0c0160000424410600c004154508411400c001c2d084400030f802c00e031030079005208542c8950801405412640350181c41c101c02c2e140c2d078855032080400000e04001c00301f120024440700541da841c0c03c1a01d00e02c030744903000c101405c0500d0013440280854403900052900f28400a80f10004d28401e86003100c07040c2000c0d10b10b5070401124050700c81c41c000c1040780d10a07030720641000400c801041075841103049849048d0354101d070507400fa14107032180450754483c0e8407082c1281c00d1310f0f0b141400240c04c11910070300342c02c01c9410040264050181c281280700f07480c0010040004640e800a400800940241c890b0810110a8400d100d0390824500079240543d1000d040b10010910390070082d08070a014090002e140b0311000207a60300b004080c0c1d015510b841e1603034014040b0b40340003d0565 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752956447 1250 752955197 752955223
    0x31103040c0611011b0503040204150302090a0b0619020c090907030314070302031207030b180c0415022109041413081c02030a0905190f120905060307030e 68
    0x5065141540e03500c1d80c0903400380618070810106072589a01990250440301c0070b103da020310403552921114004060f5002200d050b0f116508000901202c03a0480e0b480c0410350360080c10017500343c0e8401c5070100c040c00000d140700381c20200030403442d1181003071001101300004041d4082e1031311880140800006030005821804550440d9000300000785d001520700031481c0b062a601c5e07072a400c440c1400da0440c018403904c80c11076210340b001c00034a0f59055011402102d03089492029405403071a04c0903042008840e00e02a0300001c10052100b03120501142d10341c58982d00c110b483c100c030000c446004201e44050785802408000c00d2a94551900c0d000c0c00d01108000110030043d03203801d040d1510360703800700c0b00041c040c50302c002038080c1000c140d940442031815042800b0345d40c81c100b280c440300c0103105003070087d51140613071207074648110074001c185a06641c0014000b009440780ba1140c04c3d40180100c680c1c414420354042c005045d49600c005540300f0185502c0020b01c2c956000030050511505251070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752957697 1250 752956447 752956481
    0xb0a1701020d1b02060433060e01120803010515090303120105040c110a1101050c0f071a070302060a021612020102131a0a03020d06091d071d0c13032103 67
    0x407640701603001034500d0f40690440241c0809074088110035004048203c8403401c0c1c2d04070b01c0f10741e0042e6085034000c80c0458100d2045040c0b10b0380d8420002f5504420b9160040101070208010802883c0c480e0700451034440f00c02141c0e10708600100003904c1e42c1c2c41740d000a0542c0c22124010070440c44d041c03103021625240c50500d0031078903d030114020385403203050130024442d0318508640c840c1a4801c071705030758080200e081120081c81c02c1d0300e040f941e5201184100081d1074400805030f885c0c1070a90081d10540c95041e0000c140c992114001400650800040141c0500141e43d5000224940c802c03400d04414294000682e00c0100180398402a0241e82040158442070b1410000b404400c0c000c0311200d030001e140060b12a48030010100c0505040c0d070000d040b503410f004050328442c2d5440d42001014503207804403910751340d80d42e000c4038040036070242c0c18180f0a400d500045046815500030903c401e02e090502d00e50985070742d9103d80408000703e0380052101004110541a40c00d4030481e00106840744039 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752958947 1250 752957697 752957741
    0xb0a0c0c020609091509090a051006261c05040501080907030b0601030e070801050907050a061805100203090a0902030a0c020a02062a151909020a0501030b0a1701020d 73
    0x10404510a0f441000c0c015100480091311603034071118042c1c18058000c0041c003042c102088026980d074002031341035a40307001da40340c2040441e81d18803170003003140c401707060442c460510f07100c1c4480b040005499030b00f02c5000d44004910541e4014074a0842c0159076265151200d090000041c070310b1100500880c950f5024507002c4c0017085d040c00d1081d40c8050240b80c041821400003c81c14248a019801110b0a6082400340103101c0404110102500d4040c0c81c1040040c1d030302c0c801142d00812201100d61103001c204028000f40c100003849011400c1140100d0b403500c100c40c00071405200007644280200c83c0e010040c0118040309000740030070356610703200800c00001c058000440c01d2150155588244000d58509a0065480040449450030100036100c0040240b03044200300d00f0100c9560b82404800207988071032584c01c2c851140565009003c683c0b104d41403800550040c031040820f25440b01101d5400107007809440d1104002c4001c0c4400541c80d03d95035805c86060b6072151081d007640050b00c03c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752960197 1250 752958947 752958949
    0x162f03030a0509030a081f03050a0b0a141e0a0623120c28030f030f02060f2211040603080c010606050307081b0f070501051f080d120b030a0b0a0c0c02 66
    0x1b640350f4111800005803c2e00b4038102114440101d03540e88014010700070080c00d001448101c1e5240d0344251a4134030180100c0d0032600c81c00300f02c580c0c1103c0701c0585207007040c021341035650407071115544192060030000e00035488101d4000703520802040000c0341450104e41c81c2d2281040402c200c20341c00700e0b1004003d411a210000340c0110b02e401c5080c080d00345581220303035025645250701402940c028281416500e07070382c02e0090103550500480000f5101d0b5601040404280c44841071203001c4c07449201d000d14001c00e11140c0711403010786007941e04c41d010400340d0180c0d0b0740c0c4d840340000440c4640e0095a031120312072041401c1d5806544140180305d005d1080100180d00524203642c807100c04103c500685000074400c600c540105000c91a0402010549404112055000501034086071109030041600701329090351003041c40c003500a95401252a010100d4020407811401071a0f10101045004040c1d01080c50004540d03029942c1003441c000348003400d2558450302040c501d0f640b03803001000006030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752961447 1250 752960197 752960207
    0xa03021218010806150f0d1116030521160305090111030c0a0c0c030f14070503030d0902180702071d0105010c020f01021e0105011805162f03030a0509030a 68
    0x29102d040c05250300000d102659844803121059110050f210f8680000c62800b4100d900281e03005001545040c12420100400d0010384106100c900b803800ba1071803d543e812134154101c0c6442104169400c400085902d17040b122161080d0b04103200700d4000c0380007040050680307501514040c180c1c0d140c40140c408440c460407ca903808004910141d6507000c60302411141c100e041c90b806000c84021120200400403a81003c0d0718550049001d070a911005441c815107940c0c40b1320401d41e060f40300b0408601c0c5013130f00303401c4880640d0004243c81c19031003001c24004101c8808550303120040e000070f44144003807000d21280000640f0342e250840515130421001030300a88400c1c5001c0d10410040f0040241a032007007204507010a00700340c0c017554100400c8440350103000203000c1e1900e11800a01c940701164480d100c1c80d4840c4a5403016082c0c4900400d500f500c0380040940040d4505d004e49a4400c5c40c14800d907120307042004064015552442d0a65401003151809000fa0b06070783c00c10040522441c0d030207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752962697 1250 752961447 752961487
    0x3011107120503060a030b1f1409040213020702130213080f060a1a03010c0207030201080610050f030a0b060f030714121b09030f0a05010c03060e040308040305090607050a030212 78
    0x42c100380e030781d0351190000140c07012802da000908519481040000350900d1103c401c04500110000d01d0500b501d803562840ca0300c80072200d81da00145c8a40c0003c01614114040341c098003c1007000500e803201c0c5070045034480c42038101c00006c550b00051030030581403050003400c0091000300003500c0388101e030009007503d0300005011510b1150320765080001c14040311000410441c8014000c00c4500985031001c1e417140d0003440283d020524881c001000f50800540d206006111075580300e01d0b04800e60222038075600701070300170585140d613a4150201038442c0401090507071454032501c1c0c0c170b03860149402001c0340105e1327030b0304c406c0315100b070000d05184c002c0c038508e04d600000d01140c83c101082e0481d000d45000d01440f15800c2e1b03d0710503244980001800464001c000c035008000a20003040c85d401c0030707415568284580d241c0303901030b1000076000c039102d03a200315007003807281c07030300a241c200310b074001550680250310f00782c2e4281c1165002804240e01040118a034141034440541400c0380320030b400c0085900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752963947 1250 752962697 752962733
    0x9070903030c0606050d0b09070803030112170403021017060303070f0f020f0a09060f09021306080c070c090227010f0c05071e081605061603030b180603011107 70
    0x1040304290420111390440c401601c0041c01e00c0000502d682400402c0c2d00064408100501541e03101040d00d08011049030b06031207828000a00c070f0900d542d210f2484000428000c44c14400502000c00140c1c0c9040d682800b0501d69641d00340c41c0f04e100c41202e00401c00242000c1c0c4240e100700400380c009030410004170360341d40d04010300107125101c50010440800044592640c400c1d42cad51008144101c140e402030341560301012072250b50b0f40c3c075012420f00728803407100d21125040f9035a40c104907282c80740201e1640489182c4400d03041030360030341d0b6444006043c2e41051000035004a00b17507401004440b41300006080003d20112041c81e01c4002800110040682604000c503400800b010300c00c0030024000100040b04a8910369190b80d66142201007481c0645500b500a4240f104904000070481e1010b8680081c40503107070104c00a0790b00c00c580348000702101031540314a040045071780c4049503080d824110b2000c0707050526040041501b1100350000000111005100f4200030811541113072506500b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752965197 1250 752963947 752963957
    0x203160306030323092d010306030203101e02031306051e0406050a0e1506010e01050a1713050109150606110705060331110d030e04050411030a0606050f0907090303 72
    0x70711400400d02841800034243e040400c00a0140e402500c1c1e44800d880340000c801c0c1d0f01307040c0101b1401107082c0c43d02488080d41c558000622405400140d03072100c0b0020740e500e00e94600c0090b00001c2c10060380c004440c2d1035191035a1116901c1401083d02982da40040b08002c4002188000458030701d0141c8082d00140c86650354034001511341820394040c1a1428411003142c008070100c04000c2b10500c0115107142c0000c480e56908034642d4052010349408510a4507038030a4400011405030001700000d258a40f505032180c03a2102080080c800d10484600131462000555000303010350090f50b12580c0001d0030001787d5420180c520704049001c1058a900700c8040f6660b844441c031821010000f05100b0181c1104600a014041000070360345c03909a00c00c101201e4202c200c1410881800160540a408101d0100d1048298a0950322281d070040c03244641c6502c01d96000c02003807505000c0c80084030b520355104010f210310319040350340c1541414120b0f505085403410010040407103020744130003401c0c00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752966447 1250 752965197 752965247
    0x1d0a062d0b040902041502070302030607120b12010f0606180b030c070209090607020c010212090d050a06020426010606020d0503071b08090906090403020601140105040f0902031603060303 82
    0x4800310a10000c0c80070034105510340c0d48807500d1000941c040d200e89002c01c0b40e1542c02c071780d126002068000850303800401402d0507642c0d620054800703142c0c41c0615a04155540b01400c8540d0b2003503140a0300440c04400092469100b0001208662403070b0089001e2100207003103044001c2140d030003e07007a00e40980d0499100d4a8a02a42110740100c1c44020b40c450840f9040219107507001405500c10f6040d83d0886003062003000059031a5200c1110100307025008004d00c000c10b00b030a12500509502c500200c0714048410385075075049030000e401c03c0c081108034183c622281c1601a88a002c06959100208211890b04a004e035950f14104020428030501000242000d4001c2000715031050b084201c00b0781040140c90303d51102c2d401803000510991511010840b1402e15400d458425a031540007400700e42d00b0310802c984180e20b9070204604100c0104804500118042c0d80600200301500e4007581f641072072852641d8415a003016002098541070040010a503c0703090031014001400e02120a0b03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752967697 1250 752966447 752966519
    0x13020a050d0c0e0307090603030c02060703020316030333093206040c050702130b060f0c011506051c0c090e090a02190303090302120106050a1d0a06 65
    0x5001e0080c4a2600a24104141c0d108079004104515100e000304e00f554182500d0301d03007890454625000250001d104282407100501b070000c0140407450003801140e092202a8a4107140100084002c400107503c440f44001d01a20040382c5076000ea10540984802d80301500d40400711081d144610142076840d4510b4034090f4a01009a4440200d01c584501d868001d00c14076480000c41598464080d5262040c6a0b80448c458410303034640540c000d08901d03424150b201a50701a040c141d41082d805079040140100c00780f80394000300740341080301d0f0010404c00c040300e61040708a0f080358009014080d041154079040082007441c03502c04803141c0000035004204002c00c941410603a0060980c200a500a024103048002543d40d800c6208845440c00b201e001c151111020031140301c01400302d00c40c504d0500040c600031031401c0c1c00c540030000000301031f5600e5002803411251640800c200b98050803034140c0480b2000c0540744e200c46400d074180001890482102c2c49080340000c2482a400103c0300d913081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752968947 1250 752967697 752967707
    0xa08130f08030a05071d130515120f0c060c0712051e0c03010c0906050a0c0206160b0405190f080706110a05040816120f110604030b1e010513020a 64
    0x315a422240c0700e501e910701036818030004d000546040002c10440e001c0510114039442000180382c8010340b00b2a2400e00050811020f00300261032410f0301c60301d8495032601d50704e0706071041d0246003c100c01040c02e03441244401d41460100a803241c014142017005c112091000510041100e408035103d103003140303c03420440e0504e941d0449400580010140700e40280700c0c00200c8100c03d88045000300440c4075903041c1503e05400504c2a2000714505000d6203c0260180c2c008544240c00034010601e80389038a0443d4806c0340e4280c00c216404284031081c0018400108018002d0154040c020400541c894541070070461068400800403903000a00e00d040160603000b03040d458150107030302d42d1550808a8041d150b500710b4040d000940c882c40400258078000989090211800e50500718101006503c80501504003840241e4504030101c1c2c14034070f02e44075680104003c60041e0038071802418410855040c2d400301d0704002c1085111000180010b550701d00103a1154285d107000140e54803002c070706c10b4078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752970197 1250 752968947 752968973
    0xc0518040b04050f150123010807030f06051f0807170103240e06090d021515011809090303060504090c0608130209100801110c0a03050d06080619050a020a0813 70
    0x313290181300c0314010368009440c07180703050711a00380b07002d030450101d98040b41e83c01c4829a0a60700042c4c4003401310344000c0c000d9128071440d0502c0b07c0c020818603120000708071641d103580e01011405408141241d01c80d50b01001c280e40080c0c1515285645203c1240c45107240c44060001429011022904e0041601b250103142001510345205100e2015110b480e1078a039032084840305541d0041e003580308896072000c100660070300c02002c000c0c451629545280708100d050320b400141440b0540e02a0340d48101d001410000804142601242d112442d283c02001d031400c607417201d03004900742101038000800c1c15280c0c1f001e60340c207850b16165503a24110350b03032030404294038043e422014020a204c15064904261810780f0f01040003031105a810440340403ea12030260302c2d00aa80185860303200003440741004040c1c5048484010500f16120b80540381040c43c1641c11002644141042105100860044542c4080c80f09030843c10080c4074080500354490050440c4500d03c0701c20703566410400407800c2c041c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752971447 1250 752970197 752970223
    0xb04090b0703051303020a0b060120010f060b1215061b100506030d09060e191212030c0f080606131518050f012001180c0518040b0405 59
    0x1100a11080c2040503100c8400e81c1e10703030000303818203000842030404038004041e40c81e4540c1c010540c102042d00c5006803030a01600e014108110600760030010201144110300850f0304a000040d0203124042250443e19141e01c2401c0c201c10601c07800103203c2034511b415030f004158002203500b5400c980001001403055009003840c10003401c104113440e07100018640c24008200320200015210744040680d80d40030704618800095102c1300c18070140b40b186030510b030007100150028241c082c02540e196100c0042e5040300300a86201000c11080c0800182840004001820200710b85200003100819a100510241c01401003441c003007065030729900c1c00c603a400c1c4000d401070520313170b9104d041001c41044902e0703074100045d061860900501d00c01321420301c00c40b44000c005654401850005440c2c104102e034030414411410110303103171f9100083c02203200d18044110000d41014040c50300e4500003209070072060180500c1d041000d138550140d0b65094000b90824044070865036546421481c1441c4804a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752972697 1250 752971447 752971451
    0x507080a02070b0c03041d0f0c0d231609060e15040902030708011d010503100902130c050408070b0313060e0307150906050106030912081b070f030e0904030f050a030b04 74
    0x100d5019030080b0180040c0c86c03a42021600c5040b01c144140307d003903c15110711a58150704c030042000c1d810030400406000503c2000401c401c1c0c00705680343c0503c0c4094526103c01038000c0700700003442c8915000b02c1498041030624014442c10700720001c20141d41d550695028034842c032000b0701140c0480742507078010a0402c0040d5940d00e44520010301e0500c003803042180c070001300407001c48400040b4104605880024006100010041190030050850803d050742c204060a15040c41c00441c3d02504022174190f484140c2e95620301407080345022825803003412644070074030902034495007103d11150030a822220114014191038a0300e1700b14410f0420040403051801a1102c00002c10741007208411b00a9000700141e82e079504054041d108040c400900f80204005801541c3e4042e0f02d5103608a0341e22940c22282038000421259168403014065038500300700140d020815603c616940260002a500b4032914203180e5000303001d080201c0315a1061000110741260323081e00c81d62180e4143c0c1002041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752973947 1250 752972697 752972707
    0x42306101b060c082202040504020a150e2706131b0f091211010804050708121c0c210f06030f111504270c200d0507080a02070b 56
    0x540c1c01401d441c85030303001080300100051001e009070000d0807085d0140080340c50307084403607500300300c02014001d0080380e12541203000801c000c20416800e207005d10320740c1c036443c4804005400304911004c081507154085181c18600d5018011b00381c0019400000030344503c012100d0715242e0310054102040c07150b05a5014403006003189503c041003456150fa6a1265491147c4514041c00c0c0e4440c0701c08090400b1541000b016000c0d4420103046030b102e406070065880c401d44441140b03007040500c581c0f46030540004180c112082c0c0c0e03080301030146664180020044d040c082c0c0006007000300004002031104040c0c003e250100312554120080b2000a950108070554603490407030445400c16406907400c803a80c01e80c1c00f6050815440b1040c20840c4203841da0306191404196680d84410074084103420650036401a00c01185401000d28241498845540d030a41031405941c0d440350311903001c00f842d40034940901800340c02004591849401111b6242c2c1c800b80b0340c1f000d91030610315501900d05c0c5500094 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752975197 1250 752973947 752973953
    0xd02041503030906050322030e060412020103062903040f1a0708090c1c0804030501020a09080f01061a180904060606140c0c0d170d0b042306101b 64
    0x100305001d8078820340700e050209884510468580c00f0407218041c40180c3c0707152140440010000b030b6100c05101c6d1801d441001d0382d80001c43d0032038110b0360000e0320007070007900c0c460110f43c0c150198001074a00341240c20102131540c002c07100003200e0b02220b240700810000200c0c0c148607902c06e62401103500900080400880200700f4a48c07402e007100c1780700006e903200c00400d22405001c90410100400286201d8904040d4500122204408035049840000c10000080090780070300140c5010031403500c402c1710b050b181c41ca08904221411072050620b91424500b8048101d41c80740300f9115241d54442240c0341d176422800c510b18000d40742503483d0b01001381c000300001c0140c0d41c0c0148090326840d1f0b807045804200c80b00c004034203001c6c2c0510b415032604000350101c814140300e44c0c0315004034050303a012450100764038081c030105d50101d102c1007012900d443d0100a1810540608040c507040300a6080082d4203901401240600190005114080c0d003101c00c1401c52040c0540c0340d00c4040d41c200483d00c0d21080c9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752976447 1250 752975197 752975231
    0x3091703030f060d0201020616020708150a0b06070503040b130b120709050a050d06050403031b0302070b0714030a090302030409110904110306130b011818060515070209060d0204 78
    0x41c1c101c0d550404800008050f0300b031284a01a5080d07060f001010b00307469550727070302403241e80c824060300441c8540403000031142d2040284160240310411201901d0801030a04400d4036840c203c003a0080b2001c00c40600012000000c4070112410070380301a450b2b850707440e28418940850303030209554260224800c8a00044070140f41d00a034180d44498100d00e41d00ca0a100c6022500e124030b80d400155038551314040f80154119a500c944a450b0010701501c020303070010820800c527903099000a5000c02c503c020050030030b41c043d404c502ca41c05c080c038030ba41110405080074800100962021a20b481020f010036008005960140085178000c1c00180000800c6845c15003003544207034445c2d800d040036a10309003401c0b01202e007d85800340c8001c051121034000d960241144960090402c0b4240c0e080b401031101101921010b41803220003940c0280c4010313000802e490454005510130340d450703566100d0030400d500440d8441035043e01e070719100380d940c1000070b4890720614502a40040c100740c0c008442d8401c034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752977697 1250 752976447 752976451
    0x1502031329160c030509130509060708070315030201210204141806060702190f0303030c02010507110d120b04020706050906011a1806070c1701060605090f010c0309170303 75
    0x10000c0d001650380c0b145500c520005880c05a0042461840380c28042441349000788021500034000c6201000001d11040440310200c0c0c14003416080340d010b100b250f41d4084005904100d0320315003440f6000440307070024603400d181e1000030b0600003804900d081d42c2584d82040a28038071480b10071910340da81d0714103003007180c0310072480c141c483c0b94240ca0320040212040f51070ba00a96024051904040c569800d1184428482403525241e000c0309600084c100c0c0f1001c9080c016502c642d40c0424841c2c0e0b2950041e00751400030b403500c400e10850442e00c62261f080001d140482503400d2520780d04080e15801504d00900e400c1c0d4a41d40c1142c00042d0203030a0061780d03000140200c0c064400c6988030b03070307036051078601c2000c403e1500801240c08001055158080319070110908000074641458115a550340581c00c040343c0c3d02495821907001595104100280728020003003100c0d0034000e113050a0703c40060000034209001d603051250340c98072070080c580315481000241501040c0c0402d84004021619669001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752978947 1250 752977697 752977763
    0x1112070204090b011530020705070305070b1908061003050c091507020a050607031d1305040c08011a0604150c020a06021b0414040201035415020313 65
    0x1409980300c8240c40306c1d600c40d4440c00b035080205200201c0d000e294010754464241503c10788103d01c07000c004203005005070300003000d41d085060383d164080c45951101107141c800315007d10503400100141a191500e0319621441d00303140000345961030050300561805006003258110100d60380b081c081c40d85080040c0300450088800e0760b021b9641d0803c00c041440390720f10081c005800c08100c5249101d000090b9821603000070300381000300d00c680c000032040701c00c111016075200d603101a041210403803c0c810b5100c00301001200d0400d65000c580032408511491041d820780708040307c140d80d450740c420495841c809a0050840c600c1c80d40da80ca00a44c0e89080041c121000241000402100d01c1c0511842c412003408038160316883d500c80e00150b008143c5012030300700301303e8046030182000410180807a100820444042c0701b10080440410601c60600c401142d41d50500c444580401d50140200d458004030034000350380d9035503030400750740c41340784410000305080090b20142e142c4110000140e481c1011b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752980197 1250 752978947 752978957
    0x90f060c021239040c050d050907080c012006010b0a080601020118030e030c09090304290304120918060602190b0c1e040b0702101112070204090b0115 66
    0x180661403281c58010040e4544034030090301404503001d102408002807240442d002c2c001d04204080e020130181d070030211003080003410000d0f030f908003001c180c031503150406800c1703005281c01424078443c81d03692010f4601c22811f0044061900300480c00d9a801302070200501c8080c0e81c10b55a45030551a955004103403144041011a800071b5010752051141c0f4801100c0080c0c0c90f03802130078a850940e02100004003098242c020a401710701c043e19050a124040d14180004543e01c500c1c104183d8420408081621040042d840d912a2802041d1007601c0e0043d800144c4072150350010102a2031200c03099010780140e030103810440b40c640100d50b11060450b4102d0b000d680071042a817120480c10001007800800e08030100340883c07031918001000c4c00c07a012008003074100c50504500c401c0381d16007180d4041002c1440006d85041181040c12841c0787e0a0594181749001c2e0091201407521060501c02c6002e42e80808075583d0259a0b0320780282c00d00350382003042c0041c0c82d40c5070400681003a1034040c00c01c020030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752981447 1250 752980197 752980219
    0x21030918130201110c10020304050406060201180204020307051204060b1c030f0e0303070629090f04030e012105180d0e0603060109030812040308150f0d03090f060c02 73
    0x142020345260311488106070320409034482035005680b08000908502c90764807640580d0807041e00c43d03801c542007014194008584440c07404041206440780d5410080859040c800c2c2109a6200104035052095048401584903511444215400e0180c24616042c000b0304105000c240017043e1302c0140d000788161003180b80210f501c2e400820184035084010001000c030a0f200300103a01c145000280048001c098a180281703036142e00c029916008803449030410101601841708014903410030b031924040d1403085c1a4074140e0b00744060300000800150a0200556014401e41c0c8100e12404c3e102c82d001e506a041600942c0b0034000914049942184503280c0c40f440c10440d41000444607802030f842d0b0303114480d051581092260681003e0b08907418040c10303140c00300c0043c510030043e02500341c01d10007030101442d0500780202102809403451035021900d40304074440e9210f50314807143c880020342d1807074201c42240c6011625814142d00001d40020380950100e06143c0c0904050929070003214400255 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752982697 1250 752981447 752981479
    0x1141503010501050d09031412010e0112120e0303040320040c181202210d0815010807030203130c091a0a0f030312091704080d11030315210309 63
    0x50310080c041c1c035020a805014041e00402c40350042074034644a4600000c0310071011000381c415800210744800d59a441000611011103c4880e1500600440304807401100d01c0340c550b500440c207203421031800c00c445c0268041c482d4604000700c90003154060402c000ea8062f14950000042c00701b50000c0c41030781011071005007203200703510f01d60181c0d104103040707000c03680b5140d160103810240c000100d810009064000c607070302003c0e540c503444100ca1079002d0440c9042d501402819014003c4c0705006400c064070110645990100d07006a001e5041e0500594135124036420591484268100600e4601c1100f80415144481d4104001e4031450b03449024492900c0c6003044a404014014195005406c50301000424400c0504034502120103900244891203074450140801c06070581c1012403800080800003500204441405100030b4a040050640004281c649030721001d80fa510010560320004026644d0b0b2000b4041c500351103450150360100c84210440d10ba07046109400d200c1d03136507400380840e4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752983947 1250 752982697 752982739
    0x120d1d06010f05130b0303070b06150309070b18040c0906031a090621010219080a05070e0f0a0509011508012103200a0c0302030609071412010b090114 66
    0x50310b00b154185190641080180b042c04540204044001901c03402e5078000c90320180020520b031800f0358030107402e80c41c2003070034020007141900d0030f030070005010000c121140c0d40104a80c0c040d94441080301c2d540350011404400200505410582c2c0580f800b8006401c00360400342040c02c90300240c03000c0c0000802c1a45900c840340d00c0c20440d42d0416000340015426251600071400c2c1011180401c0d000620400c50850032a080080f09100700707420113041070340d0b054000000b1039005140b0388080c0103d2400780002030894070903000d400d01030555202015003035543c03803078403101134000a041d4003050b40c3d41c1c10060018044400794180450040c0c030004c01d0690850a0207015061140203c400000345580c0884044428601c40d03d250103c00311102c281c2c01d410701c8600c3c5d41c03c0c0a41c44d81c10f130711800e40c010181050070150052096a11905040060406171145910400822615812294081044940035100a0054980c0140c21200101d82120320109074003400c0c0040c0c0b02c8900c0300800f400d881b01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752985197 1250 752983947 752983949
    0x15030708070311011701290f0901080c1902010f0c0c0c0e22030804110109080c1201060b131806030305030105190e072105220302120d1d0601 62
    0x4207908041d2060010800340083d00700d40000c1854150b400c803490864600d00c840083c0c100484021100d045e031841c0c42e43c11a800703900c8643e144005482c1000060229003544107a0480741d041c41040700004400101e400203580c10b1480c4ca944c580d03400d480d1a0ba00038000c05030000c01d01da9070744c82c02c071a4a09484c410501e250200d41c0c03019284000380c3c00c2c100c4201854030001c1c1103000e0381d42c3c000d081201400d8900c2d0020702e000d00c25210324225041501d0505a5800c40c0740c1460b0401040e00c0e420001000d001882583c54030007680d40881e001c21481c00113000d040c664025400d02400011002c003480c044a0314441203454403256682004810b900001c252400c0c1d20000c1c000803014030040c4120b150480743c00300c00a081454140e9107d41d111240d80b400c420450307402d40412036003d5801440311703c03801c08984280018804110320b140068010349400d04d410208006c0109445841c010180200b04000c1018003c09010303071510f000340d84010140c4101c1c174072821070301500d415a015081001440c24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752986447 1250 752985197 752985209
    0xa051510030825030905040c031b12020c0303070206010303080106052b0209090a050a0b04020c0312070908070807051e0d17160602032a070f02150c06150307 69
    0x100d642851074030b4809031500404010807542e0000004202600c04148181c034403284aa03d1310100c0500c1c1078104001c56641550900c04e0501b82040103140009141d00c48150391554100480450807100d0848000c4c007513100c9030f141ea880000b00b03000400f900002c91074100c0b44039030313240c50031a0380742c0c0403c9540340502d2049014403044580b41040d4500140050310002ca22800014200012100003841e86038041d1340d14800660b6030824412801000e000d02002c12005880941c603002694454580d2441005248082c2403101804191b1442c0724004110003010301c0000c60fa1100d44851901e40c0720103440c41818443c17900006c07088448824000315401207180100451100300f1103440310340c1860146481c40201020400130a90b036849103031080b58901e80206001600c0e890056040003034220072105003103a8a06821446030480400011030300d4169002c280e184510314144041400d4400e0b070324070210504400710300c00000c1000040c01b0392041100e1002044072507404420f1580f5500280561 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752987697 1250 752986447 752986471
    0x40b091f02030a08191b02120c031602180108010b011706010215040303020d0c050301030c0b0702060d0902190902035103011e150e060f0d05010e0a0515 67
    0xb200118000c08513194004141814520340c42d02241d000c0c400c42e2080c5002d001554030030714004400c1d0f40d04115003100440882d4080b4a03102810a0207982c0e030007411041d0880c408014010011502c03201020141c007070305141c4812855071074004982c00380516000300c50004102e110b0f0044458be4031003241d4000d41040e0081c11480d00780b039000c0005010001c10a5050507000c00040c0c6482e80d0340d100f10707041c10030f50740e503020780780e50441c90701d64202c201e540e0149041c20390a00c03000b00580d5402044170007015102c3c0d000114100d8038404512000c1c01c50404650740c2080ea440043c10300e81c070340c00442c404e0161041040c045560044211043c4c01443d400e0200180c54003550081c3d582c40710520801d149441c40c12050394441c400c0045e0030f5810030700360b20b03a03001ea040c001070140c0c892a002e021203074151021056002c5040c5070b40140c050000800b0f9911441003034050701c0c0f8944030203120010007034001000740000c41480d80400c2c3d41302c140200465452140151202100c000d151525005400d80880307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752988947 1250 752987697 752987707
    0x103020f0607050109051608071208030115020f06040809012007061209211e020a150e070b0c0f1f020901090b0a120605041509020a1202040b091f0203 66
    0x18021079030854034048440b50340e243e079803030041030b0108002c0d0101c0c81c01c143d5032821a428100518100f01c2e40350701c0b60703081c003540405640000e40b107601500c0c1507800c4202882082c3c3e800340d0007249460710040c0b06221030300840003440240b00b640300051003c80000e0302c0b04011101c3c1601c3e215840c00355401504103076041901c0512400d4496a01c03005200e20841010490710116121400700385c000b03c042000d807606088440410b81e0b040001510314926900d0403010910080c0406034841480c0c2c54020014050911105e180c92460b5110440190f400340869032003644603441d0034031a82c465507402c8401e22481d2030131358100d20001450f040d03145154281d01d00f02021a604100a9000120703858188511000c0100301024280e02510424200d0740c0c440e05189801c0d0481c0044070025080702e4065401d1441c2e80026428919201046034585440141c1d00d01c00744404a40c038803e020b081c0b120312400003400244c841c00b66400740c241d81c441140d4211000b40c4441700c408440440b1404000541c0040c82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752990197 1250 752988947 752988949
    0xf080403030b06121501030c2307030c050f0a03030f06261219031b0e0907030b0a09090203070f031a0405150403081503060105010918020706140910050103020f 70
    0x1040200b980050300071800c00260410f039150b0400f088490701c040c44030081c02e84c42250703803601514801c040e2078107124540300c2002151414040c41a944861016400070352001011300c01d0804050f03141d0002e05807044070350a070b80905d8031800781070010f50000b82030801003a03419086124000c1120340117002171805c5410b604201d075000c2808a809001030107460f6034a03048200d03901c014004c000340305140e5441c200c1c2c4034001804a4501550303c415401041d4401101e10781c00c0304103452042400c6032400e100c1c0e0307610502140901548040140c0101200b04e0001d00354501da000166014800c0341510021910741811400c04005884042d1001c600100c2c0408a1018003c84640290140302aa05804001d80003001081d1064804400294003282004040c850000d1000c006400c00c80240c0b856500d0600001c005180e24000c4031002d040c407036110301031040380c0e03811180c51540c071250a104120105103003620070f9404981100942c000d42a05843d41c1c00e9600c070705410f880d17000300007881c4842940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752991447 1250 752990197 752990201
    0xf04062d0e0d060216083f040609060c020328020a2009010b0319060501120216050a0f030906030501063005010e0114010507050c011b141c0f08040303 66
    0x208180c031042d5081144c0c17000d00020562050078240107401036031343d40c19001c60b40084040102210403802c14014041c40342401a020502d5010b08400e030000710030b81715400c0c00402480c1000008001c030780703410a28024981c01001402c80d64904142550b149564845900a000c00380030011006030003200401001841860398174584212102c02d005c5500070213004122100d100b81c00c0321841d40c0c00441045003040c00c1828065004100070402c0c00032500c1d140000e00f0700b030106850058010b801041031072246455a08190400742c200701110402c0d81c0e0f41c00c08030240070f01028280c0014000c1d840c0860618081c0c0641130484060340d88492024100c1da0106406000400002d00003401420040014001c503000d480c1c0a072007025950b900d15403501d50183c544001d0410103d052140c284003a4010800101c0d000c40b582c4000c0c00c0110701c00000c0341c91840404a0580d000301004200f8801c07003003001001030b54180d40140c80100c0c4a110301a000d003a80c12429078800c010002e071000740000c00103403080d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752992697 1250 752991447 752991469
    0x703020904050f030a09240c020609030c04091a0106090308160c23040b010e2416050c040b0a0e1513060608060901090618020a050f04062d0e 62
    0x307003060b42c80102c2c01c83c0b2104d056600c00b058030030014000300030603c4100c1d0034858880c00c07289145814080020303071181c00703400c0301c01a0401a01ca5800412200016282480b00c82e4030440020410040d8818614202d050328441c0c8000c14940d41418001064590040780020142c1c1d13003000401c0c1c10000190140d050200440d20304a490881d8000002854545603422040d01c02e005003090301c03981940700501c001c5a80c0c00c2102c0b070400c1000341078070a0b41e8584500b50300c0c540780580c0b418842030800c1480d2007820300c01d0610404c007004a400f00c03502441400704440105c0e03d030440301844031108140801010402500950488003040d03c04542d004064441010300b0107000340030250304c40c14281316041203031f0703059020002244022080080c0d0345442a031103809858440c1003085194113005582020102168a000070503074002500121680502c00b9a0b0440310300032281ca90303030380d00c600e801024007800e25080342a0000a0b4480440048140740d000c00f150746c03e40e560641c101400003003041180c03034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752993947 1250 752992697 752992703
    0x1d1f0f0911040e0a2c030c0105091207020f0d081308011401030b070507062a0924180e04140105091f0b0d05060a050106020607090f0909060b03100501060f080103050703020904 77
    0x4241d00ea6480310800c00c05804200017040c090341c0c4421510701d44a0950b00d002300303658816000103640801100756181138031409501681c6100c02030b070701c1101180040545071800342c44c130000400c550080040042d4000241c800c2e03c1c5c001d0081518402d246900d00364280070050010840b131000805040c8900c028240301401000085038081da02080807403590391500d04465464503001c1c80e1841e070341c0c10588003802800103400481001d0f0300b50700498150781c0c1c80f815401c2040680c031003072103494924041f82d001601011201c182c0e1800c0614083c03a629250801000e100e500f44000074846200219150380b107a0800d03042d9044c1030b61b007900300c540144031010f4100d510001c85110038010034420007600740309210300b01c4001495418410041e1401c40014800c80820820020500c00005442658401c440e100100402da4080d9850400041c01403403603200c0d058840d01031154040d0049030030440c1252640c0e01d540c580035545c3c000c2140d981e042400040d00d55400b03c002000117003401010954000c2c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752995197 1250 752993947 752993981
    0x1603030318060606083106050408040b04092007020a05130e010f021e1c050601050d0911190b03130f080c070806010608011d1f0f0911040e0a 62
    0x505599450b048030219040000002c28403010000400182c0c2901044c2c040c103502c000c1d0b901d9900118105210601d854000d1149454001007010420030b0030035503000d0407070354036a0350b101c603240c1c5d42002c000c04840303845580450144070780c504604a110120b820198020b402c291206050506011130044088408000325550341e04403032408900b0f200d000c0183d41d01000150742c03030b102d688100c2058809181041c9401d201000210006082414411903854034181c000c6010f80e50b10f40142c4250081102402c0140e0514503854104204c1c00ca1040c6002c03c00c40d91001103580c04100251000c642b8000c0002c4000d042000c114482d00700c42c04980d810b0f218142e080c810324075640d038000454101d0500e2410941c4410b4040c030940505002003409401e00e0b2038180030703030341c94044100b58401e0f07110081046040103001140f444003c050f40e614508403103160003000350741d440d11a203217020400d00c500401c05161484010290030440e00b20b030220f5124102c41d200076240c06070b041004140301401e00030703440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752996447 1250 752995197 752995241
    0x822082d0d0f0b01270911190516110d12080a0f0231030c1d06040207030e012601150206090c0102030a1b02090109020301080c0a032105043516030303 66
    0x10300d02d4020341f404002c12586941e1104e51035990410242c1d000e800480900c2810f0205602608c2c880303140039501034000c0c440e20f0540b0700190104590400143e40501108850000c1000e5a500150002c0c000e0030300543c04c0140d01d2241c0500d104900030002400c00450041c2d0300c1c11000740154001184005160305d06407203581d92544e8a241e05c0442e40d00442c0501028414100c06614035040194070041c151015032520a0654000345030120044205e41440580101306003410b151101801e041008012603242c256140e07400e030341e0f0380540d0000c514010311400001404400000c150309206c050113070025800e0070a0701d07000f1b440481d80ca19504030320180300721321200580c1d240140740b4000c1540020040e900d504100160f4142904040070b01d000300000c1404200062411218040040340c80d60081404c00c0f082004446600c1150720103014242ca40c51024034440458180400b280740110f500814040d5201000fa12442c0196000e8036401040c141003000c24082d030081040200803004000c110b0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752997697 1250 752996447 752996459
    0x9120309030616090e1b161b080f0f210c0111030402100c0c0603021e0408010b120706050a0e04020702030d0309030822082d0d0f0b0127 60
    0x2c00003c60390800b0004205148040894111840c500941400c0c1c401a607036251103400103114022114068480610010300c116040750f04098a8262640c0003401004450070078654108900060141d100355020f1900c20404050b000200e0800002000e0301821012031b0080380030040706190f20b1100d00c0e0460030481178052207028030070103d1181c1e18060140d1241858014095100300c4045500c06000c0d0182120001c10b08000034981242c62520340903031354020109001008411500c1c088030350341c9021801241d161419004041002019514111030b41c560041c0300e41c0e0b0b200300d482000081030080008155082c0f00c1c0c4a40b82c0e040c580a00090b14207910790740441d142211039500c1d000007d030b44401039005c056000c0b5506030800d01207440d90141c1c42000c10106840585910010041440014041300c41724049009030b844d01d41c07108100c02c103941c040d000b02519030700010035124014544907405002d42c0851181030354110f81a510100c1007000511010030354110315030840d0200e41c1d4030a0020719 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752998947 1250 752997697 752997703
    0x1e0f02121807120b150406031e02040f1a030d0f0504060c080f0d050f09030903030901260702150f10180e01051f090207030206060d0809030727110912030903 69
    0x91688604c18450052401d4440c0c19001801021032510403400c0c04810000314402c640c2c180e40320281d0a4064418041a20000e0001c3c9034a106400c041c50812103140720100c0140400301c04690309400344c43e01d01210402c211500049071949101040c02804144915842400034500c80b61144a9440c981481003c00e844103030059400c0051b01d680722410800740b00080c50541d500305040e0b00c019401c02401e000042d8880c069014658100881a08101e8144611500c0f01900c1d120428031601c1a00780060001c2d11008000c3e0340252200807000400c0c141403820301d0f00b0f80301c2c503052030320000a40d062001003072138001c0d00f1b812680e01c26110070700c82e00381240030707c41c00f401820082654002004e142c030701d02100180d540e0008040c00c2c07040c418400401d0f0007040b010340c401c1003205d80700c40001ca0b5140c81515400b41c0f04440f0b80512498101240b0710760384c45600a2503c15802544c0b0000d4002084d03081a80c0e4210058a05807005000407801c80c281910906080c400a800b540d0900608001082c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 753000197 1250 752998947 752998979
    0x306210f15021204020f09070918061d1e01050307050108090f161a070b150a0305010f14010503010e07140f090f0601261b0d1e0f02121807 61
    0x10440c140c0134002103203001c0080320f44280d400c0d0b510301c1c030903d4940720103407a17214948206090483c121000c61080260303540900094040c0802690040c0150250390160802c11100c103080c1c461102845055500388115040c101c60300200201500c07030800004640e800d4021300051400d1007500c1c5081403280b03051003049442e04400d50b50b070306001d142195610501291b02c40c40a1305400810a10021503405812140d210804909400e050103200300030a00000c0b06506c068055442d01d850003e4042442d08148281100316a40c50b00c60390322101054200c0d240c80394091031680c0201010402450b00068400c004d510050003090001401c2d00880d40000c803c480704c0541b48002c4040002d2507030049500303071030321f425050511700c0e000e0000184c0200310760181030300c2004000c1e1501c007118414a00c00710b8074940011081440305090b040c0c115604883c090001c1500207007130400003a1503802500c2900c01100c5101e103006035035100d0141200b40b170302801e00800c03c031740601e000116003a00d2542c0035603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 753001447 1250 753000197 753000217
    0x1c03180506041104091e02030a0b091f1b0e040e030c010e010f050f010e0606040b0a2016050f0310020a022b0507030f020c100e010306210f1502 63
    0x140e45450700d001c2e443c00a20000d00c5100e00d14101c200d0303012614107800d6580441000703a01808561643c00064945128114020201c01040c02001010000840da03841001c10a24209002d5911846a90b042d075400800d00150035140c1040d044459201c0c04030b4070381c50540584001441c864003403555003151b122205506041c0c0d110b5171701c904981400d1142072030b00f038402c2408000c2da0408100c840039122042c428280c1300310818010500c5d07641d0b920100c0d001803414842c210f6548050394000f60150041d0380d01c440e42c00501020319600300d1400f06000d4061100304c41c60240b0030741450300304810070703440c0c842242c1c1600c68400007000c01c11462008112900180c2c000f0031044e0fa6404030304d10a0340c1c0c510b0074100d00900400000e070410b50403605581e031203035050030300042c4e80d00c2041c0124030f801e500300b86c440d5000380c0400004603800d4001880c010314130303002c1e80c0500c0a591a090500380305a01010035034003200125440c400450300855400244902c500c5140704a0004158440141e8000344041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 753002697 1250 753001447 753001453
    0x4150902070201080105061e0c0f03120105030c030a05070b07050703061113090b0a05040b01020a05060c031603050f070c1b0303052a15150a0803040602070501111c031805 75
    0x8400307544e000b41440707004180842e0315900c0c2c460144001003a56101c418091084400070960320441501842110a00d031403160883e43c940c068030980102200d002e2168038001c1c001c008511116040110301114100e03001002030282ca46840400360b219408241d080d00c003070080020120004500b8000c6062071480100b550303440e0002840e00c188042003984c4660b0380c440ca00303c0c1d000e0994807902d043e402121000c940000e15603141100507802e00c40c1c4c81d10002c0c5140074090402080381d03000c2d00514012070a0385603100c1c10180500e0140e0845200343c580e45160310341c00000490580c031498403150864452005c101a0001d502200c0034144038641040303010850104640315940c066525400e1022580101c0003401c4088102064980c1c1f2500f029a0401104600080e06840c0201d41e1341c00c817000181071725241940e1030142580700e80250066800601421200140561051440130640003e0700f005d0000c1d10000d0309000841f41940e000081030503210542d01c28169012001d03520407901540103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 753003947 1250 753002697 753002707
    0xc0301180515100e040b0103060b0a080a0f1b1401020114060108040f14030d090b160f0f180b0a1112160c0e1e061f030b04150902 57
    0x4050954001034038000c4260303006061640030900c0052000c03606100161205100c0d00e400e03602c05103c02d56500030041307808a1a060004115103840e20034102c0b802140100040354010041210920061050781d6085d0300007002900481c0c0703000401c0c00c0c00e034442c2980e0910390a650790385011040d0b05500a041c64007251040c0703c01541c0a02680e80d20301200d0005000340d02e0000c0028060304406807001e045542c80415040030080410700c800c0d41064200c00316900c40c212081024080c150700705045400e244618081528811014503101400700603444100261812200072038010041c4840001000140540108600d940344100000342401088459840c0c002d000003400502640e4070002165010030701c96168a00c40d2000c0e60000218000302c0048510319082031910180944c1006002c0711012003070001d00700d00401c206560301c5400b132100c0c400740e541e04104619241000c15001180807007808c2c1048141c860742c0030b480042001403001411b54080c01141c0928150f5800c001c1c0d4003a40019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 753005197 1250 753003947 753003949
    0x1e060603140d0212040b031b1305010e0303030403021203040c1e2c190b04051f060207080a230a05030a020c040b060a21020c0c01030606050903060f07021204080c 71
    0xc01a40740c8941400146130b01044880200300510903440355403d0700c040440402e01c031205d42d20007940d0b0710f84505851070311108807602e0405204040d1043d02d0102c1e0303801c0241c0d031071414041b042ea072003150150050016070440551078090350340300510445062030340000104035030f86030b02c000c088040d030ac182090341094100504804282820300f40c1c16408260f26102c0c0410340c8080007030300d074000c0b810341030005a6100034203804003030144462001e40c00ba04110802109040b01c0002c6107403807080074040d401142d55024240d0304c0701c01c04c0c020080280c1000c4d8210000c04d6102d00d100d01c80800346440d9030000b004420301282132107101d01040300d031600005041c841c030b554100b201e014042011207040020f198488000f03900d91082c100044280095403207401642031484103400314075007a501080d9680e0404034101e13038413010040d071282d001c00d02c0c11001007640e610070f405462020002400070b100725100e107807948405050041941003148281894a441c081841010388020030362640140030f8111400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 753006447 1250 753005197 753005203
    0x5010203010312050712120f05090a05010c0f09062d03051501020106080303011214030301030602071a04150b04020405030d030219080424090c060f1211071e06060314 73
    0x121000040203400e01a65011806c41c18850030000d2080c02c0c1140c0c50005240284041d10030b80c0203500741070b454282000341d00c6001060814403540b09800030020000c40701410b40d590075802c2d01d5140000e10300082880014090110880038900780c0b240070707a0a4800d414500c6c201001d421a10340000e850300140161360911011942c0301020900090040078100150541e89000c144648240511015104814800350b940f0f0420307103100301d2007540d659603168205070000c5c1d0300c80002101c0e603d641c4903621440e0030044200500696100c003d8135003030141c1550082c0034055811480d644940c0c200800a82c50380c04100b401c1c0342c001551405622120101c04440d141d206918004041c80000010000000e0110f029032040c0e87c1c041e000000c0c8800c5c1d0440f0b0b8001040050401480002c4034900414400e4000d66a01e80d0440c49646121a891307504180c442500c5000706034130030300c110601c183c20024101c26651050306a00c018090b210404c03d44a1400f035a5595200b030326007070070001154038000002c2c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 753007697 1250 753006447 753006473
    0x2070b1306050a0c0f03020708090909060405071406030a0902010207050a26060705120403210207200319020102150411010809011406010f020307020a0303020f0f0a1203020306130504050102030103 86
    0x900301003040e0280700001910310029540c003601011f034001018420000103201355400030002416252013460000251699503c06640079641440382580010340c0311384401800410a0016001509548a8000400c060200d0102c124154046c8901c04280b07600e601c44890020703d20915200490129214009045904602181c245800c50820054170903002400c903030688411581608180d5180d01b02103e0760301d6608018820b2011020342102819196000342ca81140503003100c1c0c4040312000e040020b00883d07903c0c042c1c1c05800800c0048441e0713540170380300c442450040c016075902c0210540c04110501c41164121246000c43c0314800031540d00241140d4810003000c003c1000c00c2c1040903404800200601d258104881e20341c004a0051080c010346002c251b0207003c20032540e880e4640030b51503640e03100e40c0c1860b51081d000c4108405000184408500b504542601170481d11110100c029510040420303030000291a5400c110100505ca4107202d1030003100010780700d5041d07141c030343d00b10403007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 753008947 1250 753007697 753007711
    0x12031a010903020d0803040213090308070e030d0906051c0509071403150c0a1b1203231603061a03091002030405030904050702010b10200703170d02070b130605 70
    0x424002d10040c1c88603c03054000780e030800c1341151a9541d078400a07030000100f080340255103090911002c1015080b000300d500801050b00e44a00c218281800d00d40d45004441a410015181035800c110150090380200003000341401362002c1444000303a10010354030f050314145555032040200f0400070008888014008070103c0180c4500d45402541c1340d0101400340c143c034442d00c80040c16405850007500d0284861040c01c0e14a03100121604240d180410307598040c0303000c40d040121048005036081e1107802d80d60040841600141c680d9003407009900c1c1d10180355400d06944010100da04c000250b629183d1030038695920f41ea030300d804016981800c01c1c3e0000d03550300a00601c00c0c4000200080251010300c501a100000e20b0740d83e401003240949000007a80350040089002104180d070300a22640c8950485e82051090340d22111209070344080d90311024100d164148141c5d161440d400c0020b06034610350708005401c01c000b58446d11200402681d041020800750851002040b2050090945c0310403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 753010197 1250 753008947 753008957
    0x60e101407110303070b04240501081005040c030c030b07030b190b030603070906080f0c10050316051e12070f05041e08060403030b19050d02060c0a12031a01 69
    0x5420100209401808002402e0038005040a507280d201001940ea8040d006001e5500c58145403c2c90030058855107420f16007070501d072080c1141e0340780034000c85048030500d00082200100c404140c0f4014030300a04201c0d1290700518000001c03810100e1680081d5015860300b16040c1030014001c2c00300c5046601a170b0154410403448100d80248400314001c895000800c141d49503900780002e400c04445411a10009107000307008168068000f03070803074480444c0c50855407082c89c2c00d000c00591400e0004e040001650801c0041c030048645000c5102210080c10124100401c5031003100200007800304a00c03242c18007241412812401004994100d040c5042c442851810382000030443e1095004003038080d42440103080300c0080c40c40d003280080070034109903000b82c142854010050704643c002c80d442204010641c17100350000880b144200c4200514000f18401c56a09002441c1c00144600030280140d07a422004a08802c01001521210b581c000139003a1032402c01ca0340d4031107030020b0541004 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 753011447 1250 753010197 753010217
    0x3040515180d03110d052404050f04120c050a05060604061d010303081009140921041a09131b0c0c0504051302060705060403300906060906060e10 64
    0x907602107004412010686000300b602c10405941d51558410400b0f103214040c075020403c800d00c00150340c0044041500e501a829031000c0c1d00030801a250140d80d8201d401b00ca142c08540003402c0621040c40e62a0796040030f0060100d181c444900706540920b003500c0940140f01040403520b824481c6001401c2401e02ca2068000e200c86811180300050000400780901d14000c90038000c559041040101250403040c054018004030190300060183c1e180c5e41c1500c01c0540140c801001600201d10027030030300140c10308151501d01e01c91515442c9400d04480410204840410b40d12036000401d07040b08400000714942c3c40120000c425695107050090400039140459000a2403955200080707400485000c1426101c2900c1070211422a107402503104100080101c00c10001040aa10a40c083d0325003140b85c1e02d0b40400b01e40c0b80f100c2d43c1c64482c401d51806842600c002d00942c000d510b02e1b40205c200260860300c48a00300200c0e8555042a000300c0c0d50414400c0c05460b10040c10071031050719103402c000301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 753012697 1250 753011447 753011491
    0x305160e071419020c1507120813061e0504050a0c052209081b0601061d090f04030309080d0f0506310f0f09050c030604020a090b0d02030303040515 65
    0x80c007548404952801c1c69076103c1090b94405c200c243c5894400406120b007010f1176141002041d841100100ca06a00d42c00400c030580c1d018080e12481403600c42403043c0c4409031541c0c0e9400910030309031350404084801c020800742003500d1040c2071040d4400d5004098a510b142003061042c2000d034007651042a00c20408011100144a03130b002050405402095400b0306c0d16200b502400f48507500009000580070018020000242040c120341e981e449000130184040c10300210b60613281103607070308220100003085055000c0340d800d43d4081d010703140000761074189503540e81701c036400080b80c81e08254495180e40c580346400d00c2401c4d0404012210f401c0e142c1d281e4140300c2e615040750310020310503150942480201c240725408c43c0f000b00789280000c0182c2c080ac05100c200401351914159081d204503c0f030f101180c1400514503026035002020f401810345000740101c003502c041d60845803c426030901003030040e1010005180914442c1011708886441c0d40401c07270303015900401c00051503c03040070300007907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 753013947 1250 753012697 753012737
    0x80c0604060c030b0f0f0625050c0108090f0618030d0e1c0305040b07030e100c020706091e05131e1409060103030c08030a0204050d0c2d0b090a0305160e07 68
    0x303000300c02d44000c6d40320000b500c0305071550f81d230f081880304101600c481c54004001001c00c00e140d41100036219401a911030416007603507501003032060509640214085000c41c0005035048810b01460f10442e4540030a09901c0b9003501c1c1e0006a07610143d10130550384d140030514000700341e10304105141c2085123107410f031030741c0552040140005040c0341d40d403841a0803851060080c0300d8146440307001404001501c583c000e640304000d10400d40007900ca940d011401150503280303244c10383d0030313140340c43c101c9810441040044c3c062424000303c00c59032038010047c038000400a100b01d10590307003000921002071100c8818280740c01403483c07519400c10001400080c0c0c100c3c44d64070005401040d00c81d126910a01c002c0001d2199411250307000c142c03c0400030810002103002e10036125021403007800007071410f0280c91580d44540051480954a540074001d4034030020140c211204004c0c03000d64510750343d880d031074200000d4a0080e040006114000e001400e101050750f40c1051003454400403550b845000ba83da = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 753015197 1250 753013947 753013969
    0xf20031c0f02010c0e1003110304210302030408030f060303040801061412160902090a03020d060903020c01030b100c02040624021b0f04050624070b01170a0b04080c0604060c030b0f 79
    0x1100716404c0b21b816240d64030990010380d0020003410303041e9503420070703090949400e0800c01035100340c0d90740c00c20140311f807034824026280901e030701500680c00d62310703100c106c080582c00c0144030f1034051005000002d0b1009090044200034810441c40007409801941030183c8485014078988040c0c1c450744100b0050340c2c1101002c001c40b8a203410060326002c0c10345c00114a080d450344083d510107428a034110502109601a00445129800300d50240c05040c0040d0b0540d2003501d030040d4011000c110800105004407440c6c6007c92004000140300d603180c010383c04008000382480030350f403415203002d81e40040d01000b14050440741d50a40441002d1a4400115640d2240da000c3d40540c0e101c5002c188151076400000041c10308544804c0541d1441080d004c007540c21203181602d901c0ca0315400010703581c0c02c044000180b03d4421001e41040149a111301d0100d0101a008a82c02c010403c41d00c1c01e0b0940c1482010b00444c0309030004903000704500c41c02400e94000100ca00d12402c0d120354615000d6507a503c00745 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 753016447 1250 753015197 753015199
    0x1b020307081b0d03020d05151020071d0f0103080f0714121e041404110403051204060906020616180b0403080301031407030f20031c0f02010c0e 63
    0x41e42c51950202c040259940307a0007006581c072401c1d200440c841e0701034025124803041080308005d10758594001664000108400c540c00480307140b12907456034030400c03420f20442000c60b0a01d10348500f0189184c603040c1240c0c4040c3d1480f1a000400d101883c00d001c8560308001d612010b104c1030f50460f22186641d01c1018800070300b0b000c00141ca013013040400f08d82c05240d17000c4c03c801d40f94800c00700b0300d402000d41d210b9031442040c04031100b1030b5401305900c07505540540311035540c106d44840e43c001c1400014111b00c6414400001d09000001c009801040308102002d0030200080c0c80b585090070107054402c661f0461001c2d5003103001040301b064103809410035a074a0f80d261000804904022070705030410b10340c0004a00b10000240881400700200095049038072414040364001c3c110f40d115900c0740490300004081c0c0700c80004201c00300700381a0045a4104036007807100001c8924100080c40c140d200c8012007011a8500c44c81607446400c0a0141ea45001900080c082354807a11001840c10500c09042 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 753017697 1250 753016447 753016463
    0x10206040c0905060d080318100606050d050402010329043218010c02010501050310020a0c1403130305010c0210110403080c03190512062704060f0c030b041b020307 72
    0x16440c2c2c4e917065400c408268008040c242d0301e04085205011000340d02092015912800300800881c0c5501d10440003100c00c542d803800e04042e10110754402800000e04268101515201e01c41c0740c071404404a1a20f030528034500440030b010580901c804c1c0c51038019000c49040b60007281d00ca0184c0011078821042501080040e040e540d00c6055500c268032410340b851066103001c41c208450ba4055101c82c1c1a0b40c030842c01c548040c803202d68004241d110ba0802c1c0000914000c0b0700b10001901e6012115200b2121000d4908201c1000c821890407140c0364403d40b03490b0744403815241e9180d014880d80c42c5114000001340304144d00c03104104d507644200e103c001c1c48401d00040131504510280300b582c43c1441d80c007100c11926041010001c11540120040110f244e0240010803094580003001e4480b811070036100000b503501c12200c0040c000801041516001e85aa0450f2003106c40c034030504803001034a440c00143e688100c0240030880d80384048900410481c04031060401e500001030724500c5520600e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 753018947 1250 753017697 753017701
    0x10e010311190f030b09030a0e3102030402041a060306010f0504050d030504050907050a020601060509030c0a300206030a0905160b0403120309020f0103020c15040804030c05010206040c0905 83
    0x11425000c00c5112107848441803250101c2d01900d1100e0b03e0303040341d00031071044480351a000000f5440740316412207000400d0b0182081d481d030342820040011504041d80303000b05d84000b0700c14800b40d450041c000c00800107900100700421071400e0700c181e03208028000c01080040d01d10502050b280d2101514203414454040c0021030840d110b42c0c02c0394003810300600560a43c08041c5030150040d042030086510a1031040c0024000c1c0340700da030a84101c598640e0080650340d18000c020b50b090713405080050342502a200301c50403151a61005540240180745c48440403403608241d8114400700908040c50320070245541e100942d54400a40c1d4001002c030000040110a601c0d0482c68460100001c1d03144884620380012301461420107801103c0c01142c6410b808a50401d04400f10f8440c0d88000358000c0c1d1681c50310fa20342d44264068540c105049040b129140d201c0c61102c08046000c680844e8110030000d0f080c010030000254010007800300303000501c4a0b05060b075070040490041c1c09440c80495076400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 753020197 1250 753018947 753018949
    0x6020316262217071a131502040815090708010605012703050a080903100606170403050417011a03030f1b1e030a02060115020a1709030f160e010e010311 67
    0x180103696030768040680f06014501449400d501e400040d01030710301e0154407030f05045081403100000e01c00d680c04030411800c00c4141c3d4410440f8140c24030001c0741c850b030900021070010420048010340300348c00342c00c0d00700d07928090603083d00c0e0000d00c1d0001001a411300004002070398101844200c041e840e0702d030340c20071400001d03c0028070140983c009009032180820500600400700b004201c0481c0c01d40603180302c40c44040308042038844a104600016007144000c5842144005191b5045446854914501982c48041010351115107942d800c69954610000800044102e0380e044000d5042c0c1c069814001100080113450050b80c1000c24440c07030f846202011002c041c010044c005000800c604060340e031305281c484e40c035009034035800098412440045501ca8911a068141d801aa402020758641c41d5480701400b142c80c5d2082035001400340882c8019a90501881c1da1040c48030b0011720380328000b0100d1645030f00300c43e07100e1900d07000c280c2c1c0140401d001c0c110510381502d0f0488805000103072040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 753021447 1250 753020197 753020251
    0xb07030e0d111606050304060e0a1205090301090507060504090f05010b0f0d0603020d241b03020a11070e0423071413060803030a270308060a030602031626 68
    0xc0c50082c0040f101038010501a8110000c1c0d80100d00412080101000c480b1200e965034a50040160a00455202c0301c80d00300c1c8500000c101314100600086110303032040e610140b0381341554001d2004128007050074000e03c4418400c50000c12480c05003404194500f016000441c030680a05011189001034901c01300da0701074100000071540601411800303556401c02090210f401c441c07005402c2c1c0f42600c2c441184207940180d1001c003020314215181c0740c94001d000d400035401035025000380400c2122400c450101030103200d00501c00625050349900e0186002d40101008101010702044558207007103014000081210541e030601041a03540c0d62558002144510742c0c0300555030792400c0c1800401d15404c08006503000d09000310062007d4406034415450340103d5020502c8020414864040420311030120103030009d0000c3c0c010318100c2c4c1c407502c070a8240c0c1e1044072081c4e0481d150f140c0110302640d000360001e00d4284103410201004900b2000480511006032210790800301b20000c0100e2a4901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 753022697 1250 753021447 753021463
    0x10503100807140a0905040309090218041803020c030a0b04060f0b0303070f03030b040209090604050411151210061e02030c0304090b090c0306060f0a030f0501120b07030e0d11 77
    0x8112088aa81d0707000c1ca40b43c202825000c0c0f40903c0f2680300003e84142e180c0a000e0140f039260312003c4001d800e02c02d442001b908001464031110300601d41c00007080c0c0340c9102e2080c4940350ba541c018544c00c668100170741340c028060b00751400f07a408560b0756008101d182800a400c80d50180000c0742041c0700e1007611003e0903210404550500001039a0130411020740f03260f0720b180344651400d1028000750b00800c4100d00884e035602e60012480d03c0058114501a40503d40c81b92103410040f00c0c403480d00380031807038070b121203070140341d004400003405491020080d08156200e44141c042007003040c20104024459a00403040e03044408a0203107000406000340300380d83c2c1d544091000c40b82c80326a62260700002d020101c165038081c07072410303002c1009403401c1000c40c2e210741000343c0301c03502c2c103250110324242030ba00ca0313141101010b98032280d210700001c1500495008000042000e40e011845003440e88143c400601a4001c0c14030b41903480000000c0071940301007141c8103051180d40045404c0030142480c0361 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 753023947 1250 753022697 753022709
    0x91609170c0a14010905060918010303081b040b070303020901020f241005030304290706091406100909080c10060810090305030f071209080c0c0109050f01050310 71
    0x201a400a98220019910250000071105480c5150f602c40700c10007507000c0d041c21180043d000507010701541c144100184100c1c503002e802d00c0c40380818001107524000b400c2e0021400120410305001d1001c400f1482030088100341490689807034a40420020035110b94500201419004501500640c0c000e02406202040400644001e40703841c0740c0f41c00c008182c00d041003487c0030349070780402c0d9005103801d40c20080d107101030021481c0505006010b1045217100204410415032f26070a4551140c844001e441c681f0300c1810003003601c0485250444420000040004007a845903007000b1514084030b440d141102c4020300002100c0c162030a12000512980c0640301c010304c58070070302d458034042580c42001151940000d641d040040c00d40e4100a0720000e90380980050400d0000c038203541080c0c4d51207600810b150411200600035500040141d80140d081680d0b00c620100d61040140b1061101e10b040710030901e072411406007400d00241c100007840b0356050402c030001c00010659001d41441700043d0030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 753025197 1250 753023947 753023969
    0x5100b160f020301150b0d0f050c0a140f04080109030f26060301090b04080d14040b0103063209010c0908070e040515150316030b0712021b07090608030405091609 71
    0x1807200003106d6960b1180385503c046601d0220b960b2203000c014814540074031170303a0710304da45001c0541c1c0d8101c0e040e0702c041d46102c548e00301c100091070704d0b802464014030041900707900100302d451080c1006041161120840d009202401058000e2250107800706001c0f00c0400c0715030403c58542401103801000c148000815400b015820703c030920118502501c619800c0d054140300343c0402d41c24941300c400e02950020050b421650052000400540215400401d80c20001c60481c6500421604031082c4941c008a480b201000380000347c50280a02c0c0900b001c541442d01e12649490070aa5640c0c8881c407602d1000600f4070085020484140300c042c0c003100c044100c480da00d0a150039024150310290b41c00510a2050860081c060514046502c00302c94210b111101642d40310f55040c3e5032840000c00448200e90b003004200f520414030203610502c001d80a00806515080040c520219030140d08000400e03170050208004071f07583c0482d6298020b81c0c0900d00108860000c405403805042c54000d88003100c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 753026447 1250 753025197 753025199
    0x507091d06100501050d051e0103062a0c060e0c04050903040e0f0f040b070e060f090a0b0c06070f05040b031503060618130201180905100b160f02030115 67
    0x40d100000c103210305540d058410a03211644080031818051280d1404100c09203d01c4402c03913841e074003d9070320041c1415100e0b100381e1000706c000c525500036003040b00c1895980c45e0207a409200140030a8074440041d2241101542c2d256020f8401040030100038405a21510384546002d0180041280117001030001d02c00c508000210b41c0d01c940050007a44640850100040c4179405008503c07400740e1001488179502d511980c4840084080c000e013410306014003114810700ca030303c44c035004001d1501105040d6440b0380000040022a24080c4d00039420340c4003e0088074942034001c56126040100c07414401c001c445030030019240c5004651040f0300b8040d0120401c0380300f040b1080401d01d15070040b426218580e03901c80c1003001c40a41e1040e240d410b0500304000865030250085200103160050618905501c142401e1044543c0039801036417446490300301b844004150f090020000e03040b4100303038030f0515694958101c5c2060446a01800c07070b400300e24800c0c040d51402e40c4580c03d0022540c428004007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 753027697 1250 753026447 753026471
    0x6090b07150c0c12050a0914010c050d110708120301260f0309040c03090f0303180227101d0403090810151a0d020d06080615130225050709 61
    0x4030280c040144c1d025030503215456007061141d4111195419551a203000c1a41400154130300705440c448214180000c040c21400440c03000c0152190601c0f0719516441c580180c003007280d0805136a640480042e90001c00c4050900510b0b030140c80c10349015400c4203508203c0440d000101883c070fa4008240c50280039510042c0d90404002030000710b60581c4d09000c0300f0300c03112044045030020017000d01154090780b40f0200003842504251100c0e004005d5907142410107800141d04c00079105403034100001c2c07040e440b203903c40070411030903440441c1d03403040b07402c0e42d203050b1401521138030741d094011030040c0385000141054040c510201c040d02280c01250301000303403070b40c0303880003801901c031850342c200700100b40014000070025440488401450045007040b0f107200b20305001e500050003000000e5203d10002c00d03031106c2044141d21910091074a81c0b41c1200d840c00703209501032500466203540340104580442440300e24ac030300c604000084a100000c0030702c0d00b03290b420b00d5900d4001034071090401c0e00000c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 753028947 1250 753027697 753027707
    0x11103090d1403090c103c0203090a030f08120f0a290915060a080708060a21050a05121b06040f02090c0c070e0a1506090b07150c 57
    0x108079041e11501070303046026640070780900040300c0803d081c0d84503040040c12400c0010203041e840320705082c500c1d910380170a0900c0c01c0080003507160300c1804d0032002c1140242d54040c0c3c01c00c43c0c03400c15030002d18600203c01c0f0205202605500005c1c04501042014a040003001d10480f09a518100321078511400d01146901081800307486c0380c83da0a0900001d003085600e00035405400c0003c812007034280c0c0c0d42c000c0600039491001020703800000c4803503241000301d0f00d80c8402003078401540d5461115a2500301c001802283c000b621990080414100c103102c3c840320f000e481c01d2103001030000b60300e40c0030042c9040fa1034400220390061017401550302c1d001d00070724030201816800c1401c88a42407600089030350242d84032000c50707014008d60400b10f00c04016041040700281c10681403640703549440f02e1394050f6803600c00a40e11101c0000055020441e405c41c4a00c00c055408a160106499440c517140e0011720380b81c001e010342c1180d4240001d81d03070200180e004214a81000904003888904554a00500303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 753030197 1250 753028947 753028963
    0x6040e1e131202060f0115020c1005040f0b0903030904050408130311120120070503072f1c033b0415271820030706170901110309 57
    0x61100002210b40080d03034004190345108800d000c105c0786907a8645801d5240c048509055442940110740c0401b0182c1c40d00d00062584012680703699646034508501004010890707440310258100071700600c0401c1da400700c01c40700f105030111004070301a1190f040c00d07800c501c07480b8034118030340710986c2002003040b00032480180d64440c00c036068000c003880310b000700e402e031a59070402461380c24400c1e05d842070f0b110071a0301070034800d4081c0003282c0c14481c15550748a12003490307071190a03010b240d041d18140100c1c080305004004150940d88840900c2d084000c0c80040340e00280002e007880405111410240d0201c020341821076800c0e03c0b13030b880c19820940d04000b2011031460f5a409035040c8514480c003d4114030401c001c4800c1d050b4007105414140e41140903001030700c05110103c2d0345032526480107010810004d034020340590401400b548540605c041c14091030302a05019030003c14007049110340000b0700d101e1400301000700c1070150b907480c242c04d40107110300c00300a05109004404d00c0800440011a86 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 753031447 1250 753030197 753030203
    0x6120901051902180d081606020d0609090809040b060f1b0f0105060108070f140c061f230a08010501080f01051e0112050f0102030a020a0206010b030606040e1e13 71
    0x4400b241407041e80c0782a882000d0140100c0c40444041c03a54504155000002d014051202681030164540d40103078040003182d0180e0341c0a4001c2610301c91440d2038481e5000a1900030800c01544540ba41e41154a0140e50b10309480f6980c0c03582199102d45500303088460307204a08407034540e5010451100b00e4003401c021900f80039072145d0356510182c0c1c00d05214250080f04c05864400c6076903100e1104840720707034042c0a0340d010406030302024803081c0c4100019292104c840d0740500541e1416180c20002d40380c00b2070340c0c10303182c00340102e08102084581100c0c0800d582e1400383c034501201040082448101d43c0d900040303140d8600000020256000300e6100903010254000748440c1d281e90011020042085c503070404504410001040b000c0401000c400f011031081050703800c0c10b2030140f010b84c2280c004440700c2c0215500001c0244ca41a414085240500a266100c82c11414030201098039030203030380916800e40b2020700210b110107001c42104200d00d00c644003007a0080c82c01c1d500480010360450811 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 753032697 1250 753031447 753031471
    0x109080a0215180a0b09030f031003350a1403040b1f06020309040209040f090b181f0e030c0703030914030303130308100b070c0303090501081308090612090105 70
    0x110ba6000151020710410f483d41600030900c280003500c85d02c0107001e002d4080121071004102c1c1106011520740914405c210321020001c0080c954203000440780c41c0304c2090f04000350041600d00400c00b1860036084403400034007446440342201a0282c985900d408200300c003200e0040104820050741100042c450701c60b10030f011502507a25944118044200d000d142c003d40c00601954800f414243d0203002111002031012032900320083d0840119400c0a42c1650290000d804001882450710b214141804d4120000c1c503d121000901d00ea4841c0714500c0c005000342c0321001080c140a00f0000c2d10340c84100c3d1401d8640c071035070700e01d4040c0407000c00d40b00d04000b0390f28401c0001030130f06c0c0103c190b80c4550a0302e034004001d9001f03540d00300c800f060010528001c80461040204108020401801c0310a2007501da9098180c2981030160000c41264000ca04003d02c59040200f0300c03030040401c48121754007052071600d4100840000d000ca000740b00070781c008640a0400c11000c01c1703054018a00070300145d400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 753033947 1250 753032697 753032701
    0x1e221a060f100c080a17070903020411091c03050c070e04020102010b041415153c0703050c0106090f15050a060e090c22093801020109080a0215 63
    0x2d2154881c000001d20010554240005000c20030580040a0300c03491480d21390400c10342003400c134800798030130350b0000001000e011050045003014400c50034580e01340701c1d84909115855000411043c081c21405565403001a0010300b018081c3c01600c04c24040c9100342e030344164172841c4134040d601b001c50b400d03401503080944400103410076210740c141001103411011280e545041d51030031106044040d00c0c2d0044908120701e0382058494000e4030b0200700d1100c1c18048000b003600c292440828100f5183d24a11204001d122030a500d0000c45c4c803220740c5410000d88841a6130522801406554801c1a000742042d00354500c0811680c0710480c1c0181d40c20003050826160b0040c05010711843c069880810002c14141410349130070744126601800419415103031079100704070081690390036048204610602c081c103015043d403600a81d103a041000140f11915012401202d82c0482101040c40100b5074100100b226a4800c2d00701c0c404184d0000c8040b684c030301c1d95020080d614040345000c0d0600e2950000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 753035197 1250 753033947 753033949
    0x3030a081005090f0f07090e09030a110705100c0510061401120c09061803050d11071a09040506030f0d08100b030417090a120c06081e221a060f 63
    0x2c49140078403201e204201150360b511101c81e00c1700c4000703000c110602c10703136200c00110102c0e50401d8a21603401000a5521450f00200245c0320342d0b60400d226409800c00c040510168880508141150b002841d019242d100e032410300604140e154506103801e14242035022402c03282d103042c811034030300080e03a42c60708508007010460111079081003860300180d9090302c2008624030401c0829904034030328540400c941e03565a515450a01d0110080e40413540200514903400f00c02d020140007804d028016840c070040d4901c00210600c201070810f84a075039103002081c10b5032420440e2220181c1140c1c01c44a40100c0341101603d925011110200342d0240d08801040b20309031101a607000350f500040042007114005460707605038000742601504400b850700d00144440036002d42c4540305000341b084a61142c1003c00040030b041c4014031450308981030105400466171082506c80e03115012500020114074100300c00070390401501001342150448404290000c1903d021160048908581d40068180f0000c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 753036447 1250 753035197 753035209
    0x40e0907030218091e0f060a0c090509010e0c0d02070f0308060306010501030b0a030f21030f050a09020d0b060102010f09030e0a080715050a0e0d05060601170105060d1a03030a081005 80
    0x940385080b64000154004103a81c020045c2c5220340140e105403001c3d0222041c1552a040f800c49600c5903550711050207480c0550000e02c0384000e00003d80d2144041c0d81040c4c03031401034150142650030661400220307100f070400d4941c1900d06a45d88a90b0705a03408000d0304000300308036000ea0b1307190311038060032000050b55030107032044484446026203184030403891501d9904085440050030788040750016620f02d200c032400c0030000c0b941080c6032400200c10a244070f1400854400805400109180c401842c0241e0341d4084140d02c0280e100d5044449561120700403070141088420030360a00c1d0514103a80e04054102481415245d02550102d550300c1d03845012076540c08285c070444120301d0180e00307401441841a0000d04d0001154108040c90a5940300490003003c007282e42039a46030400f8060294640c0d00c40c5116240d801080e00100441d410100000c0e91481511090b01c0919030b1481d180840304c0d00c040045005100c0242941e880700c0340d040f40604065001c507280e07014101100030103c4c487c41c1c16 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 753037697 1250 753036447 753036451
    0x3050a081015030b1305100e0a09021536040f14070905040b04140f130503070308010305060708092509020c06012603070303110c0106090f0c1d0f0105040e0907030218 73
    0x450342d1f80300010b21b40600c0c1303c00500d02401001c13015864420520240e10f41c01c08441000400059440c3c0d600c003130113410180340d148400885801c3c3d000310203080e91914543e1083c2c3d0010310072900041c042e075421820344010450560a499130f17241010801c02225005113120781110002e03541030109144c410308000c11500080c1c8071000da1000180860500d1384030210740d41d40076207044a101d00382d42c844c0d12414510f400c200320460000741d40e140113204010080c441240c0000090030710b50340502305004070b56201d5072914030407103d010748080b1402c00259514000c2e4000d00520200b19641c407564400301ea1101c50900500d41d0140c0700043c031400e52401d01c80202c1940d031441c0081c504200301c0b942e0440150203076070400b4454504c24058003000310820712801c4010301a03c0303030000d0350b5485c80c5404003c3c0c0311500c0c1c0380d0341844084120f200c00c583c00c2c961040e1004c1e4080b9200c51841074038a006039100d0088c5c8d040000d070b012841c000c008a000c0006107540a4034000c0b83d02e032051001c040f20048d015601 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 753038947 1250 753037697 753037711
    0x708071119060b13020708090103060501111c020709090503070303110304030806130b120f0d0f170a24060801050a05101211120105090a02040303050a081015030b1305 73
    0x101c114804041102640000b16554004180c440b00c1d651204044c1e00340d8001da0303000e5070042400542444150b0b010b2140c8001800c007801d1901c3c9180f01c080c200340d1244000300e40c0c0b000c4180202d140740e046a10920120006e40201c1004000108207400c0056507030f040711804801092800c0029001e94122702c0607284101c0c0e265030b56600550301ca80500107040b84980c0d018410603154810340c2c84a0356a41040d1210038840d0000708442c2c0c2011041c0c0349080c2541e410705003842843e0560f482c005510150f03504100514240344007980d2105620b04000300040313540400020303030a40d0891000080c11f0640022034186030b0303131070510f6600d4400300081c00029100301c41d4409090b2a494141d24095050102c2844c80104009003800c0030300c1c00c040c440d501c0007422416007880e0704010702c15860101c1d842c0c0d0700040d41d0582182024199034020f0310500c00e072003407031f014822880000b425a0600c60340c01805005050103892202c03414043c041c015100281a0b9449010b226400e803104910300d214203446418 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 753040197 1250 753038947 753038983
    0x12080606040315060905070c0b0a18020405090c030706020d02010b032e0603080310030201030f0e0a0f140a0303050712110a0507021f050306120a0c0b2107080711 71
    0x45560b40310a000c0c03ca4a48010701c00e9241d02000400051a2252070321400103a110209450140e207820040e00034001c0180e64403d20780840404a040784c400407001695042e140019552249541c1d18070b0304820f0314881350f051041604c0444c2e4542c0c0418140d14640194000340440082c0f81c0070162580020601540d1000c41c0f603a86071500c1001804106440142c2c03034002070b800d5241d4803803c61581c021150641e1105a0380010011540e1602c500100039605000c00c12200c1c1c0001003281d241c2810500217001180c0601c6540144800002c0780601850410100c1c1e269180601d0f024000d004200d42020101d80b035541c0348948402d840c000c0d0124000068140c03131800b03a03080c0094074107410021099800c8007904550400a07a55000c1181d545041a15075075204e25052003040322031403c2500007107558000390000c00004e021015041d0036241501495502c4224903021540031105d10804900c051014805101425420480711030181061b90703541d4050080428010790703103084205a16000078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 753041447 1250 753040197 753040199
    0x7060905010c020d061803090510051806130905190b01110a0b18031b1204030b0610030902040518071d0c030603010209030703050105060a0504110a0e030c1005071208060604 76
    0x8a04a0020420300e1720030600060000820440720803001d0b09400c003100410f246407001d201503c0e001e031440110300c107a4a001d501d8601d60048221413031060142090241c140421811a00d170114254079024220ba45030401407460035422110003a240d010364400882d00e0120800c040d13511568424603111105001030139000296074841c00d207410002c20742049001d402c4c0d054404044140700910040f0000801080d540c290f00880f14180344450013a41c80c4d080341040204001211101d81940c48001243c91055803441140c0a9028084400d4004c1d4824a01000c21046030b00d07481d40b5015200e0030700102d5480036102c41510101c0c00b001c01c43c8020840315140022a6840040d0003194480c00140000d800c02540d680400c2ca0510150021541c41e5110360401643c2d040032281103000704070440d0180315a480c01001c00c4400e200f010000c00401160140781c0020361001c00c0208020303000138101c07884841d0107a000400783d81000700115031040d4062500000d8500c80c40c200d60107201c009000034540b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 753042697 1250 753041447 753041449
    0xa0b040806070c033e0601030f060906092907260408040510270302180a14011202091501142101060305160c050705010c0809030f010e07060905010c02 66
    0x40400003204408200c54003a20303c2580704a19170802c014030180c10401c50b100e07006400600c107100c116020f202c584d4040e00041020584481101c2c3d5101d8228070006445002402c1c6100a0120200050000c030b151002d080c00c1c4107488052602e1001c4515070115981d140d085c030441d1070000d10304040007002d230607290121501c00e49250a582040c440c17a80240340c02d5480c00403440b80c8803d40c141e50040741018445501c43d0a05401c040300750942064275114540c02c1d580002c5c0070b8440c03900d404106403031810009440d2040d50b4001883c070b4240403072001c0d40d50ba44a00d620000212048100e0003059128080b4038200044a8400748600d0161589541d4440011140501d0b40018140c1044550020b01d1012440c010714080307400ba000c0c80d90046206d207000e035134101140c4081511081005800300615012940c0400c80d007080c0c403400d1920010035101410140401e0042c440c5090340740c0640b078081d62455005500c100d864030240030076540116a149070a40d82d8154903c0b5180c0812051110700e001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 753043947 1250 753042697 753042707
    0xb0102070308180307080f0717030301031a130f140d0305040b01030b042316080303090d030b010509131401120309060f1e08060102011d0a02040c14030a0504020a0b04080607 76
    0x14460004e001c417680540d40d502041d140584030f8080e407802d07402c840410304c03a4075003099010007041444c400a528651455451103640d03250100607640c500768107030119140d0f8000c02d16120480b908131280a40401341400c021440041c2d8085550345e5100d41408211240e009000e141c2c0300300d0700510003040fa0703865074a8041e4405c000900446c0c4003281c0c0c10300d444031911020010807500d640c0703c008004545090030174044c81c00a40c0c005048035401032042100c41080080e60311036110307ca1030086520000180162258050003103070320740c456044008054038495070750ac80c07048029a01ca041d845641e0381c0b8004407840e0400640500000d4100b54240191400365000c600c0d0400b00d4a0103004402414004680102c101e510100000ea040c4040c04650340e4240104002e100c0c00209880241c044403200c559942d07002c0d80c0090203642c850040b107549034000c031501c2c0f40c00f00c0e060503c03035543c0c68510104c200130001281c1c200c3c071810000d100466540b1041d4190b0b425a40c400b00100540d84503501c090303403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 753045197 1250 753043947 753043987
    0x305070210150b090a05060c01050103060b011d010e01020304170c0310090519170412031e020c0f0414010e010602010606050405130f060801180218040809150d0203010f090b0102070308 81
    0x4d00170004039000105030300c44d04010520540b200f40002507a5043d07150900a660300b82000c00d040000210021a400c0c0e8a0722491078449400d08145580d0071850006034194091507014100d01344810902c4062104080b0b86100300c03040440603141d8001300510071a0440c1e240340d4000d02540e005049410f4840c2d800070183c071000c0e00407590010402c81c1e40e036400d4816409500000400c01c07402018400700754202c0c44219070b40021006005c229402000001e40e01ca1070380810790310404440ca0800b10036104e55100015a80030036803090182c0d0703101c0042e031001500078450400150700e0498000b620300c0c401d000351016504010403004c521054800301c84003a02c901e242440046903201c0e40042c100a00748038455100303d401060b0815003201d4010405096040360050f00903009207010030002481000c101d82c04078100b116010303000041000361043d41d0068984890302e403403000001050007a0400740540c1104c8504506020001c02000120788800302c9200c01454000309202140c0000140c10000c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 753046447 1250 753045197 753045199
    0x10303050f0a0e04060f0501020c0f09220b160212030114010804140d021e030c0705091e010308030402130b0d06180c0f14150331030305070210150b09 66
    0x70402844803000102290617540c48280000d60000041055503010700080700c000070100d803040740d0800c1240104020100003060b117541c030000300000c1d404000000020791403103030f003013980c050b000d2919040c803405041009010700007620451440341400b206880c21281a40c0d86205060b6803181e008006441d004405401120790441c1100c128000d29000c2000c0044100258010510b02072508100c40c0303c089001403000242c5c00c2000b0002c50f0541c00038103501159001d4901c0c4540390707038408007010400c080d40000c100c00f4800c03200010034400c4402c06980101d008854210345003406441d080d080b5404103010b40d40000c00e450b9250003140c65070b4025104801800445040740305c440d904c04004c026181c01c2452103001540702481a01d554840c44200050b0949025803204110741c501111030200a180054603507850303401c3e001c0d54192001140c40010859403001d0a10500d19000c3d01420b130844405c0d0042c07150101d0320401000b1030141ca59134000d4038074450303207007800e04d009115540c0c0100146 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 753047697 1250 753046447 753046457
    0xb0a0504091209050d05060114060c0d080a1109010c151d010501090f090503040b0f040312020309010210050c0406180b19080603160b2d0702041103010303050f0a 71
    0x2a1903180c50140c0305010744602d00c221102094844042c11468881c3c2026015400c1c1e168288000345001a074681510300d0880901d0407034400b0800034501e403107a03003d00100782c01544221400c140d04580003d00414220006000d0307091101461b400b035000c0c0d0030600d4000f44141d400748020620502e4000701d05002c03420701059031503444d803e42e2030044440a801e90756039994001000b5038403036407007401c14561000d5001d0052202545503650750303002d940161440b44034006114aa00300328482114004c40c4d10406004c0c03008040c500194030386d0055000140580203035035042a42100a2003031138030521154468509003400c102c030494030810100c4060b106051003038800f0403200440c502804401c041c40486031038520503084020145000641010b019510032980c150f03524919180d820281c40f0030840c1e054480c8981c0c0f2000e400150841d4010304800305003e450320f043c03c004401400c00e640291018841700320890301b0000e040c4401d11000d40064030134009426100c0215000f002c034a2020b140c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 753048947 1250 753047697 753047699
    0x803090a080a0e12071a0a0302041503051f080327120304050102100507020304170a02090705190c02090c0702010c0506070906091217130b04031406091b040b0a 70
    0x41c0406030b0720291815000c11200521412a4500a042003100f1030540380588000da250028040760018450041900e80101040348500c00303220764180c40061202181010f8446030000d006001050b042e5011f02c54000210845039001d076121010508503007480c401036150011014a1888040c40c0d0750a040c03440340c80380c0c08000c5a6842e0f00c40002120070490185503a1441c050004e0303e00312689124103196030400d01000841134010060f502203461190840c1c008080c80f4414500b4a150360301c00a502030100004d1201890b0321801400020b0b100708000c43d0a509610b0f0142c4142080e5440254098816000120850500405002260700c103040c4001081c3d102d0703071490300340b6a04854003070000e9a501e8041140941c4044000020400a010044054281d881e46055036070000248104040001105125010807101c804010505000d60681b03035916413500c605550502550002c081c40741d0008a1102d0b030012030314001c0c42d040441207542500103c0c0a0001421551950075403084135414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 753050197 1250 753048947 753048953
    0x108040b0c0909011401080f093016020a0807050d02061e03040609020316032307051e030d02010c0c0f02030a060e0a0303050c0f040308090307050a060c0b0c070c030803090a 76
    0x15099000c0d004148170310790b001d041c5d0703c00184050350007010074005041413024498200c201242c0e8060f080c400303502c0d080603c6a000311552000142608800b003603000002c290242c0c0d140201c0ca400ca85200311421340388182d89018450303850360240a9580d00503034419401c00107141c010000d003001c20f540d071034044c0360605a07906000300d034204a60942d1840e07182c6407004114901482607002e03c0d460403c405106500359150340c07102410039861490700d1214151003d0b0181000c0000c1401420014181c5a0844080c03c6102c21245c200504500a20812501e10111401800340450300f084507543c00c2411460381d19000b80e803100001050340c05004d01d12841c400b2610b18091404400e100e1001450b00107050320340282111001403114000d18428004402c10310121000c0328100c0381c200506a0b1903101ca1800a81090081e07400250300240085000035015007181410b84d006001351104400c0d0355560b090642e245c8142074000300150604d2030117100080544000e50b8014280800f1200076200079a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 753051447 1250 753050197 753050209
    0x4051203090303180102520c0e060d120c0611190c0302100f0b190f06050c0d08090a020406080f07140d03031805061515090108040b0c09 60
    0x5541c8400340e80000041000340d503a07400805106051000003146060304503000051014500c6041e110352500744060325403e8054106408035101004604411010130b003400e402540d070700b85c60122041e4150000c0010009a0340c4d81103441288050410071041e0100c0c1d9582060001c400b0100c01400110424440420558801d5029181c19000e9499075a045000d07503001038001a014581004008404c08000980c007103a9a09540204100030076101140080c50000d05001e111464000c070300000d8803140c410380002c00701d044900c401101d401d0251581803c44051160607516000c56001d90b800100c09441240155031050004096400e1000a640080c0a49030b10b41d001800f65400048034040d1b8400078000c130002406c0e442c101203900c08840c400702d54450413a80b00075003410303591000c095000d01160304800004d03034480259491443c100c0e074030300d40711620700c10030340d000722100c1d060aa42550044111103403984161601c0726190345a98070342c60f1801c401030103202100c00500151040303072500 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 753052697 1250 753051447 753051451
    0x2040603020d0e030c0c040506060706091209290319050a0e011b080a0c020102071202071a0c032704020c010203062b080d02120a1a01020f1504051203 66
    0x90358003681d6600303404928000e4a2855202c243d40d500200901c61681c107000400c0e00c500b00d03040d24003052556442000945a004800c0d0142905007800c800e60200030340c4005e9520099280e40302c03000c40c5919500d8260140742300c3e401c05180300c940d0b0070121041441c2000a148e101c0da0b11006203030080980b12210301556401d40f141403000d61034000c5240b0040c001e003e000c501c490704202002d406690381000400c0460081c0240d030300d0035a18580f0b503c03860320030340444a00b2500700d076021221410410b0029500c0026210703002207100d034207500c20840c220b541c003150304214180d4015402c00c030400041814004d4803220030000c0d50011001302065442d01e0024110540c1400700043e140c2c81e09200b4032044007519807410025030b20454045004001030900e034074500e500701d40340740d0301c611069100000070300c2000c0300400d0244440041005409041d0070071000301035940f031520b82440040e4010390f078486c800c4554905039000f28428841400480705140c0e070080c040c4003110303c401c801005801e4103a0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 753053947 1250 753052697 753052709
    0x90506031c08240312070c030f0803010810180204020c0c13090b0f06150a0c060204090e0c03120307110703060c03060f0b07080421022d0a0e04020108060d060204 71
    0xc1c0810025181c441c2440c128040341c0001c100303c000307440d0000007030700c4d0300780f90302024000840840c40209000ca211281c801440e804103410700001601c2c00d2440f5603420034480c4813502c0c800d60502d40400c000c82d010b25400da03113402c0700c28503400a4990820020b0740254511040ca4030070703140007038006d5854000c0c0440000d22004002040d84190528a0700f80300c005012100305544a000d100e090f4883e00041c0c412441084042c6403100142c1d041100d91242034200504214004140130a000340c807540150303068840c410071200e0500d024402d060300c03944590904150310308184009003401d806030030303200c200c022000180d0b00364640703e9640701c0403254080300000c0000c1c1d91300400d021701910700500394080c240210311395041c610550750382d02041c482c50284440319030300200e454041042c03940c079041e40203a000348038010705d1484803400d00d400d50541c0301700c9082d5440c072183c400041c18420382140c03d564940000307102e40d50392030f001501d050002500c919001082c40841c80041240c62003d8409491 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 753055197 1250 753053947 753053957
    0xb1b060a0203060a0806060a0e0403090801020c03040906120b18030729071106010603112503122702030307020315090c0414060d110307061205010905090601090506031c 74
    0x1054010720013550901d41008061754003400600000d0b5581d09241c4080700c1c028596003540b0b545510381140c0f1100c0355803003060250b0011549554038080030001d041968904681088469510115030340d0034120312901800c090741380c2d000702d03c400d0928102c0300c6492140c5c40840385065207540e181a401000303246964084400b5050710780110326640c1c3c0c401c0d0060301500e0001e840281c1c03004c0140d11640c062007070f0424581d9074004407907458103240c2a00d00508001c00300e40c4410508000081c0c0440d00c1481c2140011181d0b082e100c402c200c1882001c01c00100042140122903007a8031460030203050b40d100380d915210500082d4016503081201b91b0702000748091521441c2802c241c03040c901031441411911031400d051240000000702c05a0b581c3c0001d0869640080c04154100444402d0122065a03054001e88801081d00358000016841c1501502d10400c1581c2c2c0c2c42803140c040354010f561a20498201200401031120706800007904494000d041d107142403071180705600001500802040892 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 753056447 1250 753055197 753055201
    0x160f05091c05010e010c0f03021e0a0c030909060803040501110304032901061713110402040902131401021f0b0406030606052106180a060e1f060608010b1b060a0203 72
    0x700d4207000b141d40101ca04d5009000302ca400000c003030040040c03508101e04050380400c0d0452071100c00d29a81443e9010013008582e103030094000280040348001064010514034800001c20021354800d900440c3d0284020f9030500e42010011106805440b280100754070061002001240b250450501ea0707001030310490a85029040074a01c10003c143d0007102400411044020504102c08169030303c003800e1140344440d4051380c03910200e019020b2401c03640007407022401203a08020b60340141003004280303510300000c60f80c5070505403208042c07940903401030f040303001c580612115680719004141500340c0f0109400e020303c1e001c5070880c0c60980c810f40c1d0b2240c4a6000b0409824030b40541041e40804c001503291110107442c403076940c2c1402401d8544007810780101208540020310080340d20381da00c50310038041100c0f00c0380c00c15611580417200b881201590407104c013111210388115412a4019103800f03540340e20b4104003805540203002c0322110144020501d480c092400d000350741c801d5502080041e00e034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 753057553 1106 753056447 753056453
    0x506060f07141606030b09090d030b012a02090c07170c030c010504200d050d0f0c06020a091a070c0509040602043308160f05091c 57
    0x64082e201c114841c43c3c05224070300003102c044c1e03030302404003900610410038001c43c15146620180d00900f850100b140c000d1b00102d000d4401410071000d41449422213881c2c01030211920f002005011044404510744080880e0300b003c8084000c0e4141a01c50f620310812030f0b441801454810720100b8802801c510400c110b980c0d62901000034401070a040c60100c080d4105420344409000e006c1c910502c03641000c000d11031403550400000c0001c8000900141c600012419420040004010341400402d41a00081c00d803001d0950714074102506e091000b5070003046101103c0c00001d410032000011a1081c0c131079100781c80b03080700d421185817205c1c03510400a208680c040b141d150300000030314500110040217500030b00e541c50524210304441c51710469601c0001c1b180c01030340030514801c100e00d2500c54020500b4500c1142402071034608074000080c030250044040000040340200000b0030 = true := by decide +kernel

theorem cover : BRFrame.Cov 752877697 753057553 := by
  have h0 := BRFrame.cov_init 752877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 752877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 752877697 ≤ n) (h2 : n < 753057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
