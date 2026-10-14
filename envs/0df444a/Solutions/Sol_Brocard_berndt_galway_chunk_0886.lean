-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0886
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:27:43.78903+00:00
-- url     : https://prove2.me/submissions/56ad5147-64e3-445c-a4b6-c855ff98b5c8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 159172661 ≤ n < 159352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 159173911 1250 159172661 159172687
    0x711010c030605130507020312040602071e05010b010206070e09101a07050f0106032a08030c151302031216170301380f2101081515040902010c0b0c 65
    0x140c0400c0d0000400c1045107001b100081d202d001e8121b840c80030084100220781800400d80541e00d40a4120140712082c0c240d07a5101980d02d91100c004a4603075003800c2e0440c90070360002c603803140f06489517180c0800c1e01d00b204040090100004124811569042070081010441050b1080c0100a078084d05e55071741d4482d0601c2860001010341068950b0b06001c1c007800010030035550144202c4007418200789003000340c20f0343c0007242d0302600000601e110104500c80d183c10005240d610300c1c1d00d49980d445080d1100701e1105050364058201940541c016002070804680070b03c01480075203e554a4000341c0500340d52441d030140030000201c0d034000000310042c04000ca0b40c1540910881d44031031092010007002d101c00c00d41000b950307202050884086249000e0014503811118014024001030703042d00f1004081e21155a000e004148007403044000880d143e9a03aa038109001e500088000495401c1c0c2c44100000b901000808078104641030307015070b0000c8c490003112030088074014034864444054400407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 159175161 1250 159173911 159173929
    0x30105010e0d061a120d02032704051f08010204050612071e020304060f020105041104020d020904090503040609080604080d0b06070602120f0a15090f091502030106020d0e030c01080711010c030605 86
    0x2905051b0400c0c80d158034407940020880b81c0420810071b1210800d00c7c688500407e000403410003940050a100c1004400b61080343d0003401d09204801d0b022095468842d03540c00c0b40200d0040301e41101c3e007000700c6543c091018542c550300c94841e1402d04484104544038980e00094185103e01590000c10140b1031550400384071440c034412840200454a01500c43c811307110705000e1203500865001a0041c5200c60a4040700c00d0b540014000340400041340c0340880e5a54014031951703000515210380401d46610204070140640d41001403103081144c801d500900038400f0800d0503600540c100b012400042d2540041c0040030601c03d100c264130301c0c01c2c9119244125000b0800180d2924127100420201000c80c2c281c810380310540f0002820f420020000750040202e0710001d0003da000d007210426008990f001103069030090780c241d1700c00141d411000c1e1001c0b802d2111980d80354001161008a5501c43c0c070b65680e0100183c54035907032100f40f0300001400c43e00c800301000006030312040700380000e003010900703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 159176411 1250 159175161 159175189
    0xd080609070807020604020d05030c2a04061a0c0a120c02040b01020f0d0302131e0f1224140109060305120705030f030703020c1f0e12030105010e0d061a 67
    0xb00d04802d10703120074001d4881e070005000030300c5651094044424000700300160360080c4010001c59560a2115403005404100340c01010711103003031039952030b10504144c01070380304030744541c01c0d104100c08070145240c44582000c43d40683e148200402403011842070600c40c0301107601e03521040790f1000c40d4010b20060340c100c03889244c1135602c00040112403d00029071250b2034901d0b440c005850b2084042c00442005066110054050b1103001c50001034440e0700300300045030a1000a9a1030b2642d5011038411020304003005048901c3c001d03030078014620949028010340411036000900c40e14210341d190f96158003a001400410354601040c81004000c04c1640586403044200608190f143e0b83c9140d980d10640300c03d5012002c3c0840032804603800ba030159018928032905588144400070b20507000d00081000b1654020304004170140c00030408103000c0e1400c001c98001c82e21710b1f801e1200550303034080c4403c0b10f1900102c6c00c14030b40c40483c900c1e2280040b041e100820100010b10108100700d01445640d031 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 159177661 1250 159176411 159176417
    0x90d0512030c0712111e0c0d081b060601090306180f1110050306030c010309140a0b070e0d030e04020a05040512010614032b030f1404170711040f0204080d08060907 72
    0x7102c900d0151001079001d004540c0c2d0000e595084006e00305403820000d8414500b50404180451101005103440207408003940d4140c9030580c132004003521b80e594a80c2654118040343c0780103810300100300603801c03458400f80282200c41d8102040e98841045040c00ca80c143d4084050301080d490320300d420030f080000c1003005d24042e411420580300003512071200001441c10b1580e51896001080102e4500c800055a190242c1d0071090040c00d0100d0380080c05c40e07800c000100e0400c4110039600d03203a101d05480c40e4243e0380e01c0c0c6856030200c092000a60102c40c4e02000d10030700f880002440d5803200104500381d606040080b503054582040c0340c55200e070b10300c0894820b03044400200c00c00d84610f070164031301c1080c54240100242101c101a0020200070406c1d00000781011130400c8110400c45805008a1023640340b1030341248030350185903850044c00001007004040f8201088245496003001c07412580d001001860159900415850460000c2d205d002003078031282046060300d0b01d1800254402c246003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 159178911 1250 159177661 159177677
    0xc0a09020f180409080a020105070801050d0b04060b04020c0304090b1005030105032e0c0c0b070503011428031a01050904080901120e0d110708070b090d0512030c0712 73
    0x40106905005030020041481d1245204882c5951960403002205030010034940d45d5551071035000b8041d1504440100110b080040002500c0c1000c00010791501d4210545003019201c0d42c0d030f000301070100110300300c0d8415024085c030b0b040300c03009100410003030000030300000e04840c250052000c0c0b00c543e5041d040c1071050078401040701ea24042258185020407a41103000e0400b800c5689141c0074400107280e0602d40b90042800100f900001404e2080b8011411203800d0398407a5800c40700d6100034045d040b000300b506104032140c2e040c07202120a10341c02000310808101c181091030140c900c1c00390300942e2071801010400b400c4101002c1c6d194003601c01071b0390580507850207481d03d502c18880e50100904019044d405044900d400b64488181900b100058414150b0f004000403c548020722040d0554003640000040c0c990b0005004022240a403110600b0203031098101306000009a405450b94000e03052101112034034800110710070391124075050788034225030a084018a9410a0070000d210002d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 159180161 1250 159178911 159178927
    0x9010c0b04030203130f05120a05100921020114090102040509130602090d03080114030a02031b01050714060117010b03060408030903070209010e0a05060a030803190b030607020c0a0902 81
    0x10615449500309100004948803441d080385148502840402e042c400d0b100c0100c0d143c070724002c400003100d0003200d0b00741d451a10440110740b92009550001c1844c0d0040044440c0e420b40b40c0c01000e203890040490300840703088803001c52440c040c1000e14070b00503507503000700104415072254450b8210400b40000c50419044c00041344020002815491442404541040c10003050f0f030119880410043c0520a02420911b40a41140000c1c02114002d41d9942e170b01440764100010403050f41900180280398400b00000103101483c0f012401c00e0420804014460200d042103550007540403400d0700401c025850481c203d01c00404180d241e0082c0e034148801c0c0308c115a000120300340c000f030300a018160380e904da0007902c521718425104000d40003504800000344058827404c100d403040c3c40302c0d48140842e54441d420004400018000240720b041c0901c0810200c100410107a0700342030705580001101520340c00040e01d410b50072250300c4010790222410140c6810410f4455004003007141d4254140555 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 159181411 1250 159180161 159180167
    0x180d08070203070b061516171c02090d080301031a07111e07230a08030f040303081302041a040f050c07060209031c111204030f060c0201200a090801020901 68
    0x1490700c0c0544060100d00c0170039090342e0b5250b00310002e00c400c2c02c1915920480c071a48150300585500303041c4e401202c44080381201e41042d42c1100c00e000701e40a49684469062240d10000390881007013030b600110041860000070b030600b8001d60103940240c1c000d6211800001814094210040001c000c0050740f0108142c009000a89218641044445a641c14000200341803404104d90703c140e03c20120041e064041c0d00100014032000c2105a4030407210340c2d103030304a1035524403902c0b884170000c442c20041000440d10070f4081075001300041e510310000d1442c41d00060140c4840b03100c442c082d0030750071000301410b107131500c81c0e094070038005003060017145420252800103004501e400760029030000b94010181e54103029001c907082100081a0b50310f00000001401d0039443c4c1c000d901d6600c98541142a103d032840b0035942182d0740508403501507812603803842c002d098003240b5001590348070300400520744203030304039801d10340d000b50110780c0c9030b180c6068000c1c660071a55110764240d0744108460861039078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 159182661 1250 159181411 159181417
    0x60f0a031d0601060512091507120b040507080601030b0301090c0510051306050408071205030d1a030607080604060f0b0901031104210606081614010c0506180d08070203 74
    0x180e060000c0d5105400410700411101002aa4141d0140c0380000c121036800c24007030300038005500034040165407100c4e0180e81e030345003880d9040e4908c0790b10000511550310410304c884079036100d00000306102d140e403408035050303c000f07030392560114103040200801564180303d21010750304110000d0010020b00d49034080700a08a00400307006226a111105d4114066401c80380790031000d40c580c055855403007200500c6070300b240c00b81001a000703003a000900c1c0c076408000d440c42d00e03130400051031510443c820342c84014001041c014107140000d0807401c40302e47e000c4c0200b501c142e00380d486600282c503200040000b243c0940d0041c841c060030719002444800081320603102c08131020b00b00022600c582c0401c030441e030f004590061480e8080e81c0344629014075621089290248101406d000c0fa544400c88a620b614540b68501d0314041c0b005e0040005007492441040d03001d03018102040605180d4a880741061802c541c004000100b5000c1c8022004e02000000301c44200c038a0554001d04042c0c4000352244 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 159183911 1250 159182661 159182677
    0x51e0f04060e0a08030108060403110304150e0a0506070c051201090b13080412050a060c090501081302041e0506030d11030a030e01150801050f06010801050607080c15090a0c05060f 79
    0x9030703109002c0c68411810007481c5907481d005a98192213682d900c8038141d80716000c450440014090714044c118160001040e079065440030700710801c4031a480d01045540b000c0c00c0709070a92044010300005416100d031001450f005016094101c4040d05001c02e000141d007440385900d0641c0e1400030903101152214012640101d1500d12000001e59142003c403150f0007240c11041d860084c040c2c1200812200050000d411403142d0020f000ca40303080310060b1203c1c0401c0c89014003043c500300000d824805400a46901140300510020303812013141d16110341d00000f642c1e544403503640c076405c0c00b4052408000c0044c00072a81d282c4240300c2d0704001e2289441c1c0c00340349001c0b414180ca4a00100d071120003074100701591043c01c6850348410b507550724514080c00058415850780d402c80e0000c109039520a084490580301d0141416240843c40c0e52031195075841004030180d1802640d40c4440c00b4201504601d01440013400140800a001d06141600b8010390b03100510801040044034900c0c822642501c42403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 159185161 1250 159183911 159183923
    0x6100504091d010203070801150c12120e0f01020408070509061005070f0206030c07031806091703040b1303150902010e100c060f0c030617070314030408030d051e0f04 73
    0x281c140c448450301048140c1d00081c0d041c0d40044200592647d003c0030040c1220324801000c40480d06114003611161801c00015000000a1003d0002e450098500340c034442451305000031103240b0316141c00d040080e14072765500c0300c1c2d400044c20041a46c0400c4008050241240c1a100a0810b41d00040ea03010340c43e02d222003440404200750040c008000c6c082240360390007800080d0717646080310302d0500540c0501c4040340481c580104c66001ca602001c2d50a09440f800d0325580c1c9018101401c00b02c00c1c0040b003030014901e00c0200f00208581440002501c3e21070381412000b0740040c01d43c035041c2013400d02140050201c600c1d0020100c090307a44000c01c004804010b40e0500c16001b601c02c42140c45000c00e400141680d8200b00c1d1148442000d03511515003802c0326903041141d6a00d9110101001c0705081c1c030f0040300d520013036007030001c5035540301001600107110b011a45455961507400b070a513002a5075001c0e03200e075a03c08002102c41c08940701c01c000c50715100e0210041c50031540d20500507101034409015 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 159186411 1250 159185161 159185171
    0x140112030c06060603091e020102060109020310120c080d021501050f04061511010606020c130510030209040807031806021e031b031305031c11031605150610050409 72
    0x14580511001d1041c150048014000181c0b60000038000d06001c10b0b0031215000084108007031607900460304a034280c0d059024000d56407074082c07018040d400203480c1500e05030f40300c0c00009004c00c040540e103601a208401a007102450702d61050300307046801d04010b003035400a810030704504034040180c0e41550400c64007848004144c0c00481c005003c5600620820b04401c02c4809519400000f8048855002002404003c0d03d0740c004903103d00c02c002c109904204481f0b00c591031030803150001c90344404821803c22001da0380c2e0f00080c8407003405170b60a68000f80f000640e6014150b212103809812450a204c007000340786070500c029969000c1500004084181c010032400010b81441180c0021400008040c0c420380c0d49401684c07264410101000e103d1803101d800903490401117281c1000450400c284041d4942262090707506200f115a914802d000030400201a0705405030005075090050303005090a02d0181010100703920080e01036803240860041c00e40256601c481114281e80451a001c21 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 159187661 1250 159186411 159186413
    0x51f031203020409050c180105090102120d0902060a0c03030f0504022d030709060806090a03051b07120809030c01170106030e0a0f050604030206150f09180a110310140112 75
    0x2000f40215001041c203e4200700900c03000340c0441c3c2c050b00d01444a060b44410b44417450300152841d12031101218050f0b003100f003150064241001c00392201c03030a48403012a910f003903130380011829070120400202081000102900381640b44c85103030400c0c410080200030340d01742307038000800c1d9105088040c0299862101c55804210107646514440d0201a04480e00c807526a54a00702610700c50045141c50f02c54040050001180011840050307501a10b80b03c1c600000080d05041c031021480117920144108100050031b45119003003112800e0003205074a8070f441c04281014207000c07458404504001001260704510304100080c94111403003402c00107482d60000c00c0c5541017054965000c1d1124440e136070443c0c1803050229140d44101c1c400c0c0d0aa9120b5964800c040100b561203a03c000e812000181c04941c1500b494110702c0d8000c4c91070f100706842100072910482c81e10080c040121680031035065a01203a00f81003025460740030f1401004c0c040d05141d0400000c8902052082000303503444000210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 159188911 1250 159187661 159187667
    0xc020d030e0307180c020705060304062d020409050601030203090c0f0a1e08160f05040504061107060605090105101209021207030309080d050a080a0506120304030f06051f0312 77
    0x100400710060306541e402c035512003901c50480070aa186489003030030644d440590b40e10200741c50055400c01420b4030300395151500c4d841d0007000c2054500d083d10443c1c6042c2000707004500c202c0b060510b00300c213025075554280003640051360700c050030b064140f600500c01c0c0700b1020004918510091829190000e40c80eaa010000310311204542c8080d00300c400d40644450910fa01c03540103825a845402214001c65255140004d12416449250b070340040811f030920051030280c10040c6c0181c02614007060381603041d5403205182d4440b0f0310440b0035540d98901001281003484420b401400300b145d080c40c21b9500840090861140941448030300b50743d80d9280c5d0210741d1420011921445502c0c02c0700d48031a203c1c54058020440b500407006a03104e05a170000c0164032070b0049a030308084503a1a03507407036111509000f001d00005400c1c0c0d6800f0401c41c51082c0a41000c0014100850241d03100414048941c1801c0d011180040c05501038140030005042908400180a00072640d101c0811814094015012 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 159190161 1250 159188911 159188927
    0x10b07111507151503060e0c0909120708040504020a050c0706080c070b0603070902030903030108070f030c180b130902040f0b030a08030a150608150405010807060f03020f07051e030306010c020d03 86
    0x24000780040c1000417080c0b0900d5400f50041032441d03021240c00e400800100203035024215504450382e4800008400d5540d140d40c050031102d48035074100b5040c070317854134005000ea8000420740d00004401045c04004c2c50401c00410004011505040620381000304696900c0d00ca10400a0400c20301c5c2c02c007140c010303113080240c007006106036042107480341440a60203841e50b100788180d000d9032241c000e010882201d0800aa8112948508246140381c0343c858400d0b050600b180d0350221480c0d4403242541d4544130002c036841144007242d00000c003410507104020445940096440010b4903010300c080c06a02c1c0041c4140c0c0b40c9400805143e10b0303654903030302800030b02800745000350034400f5801c2c005091030700030442a0082086412400b41c102c400e0003884100c0e642440352038507540c40b104003000018018161001c0c05850303454054035141a03003040041c203501c1004100c0d43c5070311031a04481c6040358020326080040402001c3c51075401d103100020107051000308040e03c03518603030090740100340c002e140b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 159191411 1250 159190161 159190181
    0x80603210708030708010515091c1a040b071803110904051603050303040303060e040213180203070815060a18270507030b0c04120b040503070803010b0711150715 71
    0x241c0f5920b140100340140808428494540980d40c0e01c05240c21b03442c080c10546486c3c00c00035103000d2107800c5001c41c0c83c0c041025000d0503201f01c21182d51070010390f2990321415104a0003600042428200384600801804035040d401c00c50040450050002510036540c0c180c4a41084400000c00c0d211400d241d4104419522542c4120b00c01c0da5000040107000701c069482103019442c2080300c00e41e15140840e401e402118000d6102060299010484660794406150001170803102c44c001d44680c2e0101f0b141c030509800030101c2e07a0011203007031496448034400c80e611074015200303c900185040000b400b00000100d01c0c00105d6158000d8800011403c0908400400030f00b9a440f0302d002039040c0a500e81066000c10784200115800083c40b004240041354220341c002480441ca0750f0250300d5001c06001d01820880d0385010420101c0302140060b00518040c00088402c15518516480c04080240c1c100605900480e21044c8080c91401c2034000c0d1082036070410070500d09201c4448200004144c0014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 159192661 1250 159191411 159191423
    0x120417070b031806160509040c121401031209080601150203070210031401051e040902030f0a1b080105010e010b0c1e0a060f0e0304060c061b0c120806032107 69
    0x10420080003d50320010700415007040c1a02d21a40b40c010704400c6494035211a080494000c202a40fa2070a1503440180007803028170b0041480354001e8202d606840c41c0c044d208168204c02d03401442800000c580c0c80d50620104e04182c1691850202403030b0300c8150503c50107810f00c1903000800b00041c0288101e03045603900504091083c02c41c0213000d0014603050381e022405240103400804c0508111400c2c40c10f454603510f280b019549110b080202600c180d5404a8150148141d440d1025004019880486100e0441e50040d001e030700100c4210400103910031101681800010803210006a181606403030a500b086552000c0e55200c4034a00500c645080c001c0825003c0f0440f903007540825280b080c070f8460319061041411002003a03041d50800540a166500104010840c80d806022900442e0744518004241c000130380c00000b0318ec80f81c50035040040b13a082d0040000300b2403caa1808440d8a15080c02c584604102001c01c0e80c50b4410020020a03102c0395803040300084a2805075481c03158001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 159193911 1250 159192661 159192667
    0x1061505071a0f010905060d0215130308040902030601080906040f02090402120f03090411041401181d07080901020a08010e09011409010f06060219081612081503120417070b 76
    0x5005002401d2042c5d0898038605008280300d440e00b10400e00000e034000705032000803001c0d40d501c00442d5100e0300d00303000c2884401100000062010010704010045c1c1e89005849180c0311001603c01303d0010041c1c140350b001502000b0000e0410081064441e406950404203a0358030310104203c80340b00001039034248510101c2c0643d480707002008200e1240c041d503051221440101c000c002e18045c0b030194400400a40c95110f8680d485210b001065000c10320034440343c10b6131140c1c501c0e00400c3e80f40c4207281100c0108100243d99170001503164001e030300c1314021480c00303040c04001482c8400c180500425242e0080c046880d24000f500f041ea4500d0180a816985003404004540204069501d40744641c2c103040d00054900d00201d80643c202004040380f80c0c441900350794200303490b40003c40c0080710503401e290300c501050406e003240c1e003040203d2701c2e8403c40e418480c00e441c0d100b21000303250314400e60001031520407006c00c0200f62401c48d10801c01c485003e0040440b4036013480c01c80c0d0020814482c000c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 159195161 1250 159193911 159193921
    0x90109080a0609050d020307150f0b0d0308070e0a05060913020904020c01090b0f100e130605010b0a140a0c14010e0d0c06240b07030c020a060905090901061505071a 72
    0x10303501c00290b5038441c04c00c441d40b01c2400340c000e0b6101d0083d2070002d000900054811040321801da00400500300551100280d002102c200140345010040d0b020b600066005042006290308040c400400c0b000440311034500c0c030700c1c000005d4030910501b0416805000d1081d14102d0020203a0181c85e90001d000700b003036440b0f62850b9803050081c0b0001c581941c4085014021a07a14040c041070540140705180b50207625a081002c103550407680513190040d50155040610042405803242d50301a02500011030399a000915000700030b8040088003000f03503030080020800702900101c0540f401a8882039110340500000d040500405902081000c035018100c481300d001076002120700c0b01039100b4074040001f0100070300c80b000c00840c00711151b800c55035810381c01d2000404480251002c14403c4c42c6c05640500158041075091400798070000104c0e5604206000d9844c05042c1d503a4082c5455008000103403403c14420b180e01c500703603001014440c00007500e009002e62201e44c08550403042030141414104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 159196411 1250 159195161 159195173
    0x3081606021605010b06030907230d030503010503010518100f09023303010f213309021c080d02360f010f030b0405090a0302070608100b090109080a 65
    0x40d0305001c0b03c50f94030300207145859213402c030f0903170703000c5c0742c51800908482d400c105045105500d0b24200001030740304194607110a5503000b009644a80c801e075125916545040189829540040c103120003000800615030a0b400000034055240c3c4010040030a1301981402d9401c010000514080e41041130b40b07201e62980c846501c41d21103620074a04162081d10315401e030340029804280140c0c0c8501c21299010821404012036022220140f0709180b0140016503444007006020400d004000550080e080100580c0110114a000c00d511106220140440d80091002e10032028441003a0740445a61418440d40c003040d6101c8203040c81c0c04640c0c3d209200910038001038081d00802800a0002d42c0d688a890074254a040c85080584214411800c2c1c5006441b40c81150408001b01951846a201941d6880c028135006140c41e801415290006040003402c1980580001092107400800c0c00b42e151151842e05080701c04192803280c882e80e0820040320168410382c406041e0b40302d8070880b801405a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 159197661 1250 159196411 159196447
    0x110a1701060501081b040b0304080906030a0504110d0809091308040801090b0a0614040b040b040903120501140102030307030b1801030b16020705030c0603100b0304031206050d08040308160602 84
    0x42601c3d4000300b513a4100811142d510a12002c4e8170707045082c04204040d101d40400741d07802910500d10103040040b5080803441c40e4004560540100d61501c040c0002e1010f0483d44800d040c10954810365511030039200d07045144a0840c03501d010300c60307000025542140c000c02c1c1041c55035100300c1040d600c0303948544c6280600b038848020340d802e0303e6600124030840000c1c80b0710422102a1b08440540e03100e084200001000071410b02c42e0060346480d8010b81e1a0740b035100e40f4810034440e880340000d05004000c80c2080b2003058202c90440e01c0c01d1500520030f80e0b00001031f0f0b42d12403001d29012070340d029002c01164501d0038004a94008008c0c04002100b00588490548c4c4680d0718420381400f590341c1c1200881c0d5400e000d124858054000145c19083d60600d60010f690020071a180841c84c10b544210f01c1c48540e03c110340543c00515092030501c0401e885000300b00084c581207079801c0000e1407513150824607208a00c0000d0443c40b00140b50003d880081088851040d0025411500d450016040c59a449 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 159198911 1250 159197661 159197669
    0xc050301050408190203160602130807060c0519051510030c06050705011404020a0627090903090602060108122a07060210020301180b030f0d020114070f0c110a170106 73
    0x25207030b11130003412880007044d16084800d403000d0344511545911144001d44c07010112848000c00030b07001040180d010002c0300001c000541e1820000001d900f020340c10105040c140c039401c00101e502d00ca01050300020281040903e03020507646940b01c008809021500c943d1008240c2c0b0307101180001c1c01c0ba00140a003031800d000300024800044002202042d0900440c2d000b9480b04c0355103024051640705104034090b00a90342c1800f0140c811640b10180f000c1c61661207243d2864a4810210806a10665181c020101c5000030003055042000076501c0f1166500641e641d01030125070031144d040b82d0024007001090654100e904c424003e810652110824000d075009840744a84180119225208032070488118440b4001c48000d01550a40941906401d45901d40300d000400b500c03081307040c0903056445c1400e8000098085064034612940c0e1b10060514060003000f1004103a003d4102100c5040c481e070050407180101c8101002924040c8290015a41c0b4400280c0b415003030007056124900b52 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 159200161 1250 159198911 159198937
    0x70c14010c080603010507080a050c07020303040b041a03040510050429010905010f050102030d020702031510090b090727080f1609020a0f080a0207020402030405030a090b180108040c050301050408 86
    0x40e94030030f400e0500343ca03004e40e22080003031011400180c11042590010b500039402d41c000a2400c000ea400080c591b8119070001488040c00043c2008420b01184101c048240d5421481d421854661501d50b25082e82d1b20100d50761a0315000003c00300004c2042e10072640d654249058080c0010307802d06c0080070024040d0b00000d5203000c00110b0b00a0301a00b50b0070460358160300440c9400c074040da080c1e010f50480c910032605031040d10900654a01c107403010070302c140c1c94100b44581c0340340f9000c214020b0301c420001c010b0044c07007044180300b1816881100c0b4058000e80207201c41c02498080b510740c41da402c8030303480080b01c2d000d0305460015280c03002c555100c1506a41141110098440c02c444040340300d488a1100400d02414100501030700603440168408400d0500606005254000c0b406990040710102c1b51034200141811606401140042c0a000302a0b241070405104521102d210920031030350342c0c14007540320001810030004031051405407001030000d01117030805240400054110030038032901 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 159201411 1250 159200161 159200177
    0x8270a030b06030c030609071a0c0118050d0302030601050702010309050a06240f0806061011070f170714061c0c02011b08070207140316080f1006030209040b070c14010c 74
    0x905d20300012030f5402088008081c1c44251318210749030091004035015400800e00601102210600c01c2c410201103005a09036801440c00614200b41840d100f200004181441030080c05402d0b60300c1401c0c1c44c4425428217000680000ba4140580b41110300c80c8003e24603410482e80480818015050143d472240c030000d0489940c2d150800340440180f207001c1c501d040e52141c400200d0314139006030014000c01e042d0a1290019841a414504164243d04000b0160600400400110701c549040701404180d51002c2c2408600300024259060b9001100f54890b90003c11010701e1000f10740c00d0111081204042000040c55100010f030291113111520320b10340e48009003241c400307802600494400c44083d400b6181460601d40c041000141c1c901c0303015058440c0d81e8001d003101010079451409440c04d40000c0c03419030301117007101d0301d40301c548812503444508042c81000140c41b5050055001640320311a00031540c1e1700407086948860105014140c5290a00301e80078410b419400051000310740c1d659449 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 159202661 1250 159201411 159201433
    0x90503090a0e0c07170d051612020a0f0e0f03150633030406090f03030609060605070809100e090f010509060f010f35010509010f0308270a030b0603 65
    0x1500320b9045910341c1030a6810416180014a01011070038070400d910002d505040c1c039020381c08200c0320102c40f191003036012080000d940d5500159401d90145840320190300d840050400242042c007074150103c144070151031aa03c0380e64030001c5591449c1e0000e021204142031400f50198224411349000d802003004210030240c42c1c88401c400e5100c9030800900829560f41050b8002c030940c4003c209680c0700c1e68944401000034190030010b5605402503a020440c03901380341c1d0307500c04c0780e000d54842e10602400300020000540b0b0b10080d1600220f088031222045a8560303400d5866420411003a60300c41050400c014007140e480ca5201c1c181c03041520141144e40d00c01c401c0c8891a203442e0310041c0401c08200d03036203980c04d20501071445004c00c08110800c00002d010995000071203010612054088010010311442c10203c2c0414010560b50040c040482d2550b100d500d0329102e148440c50341400041810620004655002d00341244081d040c122260754038241154425015a50b00b8840c1c010240201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 159203911 1250 159202661 159202679
    0xc0d0e12030f070b1012080307030e0d020a0f0c05030601120303060803090a05041a10050423090c0c010905031201140f0a050d05010f051609090c0909050405030c01090503090a 77
    0x20403154001000034503010103a00d0303034130941400900403401a20b4194021031040400004900f90324458084591a8248460054295001911007403c00ea012841c806603240d8000317051a15690405010b00c1c0750441c4d42016000003646400c041e0f003621521000160001c2e061032381c0d0b82283e0195404129064403656004e844e0b00c00d512040768032042d1203509102ca407900e6400700746100b4049a46640c400e542801140c2c2c00411003420001142003c5000c01c0a045411054800c903519100b003a0400d05a0a000038000c40c2e001d400c0c0d440c140400314070380e04030600035407044e810140c025040b251030b8040708294082c162800d0060000d0220840c5c000c900d5802c0004010110703780003441008118141070030701005030340c1358005039481d648030102d500b09a030007440390038007030801b03079002d04080c84894070050300c801c003294000d8010a280051411009500116050a5540240002c1344944031401c100380b45024804103c02c0c90352030102070004000c4000b00038107114106882560f0200d81e107121070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 159205161 1250 159203911 159203917
    0x40203060c1303140f01140117061603020c0f1218010f09050402090a18050402010e19140d05031201080d020a08030a09080f0c0f060a0614090406020c0d0e1203 70
    0x3604110710155400c3c80012001c0c19402d0158082d4030440f0382d001e00644445080d0b80029180135060918a4014040c442c0c0b04042d540d92602c2280040c00113007003443c0c210300d4110150b80c03410200b503400300c0c1b00e2294050601503440314441043c100e03510210800e440f1401b40d80100020740d80c04a200c119044294095184544d80341e04544601d00d1040c505420300010b9030100c41034540c003000302c203c0400c507074401e69112080701807820350000b107a10b400c0c8009420b0302181d603555403203502c586540a80301c030070ba04a030000790703205070301c8121031071a036040482c0300b0311610000207005000105511640c041080c400b113048888000440360764000c1800141e88420184034084c040d4041040000d01011043d0004501e107803058002e5413504074030540802a035001030500a003140c02c03010700944044800c0041c0f81e0007261020042042d10302d051400d03400611580e41e51800b4803034a41c00201484010b40c192178040070f001040e40c8242c1a150801091120881c21b524415200000e04440006000042d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 159206411 1250 159205161 159205177
    0x6050c0d090b0702010c080c0a050a021305010f03060c090b0a0c0215090a03080306030f150906070e0d02010309020f04020a0f140a02070e090f0304030b0f0609092a0414040203060c 79
    0x20246003c405030011075403900300504c241d84c01e100c20440300d49040000c1100c814914040c0024189111051041081040d02090400101401e080040c022000b10040501c01c0301d5001c1000038800105d0001038820300f2895215180405020400c20455500305000c604d101d4400c9540202528030340300b10048034010030900c42c0d0425010801070001460388030081d60410030090485c0d8000320100703070152a2604141510308000141c6041c440f03044020401250890201e0071301c03003088003101001c141d0030304a8400190425448824240542d151a002c05629140241095545540c8020040d12034160150840b0009100b082c004c4601581c4c5001c0d9251226154060a10903203450307030401e2200303400b501c44051401340c0c0311111a01001040108000d40c440d44205445140c4105e40c1c0f086842c0c01040c407802001e1060401c000c41401040c40b11011510b090011380d81c0074040001442c003d108500c494105280102110031140c581c070b82c90344917501c04c908071f41c4a991080c0c104015405880c00c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 159207661 1250 159206411 159206429
    0xd14070e040209120706020d02060123131e05060109060e061218010204030b0709050d020a05010f030605041418030a14070303111216020a020109090f090c06050c0d09 73
    0x203001425182030b800808501074000c0a104c0c0c0f030204645050b0070141590701c51400340c0c0c8804400d140f5a03030144003050040c04807011221103007495140010500c080e04001e280300d82108220274442802d00d0340001c58210700300207030341c00040c00c0c03040000c000e11080e686640426070107540011124450b400b10000f100026042500f4103410003a1070500c80c0020b881c00c21510303400700701d1111421003440680001c40c05011082c000381400e600141c5143d40713540185014940f1082c0300c4c03025854019580e41225420300c0d00c0300c050f0b081604101c0040c440e80c0c000b00d9005090030411000460000d4610303000e030225079041e10312121251001d982d03d01c10034424201042245203c0080c8020712400341030511700a04001c2124440e50440c0002ca901200c5d58070300300b42c41c51007409642115401742c5078002c01c4030700040016019580018055400c548030704510b941d12420780d50b02507845908880a829800008199a00c6d22a01c020301282c014000c40145846007484401d280c91103900c03002c0856182103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 159208911 1250 159207661 159207677
    0x20030d1a0f1f0c0f0b011d010e040b100504020c011e0203040c060e0d0c150e06040b0d05060a1706010e130b0106121b05070b15060301060c0c08030f0d1407 68
    0xc01c0007951400090026014070001c00c03092008985044004c0300301500c90388112500d0360500140d54041d85012001c01c0c005100c84c0c005101d8074580794152900a0740000b03090065988202c0c1480d2402c0c0785400654110b800403030346920603401500104205000030204105280c1998160400c900040300c0180068034000002c00c10640074542a00c00c881d405014000c030003c41d5200d002604100d035004644002414080b4042c10354001c1700c040020800303c444030314240c5001881a202d01030311209541c4c0d40e03503441c0460a00d0746c411203080d0090402082c20a5180006aa0389403500000d104503d03a80d42400c1c00182e84060700341c89400f42941c030080d8512640d00780101201c444460328444070b42c0540c0c405681c0c050300046040c2a080e840c4540c0c401d40c5c0c8058615241003190405010341032039190700aa5245507588440030359056521524043c0707420140390400940110896000322014080003034401c0840b0540001803203100c0089005024003c0d00c0b0b08075101024088850710b000503881 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 159210161 1250 159208911 159208939
    0xd02040e0f101502070519090e0c030309011103220f0602010917070303150308041502032517400905060609091504180f020120030d1a0f 60
    0x840d82c002d61003e0070348102c170a210b450b40c0110b00d03101048136280c0d1b40306001000030040f051450142600410449000c0c000f90f1000c0b0002c00d43e0b0340074118005051043d517031048006100c0400c181c0390721142c602c0018030201600e0b04d206402d0700d0305010380c40c160000b940c00414007a0050094111059100c1200740d00800a00104141901b0030344080301050707200c81c81d0024408070004580060744c01001601d50f034502d005070060031400c0300c109440a5402c2070191001072103c461001d2140b90890034000f10070842440c102145607141d8007094075070394011910082a4601341103006d46500066170082d100e2141d02c1d02031210044071101041c1c9035500302c82c24040002150403e80d0001405800b007820815400b000620900d4212841c5083d1035001807105d6162a05016484c60b034049000c00141050301502d81006008000c44086c1c18840c400c20075000308141010910074000040301030380d486807540e0710803c018110360080889240d0740290141c10305c1c43d01542d100c0c50b0311002001c02642d030f040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 159211411 1250 159210161 159210179
    0x90c070308070507060c1106070309170703180f0612060b0a0f120603080d050606090607060209130903050325050904090c0e010b070c06020d1b060e030d02040e0f10 72
    0xe00b000e0400005000306000a00d0300e02035141c4802042d180c00c203400b2246100186400790082030a4105800c040011003c51300200111050301c004a480640d20340f132908090b1090743c028019071180c03204500000400810611076401540c0e09540d9644004030701c6540c440640c0c0d8203003d86404140104200e00682e8010982080c1c05090f5040601150310400070183c2102c0c915401035444d10b00024040c80001d031144a510b034801000c07a8010305101c842400705050740100e1400405003640010f00040a50710145e100c805000b2900b020312000c43c9074903004140307070011b440442c400e14850b0303040c117241000c1c090b0202e24550566159410b04443c80100005056215001c1d0361191680401141707158560300350b075002e8610301c0a8103603a46024a80b01d2031075490343d840340741103400c21481c10411a500c081202c8c0e590241c0100c0141d16045070811900070f0181d04030504c1e2900c400100c01c0f4842e4030b0307900984101c91982ca12441d4a0741e503078800e500c01c0303c02290702d19000c0403401000e10096407 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 159212661 1250 159211411 159211427
    0x103110d0506030c09190b0604061e03180f060b0406061d01050403060e1e0102040323100507110c010c02030a03110718020414100903020f1c060c0e090c0703 69
    0x2e00070200c800c00e451480101e0030040e01a034590b540d00d58007156900e61103225000720359500750250780c024a0070745010300c020900d1300f90025404a000010040b05003030707403007034121200c40c4c403501e101e1089400540c0760851000e01c607031000312030031420242460749a140a1013003c007200c0498a603003050b00402c80c0525034100c00c80c8006418002c0c14040400070a00c0f6208140e88021690000e00d00500074078605603c2c13182c02c0c50b201c44140e004000074000502d00d08410b8106e4164140c3c600741300e80040b00c049040662480c07040d40b066240100304541598005410024038900b1002e032000040300c100111401c03200786101a400d58011071803880003906c02d041c1d01d44150207010a8403c201c3d00d0704054039030420314001d00703820280c0100302031120100161450010001c21104490303003c49212002d05542c41910010b40f10b070308130124001c01a100c0241d45010b13421820000e00d4031058600c0c02d03c00400c541d444000001e47c41d12007410781c6041c00980c2902802152906c10f09004003a607048410403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 159213911 1250 159212661 159212671
    0x5091b0a0c06050a050f0f01060e0f06040e070c03110d050304020f03010e0f07050406060509220b1320040e0a02030a06030b0a0f0e0303190e0a08030c07110103110d05 73
    0x708a420142001c41c90500c0340c9401602c0c4600b02007041d0420740012400d14201034031202200000d0303001000083d40090f4400505102696450204840c076400503a080c040c2e503120f404c04554034400c00051544c40103c02d580741e8465107810002c0c15025050560f00c651001192010135010004a4007600d4400807102d0174190003000410f064a1040a641c149a141c0c0c0206d0440d911040c002d01007490b041c012503001d80b0b6039240240c1008154000100065200a54454080384021000d50011b0712504031031040380c8050042c10803200b030108411b00511010b40a030000f41c1e40c0561030104400c50004480485101c807203001c2c403c1e00e60001c2d010082d400035040150032680c44c8000800500c1d40c1d4a80c40c400d0b84045800501d0b450503000c18410f840c5581080b0545030800c004100a0038400c1d0030501c3d80003001d0b90000350b00190b65000034a41703044204082c102850100c00c000c10b50b4444d2006003110fa20581b4030220784000707a001503040c0e4003180034000c1d640300103000d00ca070100f000750302440e408 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 159215161 1250 159213911 159213917
    0xd1205030702060a0b0a052404031a07020c01080c07020d2004110a080414010204082b020607140d0b060403050a0201121404020409020d0f0303020a0f11150c0c1204050a05091b0a 78
    0x110700280e908c010654002d5108a443c24040201492a4903c494003103034031220700d0018207946454080020030081004002c00391010010908000b9500c581c6400c05c0304952140588100b1a4410f5090344100c0042c03004922503070601416110150444c016200b100c0c2068541e02e0039910b99650b1040300310302c2c840d09801d196500340400284140c013004080e4440743c4040313504c080a010501ca606005101c0000e401c250352001e400e0007142c035440341b450344980d81d01025540c0c1320000416404046c040045100d51f00c0b84011801005105011401e000c0c2e20f0300c03d884007071800140c0e2909900750703107285c1000030f11154070400080250611350007560240740b005211b5115041d045d0b440510806045005900183d40414440160390304070581c0c2207480741078104500d039001c100d078016590b012103040001d901020785001c00c01e0321100c03109071000c3c1c4419805a0b00c2000240d0203401c4190010b10481d0b109400391100040d0300c0c1031103800300307020364001c0d001410000c0a15403e07040b01c1d070102c2c0e00c00c010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 159216411 1250 159215161 159215209
    0x7030203070b010e0403120c120c0e030a0804080610080705040b0103020d0c0c050606180408090f0607080703140309030d09020a0504060f03050c060f0a08060d1205030702060a0b0a05 80
    0x151031091182c040d104c803d202c646a4100380c20010030504a1100f4203648034508040304108603003002195240043c11400407414100314181290031101c1007110b55010700c6aa504001040751840c0500290380030307002100e900d5543c4001e561040b001c40d11801c0000e401c030030001e209074206600701da4208030060602528204001445000700c03907080038050005180c0c5407402007001014000c29402c4030342242c000380c2d045070681c40000741040c00f410041628900050102c403039103c0e0f180d0305e5a2500f00a01c20790f101c0505003071002040d800484100c1c00274120b40340048036102841c00380c80c0180c1260703000314200400c40805500030b100151081e80d102410210000c0c140e0f5a41c02070002605e8051400c8680354550315000b490505101071440c0b24102c24802c000380d07030034004160380b04101649481800341d120080842c2c50021424400341c28118228120380056030408011406403610350708450465a861880f0310451302d0b0100709591114181c40100031511700b21200516005034020001a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 159217661 1250 159216411 159216413
    0x7030803130303060e010602120d0908040b070c05010201090c1710020a0f0e0a060503040f080702091303020f0a020310020c0304051002010b131103010603020c0a02031006050a290703020307 83
    0x84640085039406400080350041c94101a458040c8800038801d24800600e25410001c0c043c0d181c03440b0840115260704041440440c401664020704c60845d000100a65165261034101da0150710201040c0e44035105c1e92000100e42d4414821028020780201c2000b105078102140c090a509040100c0d01c0d19102e00e60b45200782035044d00c010700803100f5603281c00c41c2c40c81403000041d00a45619540d18401c4004100c108820781c0c0100481c1c3d48541c1c41010514065614a0f14458500660703001a4001c044042000780704648800300c1011355000c2e80848080c0c90400b003040d42c0c2e828001c00c001f901a0808a280040e00740b00390064410413148109a9080c0340c0c5a001144803140465071400041c2e450740700c1c0300440e041000c108022010112030034086003064162001c111320042c8601401c1650020300c00d280c1402c00c0c041c1405196001301035402d50b50f10310444401409070f6000c0c007481940c007002c00151014140804400c004a454202e807103010300c0c00c0c0d44c002145c000c581c00b03034250b00013041640 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 159218911 1250 159217661 159217673
    0x4060207020a06051b2b050c100218241809041a010e011d0a09060915241e08060702010e06151c0303020405040c02010911010905010f0c050703 63
    0x24010b4800e5955207525401c60313030b1081040310041c20304505c0d03641050318070442500c20700151840484000782121407415507100112128030418103410994059205d61000700c006580080800c10f03003032114403099840841c20007002700302c9417060403401450220320036215a1144003404450800703603803103d1900c071418040781360910b0895044941d146c51800000400200f1941b041c050400e860680305198100148132054615003501c8007607c00e000b01c009081281190003410711160302500c144545829403402d40242000600030309251800d0092080d190021002600194061020554050b610f04941c5420926000850014481c680f0038085a40081080014000c40180c2d00001d0012000c8115a040c0304011340b5910724101300d0050301e041a40c0d0304400300c140c0d076180c1e04039080918440c0350130360083c860340d4070051b0024205003c402c0020340642c0f223441c0e014012240542480410801143c09402c91b0181ca07010520404401e00d040d8491071208850b24499401c40d41026202d488030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 159220161 1250 159218911 159218929
    0xe070303020606090a0b0d03120618090b07030b18040503040b070308040302120301030b04030f11010c0509030111090607080d0e010f0605180403020c0607030e15030f090a0c0b030406020702 83
    0x140e0140e4400300078041c40303040c076001990340100010b0701013040c1806180000c00c030000c0000c020b01001a445038000c2441036581c0001c00078070781803042ca618200440c60300390241250032401e503480c0b800304001070b0101e8020300030301d03405030f40c010055040f082d001d042c80701c032104020300141c945201c00c1c400419030458881c010100b180c02600c643c8154a00342c0f0b0001d240c0106620b01d20b0318460103000410001d1120094242c000780d15040105034940f1041c01110102210010a8800e608040450b003205402000410010b10154001c0c40740484000e03c0224900c6a5051075800501c10800341c00881c00180140c03103e0034081e0004102041d0f0700c490709094404120911207526540c2d1001c100e90300e444807601c00c4488006001400c14030305034038003075201c1242a000c24000c50001512404140c4145400e07500640c0052128401409132010741030150802c41e01c103612a040ea001042c003c0300001148441580c3c0500990081400c1c030101815541000e0003ca400c1c80d024045e100050b500d0784e5032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 159221411 1250 159220161 159220163
    0x1c0204020d05011503020f090424030308011a0702150306010504090e10060e0708041115030a0203070f0504080307030318080a030b030d110c0f0d141c1b060504060e0703 74
    0x80b42c1c95040c0503440e24441000d03220001814410000e01840140b00005e6070007264013105e001402c000140c84500c010070b60784103651071f44001e569001c0205031300880c0950607115040760300d2610f210794040701d1306e080c4108c1c40044d500007048442080d000d09484003c0d5808001850081d081550701d01c01030054425200b0555659000711900700b041d082a44183d0008182d4600400068104a40041d0180078090006030124401c2c14400c00c00e82c486130610704003d201c08400640d28604210068003d400944646000512580d0002105445841600d05850502d8042c503d8070075203a0b025030080011020900c43c0300192811200442c08000192252580a442c08644109078400701350900c104090840d060000da171400120722600003582d5110403605948402910203600009840b89001c40070090075400312181480009101042c01c801880d01880000c044401040080e0f0740c0002e15480d400d002d440042e1400702140241c0c00c960b821602410340003a5000c51040c0325410601e260700 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 159222661 1250 159221411 159221437
    0x3020f0d090e0a02030601050306131d07090605060405010807080601200a11011b06020c0c030d020a050610030b0c0706090209071701090b1810150c060c17061c020402 73
    0x5041151030402c0314016400b843c0d465085103185002c50000e4518000074007007a008070301525801032542029030240c0b2850440b2001207040000d00c2e101d45549814502441c01268109140000d80f806d003a401c3d02d065804c140c440e0142c44d5280001200c000074010541410014641c1c4585444001c0c694800792861150b07020301400385a0b0706100010404d41d02c17140d8100101e800c1d891094000007000f11041552244002d40e94100c40840303a4030700500307414404d9041c02805104203100790001440803e9611a000f030310305030b641780d000c1484080391a00c00904006160700004240c0b4040200600a0078490200026030b413070103030042800680c04440f001b0100751030f0f5440c1a00c840270502c5140c01080844404d110403040340e800300d10461041c5240303000c070500c0a000300f40745000da00a0240606240704951030683c1244500600101c0d0720340d0140d811919018240c10110300c40d000d0f844206009084c0d080315500c9075403d00c05941c0303140301c14118107041d0184d00320042c0d40b540010039104808007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 159223911 1250 159222661 159222677
    0x50c19080a0e0a050a06050c03070b1302011b0b041713060302091509060901052a01140f0601090b030604110d02030714120f13020d0f0309080706080406050403020f0d 73
    0xc01c003030101a02001020b10404594408000b6550391890017000d9510b149009912100010350180c0b0f50b0180c0600100164500302c10820004020340d841e0841600076030700c424251001c5200312114107107038075026223407035400c0300010089015a0034030428101c4030042035290115003807c06810741c120390130480c0020340008018845141241184d072600941103100361821010400182880c0704028003035050060201c1c00d80c0710350403405144240e0212903000426040300c40315500d8000e0144c1c2004041c0204114041600c4001443d6680c0c0b0410341038642295035420720030341d4070302900014050340c0d00540713940c031006a030b1481001400c2407283e400c41c00350b00c81c04c0c00000a84002d08129a0781c1c2c01382030030f0140c142c0c1d889824054580002280d0800b513082d4603985089403440c0001c11010b0341000344c0000307620030046e1110b200c3c0140c0d402550780d18412900c4421050703d0712860b201d00e10000d1603a402041c0460442d030310031a041442401110351200b41e24100508100c01d1020005c0891011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 159225161 1250 159223911 159223927
    0x907141809090304080709051005060c06010f1208160516061e0f0203160521070c0506041401120212010b0c10020a270503011d0c0d050607050c1908 65
    0x1007140e03242c000b0400c201541c1401c2c20041000e9072801d8030304ca04d000d8140c8031000f2500319a080b0301c800001e0180500381660790101c071024190380341070078802c1d0480c11101107000100309007004210800310b80d1000010b4548003054914074a400c0210109450600a0215240c052038524070140010a0140c483d9003172175552610800030344140802e40800d021400e0396400c1c1d040c2d804001c1703a445401c07100d500011a882d50918a18001981542d5400d02a0320f90010820340f03c900080d2038240d2180d11404000398452041c030a41d4092485a0100078030f40890011049d07005801c204400c1240c150018102400020070003e00c448c01ea0001c003141200013a072215201003401412a0b001560009624014031b0000060000d59010481240171082c010948004480010000010440100240004494215100c1128400842421052054941442990030401c04002a090301701c1d028000c1681c440c0400ea0380c540c01190383e081a4018000c660214407840e50100034180c0c000c0c440c0540f20b40714 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 159226411 1250 159225161 159225169
    0x150902030c220e01150302011b15060e0703060b03010501230d0b01020d09030506010e0c0c01060b041e12080f04150302070c060c0f140c09010306020d150308070209071418 75
    0x78070b41c81c801c40f60341482880004040c90004850880b6428070b0003126204241c400401c03515941c4400418500c49030b0301240050001d604400140e8148940050140d10364900950807901144035011052509100410582d8000e4840300c598080f0741c80e100c4c0702001ca01d04900303a0b543c06180550602540c40b5280c40c440d50303042010a900854074280312401c0d90564684c1d5640c2c940500c02d1002c40c140880c0000d44140390b01013034480d42c20030107009100c41034803a1850074594000e40140507034030801140034001c030301c4404071010464000f01c00b0708107200c001307460b10105d40d444240c032002100001c210004e82d4058241c82c0c20045600745d42c0050301c1d650145000c148458042c0c2c09202003182d11114000820b90110141c501241c3c001840c2d15451181c490071404d00c2c55100c2c0da00e50040c0318000000c2031140540003130084018221040000021040b1b175004400002c0c04040c103210420b11081005081000c00e007a0890744505104825464008030000a41d00c6100d880c000454462108181c50030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 159227661 1250 159226411 159226421
    0x606040b21060a0b04090903050c0109050c10030212191404050606010813020f09090f010908040302030d0f021b010509090103030c050721020402090d020307030309030b0c030103150902030c22 84
    0x12500c104070700b4130705035000c8614007540c0503d0403201c1e82c070b584000803d0b004004590114024400070300c41c0485509080c0d4440a040c580c15001d02207849241070114031a108460241441c50705000160300ca0390000c41c034807000e0300d10200301c256560201000c2d15244c221000e10480c400e400601c85460817000060540c40c020740182107100301c0c00702c0440180d44444040520402c01e0b1003004560b40c9900c00940b510380044e905e81844e510745082c2d003085c4085180140162802902210804428000115160346035425581d00607040141d0900e1030609001207408201014540141841100030028011172401c1e40b044020900d140722a0040100501060008150142074940c0311684007040240068080100038482c0381e000641100a81d2103080581c400e40d006011100e4060311b901d40540400b07000d000c00e9942903400000101504004003c80b4103981d0701842e61407242020f000359601403d00742c1b90032030781409040381030000303178450607000d081008040c2e01c0708450340000c862a80c00c4503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 159228911 1250 159227661 159227671
    0x1e090506011e030206074d090106020a0803041a070c060b0103050f01051311040b030402011b020d2003010912030c0201050615071a0c030a0c05031e0606040b21 70
    0x395804403c201682d50101552002d6030030090000300081c01004148031202c0c10444903010315103c190740c080c202000c294183e00401c560303c03600c0700f0b601705108001c4d0200b0309108050050f4807079070200c400100c0910265412a12800726442c161442441c0c4130402001140d100b00041c2c15a1120010710038036006100c07642801303080400150805800d40e5900d07400502545000b03070603003580184d02e00c00350717802607002000038a02151a20746880fa07541e59940140c6080e0700003443d400c0c040c90240c900310030110540b03500802d840c04489503030342c9000c2c111280d1090400404c2c00172042c43d8450320b007030144d01e2005c1e21031090300401c0c000304030780502143d010704002011a03140204005007621103018450746450211171181d01c0b261a80b0f4600c50302030070803062400240035001030050390071114002c0c501a2441c0d600a218288011404032900d000455004e81204a81e201c00b03034500c0ca00b10141e68014102801c41e500d007940303509039062954484000c081e00800210a8141030300200e000d09a007003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 159230161 1250 159228911 159228959
    0x30c25091407030c020307140a030e03070b070605070903140c01080a0b010815030c06040905060f0d050d27060206010e13051203060d1e0203010c0f09091e09050601 72
    0xc0381c941548002105000b0940418107598080b043ca03000d008109503001540d1154080c18030b42c8035107044541340c40b001c000132030106903a04d406210350b00d008280380c000d40c1c0580300c6640c24142951520000307040090400b90900080c00404404201092260541001d444005251441e140e500040204400408011946150444102c40c1d80e038001542504940d4a00140c2141040e080c006803e00d06e0140001d40d0000000400241981054100611640040300c2c0b20b034591520109002c42a581140300130900e42041803030446081c02030307010311030001507012002e190300a0180425902282500141d0141c1d004000420120107001030040d841010041030781c2c0d40c00c3d8181c0d9030070398541d561244858a401d0100025607030746c864440704035005d80c001d07502c03402000442240d10302007440010301ba40654209580e000400c1d000300d44511048081c0c1da500400686000c0c201c90050540000d51301c140d440c0d000740036080f002c103030040310075460240000d81400e5140c0141d07212612030102054280d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 159231411 1250 159230161 159230171
    0x13020d1b050c0705131b0801090c0503010e06090a060302131a0f150f1207030f0c02060f010506070206040305061005010206011502101d0124050603220302030c2509 72
    0x284808624102103404c01d80e10150020f80ba01c0301c00000d46813122980c00128000003840d119140e00059540c125010f22004105020810804a81d00d1009000e2000903000c001d000c80c846041541c0e005a11442204000881e551613a0014036003c41982008072229140c030b0b0700b4240741c0d0180c00712039000d030740c01c8682101600718a00401c0d51074060700704044e0750b284d0100c0d50302042c6007141d08a95118031001103480652a00c000041c0080000035014080d01c3d03d00b201800c5110700006081d4003c15444501000603803800d020800da503480040c040340c0119080c400000010020404580558001d81c2c1d522201f904100c0020b1810328160302c2034610031b241c9403c4698280d0086600c14950100d00f5000c2490480c41099034054101e010100d5215071820b40400c411940f00d107591003040c6680020800000c0d81d5000b0084540000d0701c10840c3e5a009115041c008244004201e030ac46e403081c0156030901640726189810454511005808644400c446a05101035080300030b0280040c0501042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 159232661 1250 159231411 159231427
    0xb04021206090601020a050d02060106080c030f01170106090203040f110d080d020904060503030c0618070303021005042904020901050414071805030a23030a12090213020d1b05 77
    0xa20320390240105000d0464500450500c0e442400301d03035102030308241103d8421007100402950b8002c244240400200c41e00d01158620880c1800c40340680a030010600d096400d044010001c00d040c40d80d03200042d0350341c001c00140008036002540c826401800d501100c00307981d04103214480241405284101141c00c4d0a00014000f10156244101315200042e2901c071203c0105008040f070340c001d141d2510000c949404000c00001d940741c410813001c104641200340145c2020b0380e0701c1c3d1600004015810003020719006c0c031056440307a075100d0f004015020561714201c6011483c864070084151007016604104810344c1001c0d12110300400c016107080000300181d02608410087c080c10120811600c50700300452406d030700e400b20001d0040101078070640d190b985044500300c08024040b0014403106024500c200c5c40110540d00e202c00d917038550191109080c0d400400501c10000100d9110700186d0012020180510140482ca0259140044c1c0c40321048403a10f56190985150000c004042203124 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 159233911 1250 159232661 159232687
    0x501050316110a14032106010516060f06060903050114150609010c060510170703030c1e0c0e06040510080c040b01020109080c060f010e040b06011d130f0b0402 70
    0x81d181448614120034090300504585080081ca000090040c9240c034903225000e103000320060007022524020f100c0302044540400c003001100310344c1036010800074403160101040c116000d204003442100c0000c0d0f8070200c803161360107c445a410040024968143c24000c1050911506c0c6074007110302654102454414207c0300240003e0104900404020441581c03036406a18034002c140e44c0084203200c0c62070980d219200c004403a20805400a401c4841a811481c002c21031009480d0140e4510507103000540b40c5002410b00040341c1c103100c107a030340c079050007164100195402030300381170040304014104801004190303800a00181640302103900d0400c9000d100041000078401c041d2008142a0b03442e4006138014410400041c01b0207000040d5140c440301c020410511920030000103284990302c0c2ca02c8403180403800c0b54000c00ca03141580c00b103540c6600903a820110040c14069007480d185480d4041072036542c80410444416445200d081840074a60180c1079001e01c003038030114205640c5840c0c039 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 159235161 1250 159233911 159233941
    0x609050412080711060c070204020903011118061222170d1103060a050f060706090c030512030702060114061b0d0201110708070605070c080304031d042a20060a0605010503 75
    0x302c0721b1904000b50010854071542c044d41c1000310010001c102840e07091061140c02c1e4800c0403400104440803046001500d81481610982c41000d075224000d55100e0807200c011a2a401c1c400703003020b00d00810440001c02a9680b18020f0740b640381602e0310760000038100001d5a040140010101d0310038400c00c074064840020200444a04031070701111f5411200200307200340b0032980050005400c090455052010340200030007202d2041c011940920440014014107002c181c40b4400180c0060707004100c285480800740542075002407103289450f03c1c291801c0a151142813682e5410b8001411203d041502841041c00c0c0110b8800340707600e085151351b608249441140d00041500b40e4401c0401c0d8518404c5404546260b0312840d11603803410b01e414080c03c2c8148003101800003054111a1147c0348c10240500300000c000b0712030840e917500b024041104011119400c42081000446c2d2031a0590011000c041440030a10007410710707400e00c5113840041d03a0f82a041141400300800501842d84004001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 159236411 1250 159235161 159235171
    0x3091205150a24140411070605060a050618032b0503090106050a03140607140304080304111c03091208030117010b0907050405040b0f06030a090204060905041208071106 74
    0x200ca90320b02c80c410000b090301a6a032060440c08030680d00c200000c64250324160381c030306014a080e409801003080140c1d907102c4600300d200c034001d221200000300107402241d080320000b170030600140c1d00d40b4003046003904001c10041455419142085682c04c05000420b550f456100c0c00992840718400c50000c04100d1002c0c83c0b0421500000282d080003084d4001000b5200080034504266a2801c2c4581403280c00d4110403514041e00c004120454014480800b00400f14551203083d5070752030b20b0b180030a41000f00305441030714040c000549142c1e100b81a05080b0303040504600c480712010301300148100140e400107a0150700b000c5040c4041102c6c60700303403411264541c240c1c817200380c0014203050152000ea41d8440c0c000721400c040c841c1c0d45400001510950b801500c08001d902506802c0010300c907001d640d1160400b4040010481515003904003e850300c1c0003030400700b1600d0303480030100c0803100e0803141038501c0d1212220800d86250700151b510b0304000c0c40d103000c803240751148500c01d840321030141c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 159237661 1250 159236411 159236443
    0x201140a0905100203040e07050a09051002150405030d0b03060c1b0304091a09072303061207080a0302010c05040e0708040213140106020120070204021e070501020703091205 76
    0x540d20208910500e0340724003409020f840d0030703100d03810000c02960380d404c01d0040440804864000441440c4204140c1f0f8a0701031517a10303075003502d2800040c059280c1a12070114114068040f40d02080081c0008850042d0f00c80e4008581e80c0b03000b02840c400315001c0c445c040c1e10941002d024007203900000d006640c3c5460b42c130f5600d409040700e816500c0d855071240d640b017081118100f4071000905140f140c9801103100c400d44504030180d0703070708070103d942108002075190510031500030310f40070041810146500c81c102a00c041c1c40c400c564203a680c5000c429611010481e848601c40c0c00405034203000b0404a0325841c100142424109031401400c0d4100810072010402d1040001d4159501c208081d45610381030340c010000d22481d034a00d012141001d0148102560800c0ac42501c290600413010380044440204035003095690380c20070000c0d5004282840c10207007094038900070031a0b8a00145100342c883e60005a85406a28029180042d140d001c504200c0004004101040011910500e40300f1000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 159238911 1250 159237661 159237667
    0x302090a0507051c050615070b071101020f0409020705120c0a030327061401061817030702040e0709060801020316050a091e0e09011a120c03030d021b0703020114 71
    0x4480f1401400c840e000b441074001c44042810f9030350307880f16010765025100e412410a030149014114850100c008000e00025000510140d10454861080303000c484005483c1022a800500954000741c110000d582d500140300e1080000400a007540c000c0e04403601e80c10026403405441d251141c642000d81415161908a20060511041240c001e100c04003040507002043c10804009c1841540d401000004480080340c2e841c01018540b0411341e07901d014003001414860300600c07402c03420072407210b1407009210380c00050f6034501415080c1d9030b1200050002510340510380c2c064403682e43c402c480ca83d1041040c08a010b0190b07001c00326808a0f8100a680c810258800f15066007440c0d01c08448241c19100f030140309400030300901e088605080c00261b80c0d840e683c0d00c0b24202c8a0320f80c45c40309903000780b1070012b99a040c0001c502071206415020782d1050f840090110b070540c2e016584020415900081500002c40288030f1408103031041d5004000c00c030304560020345001240740c0d41d1600c580001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 159240161 1250 159238911 159238921
    0x1b05040e0a11190807020c030606041e0203040b090601090209150f0d0c0905012a020d0314030106020d030c020a03210905030c030c251a0424080a02040302090a05 71
    0x20b50000c40d203103400418071a9a40c20f403a09442c812240700100d1400240c0c03140003003000548002104106450018064800c5172640010030009101e150204507490b045603c600c0c217810b0032803014510460007108001c2540c0382c00030700103081040c140c0020240c1403041c070038030003107031aa004240415444900c62a5443c0da0360b8000142030b0083c90309000300c1c18205840e101c60a584a40014112070081c0c99400040d800c80c0d071700c510f00c200e03000039604143e10910180d4015103400413401107420b000b4101b540c86258008080213040c1e100740c0094000d64824800e090301580d00d17100d640200c580c148084c11407000f0680d0f00510301d05800c6402c01d0284210b8880360001d1805e688201051a0700c102120b56417044a401c40b0784a400c590500d04842c0a00c81c02c64500e41e426119088045002c9040015140d040041d111023022a6091a5610340c00c14400403c106c0a40314292020080c4000c0706280d40c001104010148a07004003030b00045401400304200503200d9016058002d000d000021030b9554403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 159241411 1250 159240161 159240181
    0x30906080a060b18090a0902060f09040b0d05010b212d030a170603030301030309030f1b030f05010c0306060e041e0903050c0d1416050a0b10091b05040e 67
    0x185400079240f0140005134014407154136400c040c00e940e01941c3c0d50143e0fa80b503500d83d034200c0300004400f86d0000380030054868214010801400c650200900c00140c112802c0c012074a60705e958181111180c0d0350b07008240061500c0e0303200c0700c0840e0035451450ba41070182d900035521080c4030941d1611031080d601040070365103640d02c2100201200f48084913115403d81000604141c00c11a000c203020046201048050601004903070603245c164031280960340c9541d079181076450803240151481c0f0b02c0ca4002c8280210b0760103611000f94012030080500550300d081c02400c40303007190381795030515182c148104400c1b0341004c02455a2001140c00182e008204a10030b40e0014015072111416880c04080104040d08000076200c80903510b401c58141d1200940f09842c0c10844d884140c00d450820f004015144041400c4001c025220b401520100c0d81c059850583e81401911a484444c00109040c482e1880c20302c2002d40d408143c626581101d4443e03003010f0600d1090340602e5424607009000a488040d0f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 159242661 1250 159241411 159241421
    0x18010c2a05060c04050a0b0406050a12021606060e15010905010f030905032b0501030b01170f06090d030b030105011203051e04140109080120030907050d060c090e04030906080a 77
    0x60070030140d48161900001540341540720f40502d91181c5013041011400f04601416a000c0d605561581d500d00002100d050b11915174100507200300c190200700381c000017001d0300302c45101d40f44128400309a440c10f2030b6104415407001811400f01524a00c079030747c0d035070380e2049a000c200c51003070802d440e804c000c080d0120094840100058041c0c800003c60084a00303c01c610900b000f92640303c2266400006020402926400c0c4809071510312902d005101c65000903c7c1c00402d00f07241000c40300001c60806113903080c900304403114003658001214040c41c06804d0700552a8100c401ca000704010340c105000c1001900120501804000010031510020200000310301c50302e07044001125110347d6201045044203809400070f90010302603500000d1021414002e440e8101c2285140012140800c00c032400c5c40e80005101135180c1c4203e0000044603102c0c0c2c84801c0ca1070340500400324031045404030180001200e58014060b00318940204000709921002c02c01c250364051910400d01d88a01001c1c1c40a44 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 159243911 1250 159242661 159242663
    0xc0702040216030906090305100b0109210c080a0203120d14090a0501110a080403030c05090a0b090a0e0403050a0507020d14030d060b0405010e0402070f0b0103080318010c2a 76
    0x5440059031110340542d0700c098011962007582e40d9003002d61918170480b403410719480020040d03170103400e81c011021040c0d042529200780614001d00758555640d03495110090321a03000000c1c502c1040c0060a0180100303640e8060401c03600107010621070750b4082035585488408000d171062000c00c403080d1449094100350b184000c0d24460702c195041c175808403500c0d10407100c012945c1d5840c2154003400c101018060350305042564580305c4496807a40ca00750040c007030140900301041020810200203135141074109025019005c0d086480e403084200b0301c000300d201a00071007030052000c410840000c1c1e0001c02c583c0419884d1418035200d070060b10110f003c0c0346132844005c3c52042203100c0302d25070000010150400d40080802803028130750310803c0481c54400e074001c0034006001e801c1030f4103c9040039002404800e01c1100c071401081400c2e110552007132404e8208880180300003050040300c41c603111204498952000c001c02c003000f84030754083d00c400140d104015200601000203008a10f103000e421046d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 159245161 1250 159243911 159243919
    0xf031509020901030507090b01020109020f0108060307080607050a02190f02011409060304030c020f0a150c24140c040b070204110d24060503040b151309060605040b040e0709050c0702 80
    0x20f03507103d00d4010303110140f90181c46011444e10201c658258814041d07450f07010b4001d41603250303c6004000449102c18024001c2d82c05224031280000e50103810810b540c401d1115544641d05c500c00d01030000d040c0a401c008050b035031a902446200400e01007107a00306d80c03036030908000242d95040444050035001d402022944841d0101c10002810303000035100244501c00c135030794042084020104424101039000d03200a40d0301208810b10142e00a255516000d4012520112140304e4148400f11540307100d41000805500c0350b801001085462013800c1d0018510380205040905122203146240a03c6e02e02030310940e0dc0e4050f0313810300343d4803804561071480118401d00500d82d0059044170380501c0038200c02e44082c00b0315000688588102c1c1074a0040fa0300c0070b0600c42d03689403140031058910038403e00540c040e16001040940d60081d101d00141144524800702d600d510700b60800c0b0031203902036840ca0241342061405640c3c420f0106000055410f000b200240c243c0b1307800700050041c007034010005c2d00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 159246411 1250 159245161 159245179
    0x200c070521030a18090e0606120a020901080c1f020d0c11030303131e05030306060a0908070f090b0904051c02190602030a0b0105210705072405100f03150902 69
    0x11907500c45500031444035520b4001c1070282c5d503201510200c2d4000501030f4000d40001001c0b60a500e032020b612281c0341000002c941c10000b40d0f40005030203090a91154101d9440780400501c18101585048811021800044404030f0003040280d220203c2003c01c5c0204200c510042c002c10003c080d104848400c007808480e128a4164452507003030715000000d548440c40c0c10144642145039070318000b0f460398004040d41c210785a0805110168200d002d405050098100340403c003008108a000b0081030104010b19040d454501c0712021602003070720490141b00503804000100b900042c403101c004481604821190130344610407403d0507221a2001c590380c1c9174500d668240204d540195001c0d60f2940c00403c2983e014000565083c498014a06000d0b094403c80702180c00e02048810350155507030400c0d40c90003440e56121603000324241c1c83c2a180d000c0780da21861060485200d85a4050100c007403580c020760500c2c5007031544604520008102e821000400c5a444509410100202c1e90290402c22 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 159247661 1250 159246411 159246427
    0x1103040e0108030c1e07030f05100504050d081b040303121401060e12010b180705090306040b22031d04090f080c0607080c07030c060b0d06200c07052103 67
    0x40c0300e41c130505030012180309254010b0102d041d01d442c4591800481001046041d00c1c2d130365a40f0100d03030741490507155801802580044540d860060602c56441000500724a5102da800501401409000510b4a0141c041b0071a075201000084400f41c94040c18030075081440c10107400041e1441d66016000c80c800c000000840940081011880c25000c0f6410440d03281490a0701307003245c0d440c6011650220074070100c842540c146660b420f411030788600d0300919207105000030900d00341080c1e0701100d5054180041055101c41c02c03004e101c1601d281d1100b00545100c2d910000c000101b442c2c4408a006508040b1901c0e03641c40c0d03032040207140c0d03100c4000203585e411170a19200c29000741c551007085010300c400189042c0d00c91200d07948614900c00c0c0250030311302180c5048078188502c110442d206595602105095954111801411407094002043ca00d1000e480f08010740b543c0007050520a030144041c401d0b100010a4030300642d0401d4503a41c50300c42401108042030701084006507942c0c00000b81c002 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 159248911 1250 159247661 159247663
    0xc0d090302030c1e03070f0c0e070e150327010b03120a03060f180b13090506090708031303020f0d0804060314060f010c0b0403030605040216051603050d1103040e0108 73
    0x84007031a038007419599003070300542211841400360105000150401c002e14000103021070582d800b058008e8000003001a00c076850b00031101c8087d941d10007c108081c03282541440c1420440b002c540c9440b48007421401c01c0c641505480412558074803450082440d46882c0b031030300354000c1842050040869405030368010b07100d90141d0003402c283d00041d04221020400542e000c003654100c802c501e81140e5155040600c000007409000c4001da032080214905078000d80309401080310362030251000d00090305080032201e29282d8158000c0e01c1540040c4001e03014017103036221600c100c035019126000c08089540028a0b0826030308402000f810b80480c0104615901d9480114203003030080b0703142150380390700c01001185c120b07070a5201e00191001c8002000901020400d030380240c402e040100345e01d910384000030140c0c1c000464640300014541104000d01c10208000c00040f03030807141c00b09000d402c51321219202d50b80e00b0a03003c14052004901d1148813010400c490040036101c100c0100707540c40c1c03c0d0301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 159250161 1250 159248911 159248917
    0xc040f050412030506010203030103061a0a03140d02010506130515100c0302010c08060907050c0a170919030503090d050a12080103120207060e1201021903140c030103080d050c0d09030203 82
    0x161655482d845903000098024071900e800740d40141c00a40c02c581c1b82d95500e030060b02c0ca024103403841c0c1101c01c04440c4951602c440040185d071181d81480c090061820400f807400d00c02d0800d130001c5a040005100310b9840790340c074082041d0109000455141d4a0160099400019401e42900904c0300c40c03040950a034003a0000015612a0b8001d000f03030310f0450000c95041c1d0040c4e4030f00340d0110504000c00c2580780114010501c602c41d110aa513454600d030346174030880c84807010116003015400200b904441c60040e40300d00d00c0c10851122820903900319112507641e80a00c0d480300d4040c540d5440d258090007020403004a0140d80000c2c18035400001c44802040c521080c03000700c491030751000d0007250700c2c2c1c00892000190359140e40c07020340888014040207460003c251548881c0e5500700006440b0a00140381d42001c81c0c025240401d140068102c18141000003c6c000e141e914014401800051640c004650202110301d1002c04c054541c038503031030002d00c00d08d05266581c030318228030038040580101c06 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 159251411 1250 159250161 159250163
    0x4051501080112142e0908030a0504140f031b070311060310030b01080a0b0106020a050607080601050c0703060b030712080403121b0c1404020406080c0d06030b01090b030d050702060901110c040f0504 87
    0x2540006011101051091b101c054000400826042c80094021b0b080e690100da4014010024840c40b141010070300c600f0701240624030020790b00001a8910100ea0b40592083c1500400c1c005014062941d01c0703140f003030b003100c0d0b42c145c0c45008000042015034902c0c500c0b03903000c2c6401c082201c0c12540e4608000ea03a50b061100200d800030303001d0f000060010b00114001d031403141c01202900303103903858900489401b034004150364144803060106070f961640802c5000080c602c0740f540040d80d081c1090405190000a41c00000d0804400c0c0f5000700240301141514100c0c1c0d440304203200908211002514554080344007680036100c426440002d100400d0842c108440c41040710212035403d0506000c1a40703c0d034010100851900c901090004050f80c00401c800d007242d690000c0d041c0d44998403500c0c0100f00781e003e40c41442e25081d014100389024481801c02a01c0350812515015050380482d04501540c9500782c10b0050a0898250604040c0110040900300074420081c107980c1816100007442e0a0360 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 159252661 1250 159251411 159251473
    0x31509070b031014041a0405072c0306010e0106051b0118030f200a080903010906021b0f0102070c06050307020c040203010902120105091012030509030d08060405150108011214 77
    0x40311807941800d100380168800744007071440036561b5400c148405048040e1514041001c1c0000244500f2109200d102c6903a0b101c03802d801c40c41d540002014940001a08418502d07040c2d900100140c03500300c41141e0740001c4602607a00000004075aa600508400003542c00b035600a148441c00c240d0b002c07091100701099903d034100c0c0f41c20045208880b1845000458440e0361140f0544000b0501c218081c0050030030040c00459007242603a14541a030f08010703000c14048c0074000600c40e41d12002c0c030240c0f41d0008044021030505040340c580412400d038a20401061007000800b00d8140f5101384415483d60002600a55995940d803150100035404500040480c4003140d001141038949144c410380100050340f120b032212424018814a400340b005400c600b03110042000101340d0314144900081c08245490318400b501d45042030205540c00148440c0c003001e0007140c0407145a0b007160070141501c10f078452201031151140303080402e03600b030842140c40500c10b01d0314014a1511a000d5020300c40d081e26 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 159253911 1250 159252661 159252689
    0x90c020f010506060a05070f080d02030603100519050c070204050106020309010e0301090803160c050106060c11040203091506011107090f29041503061b08070e031509070b0310 77
    0x140c03065080b640c00341d4900d540420104078880f0f80500c100b02802441c0d0042a02c0d962500842c0e40b05c104076402114286040e03500481040400d01d010310031040d8030304800c0814021480d00310791105464540100d1003400c5541e03200801e4403c0c581105450150382d000c0c02c20012541c59400281d030701e40204203042c0c00110400c0c4201071604060140c1001181e00400090840c2c84800d2902001e0080ba440c2e501040031100c000d40208409002c0d0100030503854030307405100c96103420041000744030b0a012500440c010014040d0310300b0001020300810726080080f117019280d200040b10188007444944c0300b03600c25080003094160301c684c0b29410b0511a007004020404061f0601d6104c1c0c103c00c5503420140030088003a4001c0d0901e6040382e20b0002d5807062840c05140c4a6507030508844542d42012540d60440a200700c80356000030b80301d6084082030a200c818030103504006641d454400105203e03443c6850041070395410104003800180c40e81c1003203642c803480c05032040000d4100c01d209a400800c940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 159255161 1250 159253911 159253933
    0x3030e010510170309060403080a030915020301050103050a0e0606150c07031a132a091109090604060506040b0c10241406040302040c0c050115030b0a0b0f010c03030b0604090c02 78
    0x12122103081c0071b007031142490301c4c5446039241d0350045002c1d0801d2588812800000406003945110701d6007424070010f0300c82d4182000101211801441c05010f1841c0c481d042d60030800c00a03070144e000300c0841d640c81200d4a4022003c607a07001d00c00c200d070108e2140a03001b004000880c0c00121041d41141c0300ca0303a00b5500c0404244102607200d00140441d044000c0f40c20f0060740320080d60188100900c000c0e400c880e5150404011510b00384000d52000c01e01180458942c80c16002e11604035008940510501c0d08150010304503100f5407040c0c5640800015640c4285a01445802007a041c0da0004004040b0208840132107026580750780c40f0101c00384c0702c0214a010407038550f10400ca101415690030541183d0903c00140702008540c8140300e00ca0104500041c000d01928042402c4254020000c2c0e03e50318124914034005000383d8800c5090049035441900d80d01c041c90140002442c020071a81420704090f030007401c950701007a82056001801040f001d000740c0248503241c95540c03c551a100078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 159256411 1250 159255161 159255163
    0xa0f11030f060114040b030403121802030601050609010905041119020f1e0f06100801200a0c15050705121303020d18051e0f01050703120903030e01051017 68
    0x407a100d0101c2220940800c845521030034286400c0c030901c0d2041485c107510703100c1d030400310303001141c00700c0000316514403003c2030080d80d0141c10420001503810140002c1143d002a44548050040034000c0c2c0020501140b035038401c00ca00401080c2c05481003010880230301c4001800e50056802c1c00c2e03040c11540302090102e100160341c0282491420107845891190b0205801d60114402c1030016442a190681c00c3c0c58000d100c0103024544203c010103045140c03801032801d440e101e003071005000c2620641d0000c94a168411500a41e00c549020810440749192125480c2070710100009220710785010429040c4e0090001c2000034400702c0c25000b95030b40c84c1d00102d4620303080000100141c00030081b100c01c0c0c601170300780364642d01c1c0300000004150307450f4000300302c4025201000001703001501860038420700f442d5807100041e91082c80c0a07860440d094802400e540d5041c3c0e0090403403562076800100340351103603000301e00c0359000350000d1000781448114001d0721601401484000368600015101802d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 159257661 1250 159256411 159256417
    0x20405101401030b04020906210718050f0102010e0d03090b0606040602101e1505130b060f070606030606031a01060e0d0b18120a0e0406060504090209040902090a0f11 73
    0x10314a414401001000c00118050401134400c9074125030284140c5013641e69074070250a09611214910441c40d02d8070050305005034000d07101c0d606005200303004110000d40d118868055460170340c0c00c521019813050040780100300c0a0f1080314035015501e0b005544550542004225a01511001c0204d849000401a480c402d034841d03140035a110501110a035007070740d001481d198445003100c04180e030700c0000303036420344043c0e022409400100110500051500d94800f120081000104011001d000d00c0844d825124400201c006c00341c1c0403c800080103020b801ca10061507221100303003c0d0307660707d1500e011104405104c00034030195040003c584184540244a1822401808107140c07500315116004913010140215080c0314032004a8103a0300010020b02ca405825500129500d000d9454000c0c917a03464002558402d50400d40108400c03580a4103907419158010801a5682000030001c0d0080000e40c0c4d00a400c01608410006903005a43c0000356290224205000c40380d940e00b12490340c0d01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 159258911 1250 159257661 159257669
    0x30123011701120201030b120309120118020613030c151709120f0730020109021809011b030b0a0506040e010e1b030f0610020f061602030702190302040510 68
    0x450441c0c010842800c07410b601c504028010305000400c1d403110740104031002c014844880155000003004617041c10003021130061444d40302c6c000c102d1008800410610280caa0001a106c1c0b000480c8005519a1440c54800115400713200208929590220741091040030f607412383c00702e0401503020700d224516403440340c480c2142101a025a41640f0a40301c115002080c045001920a110500000d840c0d070040900d003403407802c04084030413980c0703400a1060041c07011000840e4180080040142c881100b035111604c40c10880501c01e0361100c4840e4010050404400c40b01c02c1000d8810b0001c64065000c650b45080c155604103614bd214418005a84a64414001e00c0c1c4600001003080e00e4061100300c2d00441c0d51207414103004083c90808074903800656440407484080c03c1403103910329100751400074884060018042c4c0003e03400d20b054450000411524510340c580d940810803601c02d00849811980c02800d036101c000203040c85051114030b500040340580d16200100ba680400482180111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 159260161 1250 159258911 159258947
    0x6040209071d100507170d05060307032d0209040318060302040f141207061d04140415110406090306050703050910020f0f0f1903020324120303012301 66
    0x10030b81e2000348044818400b002d03000b0031209200c0c6500041100b03084c00d03a000c82c9440c11a1300c52602000750821a43d02508403442648000c00810004031410092b4601d081e161100c5103a068079040030320170058641800a511520135802c00c000c06070001c111040e9101416030504506032146030075001c03841680101816401c04100c20010610425800140c200002d0101107520441c1a02c0700d203030464a030000c4010400ca040f121100c1400b18100c00000c0204440030321448000003403014a22001400c00741400c01145031008801c1003e802042900784029101a40c40d560344030b005107241c0c942e0008485007400e0102144540c1d100e401042d003c4c01001d0042e014500004840c28003d6000c80e00030080350105101da0581413170001c02421a2a550054261b1b440c0e2005001065101941c04000f092600c103006006004201411001c215207107128286091000c0d4400100100c602c4584903016110000001c40e032244c409034450034100040c1000c50401c40da072401540c510803145112180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 159261411 1250 159260161 159260207
    0xd0305090a150f0213210305180307172a01090e0a060f0303050a031b0801090c0903050a0813060206061003050a0b030d020705180108190317090604020907 68
    0x402c00e10080303511001100d10001440c1549450341e02c0590708042d40c1e41c81860611a81001040700040300c81c14100300ea20341348103040c001e503078001e0200c0c000e2402d04504100341c2142c0080300d8500f00b140c1d5014104d40052041030800003050195194840c3c40b4003818100031000d904440324803002146200041612104111801e0070420024044018814440385d41c448200181052052041c107015600036501c3c6540c500383c5240207402d4079545000800d004001c850800e42e2283c0c401400b5043d00c010400124a00e00444030454440c2d245030409082401800249010029100c00400d0382e8446c031150812207955428003170b40c580c942129420b42082100c101e40e14294420760007940e0001c0f08000020f10a04510042807500030201d80d4000036038000c0302c3c00d025602d041a41701600c4a07685440d40320b40d60400103510b0303c450000d170303048a018958020800401d80500100c507442250480700044510b4501c0281383e9401040e90300303071f01032050302e00442d9045100720703007000c004010f1b800903003c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 159262661 1250 159261411 159261413
    0x912150e030d051302010f0e0f040b150d060302120712120c080a08070306120807020603040321090221030304021e060d1a0a0e0403120207170304050d0305090a 70
    0x4080d001050941145001c10000002000641c2c495140108810396100100d980c1074400944001c08010a200030b000456108003000c2c0e13104040b0081190342501c002c503903056444045200d48511200e24046440003044a049010700c80d40050101c80c000c03100e40342903180c1e05e004c0d242c41d0101070091031105200c0414041c0841c900038000b49420760a46009090064142c803500181e41210301c0782000200082d090002d0b01d945405490082d01c080801d0000260240e0f840c0c26007481151002409040d000c8001010b043c061003848104c004404031311014408810480c1006142144e0700300c0c030032a40c4545a075075242d42e00300740c000010301c540000e61840c1c035280c003081628140d010030030901043da00600409500c8110107031041c0314510038046400c4220504005807070008401c26400740002031010040c84200b02c50a5422540500f0480030f40021940c081c800f034442c4810140c45e0500b540901211a079005c1c00a5100f00c0c0102c064584004101000310300b83c4500b0f0b01c881c0b0301c561040c00100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 159263911 1250 159262661 159262703
    0x30f031009090b1302130204030f03030506030c0102070911120c0705060a060303080112050c120f0f0c240d02041202040518030f0d09050f07050901120305030f04021207150912 77
    0x720204d0000304900b0040380384808075011f980c02a0001c6a42111280c620300805030540215a040f01c1c041303024044201490000030340c0e840d0948a040c61a0392a2201c0100310074042d801c441a44010761201803071480e204440d18000e90008000300c1c0c00b40308240c0080c83c00800c03840b6840640c0e83c9a510261581d10340b02000b154110540c0040e2510301800b102e003203540d80c0b5405950509894071001e8032032844055409401c010205170100070507081803030200d200d036076000000d20101584c1d602001486010030008486401002403039483c4520010700030031566604040c0d098079920842d001c0c0700ba9524841c2da01c1d1a0302c15412040501e601c1413004a60005460000c0c10000006001c006880c10327440e00e8480c0b9000080d2160314881e0481d000510683c20b114001c14054610b42000c03010020b20ba550013400351000508840d203409800010504541e90a44194006a00c0d00c089a60480d140c03000c0460f80c0700c24551003004101071900c0059596902003905d4001500464035041800042000d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 159265161 1250 159263911 159263941
    0x906040b0a030e06010e0115230c0a0503070f060c110d0e190e06041d06010302010c0309030209090606010909090209040209100e040c0603290d060608030f031009090b 73
    0x98141a1103401142041c401000f11500030006d03e941c00a041d45000c1c0e12550300c513840590941080030250ba044040160a0703501c0e04007206200c0c40c070303503100c40010141e4101016030780000c1140c080010a181440107103101c4844070f60040e6400c10000801000648512040024a410310303000409281e0025010340c0414050388409401070828030880384290314419919080501d05030415400d004090605220b84d0302102c561001c214041841d05045941e80c14052100a040081d500301075010180b0400484000f0355010f0704152281c20086810754036401c089806d280000d00044000410001e2800786008464004c2d20001c96a00c980c0c0a010740c50300000e10040d400200600e00203440d018800a0901c42c41c01030b0001050503081c01d1008064072809101c840081e4500344540d005101000e604050103076045600401d40512881c01c50040c040c0d56006280c90b00010039850343d12500c4000841c4105104450b0744011900d070a80030040355804a00078107036270244030004044d00041d03514 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 159266411 1250 159265161 159265177
    0x1504030f030f0e100e0706050906180102010f1e0b01020313060318050a05030307021510120609023109030806060a0c0f030e1305010803090d0c0f24050906040b 70
    0x1052003040710700940c2c030b00301c5071340425502150344d2040f01030b001005218240140080c2c2c5821480c0520032000107501d402900d4034440616000310110300c150b03000354000c44000301415400d00440c408000000c0c03158dc3c60041e803246040c01c0c460500c106610100441d00441d4050804408950a000040300140b00b000521050940e00c5040702001c00c4041000803106803191008554901d00084001e0400000d81c2c0f640312000a8101805014805c0808a1054462078520700452800a04080c0d0280c2179078500a5040041302d10f1402403040f04002402801c402e82c42c2c00300c5413078140345000302129081c0901034001404440861446d14028000b88880d64041c50700b00340120351500e0385e4085200386a03044010030b5462465461500b801d035021042190b03c010304019561408042c40c0e142c1c40b0f90840305100703540411300035041020406500015040f4100b481c003d1548a8a000c100e10f2291002103107110b1a90b0041a0a24810022038000201c050029414240381c507000e1121500030243c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 159267661 1250 159266411 159266441
    0x10f06210c050a080d1e0507030c15060f05010311030f04030c02120106080d080901020909060103050a020d18020405060d1205130312180501050906030408090409050607020a051504030f03 82
    0x40002015607030b81400f40094215800030b804a00114003001d0402200c012200d803481911441c2d100c02c80340c002c801c0d01c4080c0d8140c240716000f07400d68680f142030070700b110f00c51000d020319040c070210320703041032201407000c1e03400c2031700c003004031900003a0070007818001212415030040380c40c00010000707441485a84003881c030180c12a404680540c0c3c0240c2541c005030805009a40948203094026500c01c01554111102e28021450814000003241e101d100060826041c140c84002141c525601a41181c80c00020105e0403c4841c202242901d402c14203150709030322890500020940615121101c000500e5000400b403ca41c3ca170084c05882c580c0021900426804050100201242240c003880485811540e64450100c1d100d000011581040340c210798104002480054482d0300e420707003265013140d0000c000503200ca0b000c00005014281526008200d0701414090016298000a00f010b900e441403058600844201d03c805030201030072a0082d0000d03680b0015203100b035000b81d04c18001403805e0a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 159268911 1250 159267661 159267683
    0x90503070b09010c180e0f07110304080703150b0303030708061c050a050706090602030a030f0e030a02070603050a020306010801120c0515091801050a031212050705030603010f0621 79
    0x9294840c104a0407240c00207240d44a0304110344c42c5504c00142200c0b1800c0b90700500340a42407900940e03a44030300900b40109129404d0124401324001c40203050490303200f00460740d6481d00c030080540c403442d0a2108441c20401000d045500714440c0c080e1044642028004606660b112141182c0c01e4001078441600135032014942c80040c180203841201660042005040142740b0385041480e101c500da10a000f0400405014400c036039000c0204da090207030524006c10b4104c02d0b40450002800b2070f2449500038880040c0c0f0441098020501e00202c1e12151010000d0b03541d00d08810041e0b1101711440c0d80003c1181c0d0041c030001c800825641d03582809400704510182e1180d011960488842c643d800c0f010b9004603003e442413600011200c54541880d000041c21b514003000700701079a03090300008080e0000050031085541c0320f407020003a01808040240507900f0910005080b03a03200b540c3d8039000e5420b240050000d090039000e03d208403215000f10131001301041c2103225080a401404a0703080c00a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 159270161 1250 159268911 159268913
    0x51008040f0c030f120206040507090c1404060e120f0a0210170f060f010c02031b01120f0f060e1501081308180a060809150709080607020a030e0105120a09050307 71
    0x5030700c2010f54030540b10343c507400915003442e00b030f04900507045a003103500c42c2d03007004002100031070f880085504000d13000c140b243c0b10241c16900d00704010b0f107102020001141c005039581d4440c00210204900b40d42c0d03110074502041c80c817510742608a0b04004941d010715600320060802016031284280940f1b03108070805520b80c5800b1100506a50a030080140907041c40000c0c904200ca590303500000b400c200c03491200356808242c0758591030210302c0181009040071111a401001c0c00c1d403030900c0d001c2d070401c852901050701e000240302c01d9aa01a41c180b4001002c280e0079180b010f0140a0a44c03100004240c80c0d0700703401102d058400603c40c0d404880d1200b48000000d8001c03024100d640361204c107110f822101c2c10306000c1d134141c2c1540072400b04001d01c0c0501200803008a40044c0c1130150358000c5940d40d89011007594005401d0340002c0a40c410304c1c00f0400030aa01290300d2000038400d648080b00c070802d0100441e00c0e030040708000090900d031800407983c10342040d400328800b13a2251090324284001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 159271411 1250 159270161 159270173
    0xe0a0b0c36030709090b01260313080723120c03030705030909060a0605040902070c030c080d030524010c0c0308070b0f09010203011503020d060803030106110601050307051008040f 79
    0x9503200c1007601c06111454000c2d16051001d10050801d03242c04100003080e0f1b84130110115810b21604007990041501100400d10b0100da403c442442c2008890703903110400c0c090140a501c0e8801c41200e03014110f00810400c0c00e15505008902e42500f030a184081e014080005c0920403449100081c8240400e5425135102440a0030f80c0b9400f5901031a15000140148401d00270020051131040c482e1034014444690080300355403d41f00440001610303000c003232500501c1c5008540020b88030624030007000494000c000341ea1491a040d5903014091a1200c090441c0001d0f00b980d4201400203540580c071071107512480303c1c03d94660061001d507001e16a030351a842c565500001c02070f01c0601441040260400d90901200d4004003600001c40c51076151281e204000c0c0b0302040301904040c0c0000344510300d04026044400600308410550703a9a595641d00684500c0d420704800d0034074010303280001032a180202d85002125000b6100412039040114111900c45c00180304442c0701d070208001d071020800d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 159272661 1250 159271411 159271477
    0xf2c040f06050f10270e0f0604150e180102040e0f040309120209040b0a0207020a090e010b01091406030408040f0b281e20060a0e0a0b0c 60
    0x80100d00000c1c0390341440c051160b0300b0b100300c20550144000150500d40190720034000d0411890404081000c0d44411007a88602006580040e182030020410300c040740600348902c0340100c00459040042c0c0700440c0c407414110509124100d0b904c02d5a900240c1ca5424003000d00d8900c00110700014a8a600c90381c60010540c0d0540301419600204400c1208054000c6100000303880003c4818001c40c60a5000030743d403c9000b840140f80c440c5140104018200302e8069500c1c0310f80c001c1520041d207464660000c0100804c01007140c1c15820015800500c1d40a50782c000140d50f50b00d080003a91a0400313050091950010b4030880c0c1078a000c010000c0da20501c883c1500103007981e40c418a58816040703c40540e6425104981002100d00310503c83d6043c1c0c020491401a1034030b50000c1d840d044007404103541c3c24000d9000d000c0d4010603803501038941400401c0462068003403030403c102034420080c00542e02da2003210010300b0102901c001c074024180b2000a000c0854041500108402685203c154a24 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 159273911 1250 159272661 159272681
    0x20c030a0f110102060f0a090212060703090204060510170c0909040807050601151b050f0a030306080105090705030a080d110c0d02010b060313031206050a0b040f060f2c04 75
    0x11160700c55100401200c07150555403240244024040e80c2030098403c5000a8058000a54181e80f003ea110031522131241641441604000b9510140f528580c041e0181046050480c8214900140804c13140741c14140f18409400654270a5441c10101d029038900700405032522503000d800b4001d80c01540d03106007216104500c1101340e02d40700d10803840e2030340c41d010043e000412407402c01c241034070015501014482d11005402940c4820200500706603003040c0c124144548a80207007480742c0141901a00f2440441e141180200300d03903036500c900203417590313054001c02cac0d4907402c0750740c3d800c01045070400a01100000340c9000640c801070002c001945074040440c030481742e00710711081d00002c4d030203205140e05640181e501c3e074614a8a5456000c86000072040281444000202907513141103c1d03000e00060b00e0301500c82e004298940d845c0c507900350010310850692a150b4074000c0740c00c41c843d61042064103011380354409146179141d010400f5010b450320300f0840d03940d1a40c030a07509644501031175002c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 159275161 1250 159273911 159273923
    0x8030c0f060c090f0d0201030f240b0f03010b130503011407080a0b0f0d1106031509011508010306090602220f06141209100f060e06010e0a15020c030a 66
    0x103169030048050401400074042c2500100500c049051610b80880c000700501c0c040360b03250714031003562005800030080c00d4002c04140c0e240240b06039500000c083c0c0c00240c2e1205000341c2010380daa03114015514131511100030000282840100400a1480041d1034202400c030402c2c0c40050721100400c0c00c4495140312520491a014140034440ea0041803c6400c42080001400400f100320302103a002c814a01103070340203281121089060200da04c03031804024400410440e5a400d18a0407091f014080340c00c4140f14854031f60000444d010000c40585280e030040e01d031000030741e10319260381e0010310031400d0544003e5020040d0350900100082d04800f04440108550102410000d070f41d03a2400e0283c00020a0090060602141119003070a03a003151b242c0b09181981ca5403200603450030003020522456856060041040516006810040503100c1c4003401d03010640da210b00450769101a1032120341c2010a440d010f001c0e40120034883c0b0078550180c0104c415416102000c640b4000341d01d90181c1d06 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 159276411 1250 159275161 159275173
    0xb0f010612060b090d020a0b07080702040f0203101512060e010303110607020703061104090903030e0705061c0507021c0507050610031509020f0604230909030a0e03100e01020901080702010216030c0c08030c 90
    0x131803a1510562400300c004000c1143003103161a602d0140031580c3c5000d140101e12800004c51f80c1c95200c3e40d180d00c4040c40825041c40455607548222500703060a01040740821250296000311180c0001c52071700c6041e20745d008118582c51501d41000804030380c640c00c0c044550412000c54685458028200410f100380d80000e0380980da0b600b0346007491015000a03100721402c03c942038003841604211000c2c020f42481c001056151840d0030f07860b01c41c2d6000d129994502d030386212005150000040d03d1000e02400c1a50b0190faa681d00b1103c440c030042c00001e0224031201c0106003841c8282e406214020b1000e010b080c8002c0c0d5a000186041c0c000d68040d0710b82086010003071410346102d6107941d402000a80d0405081e081c40d04441e0344a0203070b50081c0c000c00c030b5a01010f0b40140d504100145050848aa040082e0001c00d40401e01075440003080f9808284110b010500d000d00c14402c4910b204402a1a898160026502102c50401102d02542d01240c2c07400e01040c2036000b40300030a0840c0c03081c0d0003484 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 159277661 1250 159276411 159276413
    0x216060c21050c1018080c0a020a0b0a02010606031419060b0c070306110901140a020a020d0308040515060a06030b04020d0c0522150e0d0b0f010612060b090d020a0b070807 75
    0x100d06826841d0b4013900c1c504241a82c140d01c00380507014003115a104400c1902d4401c110340c114500020b641c4043d501909000b0001200b408000c000c201c202502d078024040e05072100010340903600304030030003500c1c4000c50b000600040a042c88202140181eaa004140140d403540160060340051101c0c204542002c2c070304004000b110305c148003440c440403042e0b070706007d11800040c1800118002d2000c4880c0e00140721011280f003444840c2c1215401000c4520803000d40c01c3c001e10005048138111054820032a2410007803d08a50041c85460010005800c03242002000c602400e0358840c0303260016003c1c030101d404e2400754091a030380105680e450a4603103508540385015001c441740720400980900f10140312404111101c064141d0072420318180b116081c2d8045a800a8018000b5040000390740511480344004104103040f14002c2d80cae00c801c540300d1504006c08032210f03441400030142c0208421170a41c1800300d20315109a0000308440080b0b662081821260f910aa4044942c0c0a00040d00c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 159278911 1250 159277661 159277663
    0x7050109050606102a0c180f0605090f160c0b01080604031b0c122a090c02010e0a060903110703050c130603030503040303111308010e0d0216060c21050c 67
    0x454034083d907240c83e40005004404980d10170001119280d80c03060420218000d02540d40340250040504460f028040071003814524000c03c02a1504200c06003400400a114a00084d1442c001c0540d1340038000c05480c2c4031001004505400131000c20310002c1d01e854000325000f180114001c019030f801400300341c41c1034500200300755101c8000c0c2030409805241807000c01e4690144030143c074203407140d175850442581003501140038040e070080d5018803642d40000310100c0b0305684600f1240201028058980903031020380c01e075590516010151b500441c3d5110108a0503003250401c18060f05051903c12030b25070205040045035041030351103038082c4030030384c1c5075040000e1141802d0322812401c105060443d90010602e1001410146c00c060f210415224120b919008a59801900c0011908680d42e01c51000b40600300341443d02005019803242d000c00c003400814400900340c507a0f000a40013600b00351054400b02c40e07441090f140301070032210604502400e06c50b00543e0b040103845d02d64442c52602c20303207 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 159280161 1250 159278911 159278929
    0x1e0f191d0f100312090909050102192c0a03050610210b01090203250e010801090e0d1101020c0d0e0906120705040b0402071b031e0c03060e010207050109050606 70
    0x7911810081108011500c0d620090710020380e0341c001c1c4541c0201055003c03c49a24210ba001000440c0c0703071200c0d80c0100501580200b901c41c04040031921811480c01c07003552a0011014100c002c0d40090380410340080c0d06980c1c001c0002001486a4401d54032912000d103401ca0455401d603d03038004d0001406644810f6045c1d030103100030107104c95101d40b01961401502c46042c80382c403e40170380100201c0e00d1b1613103420b01a1240441c03820512160800514018080311100c90314501007400e0038004585421203009844002030710000500300c001f0044012503075454006c0500380695801e019005d9004002e212111701c5540c2d55031023404888041c010060701140c0549007502c0b6078032000780c0c4d0b1400071002c0341141c210b03801210000b0301c0c500c2e1480420041d10074403000420001e0310200100c07a20500340c10b184e045c1c1c0c0c0217048500102421039681481560078501c041c1c60302071031100800003d074581e001451a02e0680d0009424524642e40b40350a44040080860700e41d0000001c125243c101b000c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 159281411 1250 159280161 159280171
    0x309070b0703020d080403170c0d0c03181103071e0302091513150503030705060a0507020a03051615050a05060f0604061b06061a04050f1e0f191d 64
    0x388a19105069070007954844100c090700c010b201a9100060515005049604041d0341d00c841030895450045010500380c1c1c000d24541801c1c51a100c4444c008034860711400003948520b05c000720342409c10741c448410207080a01c6040d490701c203484010400d082000c440b080c4040d102c60b40c035182c00d401c41c81040711603a401000d041008590010404041d035820070707100b07040f0740360517000501304500c0c440c2d9500e116000e822240d018400050f1500401100103075451040d815042c04200ca0380364810100d8440c2000240a00090030034000307940804502146205154881c0510056401c0010b90315010b0f114205c07008011030780c2d2182000b0481c1060f80010008a01c04c0350303503d00c0c16080000c090003083e4140c04140c984181d1040b024108a900d80c801c9003e04081703000504455000785080d009907100d4003031a4080c505061501e440303410038000f4112103046450302103400754004400d000360103056050f0356900180c0c00c4403600401d46018040009000022200100b1041c080c03c40d08400c94081c1c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 159282661 1250 159281411 159281429
    0x219021506060a05030a09020310020a0908060705030f010e0619060c030306051912020411070f11010903030e0603100b031905010b0c060601050705010609110417010b090c0a050409020f030907 84
    0x601c3e02c0c8140d100040380d0348000681e5000807184058004030745081d03000f040681c140c0b480082e01d10000d9810006140c100c03203010f021074003150f8540d201164180815260300f00445100c070014020b2040c036041540d84001c0140c42e00101c0c1010b00304404500041da40003102089403500e00a0502d80d140c003820020741000c0e184200c07100c2d242d0000d81d82200d12881002c00040813032036003000310f40e19a08a4102003050402d5036848206500700154071103651402114692907943c54404079500440d001e1040742d0300364030703441c281000c0841881010340c401402e0b1040e1441c3d2210101d400e6009001035402907460221540d916a0000703100801c03100181c0188460310340a0089844800c070016010b0760043e001c1c81c0c0551a01d4180c50120301410302d070b40062542d9400c00c002c202155070f050028104403401c0b017801581294003426464229024030741942e800440190000740074044070801002550468905645023503950051641240c000e0008210105400420302c9491a404c002c0c5d403001c0d001f012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 159283911 1250 159282661 159282667
    0x10e1c0e030a02031f0b0d141b010801060309030c1b0f0f030b04060b1207090504021e0d110607060501090b03121314041e0504120c030e040f021902150606 68
    0x1800180d5262014001d801d0400001c80180001505607008011840703030190110b12201c01f5032800e41e0400e206202c4009180c40381c5a80303021000b0420360744000c404410f07100c03071543d6400c150085000c2c11020000b5401d01c0901c82a10002030900052031001002252407060124100059440310500301e030302c440c4540301c0252041c80422152411a0703000b503485440081c24030f843c003010a44078154040310034214000ca40c40010390348016042244200d10032900589440d072184090601e0344e09840c403864000c20b01030000702c00a01a00007881c2e0101f00204454244507465641e42c013520402d07004420340545600100182d82820405401807601c0c10610a0410005411441c504c0000344514644550844000219500d699002c01d03d619801c3c409504150905151040906401da608607500c00c501e5000040007031060b12031a030a03941c160b40301800c04c0084c0040002810f030485440d6034a030ba00308070080c002140c00e802d00c2c000226075000780106618413012707403814007001044240100030070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 159285161 1250 159283911 159283913
    0x6040f06050c040321180602060f070809030d0b01030b03370b0a050402040204090603030f1e14030a06120b010f0b0906040504020a0201060b0f0c0f03070201020a0b09010e1c0e030a 79
    0x6104030b0300c00c0300b08500342e000030b40b05d002608a40c550f014404000032000c01c90008241280d02003282880746015456001450f03d549001321141c100840b00f0800581040c026510341007419004008151414580410301c684804c0000741040788007000c02100e280c00c21007030f1301000807860410121500c809001c07100b172000d41c2c59503d02d001005141011040d9074400180455640394151000740601c0c0303800304100c907164500907000f04c1076100e528000c030f803580310740d44000700d02d0070714000c450440e550b0380d10542211040b030002e26030006080d2401035038271000081005004c0c40c05c25040e030b5000e0100342a0035450008500d1020b5480c3c3c0100703040000401440710710b0b482d850111021204103403030041e5a456901012401841e04d40c005d503e084100288031443c18165002508088c2e1411060727072400d4007150072590f600e204240d8024056000985120003080703856104642c0000c1410000c035800700b00e080c0b05070400c0b170804403003089805510b140f410040d40c800f001140590058006001c05840c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 159286411 1250 159285161 159285173
    0xa080105030111090904050f030d02090306060a0308180d02040c090e07090608070f170c09130608191a07050a170405060a0c090f140103051b0313060e06040f06050c0403 74
    0x44e06030b80500650301100401e00300701c420810300c0c1000090f40c0680c1e441f82c0c1600d400310040d610882c101d41c070074401c1c8000708416290000140040b294404402840c002c10070080c1c5c0745040a20395a0340e41300b50401104030250311140210200c9a230165903014105040210b840600c8001070b01c09030412101d81400c0c459250031030185e81d0043e6241c04c106c840d125141000300d484849a108140c0144001c005025040c80c0708005450540f03c121403562503109806907a10444131644141d112030780c40f014010803062842d2603010103031400303103010b944021b211515022850300c083e12440c002413030000f12000803a60140d4441c80380042c101b9405020b081c180c45a40c4d9901e0050200c0b0003090340c4440c880d5000e030007842c00c000240200b9841d48038041d5030b0000648540719801004c0d010a0600d40001d043c02000c443c0010b50201041c1440d0460301c410160000c0c03240c090380111a00c517070b02d12014680103401c1180c0ba100f203120341100406a240c92400205565018001c4018400248414400210 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 159287661 1250 159286411 159286417
    0xc060c050a03031a030a06152709050f030708090108010504090b0f2205030c0d030501060c080c0304031509051b010e0d0c05150711100509040b190b0a080105030111 72
    0x2c0c25240106036407180c030782004034104654001d10f606204035420304041220b1500010340007411984030140032580c03900b654180e8502d00c2e0f001d01840c0842c4c8461040d405603a4440100140a002155000004040ca840c6103070301006003540c00f4200443d243d24650390001000d400343c0400c1d1000e02180d9101c0da12071310b1000c0003502480c1c640741c26030300040480080c01802d0303200012508164051151501740283c03254008030890829018400050729418080e000d000e040312071a5a683c84030306444d4607048250b410561040032540010000040404d1080800070452500500c00061003601d0b8a040f510f411954605401d8084810405e031166a800145c4581468821750783d66100c078030640380003a0740406580049520210801240c1358000c4100080d100c06d9201e030b03051400741030b24202007141450b640e00c411b90009000700003458890401d6081103400c074002034007284200c05003002d4001500c0c1140c001c18403d01022030407200d0b0360703801071805004190030f07002044000008140550701e48 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 159288911 1250 159287661 159287663
    0xc09090106200111070209060d0507090603060e070302031e0111030a0f0b010f080a0e07030501050703051014030c04020d0e070b090a0506030f01030803040512180f011815020a02040f05040c060c050a 87
    0x7c1402c10001d00c1545852000201c010b42c08010b40303080d1616134a00600030811070106a446c2da11705403004500d031000150300c90030349070000e0081400c03090700c04101c040b5221000000c0f4455403914442035282c1c50a1021f54001c603400c43c80450700304081c840c0401116202c41089040050000524018941060006410100407107010850030740c1e595215182c04040e41c0014469031070a0100130100390300d5488a030007100300d003c0040304555070341d4128000d82c07107036155142c0c55004010088802c1c136081c0e00828542c803a926011510031100040e031420b1007102d600104290f4000034500529103011104075014103001c80f6200e00b54100103030080800c0c0f40500006000c00b4000020400f402400c2282d6510000d039500c84643c2d4103250060b40c01610070300342100b4003403856650742904a40c002c8000e80c0c2d43c4400c610381403040b180b50009050065030407503180400c1d4014040c0c8580913031618090310f0002c4041c580c0110b030b20f00303003403520300c00910040d808041006200070130781000850106160b1800c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 159290161 1250 159288911 159288919
    0xa2408071422110705120310170304061b050a0b0103060606112104030c09140f0103020306040f0c120615050306010803041503060504020414040c020c03030d050c090901062001110702 80
    0x60401030422070f403c0c0c400c1640c050001c2c400c8500c0710f010745442a005521940c503d0280454950b504c0c0b00d0a200c11041203850300550b0024042030000e1441a6680400140f4070207207045402c3c1e0503102c180c00c1c0380c2c080380252035244d403840041c410b00c8114005c6400070708007842c204401c41d20303061104c2c2d240d440c00740c603100925511582c2404842a02d40684010b1a000080030040591f5100c003c0002d1810310b428a00b414054070000700044030385840c884c12260060042c1505a5031035517110b9031800d070008211225805694003203403101440300b40048580c03081030000748140300f078000240190045d0740058440ea100c000140402c09002c02070382c0440c2c5040480c0c1c0345006003108142d002c3c04c1507401040c3c001d8800708000607144d00c01d0741829141241070328100b0007180d000c00100c0c1c0b00c44051400d5501540100041c130071288113940015804881400c040f0f06098048000540c1d00e80280e120f0300000300c82d0341303400441d40244012241841802c070020001003421b50410b040740d018199000e845 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 159291411 1250 159290161 159290171
    0x60c090f0f06040801020a120b03030703050f07140303070f020f1b010c0311100603020f2b03020304050d030c021008070c110f0a060f140c03030a2408071422 69
    0x225442d08000d58018140341e4000b59150101c080c0c00800c1c0b080d0010310044101c1c02e0180b40c1c013250501100b01c270100c80c0c050fa5802d20740054102003461550104100303d0309074101e0a0042c10703009043c0040c5004450b55640c51002c1192084000e141c003480806032403103504286081c4041a0760402500d428980a0030201050012414107498005040c03001e685c03203000b00740400c0a030311450303400441036920032a200d003000e00142c010b102c20b02c400030301c0d0983d41c0302c4000c0e40010f21444101c5c68030b070410310900c12249420745541c08901148050703070341140030580381c460034011880c1000b02c0d19400340d090f1800c00500d24081e2002800408030385006009103a00040c0703044c007a15000020100c000c0040c0000030740c1d5690700700c0105111611900040090900f040161880103040c0c11940f41600c107a00031411038444144110081c070921500f80c1006405012505100c00c6814640d4000c2440fa030180c90303202d1500b5030607a48003203c5021284280c0c1e40840000c0701004041110039003c10079072000138 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 159292661 1250 159291411 159291439
    0x7080607080c0c0d02060103020103060b120a0b120a0602092b080a110d120e0304060e09060607021503010503060a020702130504140a08040f1a030f100f0e09060c090f 73
    0x2c0c191048a4034400d140c084e00d01c0b2100f1440d000920281240e100b80c2c1c0c10400c4039560080740e00c041c0150310844166010490105c0d070022139980003405024402091281c89441c030380101440c0c542100d904885003a00410224502d10b040e107090f2040c44c5030102da030002c2c0d03074464059440280300245c00403c401c030003061b00141148036026003035042509400f03c1c1e0212540a002504030310081c0003d0445608028403840b0111001c81602d080785c04c5502ea901042a991040200801c801800703d03402110521600d00981c0d83c880d01c07100c16034100080c084d6254140420b150401e03800a003e01c2225004105440040e103600844100001034460002883d0b11981380050900381d881c3c50021070b41c49124020341c24071004000400c00c58420380c01201368299190040d00c4034120385442652950401d20010b0000100d0b812072940c131903201d60405200644034800b800d0680700940054002c040c9610820200440030400650031078100b154803410591428001460b1208036080503000d069001d0b4902 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 159293911 1250 159292661 159292681
    0x8010b07060b090108060901050702120a03020f0f0f07030810030b06060703020718020c0105060a0b0a1407050a0c050306130215090316030f0b0a0203010e0a020901052b0e0708060708 80
    0xca00e040c0081207030b00d280d6900d0f4200c5a0b28041a180c01007e54a00750102e41071074000500911600d0300c10040c41d09243c4c010606600a4005054400c0040401c0140215450082c00141107008400000c252101020b0500800000e001884400c076024052000c1c004201c1e84907203031707a10150465446503036a4207890200d040c0080c650103084801c160038031179071100e24690007070f00c8443e4000000700710baa5582400c02c40c940849100300c03001114100820a60301d4032031407003174034034000076025a440c18045685980c0b4102d803094007924020fa00038000d00c8a843c0074821640c1042101544c0031400381603400240c2840220805007901400008401c5161344041c0640100501c03400140c501c40d07662810182c40e065400d4800721801c54030f010008801000b2407094038103884131343c890300c200d503600d851108009500507550641480400d000652035406007184c480c3d00e03030802a085400d0100c066039500d0540d10f10344c03040c25594100700c40c1480000d40c0015a50381c003a0780d40c03605105648499040c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 159295161 1250 159293911 159293921
    0x70f02010c0203061005100c020d020105030711060a0501030308090c030714030c091f050d030905010804170a09050306090a1509110d05010912030501080c101e020a110607020108010b0706 82
    0x9403d4040e10303080002100d484018442100c1d42a034035007131400034181c02103a09030000c000007548450304403482005944148003441c1d0000031303030030300c151205d00121102d85005003c0703d0446189880300d00602c20154481301c4240c100f40013000415400d40e00400180d142c11981c000d854521000242481c40d5503010051038592940140940f002810126102020b8508011072200304007084100000c6504280901090241d01a0340300300810707040000455030182c01820507034141c0089903034850b0906100009084603181030310344000c1a4901014181411401003005c010340d00042500340210b100c140d044003120010080004150b004c1d850840032086a001880d600000b00b00c0007501005415401694101c2c002c2e0a00201141d880004906070b4500b4001c0e0491030708440c01501c1c1070b013021500c152003407540c0d0802051180368a8407a000b050181c0010350010703480000746a09112115102d014890000c1c0c5003545000880e800190010006104024000000140c560240b02d001d0b404 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 159296411 1250 159295161 159295163
    0x60f07030b1009091104050603160201060e0f061906020312090703141006090203061c1502130303080a0c02031e040902030403120b0a0e0105190e09030a0f02060c070f02010c 76
    0xe1140381e41d10b24100140190441c0c05280340366840c1c000c10304100d40f900000d5500700c074401001a4030310380d00c003140780500c0c49101500c8003d40d900c03664041954001410035074882d0700359072811b041e61301d407900420030f50155110b495004d90418400a0007540d40c00f108852103c2d00700d01c1c0144241c1c4803001018944000342c0d1001c2c0085c010302d100b002d100303c8003203042c2d0320203000035800340300c031944070307100d02003280300948602e548030741d24001401040080c01d03c0501c01368011211561103501800d44c040599100c1d103030070f400011300068140b0405d40c22401c003503007019102004002030741c01e1042c0a952441040c05003042040702c0c0882902e00c2d41144111005410840c409644a0501d4900540711220b010f89114115003489402035041c28210165030469591341054011646040b082c03009030741c205c1006100014a01801041942e501494103004031121070065640f01d910305001000c11041145507400c540048041c040c2d51182003050341c107002e400c14194030701c035074491006a804034040c0c10 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 159297661 1250 159296411 159296419
    0xc110103021612020f1e030702011202130305060105010908030708031807030c091d0a03020703080901030605030613061b170a14100f080a0c17010b0603090109050d030b03060f07030b 80
    0x5000d50304550f011030a4000c0084000881c0e002507140ca0a64601b481440e190040d10b6000f4007101016601c24582403002c9018240f00600d0204c1c041008628180c00e42c0066800c0e902103401000030b968030158030001842944055801c18000b071f6181e004502c409009919010a00e800440800c64148491002982e0000c064041c0c199940520f001402c01400e600c1c00340c0e000c03542c2180b14454041002000c1d079034154040c2088900f1903071944541e40000c00c156041560311000419251010040c0d18050809100c2ca440700400320700d0321000740d40d0305445014082c1101d01d8203c42e2103800c8522079461881f8000c12525030b5960064039002028001c041000d000100e0040c0701e0303078640301070780ca40650384034240c0f82e14000c0d156040240d0300d4541e460000d1034040352000411202d00ea412a81c40c0348407203500080791200c0000000ae40517001038614581036503580c96144c0c00c001c0c003080004e0900d906400c0c240202c00701d040c0003c0c0c88440081c54100d09400480020707240c1407095000c51a1140020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 159298911 1250 159297661 159297683
    0x90603200f060d14010501140a080702031c0b0a05041b081e0103061d0607050d050603030d020a120e0a12080604090605070e1905060304080a1e030e0606010c1101030216 74
    0x4406130001c40c0c40080081c4d40d00001180d954450a08d4010384060004820f00e0524410710440f080c0794020000c504600043c400c3ca03034078001e00721021500509450010541448410070817504103210341c0318903c540d1429031450407d07117048080c00214492410b00c18101c2d0313204000c810344401c8440804100d1942c11001004000217a8000086150201e001c080741940d4221880e0b40d401301a00d04001248050002c2e00d144007640d0090f9510034006001d032400c000303a0344920f8040c2c0e00074104a101003900d4440007050b60800748541c1b2000c1403000010801020551258005417810700710705810000c40c0301c009100341e16250040c041c91b951001e401c1046113407091004228060040450348510031980174080104198103102c002e841008101c01d00e142c480340c1e02e1402e1075200041c503078107108001550420742e01c03001119100104942d10041006001001c1440c10850001c0c852814864244034400100f40c2e840000750b0021002e00b0016681c00503550031840d520b030400780c001c002e84415 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 159300161 1250 159298911 159298927
    0xa030804051005160f0311090d0206040503010f021905040f053d02010f021228020f09010306050904050604030e0315010815160f03090809041a0a090603200f06 70
    0xd04082c41030352130395079901466071001c04001c41c141d900b6803804e00c01d120818009100d2a151031004101501d00c0148003d2400759075401290039590b818085003c1954007207101e140407100c1d0b403695004603c09280c194901401e09503400c80c000d9060181c1400745504115440a25150a1030341c9400c1c404012001c0b0702090400c0103044441d4000d00396001542403d00106078141c0071b0096a20300b50032039a8101407a514040ba9000460a10300005038421082281481c441e0303062008080803912081e1003a625004a0000750580c0c102e40c0c0b041e80039010700c600b0800498008100305400c02c0d410314020b54001390002c006031410049104441c050314001e400065030741070004408817500702c425480e452300c0e83d6804c0e9155521011991581c081405200fa15840c01e02c40d5203c500458811581c1c00e043c02800c902040442d0841ca0103c004c1072301003540c2031981d141c45050074006141c03c2c1070501c400e90a60390b0307030b40026150b1054070780448005551181c2c1039481400d06800b4100c0505116151807036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 159301411 1250 159300161 159300181
    0x515060c0f1006080a30081e07020d030b04060b1809090706020d181703070506010e0c040603090f0b0f1506030c16110306090106061205090a030804051005 68
    0x4110004000d20074030145180607901d034003c010490704104003400c000300032a2219500e81118951002c24003049403500d11200e040703000b070300300017070b4995031100840c0c64850351890110b0070303511708031034140302c46401c0203101a80000c4424010f9402d160115008074004080b0300580340c0303900310440c60140410b49455a009c0000182c100034422100a0190f89aa480c0c0b55100c5000b40646801a04500e2000c5035a602450303840200d543e0b4420004d03130950380c4680c1e5040800002000541c1508009170960622100304445805400b0207003241c6641d082514205905115a00c1901c040c551980c4020082c044a5400700170480d40020280036189000c8150101c5803500316521200d080d1448200b50f054202001604d00c01c01161807054601140c1c103200c542200817405080b9562000700c1c1540013a510280902e03401680150000b00303400e07080c100041c3c0148074840041204600e40000c0180080002401410b0546c16081c400c01036281c5040030b80c10301019815030b070744642c1010103004604803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 159302661 1250 159301411 159301423
    0x2a010909050c0c0709060b040501081302060301060f021b01082a1b070b0c03030a090204180b07030c140403030311040806010b071202061003080a031e060801200d0515060c 75
    0xe850f0043d00c08503500c07210f000b41100c0d078502940009a900740411704c115409103007000c0d0050722154006c402841245d002610a52098218000080071314201954840e01040941002c00610560301c070880780340d20009090940003020101d145c01218250726071040d0306041002c131681000e15003035440c20a00c00c240ca05280140481026224588001500c4d82c200c0342a07070390b10701e202809175185442d0703102d10b1000780c03010381e8040c0da00c40c2c7d99035a060420a5804000d10080d4410201900c5915041001404807807296190905100001c10b0b1000c20554800880741980d905050005e2a007a508610b01158012504400c0c414854240045000701d808005854058460f0199100805001c6012a11000d0a5540ca4184800120705200046000000d80b51a502d035290001e2024240d10b032622004802482c02c0540035070368031080c40524028000c00b248450070b075a01e44141d0740c0c000040710641c1700d6082030700d0b03507140c0d100e002c40c51041a500e85403040000040c41551075150741c80c4007a440f02c3c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 159303911 1250 159302661 159302677
    0x30712060906080706050a0e0d02042d0e030a08010e07050405030a0b010f0b09011b1407060e03060603010902060f031003020904050313090e0c0d050705040510090606022a010909050c 80
    0x100c1841d50000d0201d00c1b42c0c040b200103504558402080502e88824031201d001b541301c04a0740540c543d01c10a201d0051248801d5014081603812200360a80c0c001f00400c440c500304401301960800c001d8211010340100079541100d40c1601403c015a4a06008449900498100950502855018005020405c014207050f2044004c001c0b050741c7d501c0e0031101241c820304079540d011032020840d41100c251020241075015002d2182d50041c0040c0784000382c10924590010f50200d906c1c2120100306007410040c0d5988100190003c1049032074035000505a40644801700b2102c0788000000fa214511450603407004550180900009040500d0219169042103040c500f0b20300300c01500080040b0b0138001c04902400c0403015054543c0c1040900c04915280082607900341b15030440000e0684a41c0314561180c828980d18041c01ca081820480644106074031010441d44480c035400c1c1070140d400010028003040382e000071010b10340300380180c5650f205544413100c0030340741c442000b440400410091100f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 159305161 1250 159303911 159303913
    0xc070b03010905130f03210c020a05010e060103050a020910030501060905041101080c03060d0501270210020d0818101a0f0d2102100c1706060306030604020603071206090608 76
    0x3903030302c2d200b240740c4c0c03c02c207403d000d06100290b00303c00c80400c0c01100c103215264002001d10041050000c2c15406031005c500b200d000580c40180d1700c5060103800c2c82484803109030040642155491511800d5440701e9020003c0c0c0309030f100d0808140f25018040e40071004580c044000c0c05040d5444840200030442144c060310844a80b540311400303503100d6203405104a408003441421900c0321418003510400c12241110990750741c4045081d00d60903205a4041c18480c0040c5264550442c41400796441d022020401550700c04500840c0081d008440c035607102c041e401c1d80c1000903040401d6146003248041010385041c0c6443e0020341d4000d41060030111040742580c02d0701c5004040014401c1002a0b20000350840c24140b2841c0041d41e03003022508000711561040b00c114038400003156007260309022404000c10450b200a10066017609501544040121101401d501e02a004242c4641000b80001d100314000000900018050814040d0852841c60100900354454922000904050092490f9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 159306411 1250 159305161 159305171
    0x2e0305010e0603010b0117180a0804030201090b0c0c010c02061c0603060b060a0503160c0812090c0103050c0a0309061116060f0504120c031e0503060f0105040f0e0406020c070b030109 80
    0x250f06050140300c501e001c2c10707960f496245214800c0040302c044050100b44000203500200e525145040051228045c060200c3c03607555480e6200140c000040c80d0300040c4004024055000845400f2901c1c12601c502800c10900c0c1d0b10759840050050b100d5100008148001d4000c9400940c003a40d101d00d00340c1c2d205220420031000740d02c0811030180a40c5103500001081000024a8000368004041040413103007084000b18025903580456500126408178107000100c0030481020410040d100286c40d0a0038104194207000d402c0ca421840b58040400074142c907108408100304003a404849258990307500030f620b50240071101d860a40c0740d0003041e280241070003243c115440f00740c85440d01071580454001404030460005450b9038501400070703806e0000014400c90181407007540c0f00107214046d510030b983c0b0700c0c3c403404001d040318010444030304021007440240101d481c0e00e58083c00b1361310f0010b201c4201d0341d12031909801a1140103400301c0b007400341040001d94100740c2d0f400345059030404402480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 159307661 1250 159306411 159306421
    0x20304110a0f030f0f060203280921020705031b01230913020f0706020304030f0215010b0c03160b01050901230103090f02033310052e0305010e 63
    0x1800111501490032100c60b4204100005511810002c5805201d0710111021402e00e840c0c0108031307002180d03041110680340440c90340001c1ca0321541003031810403150401060765280c40d1a00c820200740d0310910700b00720800042c258240200044002800010200e4130781c0106082014a5401c800c11044d005c00d2025204a05800f1503200c0718102c1c1e400c4800341800c00810104014030025043e4484650550030081c00044d8004000100f4102d801404003598174205460000c014148240784401150040300382016802a0706000b181103e00003014580c54007501180942940301d1844a01a000341029240d800c10003006d408a04079482128507403e560ba031140c428446200c40441c070451881c40002013013042d80290b0103002d105000d0145c1c00c80913a501d60202c0d01e80402000b013907400107006501d40c10002c10402031001c40b01c80d985c4a0b8030060810460240b1440000d004180c800c40161080301c065640710360312800c82d0201c0d07401848604a800b04060000d040078004c42c0d6030440c82800040e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 159308911 1250 159307661 159307669
    0x2090a0f0504032c031c12020a0512060315040b0709050a0801050403020106050303040f030209190e010f05060114030f0903160c0807060c0203061609090623030114040b0601050f0d02030411 83
    0x4a0718070000345c05003a08140c4603501028540f15618400b041c0952056040d240c01920b10241110003180d44855540f070303480e500c2c2421103980003010b0714443e61142e25121009a0703440c030142e40065014044642c0394031000300940f80068540c101e140c02000441c0c0c00102640c0541000740598042c1d0020004a6198018140c9030322450140d40c80c01130300c8050070001818040b035182c1c1d000803007c410003080840c075a041016990410281c0550780e444407a6001050114403540c0d0700102c003400c2400501203040e0303210445010081400941d802140c00003161078605000b183c00303002c070b0001318801074500c0d4500350b20106040d000c0e144952054041c08030b482c0c0e00a814001c4003640081c020300403a503c00983d920444d20000d003000c2000b445840008800c82c02d03000b01000b41064500840c2c61034030080a109d10042202403080c40790781400c04031a140840e001c9480c0e041500100c80c0e607601e545400c010388182c0300d8606580311044000076410b5400ca800d40c05180628445d110001e11000c03114204 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 159310161 1250 159308911 159308987
    0x12091206090d0f0201021c0c09080309012102040e040b010e0105010905090a0f060b0427050f07230703030501080c031b1012111c09080702090a0f050403 67
    0x1507142e01800311004118059080002c0c035400c1d9200240c0307003501010f01e0a11a16810800c0c1030a1502c8110500e64030303400120010280044000079070606800200007001113602808800d9003e001c0b20400c1d800c12403c0c0c04550250428540f014101d0030145419803000400340b140604200c01c0400201e6a0361041c1c0d0000c0458030003d11840309501c0b00c80c10800104480ca52400e111039459400103465221540940014a07500e07403890301c07080083d010350054641000071700c80b1180c608401c0013500525010403e40190a520b4408643c0183c0c00d00999101c034000c007001110400130694504060b4560040c44c140c50b202001d480d01c4840d013000307050361200b60001003200825003004a81c05030800e0302068612040c0c3d8900700180c02c1a80314075504607a0959003044110400051103842e03c9200d0301c85950074000340307030300304405040368032040441d01601341c0c020700c150211008140e900145070441080100c4080301009141020310b00038002c002c1e4600144d9030022103480704080d03107140860b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 159311411 1250 159310161 159310171
    0x6050304200f0f040b0306190c030203060a0e1902040806011703070b0414070306020f0d110703020705040c090806070f0e01020a03090510020111030c0309100e03070209100812091206 80
    0x10b109000c80e800800489482c0c62107103e4000e0780d00d180440b9103a4007080442d0081e05030b10100d6010000800002c010b40c2c003040d5055042c140100305206c8191610040c0324111069841c0c9450640c0b41c040600385000204140000054004540401c0c0c501011031003a040320b8070100304080030b492048000d0345038003c105000e801c5613580400200460750311101c55034160420015904000e880f5030740c2c54107e0704005030303003020700c1008107220004544030b1207a44201c0c0031582e003060803c0343c640c0d0000d42d039005901401d8020780d00d44040681c1c590007520407070068115141075885500e4100170003010030886106820020f0081c00c08600e4550010810101c0d151300340d901c02c0c0da090f040c0700500c0499507400d1100c200b15940c07400140216802040910b004441c0a8a101e5480c01c0600e80b6601d4a06054000d048152900e220768440c0d0030000110359040d0350581c1c4030541d0355100b0302142040b02c003580c440e00e428020303060107402800c0d440c401401c0f8904100e80540217001d00d1070459690701000c8603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 159312661 1250 159311411 159311419
    0x31608010c0804200f10020705030d02061311150f090301050c0f070f0f0501020a02150105041415031006080d03050c041208030a0b0d0b0a05250e030304030b010605030420 75
    0x1c1d42c440819030542c4040140e201074200581c0329240740100303001b03d1801c0080b800680214000f80f0162500f8405000c42c6021880144a00c0c1842c075003070310001210601c020701900300303150035441d1a1180c0c4400003101946508294442c9040003801c0f1a990000c5038031417095281a00040c40301c0c1c504d40036580035086c200e4400f800e101765030b96503003c510903108040d2000481d00380c00c2800a17209000419244c100b59014001c030525400c0440c03840038060b00014421818100030100e144000c0c000d40798010070382c6429007440200300c4040703802d00050900c040d417103038101980031031986000540200401c4c04c554040045558424401a15000300c0c0151080001600035041c042104440510b4220740c201c080016114552130000308108034900d412100c20b2507034410001120780c5c42c41500e600c411940405e0100d0284401c031700b102c07001d4010400c8240100070101032981e803010401e940c00755034001a6010156103940c800307800394100701c800300e4001b007912482000039410308440214244010b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 159313911 1250 159312661 159312683
    0x30c03030e04060b220b0f19030e0606152a0c030f0307030c0201090b0304030309020405130507060503090a0c0f1a040602070315020715091101030c05030a0c030b031608010c0804 78
    0x1424100c061070920003500007082c041c0001281422494001f070100c03104400c081c0c0d680303030700d50541d0701a503e00043c1c941c0305061500703040300c1c1c080741c010464640c006000c8840c5543e40324114030b0704890b800b50480761403004690280320b0ba051441003181381c07031020aa8013107030b400d100045c081640c2c030498800b28003c2c0740c20034440e150001c1c0c054010408143d10505200c0305070b944070003c00341c8640089a06900003901e6085030020760502d4440e458202c035030528442500301d410388030150b4a042a119150030803a0000015210043c01d00101140759030011694009543c0c2e03030421013400071580560710301107400108105070121800100c7d01200c0c515009082404d00d035444011076120341c0000100e0480c1c0801400f07000a08100c00c2880000c14500300055110040c28034014502091415a040c50701d051006007020390004140c99200a80e00320104c0d040380b003010b08030080c00b008501d0580521078024043c0310b602801c90008182c1c2c0740080208800c01d558107080300d25440981d00a00b05085e50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 159315161 1250 159313911 159313927
    0x807120c0308032d070f0305040807020f0f12010501030213091203050910090302030d06080c2101090c030308160201020a05040b1b030d0e010612030516050a020604030c03030e04060b 80
    0x102c009960320000144058001000f56500c485400c801c180b08119142c4460301000201904440d40350511762951808211a00d0159120211807242d1840030f4800d0b6041901032440c1d603209031a11802920140840040660043c0b410707001e808203000480c401c2c2d240c62021042e0f14014030840c0c0789541c0120b10294021042c400580080070040c200c0c0c40700380135249411000400500550622601c654010760359444012520011aa01d41c2c1000b5402e401c030035040b00142c0e482d01c2c4940a41040d4441c0004050f840c1511180100044c2c040140485081400001415000719015201d0681001c607991800f00203c030032401c0b882419080004520f041c401032040c29030841c06001245001e144412110003000c2e4100e1a60f08420b0071101c07119290103204c2c1d03540e0b8003805850006d0000c12000c0031100010354000d010780c01103544448000c02107a039920b09100c8100080d03880d9540140203191f0b100e4980c00c2c9045030f814507000680c00702d04000100d0070b031410580b10710800c440102d1541400d00c542c0e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 159316411 1250 159315161 159315173
    0x10c02070302011d0405070815041e0209041508070323060c0702130609050105010e0a0f03020607080712050a0305090a0b0a020a0207090e1b03061005040209040204090c090807120c03 80
    0x8482d4240700d44c154003000b03485191241d1046600419980c0c071030340c03158500f0f00c40c402c00c29960091200d0007203003405100b80c0d811901541d00c031810850120007585903801080072800170005602d80070103041c0c1e035407400035059001164550980380942c4041d400d0040488402007035550404198909a01503c000b50404c113042024002c95880204131003034038014440c0000c15940d2540015400c1a0b403100100700940c0c111041c050100b20030340f5101c41041c90300d103001032460100d00c000b2b40201030019040c02001582022990001e41c0100d0304d80c514800344c5070042c0300307410100103680413924010200c1d08035140024560195a0b0204170072003180e43d210384120183d042103102c04254410030001107502d0402c0d0003803420050400c402042419803100e4000a02a55a2252800b0350840401e00c20942085205001510426100941d4480e800b401242c02803003241d1065200074a01000075207080e5008017900700b104e0009049840703094544010410200d400b001c01000d41c00780f68010400988 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 159317661 1250 159316411 159316427
    0x60c0304050d15021206090a0606050904050901060b0403050604150e0a110102070f24080c1b03071a04170c030d2316021b010c030305060415121103010c0207030201 72
    0x8410001e941001c42e10102039000c4e070700711000e11202c0b03014007010041d043c181280c0440d4003025849007840b985107082c402500302e1045050082c0140d8440001402e800025040b1100401c07c2503003065586a99062150701c44000741e400b16030707443c1248155200e1110a0040e80e01f040e10340c1024040d00100d43c3d903034041320344041000a055015111000580c00c00d030b07504906c02850562018289582c80711410002c8000c1d40640c1c90a0010a03c244a00e05051030251078005121882009601900280c90351441c09042320003010341a030904c0702c3c4c5100480c3c0032103d011304d00c00c2e0386072141301d031700307603e40c050039010399440008154820310102e84c4801d0990000410349035450f1030940000010003e010311200c0031251403109014201d0421030079681002119440301008002039102c2000707c0000b0061010418090101500e8601082d45d6030f0f1560b03c11444590384000c95201546c1d5401c191130880c80302041510054a03c041c2041c4504060203410502074081d80909101800e56005440080c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 159318911 1250 159317661 159317663
    0x250f030f090206030601030209211b0402070b06060d0f1a13140a1104030203070e060307060908120d0e07060f14040b030115110a030201050604180b04200d060207060b060c0304050d 79
    0xc1040d104540d42b11003003c0c9a413001e00611006e001e080c102e110340070500f00000176655001703a20421500e00070a5030b201c0036682052040302c1c41980c640f4000b0070038000c0c00c16492602045443d000344c0c491324201001030304441020990f0760208a4148000400c11209180b8482d10610107400002e18140400d0b40101c103101110750110703060079101c0e00400d01d003922940004080319000c8042c400c1c145810131444008110170300e007000e030143c10424481d0702c0e0000b900e142d0242c2100462502c1075442180c1010742000401e004031341c0400d580304401403100c07450a8a030f90200721401400e241e11030040085505031600040050724603440c0c4a640030070112448000320800c03001d8010b101c0080000e21400e06124040c3e4004038142c240b440400c011103010481c15000c00c03901000307079000941241d0801e5809034010320a200f40010300f01b400181400300083c0598401a41e001c1035041111035409029202d024400800c0b44d12901014000c85100b0b0006504c81540306101c100414600480c41c50321203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 159320161 1250 159318911 159318919
    0x907050c0d0e0a030b0415060503030703020a0206091c03120f06080c06090402090a17150105010c0b0402120f0a05060108071a09010509121005090111070308250f030f090206030601030209 82
    0x2242d980c1d10380b003d0400c41981d003101c1c1c51304503104440c002c3c5e90600401c0027a02048016519101081d50042e41c1c603036410760001d004600100d00c07500d1300c1e60f6031506004407a07032441035a240c942543c038008041481440c02004190714041340c08954031000c1c0311b94821b6a800d80c00500c03081d001c510400c5501c3c0c00045a595015170200a1ba600a40714101c01c1030080002001c0342d400b40681518550600f03000802c007003149200341c0b004014580c4d001c06115a250380001c415241500c413400464407141c90040354030024402c0080c1c00c0b040410020303203d0161406642940d0280e621081c036540c4420b41c03403040180b00440e038207400c0603103424180104140e15050400300c1c6001d4450012030010203103280c0012654005a2401c20211040e00619500c008540c0007004010a0141c81070050b000b0000050100130640e400550708028050a45980c1e51580012050a24603170500030036804031070302d071800003904001c1e514002d2115030103039000c8240e004210031700b1030b0398407001100290444800c02d944 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 159321411 1250 159320161 159320179
    0xb0f060708040b22050405040308010e0a06050604060c1406040201140d0b090a1b0905062a0102030903031008060624160818010e06030105010c140105150907050c0d0e 73
    0x12102800d001440c4861042a4881c1c13015030805041c60000302944c04107014500340380820000991180c00b503419500344224258942d2218805070009144076003045800c003400081c0410490f0700142c280355041e218071100c032089159000c0383c07600c0e0a02030354003c1c04100303041c00e00b50100c14282e0151041c0b06941000140e081514400140308050030f0721680c0c28955114101c1c54070ba601d1b280c03010100b40c41030a100c6422498034000c60040d116035a8000301d018080003075103010818050940040608502c000c0d500c0e82840072074552254010f0300e4088901e40954000a440e00340412828880d0300b00808042108030785d85451706940e0024500c0d884034110412040d28110b01070350a07000707228007403410751b600c5803d2207006641e10346518101c0c5051220303106000340282c0d00c1c2800c03241034800c20300e0103481500300f41c500615081002480c0040f00d500f0f0104100f05244000505440d0144c1240c0c5d600181d2a58801a6110320840c1a6001250000c511a140303c0307020f00b12006950202074040c201d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 159322661 1250 159321411 159321419
    0x40b060c0106060507060507080f040201031806050c03010f080d0e010503062101150501020c030307020d030c0b010b0702040b06090904030807090512010506120316110d0204020415020d02010b0f06070804 89
    0x100b110480d40203103022a002061705010300070544110303a40000e25062103a11401d01c0e07400480010030040000f8101900c40812502589211901c1c00e5504c0e40050203210707904201c00101c6154209000d00915170400500000e190040000c09000c120016201c03800d000313a038000110380960000781078a402100c291380c8044020305055411202d01c0403e800050507250058945075144070b5a8403450440d48007101d030303403580e540102c101da801d25412070300b200c092480d80c075060360040030410010300400011000041e01c105c0003030080a407a88219003c02c1100f441d007042140074065842e80540040d110800180000e00541104d42c21051038180708007159507900c00100f44c0085101c6490740360b5150814824981003040e180c804489a400c003079404c0441d496a94109001e480c0d402a1800e100d610075002c194640303030128814550007802c1075590300d4441d4110030422142c0e550801c01481001520308041c2e03c103100c1c0b62040d01009025a4800044500f0440f050704140e4082d9405101040001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 159323911 1250 159322661 159322663
    0xb0901060b0c0c010206060a0612090515010f080c09040812071223010b03061f1103070305030402030d1106190f090507060908030a0504050d030e0301090b010906120b0105040b060c 79
    0x45140b2024800905400003110002414070501502041c040c6000713003400d004181d0001c00802e4131452405000900241a040540c42c203091318002050845851002042e07884141e013544043c1c0b031400040b01d0b480c1c50100103001c100c071022100134000110a10000e01110560714485030444160b241c14000701da4002c141c1c0044494560360303080c0581c0d410828032280160f10a925004104000980f4114982036010882101c891040c440000d920035002c0400140a0840781e00201c400c002200c0c1c0703c149070b14012b001130f0305c240c0e8182d1003449410200ca82c040e00c00d00c02811202d03c0c031406807440c0c1e1108000000d00344e4100d40091a80c0e5122408659400140d210782c2000ba07006100030078600d0b24148018200c002c10703410083c500d41081000c0d000300c98010086034100c80c07090b214991740e12420300301181d03120581207103242e155080c1034818081c00070b00f0341494180e40c1569020001c03c0d07981c0c00030155101d00c9001c01081c807038410004002500d05a07006000348580900b2462500341c183ca069 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 159325161 1250 159323911 159323917
    0x81905040807232d01030603050c040506010c080301061d03010e1e010b06160b070203030f0f0709090203190f060f1206110d051902030103020d1104021902071404090f0b0901060b 78
    0xe213007090300c100642820305051180b0040c02800d0400116080d502d03900c0c0c40e8503160b06414000d1380c5610100e1042e1348265000060242c014046644950312004000c00c08500341d01003603143d0f140c805035881980b5040c4190156900003c00078030f104582444200b140130361b400348120f210b55a807000c1c40041c1d02e400b8003d050031459504c00c076190b4641c500d080e0021200c094186e004540c001c2c0100700400341000240c0e600258448007540040d585d044040b20109020741044105030300100c10f0010080d00410007001841c41d06009001140b021080c0b0801c4030310511502c182080c1041007000700703807141c078400e50401e07028003000320b042c01e0b0041d0722181a51140e4400030050b9030b00d00420048403001503100c0007400b50f00d8002e45c9103500d10f40015001c0800044094034081308100e418090380d40e141d0483d561070040c440b070300c403070304440001c083d49038130301d602c5223400030007114129041d00e240c14455000441d0780441c1d12604820580c0300d006a8860041007402075651351000420310054030390103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 159326411 1250 159325161 159325189
    0x204030602070b1323030424080609130b1b040602060103120504050904080c010e0607030603031704050d080403090803030a230c031303021908190504080723 69
    0x80565500b1032854000d00810006200486146115201e0070003c0c5815144400000082da18445408004080345040d44500d6200001c44800f821541d07682e244801d00340505840703a6126900580d17603403424071541d10300c111000080402900f014000003043c0070505900f1601040861940410800240c0141d0b8001e41004025a200344010420807481003101c101418451518905152511000c240d42c0b070340c045d0000304905000f18000c42c00403400d50180d460010748000300d800b01e040c8640040e004140a000580005055064840141e52401445405643d2040040480006a08040303a42c4500944120100082c44070002510b000401c080d40c001c0406c40d000203400e07042c8078035401070600707401d01c0f84011403140c104010300c06d40c2c40c006513640030010070041c0c075800a091900701c0c1070061201000d81c0400c6560800410b00000c00041c1c4580443e4246256480054110035160340c042c80c42824202c0e03010043c00c0c4180500c501140800821030800c0440481150001950b107168030301c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 159327661 1250 159326411 159326423
    0x10219030201240807090216030f0c06050c13080c0307060e03070803070303060f08010e060106050d0f021603080c030112081b0f010902040c0e0901140612040b070810140103090501020c01020403 85
    0x5004d001c9103005000460042c880540e085203400181200400700140e2040007038140b1040c044c59061a501803040005503580c00182000b0a02e48542c005446e41c00110300840c000c1706800c800f10b460100002d07500c1000a009006104451405108454100c542c0303020b01e405000d074540000d00e80ad81000900340991003a10040ba0b05410100d0405c81d0007925400140300c1d0303050000383c000101c004115030341920000d140003607407105101101405808505040d801d0148001540700c450307442e51000d05c131a42e200f903a9603c0300e81c03941d10311981540400c0c01001d0700d018580851000003002c500040030301d10010000c003509184042c14007824019000408016a5100c3d045039045180c94803c241201e40c0a0614100700000c22020808928050254680e40b1034140868850b507a00d03001075482c0d0203481101c5901303d01d07141c0b400380440071007030b00c070500071603513a0b404246001380f0340c40750703500b52010344a000103222005e00044020f030800c5982603403555804c014420421307200303000800155000303038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 159328911 1250 159327661 159327731
    0xb0a0c02010c0804020619021c02060405010b0105030103080f09010c0606090b0102070906061202160210050a0311090d0b130c0824010e010b0a0504350c010219030201 73
    0x1520180c252000d001c14141001a84410800141e40348400e995030715202d60010000d40c1c0302c002c0164030307243c0400070548110503c001000c003171680c009800c510441c402c6009000b005040c20054030140401c2c08010701054080c8a5072402d031803882d01410b5402414500940810010b44038241282c8080d000721500c0e075281c00c640509945c042025100900c0442d0040100a103003c0c0010040c8110a2501115540014856a80702500140181ca0a40003045c00410b07000500001e031540d40079603d10750220742044050704d180c000010036602410ba000e0300c03e4513102c496a0303600c5a450001030244030f00072012134284c0003040300d45591501604440c0001e11030581502501c00c01442d2418a0003040d5500b01d00502c140d40c04d50001504540c4090040c54668038ae1a00c09e48060041c0d41010241c036001c1c4070003442c0450036075406070303446510004091003a4680e0103666125660001d0882c0964840202240120031212801c038a5030b0080c070002900e08000310b034880002040302080040740e8040c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 159330161 1250 159328911 159328931
    0x70b0c0a110d050a0c050a0c0806061c151d0601030606140901031205090d240e0f060601080c0d050a020306010e01080103030f0818011508060a0b06041e030b0a 70
    0x3211000c1d501c841d80310020041d140361484001c0162007425022010481446040c004022041143c09407065009104030816520381410035680c0300708842d1244078640300300880a0103076030091141c548582011108070b038407202c1824000544020300040c01000c0d030480b442e60030544284040c60207540304100c0411100d280100010074400440c3d000d512841040300100002403003894000801082414201e4a4004503000100311b0858030801412454072151208441c0850b00382038500808403017001c100c00c11a140142e940c5c2e5005040c41d0800c1c1e441070000c503450358002d580304e9038441c0c40000701910f0125604114416150207580b04107a041d004001d11010b0b603000202030540c150300f032900300002d61450310010b02e914000405581481176050124446842d0a07400d40300c40c4203180000d01000244101d03c0d40c0840c80d41c443c2c801c00d13004090100f03180704411b0003a800d000c00005c1c02c403404c0509041001206560b81080c0030b00e141070b401c40c00800500c6600215105a4424000140480e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 159331411 1250 159330161 159330167
    0xc06110405370506090f18280207080a1409100302040306061505030c0903031324030e1209030115180614150a140c07060212070302070506030903070b0c0a 68
    0xc80c1d4440d9022080b9000600060303e45506903080c14138111340c10080002081c0204403100c060b0030691000700420b00030000341e288070075421442103000c6c0300018525118030410780c0480c020031400401a000411a468074103210f81402c20102c49984d03120f606d05a2002c0006482100100d030072004250003180c01c00c1400442d1003000001c02084027044004c0b071004c240144075120007041001c543c6004607044000f610308005036012940b944581201e074503143e800740c810560f8250302c0307a00410240c00202c114244680501d801202c1004010030060403466801e40301078205810f41a019035a80452202d90100940484000c08582d1901e07181e140c6600b04200540c0c0301d582140c0c01c190140c0d80584031f41e480f0881c05800035220942c042d0b0319622135600031202c5000441c074000d449140840c014000302000b140c000f08580e0a6001c6901c1540401020a618041d409019026810103c010000d41c00c004004690101e014030590b0f10341801a41e959940c140c0a9440f940c42c01d00c003180030055503030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 159332661 1250 159331411 159331489
    0x61a030d021b0a0506030708040609020d111306060806010e01020a06051501020d050a0905040f090c06020c0102011a03030d09170a0509040b04021e0f0408060f0601030b100c06110405 80
    0x242a039804810f1030600c0085107182c40043c004104000c0b2100c00582170085552110f15550f40c01880089515000d00301440b00c04800c3c1401ca05c0340c907a030f19550140d40028801c580480303d0380c1e103417045143c0c0c5002c01541c2e000d4228080d1415801211072160024800e88101441a06da06003402d130a241190700091030001241c6588080c070000308148900710f0340249071002144c0080364041041d0007400b00001c081c03e03050358010450701003900e003c00d1194001c54121a01d00c000ea00811180000a941c1c004903055048000d0f0546c0081013130b041c08008507000015401d0150250b40b4414285540c0e0002e254044c11a000008801256403003562425001d0301d804c080e0212010360400784a40f14500b62098034000c68100305d080014500e1002d030b002d5040d9401401590250f5009190404421201100131030b5132a0000f450008444403600e44560a20220b65180c1c0d900c5900c80c90541d02c000c01820030116034807003004280000038055a41c00303507417944142c806000103030015281018842c1c0c90 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 159333911 1250 159332661 159332713
    0xc04051503062e06021c030b030604060506120a111002034006050328090303050402030c0109080303070c051504050a150b151e21060d0c03061a030d02 66
    0x4120346100f0402d045e80000c01d402900c02c21804070000e090f16190a0300105440b043c4140c1500901080109100850340111b01c40c200030fa54086010070b000542e0341d01d680c0040b034010080c503106030122819051001103506c982ea0135004030b070300c0c5c10020740401454941c119482c600c1c0184544544109034038000c640740c039001895140200c0c03103080407800b070f00f140002021003907a0083c5004403044107000c00b00144c001c2000520070400c05440703080c010041e00c01164180d01034414402d00075042d503c2201c201e400c8400c007801450864480d00422149881518000e035241c0c40780c0c00c0d0303104603174031a5084280501d110310001c0103c01e015203483d0300c2c041400300d00722072071618103a54060152106445c6211528003916503941c2e9000c000d0700307100c5170a10150b00d0110018040303040b2072040007410501c421440100003516a69940380100f0441c8009240010030060740e00d40104001541c1c4e4100390210360212041c1c18444040e40e0110b0b00e4101d609502d0070050b400051409288041c00860584030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 159335161 1250 159333911 159333991
    0x30e06160b041a1b070c0b03180f030306090f04060b22150f0b0703090e0a020c060c0307053004120f020c0a0311121207031704050c0405150306 63
    0x62500c10a00042542403813501401041c00007500c108010144d20740c4800740900315015500d030300f014240d0061419000d20000003074030507494150705040d000410340b413241100070800c014030754492a460600320710180046030403035260b400d030045548d81c101144030160428034101d0b141642c00320032603064801c2003098180b2541c00c04010b00800400c3c1c20a907082d2030042003001c0c4c0d01e8040345012503000721a94007411000c4000307400d0010610958000b801200d007403c0c111041a02c1d24020750540344426070f40340c00400c400304000c490004404031404e0a601c07000c0d280580820410046c040e140302d0072201102c0048550050003a21608111320700ca02424901c020400c504640e004140b8010305070202500062005040b90b2281d030b20300d042c4400d420b0080095a05503455103450354006e8000403012804210701d042c4000d410295028028819904003000300a038001e20000d00c4010000601084903890145140040c1d64a0070406180590000740780e0300d42d841c544010006885051120140300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 159336411 1250 159335161 159335213
    0x110408070305010504150b011d0a0e040804030506181903030e01090b010f0b071e060603052401050906010e0405040206040b0f0304050111090901171516021204050607030e06160b04 79
    0x66668054080a0200d649c864150744c10f503800c000041900c8000e0b8490813130403409100f08402c20154102800803a88038104544403600c604071040e081c0940703c1c44203d45c5610910341c1410004a0907803400c0800d0003810f001564061a4200509698100a0642e03150400a004201d0301540344140401030000785161410100c09584044c20f105018030303016a01c01c0c0c030303030600401c2c0003007a484440110741c0034080b91201d111210b610550a00c10b4140c1580340e81010000107000d080484803e4880e900580d030306888030400c5410000100b801800980c1c12080074400490141c00020003000e8902e0312a010b19160300d0700b8a0a50b09440040a2402c1c00c0e07003042c00260760503110410458156583c40b030a0b420301c441d611311158036050000c1c281c01e141c00107203070170b00c00c0760280381851180f40e903915070035941403010b45d501d000050b220328415141c02c01420803d03540841d11034072890085000080940d440d2019094410b900b4000103002030f03482d14402c2c0c0c24841000244a4104009407404100d205 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 159337661 1250 159336411 159336431
    0x7060206060a0603020906040f0602060403031a13051504050108010207020a05060703200309030d09030b060108093417150103020306070804112d060f0d11040807030501050415 77
    0x141460483c80f0b11801c0c56008034001c0141e5884509480280603c0700c11203801a6035140c00a554050a550907408245042440000e021295034044c14407140030f042c0352500c0c100c09544800402000f0a41410020b000710035043e150f03950301605d4000c180c0d610001d80c440300030303004000082a02c0d030300c4184545400c01500c00002e801410200b09500c80340a02180c8800e0302629500b035114295020354140500d202004801e03030400106000e89016092003030459a502c40150747c03000d02900d03940265030003650080d00c481a103101005408804140b96282008a44202104111142c104e144c0001800b05552601c040810900e03040c0829014400219455a00400d0301c550740039007040d04106220700001c044c420700d51040d280303941e005060f0300b200100d00e484509010880c0b0181824141d00c11011502c0f91401c5401c0d40c059642d504442403a0070400041300d0b00800040e9403803091020280400600c00720140180340003180500008205c0f49040d2410108142980301801d120514150f0104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 159338911 1250 159337661 159337669
    0xa080304180b01021203130c080d023c01050403020610121101050f13080c0102010905150612070b090102010b040608060f06010e1002010630080a14030f07020706020606 74
    0x1001441070200c001440d01c0c24500100c1c140050000120201c020010520140c54a03100c1b007048010b00440101780200d0f100c654654641c018000c3c0d1400680c85517012900c4c2031b00c908096080001a0f085101d4104100c000030000b580c000c0d000001c2c00c1e5990000c00092540500507a13901514441d60038400c20300300004c401428101c04805450b2003600c64101006900440c1111404248410307020b0b143c1c3c8041001e1341e004600c43c0a11a070364080d1181ca0307061540140900ca42d21640031029000165050b030b03101881d024000e048a5115021003a090207298040c80314801422203011003940d5141501f00190945044072a20ba000b41d24040c800c1144c460081140f540080d030611900c2e400780c0b0f4940040307516007110401954810407003804180e00a030158048004c0b1035114009181c01881d4612158040c0300161419071220144180000018400001442c0d46a000c0c1012418040c032035201c040a41c00407205030118015800c28810800c0c0c0400801c0700411084c03000f0162407a0280c041 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 159340161 1250 159338911 159338939
    0x1a03060610120c12021602031b0109090e1c08100b0306010801060e030a0501020a091802190807020f01050406050421052b02070303150e0f220c030503090a080304 71
    0x6408490381d0b5020b408003d034030602c0e491502d82c00001003507480744150304540c0c54504036560203c0c46885540d04066101000a07015065040c0585803490500e15091016028100a00c2d03410000d00a0081c0c0301d045010075011620140034959400035149007020102030040c90a4100c0b074014a018820092140e9110758900d0542d403051502e02000107070507000c41d19204000000810950010448500c400d5028080d40121000c000344a4a1151030000713180c12403050310b10121007410301781d4100d0026030103602c003039401c15014070445000180290b5402d013140c5040d42e003180d5080d1140140014880e414405094007682401c1300340d9201d081c1740024006201301000c076400542c0b008507451a07200e0514940c01040c401c111300703640d1a0500c1c40c1c010001c01c0004166001c0d4580001d0100703044501c541118440c05154440e4003240e2036501000e84000c80c6803540e06031085401411000040b01d0506201c0154070940055440340801e4040280c1c950315a00080c0640c0c0c07040c0410054090751640c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 159341411 1250 159340161 159340187
    0x19110306040902030a240b06040312081b0c03070b01140d0204180209010306050a05160905040213030204020a0906020f150c03060d0516050f0603070804021306091a03060610 76
    0x98114840c4042410041003101c05011a14008007035044101b044464908103100d0020400c00030b004002040021f000b80d000c0540814403802e0b252203010700484909800002c103005502e0b400103126030f5088541e229404400c41c50b04041414410007810fa0f480074050100340d108115104502004202c0c89010329001912070758842940208401182c940041102d4010301140c2c0190303120b040030302c064a003e584c10901186004002010200940d4042d0360041c015514540c1c101d01d040204400380d00102c1c220801429524000001030343d80d44010322f00c0781c0507070b1603000c0705529021005c0d04048900c460750211740c004040e070b440d00d41700071410903600080b88019243c40307032250004501c49400000004006110310b140c5858000c0b503801500080fa0b4040ba000c400c810025002e0003028041603c07070b000400e51480200c0c0044c035011300d5443d000c91421000141c0696517403104425986400e11424840050300103500e964201403120790382c00380b8141c0700074120700c50080d001002c00760b100c05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 159342661 1250 159341411 159341419
    0x906050d03210b030a03022a0114090114270a14040e0a02090702070e060102070e011202041407171b09060a0e1f03140105031903020f1519110306 64
    0x2d10b03811121254448038410304094110790885c80d483c50f0107551100d0b81c1c002d900c1d1b800d05110a480c480c6540805820a05406a43d614450103495808000700d8110181040c140710100040054070740045000c3d090700303100c04886121031402c000503011010300d00c092190058544a101348100c0203200351906240c0400d82d000540c186204801c0e50400048038402540032a0240034800010b0740040c5107001d03030314000c003e41c2442d255040160798800181c49261142c00114004016486161000e1130341e0701d00103440400e11448680c036600100c3c508940200128400d1200000c440300c0c5c04101c0c43e40010b0505001000100714007000545004110351075101e001d00188218440b48544544991203c3c00350690042451900b018100309078004049130020f450460140283c0541d07070000b07412984017501410001d464015940c449001030300003a41540b103856041f02d00901e0410104d6401e682491a00c1d04034284642c8002800078160345010a1a040c9480c440102140504407070308418111 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 159343911 1250 159342661 159342707
    0xd05040b07050a060e0c0907022a010522060f020f0a0611070c06050702090f0f0711070e090c01030c02030c06011206060503010e010f0e010c090504051503060405070906050d03 77
    0x1c039000789400580c1d4030044c0141e003058032849400c1c3c030001d107591080d40225143d1503a03644204040b6a0b13050030702c0d0420100c1c0c3e44100040310501c000e0b46021500388043c94010f03d068102c00e0210036094142e5850941140c090004004840d401401c001039055a8400351440314007900301e055841801101c027a080304d9403240380f10303801072004c003c4880c11a0322541054030716030740c0c0c0c10107001a00400c900341c2c0a02a50780016130341041260f000ba01c01e8a0207000040b0a8403840000c880d106140004600a8403c5a0b40842c4080c03003200c1d05485012072000410b880c0004400040554892401607070030766200b400841c5c241303103000c42d8050540c2d88900220128150600700b00e0060500395000c0ca40552038182404a0b840c410b420000d1450007400e01409010b198003501802c8440500c0e1801c001002140244403c2c50640c0141e6000a1142c520b150342051500020307090850a0303400701da550b841039204005c0ca4030f4600460000307150489241d2900d50f45a200985a500001304a1061303180300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 159345161 1250 159343911 159343913
    0x90106181505090a0f05030c040203190c0201020c03040e15040c050a0507031806020d0305010f061704020d020a2606060114090301091b030b061c080a11160905090d05040b07 76
    0x18001e0f10300c00c00b802400042c4c0b0990700c0600040700d14007030107010f01a0046c800c9442c458202030088a0145450249000c001039504034044000c040e0021002c0455408210341450864100090406040b2552001d8100d04000c0c2d011071018083c058582c0c001e9050450140c941d40e0400195148000141400c84e9202c030b041c40c1c120744000c5082810005500310180c040b8007d58005040d00030f0888503102004640d0301c403013070840c0c0010f10b440395000244d412039170408050040c1081a4016201610390982c4100c268005018004030341c102200d02669080c8207442c0b5030109a19401e040013500240c003d50030103600080c580041440102c4c600d410000b80d801c1244c809520074050150480e10000411045810700d45165103148002c0d5070840e8040c01203503051901c1400300c50b80100c2c8001c08c9046502c5566141400e4100e4007000f0180141e00d00302204910b404d000035040ba01d426540c8001150401c0c042c0011190302512420055020704014080c2641000031581500e0081c2c2e186a1500d4031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 159346411 1250 159345161 159345167
    0xc12050402012709090305040510090305030409021b010c02030702010206180a0b071206090219020105090c120a05060a020d140433020d06080106061d0d1a04050c0901061815 76
    0x6190704c0940505d02c0c0c078070507805041e071000c00b5100344c501c11252100407854184044549010500000d840380e04100701c00c10011059600500101c03000002443d4042c50103420b042c21128814900d0340507800c0082d81c181150781c10312100c2d5102c98008a1009800341304488035944846410004101964180214100320f0081c041b0420032074110009004042d15000c00c08040d400c14410fa28454200c08808058a030041c05503910820101e001080c1900b8848100220032001d080040d07864003d092011010800030300840e4420150003001507031316442a030818007203d6900c218400c0581c690703011300c400580e0790760001821040d4801d041d042c40c030b110740006c00b1034010151101000d43c4000781c1146150038980000049034040d4008110342642e448040e00c6424071020704030f411007403d20342c013050f40c605981400300c407500401a01ca031140020840c0030351030740c0984d400c0d0b800e40d1011003032209600d080c1c035420703016041d2890b00c0d0340d02407440314005008180500a50b0f01d20700320288150a8144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 159347661 1250 159346411 159346487
    0x30118020714160e060301020a050f2508030105010810060e0f01020f0106030b040c06020c10030c050d020301030807060f060b0a0e03010b180a050a02091c02030109150c1205040201 79
    0x64140241e550007035000c20140e04960f124071440c0c5450035410002034840c074042c42a01c0b44251240c4400b440d1942c07444448074244d0102000300140000b420b018211509c840309201c40e500e201c0e05489580394180b00c0003501c4110020034442c11841c440c4000e00c04240d1000030040c1c070303030001d4401ca1086401000103034184419201802e81541c60100000b05100c0103a601c180502d000320a90440161100c0c000ca86944c65014078035000b0303d180107410307182486648052250982407418900301a401000d080c2a07900a92050b20745000101c1c0300030034050f080c032410f06500f04000007088150701d030450480c1d00e8042c10000c01c0911140c460316018580f400c0d0004500c21130014140c1411481419a04403140b03801d5444000d043d2a01e40000d02440d010310072121000d100030100e030003c002601c3c1c440302105141000f260555200c810190014150007010505512415004903c40c69024402041e03042c40760440b403c424108000d10003d030360000f0800c076402a40020b1448034240e1950315101b010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 159348911 1250 159347661 159347693
    0x1e21050615040f2d020c03030f0702010b09060906060c0a02060403060207050f06011d070e13020c160509010302091e0f04110306040314090a031a0702060c0301180207 73
    0x8060310041080003080701445102048040314100f02c080e5241e40c80c101102c521000b1a450400d100c1c09156203140414040d11103003041100262030a41c0c5014154210b8105a6804043d00500320900000c2602070041100301d202c1500d00042625058001814807900038200350b01035040022400c00800051140448660b00900b4070382d5510350b20314051000b503200b03032410b403024000c0c0718074916400d2004c64080e04035094028141d80c41d118116051039040005045c0d901071240d0400484200c1d10307030304840c80c00c09011000068807083c00184050501d40072902600c0203e1034000c05120381d5071620354443c1134030380694603d110383d075420360144000f03604a800304150002080811a070070110704030040c0b05502c991030010040002505155844c5410b40303000700403803080014016409641400b4004020740100004403195580d124540c0385c9020441141070a03803410704002d40c0640401c111a0003d01c008030040c17a540c03410000c080001c0b5050102c550040c2c00048a00a004014500890b10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 159350161 1250 159348911 159348913
    0x20c070608130c031115070c03020906210a0201031d030d02070809030a08030a0b010306080303181f060f06110d0c03020106050604080a0308010b03090a1103070317030109061e2105 79
    0xf26260b081c9801003d0f0081c038441d225500c500e03502c1005030350010594405561101c50061090301f140c2c20403014820082c0b4147e00000211142c0818201030101c0c601d8601c1410003030031958443d80001015185c3c2c0d2002c443c5005400c1514103042c01c0000b04442500c1c942280068440341075160418062107803892030766141c40350010140a100c01900190300030422000c0410514800c2c0c07005500ba40c1c8544520b02003500b007800000d100001442800c3c0d589505e1a05649044c1101c0003043c9464494605078581355030f583e04180a02c548000c0030101a1030300d810000c81c6150702804199454410700d44041c03c100c0c14030b00c5402018000d4003c1e0001c0c0400400303442d101c5032107242d2542e944640c80c43c29800240050000a60600000b0031640103d0500025155019443c0c036a40c10b50341070000120303014400d1640000100341c0c540341c40c00c00c0749154074401d0340e2545421113000c2a52050b400481d5507040c074006140b081c00d4900d100408881c4555030b54134840880100f07002250341314030f030301600d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 159351411 1250 159350161 159350183
    0x1050a0b070c09021209070806010308090103150503120904290d080d02030103080904051f050f030f0f070e01140a06030e0a0215030a0606031418120703170901020c07060813 76
    0x5c0f2140d508070561003285400c0840b5081c80d6180c00c5103a03200820b1201911100081007000c0361544a90814001070003400c080c150742c41d540e407011903d00308400d02501510040810000240e280c5030048045061a45514420440c00d404c4004062010044428401c0c0490380b1100e0400901005691582248800442d100c0da50303400c0501440d44a02c407814400d5283c5000140064901340020802c6e1100550030010103051905016054007072403000395151207030007103d11003140200100c191450070300000e041e41c0c41c6000c451081811040e000040d410303981d030700780030040e4880101080c1143c0e000e140100d41406004a85800e0092003580650401001c003120420351160b14011405601b001d04104402a5900b4003101200c0341803042410001c0c00c800451000c20320310044100c244c203480300761203882c0c3e607511484031140d01c030505c11004503810134400d04082405040f40c90b40013450301c0007589010061382c3d00980b904018000d18092204910105040489110181c408a5848011942 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 159352517 1106 159351411 159351427
    0x8031e0a03020c011509060506120408030a0e0a031112070206040314162403020c1009051905032a0a0f06090204060e06010e04020301050a0b070c0902 66
    0x10070180c007800032514025085c401c560307074842107422007000c1c10301d030a505505590980e804244618000e0003882155000080142e5220307a00c9400b00d80c1d29594000700c2030041c40248039150302403280107003400c2010381014103943c4544c9120700312000000800b034100030303901c0303000d174002d400510600c020000292011013040c0404285020342c0c0700102c50710102d803081107903075005002c0e020544000d078081514507621103d10a8107441c00303522302184a50040e540745000a1841800b590340c82117441400801c1c00800c2034210601001550310f99107050155494004410300b41401e001c81c511035280c12103607038400b98244d861602804c1074000d90b46501452404141065640e507032100c1200006a803a4407a80700a41b030f010980c05480d05280000600021454840343c0c0600d10420040c040f503034078400300710708071501d03921010f5681c0c140e841c0180501e061035000d03000721400070075503031 = true := by decide +kernel

theorem cover : BRFrame.Cov 159172661 159352517 := by
  have h0 := BRFrame.cov_init 159172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 159172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 159172661 ≤ n) (h2 : n < 159352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
