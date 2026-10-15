-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4644
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:51.884029+00:00
-- url     : https://prove2.me/submissions/d6e04258-7808-4937-907e-e03a8acf6d67

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 835071942 ≤ n < 835251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 835073192 1250 835071942 835071953
    0x6021201050103111606021c0b040b1927050c1903050714160203060c0a1806050328020f1308070e0c0c010b1c03031812030c030603050f0604 62
    0x5401007609207801d101d900820b85070200e1520900704061200b1041c810300105000d49a0115200b00c0c0350710f84914107604464400c14010241c02c19018411402c000d41a2240d1410b42e1914080303040b00c100201c0014900004d078102c81150001040485040b0180030720061054810741e0721420103401107a580d00d090840316103266595540c100b050516140920480301c3d40300c0800b500044410078550b40e40c4c10340d1600c3c00d4075a03180010096047c82108200712018461101405030b0070280d844007003100d010034008111224590240100150003400000d00004401c2c1e60403003080e404404400040044181c0ca03426680400c4130964104000540301b00d010841030350000003001c0205c054020b10b800c240c18039207501c4001c0c04032021131501091100800100707501441484100401801c803c1e4000101c051002d81075400940109190445100342a21a25000503030750383d205000010032562540300354000c1c8001410b000030503586e06c9012000480c20040d4040c40c00c1d50750010042e6182c5864907 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 835074442 1250 835073192 835073227
    0xe0103050c010810050d0c0f0f0e0f010303020a0308060f09181002040e04060207021210052d06300f010b060c070e04020d020402070b0105090c090a050405100e040602 73
    0x8041c100003c2c041084058402444124152502201e030704e81c0b985564148500d48041640000308080d10007034000a0385030300c48004000f1185503c0c01d90040b82d440b0440d20120282c244000350260304a0710f84000003a01c07508807030380d100b4402001c00d12980d81c824046501001c0440b100744410711110002d04418108120b94440c44070946019850a4107041691859101c00341004140039008a444070441daa480880c0442c48001c00899a1403400401160050502a10400310085124980728400d03180c490410002079109400e0811640790542440240c540c892382c0800386485010260709084102600c1170070541092004120305030001068a00316410558500d11a480c10819800745e018085018001c403490f141441d029070741c480c0081201000200c400070f500c2032000942c0003c010f103001e44170b4103030351060310806110350300d6110151981c4282101182d00048103081041030340740c00d800c207580c0110781c01c0400300280c2d940c211200001c542500c08139411500031071142c10b50b20741d00780c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 835075692 1250 835074442 835074463
    0x1e13051204080c060d060b120121030507021210021c050709030c06120605040203040501151a0d200c0a050f0616030506030c21070e06090105010f03150e010305 70
    0x8403500d002e01d4140c5042e82c4202c5220810300408010411740d40a140c41e40c4110000c04480c41910794504000110701c6185509014200070b18404440b0803040b004000402c441c13080e4551a03007442d10304036808001030304401d1018400c0c14490a20b402c400100c45d0700151021455108000c0860301c4034440040580b603004001004100000c2e0301000460244042c0408a420390b041524001c403604c00c449016103030503004550080e000100388010803005612080340a8207100320142e2041d01c0c0d030010f5200072aa000304d002c6540c4113005004140d50203501c0740d4910740f4468040d0030f00c206070001128a9030001c442c0340546070414048001404000c0c0b05482c0c50601c207902a092a180c004000d2607410038003151001019510300001c0c103151030400c0120307291003004250040c0d04401c1c5080e801c039644804562513031401842d00c00200c0c200680c80017406141c0017007070136100341e007808011180759a03180c1c000304c109501d803024460140151a40500544280300140c0d40d00d605505006103401310046 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 835076942 1250 835075692 835075723
    0xc05040207030504031217010f0e15030706031a04051317120412020a053c030405010c0c0e040b0f011d0f101707060219030e091e1305 59
    0x211000c0000c2d40101107a044d41d5200c0302c3c00d00786ca900300d4130844404180c60b12444d1f400d440c0c100042502210380259404440c0c404141000b10364070006603100b0f00d51a450502c1e01580003090a0100c60700a40001c00e4a01018040603500508140010191102030b90840000003440f040c20092007114008001d9001d0090707002e40c035113464101000760b00c00000308050409002e010038010010301c248107011030701341c011003119461528a143c207400280100c0d0320405131501d020003401150094121003e91403000c1d00914141440c200054030001602101100d46410703401010410441c507803051030007240959030300c0141d4508612581d0303944070b040c0c10030a050350455035042484011600203d81c40f10400103c104540c81d0700f0b0344071081300071580010380d6415811807514590903000904004407541a4201c0340340c11403010b4087c542d081100c2d8080c000480d00482342500c0d040c1a41c1d030641012400306c0d4012060810011140d4180b403d4425041407104420a0405d000c0c0c02c210000201603a503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 835078192 1250 835076942 835076947
    0xc070e0a180f02060d020d0f140105030c01021e0c060319060b120406090501021b0c0a0b1908190c020d0f03021602010c02030f07080604120f0e06180406120c050402 72
    0x50702c42100d02100d41c10000c2c03003128005a1459801000e40545a54544c0c0200920120940c010042c4c050280012a020b40b45210400040c0d1880c00141240c2e0000c1c3c1a0003904900b1151503510740380e20b1080300b894a09119494041005031580c0d8011071041004a152040480c4c542210303005450700c42c3d01071351500c00241700c5440388410a032035541c1c00685c42240018a0012450002d000e4010743c4200801281400b070089800100864418141c0c00202c1d002c00510341c94078000402e500900688900c8018100e40c1120024040c005060b04002c1c0d4407156040845000c1c80b800644030318403503000041c0c101e0f811034034170650132a0301c40c280071400d0306081d4101401c1c85110900091a07280280c10481026902015902c0c00d000541c0300e0544c9405840c0c407562103402c440d40d1801e00b0303201103581041e01d40c007081011b4800e02088031010955618802c001e00c1e100204680c40d00303d0803c0c0156400c1d03900200d84139980303622400700200b26400d8890070105480c10400522602d5901007409103004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 835079442 1250 835078192 835078241
    0x100f0b0405010f142b09030f0518150703080912090105090109030c080307050d02010b01020601030f05150406050610050c03070204110c0f0c040e03090d170c070e0a 72
    0x810064506841d4203190481e0b41ca0708144003203400c0700d040e8030154a09840081d0307544004107480060741004540860400340301d440c0c2120f00040303c16036200940080ca10581c0310513601c2c8a80010140408198643c0c481c480e074103400151006e01c1041d0b0075800f2507000850200305034000348455030011000c005020700c0113500c2c030a15524425492040d04000001441c20b01983c080e401e030f000515000250071620035203540b07090b9a2984541d0094955104000b036507907074280b0501075412001d506074007404403a403950741c6d01e054200400c20202c80708e0080a0751031140d1001402c06a03c078078001d4201007403a081210901c040002d50740303100703401c00004100405501070000708403801140d043d20006445402d498568a15024030591078001d070044001e0b190b915603000414801d08a0202c1d810032681d201f1000c00c43d503a100b41d0741c00e180c00885010350440810380d600f40074002020301203100c030701d8400951106803c1800c1600904581c10f516020300c2070240451241004c04803401400c00a665107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 835080692 1250 835079442 835079459
    0xc1c0e0103050906011710050108010b0301050916090c05070609050106140d021518030a0507090c080103050a141f2f12060a03060903030f1506170606040e0708100f 72
    0x301401b80c4955917070300d840b0032510802c04100c200414404000204190b58480792000c1c060807201803854070940c2408080b42e20000c021a10201c5901029141d459042c5401c3c082000b410760807141c50103100d000d0040c180410090b024901a01d40b003000001a200c2c100b0b0100c812440d444030f40b4501418462402100684032100c5070400b03022010051030301d03120380c004d40d0101983e0141025030140588003503041000000542c107015101c68030f40a01071031109c440c04a403104800d02c800b8005a02c550b10f241e0100340c4d008900000d4038000e9080d240d0003c282c0201065104048520b500c19a6407100c4d00302c4004003101c4201c0d2016451080740d04501103c140340c44040c002c04143c64601550080490300e15561452250011640034a0600c2000c0c0760b07080c0900104412540501c1c814100100500380403c60340c220300a44a80b80c0300d01c2d60319110401010a1078000514041d0400c10070000415130040c90400c41c4c1c411442036545402e10b160142c036a91138080990302010601240c203005000904 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 835081942 1250 835080692 835080703
    0x1c09020910051c0c050a06020d090806100302040b0a090216110609010507020118051003020a0305100e070318050f28120c050a15020a18031104020f0c1c0e01030509 72
    0x70769100702020f030380003424204000207203544141d03801560f42d000014a541c022501581100054a815200695500c0700325110401155103d191001140341800180342c00c0d842852010000b801032a861a100c0c00300c40201c0e44101071044000c84210490b00c1002441d00f500c0c004070400b9076010b410700c2c42c2140081d0142c060010000e040c0544485040002c003955030001c002000003d10502c0000c11211001d8029030103140c03c0d00029081200040a00f0840081141201e842403070100300d599900c0e030128014040c1026141e211030b0070b000c03840d011500802050076041e508001a003e00000700f40c1c081d0541e18822103130344115030079116440c0807d100500c1c94202c884242402d000013100352502c02c0c102148100000d20a030107984c260b0b424900e80c0c0d4080c0035a500b060b1601d03003038003518281c1d04203110f5203840010001d04c2201c1440b0340700d06068000d00310146003403c8060038446e80b06a200d0403d551074242c16001c070b100c0c0041d07140803544110301c40c0c070700402801d0030009410100d140b0780e00d92 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 835083192 1250 835081942 835081969
    0xb0f03031309180602070f0303061202031509030f1c0b1c0b060d0203061509100e0a0b030307170a0914010e040b010e21061f030303111c0902091005 65
    0x2da030703907001002c008411440307808051680403030308540d40d401c9071602404000342d0240540000c1d103015800300e0305a00d080c0040245035001402419101140c90049103e040c00034120211350000b0321000030841e1603076010304010f00d00d840166014081d000721200071a100780024034402c0050310030051460f4140c08400070020380126400b4070342d6075000082004601705036002501482401b00300b003140e2a111030b0f40d290a030000c907031016031034642041d04048944680685d0201662120200c0c00d6040e41e03602800c54640c0c0501a00e080c070b0104c0d1544c5091090b01c0b4020310b06500d0005002c80030f95800030b0040080c103089440e00c00341e905007000003040f0303070813491425010f15510154440c4c0343e03000d80a020070082c0700801011040460450a408081d980007041950b80300c1c0c3c4012526480c184840d8405075140089502e400307038a507131800c8000e031121400003402c1000802608900b0702070f50403002413aa0408c00003151404451042c0500b010000301081d103034020038031086c0519030b2512000c3c1140b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 835084442 1250 835083192 835083209
    0xc0a030b01020c0d0501090317160c0f0f05030a23040e1f06020307111837091209060206070c0203030d1a09010603090201020c01050c0f0a05010b0f030313 68
    0xd4484403401030b4540041e80c3d0b0381d203501140003600c000400c58150410104039100340d071740303440300750500014100c6901d090345e51001d95074110b030594607068840d46034090020300880c80c1180964580e00c4d1040025411001a69181c01c0001c429a6080c0c008102154281c00c04050b070b0f402d02441003600d82e0f1406a03000d1402c02c4180e04004c1104880010702d11201c0c004440510141c41e9550900690b0700d43c001c00c0704803000f440190844c9024507100700700c103800d482150071050140c0d071840c0c85404958003224030300303c42030586e040d200e0001c401148003c2025004100014003401e02d170402040011100d028041040303005e09003405010750116591740c00030017501300344590f1000c9100190440c0035401c00c1c16805480d04060b4651081c400d02011001d003003d98001d0b10744d0b40c85910032010b9854030138001e80940d05c990300358005540b007440106a00203108080d140500c0d0341c14480c0d070501d0030180055519a440381900c0403545482010000401001c030300542ca030421143c061b001700030092003003018 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 835085692 1250 835084442 835084451
    0x618010e18030d0c02010f2a03051f0306060512060910020a03020d241a1e0d140601141204060b010c02102c221d150702060c0a03 57
    0x107240d0041003641c076020340885050149441805000b4000e04200c07405100050910140620124444080c081d19030182d0a4101da5140c948100b0b0f409410050440045a42000f86807001c070002c20280750050b40c814030012500a1030701040000400c24118aa40700307070080700a10060420004150000d000b5107078000d0b03207541c2c19080a41c004c0c0036520454640e182869020491044114600005008103404003081a52110036a0717114000003202c1c003a46010400c40c000543e01e80c8420480030b1603640446901d080d90312403800c030030b0314000380341c826042c04041c061103125070708820400704c1807809810050821340d0301e0345042c1109001510140031035a9031940841c03aa4403a124940500b0380140800761045c0d03500724014030280c4414006003242c070a0085201c4614030103100c010880600900100700c00581c07c50811070341020300b20010102d41d0300c1303c03007403103c200a009401c49410484040c06003400015009020322400800060454004c3c3c0c00f0000a20040c0f07091302c84440d040c0c640080d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 835086942 1250 835085692 835085731
    0x92103030a2307112a100f05040e060a0317030a0b0906031f02070c150306050a0509040b09010e10020d06080a0b07180902280c0c0909020d0206030f0618010e 69
    0x1804c0511301e0340e0800408205a640c078036005d41c5005141c0da1140c040c0c3d602c101003003404001301c0326000c46c8103400000407010032040082c080003140c4c007074200c1d9009200051440c1d0707990769124070140d0f1108104010390040b080210742040ca214000d0007560640d4805820b14103500080d488450100800078210315007500d00500700825419124a60781c02252014820348582507000e2207904c800700d080010f42454008180c42c00c1000c0b00c4001c0b5400601020040e45440c1c4d01e4001d0210300808500641d940c81000e508004010054001201e01c40c040041e45c03050314901c01c1d8143c44041d044450a030b4081c80340d60000818540000354020128541907100611504408800300c4055000121150000c1040581c99515802d03d0100c090104a146800d0540361016603841901000c00307002105903101c01c106c01d42a540000c0e10443c0300415103200d21000d41e0004c0d06c15003041d650070f41030a0600d4100000c2e41049146d03c82d0b4868914000503166140071008a880c0b103008124817170003501250314a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 835088192 1250 835086942 835086977
    0xa09020a05012f150a3c0f0506040b090c0d0b0303070c08100c18030201050a12091a0f09030f0d0603080a0309050d0302160206092103030a2307 63
    0x3c1c003404903a10305803091080300d01891541e440f000f481180c40301140502242c5064541c0c850204a8541070b84119502c0c00c881031604000100c0c0140320002c07007440301002c0030310f650354403810006c240010b030001150f040c201c09200448101c800b10900801c2d000090148141c0000309907a03030750030400c2002c0348003a1480046820b5000d51034005100c00076070540421141c0000c070300d195062180c610100030b40484443c045480c03d074000140f0f000c1201d002824005548a00000c2188601c00d0510204000c03014000f102203c6e11444151494180c0c201699940d80c1d04030b108507044083d660f5513006034240900d603a0f44038403681d810180100c400081c48100c0020365004800210b40146040c0d44a003a2184042d000c1e100011003200c00e4056200c1151031240288280c5400c40041401c1603602c041310b03030920201354800c03494682e001481d90f40480000e01050b101688041001015580f00e06204020750300b03890761400c0b500780b54007032440109540380c0c02006441d44030315540b0302882c0c3c101c42031015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 835089442 1250 835088192 835088237
    0x150207150b10080f16090b0c03040503010f060f0905150a03050105090105060405070c0803091009030908060f0402300102130f0e010509010e0901180303050403080a09020a0501 77
    0x2826003a1041030030030504581d90110300c1011055408604106514104075031488044070b034808503005010100d807900c0148070b6036901100c0c2c1e40c10001c00e11602e41141070403c2c0c0028158003030540c400641403003542401c1c0a41c42080c41c0901c0203104d01401c0007110b00120780c0c2e0780110800aa91080054114010021005101680a0304480086d9120b0030311034003820085405030070b02d40c2840c1c081001c03410f2610a4510600003a80d03000300c5001c6580d92070040c7d6002030144e001c94410340c5140c00e010652485800112803103900d40b00010303880c00a009042c030000900351a07410b007100781000056110000c040c1c11222207a290316102d841801d0340300010500a130318840700b0398808210a29000c001c182d804054400004901316401d58400d0f01980c0c003c82400f82c0340d0003007540801007140c603549051441c0c1000d0700c2800450081c001040c50304058140010070380c0007940b180144402d042c3c01c85000c58000e800564103001001054000ca0f0b1110a540f1505042001131081d40d03d4804100e100d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 835090692 1250 835089442 835089457
    0x1e0f05191a0307080f010501080126070b031602030a0c06020d0e0a03030203190504022808060f0f070516140304030b01090f06120c050d0c090c08090d0507020d1502 72
    0x140c03408a803040000712112604112443e002241142c40880c852401c0c00303c085040780c105940b10f25082c0e003041c00300010040703181c900c103030810060015490030310340905c0040041d0034013101d01603c038a00500e00c0030100c1207100d02c903030540d001000750101c41c82c0e1100b401020140c00450141e90342d1078080c0c5010041c0324102e445d00c1035014a211081c105a8982c00a500a00000c1100c0064810701c00c000011600d06a4009502c40d4100d4880c10102d12404291081182e80c2020702ca0360a5450b0340003402e10408860305581016007a04201907002690003c54101030070b4940b4038203184845140c0280105071140103850700080303044003180d036441001202c001d1580110240d0b130b80c0d43d580303c0000240c040501c1c000320203400d00001080300758401a0b40c052041d0440130300c659540c6842c043c05680005441c00760740c0c1b48501d15001c80c002e403081c0911fa00c00c1c0c0f5240d840d0b0b4001d00c0d11101c10b605105654104904101041194401503034a4103001120541c01c26a101c0c003810038010088001d200e40365 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 835091942 1250 835090692 835090709
    0xc030b040f06020a032909152d0103140103080306090c0409090c03050606061614011d0a140706020d120f09050d02240103030302311e0f0519 62
    0x20b045071382c0f10307495045158150020319246100001124825907856503910041c0d0f04181010000f0740c081d107035001c014100440c00b0344089003d22a1815185207684000102c501c082c01c49100641c2c1540d040c4142c4030b6184044076203200550440d07807440e04500c80034004611507038208021905004214048030300812611304108980002d84c540951000c1d41440f05503041d0082000203080d900705803084425080c41d542c41034120030110703564072501c0c0807207200d08042d56503036005641040300c0c02091303000e210b41500002d00b000c1031680303849107124810b14030211154110031010450541c00140600e002807031400e2142c03845c034800f2070000040843e078110440c0103042800410070301402182c0c04481c20200c0c1c0c00d03504e1a01c8004250f543c9000c100040034220400c1c8401000828400d902130007004141c0081040c103c014420310f03403140c812400d40803080b016199010013035040d0b172001c1c0000358045554000d01251038130f4942c0300c03110306504c90b0b613000f0841d503011000c040e03001c050380c00007a20021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 835093192 1250 835091942 835091947
    0x1b03090201030f2c07080616020a121d0f0922020a03030306150207080718090209160e090c040e0402060d050c0414030319052104080a14070c030b040f0602 68
    0x444c2d03840310010382c640c0b25005000c02ca100000c031488022540e402500c144000a00281e26480d01030a905252100c2d03000c110b014000000c0001209100b85205221f15684c8500e003e2406004007003005c0014510184548401240d08100fa00d039140c6a9921200c03008400902001d001d0b181400c0701500c3c11300031f5020944140100400d50541d200c50161480224415880d9a14010176a560710752401103854980c0f244808202c1109052030880048942e80008070b001603290340400d00040c0140c0d81740903c00341030386021030602da20020240011400303d403404024101b51810390b20b54410f42c0100010a07a500000405645851044a00e8040c00c80340030841882e01d8010a41c40b0381190150034000c0109007503d0340d00745800010303501029800b54626502500403542038032164054080407010700203ca003060101088076910900c44d80c0110b4446030b4811101c14004d11162000300c1c1800c61103414000c483c04103a041290700d040e244d101030700300519180c07800c00d5a251041980020501d5000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 835094442 1250 835093192 835093211
    0x30e0f030a050102161a01031a0403111c020d020a240b06030f0702060708091b0a0b0c03130b040819110406060e01090503120d20070c0f08011b03090201030f 69
    0x1140710310402503006006d11000c2101081c949055040203100c081d25070030300d1402504144c0ea514060a400070311034100700c01c8807100010880d09064541000007480660241c0030307403000e60140305401001d071491015010000d0150380d448100444440c1225020108407410070440d8403a620200440c90000c00743d44c0c8914001102d0809642d044032294014091500446d100c50700460705c4501130070841c80a4401400c00019003848201080105540f12544400c0058504416402840f40201c00340c044e5541d6040000351010014080e80704140e50340c03081100700714071030004c00c0c1202e041ca1402800c05c0805a40d040400d0480030090030b481e80b00f407402c080058166000042000407440a80301e0b2450030340e1312000c15461341040400444815003c00208540d0304003a03004032400390210041a0303503009a05828507c030b800c110005c4943c58181ca00900c400300c818081d950040c14600e0080c45100c400b989100c120544020a0009160f194981c2004580c083d03044943c1441c280441045160301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 835095692 1250 835094442 835094467
    0x10e070f230310031e1e0218090a06051302100f02032101050f10120e030408010c2304082112070905040f021e0c0a120206010f05040504030e0f030a050102 68
    0x2030b0784012a200c21696804140340084004c0c480006500000c6051113500c00070031446c0c1e2000340100807688100040d848801a2903281c075000c6c082d00860000305007001e8903181203011150060180950b01c2440c002c0d040059890b080718002c01d05480c0380064070401c0c11b28040c0d00d103010f40c01c5603d40d140e50281c01004901300f0840b404d0704a07041211300c401c8030101d003814015070040c0040c1c40c0f00080e00c2c50301d0750000c80c1c4690700040f442404c114112032600350303610f034010300b101e0400304d4010001e803480c906110b1803080140406450320303603102c200b0320740740c900101295540c1102c5144800c240303108822000b460751010a407400940c1c0040340e003400d80780c40c41e40105515071320300035288582d107050151209404030744252030b089800a8500302c1d24241000d202030711a0841d4055900c940b1074200c0d02400988824450303900038585800078482ea504282110221002c075410081c00380c5d00d81410080440e6000c0641980c208003540d1317661801c4103501c003107030802040c0758014120350700002e80c5084402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 835096942 1250 835095692 835095721
    0x310020f1c0b13050f0a2c01051005060a053a06180204030218040809030d0201140609160f050408030a090e0f0907062111030609010e070f2303 63
    0x314111000405411940c940f0001c07124250b400a6103403102030000346a042680d80300350000340540140c1c40d80c4041000750b0702d000594070040074003544d4403682401501c102c0b40541c04041d00c0c084503990b04180a80700e0040080c0a041c0e500280300c0c081208403000b5800440300d82c400074038404440d8000e100d4280044010b00b40620485170040d00f6040e003588001c00d54400d640c02d40b54000c101c0d07400b0398080c45594011020141080d41c030400100640465640c00300490f00c2e00754903c0e0004240301c400403078541c0d50703014000c0419002c3d102c200204207015045101d0001c0e403402c0c82c20042c0d84071002c0e840440b000e00454010304a90b00c80001c51224058000091a0450703081c4c0000c4000c941c0c602c00078061f0300c0020340e0700342ca0704c0c0d005100c02d00c074603406000110490820b240000080c1d912081a950948944120b851401500081030005600b44a45240e0142c41c801400310301908051000410700300040300700310100100800c00641c5101030000e03464004480c1d6001a4880c05c0119104034180e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 835098192 1250 835096942 835096961
    0x14070503030711072105033a1503120c080c01141b070201050717160210170114041508030a020d0e130f09020411030601090f03020310020f1c 62
    0x84a00e002c802c0c4030040044d03880305070340740b0040d000700c000c2d2003030005d03c101400003000f140e0501040c8003411340ba448011a00c103580603404e0b1440f43c240300c00108d903810503209055461005080502507000c20708500c40c4c03041242d80c00901400100c00d40300c411145404882d0008054200008140c541044150000c0b02c0011180c0742e8900d03951078440300e650920080c08048078009900703100c2d01c00998011800b0f007400501482d9030b031440b07200c0002103000070313840000a801b14000c22008607045d400c06050092011a03107060071401546c20740d04094a0321014400e0751550f02e2094422042078841d600448250400c0b6001c0c024110b880e9180c65443e500001d004200501c5003a01d42c030170442c4036900e001120341001d8204900c1c0240e080c075441c003603c401c169035030242e03466503040c4005841d07030301c111025403003000603260b12420400001481d164840d40500c847d180c08100074000b598010810014404515000590340c0698240c40ca8030b50040c400440e0407105148020b51140300c842d0440c1c18403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 835099442 1250 835098192 835098197
    0x31e04030c02220c020a261306020a1109100510050706050a0903080603070311060f1c1a12060a0504020a031209031704060f0c15020f0909100b0d020a140705030307 72
    0x90700e402d0201240e0380c003607000b8040c00311f00d075008540c0046124902124450200421218546100c1c00030340d100a40c0190f00400043e808055400c040c08900c0b0b03202104014201c0c1c29840508228140e21150043e078010b051090001000812059002d142111060f56102d0018003581ca01100c0e88401011440340035800f1541200015540780b40108200007034a0740546088034510700c4205200b01da420010301292000820025000501540460300340e0142c0d9030b16001c43d50405042000f0b0144292540050169020092808004102082560784500750a00006281c0e403280001000c40040754405070100548010201441d64408000019030f4025040c801d0b0480c0040e507220b0480c81a407040c04001083c41a050040c148248030143d411400b601032070000c000c0058851040b0780c440c607480181c003140050700b004642002a03c0c180e10120014001d104580b0342a4440c005118401d00384139115030000f4081e460900591640100d0000d0100b440d03102c1e415071510030390726442510076801 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 835100692 1250 835099442 835099451
    0x1f0b09130212130c090912141305040f110f0a1b02090414070b030a060306060803090d08070c0803040b0705010e0c030d030207050106050d06060608010b031e04030c0222 74
    0x100032940c022a0059407054030762180540e522207010094950340c0c08119107202e18410001000911409101c5442c0c0c05aa000751100840e500080c090001e910740145003030005000588119140c081503078201c4200742c9010403820420035110b0002c05940946c10701c554004603290410030031207000303401c44124644404c9c8910310302c031085480070a0b03a50700c0290301910a20000e0005010301864801c0328440c00211640c3c00c0d2582040101500112582c1e03403c80e940701020024802c0c1402154024040c6801a5143c5909000800c0c030b08010460082c00e00c4100181c00c6003004540c16403130008004007000c1c1d9450341d032101040c1c00254000f140c241c07480d600301014504550340220740c01c000001c00800808403880152415400b03504080701c00e542c80c0d541c8ac6030006843d243e460248c4e001601c2a11b0000711b1904100000d8a01803061b04501241001403040084401424000111030502c900c40404a81e45030b2908462641d00490000d4016a9562001c0c801076840100c404035428658070a02 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 835101942 1250 835100692 835100719
    0x9100b0a120b04150e0d0e061902011a0d08031b0408030f04032310110c0703050c0405070908030306010c060f021c0b03120f13080703050f100605060a081f0b09 70
    0x29985c0c10305096515800c1400a01809406170b41018120f207409426103040903034030540022004520621000580d44800d110200c5a0050b1051141c04808030307038050b06120143c581c1240c0b070000806840500b692043e1009207100740c84142d81c020010042265a666004440800203801030b110844850444ca00c1d00000321070610480c403080085800200041444100c00c000540b010042d0003080090801c11034a084100b801840301035401500140403072507600e001d00c42101c100805800402c41c0d44c200038400f0306000310450f9004802442c01d2541100c442c10260000d00d0314481c003400c00707480050300700e03401031981403045500c10031442d003081840b40100c2030645038101c000c0e44404105040200b0440c01c4101c80c0900030507000c01034404101a2a1641585080c1054106441540c00039080314030545040110915051200340103000407440c00300810694010103540509024040d0b00207800c4039980500c0c5001c0300708540070380c0007150392040340d4880e651100440d140500c03001103c0a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 835103192 1250 835101942 835101983
    0x31b03020d03032009010e1012022709010503071503110a020a0203010b1e060304050c04051810060501052a190203060603070b0412030e0d0c050f0909100b0a120b04 72
    0x440c45c040703045c0c41c0e05594071180c17020060210f2042c2c40340f400b80664074450305035040252010f4a00907a4903007480030b80440c280f03101a01c041e0711030312003841202003e005211a880200c0c81030102c581070034000009601400c0c0642c040c103108160141030140124401039016800215a00100c2c0250000c101e94141c91091000c607440501858008040180f02c0302901e0403c04011030f40240a01e00369070110501c2d4000a0a44000b035603d1507844840107030074580b15200340300802e810249031804100640c40c020000c0c0003400765480714071110001801901c15074103600420300c4981000b100b42c898009050f10070b498582c031240020f034040d100e807000166050a001845a0070346680030300701e0342411301d031890250702c0c40040e40d0100c0c00c1180c070303171410340c0d5507100c800c0c00e081c0e02403103165411035030350401003440402d1035261501d5100b01e5059050004080000c5907403108e12114800104802003214042614422140c9c0403000c060a00c20108082c007d0980c2c103070380192b102d030b0f07250080303403140b40b908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 835104442 1250 835103192 835103197
    0xf0705010f1a1e0d080d020a0c0309080a03020a120513081c14160f320109020d03030c02011e0207030f1d0d060b060d0e0c03030c07031b03020d030320 66
    0x394060300b10000f11240d0240b80c040c40c61a80e5902c60794040c0d2404103031120b500c1c00d90700070300c58220215490b212850105a042a0f00070040d001c04002070166200c44e0302c00030f6a03516484005417a11901c1d0500d40302c41c81c81402125003541070000001e04940d0356110259680070300705c22071020964030b0031034102ca03184602d1b040d2a29a20840085d401c000b00700c958688030909030721045810859007410300001a569001208900c0c00d01890348547c1c0e40c106c00c09500c65560210841070a034503040354040140d442585080c1c01941601c0e000035500d03e5030000764010245c050030401d040cd03120103500d4502d590f54000b48065842552144032201032101d042d03642d1003022500181c0b00e1080703a44d107480e50520358107082c5540d0040001046603414080882c409a010b14a450030312501c030707403442540d004204030100300003500b82c00852078001030540203a00c41c400b6000090000c2e03c11000c02001c0c0000c2c0d21104080d41d0000c2002c0c014008901c0d003e401080c0c8120f560360520001c0d90300305640c1c82c0890a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 835105692 1250 835104442 835104469
    0x40504050606120c0a0b0903012007050c120a23070e160f020a080c151f1e09020c030c0d05030f01150503071803060c0c1104020705030f0f0705010f1a 66
    0x151103103e406c00c10b070b08260360400040a0780540d41d03a24107011124440880c82003040c01000b069640e01d070305052190801031986100c07400380804e02d54007400c43c00c0000340102c5481e0401d1051030241801c10041446850103d500310072803041310340208690079603c55503802002d440350303031101d1145a0365081d5021209142c280000d83c004080c40780100d0420401407207070070250000e49456040d0784042800c4400151010090075210651482d0225500c4840b0005840000c071082080100300648880c4500e15001e01c403079143d004114044599000c0040c0e442403080c04080d544881c2403510010310640003140d070324071090801070000980000390142000000c0c030390740c0c826195542d440d00645a0700c41c014a8024803401c5101d0000c00301b200342c4100fa00301c030070b65074690b808840e140c203107042c22940345004140b1641c0b04200100000e04000200c40d01034040000203a103c2c40781d61414034143c000c00201078459400d14014820000c050780c850b40307083c402c406100034000e42920a000c00e2070003400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 835106942 1250 835105692 835105699
    0x70914070212030406020c0a12030c033c0906050402091308070809270901060602030301050a0509061302120712020310031b05060414040506031c0305060a05040504050606120c 77
    0xc520000c2d5103544002140c0c0103008400243c540600c00c10342c035240c01c041000c1075510320788001c21f00030003e5050060f011003d00c43d14044c0301d01109100d01494201080c2222201c5090010140b4000c24160030058050380710008100188181c81c18844050881114100e1280344a100002e041c06007800e200e050352074000c503945060640c4c40d510805513911208425511040805400001607515014400c00c1c20721a254000a81030a204081c02d583c1e5076005107040d50420320040c02251030312029a4116402290030b19040e0301d421001c00d81e0302e201610300d18100d50000403421150320030f02c0450390040000f595072175000544150030008030302044d1250745803680300082c00c00204984403c55041c04202504140703940d681c400008007568850781c8000100180c8040700400303868584a0294844415805004800c001c015150081810001b441c0d09155507100410b01940314058041d018003000b130010041c2d07003410305066660345021a1410f119214504600594440109003001100ea01a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 835108192 1250 835106942 835106953
    0x303080402041d060a09050d0c02030c090403030e03030702070e1509060f03030904090501050a1107030903080a091d0405010b0105042907210f05120f0702010f0204080709140702 78
    0x154200400341801443e21110382403094120784012906000e240e02600c65098000340300661407510038240000840b1b6103040c4003150003510096140440c0392580040100d5401c40c40c1d50700c510b800c0e801031189109614080c4400310401c10b00c5138001440109440b0324000c81d04c420b035076007000c0010051a0b6100d113a008215500410001c0c24829540031920703000400b40c078184811311000c2000c450003c2d000741c580c0e079112802c2c002c02480610604150480781c07103c1038508685518040c001c2074007444001c0c038042e000150b02c40c0346486061114050417039640441c606924800070b001017180141c805640551802c0c3c04042c0d550f0180044408031000c0084448488541d00070f0400109a0391441c03405400e400c204c9100040d043e00600360a0b00e20b8002c55020310f11080400400c0e20426100490910504100c242040c040c800a419408044084001c1ca295601c140480c0948044001605a5400410042541c02d03000c02d0b0402900ca08041c10040d40b05100b40d6105140750540d107400268000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 835109442 1250 835108192 835108201
    0x70908030f07020415090507170a050408030f1515280207090c030f062c070c020906060c070f1802040f03020103090c0e070504060807020a030207050913080313020a0f030308 76
    0x1742c22403280013044100c60b6180c00d40d5030307914030140c58007150b4110000d0303000d12000d03c10100c8100c0843d041000c10388100305620f8281c0c1c898410b48000b40400f0748072051603000414540280c81d440700c810300081c10480f41d0300b0708840d602c900c41e04525003040c030103110501010f69031307015000000048641c07580280b000c00d240510b00d000030f03d4121150f40030552620454240d40140d0b006020082c1840c03103c110880c6107a000c80c02402a210000b02108000b100074800001c2d0302c80000091990125944229501c0d4040010040e1080301100d00c114003507494002500048680d5000c03c88081d04000040d407034039035041030700720b101e0b6005158000054071020b00240d48294410b043c4288500500000240c4844c0947d4100702e08540030350001728002018010164000a91500401503000a20221156550294540d00c490017000e02802207100080c0307030081160400c5c8559034014052607620b08004040e4000d2008040041c5d010fa0001d00700095040e09100d0800116134050b6621541d80d140d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 835110692 1250 835109442 835109449
    0x120d080601031a0a060807030b04050915011a030a020313051c030b0607030c060e0109051606021501030f0210030b061b151603020f0702060f0d14160c0203011b08070908030f0702 78
    0x2028003010105980c4000b42700c12510317280301c1d543c000c142c5000244800c1c40381d00e000981020058110750a83c0e660f503154a800b1000d0002641e030800800080583c403540d900042c03070b0b030303071a0840e502030808e10490b14404007502c0926503054020707640d41e605010390071074842400001e10543c01e006002035032401165012800940c085a41e1342070450020450b2001522020302d0300c1490181c280d85030f102e4240420003039404001300d0143c6c0c40144006001507255407140c00309071020300c80c041e0141c400b051305554010312a500c08600140010081d503160041460914a090000400040d00740b080c0b01c44c05c3d10003081d80001038803c07448000140c0340124120421006908100c43c2d521a003c0c00f0b0020300010303500c1c0c4010b440341c00e29030040c160700c9290304e116080a0b80c814000c00760402c00e02d4401d1011503030340078401c0c3e541e0728a82c0c100803540c0c00e0544007080c01854104071030512500b400035207901c120380c0460024096812039031801102d6484008042d142d02c550350010104440030003c1c1001400d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 835111942 1250 835110692 835110707
    0x90d0209040609120f090e13260d0b0f030610120c050301060b1c110901051b0703060b01110d0e100c0b0124020f150402120d080601031a0a06 62
    0x10b11940c00441d40380c0480d40c0d204549903c804525020609800c145203540394048000d40040946626090300ca003414011641500f00c4280302034940384043c02d8044040301403040d01c0d90500c01200c0d81030f950301500b103441001400017a00144c45589680b403010300768900041c4a900481c8840d0020084a10f04101c2c2d8400c02010035044801c10489000021260f80a1050000400d41c48000640c2d500204034125000300a2046c400e240034500b513444400c400b4210103a0309003010a081040d5160622480c6004a0007644000342e2584500d120100401003250880c2011013403e07262a0360f20760035011429269121150254001444600c071200d1600d0055030000c1400618100522082d503103446030703020704001340c001e580c051030034148900e4415014510f41540380010b2018000d21608080d02c5511452401007010b0100440340115040d590364480070f90050300c0079011560a1419031380060301d8200100d0f0324a010030f14119004000d01e8131007465040101004000c100f2050810205581d2003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 835113192 1250 835111942 835111951
    0x8070f1502070b0d020a0801150f0806121212130b070c06020904050a0c020f0304230402040b04030c1d0f06040903110a0b06091e0406022d0904050c090d0209 69
    0x10701c50b010002814201e24401400142240000580c0c1e55945e030303901401c2804183d0001c0c90b09204201c00803c002d500601c0d211031040310f0310f4159a6a107402d4009040b07a00c07440400180c50280c00b22103d0259082c03002001106801c580e0f218450303032181442c465a201c400c1020b0a9107513030000040019201d248510742080c4902401800c0200d20b1001c07804440701102d9641e90745660f2203040d94016010000301300750141b02401189400c0c2047c144013030701421080c100300182c1116095540e9642d03150140d4001c2d000e12000207440c0c0f41d4900b00311080b04014400c82c589024488681600d984012910b503115a0f042d005410082d140d134400d100003045105007c0e07007040b01e2540d088070400820311103007010901804240b221428020204402000c3c090082100d41103603581c100c7e00c0c4601321225543c000c1d000300006032120313600d17081c40e00e991440c5258030200240c2814802c1440000c440504810002a241003004e55900d44c0950704511842001981c4007920800000045ca0005100d6610 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 835114442 1250 835113192 835113197
    0x3041205030403080705030304020111030c1b06041203180503010b100c0c1e050319020102070308070302070e01060302040815010807120c08330609061314041b08070f15 74
    0xb440c0e83c136103404040340c20070b201c1168280c1000052205540e03200e00d0400004040f24051031030000d402c80848c0d0360342d12400c51010004101e0b68180c103ea540c1d802136070020042e000403140c803a4028074000340b024280076100b11b0400d4240310041400e083c14400d141820001519401d00c9a40b0058256800341c0c4080040303881d41503854001c940042500001c02d00141e400b90300e414001d00381000c25080844407649803d203503521010782c4016030383c0042d0907001c0b250012152591019142012804c00102c8d030000c7c054802e80b04000180c0e554581d004000b100c40f00303001d45e407a40c0c0400e07498000000d028403501000e640446801d0226111170008840c0e00d42c480d0744010542940e0354040b900b441c0041d0300c1010803c84000c02c1e0381c2031603034100c0f4207000741440804130100b07458040700264825030040e00b40740c0136540c0e041407403220407000c0c0e00c900401d00d059007003441c640c64940741032055005c520601d0202c0960f0700750009404200080d16400703542c884800130300b400742016110300e840160305042408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 835115692 1250 835114442 835114447
    0x142103090a03050c0102010609090f080c120a082215050606070b040c1403060108061308041e0f06050c0c2701030b150105031302010e240d0f0e0304120503 68
    0x455a5601c50038401544903402400403003442c01c002a084524941c0003019442c10200300000041030303041300714241640034407150f4a03080c00040191820b02c1d07681c002201c100c000a2101d00603600180072038801d00022661501020041c0d488071b401d0150f001c0c00420082c100181680740c4a0940c1200e071340150054038042c103154558641680500099405540401c2075074428852183c6c51030134a292450280c0051109501d40000300740c0c3c840000309000100e051300c0c400300b42003001000c101d800400201e102244120548619441403101611034120015000790340014494040c1080c1c540680100c40078028000f0300d0001d01c40c0f40300c2012195010b50200c81056200e00c0c0d00440072a000c0c3d400380d0303201441803800c180840c15903000440c007241481003e2041040556001c004011a281d080c81d04200d00e003040d1700170a840340383d0900c50004902e40d9414148089169001070105d280800109210300c03280d545c0380404031400c200c5003a09a0708204130511000360b5045241160340d115070203d0b807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 835116942 1250 835115692 835115707
    0x8040f1202011205181f050a02090618010302300603160302150d1803030b04050115030b0d0605011221080c0c150103080702030f0601140d080409020a09080601142103 73
    0x41c1851310960051074042800c0240c03c4c0034402c1b520031903a211424000441c41d103400080061036602981c6401511030001d00d5404030aa4403c0d010754510303d240100c020001c5a400281c0141070f200d10065864500f4000002440b514001400d8502c00c2400e01251203080d00315000d000c407a0081000300c1030f80c2c2001f001000c1990900c1e04c101400b0440303a82c0c0700207030840b01d032400909a698080041d407050342448010321201c0c1050b008109240564240010f0240740c880207d04070fa00c040c84080c0207a803900703000041003000d0642d030b2001c149c070800303da60750100c0d0240301398001300100418100062055000800c204031000092018103e0201107803407410a82110250f4013000340c1044030024001302c0c0707500860408002103070001e000000504455810030304d4501c903606140140912400c0d48840542c103000c0c43c80b0407240500104003080d96540b81c610006862912036210703400103481800000100e00210a0000801c2400100f114101c0c9900b0340b000320b00a10030071340b2080d45020421514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 835118192 1250 835116942 835116991
    0x10f08010e0c0c0c10030c02100c0e120a060504080a030b0312040303080421120e1c0509010306052701050603160e040e030d0c030e0a0c050603040804050a0308040f1202011205 77
    0x1800040f00c13076502080101203030400a0502027000c44c0302d4107541c180461a00c0301d40c2c0100070040780d00c40680d000c1102e49000e80346280303400da449801034025445c220900c410702200400a11901c4a01c2c1c806001c544482014581d035140610105070440e41e0601060000900c10f000c1c0c6500180508040642040101801071640488100c003401103411220450003111700d44c003e042100e80780e100900041c0c1280d1b20345030801004034000c0f5042210000d01c186082c1e000394000c2e40234001c080c017102d4104525540c8071800400c99084550504003103000029245820b0701100d1151059501c5024001d5502c501502d641d40482025503105072540020307006403504001070094855024000f20702e5034034000015084811002c12203145800150030300000c11409990402103075401e031f9055035a03a40b942400b5070380d409030fa0460381c4d00c940003040c00414032480101900640b604100c03050070807556410b8442d013204d0040c60082c0482c80d40201d660080c05c0740d6010650003462a85d480e0078041c0401d06c10b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 835119442 1250 835118192 835118209
    0xe040303110301060305090105060d120807140406091a0301050d11030c0d080a2a17190903150b130207050f0303130506010e0106020312072705010f08010e0c0c0c 71
    0x13035001a5685003000340b0b0000c2400380c550800300980f2141414001c0b900c0d4144c418800703421b0340d0180400c40d40800c009034810012886400702200c5841d443d0707900c80100a010b010f04d132046c01004100c41ca401c480c8030b9510801c0384d048650013411509006803941c0c0f0405196070014001d58035009043c0395050540f030303406080b00c1c0140304070700716075541d005132101418800301120034081a0140c1c1c0105c02c00c050702034204501d56504080890400494100b100c1501d11400003021500d51100844c403150a80050346a410340c1d115244800ca0003204035424406c0f62149400c00d0307440038800c1c0000290780556402022124051400c0c0e610415040346041c0c5148d00a8030134082d40c0c103030082c009061103405d20049026081d510305412595261900082d540d01800502001010780e01c400f0880042c080d0302600c003100540c4003901110780e02e04840000d61400343c403a40d4042036a000c03402544501c81c10310307030f81a02c401a182d0f80c5640c03610862210a904909070383c000750310030080d64030f46c6996182407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 835120692 1250 835119442 835119449
    0x409050105011d010206010b09040216050a15050c03060d02061303150f0204034701090b030303090a15020702090c2802060403260f100501180e040303110301 69
    0x855594981000188844081e00a074100c1c0b03004183c1c0c40c0482da034007055450444d041c55640d03a0321829000c0008009105d5030b03180e500c18206105003a420000082001c0f6081400b07819059941ca002c1a0315a05885d000c407441c0410280c00c00028209280119400000a002424041c02c0c150611140106038145c2d4106851319900d4074030b13041d91015107008280d0b004004940035401c051460703642040820140700d0402c10920101c24404542c8801700600c40d1b52002c400811040c044c03a90781e04000c8140a01a0b05003071401c00ca50100241000800c89014102c01d000070000450035484592461004d2244646a00c4d000c000a0016030707150b000d60b6005000a05807150388200c107082d44400344420143e0b103250b40d402020184151500400e003036612030b4060401d036081d000b103aa00a0044045400b00c07900550802050144040c41c0361002841411032500501e542500d4078010b440e907141d0078065140000c10344105001d0700840e44441900701e442424086010680c0351480c43c0035810980 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 835121942 1250 835120692 835120709
    0xe0114010317120a021b03040605030919050a14030903030706060f12330f0c03110438040806240a051c0b070f08102d090204 55
    0x2001032007403000140b81d08000c40000c600380c914201d0800c0d54000e80040062920302d07801ea0118409241442c01d030f02e00107034008204262590755880c2d00014005030016900b0306540c0c45504181c1a900d8201c070b4104661940081c010090745079103035100e03a10600a140400c07030314001886546c0391071310108084c041041c454040424180d06042e040104120b540c0e100001c80fa00000340c250226400c8a9039000002c40c2401107000c80400c4801102c00034600e84120701c81529110650204081941c80344005500654050040c20710130f90582140c2c0c011070141111040360380c4d0400d4990310a80d51814840c04420b2001d4140110000307191280360002e510841c400d030818020801c0350b885410ba00e1300c10786441e080ca060014018000300d481d05026000f00ca000e1f220105551304000911101d55910550198030840d0038500003000601349450b0700000300c00f250400000c294510b140c0c0041405072030880240044c0f181105950204c015045080807040f02c1d0407131000315908600f400104050b01c440b8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 835123192 1250 835121942 835121981
    0x60803041712191e0c0311010c050418021231050d050705120d0203091c0e0d030e04110903010c05160f03090306090c06090801200334081003051c030e01 67
    0x11b0801a200c3e0421403036549459150a014095030b0340c00030143c3c1e042e0341e041c0180b00c2c8079031240c52550000f4810043d41901400380700040100072486003005518100c7c510704801d40a0300610081d1f02410342d001c0d40101150890910501102e2044000d050024007807400c40b00b14264118084c1c40660180c0b0740071881640000070411088001c1100f030030500002c1e40390036221442094001c11600f15a072915118107880100d080906100b50084200c2100c000d00812404a4802151107590702400c3d14034002d500f8030503500c42090181e410340301c5603c0541c0354015100b00f1552030040750504164100d00b4171000307202c080040b86280c81203010040c0f02e422546083d41c10f00e040582400c1080c0c0c031440d80c980c10410b00207403008129091344a41c3c052411055200d8440301d503403660800f00b00f0f4921a03c45014011032501000c0c3c100400d40d2a0b401e522616403a891340031a81c00064050b00001d00241e0040c11307118a0000c1c4100745550601452130f00141c03400780030398400d007596a10300c0100031035441e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 835124442 1250 835123192 835123217
    0x901031b05090103030905010c170a090302040c0c021c031b0501020309060606091e03070b0f030f13051c18090c2705130906060803041712191e 63
    0x4402110050710084030301148a62440d940140140c1ca039001d0300341009103108030313a020016441a0708204010001682d6280c0c00e65460007801f9120510069118a090a408400c82401171024000c1e80d900070701a07608070910503a50415100700203c0443c01c1014248600120000c1c0c00208020760b44241c00159a0342003082d880c901c0d01c94083e14049c46080c00300304d241260f80d11a4012138501c41c5001c0342c20042800c203030009050040590044222a20028079000c07101c5051000354401e14004644021644850030314010303076115000010000d41c80038070042c0410080d00b692450200305880d03c41c0300b2030782218200c2c1806140c0d80c88407001544803030505840035080014070002d6851500c94104070261480b904034110118401c040c00394210350001c018003040303a001020000c2c0c0141c410f0101503900c440780356995100e4420782c4c0c143e01c20305a160080043c04030b200c4040700c0000c1620b9042500070085e00640d83c60b8000c680d02840f826600400400b8001010913800b65480d80b200903041c5070703 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 835125692 1250 835124442 835124483
    0x309030d050706061406070f0620070317060607080d1e06180c080612120f0910020106050310111306020d0e0a051f1107080a0c12030804020618090103 66
    0x10140c02020405000445100e17843d00e40e041a00d9001e030b045140c0c54407201580c20004024030754014602c1410308411000c50004190a008040312071080e0385515540051507000d111103841901c6a9030300003020040d4030080b64503600980508110b0190004420140c500e000c80b41c4048004da0700d0595860384c80070894004007801d10f101c1060034481c00e0000016045006121600040049120b441c0d03004015400400400c4802d44c0c0c03415950700146e96440418050304250045000b46105040101103c98400c0c410301070b0f4411690060000c040200c850800e036405031612805031440031905012901114078441c3d2058010001ca402520b00d154040c18003c100401c201c8000e8000c00250404000c142c845485240020b1204013450301c41c10b107000c200f100c4540216540c42424800c1d01e4000c200d5100c041641a240381c40341c8940c4003501c1d80d40840d010541c4503240042c0c04a09014002409410b010004024212604c0094100e1003107250010320059000e80003510082ca0748940424000e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 835126942 1250 835125692 835125701
    0x70b0a0f0e0d170a020102040308030f060a0503120f1b0a0b010905070507080d0e1c020c1008041a190c05090a0b070f200907051314130e0309030d050706 67
    0x1074141c0c1d9100399040b0644422210740075194000d100d604000481c4003919100b0340c1034401035903000c071495a80f828a80c40c07486d074500080d11a20310691540b4800641e51600080388031140380c0c861200350800e07038006464442600a1a0303a2038400d03140e044000225a81400718000309032255441191a504094601d4104c480081950f000c0c0a002c100c0000403c4140e0180e50320a02074034004140c44808256190038240e00200d042c0b045213184108841d20341d00454000d141d00f070190303104117500180c01d80440e40c410741a50050812003441c007031000750b0b080e1420016030100701c9200100c94519a01405002c07640035491040004d5004a44140c0d2403800c4000d035402041d0b140b8045003495100d40340c05d0220000303404001c004034804000e82407400c400300700408440300010980702c02d51801d540b019200358804680440221030b00138002c120a114190b2410038040301070040c00d132501450722110001c00c005480c45000344000d00481ca020b540401111040702c000b5680d0300c1c0c9500c61840d04d1000e49 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 835128192 1250 835126942 835126967
    0x2150c0310030b0c1e0d051506070f140304140406150f1b060903090503010f0501230a0924090515090c1306110d030605030601050909070b0a0f 63
    0x8240400a101d030703010403049900309581d0440a50b095030389906402c84002d00c10020904511080c0f540e2a0650b12003030030181c059460507003000d1010f952500c1d1410b08010b140442c040d80903200f8420400441c4400c195498402e110f8846065009400410384c2d141d60002e600c010200700385030f210300b5079606050203000b0040001c0d4510941c2d48c032038000d0240a020285031440204541d800311a031307484040b1110305092a801c40c0042144800da4107006040c0c200034080e442c0a0f44c280310488403445290b200d203030704840c1600c003075142d070b584d030b0705080740e810203011504aa001c0300003080800c0e0220f1a00c104000020400c811340d02c001d481d049607180961550f8800c0440c2d42c60f0404014181400e1880d8058034003049403084020b580f8a202c0540c6030194090101400011940106101da000840301c0c0c803100141c41100c02101c98003008070169122405030b0340c0c15410041c010840e0b4200344000a070001d41342e0b4166018280c03204800031081d0032007000c00b0002904000d12060081c4c2048080840c0b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 835129442 1250 835128192 835128211
    0x50c0117090d0503130f08120f1b09061209060403090506040b0a03021b0124091104050d03020309030a0302030918011413060f18060b120f0403031401060215 69
    0x640c94611401c940321246a04010305004000001511441c1c40381c3c042c10007a94440c01d1003c644030541081c00c1190002c4c00924120111140400c1d0039201c00244a0b00c0740c1c0410204600301100214900c9450b0030114520303410030003d12440583c0180007200a00c0390307140740000e115500d403900b00140044000c0e800503000b03001c00c100502030b603078501045a113803035102d080159540c0c0071074070580401e0748100b00c02d45080d4a1300510190b2110303203041a6540399030b80d86400e550b040c0c4414501303044446451035861060400c0000704214103240031b4100500c0d002c1d0050700c3c104511030010a051808010f03049005070000101d0201c03600c3e0800b440d003002641c840b0418050b60500c40200c8018200a050500c6131610000404030503116400000160101c0e0b03510782d510f25660414013059003004070002c3e000c582480d00101c0d00c4035400c41582c1c00e5200740d05204078036440d0500c44001100c80900141c0416444400d25540c491440c51001d00a02582c2d00810f0020450b020f21100d100d00500b0b901d1301c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 835130692 1250 835129442 835129487
    0x906090f110c0607030b1302070b06040c11030406082214150112020d05010f0623100923031b10021c050c0f010c020313080105040f120318050c01 64
    0x100b030000070155071202d40d60170000780d0b11848000180000140100120301a400040d01c1d00030449a50522402108152801d10441910307480580f190140006130300e00980c420301040041c944900901d0b0b4005007a0240c00e48040f280070440c101910203080b00f40c070b1010810006c000b017103a040001c00c001e0816a129603400d5414100381e254030380352409019203d070007452100c405020083d4048a49600b10f03283c200181c0d6034400351189001010750203100d90006400e2910600d082040580c0c00ca54100e607941b0040e50301f0030030345000c00c0b09046085809640a083d0214545d1000c103c107a50042e115550400d071310611508111400060200c90401c5400401d01070000d004012080c010100141c00c2c12520ba200000402e40f40c98154000c81001d903081c89084840e00350040004c2003800d6091403441c030819258803040c0d080c0c80081d200104101c0e912032a40000c07400c20070038001900818640132850f141004d4008158a1003064240c503641c204145050b0300e9a000252002c02c40300c803c0d64001e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 835131942 1250 835130692 835130707
    0xc17280f110d24120b070e091609090915020307050f030a0504210c0321150302030d08070f030209300c0a181d071e120f0204090203070906090f11 64
    0x1851110000c0014481c10780440400c00b05030040011fa0410344000d41920224078241180e900c14a03241c020705c20100e0072101011920000d0350090002094012100c5580350051110941c002c3d4030080104003044402d200b4000c107034942e80000c60088050590108841c10581080c40000500940b0703140c030f07400b1140c1c1c810800b0350002d4221180c0c9401d07007411480034449892004400780803040141d0900d28000247c3d0f202c4030400147c0040c0d9000340c1c1110940031006009a0300a036040d0307071030340224140c0144c00185a02c26001048003210140c809420035140742807000080c003403402086688141c0350364541480c5030170002503095600884070745044515000e03081541042820042c881c154450b61585400e00d001110b0740d08018100c0d084980b400d03640c621040212510300354040e420b2030903180000307002c0380b1803c2d10080705802c8a184280840507900700001061001c0e400ca030140a90301c8001a00aa241328078002020044030200758103020300344810880d9819541806419410701090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 835133192 1250 835131942 835131959
    0x90910050d06051005130509120901171e070819180201030e0703020604030506041e0201080c0706110406030c0e0405040803060d0809040c17280f110d24 67
    0x8030200c82c0c010310b001800740c030350100e07203100901c968101641000d88490569240c400c02d0340001d200b03610707000035901d03809405400d9003d184204040749000407800352000d011a90742071205604818800e1040c542c406040c070220440105c11035038040451940ba041195600707100824400c4044805c4080100141d1400000500c0425080103410141d4070082c486d0700520810a50f0007540d0003d1006031560b94a1812036500d41c41110102e5038004042004002e19140c0c0401e003c0190303050f100c01120390b5440025041d2a08a00340a42d070380c5444415440304040100b00074000340410740e8001c1100c4070f03d6900038110350b4105145a018516080030000858541016260481e40480c4c428a45041c00c0c207150016000d450380c2594014545194244003a070003045000e48140320808240b0190b82e1003504052400d03010070840d8101c4a419903461401d886540508491401c0d0a0006924816001d110142c0c0e041042850603959a5410b03a11408110321800f4510462680810300703110701300b0584 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 835134442 1250 835133192 835133209
    0x1b120e010f0614090c19051b0703140303091e19030504051e0f04021303060c031a010c0302060f1008250f12061a0409060507080a020a0e0d0311030c0309091005 70
    0xc0001c8031b17041011900d1300d02c20003c0f680312107101c0d00300040c492152011035480c3e45862004942950b020781400c0d220b42004015284115604005400d000350303d10285076507049902441c2002c0e000d510009140900000792800039240280c5d50203807164100002c0c044441c148a00c01c0d9842d14148070710900695405558458440301500e002d40c032201801081003029005800c024016070030b040c0401000d80c0d0640c00120f100c4003094100c08007081e9140103484a4008410140c0180c0006001880d4604031803000e0b038000c0c00d8501784514a590700c2a5050078004900442d45c200c3c0c3c0001402031601d5007043c000005441c4104a44a280d45090780204003186904401407815858518007a80010111850f03000e0840c0507205002a5001b8a02140104011036102d40072070660404962161083d1007951041c20451f2500754651040c002000900c10000340120204103445840706030400c814400f401c0c034400140e00840c2c03102c442600300315144038000c3c40405608040c0100b00a555241e1fa003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 835135692 1250 835134442 835134457
    0x6050d0f03020109080a020d0201060b0c0a17040f06020109060c030b0310050a0f092303160b090f0f0f01060b09010807030b010c0204020c030a0e041b120e010f0614090c 74
    0x8505480c039100307150681c0548051200a0860100403071840d030081d40115004207400708640c000c05c242c41d11003417a0281802000d101c50f140d641300d0500400040e050385038007501d80c1114010103081565442c5040c40d4000a50800b00050751180f5480c0200140e078090300492040c0c0c0c3c01c003401030000c904d01083e074410031300440e011516118000720380040c0303650b030010300c41c0c0b51066000d00000000307017080116040340d4100c01201c0c1001c0341c404280d810b400f00a4455404001c41c02508100e016111508980400f400030384541c081d010b03905014910410205061055820160400c40c0c8000c51040c03c444541d401020310910401160b180c903a40000b000f13512080a00b4005103070300e070100040720714004404009401510009052410000000260102c40302660381c0c401d6003c0341005101c10784110304e4852000f11616905d0301d0200b40101d900794160004050001101c801880705c031030954808991041d0000d980d25018407141503000e1000020403002d450765400d0b410f1007003441049116050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 835136942 1250 835135692 835135703
    0x140a0f060e0603040f0f1101110105010e132f030706031a0d0f05071e14130903270e0c12010501030c170c13051507061808030906010302030d0306050d 66
    0x2000804225030a09410300041e0401d8014908281317910b4401d6101f4000c41030280422012146003500983c140501410380301d01e00f004003165200c5010310513000c0c20600d011944d019805c0c06185101400940e001101c8905038400d10180840c001410300307001141c1c02101c101410148400f104484c50200400c0c59039080c0c0b006501c10b035031030908241c040c81864000f81540503d110001d42d0402856030f1b0706100c86503148100900b0b54a038070881c0d2107203002050030f0304014803e034400d00c00e904030b40c480598140a402c10900e49641d015001c4135160386511540c032043c4907183d06201c0700ba20801c445d0b03400108900b105282c020022003d190800c414461181010f0300e4507101c1151500c5202e5201b210003203541800b9403410412118030740744c1c020030500300c8060403100c4005890b14040500710b114400c00c803505850140680c60b03550182c20010201c1e10303050b40c118000b000180c4042c004520940b01c0c080030b4589541903104040c24505055400e408042c107100c000c0c0855920381d00c8106d046540320 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 835138192 1250 835136942 835136947
    0x1180606080d050430030e04050105010c0309090c1701170606010302250c090e030d0509070e010b0f040b22090b03100b21070f090c050a0305091204140a0f060e06 71
    0x25041c41c5d0f4a204400c18120744160200f040c07608268110342c01a0f11246c040f101845182e8071040112280040f60201900003a00310004101c144000e40c04501d4019881c608881c4030144081e0661a501c0f00303074440310004050850444891744107000d105e81040003403038198642510801e09004c01a41800405003203030784502a2303010815112a14001800c9106d02071100911455081d0b480740c105041e83c1d45014240f40004200c0b010104112040c0e80e00c41440804903420940c0801c0560800108040158010000490310407c64409066000c22003248500c1c501c4660101c094581b1090b400014014203024052804d0307500441d03c1e1007511118130300010000c10420000da4803902c42110700620007000d41a8111266000c203541c000d58005a10300101140d8510201c000c81c0c500c0e051407030001f0b6003401941c0c030040c0309030443c0b85c000c840c4000301d54000c10b80f0070603d4819802a40030200c401c01e411007041382030400f80320b11002807a00310009a1401d11740200548080d101c410450300c00c2800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 835139442 1250 835138192 835138229
    0x2a0b13150309171305060405031f06080a061b0e031e0114010f060813080a08040812070518010207080c040203060a0b0d0b01080c0a0918020c01180606080d0504 70
    0x39511181082d90490580c40c00100e05440200e25540402e200c0442d40b403040303901207080d0501008031011208094000c0c40d2081517a100c000c0c0c10249007800a08454036240c000031018010085103210354000c5c2d800207500d50f03626180042d0f01c2400503801052100c10028039945035400b140041180c0c00344800302112601e8004a90b0050054007000c2c4800c01e1990004030b500041030705058103589550b22a640315441d16942102d80c0300107910010400307842000810441441403642a411506c0b071070109042c4920120480c180c000101d03443c41c00240013056007003c48681100340c0003500740078005022002d0034054216160040480003d00131078000021900303513261000140b005200801143c4c1d100d4074000d940e0300c050481c2c01d01c001d000070281d00c041f40404040408a0b22101ea4a440e480503480c500746240c602c000da822200c05000341e00380900c038080d01e4207001d52040441e221380054240d04551070604211005500040d9135680400084101260807900322020344003441d041c030508008 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 835140692 1250 835139442 835139447
    0xc0f1f180e18060714031f210303180206121302031506010e0105210a0209031b102105060301020409020426010c020307020114072a0b1315 61
    0x34940d00140d4485007a10800900c1c03070b82006500c0c1485141c81c2901c00a0f1075068085610840903150003000c0079040010a96903000f40c038a000b04404451170a0b04d8607a960114085090402803213081000f0040f8019400c050341846410b100316158201c221a90800781c000c275500340541c41031541c2c1122131001082d040d44092081c0b80c3d80c50b9004048070b40340c06050a8030a50307006c0940c4c1075400701d414210009010340c0103a0589550107015000c682e030360486a601030b604400e02802d0f000406500300481c02664405002401030302c10b002150005030240901804111010502103400f0400c40e42c0420036240000907001c1c01c50030304142c0205031921441c002a00900c01c60384109003843c4002070000305814800c2a00d240c00c8000c240c0703612010342c840c1c089030030303940320703e44810058004000740c40c019070140c04442a8220398950302ca00780540f90341e0740110345008204c540707003035005480001c204a02c523100310b20107084480300c01810001040c0101008144034022118a10442e5405140c20303403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 835141942 1250 835140692 835140737
    0x60b030609031608090f060313030801080d05071e060e01060e010801142d01090e0613080306060d020f0307050702090a0605010207060e060d050a06050a0603060807060c02060d0c020c0f1f 82
    0x6c0300501e026901d052407003545051a807003c404a02250040c0000150340d07001003a00281c0b224070380c0700d0914020f007940c0c0c3c15000c86444181b10300c0c641306004480340401d14620581001d440c104000040c09410704403030b03601e00c40c0140c0c0005800da05016686041c25420703060144c020118002c80c154004000c501d0001805884590b0900c1c180c40d030000184c140e941c0d8011516582030170040e141c0c940c5030b01030955210081c040018002da101000443c0143c1483c50044c40780c1084120018100215210070030f01c90741c81a0f0780080000c20100b041d50652070030b1140c1c00e4220180701020086c1515003070001c0d44918a0f07200389004c0c80031041da0700c1d4654444904950440302d07440420002c0d49010410000209450301500b802898004070114480d40244142816603007554004d18507507103420400c0715070307100d60344080340c0201c0203100d141824840c030f0081c0b0107580440d801030010a40b5103814421030003400884148190009221101d06040542182520760b2944c903003400d9543c1418034100000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 835143192 1250 835141942 835141969
    0x60c25111302070f020f1305091e060f150103060b120907290a030e0307030c03020d090605120a0b0d030c0605061e0d1e030c050d08060312071104020403060b03060903160809 76
    0x28104010000b0341d45021807840780d142b03860406850051a481005662103d04484290b180300050000c102c81c00415200750081d140705260200b82c85403030311455001c0c1e030008410802444128000d001e04001d0511181000d04405e03101d00c0002544010b20411a0740c5116880300c0e00200003071680d00d620b100e60012058000b9027000c4075580c00392460014601002d811080d80140140048020818800d61805003215495a0343d24207011010056001c8400041c0041d03249030394680d1014069106c02100d0400140281c44a08a0707210b5401d1140135540028640d41c418106003070340848111810010705ca0f8410180c50301c41e02c840781c1f450403a0890b14800e55940a001599940004150340701001465451040007075030341704e0b000c00005076903500d010307115143c0c103130000c4202030010f00e100405400ba0f40d02604c4c1812004201d400070408a078440d0b001910805e85503511007060307050400a00c0c1d0030072483e0f0000c0d403070640c8204180f101c145060b80f0080426400040040d2140c3e54880320408a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 835144442 1250 835143192 835143229
    0x316050c06030c09030106060e031e1c050406091203081611071710090c0b0a1214070e0f010e040f0617030306010818060c25111302070f020f 62
    0x81e8100007010072103139007101044910075820083c01180c11440380500e10860000070340104030040511318031000c2c0545000c4d80c0b110600c0385c0d1000c1100310050211445040406480d06580c0700d007821401880104250411100c940f08600c43c000002c0e4011b44203584016081440400c0d203080d2002215480c0041007103521f9489000800f0461946558030140747c0c2c22010101d95400c4900000d0300243c400c403190242040d020351604000e4441518005c0c0b4010507039241004030032030003900c25011681094074541c9401024400c110300a0340055580300c9883c004c440410f070031011000024400c0c142140f0160040b81c44002c8510b004c10660060006000e00310352000441080054ac0c5903a500203c807440c0c00612042c0c0070a58482c0c15560f18005064444081c16180c0e41d41c280b20040b60b03120019485480c80c8007407802c24140c080340ca644001a21038400049a6000d000410030300944414011b2065841080040300141419480c4041641c0c195101c521500340c60002507031002e03401004044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 835145692 1250 835144442 835144447
    0x3060c02030c010f020a09050a03110d0510020d14011e06030213050409050a0611040f0303030203060f300d1b0c0515120c0702010c0204200f07110907020316050c06 72
    0x1090044c0c2c2d0050311507100031f90340360107045070b5800410120f00d80c5488043d10007000590355200f00c1c100640005942030065049541c2540381810000899100420032091655505a07918010700d10030103d50040c03030a00c14514003500000442c00192800d4402c000038554005a008050b190b041c04020050038020000c20401401d4284962034810700e40e002c990642c904444000c450980c202550245c445003080350390b0450441d80c0039002540301800183d40170541441c1c08981742e88120100303007031868540702110b4038200042c3c00d07007000403005d444440b0f03034000c1d585003162154864000c004030301401031004520368907820060118002500243c1c0c20007204400380d001400c0d40401040e0b0845422100c800c566250f50b031107400c81c0a1404000c1c0000c030302d2058480903141070340011040d06c0352500d0090349803100c0b00d8098030560223001060828000458030034240f22000011606154064800d26128580744c00000e480b0300c90040d1900d4516251900e25040c44420040342510800142140e84d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 835146942 1250 835145692 835145711
    0x3030a0b01020f010f1d0a030c030c1a07021c02030c0d3603030e01030203150103380a08060f0c0a03020c0a060b100e0108011403011e060302031209030703060c02030c01 74
    0x292401b107a084660050310b12240c4116100019400f015640550b58405d40303d0050398101c58000d0103c6050b1034101d2003400c1c4e100d0919115812034012441c82d002040195540c0d4480b0300300440c280310401c19074200744090762a002e401b04070760014855516006142240005d10b00e60804c00e50000401d955520000a1080b00c4005802c141528043e4032100c1d82410f0350001102a40b208a440088400c5503407200c00031035020750090000d0f0b01704084101842152010b084803001d0030030b01495807000a0000e00d00d4142081030114001e441c62101a0002d890450380b40307104030102420009080ca000200c454102d40f0a038142d0303417414800e0040e141741102a090a0010740010540c1070310400400c0c2040e12a02d000c5d450204400d0010f840b5000d580e0311b003000a5801c03040130084c4a4055407514820780500c02c400c0089207000200c600006122420760041c1890605c401c070040043d43d60800c101003181c0c1d00040c1d00c508a1344e0061001c1081c2842240490540c016a140401d02d503003400d0046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 835148192 1250 835146942 835146971
    0x21070c030f0c0e07140307050c120d0b090103050a0209070507060e100501060e09040210090f090203091203090c090a09050d02012717030703090206030108060a05071103030a0b01020f01 81
    0x350100c0d40100c441d0b251941d1100c0c140b015580c800e035140400310300100d2081c083d200c28500030710b5110409040050400040c8100d850400030048204c9a60306030001d04060005054811085c01500c2581c05030541d41c191b070745550341e030740b400840070b4454400c02d00002d80340780c803600c00c44078a0383d4044800c1c48200c605d9507515a40350114070740404524104000032072028801c02010406c900c0050036042142c807140c09014401246140c3d02040000c0001c0c0880d489680801d01001016401d00c0140d40707107006c4210901b0320140c0004d4a01b211820020303c20084e5000420794040b00b4101e81c50140c0e9194401464001c102e45034004050b4041d03000c082490b02d40642c04072840b81c8050900c000d04075140c4008d500916416000100f0703080624002c80c8000304d0f41d0024591004040c00c001448000319000900c140d003003640a9159544003000304940d1613404d004d0513411500301d061044100d2820307050241c50740030090444400d103649045013807041e07208001180170309402100804c00340c803246412 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 835149442 1250 835148192 835148213
    0xa0b0403081213020f190918140c09012d3c0605030a020405120a03030b0a06080c1c32010506040315091b050102010b0f0321070c03 58
    0x15811980180340020710300e0302100c2010301d849030340204942d100550f07020410688150700b1141c980c00c0b42c030030754004c98030303d00c10b00c60300d505443c80009180c8e030100d10780780125801054080e42c1840b41c108480e01c669948031728145c181598512480c900c4040300584040c00c000d0031b003d004602e04440310b00c0004401d4800540d50803000031902c00032803241035115001007696050046145400500441004001d10400165810454201c0058a1715580383c1c001021150304041d481c0d61a002014400200741d01031107100e64040040d15842d01040c074244002d41034020040c60041c0410703001465240b17000c0b030089680c00312805058200041c149010354011034038844d0b2800503648170752018030041d00c1c489a48503812203100801e00c5240c80d007195980c6400c244a1011145c440c1c2d240c0b00c4580c00600d9058011140001c0b85d40c0c03040c8824074200c00242500c04002d4950b0140b4000303c6c1d401d180c0d0b24042070419a658042c0c80f1500c020f040400c5210075440f4010018100d0000c51740007008010f80c00c0d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 835150692 1250 835149442 835149457
    0x19050a021801030227060d020a0317032502061315050c04090b0a240207080a0506161d090c040b04090207060608190303180b1e220602090a0b040308 65
    0x4500b095000200b50710200381700008140200c8648480004078541350400312500b6517840501220701e10b580e40e0350b4120312142034003442c618505d1301004000007510300c20118103055503c41e610001c50b284940340030751240e00241c00a07031441e40c40300020341803241d1140e202482c461071060400607860301e00300c2160765070440c1c000c3c0c1d02c1442c200b06c07203030344145860003e000942e0341868242d10003558072020f251290b5070404800085d40505540024404018002d5504181c080c0c0050510b51070f015aa20980018180444040c0911b80103c51200b809108100b24501e200762020800ca0311280e0180c50709000315407003c0d802003800a00420440550f40282c128a4420b15080c024180c0710348104d030302d40c0c070024145145400f04003101c02c08648aa0001070002d200d070103e8001c11002c6803119003441c41e00700c407442407542e41c0c0241d8a10018008101550000e0080b050030340704000c100c04000d40e2890b0000282002c5c2d00032540620f1581d4400a1100804803030103855540d59032850012130300e401441 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 835151942 1250 835150692 835150699
    0x603020f011d0f03120a050c1504050309090a0213030317100b0f280806090705030709030b060a050307030302150a23070e131d030c19050a0218010302 66
    0x220340209500501e00c200d0038035020104030100744186003c1c440380d0288001540d130316204400144031303151a1240180300c00341803651016918503400d11418a8501d00c41c20a40484440f1810080850720100544901c44021500c400345030f200c00d20b007071000e40a40e0700d034078012840b031410000804d900070800b00c02c200800c04110a2655400001104104091194140003070b42000079512900901c0001d048135450000310602c56441c03a1103400b04400703c814101c0120307544605100307052400d1582c843d0701c060b0302e15186295142180c00186100e01902c0000c2144140101203440c40e641c3d0b10b2190041d01c400303001c40e18010303540d0030000d50341c000310200090382841100c042001d95420780512400c01030402400146004191444590484d000700340c6001c103c6a0b509038800c984c0c07004183d501c0002412000316400c1501c201c0c2201803241001b0407885a4000c00c200010402d0104404844154010651102007882d041c01810403004a10083d407040c2400c0da4103440591404105042c0ea0095 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 835153192 1250 835151942 835151959
    0x60f0a080708012009060a031e0204180911121c1701061803020108090c12030a020f0a0c030303110c030706021206040c0e1e04060e07031803080105010507170d060302 73
    0x408141d05030003c01807130108982d001c200301c01da2420f000000700700d0103569150014504480010300c03c180300000303225803000350b0000ba08008200704250a508400c001035410090402640d541c2030358841d2107200580030386d51600180030300d0901403101080200300d04c091481410b107060380040106035060248070b544660380c00081030380f5104040100c004c40010a0100000341550019140d24500620600d9148680100410680c4501c0c1c03010005110b0203004584030308894402a007808034403021100203038010041040420120038041085a0305800c4c00950401c81c8404d2810314071485281c04210701c0001520010001641e00815000d190b580c0c000713610b51164810401a524007a82001c0014245110901d180c5010800c000c041001c0c408190341c0d0700c4040c0c0c041020380b110780c0e0040c0c01074101d41c010003034031540502030170300300d680b000c025000e4080e01560f000d055088180036060410001050030400c10242507942c00c4d0b05902d012101e0385903a2030090b0a4090520f0b8002203024407100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 835154442 1250 835153192 835153211
    0x601021f0e10150f03080412060608011e0506060a0507060b2103090f09040302100c030e19060b041104061b0605150a09020c030d0b0a0e011d1506070b060f0a08070801 73
    0x5520300301174030740c04041e140c54545001c1c84091001010481500c605548000012b040b450922803072400c1101301c03201b018000d1344050520103c9000403c05c6002e000e0070410301c10744950001c125403180754414030002d65159a0004a200068070601c40c100c0051804c094182e000c44c000052304525108a0740901440591010300c034205c0c409072402005a0301c40400680181d007942c0094400070141d140006409a072448800c0c905080c3c0c1555010304890100748206000740e030b00651135580d00560f4140441c00b05090000c9151250388110700401200408808107409020036003d90750741c00581c140702030300700742c1c0451004505591810b0f00c100c15095001890205034001c1c0c032440401c200245003884000d044d03075070150990100c5d0319070003100c1081c0840d000d440380c41c1150203441080702d5807020701925281021040f5019001c01c3c088980400c0d07080781c643d00d10040f5140076611180354142605d0f4070000c1281041610621584a801c0c2c0a012a8690f400185601294903000003031103111103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 835155692 1250 835154442 835154459
    0xc0309010b03120306040203091203070c060501050a0b1c060b18091f0611160e01210c0308090613063612031110090210080601021f0e1015 61
    0x4011403c00001e940510000310545807130707401b45900c891a102620032a68803517480c0c0541d90302c21589100231030340181d001024040e8602c10b65024000683c1c6200c80d035420540700c0c00de940101040c00179186103164055590b004c00340c01c0a4002c0403e02c2480392180c0070080340d0600f8621a005150050114074001901d44e80c942c03400e10700c440c001802c1d40602d50308143c4210780c65200c9045a110910498a0a040384443c0034040c500800b0b00b041c2c040c0140d4184121151002500c01312400710b1002c407030120021524003248581101d03446009940d03204004004100c050280718144013681000d008001891600601c100007901c140b692070305e5203042c0d00244200d01c0c0100c1081d003013000414020a02c110584015a41000c0307020b800e056060028030000203213032081d0740a0060070301e03484608000450410079565036420043d41460b0002c0c0c030380351b40000e42d1003982001007140c00c0100c12444c4018045a4841c3d2492041202500d00071170541c507589005c1c0130f00ca491050b5481c05103a00080480c1c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 835156942 1250 835155692 835155703
    0x150411120115090f0207050604060b03010b030a12080a060308130e221401150f0302011418090402041b05120c0405010f0503071b23160302270c0309010b03 68
    0x5000d07405072444504020140c402403454403070070944c2c503a00308402d101140003085a00d20585c89840d01103080700307004d0103250958000080d0b25001c0da114110a40001703c000f01c0d0341645170464038201d00d4075aa25103109002d44a5a4409454a1000902c91504140c81030192082c0c6403000382240141c1c940c50440c00c1000b20702d290204001e0640b8815000003400c03200490780c6003403071000100e40c000b074500031b81f0829a00c940c444100644031030010021940c01180810054100d8038042c6c0c106641070742408414180000d901e44128150800a401c640e91680441a070122103510102100c200c07900c0502142d003c030307640342c1c0c00c440110300144500704002d0071642518410b940b006881002e03100c00741c0310341d00042c00740c03020b00003a42010b00e41d2600005c01d0031960b03401200c51910140074402c0394001e82c584107104a043d60042c019103224019001845411a039042d602c2c000c2c0160820f000001459041e0302c0b110760650404240501240040c0246001d85035410007000140d904108140d0b451303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 835158192 1250 835156942 835156961
    0xc03070801063002040b040b0d060605092815050408010b060901051e040308030c070219050307050f01030e010204060c031d03100b060c0a050f0d020a0c0e07021504111201 75
    0x241c62100080300c5003029400400d81408641070242c05c00d9102c522100480e0020f800035200d800c8081040c2c404c40c0b85600817040200807e050043c1f60154110200329a121001c0664003500b000d041006034064400040d00c1c018042c90800d6078102001c1d1000038003a6001d80300311001982031000410040c5000000c6408801d0305845051612202c030403201b81c041011888400d107400103000c0000030405480045210300080340c0400c0c0d1340d5000d4030400100e043d043d0304e4101100b1604406025503280014080240c480c1144c04030411028000101d000e410070b0345030400c25500100700040c02c103800c40c0500130303054800d8490f19404201c040c0d00c221040410107081d9855800115101100b07000c5034062407c94901030b140ca0f00c0c012512202c03a280072041c0c0822265070b489584040d00321030040c4100c0040e0301c00780c03000e008800c540d500c0701c200c000100d010b0211488680404107101600030060040e080742e581c1c2c1510020701d882d003400b01d01800c0d110f1602e4014001c140c880301d034250f0103100d4810310 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 835159442 1250 835158192 835158227
    0x314010b1207050d0e012c070315020f1602030c0d0c14010504170a1103150c03070c0b15030714060d1a03150a0c030501080607080603150c0307080106 66
    0x20070001601122418202a0900e41808800c0010322074689040c003c85039180000340c001300700c000103010a50708091030403c5c6140d5040344641c0c0721241d83c074041040011a0f0b002545030710b0444840012030001d00c28141c0c214824540014419003a00b4550300200c3c14034021400e81d14050706110503c040039071000070080c01c01c600e0396014400c0c085140940110098103240c8181402e0b224046105001d050010080b9240d002100600030802e4045880401ca1401c0c1d0107440e9141c1095510a034000d0003500302e5182c00c202000044c9010311030000f01400d585c00841c41405030511010780160030450341c1c1100c3c000e0144260101c0c0d1741d0a084c080a00008000d440d25142c00c64101d5890000c01705417420302c44090180a1040b41550b007000028461958000d0004450801d071040b00100e4111120030014103007804010018881e0104403590310101e24200f1004030754032000001e052800e811000000103003c0310911103c50501e0024600c1602e1640342c00e0310303e9883d030380240e031495000e008a84c403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 835160692 1250 835159442 835159447
    0x70314160207052706011107091a060a0c05010f05040c05240d15121e14030403120e030c0a12141b2403041e1202030a0314010b 56
    0x110500006040036245464415161501e80310400560751061032540d10180b140c001020444449090f0500d681105003401c0c2000480c02c034608407a203c001c0ea1041c1401565a00030742c045803075400245d8042224010040c640e240c44604015102141120041c6c880b5843c0003c42d0301c803102c541c4291400fa540254400c14111300c0c0c0001c010020700d40000c0624141320011002d01924100c00181c0981110501d011518088090503100010703416485410f0031200640c00a020800da03034a904400c80101c4038034666410039080c07a07000030500000322661484006400000c0c06082140380350b032a0f83caa500e4040d6481403004051740e488181080079484042010100f00f181304038a41c0070f032207520a2085034450312000ca0035605100c04d260f58042c0204584226400b10702d01409a02c040150105580e25442002c101070026800000c1000f0b18950500c1d501d280c0309280c4602241046921540c03410b2078a041d480000c1d141d4004480400120381000d44c015100810055003d06031680c4006090 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 835161942 1250 835160692 835160701
    0x4051c1101061508100806180a0209160e0d1e0c0b03070509040605040911012006010f061e0c020d0206040b0706091b050d020409021206090a050d03020a020c040b01091d0609070314 79
    0x8d9595401d82010b080c2d441455060030050b00d4200c00b59101d03c034130b10342c2c200a06041c2c1ca000380c801038607040864403030b551a151305800900c003e00c50110380d8117040c1d03d81500322858a8280320800c0d25422100895901104122110741d1001c014050300e00c0656051224554030018030041d100171000060030002a1690b01206510410b030088104004800b15902e4500c4030401c181000c900f0303001590038042509040c001e840e0440381c0014900b07003415100341c4100400c40002c0041c040218024461404009240700703560311041507401604240074000e50781c0000b460180010b055900e81100c0c1c0d40a441011060200321424200c122070002d8500c404051030340d8200001403400c41001c0f0703840a003000000200384420410305118001b440c0c0240790710207660400a03d8195450340203800c0600410001d11442d50100c0c080110704000c0c0c501242d40314a120050b101c013030b201c2d00a0500040078a00c8e02840112000c0355901841060b12208656124100103c0a4500840e0903020410700703a00813a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 835163192 1250 835161942 835161961
    0x7050a0f05010c030f1404090b040c1701031407090f0905010e120924040e07020f0d3011090a1508010b0d021215030d0804051c1101061508100806 64
    0x300030b4161030b00c4400f840b541b602e21100da0b005a0060f03e171041c0c1d9117000d440242002c1c850360361904400e09018983c000180c1c100ba0065405000c01004148284600340c5440d200301300f01d001504000d041403046055491002e4003c100d079000980780d540c00c00c40a40c06c10403021542084100c1444a030916246024060007c01c08411058a250803100342c180500b4a4a000181c000341c60b1254400405041500c402460110711251903551500103c51b60088250882500000d4880700c0083c440420b02d01001010b440043c0102c0d009024240b00b8490300c0a80d02c4070003011609070446400d404d1030b444000d032996030341c03415480da408035058070b005000011031100680a12814903d02628001281075000d40da1102610403c5000d40c5188118400349030501100401505604c1c00041e14075051300d1302956103c041981400c514103c4803085001c0d03104802c43e00500680c0b1001f40409070b55900031880c1060740c0d2561800040f400000b0546607064200e03244201c41d40c1c100200104d40b510400d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 835164442 1250 835163192 835163207
    0x20c2b080c180612070507020108180604030309080706050c090a06030513140715030f1d330c03010305010e0706120203070909051e06030d17040f1407050a0f05010c03 73
    0x200f64044001e00c180e082c0180e80054141c442d44a598503103449542070b10014080308400380c40c0da28a0003008034a043c20f070600284641e4480d03018540810740100e282408200c9108050000e414203040c0010401c031458111300400c1e40305420741d0611401e91f0307560701c1103003120303001d88042c3c02d25200d5408041c08241e051521184003e502015102841e603940e8140380040c00b10040360300800d45803410401c0c0ca41286c4a0310380d154010400300085e1181f50110142c4429120301842c0040c8112484e070740c11218102e00c0040302c1c0003080d00c0180c460030807444c14543c58200744801c442039820074940c1030380e0700c0b004620030040b118240c9405504042d04440f1002a41009201c101040b4640b10002842d0415000700b03070080c000c040350303103900b8550001c1c007034030400740100030030b0007a071014483d003070300c03d50243d05402d0020f00151400c1c0c071790301e403890032800021360301e8009004441104007403540c0300008a0103008441c02181c1c1d01e040c03030713942e5001d5040400280c814140803540c50b407075241c0401e005020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 835165692 1250 835164442 835164487
    0x30e19031e17120a0f0501061b0507051002060604180c0905041e060207050f01060f0506310806070f0816090f120b0a06050a050112020c2b080c 63
    0x12490601d1100320b6032540c0c5400200003904503980010a004004c0b815118040305045c1100f4240400e42c10000e02a2894060640e1703241c580318030842c45001d2203410700c0808040d2000400030315441d20720180003035403103505584040c0700d41c0c40c10046440b440144140c255882c0d0b0b2007450a94000d281840340e800400c0010001d94085503400b500c61100a159078000115a1040c2c2c401178840d5600d0901c1450104000d6004e01c040e0f1500000744682d490041d4082c0440304221807240e520070004212024002000540d05c81003c6004800c6409500f004d40d0402650880310480f00303590340700d50b0102c1f07101c0c125a05420104803580c010484a24120705220b240c0742d014241544000c2c1e485c280191211a90780c452110800001a49010008890132840c0c105043c80030134880241081d000035030940040c81880d05200400317550f29000403140d010344144904c200159285001c030f0000b000041a0300342d580c2150484d10184051006005004041c040c190352600ca604140718400c68141c98440c100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 835166942 1250 835165692 835165703
    0x19030806060304053a1101140c19020703021c1712040803070e0d080d0b09093004120309091401030209130c0f0509090a031407060207050604030e19031e 67
    0xe100d00500c65010204a8072800c030341e180c00c0e06c00c1060072501e01b1256150000c06a00c0580411720101910749400e031076000c0c69034031428503014600c85042c0c1c540a460342c40290440a03142d01300081030203440c1c00043ca94000d5061690070783e854a040c441030f124000d078030243d00809401141c003281000005d56031001840c205140100d1001c00059800045080115400700000400740c901d044c0d14003d01c0c10014003924250064280014003540300c0d03405960713500b042c0d60b402048202c02c500001c4101842020740402503640c54403070071154041300c0180c00c1980403d00c1600c0c0090585414411507840d00c070f030700c4403a512990a660030846a4a0060000d10802815403041004a80d1001610000b0424552050003031071920b820720158510050444c0307129001000101e000c0781e0401015461104d140060b03d5403454103142240080c0200e0748081d06a1140c902000b00701034001c00042c000541c102d880340d040004101214118500500000700420910000001d10a050600d50104c0318483d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 835168192 1250 835166942 835167013
    0xc0504270905030d090c06180302121905070f0b0909130501020409020c030403110a050105030f13080a0305150910031e020301090b1b03070f08060f031903080606030405 74
    0x1510340b185550884c3e0032601c1c00c1e640e280206010071260460840c02050241440d0b500f0fa0b0301240c4100c40281948006070192502000e5900c0c046001d000001842542d8032088503501524100141c3d14034240c001c101482254041c0810100d050100355012040c0040c9050800e5440c072044604007862000115902d43d000d00000c43c000206001500440c1240c0c3c0c010f40e11240755040075800c00307840603540c9001c1d001104051001c0d0b6030140440b85d20804081800241340c50b80c42404d004551042c5014250708408a00e00c110769030f1540101d07020b180403ca48000d01d0340d00c041005801c00003034808a4038401c2c81e510800004000703081d118991041004150100e07441ca402103400d5400924040342c00c004a0f104010540c2d00e449a9410f0600c00356114604500e01700b1001380c005182061094207100304c200000b02d09030f95000340404420780242c00d03650f0440c0e0000019134100700341401200032900c0000018024104001502c3c40344e40c01c00000e08000d41c65948214402d803684201503136242c6013 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 835169442 1250 835168192 835168211
    0x201060801051306050609060612131203020301181104060c020a05040e030703020d030c020712020f1806130908030c0f0c06040b01050f031b0105090a09060b040302040c050427 77
    0x2e20520f440303010099000d81040102d0302e0300400f01c800041100d8403d105c02020301506071a0380095a030a840e103540e269005460344811b54202c406c110a00070301315081402c003d02140d40c0740c2c0185040720290b000d084330f07003000c0c14440b10640c0e448803034201e0701940901c810032419100e6441c15030154005841e00307500ca5129004101551415180c40c00590700008004041550401041c420032005280800c41844280b2000752100301a12030003100040a102190565841e05000042c904004100302c100c00c0401c0c4203041940f50840c0d40e14828200c80035621201e510b5800380414035648002e06a15551301c12400d02019008076141a0ba060310a002140190804015140c025400b03413000081d290702d0030b805c002d4108c2d0143c0e22540a40c1118000c907a6480b000807540d40180700c00d00f49192902d0f8400041150110340750b126240f0142068400981d4002c0b0500900a0324001d580038410300440701d200b0b035807900c11803090140c00c414000201c0100d060500c41315512070072841d0042548000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 835170692 1250 835169442 835169459
    0x23030705120108030901090501020601180b040f0f0e01110405010503011e0b0a110607050f091018030c1701200904091524061d0a17070608091b060a020106 68
    0x7400d030000700c1960f0000800c0c040300d6070444180170050074244014150b82d07040008482c510880b541d0900311461f00c034804c4880035075464100c00b0004403201d8081107030804407035500024084a07484103009500e00000682c010407160215000e030358043c1c40e01c80c51a4a008001d012010480800860507a000c060200340140340000404040030141d44a01c0850800e0303401c06d0030010007401c0c650a000080292003100f0403210146d81c0e9000007129924841d1000744401c1e50318081841c0641c406003100d10011040207940c210b45010b5550b0790140a90b40400e203a14203080340c03910542e43c0a8400c3c058220010906800018032901c00c0180002c03402011a9480c2035082081d050101d07282615402042c00421052000a00c03450403181e081d0061032030071b00044c004441c12910701c0341208618506034025156200c0d11001412071080f28007031507024114003601d458040c0a180001252040880c0302c14400180c09000442e4501d884943c040d05003080001580c40621010251354031340100169101317 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 835171942 1250 835170692 835170727
    0x80702190f0f0c030b01090504020d0219050603090d0e0328051203040b0f07030908030c0f0c0607020120040f14120706031a01020609030a050f0d0c0507060c23030705 73
    0xf0310620420300850b040d8980070040d004160800842c0910380000c2002507902d105a19000c0fa4060b241010350f010101412100443c0503080701e5003028000040c410384000c0015046008401583d40030105e07642c0104058644803103642440420311441a90032010400216150340c9034403410840b1a003165071046400103030400ca81c16120b2400480410400110b05494a540030302d440c07908001c00304040d40d8134416404080c0c042046402c02285032000b0360303c3c04007214091000d030411030700246030038070000b8060445451544014080c0c02000c0660082030b1051700c0c103a905100d54500b00d107003403448000011400c1000e1b181c1c408603085107402240c806010540160400d69804100b100114180943c00560212510304540c4124200011400d021041d245001c0071403500e00e5481c0c0c80501c2c0c00001d405041c2e1110b12441c501021180c1703075a00500100341c22441020305010395442c4c494147c6000d580e003c2c030b03170400250070340c00000600d0034a0021503109002d070510301d04101d0520908407089 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 835173192 1250 835171942 835171973
    0x10c1d0f0111060702010c1b02010206010e1503010608030304021011060105012105150909120405100c05030d0b0f0a0b0306220614031b030d0c031205150a06080702190f 74
    0x44c1d5580c00e030b01a0507239009800e01d01d2890504121000000503900003581d95105114102041c5071000205002d100d00d0110a042c0d6400180240400c03925421640c0d2031745e2003a202248500a40325400d40d400d80120441c1c081d0504082c0901042c0c1e103000010344842229001c000010000714406019400b41c0303100362402014640b00350900c2300c00e40c0302445440140a0320910041d400b0841619455004030b01300c80540c1d00075101760550588564045e2880c40d0b40004c02040f500000c60891001c81c42607010802440c0115a0046ca500340c0b601440b10208031806092100e607003c20000d1074a0500c01502d5003000c070401c42d070711108140700e1080c20450303400c0e40000180d803201c0c200115251030200300c45a40401521120784014038584002aa25030749100c2500074000888400c80605010713101800c1c04110354038050203c3e01c1d04800301205c01c54417003e442d2040da00c01e4004648a8810300403a80b00e00c00940041c44ca80110b175074085040d08911350121440c4102e502d031040090602100b21100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 835174442 1250 835173192 835173197
    0x6030204090807020103060504180f140105070203030f072c01110d03060503060c040e0f07260103020102010c030c050a0c05100e0a1509081c0b090c0408010c1d0f01110607 75
    0x40f02940e10004041d0340e1558899446036007414444204600d003001c841c0380f61035111151240ca18000d141514a001404c81000082d500e0301f41004807294010008611601c40100800d601e036581c044280e070040813480719100190080c110b500030401503903a00000b14501410840701591901c20300070702c0d00c40d0500b0704400007500c800d02000181002c03c880d54001a0400046052508140c42403010300070040c03100c10100704510109100d9405049007192817a46502194440706c504010f8001c81d001c00c2c030080340150707c4e00d060344003845d10074842d0034500b00c01350356890701e81181d1000880b402d8032400021344860040190440c1d9441d1184203425103d800d060281c111480e15040c2030010b1104444810b4080e03042c01c45240008400780111111400485856041d600000b1071207801030100d0070300d42c2c3e0050301d80340038402200d160401030800c641c05da030002e000404901c1c90480d05801150119000369101c0740c5c0008891504404c1803c0c0e0610605d043c5104d119240b03d0030b8038200003a68100301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 835175692 1250 835174442 835174447
    0x60c0509031501050f040c0c0807060b0a060309030816030e060a061403160501031512150507050421050c03060133020319140c24070f0c02010201060302040908 70
    0x40d03604052192114054251801550300e40c508404280e410a0715440d0300e105a50b200d140e005c00600914840c00b00f585c1081e50540c80e0000361a04000618841c1949813260b011024006400d0340700340920000c2b241c1c0b50b07440190303540781c10b110354048825582136074090640311400b607140c50780308010382441a1350003000464074924251070110440801c02519000c0c2c4c00040d251003111a2112101040300e2080c07034000355019000c90544800001c03070b00b19004403003990f144402486400c044941400c0103c41082159403188101901e05d48141d1141c0d84011000c0100c410361100484016051140698140c0751000202c82c002030034960260040303040e00c3c40780300c914030150302100c010b0b00121320510700140140c44044000395403801280780303006800908040115000d4458080c1e4880c01c100c03504400d4550000e5540b05807980709400340d1103032201100300751b007603600640d100e07190054980345c42e0101d220203042d000712482c601c04801030b41990340719000080140c84a110711440c45005c1c071310054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 835176942 1250 835175692 835175707
    0x904020c0c040f2307030f060b191d15042d06142709070f0216050d20130219020d1407031e02010c02160e01060807020a060c05 56
    0x41102c040000302c0c00202d240c40111200e000c92002044594100e01861515a0351a5070084000d0200149100821230410b40e00041c03042091024100007003801e680345144100c07a02084421480e20401000501d2080700c0326030f07480c2000406511454880e4501a140c030b03882c2c64640030f0441040040088050b148426440b4080380c14a080000d1321181c0391910104140340c0c5059054000d0072844034041c4084652010030b0440091035040308035000c1e214001c2440c10000217081d41c0c1500751a0800b41c01020302c101d204d6070340340c040c01c1d09a80c6c00a0003840310840c0364a9811242801c22540341801c4000700d8241000c0e0354101c260014808410f01c0542c0c3d4401c002c916041c112582050701e4159480f1000d44413446411404130040224038800550b100c8826080c01c0b9000a0301a03000c15100c10441c1c2c505500640c10741203641802516001c448481030785003800d81841030244683da0003152148010301140384501e80c1283c000490344102ca1480b20117403114401c0300d0307040ea041c2004c141c0010f03240c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 835178192 1250 835176942 835176949
    0x11060a0f09080a2d05090603060d050a0813050402031b030c0412081b0f0d05090d1506090e070303050f090a0503190309150905040902010c0f0b040b0c07020d0212030904020c0c 77
    0x2503010315041400d152200003841018043c6e0148100f5984540c00c080006041c50700d0b018a81c50105410204a903070011007404c1c42c060f5540724201d10300c2158594140420070707082500889010314050401020701a9510b0780c081c040307400c0130b006160408010007000440f008001a40448540210302056841030856240c00844040c070007245c40980001c210440b003840b02003116501c00c100c5040c12652045440c0019911002100c03005003405501c451508412000d50f000509444240310200481d01c1c4402545903140c0e00c501c0014001801041a1002000450040d149210300504000c41c0c058850000a082800b90301c0404c1d10100402e2203c030078140c2c009248401840b80700341150300141e0420000701001d040e40200da000740d454401410459109000700000590803061920901d1103514040900c030005803825128007910001080f4800101c00440340f40640c020004440c01c0c0b01582808039004a1407501c07401c0e07000900c184034054503280028080c80180c1d0000c0c24100e01700380100b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 835179442 1250 835178192 835178237
    0xa0605090f01150f200102130609090b0901080a11060702040207150c080907030311121b0105160e210f0705151e1602100504080d11060a0f09080a 64
    0x32004001004c07142c4020b107074014146540543c1900080090012102c0e81180a40308002129690784011540012040e0b44411320b2029a20610b02c14031826042d0b1041200c900c0003030040201e0354105c4640140000c0d0051400300300c3c03040140401e0704299003500010100d1704000c43c00d40c2c3c0e034903198840080001841c8500a00740d10039082030752003414820100c1d82c0d81e1a250000405008040f07500b40d040d85003c10002c800032240303a0b4103e03529080c05040210b030070300406400d407156003808003080d40300b008282000315402d21551140c03540b001900401036503d80c8012103001c03950015012070800300b01480807d001e485090001c1c4011072500e03007072080103410020803242c0d2031030901180d4421000d003c165010350519041450301d50b440c604842a140c09244c0d0700941c0401d040885481d49904003001d0001c80c1c075210240c032001122101c0903a5400ca9480500c0e40a42002000448000791035204991200c41e01da000a840030059841207140d60003095200c0104051190310044228800342 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 835180692 1250 835179442 835179479
    0x60301060608010501030b03070905011d07050c0c0402090612100f080a211103040807030b0a02092b08133011010c021e030f0a0b040b0a0605090f01 65
    0x20850380c0d00c1d00340020301d09901070103918105600d8241d038025a0760100420400f0701141c88041025582d15041c021004c10341c038503014109444d160022710f1190007041035031844104c03140070f0324211214108000c000e502801c00c19274000c2040c02901200f200202400b4031607500d0b0540000018140710300c1c2e5040c0c0c1a04d50082c01183c1c8808800740000e5480c0395003035404032401c41e80c0c02d80b55020302003d490b0317025902c0d800300c0e15200c04280040c910000003050011207024440440b0343d0b888500d000170a0344030b0498900d810106035120710034903481d0180025602102d40c80282e11402ea01c0d91648542d9100030304601e60440402001e00ca0403071900081200d030b045102c04020701781d628000301c01159450740030203084110860551602a401074160300c111660040a283d060141d640240907840754003a0414020f201350075041110940018607034500b150814104212030380c66645141f52003800800d0141c1e030075103401000070240c9a40016a002c0c040141d4a1081d542c1001c2441520301c14801 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 835181942 1250 835180692 835180699
    0x604110a08031c0f0b0d0f0816031706010e0d030c031107060c0209130c03060218060c0a0c060806030a11040b030a03020d0315050a0905070c0507081f091e1e08070b06 73
    0x3920740700156104040607021b15405041d000c1302684d02d042c111401c3c040e03061605d42c405a0742840740301b0980c0c410300141c04412840e405a00d10340307444004460700d00c83c02d044190005640c80780c510100b03018191014085210b4a00400c00000541c042c6042141550007100403031071481004003145044c061aa5002e0b031102c52012050b482510340d03105041042c0b002421546d4001421451246420b40c1c2e00b101d039101404550380e9034049006503a8984e03500c5800d680020303192201241c81d621506120340074040c024020281495240c580e10303c4102600c030302ea940a6998150440d10784c074244408a10180660041c00100d0140100a019266010f9076201414810b0100b8485550341801c020241c0d4024200090241d80302070054407071f8080100040c00a1240d09400a6103082c0010351f0765984104c032640c0500c10a20507850025a02a440f0081c400740c03000b00c01e24129410801c1a04080740948941c1c015110000e1000c0029003618a060310715000014036030040c8601e8804c401e40100f0b055 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 835183192 1250 835181942 835181951
    0x19182d05011802090114011e3e0f100c0903020d080415090303020d030e1e01051b0903030405190902030a0c2006011401121a03060c0c0604110a08031c0f 67
    0xa000a00401181c2c914003010b4682c840712300911031088228001041840c0541c0c1100c2002044540d400181c400c44d082c400c05401501c0402a140494044d01d0007181c880102007291031300c0c1809001d031403846100c1c3c04203c41210700201681e02c2c0d1860003038080c05880c03026a1142003540c202c0708c65080222400138071003a0241000081e500081c103158503402450300040d51004205802d0800040614003070054500345c003408030016065101c80d000ba10030400d6401402c290b1440142c240c090043d1450b85900103220030005401c185032150303091110f1074020f00c1e0090315443ca6000300d8000340d0701941c129641d1065003e0041e0003000291441c15609000240041964100c2c0e0340c4032414020307041c201e019881c00d0030050340540c48a81c40060303070840910a04082c20105800c20450840d003610a21503c00411070342c0c00004116401c7c0141800500368039a01c80d140d0043c040d5a039600150400b608800c00a1b800c0001d001030302c0382e0005000407103c4015901601d50550301e505101410a5260 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 835184442 1250 835183192 835183229
    0x203040203061b120408090d1a07090e040f050a0218040b01140d061104080706051809010f03060203061908010509070504060b0a120207080319182d050118020901 71
    0x40f0b00f40c0c1d0315000102c80c0000281d6840c40c00c50924002e0300d5007103420030301e084400400c105000e0348120b8880040340f443c43d2503039217140301299404118807a034015182403602080110704034031032000c101401030701102c50246a5a0200740310303401d88641076440010705800c0c0030810182c450342600521007980c104140c0c9402c0000514004040c030401440d146d0f03100550300da0424240e00342c400601d0444180c60400e07943e90805801d6a00c0724401c0003019010b261355003020710700800d140741a1031a40780c01c0030f06c03c0d0540e52803100960018144075800301d500c030400d0031687c00e054400009880f0707030000800c40e401c003a00340a05e810b42c2078005521072814030720b0520030b00e08a0b0090340d02c850002c2c600328000c04402d0941c103000f0711590340b000c0c2846500001b0008242c3c001c80441a060220050400840035140d140358030f412107800c1e00815410750003402d43c001d070709049040149403240300d0624189580039900c15003160b41e58281c40c0c60104022100c842907140c100302f85401007501241c4200d40540 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 835185692 1250 835184442 835184491
    0x2030d090807092003090f1608061b0403171303150b010f0503131104020d060e070207140603060418110f1f11031908041707110f0f04020409020304020306 68
    0x404c0764160340d00d408003100150000c9020048042a0005a030907a0b0034180b000019500c0d4060600511609205010214100203c0010044a246074008000c2c1c103007403c60740c0c1d107821340c011002d40031042d4100f44103a100104c04441c0c40001180b141c0c90300341070400304800352030581b90700d806094188040e403c5c180480580200071030f40c1c803044c840c0003c00c000c01d0600d000500281c6007442c0070703080352010482d030104a080d68028816525501c1c030003145030759000422603035020b5034051806a480c0010b20302c20581400350145811600083c0003048807122080c880c0a00d1a11785025500b01c440100b1441160908810000000500740d54410000d90220503141540301300c186194100150701c10311403691a420701c00d481d03078000c20101c045030384003000700b00070912242030f1001e507500c06070204008980403c0c83c0c2110344d00c9520904400c1842101030404c1080c0c050426199007060300f4060080c1c0c6550f81c3d100510151252850060b1281400c2c0145480c00034010601880c1441c0c8030440f209544 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 835186942 1250 835185692 835185731
    0x1318051501140d1103040f03030e061e1003021008010911041a0d1b08070f0c030f14040f0b030a050108070b030406090507030c0b0307080f01060903060b0d02030d09080709 75
    0x41104581d01d0b940c02e683d40e1814000d01c071512010030010b50110030310007000805921061414040c0c0d1302408640d50601d2101c1e1034890079281c5000e6080d01c0048903810441d11410140c1c041418040d0004240c0d5071b80201c1c22410040d0442d6001a20300c0300188084050341c85a0040344400280050a03d0b007009401c0700c009034030088600301c1c401d020a0b1501c140b40590000200c1d404a5440c030708481c80c80c90009040080291003000105142c951200e606a124450610020390541d0707620842145007001502c1a10b01290642d0803048208070110b0315104110501c0d0041113080580ea5a0313180080007078017220703c1a00f12444541064200304054180001600d40007034008100040c05801c41c0b518034035110840d40001d21300003102000059661103500510310419262302c800650f0382d29486454070000007400381c4004035040180134800304585600c50f03426440b029201c1400d44a650300020314041e00241c1d60303400602d00950a0005c00401c1c0030400051409100078068044040c28450310742 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835188192 1250 835186942 835186967
    0x703110d05120408160f03030c05160209131b050102010f020c2e06091407020705101202070c090204051305040c05090408091e042406030c02031318051501 68
    0x22000d680c00b08052001c140704442017042c0d221400c42e8000309629052650140441c0300b034012074608040820158010422641580c4c00c10300d140c84124615030810110110142400742a00c01c040321303490018400da01c8a0000720110228440c5c903c0c6440c000a00703440c142d21901d0b0400380140118030f81d1050020b0a031401c08030000d4080140080004604504010034401001c0c1034101800010716410700da0001a800f0004c45110205076620141a0380d14442d030701c04c1079000039124032809280e1340305508444c0c007039604000151074804262142180c00000c1e80102035120350000c2e041003103240241c04c40b00c60042894040c4078a1909484007181c8403c248241401407070900001000c1040d014105c55825a00928170f5401c09880c42c3c244601010105401e40114540107040e80ca11044c2000817440c0c044255400081c1d41c01c00038210068080d0085010652106210100080861040d2171380501030400c06034400385004140700042ea40044c1100613000c8003071412003c181d13481658000c0c1c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 835189442 1250 835188192 835188217
    0x414150a050915060d0c03050105010f082a07080706060e0708090319140304050a0309050d110d0f200109060e010e011d04090c030c0e0708150f0907050703110d05 71
    0x50f0107102080c180c2c030030610f6046519161004010f02c1613050b5021034141c46c002e90b180c90441c851404251000c070000d039400c8a8200e4040016800300e40104901c0d07801ca400b0070703e0142440b2840c0c1d65030b48107810003001100c809486401c00d000c08a1140e4086a0180d603a103052401410005102500c038807031040c04d01081203180c02e21100b00750290000540662280b00003940c0da00e02410700d141c6075050180210001785c081c0500198901d4140d80c0c0d004515040710003a02c00d0a100750801c07080910200040703810b20002c903032030404600d00139004004c11200d82d51134040c0d0743d1420001401031000f038000d02c090094803880041203036801400540c48a2081c00c0410700b00c40d45006104403100303902030300382d0b115003402c0d01c2108000c1145105801c0303d00c030b59054034610f41c4030002c070001043c0440301580052201400103901e0041005801e0030701c1c90203840341c1d1900c03400401003100c91408a400c0e074042000040c640781011f40c007150b00c581c0521907501800319644265002000c52103800068280e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 835190692 1250 835189442 835189471
    0x70807020c0a140a060203211306110a0210061208030703090b011203031d1f0603060c050309060604051603090503040902180a06050708040902070503090414150a0509 73
    0x4040c0c000c10500500c440010840001180d5030070b02070504000ca803454078054074aa44d000500240000309964070740c6040070b40c68560100040d102030440c10010007a61400c403c0c0304040c004500c481c0f04181c400d441c81216607990360000c0801900e80a241018100c485280c02d20030461b03200c0c01c00b40001e9165116101e1507880d140c50101301c0c040e00e94804040c4c070a0b07002c9400098080421112480420b2007500c090010aa50f44a00c61010603241a410048d40010b00704000f414040c80090700c0d041e03020000006d003d03482c0e8545d1000c840001c601880413940000511013640d0040140681c000c404035002c0c04180350860f081e0701001c01d038020400c18142c94865510811000303109480c0507180300402151941d000d12000070f0a880150066401494088004103085100b20111030342550050b00d170511349494041c0746002540700d510150707501c1c08180608400c0ea6214010f82d034012011818110300c90801174042d5600300d08101055128038120141049140c80742c0748a1503106910211450 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 835191942 1250 835190692 835190701
    0x6011517010e09030705061f08010516230f1315020a030810050d11090702061b070602090607030309020301050109020c0a15090b012c0c09040507050418020408060708040b0708 77
    0x1480d5026109004206001f180108011440500c001e40e03c00122081a11401c907524240c45080390b80550b4060800305074905440302142c0904169001207680030109052007009101c6411907400500103980702c06e00000d1031904125650001034042c00d1010058002c0fa0010341c0040c2d1b0760081c200340282481444070014000c0403461020b2402400b000d0300461111003140341004140b008408000e00c02e0502001185219200003580c5214112141d074204026107074225400e220341015504449594007000001c800b52186030181c02c00707074843d407400b01d130130000c1303104050a442c1c05070400d511591050001701c0040400080d01d5009a070072129070000ea28600e400c82c03002e08101d00001d004854158000036204540701c144200030001030002030030005113044410b41e114010380c0d181040090900c4282090f1074244c2c8616044080c500f4154078140d50307400c40240c00030b80c010f410560517501140402c0308035418805070381d0020072843c0082c124982070b0b580002500000d0070780c10400003200b0004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 835193192 1250 835191942 835191961
    0x209031b040209060a0306180207020d170723011d0d03020906070507030828140c1c09030b0c030c0f030a060806040f021903021e041b0206011517010e 66
    0x1220720203c083c12881da50104081c01a01400c0300744203070036105070b000349404109a807030b02c01c1c2c84d4855070042c482240300446031561251406014941d000d491010002440014000d03401e0120100460001c1401c00c011103108a003100c2410040e5000301d07001d14003400c8200d80c0070a050200200301c1c2001a01c1d801c484c03021644c14040c01c04020304501c1954004001e110424014101004403140c811050440c031380f0a80082450215002d070102b60344200f4190090380c0794000d00800300005c411169043c504903202002c05032103280640102e05884030920034865007000480d800180091007902e9400c055100c02118454000c0c07039444204007201241c000c00c80e940002d402020320b8400c40c0c0300b80c20141455a0820901c04e0100d10402421803015030188840802c03a04694005150441e80c284139001d000c488034001c0b0700b00e90f001d03a9444111240c01030a101c0c1005080c440e80c0185440e6040201c46007070f0031014503403041031000024042131107400c04c250f124190780440c005041c50b500c90b080003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 835194442 1250 835193192 835193197
    0x81b18130615200d0512011505030411010201140106080603150108030313021c081b0c0d080306010314190605090108030d0c05072913020108060409110a03050715030209031b0402 78
    0x9545035004e40c001145802d0392010181c0303004e144410044204c0e03682c035510076a0424580603030703402286007403000070b010841d03002c48010709140600000c02c14800c90404440858030982244001c601d50b00705128031414104010b641101408c0c4c00d000286d4105902a6560301004103244407090408504004549801022030039520384403005160300f810a00e84960301da0070441d03030300340c50180094048000c0b42c000228000c49030320251100300c030078216803985c41e5680d00050490b41815100c614414244000454041c0b0540203040e110f10309400c0da00e03c280566143d9481396200f00d10040c01484501700200071224007000700000000e56030a000c038140e0b40390251500181030807802082d02d600f005000d10514400c1c00d044203150142c0e80c0d07010074401100e4980e11000e400941e0709c0300041c140d403c207540904c40e1a80501c0c400c9850200500000e9002d0555800c201e5036508101010042c90ba03e020405501e00c5050405500304503007200429902e48503119a121000611503004803951901e0f0304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 835195692 1250 835194442 835194497
    0x15041a0f2209021f1b02031c02010e061312110c10020319051305040515040c0c06050609040f060216120c051605060901081b18130615 59
    0x452825a00d241c007440340100481d0308140c0c000c602040c046060b02070ba103132200304442c4003600c0714400c02020580c42d8080c50051902207800d441501a43c2d00c990803c40d00201103180d02d60f0010901d0b410500032641045009044407581c10f682c3e1007072400140c0340c0030705410704414510745a640b80300c0c0c5410181c9004a803080183e009111012204c045682c00f100030b03e03003407031040003d070505a80301c07000f1515032141759415115500ad4070800e01c21443d103500421340120010303080000300c00c0360400040c1200c8024041c84041040c00c15010b042160038020180e0102d1704681c000d00354901038581b007018090749040103240326800203401c802c01c03590f0a565120f450700716104804001601d030000d4840d01e5207035010b448070300ca500c400c04401d4182441d074a0959501804082c103100d00b000c01519009800f0301348406407400140400710a078611005014450320310300001030344250007014001c801840d0320420034003a060020078410560728000c00c5046040034580344604000c40307003644142402074203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 835196942 1250 835195692 835195729
    0xc010906060b190f1d0f090a0905210702040b0d0b100f09060b040b0f1611040c031b080619140406050315130c08031215041a0f 56
    0x1075021030050a000080e00d5a103200c03106240b0703414004441502c15006100100b0002021802c00d42401c102050000c010000060046c0c0a981c0007000005e1884034201d82c5100d120360340d03403041024000c00b08480018031403260f040f280d06441546100c000c51080c542d000e03005a0310b49290006a40b02c41143c0c0c40220f411003604205800c02203040344400d101441052401c02001034040b514050511808007150031003205245002d15040c0d0002803a00030072103068440e03a0520014000002c41054285640d01ca02c0e030900a40d03262070104000c80b41d10340090010035192801007049001190000071001085080a030801c1d03680800007100c8505001100700b204051480005503203400d100e07000080c0000715014042540c58a00b89556252030002000e9259454008504481f007158102c6034428015003124102a0322103080c985160b0081c090911444800341c1045003400c0c400e03041403548002280c05008424054440d1025100d0060b403080c410342401d031500300588e58010340c921a400550 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 835198192 1250 835196942 835196951
    0xd0f2a0b130308010503010b01091e0f060201060e0717040b0a0e16050a17150702191101141e09190e01060f0201110d0c0c05071e0b070210050c010906 66
    0x12042101d80c241c951000c42c081005100042201c0c50107004d0f4940d00e03041a9281034800380b40911100d540201440c010754040100c0358040348050b2150344080c0074100c07503000071a242d442e001d040070701034000608030740c01c120060000489003d5000c034442e0300143c00c15900780064031102440310042485070b55045051089690300c00d04115510b40201c200c90b0111101a949581e0786808000340c103405000103056005080d03c40e54940d1000307019508141ca0348110f520146640224240c803090b424820b86601e80d000d003ca800542e40a440550080d0143c4012800c00d0004c9400d60354048040720366040101000c1280c0700b01d601c40e090b6020740c902c40903000c800015500c40305171044480c00e0044400203000b00b0b440c168003500500400e0300c0703020050409031804802c040c01100a05050032500100140d500d405004244100120304c0a0512220180481d8030847d400310141c507000c0e40418400f040501c0020096510306181440070706c894240182e03100152800917004210900c0c004001c1c0e40341 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 835199442 1250 835198192 835198201
    0xc1002030112020a05031c2003070807142a0301021c05011a071101030c26070207050117060103021b07030b1519031103150f0601020d0f2a0b 62
    0x1030442c8010b959000740c4101020381e46039014581c44a010b0348000311214200d40003101124400c40707215030240038840001000c208040602801c55118031000d480200010030398400f07000c4003008003040c42c00308100810710f00d1030a10480c41e40204000c103ca9080c034240d00c1012603500e003074044404044111108440b8440d0658940008000a01448500c411901040100c440e1000c00706c454a030b410001c919003c0c01d10500440140c10308030071400810000c8a201f52001c1400300b0082401e01508649140511701400024500f0f80654081410001180288808001140b00c01c5403c40020b10b0301596031a008103001103945c43c5041e8020480c810002e000042c4141c0c0c51029000d0358000c05c602c2050703400441044404095070002c001c8914500e202080050b0790100d00003916030000d002d0310b02004040300341503a400d00495901c6c040b502c411003040083d40e814807444805584038102030071408040c4600820000042d40030000d01d0108181e1a1075140d480c074080d58810790301c22140040d5240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 835200692 1250 835199442 835199459
    0x12006090d02010b010228020a0801020313030f020c060f0c030f0d060602010605041118040e030c0601291606090b0903070c05091e100e0f04150c0c080c10020301 71
    0x511441c40005501e4580e811580e90702c08a01d5a201c030080d1200324005441c4448103464100541c402241e000c142c1010003e601c0801380055072003858180602c003861074141c200a4003080c1800101c80840d0001c00260a2503654a03041e00d04800000c0100381e00d03140b0541c00107265100701c00640d4000040440c1c1c0a000c00b01580004003035030b4031f6600034019656a1824401612914030003c0c018617004d0103800401c070b43c0c5800c41d00700c00c1d00040001c2100b1800d010503d0850740218440400798001b080140012a40c0b00307506c0e01c45a0b08403501400702c00b8400c0e4141c5050244490320311324052851640350600525410590b03400c0d8102d050000d00303003003081096a5a610103242260b40c03080306600012645440048039103ea408030482e0b2014803041807183d030401c00000e003100100c00c0d013442d0200d1107000c1c20b02d20601c1402c40e0031040c921800d2134204040c07192200c5660b00702c1b00c2d0900038845800e5601844220050380d00c51401600d466018050600700080303103140040d46d61020000203501c11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 835201942 1250 835200692 835200703
    0x20a140a0807050304060905040605130f061e1d0f0708090a02040c080621060105060906160c05011413030326070201020a030f060b0313020d0803160e0d1101200609 72
    0x9506d40c1f0b40c458110b54540c28070058504034810281e12282c0c89210b9024919507800401d2003447c0443e0014900d515010400400c0c0f44911150381d130104580f4041c081c03015600190030700340e40149245062071601071100000903000604210400a40001003403041d01d041109540f0390760700505c14400603030040002405654102c0c4c94a2040c5139000c0d01d0040192a59900d000381508a005403640c0e070f091009100d9542d01440c0035940182040150840740701114002801d01441103802511080c54000014001001d01441c1c1136003d504024001c4103000380751804e4202c903414202040003140451a07494031803800c0d201814a00450b10411031029070650041005140b180c80401900f91048010000c0300d00e40e0103500c41142c002c10102c2c06a80d4400b443c603004c584001c0c0160b041c0d807101e52b6403d15942090302c081e8103034004000790200d013580003180010300000680d02c080780204503840700c2e1007181c0c0a0031064140002e0f41c41038201849414905031841800104680c95420940442079880 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 835203192 1250 835201942 835201949
    0x30b0f0a0c0503060136090905010b01080c0712031413141f11130b2d030406091e08090a0f060c110604030f08030402130606020a140a0807050304 64
    0x228a0300c0340080740d690050301541d014002c181c0d00d40f40803003404100201c0300400351880d44800e040d41074100d41e0003420401d07a840680424a00450302403402d14048e403e44071b103190407905001020040180d0394031101d0540b03030704a405c21421466071643da48107500809840400d5032955480404005880f82d0200a4824413445004120361442074840d1203501e6400fa01e81d44400710160043d0801c0b00081d9411641110b52615010791134440c21450034a010b080d9540a407190903400308845084000340e85032542514012001d150505ca9080040d10300c0d07100c0200010110b598440d910428041182100181440000a0481c032009981003040080d000001e03118030030801c100c03000c02da001c081c144100455209440e0341c1031815131a0340e0024810f03010141160410000e12000002c180702c004140d4005024a2034036a680c103160044c0f10500490000000d8601e091000c2004240d40c0001c01c2003042d034001151001401c0011016810000c4081018060890100e12082032160201c02030085 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 835204442 1250 835203192 835203211
    0x7050307020a09022a0c04090302150a06030312091502030907210b0c0a02010905060c0318060c03070c080c030a0302130f0b09010507051905030903010b0103060b04150207030b0f 78
    0x41d070303940783c5522003a88540b407094224a025103610b0300b101280860850400703405070069640324000307400407030202d402044007540140d00c24150144483e88240c0c1c130642010280009021082c1962400381c00d4280042d246800c642d611ba0495090010206419455055054095503a424800c0728556544e904d030048481c0001401e00f280e072416503000000520550080303040d4041e585a11001e0610f8110b58046002d40d52a9510f80700050002d02c4241e1080c484150055103e05142c03807a5404501c08c141209519405003041c086003008000940394800d596280c00c000b121100e02e400c0c00b00c9e020f0034405212900c00841c04100b5140c00d500505035400341500082049a078448032142d0202e407900c6401c440003010040381105501c40c100070242d960040c4200c9500060703078004001e2005007030105840c075030004118110245005e000d140692402460203003c03d80c14080302a403240b185200300744902080c001002500c038024040c0c64015600301034034441c9440c0c61010482548001c841c00c110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 835205692 1250 835204442 835204459
    0x80f0d0e030c19150809070905040f0f03020106140d051c030e0a06230c09011202091801030204052a090a0e0c0408060c0a0f0c03110f011b0203030c1c060b0705030702 73
    0xc15441030603411b100e080008014540140f0b00796200c00145400f0b0020365a40c5000c03840a000b09200d6000c4a040324800d60000901618111820f0440c0a13402041880b4400071070400010550006070902411700c008904a50030405890030307001011130341d0881781e8038010308015400b403002603403052100c4441e00e15410501e01800c100d1200c0d0440880e21948425014403007069254480c06400030107080c40d001c0140307090075400000307007030180341d407905c080c180d0b800d400600c03c40c00c0c2802115041440000c2601a0101d142da0101c00c03203102a151690300c5074041108209640e40c41d103008014013100d07010b10014100384500803482e600900544a0034415000440c0d0440104001c6035800449a62440094401190101d511115001c0d040c0c2c200508020f40b503042c1041885105503602851000045d40e016201c14106d080d240c070006441075400c00e10070070200c540188215201c2d0b070301020b481005c08100458550050000342c00c100c0940c900030480c101000710004c000c14145000320745100c1d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 835206942 1250 835205692 835205729
    0x20715020c03012403030503070e06030429100303050f04091107060605060f04030b04170a11061e04030f1209030e03010b19050402090303090402071209080f0d0e030c19 74
    0x80300d488550951564204d2481010000300348180050f680013400c13898084840d06030780c00000e1700b40e04259400d64248040b8104610640450354619094a05040c200030392072400c2d680c02503000c0e41610000d824403900054030355000381c0310f074110b50280ca06001c08104440580740d000c0c00d550070842d0211445031804401040916103941a030358060703442405240341a04690703031010042009070040703690807021200120200c8810f00503000d612015a6518000360241d60300929142024101c2c0c4c00c50703089580201102d5211030a51988035815003002c2c0a041130740602241c4416020182c49121441e05034020105680f200d2404c07005402200244440000c03081042115802a0110402800a500704014500701a000380c1014000101030b20f0421101074040f0302a0303880301030219203500c44036508140e5160405215400781488400a201e405000286d0320355480701c0e0404c680c1070001c2c81ca02010b1030343e0700b00260f1031005001341481c601c0071441210000340d441c1034000c6442c400d003900040c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 835208192 1250 835206942 835206971
    0x70e0a0b03040b0112021207030302060a06050a0f06110a050a030c030f3e060a050a0e060903070201180510030f1d0705090703020f0f031014060a030c020715020c0301 73
    0x700d0003580c02034907681443e46440c5659402d0b40c001e502c101d8208401e2110040845400d120410095000350040c0041c3e00d008011141211310b103400241c42554400000d00100a05006078800c0d51045c0c10924105401c10f00c00c14904610150300501d05c3c403d1942c21801c15502c400515030861194a03001907841006006483c40e800c425420444031911560446200e40300c803500c2c0c50500b1101008500d1034004a00380382c00e00104070340c4000442e455006000305400d05100e101880030030600039000303905003206110f4072442030580203810004103d00100d108440c2e0940d487c000c180041601c00702c441c0c1c240d0040d000c2d10302091407801c500e10305142c1d5605065510129039440003843c0c040d05049003000100300f145a80500064101355090040720b681e210350343c00070071440208916a035141c0c43c101408694001c0c031908541c20a100c444229503441c0ca410050325440111402c001c6040503600000301e01c2c0c01c0d019072118205613a12007200421319008100034881600a4009104412040c07604 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 835209442 1250 835208192 835208197
    0x6190207140414040320010e0307021005030c040b1c0911120d02030403060f020c0f0a05211206010e040c03140c030c0703120f0c0e090a0b03071814070e0a0b 69
    0x1602c034030030f5400b0006002a106401300800c40381403440540c604894000d00500312001c0c15030410041d880000c400d410340c60300300300c4d083c940005803400518500d4201d00f0b03100070340a50700c00d034044e02c000450018194245400e030344036003001c44c1d101000618964241440c10a2681914074081c0001c0032255056001c0854441c015041c2500190300e00391455407034070020072004e1003a04005a007408025000b030002e01c281c1d590f40320294000c00c0503c03100d0410b41e0a241504003226141108201c00c060023200d02c1081d120041d10b0170620510360b9441c14010303074040c007501c0251640b00c2e1404c0754040380750f5090b44c0410201c4010b40908849644c4862054507188000d460a07008548140203500000c2c0c480c4200803c0000c2100c000b0070600140c15a540c20760b402d485121001c60418a030302c11190501c80c88460f400f85003001c090140310490000310b9140d4070300e4000c1c41c1c030007288030214070114615500504544002585101c03e02c5c81c0c0510010400340c03006c1d00003481492000000075408444506 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 835210692 1250 835209442 835209461
    0xa0804140a020603150105121f0b0a02100c02010e0d09090c0503060f0d020d08030c0a0e09070909150512060f0c0a1e1106070e04060b070b0a0b061902071404 69
    0x951954a0740c14400482610001703846040090402960000d007001d05600d5000b05841c80c54150b258401400d030907140d100d03a07004103000000500051144c6980020700303070416070100000207400400d0480490242002162480d00ea2060159070102c0c0741e440104030702110000c9d0700402404500701c0c4122200d10060350380030740c49070040d002000c4600c6c00101c80c0307452610081074040c02815039070f684201e42e00107d0b15001001004600b4103812900071681340340348241182e8000d034a01e00090090039158070740c00741d0501c0c2c5640c0c1c00d000100700422064000038000c01001c1103040c00340096020351f03402d02120456003000e11680410003220340201034801d0300300551a442100402074845500a45d40c608520007003048030220104480028058107000c0c2c8030640e11100b240d1103080a000c1a10626070140e13005500403c00350300484c50134110b0a422604921000c02c0b00c503003a05c00228180621581c099400f50203d00305100302e90001031903804ca07180150002303584100321003040300700e170181036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 835211942 1250 835210692 835210699
    0xf060f221205280f06050604150305100f0b040e0309030c0a060512070905060c06060306092d0a02030304080604150b0f040e01090b0702070e060a3203030a0804140a02 73
    0x400510300350560030003ca9020209041c2d00c001c1c01900d8458120ba410281010741d0042c0da1041030000c00d05290040d00000000100c00c181e140f07140d039507043d13505c05020740305444961b50b4028407420203003e5005402d894200a006020340c0120a162540380c0d40480700d9181300f40300d901c0c5149490300b040f00720701045030042d40b54942010001000104d100800030100c0b000c001a00b074003c14035980b4a0060031b44010507400401071032601d042414034090024001c180c055101c22001400004150b65804100441c0c52101d480c3c48015817240380762036008d11300250301d8040420049020000010403a1241340a106502a03840c110b0030703050b0440d614620041d40100c800382000e122410150072880d00075451074000030b60b04407980c442845e84901a0b900c440141c000d0348c42004480c2e403841007190841011074030080c4251610260755004540601c100175000c0c2d0104a01d2514910181c822801314400b41c15269210664a4001c000e140700300e40445142c0d14030328442e02c20200015840c0004d030b5000c2c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 835213192 1250 835211942 835211953
    0xf0f0d030e0c0a0b0a09030602070b0f1e060127080a0512040b0a030b0f150d0c0e1305072001060509152b0602040b04031a070e0f060f221205 62
    0x7030944c00643e02407440c40040c06415600000000d461307100400340d640c0281d8800b081c80c00d0040e85542c1e03151003d0210071881e002c000040140041448440da0043c2090811840346080d01643e00036100300403403460116124190002106580411100e01003440360040e990403c02c40e4800007407a000f64051030040040500c0b0541d8480d010340d12016983c3e00042040c0d82e2600001c0010b22003402c2552040a00b00001c90b40a40400d01d90080481c5050b030b40c10700898581482010079450140801242242902c6401043c0c0481c020381d820780c201800d040b5003440204803810824064106032080c05e0151008100240c18184034913941154000028802e1042d035035a035880b0452840d80c1980ba92806a1044403100000c00620050000705140c1c0010354076940f83d41002e22804c180301214100c180d69940822414507401031180364450022154944642c00000106426003c0c0c400d0700c540303032a0002161002071500c1e4044016000030780d01e203801c6032911040c0100c488010a000102158041d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 835214442 1250 835213192 835213199
    0x90f220606020607080112060e01020d1e09021315080307080c0706170a05060a08030a0206160302030f0403051c090b04050705010306080d0e030313120b0f0609010b07050f0f0d030e0c0a 81
    0x43d1f00d80840068090341c00803460403503014005089a005c205030400c0e1503620700d082106024407080302d4a9955450b801086264455000b003115016000e650a04841c0d485440201082c4119819405802c80d403080769268140c1d4a01200d0360ba012344130040c41c922170b90500180503481203028460400d82c0c003e00d000d098135041040c42c0580005030030507500c80d05241c2d012541d118204041c00d00b200075036008010508144100b10310408041c85c500041600400070032a5203034180f1011508183d1615002d5a1100707401412000170303d504025040090405031000c003402400100700380034074080c10070754840300c0c0d580d40194103c0c1d2151180d4526130b00070556200501c0d00078080c10400b404094183d0745020700b0040050403c00c41904204080c6060044080c103101c10784041039802000810140700c9400c003600054034026051240f0540c050380001c00c2c20030420140400300b4848150012a20b103400b0030840c003900c5000c0119060002498145140d0b6901400a415101550041d088102c170f1402d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 835215692 1250 835214442 835214459
    0x703050c0708120a180305030a050309070e010b030402041b0e1e040905011d0115150e1809010f0207020f1023180603100506090f2206060206070801 65
    0x8814909005401001d500181d0700b041849403221020f000c5461941d0b034800000c02420488210f691040c040059010500c0003039000001c07500c00c4e5002e42002ea880f99241303440075207884050703000580c480725014000101080f944015501a0f03108075810300240e91a049140c01110481441d600040c0a0002c16092810700c03010409160ba6901200750514965a0109055544010040703c1507136550303841425045400c4683d03601040610300070b1002c41d80c5141a83c116003154017075070541880060f4180c0b030690007124207074031030100503001010070000e024081383d000104849041c140e50070442581e078001c01034402c652515a0003030151010340c800c4024004480341891420091103801c00304411b03d130b603074020a4502c0c400810324050342d03440d80c141c00d840740089100383c1e035004000920030f00241d00046500101a00c105984a54650350884002506003045c00141c42e00100020540c081842c0349100c0e214031082c18080a11180303649060499481204803030007400140301c40010b008495 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 835216942 1250 835215692 835215697
    0x1501080109050606160b0103140a08040605030a0f0f0b0109270507020c09010e1f0305060711030f0406020307110a0302010f030e010f05010b030601110d0203041208040b03010e0f010e040206070305 86
    0x40044e0a607800c0c40e03501454101107210b10002a00e515290600400c204008207148441544a00005d0407243e00e15030fa032080d8034080c500030304060010100024282c031140d94400072860340c0301c4106200140d0140b00d0000148690f402c030030b0004d4032035080882c680003940e80901524840b0000c072004100000c3e0b5100080c1400351040d4210b025a0041100507a01c1c02c030780c10301902549000e02003504000300d000c10000d88a071aa6030b51800c42c4402080444c1010484075403100f01c500f80056000d200401c03103404c61050b444008402c44e8003107000324650340e00102821089100303280802c281c104001c00c200c807488a034480240000c100c00541690a480b9800101c1a40c016600200f0500415896076040e580240c06c0f6604000010040003400d41e030109901e030024440c078015002c2c034940c50000a46a1059018581080788980c5c040405c20034110100c800408440340e0b601d4403540c4580784600303010b60503907001c0e10b4a40c403080081090301c2c3c100302560040c0e41c0100010f152040a039025101074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 835218192 1250 835216942 835216951
    0x7030e070b070501091b080c0f0a03120c0203030d1406060414061b030f0918010e0112020d0506070207050102071707050112020c01050a29030c06031801020c030a08150108010905 78
    0x155217802d010070000380c00e0350918540c8903060300c1e0101003e041140c0640b400448110310b500c5805504076100a82e221090501e050b290001d50380b03840b0000c860b000b5215050b0fa4070000790548400641d4882403280c950021407a80303a801071103031140d03c0f00070401c05580101c1c002c40c1525404034140000350b01c1d244d0000c1840701e0300d02041c400d60310b454442c00b50954000008408402800003008581464185002094150302d00a600c40c99418282e008408082c14000c40d002001003034505001d650b603000e0110046a4440700700e901d20300d800070000b901d40e45c10784901d502611070780402103080324913149a40c02c2020b0310310061071110315040046881c041d42d6081d00100359800c01000692a40031300071980714074894480410305110105d40c80700e100b95000784c9180c04410f040001b658940e0b02140d0b4890402040fa0108d44a840b44070008010914801803001190700c0080e0841d10488084007400c0700444a4481407815600d00301d5400e01b10705c0820b00c0e503002940002c018851441c42e0350009810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 835219442 1250 835218192 835218203
    0xa06080f1618030c050406060302070b04021e09042619080703090501050403020c010e040e030405090c130e1611211608070606060203041203030f2a0807030e070b07 72
    0x7620290b18000078014100e402c02d607494018034509111605050044100078041443c08601d40400da0310b03201d031400400390000b4450482e8001c04008048288071031490381c00002c200c411142060b203413a02c1207070170b68615020000c2c6001d0311200c0c401c808605403a50a01c0401e0b4004020035903000880704460000c12450a06940361052004070b8000d00c500c03803140e4403d8005140f001c1200c0b00161401001030700842c441d80c217000c1140707459600402550b080ba0025201d4505645034441c4500c1c15000d0401555030000c40008001124401c1c041883d0003100d076005051000c03c0340100485440801001071101c540c00212061100c04890307038004d60703c082c42210b690a083c000101186014141c0400740d40380203003c01c0e40020b12449114000c01021140001c524140ca403045d00c0400b0410104042c1c00d242d903071403e0b01c2c0e159441d90000c2c0d0b40044800c0007130249558020241540d031480c01d0b42000040c582500083c1f109001c0c2c0b0420300050304580040080313038a00034241849a1000400301e40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 835220692 1250 835219442 835219457
    0x2131413050a151e0504110c0f03040e0a060e01030320120d0b04020301060c030804080d05070f0f030e030301051203041203020106080607170412022103060a06080f16 73
    0x55a4459201d4540580801000490301440c012100101c1401603000307441407600c82d03c90011020740030307010352044642c10342e00411010f107100e41110060084a888608a02600c50160f0340300d2000b0000300f0644401e5800031950f03440c2e001c4403400304c0b0b2160240030003068441005101003030285a00300032440c2d0200041010503160043e2034144002000c181e21550004a84181295194014036a400c04191421800c0d0341c5051002003200000c2e480c044d0500c0f21140210302030004500c21644000d5403440f0912203403d00c41d030000e00424002c640c0390300054810b50755900e194800d0041c109405a054011803c1d079080004100c00100741040f10401440304000c000ba4a840018101001e9402a00001815440d000d555400c00398018040010401601807810380340c143d040d400341e08180c00c840810300c0307a101c01313805a1408044c80c0503081060305444c030400f01034007408002c522501d0182d455884055954000ba01c80e02c8065403014041c0c0b1034080018806280b21070410054251460f00300c8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 835221942 1250 835220692 835220719
    0x60d020d021611010f0804200a030602120f010503150403031a21070e090601090c0e21100e1f09140f12030603030a0e060d110702100201021314 63
    0x60b0107107504404450000310704140e0320700c941e000803d844152015003040d0645207059035a40f1001402031401100c908480310000419441d4810003501655000400310b5403140105041c0bd01458101c902102c1520b50200100d074030709006c82e4a248114402c48082c0c250788942c0c2c0d09074050458a1141800310100101d0003a10b46c2d01c29908080b036541e00341400081030030700f00c103c1d820007050344c0180c0d1904284406101e2043c0d8001000c90440e050301800040748a61070000f1540148840040c99000ca9540079054800b071110980e444410915000c981211051080f5071080d18904542d0002c2c0307420031b5828151854200c4410080900d03800700000da038007150354443e480481041e0313000220303510121a20740e600d82c003000300c1741303007003004048942c214540000080d0b40c034410000314000b003050f0000800026207400d8150391130b0840342c0e40280881800c1d0318070001c0580010030268030450b040301c00c24050078018403c50b005d403120124840e50043c244485081000542d18805800044568070b80 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 835223192 1250 835221942 835221967
    0x41401120e1207050d11070b0d020409050106110c1002070b0904020405100216082b0905130c09050405060603131416031a07050a1b0f0f020108011202060d020d02 71
    0x106403002801c916103880d4202414041e02d095145c081d50014000900540340c50303054002038403001c40310740d02c25056440b110700d44c802c4040d005e59409040d05c54200b03c00800c040d90000d4880e2440027a6008685400c8500010040c92203902e0700700d032000d40c011640c1809401042d0000f80b036440d2014002516042d071360f8020800c202220300c00c3d240140c1181d045506450740d081502401030004030014403400c10303d20200139201603540204511403004200344209113000310101401043c00410001031901c0d002c20110182880701346103000260300300d40101d43c0b440d19205042c002c42002e40020305566681180550020a0701c10503039160158609220203a00e04000c8403403068001524854041e28524207030141000380d60200d000040e4000800ca5520351103000d5036108102460440728568140003281d030401c0230144040c0420090034103080c24481c1b1101c400505520030303610400581c0c0c0c5d0b000c0340c181084d0701150081d0302400400101290404d680c0107880344481c5c004006251402001d500c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 835224442 1250 835223192 835223203
    0x10909060b1003140903030103020a090e0f011506200d030e030f0304080405180402011205150607061b020703050c01050703120509010501090b0d0b060d1e150b0402041401120e 77
    0x1102d0009865031030f64002d9801c1c007106150424489002142994116400902500350034001d800603e951106480050041049400480e900c620b0080000403014407280300d005007140500d10204414401c001d4107054036126200c0642c083c14040d01c032034100318404a000c1c4c61030b181003540c144414004003038413407400300055001d40d216040081e45c43c0d2800051180000c0400f1102981e9004482000050b0360031401d507a244c250580e40c0050165280c031181e44181100181c02d503080321000c00c0410070001e4550141340100e0802c001d0042d13919005c94120f0b52500103000085c065085191341c1020741d4001d0000e0044c0501c03030704180f6400c2c8412155403007182c60488000300e26a445500400181085118001c480340b01034800b680002d440d07884000203c00058007141c02004070218100074816400c000d088003184600c20649900040e0506140410700003042006003403800c007107045a45003901c03c4a0071943c9102202583c08201e20042d56a1000c4c45141125540c0740c5005100005c2d0a204 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 835225692 1250 835224442 835224469
    0x1903021c0c0803010b0a090e041a0405030c24010509190c02071a1b010b06090904080c0a0c090e0307020a0e151309060506060c03030c0d38030114010909060b 69
    0x1707207902e5009202c0004d000c0705480e80b20402e4464110180004038107204e001c02901d0400442030340c440d4071246805803030f40c0304100780503055014400a00141d078100880c1d2072070490a40070119030998035002003003443e03034081d03c441000301c40c044d03144541c14105801030885480c080c0180e5207968cd40d050f20a0b522001e40028450501c0002511641d015403801c6060301003000313100811403d0a060040f5516219480c00d591185407030500050402c60060101c4d24800507403130946448a400345030080c503610307450180035403080c146804803001150020980c0e110a400904148030316140c10f441c54114000603100d203407c441c200042c0485502c0e101001e20b854109003800185114003030412104880000c0c0240f0f00c610310401042c520f0040000560740c008103080c0315590741780080c24000004010006501212940d055002d41840100001400400224050a00080015408042c00c0310790350a4044a414806d00040c0700c0104103a0006510b5489007400081c3c1950b600002140d0481503072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 835226942 1250 835225692 835225709
    0xa0c0f211802030610050f010e12010f06170a0206070b0a0e1f0f050907030605060d1403090414060315090a06051503190b0103060f0209120f1903021c0c080301 70
    0x11420702141000c01c00d060b40031111018400200c0d0406000418032035403258420304112400c06001450703074500503402541c1c1550b40c0204070340350b040c052201c09481103110302c841c40360b401c0320101c50b002000b1500640e0b140d401018146010101d40e141d40207080c0142a2a82540c0d450b0800301d9910b02c1005070204540403080741c41c100c02c511710031000aa0314004e082041c0c050421003031001180c40040c030f03041522344c0050003050a43e110350224030b849080c09400b40c14100034911740c150034000400101100a0103880501c0144070320005584951400d07204242c166200448010308400010815038000044000703540644440b41c0b01c007001e85009491000b485800000003108030f03d000c02c41d0300d1800d00000e0a0078181809500e80e110307841c10500c40036105a4488101d420001c1840e412100d83e408020b0890050100104615648000e05407507210f8910403d084880034088000c42005408e52603401003140c1c2d410041c82d52440401c0401c0c0005018526044000141b80040070754041d20541d03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 835228192 1250 835226942 835226981
    0x130602160f0b1501080109050c0f03010b1806030606120405070b12010f050d150b0f040c0c06060e13030e0d2901050910140f040c0201020904050a0c0f21 67
    0x60400103002ca5010703106804861030078003200e04a0340c00c100080d0454150380c50010350780c0d40c0e11308000d8052181000e1000180d0000001252143c0031501170504220030528a21070303905400c09000c072a00c000c0e41c02c240c0c48041405132404403c4040034869001d03100c3c209454010390b03500f03002241d540000c800030001020280c01480082c5481e1403881c0208400ca4008a456007903842d48030390000e200020311400c503140c442008103515507001850030900060300412003e404c0403002840b00d54650300403202c10703081100001c0c1000a0450140c041c1003007102a0203075541d1540d0949071ba0204001141e000440c98944c50045410201e8084603d804041c8481e0f406140300b2040584c0c84050f089288101c01c0c450034031041704102c901d10310503615107228409072142c0380c0380098944407042d40d80f190b012341004094100d456040d000740c010000d0a0718107022030786a010090f4155030745046c403040011200420510b000d0f2203a481c0c00804e00c8040720b509800604021744000740d62200009031080c00300d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 835229442 1250 835228192 835228223
    0xa0905042d050114130e03070812150f1320031602060f161101110d0f1a010e180c07030e010305060a0e070201020f0301080f070b030f13060216 63
    0x804201800c0e011801c0d08002030b43c14080211a8800c08144a9003c2c00032030075800c59800040d070100c40a804120101c0c3e03107900c49864800440d600403c0c1c02000500c0b01004281e5004e00e68650492125008000d0421088003806101c44003c4120541c29055110382050502c004a900c1c1d80f8050704422010b590707a8500300200701501c2206810710b108560007102008002c0803440c443c140c0107509880c0160788100c804030200c2e1a18058100b400c3d265103083d0280b018144002c00510081e00100d0003031000c0a148504001140c00e210306c0c02101c4411514a410345600c100c41c0c4020520004041042c01743d8503188282c0c80b00e200721003a814050001400c00c1c14540c1183c2c02c00c041800c2441c06000f035290000c0881c0300030605105069070540103001042c50b4500079019980c002008192041d04c940c2e44030356a0703980b52402d04005c50079004040011803103810240480e40300d205000090510b64031100340001c45003602c1c03101602c40399401e0007020b002d0400ca0200340364907805030b407103c00301e400c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 835230692 1250 835229442 835229501
    0x140c031b0703032a0b041110080402150a020a08030a09050d0206010602060a1a040c030e0f0a0b01060906050313060603060f0c030e0f0c0d150c05030403020d020c0a09020a090504 78
    0x20076641c850340342c2d071040600e10031240c44ca01401807140d11506141c155112441c00118190404203020b62100c410440080c0300c1d079010080b03c1c070072802200c50500140311282000540d1084904800c0180c01aa040e040400c4451000b190800041c007030024100507161034150400c07804c0070550b0016003100004000f0705904101e040e03000b848010301084540400202c520b958852840814003903500c0d0b018007040c00e40603038481c81004030380c0c0041d42c0a41001ca4100c1d62103486215084801e206148008540e01d4402d01c0c4007802e5038895212285591a548000b490703401224500301d84c2c0ba81c480d03c0101c0051401e00039608000750300840440c1d101c445d480e0140588001c0030f45101d00d58840c040b11030b0b1848002400300c1c881c41c0266074402c681d0340c4900f0b1182c1c004941840451105041ca81d0040d0400c0d03120008500c518081e5003034030130900d051141280c948030032a0019074081c0600000344442d5408d6802041c07500403d0401c00c0d081c40c0d441c0c002c80c040d18030403185861b0341e0201c9038480c03d41c0034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 835231942 1250 835230692 835230707
    0x515060f040b0f1c110a1d1b04090b0918060f1f06030b1002012a03020d0501031a07050406140a20061f030f030e030a0c0e070e03010c140c031b070303 66
    0x403006c54134001e07054241925512142d0002e80c00c80b0032207140c40003042041c4441c030301d4008018440c2c0603080d51a03480348074042c050449550140d0180e080100020079034a00214251030001d8610040c06583e00d50342244441c40388081e20162251449030304081c46c28044010142c02820b0a41340459042ca44000300f03e1000e460440714419a41006241200340321184240d403030704019485400c00c2244400000c80003406420000da050f01c2c5010b001105224240c0c0384c80340c9800c0600c6100e403c40e81c41c90f504683e00d0046100d4400800c0086607150003820035180601503020503031a010104a86c41104500200140c0010342c1841d00100d0a000c101800300d400714040c0c030300c8052038207041840c40d030b43c8180c06600700801504010704c0288200c2140d030248004c007641c03600a540c0621179911a41144e140c2d9030181c0e00b200c0803e030542e039800514107060140b56813070361107a29402c000040c07107039100460354418203007500c00d4023040000b1000b145002d00c001425540250052000c02d0640c9009023148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 835233192 1250 835231942 835231973
    0x7020c0405130f06110717040306180b0118240602070b070809130204030b0903030f10210206090a0b0301081e070909080f03070c0515060f040b0f1c 65
    0x388580356920000c41c032000070308000701d580510002070906882d42c00380c0441c041d51b003000300703020200006042c88001c2400030b003099a0040504200d61444540510a2982d0309c4000030040c000c0c2d0340040080700101c502c541903400945002050455140e0701440301141d0b500441244000b00c68810b01c00b440c1d04000001c00381a000801034a003125584070146c03c0d015200e01644103280c07500d112448bd40030350f01558020341d4421200d180f9400c0040025032603800843d910401ca030504800280e55030701070701b56001160401105104118210503031034400c20302405050741c000d80100980b841c140c413403210072030007010200450b5459505120603a41070000c1c0485400c4081c0c400c2610307050700c02c0b010480341e00b1141c1c10a4002400c0745540750480d100d00840c01c89611502012040016840e0488450105644a00281d4600d92841c0104141208040e292030790442504000d0b0340103410103074040c4014040080292480101e4400080c184540890444000000c60041e8408000517440e241828 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 835234442 1250 835233192 835233211
    0x31f050d120318080a0212030c091207030218071e050406050304061407050403031805090610090b0a030507020c010f0906180902030408120708070503071d090103061e0911240307020c0405 82
    0x11410728081400d27050190043d11481204400b0605410980810040b40290346c00303044028281203e5501c24402e1504445420104070080010280046140000701c81540c04d601c2d094201403e0010844550300020003c0720819a41c1140c651614280a225440780d011965955981c0e41585402018480030522046a100c204801480156204404142d004009540303910b4040a10103040f2035107540c56105c500004800900550742030741c1500114030918040d000ca030b03c910b545400444004400341e8105000596141040c030105110303d500b406104c0c00315400b0701c07100f82c0703401600049038400e8a003110004000251060411001c0402640c000c0140c1443c0341c0e9480e06047c0500fa51000422000820076003545401740c00740e181c1c188003100f00340a04525140d40e180d01d013080c000d120050789a550a40f4200494882c2c0d00d250107015000c50f4450303080c0114a00308814020401028880c17450241032507500460b40c8101d0030003941c070860756540101035144030f86d0140021030f50301400c44000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 835235692 1250 835234442 835234447
    0xf1b01170c030c0a020307060501090b0f0102060f191508061b0f0304030c0311060403081f060e06090301020c0d0903060c0801080a0b04110d0602031f050d120318080a0212 75
    0x258038811a06582e4400052000e2079074403644400224211f01c074a1800504132480c2800103d6414100e40c030240c642c07242900c00105942002d03006a0340c1e18070441d0b503101c5011000c0001900100d41c0b414848401d10082d03004150080c4524000c081c5948507081814154000c1c1c04200c036000c040c80c03014103145150380071640741c0320266159001901c0000c00140900001d18a10710800d4420f1200050303011030b400540b1031505103440c000344507000070782e9444038280b0340340190020039003d548200100e403816180c00100c0c03540b0702c0c18042d8613000848031030b070b05550074841c0710340445040c00b00642ca03801540c0c44404c06401e40c40d0501c12500f40e40312010030092444014048028001464903c454002c20301c03081d03503500c46c54900800140041034540200599951008124694000d50300030000702c0c1001c00140316004169003152260700c0380e1f035407100c50400202d010a2690714240d480a11030f20740070940c1550800d6100d404102443c1c101c54041c0005090201686d05120496482c84040f82961 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 835236942 1250 835235692 835235701
    0x30a020411090a060e10170103110a09050a020306030105063a0c0b0a1403040809041a0307151205060319110a1d0609060a05040b0d0605071e050301050a06030c020f1b0117 75
    0x100c87e044140001441c2462003200180d0541d5140c90840040c560110f00780003a1821300e030a0b201039001541e10501945c00c04000c01c3e040d00c0c06242d01d0103014844000d40d0f0410200603a035048290340c0f405101203417003814021f4000710b1200c5040002400310031480303940c2d95801d001d00805184001c030015030a00c0090040c400026180c00850700c85100031140070964284002c0e801403440c1c003003010580d140c40742d840001412052602055a40790f030740d49030300380805564034501c4240c80d01101e91541c15040030480b84809100c204034000030300d018120700e11000131180f000c1902440f50b6082113a8000c10707210015285028049401da01010607510b40581d8105400480c0d400c8d0414059644200e40304e1036404da180e124181303038141140e02300800340b040703082144002d0301188050741d0700211601180380511040780104c0071a4100c440150140003803501d0480120001c021203061441140030716507000e01c80c55402c014149034803c5029003007400c4c41d80c400000d0f003002000340f144043d000726007003040f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 835238192 1250 835236942 835236977
    0x1a092d16180605091201180b0105010e030304030f0807050a14070e07030b0901030314070215030103060510030302060c163207030201140c0114180105060906030a020411090a060e10 79
    0x100c80131201038640d950032604540c089800740003003004c25038614400701210011b01c0250894203048610a0303c0342c00681e9200d80900da01da00c101d02010313200c000601008800030380c141000704440d600441c140d41d19441e4564800e0410003d030b10010100d540311460a0008981d8104c40c07075000f40d080e0504012061244000c11614941484083c0038000410b50019020760b414086805044d0700504074a1940c0a0030600f8446400a000c01e442d1245088005074101900031a0038040d6600364006000681e02c550f8990b180d030784490441d050125070a00c018001400d0142005007058000c1200d41c1c2400e000100000140804c4000301401d5104860070005070743c1183d000045901034001c1159a020b2203840107000d03201c0501111505454941049401150f041c524180744078040002d1026440748020446a204181c42050b0b06400013581000186019400400c003507049501c0300e4100002c09002030300070080c65100a004c6414841311583e1450001800c2c042c19846080000c005035041050717 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 835239442 1250 835238192 835238197
    0x9060c0f1d031c0507050d03020c06040b040203010908070503091f21241505180d0c03120504030c080609031c021303151a092d16180605 60
    0x1140c40070308440d503004510351403e00c00e02842c0c0103106000f1074900000c00b070081481c0d01000040d515070082c40400c1d4500f91080c0210b07500d4000c008003e2650b40c6498540b11080b1001920880c0d02d50758490303003038000440300006440440d006001071a00d5103000b10602500d07030490a0a07455011401c0c5d504840706400040603002c50740d800c80c200f8000e100c0c2c00c0a0320010600400081e00502d10001d0710f9181c3c00100049505aa6001494034405821414240ea06000e5a40070668210010348414100c0c10b04100450f69540038014802e809a626220340e90301c20b44080c00c880006800003014002e004542c0b00b03980083c110300d00200b40700c0c5001081c00e030f01c1e40a45162118018480300b90102005c120390150387c40841c00ba00e401e00c0c205d99a280c50700100400c00b482a001d02e00300b40300280302500c10716103c0d680d84405000d00f5910b9544001c1c500f00f114400055482c241481001d4101440803000d000384110200b10b0b2b1522000001c2e60301510344100c020340c180c0800c0d2681d8040c803126500009 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 835240692 1250 835239442 835239467
    0x30307030c20030c0f0105010b040b07050a0215090307080c0d020402133b0403090614070804030507060905091e0403090302120105010608060307030b0c09060702120109060c0f 77
    0x800240e024421082110142e006400001d03442c000162501c0d1042ca0110040000c00c0c03860342111090040d4038401c0e4241c890911400e99492810300c41008143c030508020306025215001f651103e0815900144840c103403201440602140411076110318101009040068001e14000f420780f5a94200050206059900001d010b00c3e0080b6400601200d000285405040c081841c0c0354955036019900030541c1c11203101d0750408000507111010400d03181901c1d40102e1301a070350300e064103043c0030042d981b000900e4400d0542000c06c102c03110204014501038000740d4412009040d80900d8030030010011081600700c207108220030300c1031160000042c42c108003840c1c0c500000d48550740d8cd0f4102960315013504ea102940182038040541c600d0081940507038103a43c00e1352136030185a111641415542c8825020040c40e44c0e4410010034511000031000d0b041d003242c001e2500c2d151080c50f5000c1070030300f1140034145855a44030105c010400102c0d004499140005141c0b4101a00203400c0040c0007408581 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 835241942 1250 835240692 835240697
    0x3120e090c090d12020f014d130302030706030606090905040201120e03071719122705071a0a0f0309080c0a0218040809060c15010e06090a0905030307 66
    0x355410103615010a4900c516410014901302403948200182d203c022103040c2c071550b5460102403140401c41d0318202c04921a00768041a4001c00780051007445000d2560109a010302d00501b50f8409106440103001d2102d450724189105495841450f241c04c0803508184141401c1c404180100350344a0300f250200e40b8010030114464075580010703580d03e4802100310010505000d48960f01c5040000180207043c03086114440c1004404e503c1201c0d40941c2441d8280010421070b41d0320386520545003010405440c0200084000740e50a100407001e41d10003070114454000f140c3c40051200c14800000109080301c3c11003002400d0404203400f0303128540e004401d101c0c0803001c81c0110392007640f000c80c0b929071210400d80c3c1c3c0c400c401d004556403014070808a02c542490042c150400c0c40e042c0042d40030b42e50190003075040004e00c0c82008a1500044030580480c49501e030102e01d0080d0b0003412600030013011a4a0466040010500c038040000901c03106419080008040000f1400002c9903400043c51 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 835243192 1250 835241942 835241947
    0x31b0d050316090503030a030501080607210b0a0e040302060108100b151606060906090b01020c0303040603050414060a0606260601030506041107060b19080c061c05070903120e090c 79
    0x1c040660f0024020380029030580f00c04074001c0102c0783c242e8440c0d4143e03040720080300d600f45c0d14094120342d001512503843c02003e009003401012009190000c08218400034116008a0703200d130001210010f04644c01d9005a0000b00100881c8009005010080f6010441403000c40c0b00000411400b00f4080383c120360303007070000074649030000400e10140151540a40c051119680c0c1d408201d02800741030140d050061b240c803407000400c0d0700004003030b00c01c0c1d10050040c0d030801c3e1a040c010707002800000c10548010000c1015250340c600b0600540707108802d00c4200040741403c04100400012201a1342622050038441012022441001c0c4a5100100b4600030403160385040115018000c28003c1c844000000b00f0baa00030004035401c0001c0d0407005849600d1511005821070448030843c4c4180d040a0700004148030103800d00c4802001c1442c04e940070800b1008400b0300300400c580d412100c0000149901809000700202e4028111440d2080d1034566014000d800024602e6030001c4c00c03a25011000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 835244442 1250 835243192 835243231
    0x5010c0c0801090303201606020c01180606090c05040b18040b0a090b1503010e1b0708040806070905010203040b040608150909060406060f060c03050304050c0909031b0d0503 76
    0x12a03518034040d00c1c1c004001c0c070032100d83e40390140c00b92154654401100b01000c021031b090702d0050f42640c15001c0030f50f00c0f5030128040c1d52070760b00c000d41c080d20f030703003141e40d500c03460349912085800800400301d52185c44001041c601d030a00da10101d0344a4019a01003010401c01044031020040c1562848070780ca45003ca02c581960b030000780181070b140100380c1c11140030b400c0000d81e20b000354049000e0510540341c2c02440c0003080c001c440d05110902800002c0340784240401e888840c0400c141c92210401d5000c5441c001c000c0c0c4a151441c1c20175840095a40c1c000710403c40b106a110b02503000905084c0011800d00d41400178015482c05180101c504000905002644000840a0403903d4503400780c81040c181c01c015121079114a01240d050300c059007040c00001d0b40c0c84800940100300c940d50f603a58011541c06980498803984043d0090312184100018101c05036500440e950055444a00640d40c0b00c0d01d10120300b0407400707500741d590403507045840036100e8240c00c4812207520582601244418446 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 835245692 1250 835244442 835244453
    0x90c01050306180a06180207050c0319200a0b040501021903091211060406020c210a020d02120d02031c0203040c05010806130e060712090c0b0306060717121e0105010c 73
    0x18075034040340c0314404500e030030740304c03030445900611080c0e00420039030340c0d640003e1003819174a240c1320b614402441d140301c40000204a070de444010041140401044c40c041e06180000c0e1207940c290070a203044440020704000640c1c040101e141c010311481d100d070a081720152001341841e1894411401044400c91203c030400940181d92030155000070301150f1529120f100080d40c503c03410a45500a81d036485426911588005440c05c0140ca20340081c1001c47d0300d642481560340d01324000300e8000e04000804103240301c090019152060095001f0742e100d1401880d0310042e40300b200464070300e8505c10424040882c40020320101034850a09040a032a00c4880106901d106091075140d552850448950301d003503008141d1501030750f40d43d51004800c007a1400424115100040002c05a4021201c10003002e20340601030343d07100340d004001030700b00300140d251442a023340c0d06848041d07110004541041488541c58203030091000d0042508518410710035130501d11041c004c480c10320201282020800a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 835246942 1250 835245692 835245701
    0x100207030f0c1419090b06370c0f0f051f050601021221070219151a0d030e063007030b15160f0b090c01050306180a 51
    0x55200071050241d254034188a512a290360003100424000c0c0c05000059160080c041c42c0d655000c2c00820a8a901d0440d150000300819440d040c0c0090090100d01c9229610b0049090205903000b40e070b5a6130504854090030060501c1540c1060090a1000c2800318203440c0d0020115940104407540720038403418100d1515103030362042c00354010b691103414600120368010034011002a02107450121f20000c1202181c003030340c203e40d078001d41092814aa50b454004c0c1840d00020349006941c4001c0000036000f00a40303c00805541400700d481980003000124401d02c8401a008c03101c1095a4801e000000d81e8002c00300d501a04120343c902c0c00565683c0e50104441e07011071000c01c042d60780040b40d0007000c001c540d4160002e03610520900001c6989010f4011154120b0008103895a0800d10300102c0e0036540042c150b680003010030b1081e950000701c07038002c45400c1034060720b000c80d264030b844044107241c0001e80440700e0400c8020b100f440b14036107480d075a4900c04c0da08a0303c407a03c41d9403450030507070080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 835248192 1250 835246942 835246949
    0x30209091c051608161b17060705090906010c0209072307050604150239010e0606010c0c150206190603030806040221010b190201050c09190801050712060501031a100207 74
    0x6101c0740c581c201c0e0b00301d0801160b03001c403110700320030382c0107e00d00000e1340e61075080c00c6801720080b8a0411203000c9038038200c2c40242d0b01440505100c140140c0c1500801c0b16150102d0316031000c100c4d41041060301c019401c0302c820740862240c00c40341c54070b0740d107a881d9500c1c0c0d03c01400c0103240d07007140d140e41030098a40741c042e2071400803088001c02403e80c410460b80d00b10001d203413019032030f0140c444552001c2c05d8103006d00c0b051780110b070000300143c3c1c403800011104000b1510302610803c80c00600803c0d4441d45440d100d00b03103c2c2c0c43d40200f0482c01d041e060f080c8940624910070020074504507082000a030003402d1950f102c1d0040381c0c0140c0b40c000d40d034501e40d480e03c0d802c01081e20030314a00d4000b01c0c91000c148060410b4164403099405121000c8209908986040d02c140c4492141803109010710b103440050030322940461380301c030401e0b19a60003841d42500e038113981d101e0116940444003401080766204100c014007003440c0c1031020144141c0e03101c0c502c00129442c5c4d80154401030440590500811051004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 835249442 1250 835248192 835248203
    0x2d180c06030e1f05070e060711100210050411010e03030310091d010912030e0102040b071506030c031110030606480605060306040b0a020304020a030209091c05160816 73
    0x20b0140080748a4004d1a0440e5044003040c10b03141d9054441c100503065a04141d40413000442100d00c1c201000b0384103004050103000c620400046403c1d118580c000c00c0d005a20a00c15184e04007003550016000910000a090080c0c0c014010002e14030380714100c2e407040711071215000601e2038904800c81c4c680b11103149ca500fa0356003050502800c0110460003182d81c3c0e91142c2c1c04000981c840d0840d1400d03031046101d030b0510610140a25400319030050005185020400c10020300340382c0c0c95554a141030407641c0180c0301c45014044200560a002c1c075010800041c6240412405042507405002c0543d1041c0303c041c8055920315590407651441090000c000346402c000a480800c42c81000c2040380e24602151140c4c10a0007007810b9040c001181070155038400c071000a2344d40d80390311316802900700400999104e00d202c0700000140e16a40c0300b440c042c88050380608032010315804070740c0210110504a40070000200800040b005204003c0404280d100f10213a0313450800c0e61680d01a0b000d4041e000c1d28 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 835250692 1250 835249442 835249483
    0x19030218071b11210f0c0d0201140d110414010504060f2003030901380108130b04030507021002300c010f02040602060106050a0c1202012d180c06030e 66
    0x510314012041c4d8404411688203c070780410503614500d03282c542980d074aa40214088001c4401580540b5200b407c0c03c006401540c00c0c011200320440903240e8032001c4039460040041c2c14046170145480c91904482b0a080c050303c0c091500b04000c0c45001031881c04420000840c107001c5a16a09031500d686245e4401c041300d8680c100004014020861a08801d03c0d510f101041d220355020803c2d04001041c3c203d0440d0f03110b034100000195201a001094140c60b448440500b03800103824002290145009540e000e40300c152901c140142e030b07450a4007100541d4400c0180c1d89803000d42402c2d0558126108006034075522040811200c3c0340500d01c8061a15402d01001029014641c3e01a00c111601035081301d0441e42e890900391614031030460803900180c000000d40010410b065800c80c407000301e84c8000140e01c125480c5442c080c944803103c960068002c030001b0082d00305640500c0882c43c50400c507010f1103008958074000f46141610981081c0350f02e402e065090040b051050150034004c1510301c51 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 835251798 1106 835250692 835250719
    0xf0a0e0703050705070c03051506041e020a02280204141614070206030709151407020d03020a17030406060b0307020a15020919030218071b11 62
    0xc00c0c1300040065900140d100e80130745000394000d1020b444028041007030404a2000548054855820800e8950a041c2ca60400d4000e40e90175050050361111021410380c05c045c0240d556004070414010907041c4080382c489010a000c0c400c6504205510f03075108142516a0142d03010005d40d508803500340819401004a007a8040041103814108500c0c1c0e400214158021186140010480c410400c00c803802d119001c200b10b81e080c100520510000313800141c1c1400341c46006481031104030540e8041c1402031142c650916000300070342c0100003440c200000580c0c17040e01c0031120b0710b02e400c60000b1200c180c003080e04d000c3c1a0301d41c050001d00c25507843c4c0d19041c050090044241d15820403d0891f05d545210507030340340e50301e100e4400c0d540d185140100007101804501c8080060b0100c41048449030340503040108040d00c03802c0142110031a41000480c03000c0c1805400c1e0094980001c51 = true := by decide +kernel

theorem cover : BRFrame.Cov 835071942 835251798 := by
  have h0 := BRFrame.cov_init 835071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 835071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 835071942 ≤ n) (h2 : n < 835251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
