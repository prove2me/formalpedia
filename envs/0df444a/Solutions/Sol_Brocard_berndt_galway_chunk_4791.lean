-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4791
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:44:33.464213+00:00
-- url     : https://prove2.me/submissions/42979780-722a-451b-84de-c4f2902b2606

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 861510791 ≤ n < 861690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 861512041 1250 861510791 861510803
    0xb1c03082202062b110a1403010503070312050c07061e020d080a1503060612030e15030a0b0f190504050106030b0904230d050304050712080a0c11031009230318030703 73
    0x65943c909a00c81585c001804c40783c01f203101e007500c403046941d00d003041d203041e43c0010340240f80d03c42c91a200c10f541042c86102190602000300301410f00b2203404c1c0111030160a46483d620550702c2120040403508101484100c03c64101040d00e29101c3d0f817042e01c085e08816400c901140c900d803600151034007114554001414949400c0300056045400780545000034003a4840c3c03070350b04200c181402403014100101c0341c0b201d60100000b0b4074000301d5a103d5650240003901a100c40e0142502284070150480c2a2038001d104038442000540307014000c003405011685001e00400c41d10001040c1c071040c010b440142115800c6000c0c00c003201010030f1021006103003c0840d40040b50310500a0300d01c0c0c3c82030f2019119802008008900c181d100b50800f610b49501c0034940380b4000008c20116240081d80380125546001c7c040312000d2582c0402203000b203107100b40400a41e94070a840c150031200b038030000c03054400ea11020071001c40c640101c207175841c90320001d20014840078424002401c001c4039400040003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 861513291 1250 861512041 861512051
    0xe011101020a0e090117151f09050414010c0c0222110a0f050906030c030a0f05010b0a09080c0307030b15030d03062102130b1c03082202062b 62
    0x556000c05810540c1030196844d059a0341c840b001101d403003409a070b2400d400d034040f41c1703075101c910b0424140715440050805900304007864000c240c0000542907010700c01e00751f2243c09000c107002c156020301070071801c040b008000031320340c2101c0504130080350302020b40300c1c101e11140d862200c1802000100b01c00c0c2c422404001407403910b180c50b01e40f42c000c070200200088a09010100c224010011101d100c58000d000d070b811f5035502210302841b80d00c02810b944909482e40410452401d280c004d05010708030790401c140c0c0300e2110f904010a620a03a500c01d50780340c0d11200b200211138070701044220540b0340000b00a0070740d80c0ea0056101e48040d03218401601032103030a641c1c48030290705030b000703100740c400c0c00d080728a01042d0240420010440b61034003951004070b00740d40c42280202c81e40706075a003100207001c0240c8209124100e0b81c0321030041e00e003600030075094000c0013500e00305ca81c04844120881d80e5601c031180741607000300341c403801818508690b6000071078222441d05005c15003200c9031094608107000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 861514541 1250 861513291 861513307
    0x2010515130e150a1d070b0301050f0f030706021f0209090114060c0f06010f0602030315120106050303071109010605031306090303060b0a020f0d0c11060702180a02070b010b0f09010e01110102 84
    0x20304031901c1c808081280c1294940204002042c006d040700c50348204142140d0a1608100d07201ca880840158441103100c0240700c96101070001c18000d0100b60050030900700c5038003802c04011550f064005405204108170f11465550f00c05490565450848512210a007007012488500c109141401540b0a140810b4605200020303d14180e5609107100010b45584080503681c0e4001582e284800303001c9000c0301040e078107040c882c22284041038030000c501c0998441c0468150b0f4840d85003507800302040c0610510304e09043c052103006101030b140040c0b841c5040b0034010000c1400520082403262601c54000c281440381e0032200c090f1003c5407545559070280c00005c0d41d10440101c4403200c60140298204034030303000311500c1010603040181c540703512281d08100011a400308004070b138403005017450030100c0c00442c20060310505558500583e1114035080c0420700400590010a401038100300400340d202000f010359000490038288070700340d41c80910058591180e00c510035a03d56101150a00c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 861515791 1250 861514541 861514561
    0x60209040c030b0d0f1b060c02030c06040b0706091a160306080c06090d0c09020a0215010807050105070212070302090a02070219052103091f02010515130e15 69
    0x801844215030400201d01e8880d0154107840401110580c8500c4244504000c281c01d04420f60f1031900c101d6130481003003031401220b82d400c0000e4005d03c000404910700705c803c41c01c0c02c01c600d6141716004c07103800c0d0406242a100050a20071350b9002414a6110024001084071480703c00012515031096040649048074108040075420084c0d03800081c00d000c4001001040422440000e80f8040e251500e03020310031040c800d91494050003180d0001c164107000400d0086440500503264042d4041c000b0100c1c01c5890204580043c1c002d1109500411010455a030300082240c0c081e50781a01c8042c1082a0f04c84500d0070980d89610107504030014000f0001000c25590007005154803ca070a03038401e02549480d0b50200c003003030191580081203641c0c4900c580d4880c05406020321044d03000ca0b85844a4000807032480088030b0b20102034000341600e503403030312030702809030b50b602102104412900030b61340b0307001500c80c0440c00b29030780d80d855441e1104c07030f0402d4080c030600914140454201800b410121240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 861517041 1250 861515791 861515797
    0xe031801031505010909020f070204061d0c03091902030a0b07051b03120a0e1e060406060603021303120201020f040e010302030c01080c04090c12230a06061407110604030602 76
    0x1540000e02d4812070041e10460500c0c0601600e0381a9210342103642043c0d0180000d40c80304d2004c8002180038080308c4010b039110301541010b00500b51032604000c00c04a1a00c070002e801402c8d0700701003003083c0200300c4480b4000581005855640b00c80080c0404c2c6400480e0910850b544c029000041c40e80400a40c260400000c0035100444001d800110307981c8500706807240641900d4419032445031002ca4008206500007042d600119000c2d101d21812500031000c400300b1909125150b90045802c1000340a16840f40e000200303014213007985824414110200c14044500005020324051030700c414009100354143c0321524031001c0f0042e611074482c1c003800501c0b4000d2101b24820f22071502141d042e075104100d001d000d0602020100d0900b0f0805002d0f8000e0201044041c0030080b980505451a003070070f000d20780350b02d980c10f890140c40001e45003441e600000001c22401407070703080c490200b20465102d001240719a81201302c4c652078404600c4c00c0c000e20090366007540c0d8449808203000c0103021040e801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 861518291 1250 861517041 861517087
    0x15190c0206191e05090109030221030c16061b02010309080f0c0114010801021317011b08070e030c01120b040f0c051c050c090d02040e0105070306080601050d050d050d0e03 75
    0x1440007208070140b004c580070320802c0da5076400140844d42c2000103092544400480c0f81c0d10050306080110000d0100d480c0d80c1100700340c42607560103000c21884d04c0030055101c1000e02060b1a00b9000c5402c150384004140c11100b60090402d9035500080c03085c450f891003034640004a0041244d600e815120b8110b01030403000003c0700311540440d000040c0c235507051085881020b40c0f088074806d55854203100700003189a204001506548811810160300504030408034103141c55103074103503107007402540203050f03080d40d0b11650b010b507225002e1000181e070007041500ca6001d50391404611514014003240241101c0c2c80c1d80315080c0d09040380da0580c06d41040103031901c10404003400c5a2000d070600c1260079035a040e145018140c1c8100314006107414502800182240080c20108182c64030954650840780115540c10020359155014030118800380012801058200c40743c021100d0790f0385400e40c4070464030008005114002640d40d03450b41c2290001049140043c0c20750f900c602456a420303400080303040c5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 861519541 1250 861518291 861518327
    0xe070c0606090608070510050c0303010e09060708091f090b0a09050f06040f17120103080301050a09150608221109130f08180607050a0215190c020619 66
    0x40400c40d8001c070b202e03200441d55440002c05c2c0540c9000288159004885024010440300f0810014940e0040001307500818211150551603d008013a0500b00030000d1300c15400c114519041c024004000500c0d80109a00d10b2983d04c00203604420078401002a268024050410303101005151050b42d404400002c3c054002c0d00c60018021003001c1e26140304580007000440c404080c200810407291140c44c20f0911541c2d42841c0680e031201a6512250980c0308840b83c03000000144840e050003000c050083c002500306000600324004002c400d100c06000d00000c10440c1c9000406d030240d002d41c00300303455100c4060905081d010f42801601500c5a90035680208250b00c00710760841071000c44909030b140c03c581c603d80040840c0e07032036050b00e44c0310340150b26003200070703014070100c81d5919001801d20324807600041c010380c0668814461000d044106408505030103100d1001c2506884400d81e40d008a2890304e86040c120510020346a401120a00071440388000045000103030020004140614104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 861520791 1250 861519541 861519551
    0x4080a03060608070c080f0c030c1b03010204061b021f0201020705010513050312060102070906061d0d020303041802160b090606041a09060d061118090105060403110a0e070c06 77
    0x42000e844490f001c0c0c2e42d42c07000500103c2254086840710b40640041000410300c5880e24903000b1080d80703190400070002c0310940140c10043e07988600ea644d00b046603c0d0a034029401c051401c940035040e001c2c1c0c142a941603841c80c0010600711b55818090701c16040350f01c00d41030800b10300700038024001e411503c4111015881c100104100c08658142c51501079071000c02507107440d83c03c804034115518003401c90f5040d03205080000c500c2400310702603c000380c4140e94802400c03640700000005400d0120f0349450142e105040c405015071804412501655084042d28198060f1904108001c1c4104001c80ca44d1542c00100b1408100322091205d020b00c0c080c0d0100c4600d51038003420070045450845003a49070b41c2103411344800138149600302661011005110b1a007506081d00c869080c8d50720b0b2682e440154800184244c10240c00d4a40c070b03203190400b540c040d00c5541c14080031807032a00c02e60001500c1038940001443d4a9901d90800030098a10b01c20324012500b8803078005130468010440403140e40d4201 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 861522041 1250 861520791 861520799
    0xb010e0105090a09060e03030112030206220b040c0b131409090606010c02150a090f0603020a05160f0f0507172a0a080303191812030e01020d0504080a0306 68
    0x4102450507607000800c0d8400c1d580f1904502c1006103050002120b0840d110b000100210b041440554004c000448209212500c01d290081c2407090042c101003800c020358046800c01a001e076030446280b9800000c1401c80e8071107081030003035440039a00c86100d9500c0010720560088100941c0011121080646028051014200a0140c00032943d8140036485800022003d41c446c50b6203850707107800500441c0c40030f1001e0203500500c1d4030640b954800f00700c8406040214035405210840105024502141008040300009109224860440b5190351200001005000d2120400a074590740400500140101850240d4039600a4813420207820b10b600e441411084c0f020802021040014000340e201903019681c84101000300b04e00030382c100d00c009c82e02054844040005501508400c0e40213940205040000c40c25940c2090a00e4a1040440026070005a0303600c802003020046050100302c80c60404802c1c1e0082c0a002d50031034245043c0b2041c8024000150002d001010311550240101d03502e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 861523291 1250 861522041 861522059
    0x806040c0311030c18070306080a0b0603150702070b030705220524032d2802040605120c0f04091505101b0c091a0111070510210510030b01 61
    0x4c07a400341d048088249210b0032210100c207100c3d400301e45c6080c002441350710340341c003d8608000c070304080359a0001c050a01400d45020000084500c2c080080710322180340c0608000d499038080d1040d00d044090100105101a000314161344501b0501110451084060180303400c54030164407480313001e482040f00c5508001d21100b050300816250040561850301d50088041601c0d210740360a212410000300503c51b4450100340490180441c41903000b6a070072010313000000298902d03503584d80144100020400190400142c42002d11410360001c016034400107200a54401d01c071101d0140301e800039012503040c0e495808907410303854010b6900122601d07541801031946c45524024042031174000c040010400c40e41c0030903280e610844004e140140c0e83d07602c05044d038503505048007000385107100d030307d50300e5074000b0058100c1c2c016a0000c0c50b45921f44804205003021102c044010411390014000719103034507800036240c6000c465000c03c0640341900c150580b1107132038001142d400d85200000110202 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 861524541 1250 861523291 861523303
    0x6292b1d01051501182606070c0b070305041401020a02030a03051b03160519200607090b0c031903020705120702060f07050a02090c0a1b080901180806040c031103 71
    0x204000c500c02141c03451000659404550b07510b1000e10f1020080c01242c0301c40025021220f00c2d80c2e4040c3c08000e20300306d2001504103800105208200715040e0140c801080b4824040d64120880f07040000c0e183d03c3d0307070405001c0c0c8a1035402c0d400303440d8000a0301c19411a030000c02050104241e0354204816119241c0c120b00c0c0209510030b0301803d00d414804510344d5807506a0301101446281401c600c1c040500328440a55420021188081812500b5061644800711241e41d40000b0b030340f02a00700c620700950050108025401441b41d41080825000e011171400c004407003d8040000b4082500c811a40707005010394084001220030740190034210a1100892060703603505a8010100c50a0810b020a9039141e0381200c8402d81c2e2620514000380003684440d00c600c1e00800111010f9942c0710740c00000a40b46000448441d014401c01b08a0f100c0425255002d0707640d40e500c01d1030489880e0111445c01c0104080c142c000d8603890140409100030014a8101c1500b1a88210000300640c240c00d030800d501c400c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 861525791 1250 861524541 861524551
    0x30604050f0c011707030b010c05072c0f0406231311010804080901080c0d021303140f03180103240503060a050601120f06180f06292b1d0105 62
    0x84400f04c04200c001e80039801c44511180306151034502e03140182c440c00e01c0d2140c25408200c0c0003c807107000ca6650600140c0212000441407111807560030942c02e40f00c051000180094a0725036281c1e400c4030460080c40d000c28113401e41c662400c1040c2000d840b402c4460505810844820f84810b2042a00b5401194000e101d1030b0044403503030400307103000015107c1c100000c2a816202400300403440c00b094451002d004e01c503462025180b0f2050841c500081e003030101ca10380c0b8001e039121081049203040d000080b80c100200001c46c0700c000304c0200c40164050007050342e410100501e1407085103516904e2040c80000c54800f2000c50b94151a40b0321000b00311401952554000f641d0030072000c5410325030b40c20180c1e071450555400103d072965283c44040c41206030400e20509510361950700300782c2d03403103000715005800c1c7c2030071502c20700e040480e051403d07098040300f4040f20070700810380440c490040001b258912401c42d1740901e035a044860054020038074070100510800c0c000c1002d007407072601441614492 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 861527041 1250 861525791 861525827
    0x4050a0903050711060d020304202407020a0305061905150a03080724061706010b1606060302060703200a02060d0908090a060306050111241302030604050f0c01 70
    0x103a51140000b04160010490b00175404119081c4d8900b5a1310082d0300c102e008202c0c141981d0b0801541c84400f0551803c128842c0380201c24880b401905114910181c8011004103617a07a2802d2010820020040e44081d002c1e015400401c8400300c1c5c1280c00e0307401d07031043c035604005940d910b0704020101e107030403e055600b1220605040c40000d0122006060250185141407115039200d02c036413800c51040e4034030311901625501c04010644400110341080c0c402180a009a5810502d140c100e90256101148041c5040ba40800070b0241d160b0101014640203440980c1d01d50342d609001d4425451003203240c1c1c40c02d4244030030f01008003000c034501c1c0d21664000c5c0910314085da211030800c040d00302e00e81c00740ca100404005003a8255110181b01000f450305881c0864407a01c0c00e00098000050103036055459089811300414003602c0d0041100310b0f5485418034441902e40300c445580300b50345888000d404d071080354240028031500050445140281c041100e036200900c400444034032a04901c03000380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 861528291 1250 861527041 861527047
    0xb1308030402130207061a010e0109080309060a1125050d030f120e192d20030d0801080f01271b0b070302122d0f1804050a090305 57
    0x103140c80070410142200040c0c0250170004184c496070100c45d2045004010034490b007100090381d5810425403a2440c4090800c4550a4602181681c99100320401e070341c494040041c8844149004149403d20303002c0040c01c4070010311035103a0040340c40303000031843c9249109103140041d09207007150841700034507819558940c6c05014590180c410305800c800403248151200303484407003d80e042020240103603440880e004045607909100301c410106180b0300b424009085241c00082c42c044c641d00110b0b07940b00101084501210052414004503103645a515011b0045c4000f641c941c050342a6050f02d4150701510f80066410412908880070005084a102200b0a1100680701e11003503561156004030225031340340c48041c2100d107035240325402900d90f0302e40c003182090503d036042000c08021040c502c083d03850104480448144c0d5804022a2241801030b5042640554080d01c282c036200043d02043e02d031280c4c02d9250395400b0501042255004a00d8400003681c45a51030059042041d099110949 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 861529541 1250 861528291 861528293
    0xe04060302060a1404051008150102012306040f1113090213170304030209180f0106050a05040504030915091e050d020907020a0210090501031506024201030b13080304 73
    0x9051803e1380d045548030042170000142c40d40752500328808903442550740d25841c1c680495442000c80420051a0440e85014400c01500c5824250341000481074036201c2030640d01c00d0000b401404400300d81d00082030510741107402030b544e0803002e44110350003561001d0002c3c5d1242803c001700c3c05802c4002a10440840f81001a42c81c80040f00044d0b90041041c1e034641507c2e500481c94ac0541600d400d2242c0c8010000e42c001c0c580148204800c1c0c0200c200280a81440c00c00012200c1c1010b0143d0344c0f045039244c0114017054020890403000f0700c0001c662030f18004d01664040c040001c2032141c403100c8460b5440804480100300e8a200c15204003c02c3e440e0080b4040d0240b001c0c82d00001c1c49038055110b200399400140c0d07a021140f0704c2d4903155039580442c0394288000141134848804d848280290206410300101750003250081b00c4400b1720140710443d0b0a04007880b0303401081d0180b800c08201d407100c2500100e0082c00c500c28149d80c05458001c0254480d8030303003406144183c80c8054020642400810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 861530791 1250 861529541 861529547
    0x9010e0c010c02061306180b0a050405150d0c090611120406180305010f0906060506090d0b071b080d060e0405070e042301090c050f060702151c0c0e04060302060a 71
    0x4101c0d90f0020381241c1c1405551079802203100301d190010030201e0300c040300340b9003150a4103d68001030650180b040382400c4821902401c580039501802e84a40c0200d80c5480c11078841c1820f460407031030200000c0c4114020007030058403000d02805520000350188060340110000029802044003418201074038261614108440603d016102922035000c44c840c0000805c00034007403451070503125030000a86866034030f080d10403030b4a264401409545c00b8400b0408642e1040000d80041d90041d10900031607981c10740407511403d001c8000ca00800003d5400414080440058000110100b00030842903071213001400442c1d0044500410301d80c84494240042c0c0b2049a00581251269200c00c03001c00450703002c0c0c1c86424030003100d40c0c9560f41d590036140a0040304105d40009140070740c0c00340e0302e0300e0b030040c0420000e01c00c0b15006070044401019a51040015004039a240e00396401a405503070301f4a5400d2003d008000c3d10400046c1c1c01203411030041c0703082d11a080c12a03500804440c6171180e981416 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 861532041 1250 861530791 861530807
    0x20f0c031305010f022d010e0708070f060f02060f090309181005010306030f080f04090e101a010c080f2b0b031c080a06030203070902070c0902160f0524090609010e0c01 74
    0x61b040755250310700034540000401202e00507203265009016401d0a20011402000d0f055225400704200b1201000700c003034010544540007186592a2280782c0d807100101461845507050035508480950a041d05600a179280540541851030005040c2d40d034440c0110142c1b05203010140030b20030200e50020010b503041d002000c94021109583c1d06151342c4019060480708441070350351503070300a03013065030f10250380d4420f58424102260900549180000000300a50b50700040105100c0c0001899000d13101c2c6001525404000e16071074000700c44030500e589030550300c12150222081e090242c00c000a03e8082000c01b61044040118146c628118000701c07000c12010f41190700c0c8654554010015132001e0042c40c002d058285030150382c0d02d94030320700440c14846a600c901d030601d1060110070b82a058600759a24074582010006002044a0030001d050a89007501c62810704590501c0d00003031114203520706d120340c030700d1426510300750f07200b05065080c1c8a20752030800041c0c015a20089140d8050b03004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 861533291 1250 861532041 861532123
    0x20d051e0f07110d0c050d020607090b0a0306030501020a0917010603020108041e02030a0818090903040611030f1201090c0e0a0504051306050907141801050103020f0c031305010f02 79
    0xf815100150595050030a10018810000502c45044200c2806820804401080c5803407005059a1074283d00c000c2c891095805814124040010000042442608280040c1d03800100031552004245000750152002c0e204100d203040c50a40d1900c020308042c07280303c0031660103843e80422659940d0361050246a410481c0a48807028901c840150f10200440000a885001055030700c0d0f00c00480381031002ca1007035103d44943c0d840020400e250002206a5048803030f6030802c800c0381044c2c150f9a80c190301911012110303c19012440607802d03080350b941d082c100c0d07074a0b0400300400746800004540e44e0013400c1820350090314042c010005070800380d01c025403040613584841c640405607524042552003d8407001c150351f00c0288140b000051f0b00b440000e07524030440d102c03c02e209401500511b2010148601410315501140d04c2141b42440d2049a0300c076103503c030580360b803010030b03030300d140030204150083d42e00041c450a00c0104103400001c0881c0071841490740901d4507110074259803000c040b2005 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 861534541 1250 861533291 861533297
    0x141e060f0402091e070201090312150b18090709140f0906100323040b06030f341205010f020c19050a02060a0f110615090403090f0603020d051e0f07 65
    0x44411181350b0301d01e0303940703020344880d50010030225058140101060002d90200f111a840c00e414661080c0c0441d80c00c1080361084050240ca0365490001c1e551401c1441c80c440fa0440400c50070050344640c000f61410913600b03004140001d0f0b400c1d00060104500c1c084101e15003100800010480514202e40e440d0200a603c0c0740104407a06401500c05c00c030101c4440b001c4154810070140010072041e040d0300341e4031142c00e42c001e0001c003030a00300d10740c4e40300c00384105280c080f890340c142c840313201032418452920028401e0f408103089641d0408550090408002655154a41034540f0803450060080328206da000200030010454107070000c1c81e140f50340f0703403084a841c840da21040340103031600b4000d000c01e1a4261140409400e1105001d06003144030030104a09402c1003040124081c2c2c2c110300300c08102c00c02d5440d0750b5590780350314080c4c8020500380c102c45e40450701c0031800a241d0733901d50000c1115401a003070601407510741c034501411402030182c4001000440c040010b20340d2031001030040d401300c1d6a00d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 861535791 1250 861534541 861534571
    0x10f091b030b0d0206040909060b0405060619261e070233010905010303110105040203151e040c05010f021903030b060706050a0b041b090b0a0507141e060f040209 71
    0x940028906e038043d80c80f1984c000c3d11501c01005000080c8106602c0c0c180a842c140800d141800025100d84104914540c42440e076070110494184180c501441c4c2c00e03000b142c2804041d0100702e105a407174104486210302810b071080106103098039440782a00030407164004040744442c0040c6076440c0800000400c008007440c020380c1e2070192120003058024451520002059411400c0c01804242e41c045961074682c1410203010068400041101900c480c1d00380310022902c5004910b00c80c060b2042245401c040d00d00c00348800d00000c405213400b240c400341ca441154080c500d00582c0c40b8458090340307025074504004a0000b09000ea00310440e12a4001e1402c1e2400d0b9040da80c0e101100c0050f5107240c0881ea85428005585c201440b410502051024107814000c5030820003c10361000c0713000c1c0390b00200c0003141c05c0021500400a903003c640d0300c0300080803800b244403503051351203100104c43c1e808001001400340c41c850001c91018094212410700366101e689580902c000c401c0050300c00c40f0340c00c0d001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 861537041 1250 861535791 861535793
    0x10b03010207140f0d05030105060d0e0f101808040e0903130f08010b0f0916030e010e150105100807210c4d0321010f091b030b0d 57
    0x3880204100ea01c103030b20700c4030b81d2141d5900f110b14000c1502140100d40d400007000300b00755a040001d0300d0440e54200c60b800d549080349041840640302c0031015090b1817041c0d0440103094400130071a070101c0001901e080000550788100101c1c40300701d210001e0311a5100700004d1110304112a26540e00a01d280210303403400781c900c218003e140710b036030f809081c0c604084102801005428020f40c0e904100172282e041e492281040025268040642341c085502da03254840d070301e528000c0d00301091040d2108020040400c000340101d0f110341307400040201100074240007198501d880004440700141580c3d50903160390341c544064455800c05c800d0035003044101444240801160b000c1d61800c91001e685c1c08003a8416603910501c455085244103168541c00c40c01e444030107039044a031a02050034411008404886003000c036041d4840c810740c2040354544d0b9010f020003847d58100b0a81201c0d1406500c0c0c5c416a912560141143e030142e03403642045410b0101d00241600c00d0b0070207100d4004c010102c540070b6042e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 861538291 1250 861537041 861537043
    0x60518060f09040906091e05010b100912052505040b09160804050316030504080606030c150d02040b041d180607050a031508010b031002071a19020a1701151709010b03 73
    0x18288141d04a0121804140c0c1000000c0c014407080360402cbd14403125104080c2406856658140a584074180703c08001c101808801c002040424001001040b400c010b4001e02d034030385090341c0c0903040c0a0741c1450720042840c140301403210310544e0b007400036001d0a0304400c4111007881c8054410b485a00c824010310f844840c802604092003031103034a0f40d0340d42e18500018581000c0c0300420140c1300350440d01c3e608149490b017000c942d82080890151954842c194010b8a00900594100503000e400c08100840c0c0103401c00c0341d2005000c40606001c185a0b2442560303145034101e13608590361900040045103005000e14090079074240d01e1708001c5800c020741e4040c8880d40c0b203142e1120440d61b440d0b25036428542028400c1d9441c2c01c42640b425881e092080e09d0b03140c40c10581030007007502c00314104c00081003811070710000b01e4071742140c0714150b5480d0302d0604001c204008104042030620110790001484200d070081070341103000076072100d03803400480b0700c000750100300002c10703d50071035403108001c17000385d82c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 861539541 1250 861538291 861538313
    0xb0408040e0a0504110913060c030617030a032d0b0f030a0b0610020a05030f0318150109050c042303011b021501081f0207020105090a060518060f0904090609 69
    0x560340070000f0b803900c0c103400d0440c002c80520600720300810f64102840300000040c010f00d88800e4100d04089560780300c24500310018140341d404002801d17034408481c071315a04040000c01804406a5051086055007114121014041c010708030910030f41d00c0041240c10110b40044203007110080040c0d6003d0f802c600402d00300003415204983c071240c0981003124918201000038402e0300c591005000182e81aa5881d951340300e58204810700840110000d00b100e684100c8400c0003107050400c0d101c812203000043d50707180e903081c05000301c4141071400003000c2d524041c1c1603904481e6801564003203410b52491044000d1f2400c60342a406540321442c6159104e2080c619840c000c0d1160b00610640c5243e03510090410010b802070b00c155080342d400a07000006450304091000098a00165030301c80c00d100507606e40c030600c9045070b0002e010040000e80950448058190744604010710110a20408200f00c2c8921070700c803050310304200c1072209540606083e0301c0f084200e03106020015091400703480e140e00d010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 861540791 1250 861539541 861539551
    0xf030b12010e01140c091905040c05030a0f14130614090c0118030201020c060c1606050304050f070602190f022e020105060a03060e0c0a0f060f1701030b0408040e 71
    0x1030b46403034401000b64000d204003003445000455403000c030300300303d19030340013611a245007940304040b007540302c0c3e03002d1020b03240b002d0091400501c20441900d5250b00078103250400c0b01c40c80055464051180b0a4030074502074843c1d1080450801c40d6941e65400b190b0700741c071880e04400d48001e82e68600c40e00003160058800c5020b8a40b400003007502140f0f10740018240c88859405403540712481c02d007080140d8000902585138241203d01d1a210440811080c0c40c0c0200c4034209484105c08260006519030020f0066004a0017030045c0c4203011540c1d008199140c3d69440b407a00160f000c5041c0c45000840c84503545992481040c0b048541c0d24650001110581b10300d4070780c3c2100b1181540d600c4d13180d0000381d00d000040d00c140003d001c1464000e0004841c2892444041d1145482c1d014003600d201044c07006d1148000c00070806140d25440340d016082c800210300661000c2400c0705d41001c003050045003038a10a407402520020540e0170366456940c0e448020b001140c210405000100d80c0c45100080c8034440c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 861542041 1250 861540791 861540793
    0x2030702100801140f0901050402160c030f1101021f020901260601030b031b0f040605090412030617071401090b030c121b0d05100506070c090c05040b0a0f030b12 71
    0x20f5040001580910307510b051071500c10061640d0354001d540700c601320b40d41118012240140c0750210704502215800c40603200400c9588140c2000c810008543d26100d4001e00a100500303a1340390410040e0780c1c4101e00300f46640f40c84a00d215005064040350000c1820a2042c5010340701244881e62100c002d4515841c04640b60501030104002540e15201304549240e0440040c080036542e80c40000c8040c00d1510424000e0301c00110888064840380c2221004001c00703041d500c0d10349018280a040d141d40445d8142c00241007420000312640c2040300101d020350341501402405d071800a0307502e9405803982601c0d052103a0040000741520045024600c1280074031b40b0541d8276034403049440d488180003060b03c80380700900680210385408134005c0c0c0e00304151841e4001105d0301d50840192001c5025445990f01580c001000c00810070342c81805030844810340b5043c480a90121000d407480c1c01680907040040304240000c14403c0d1094144a00440007428005160b42c070180101d40d030800b0740c402100203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 861543291 1250 861542041 861542057
    0x290a1d0a090c0512221514130b1f060509040e0f030c0d0915080a0608071205070509060108070815030303010f05100f120e030c0a0f02031504030903060c0203070210 72
    0x144131344000c01d0715030044809030407101340010103501c214800181c3d140039240700a05c0c40282920343d10355000c10003030340c120003101e041840d210b420019030144514080706c04c0781c1104046148840c40c05440c68a41580400340b140d00d5060480c12941c50308012661640542c0b14003078000e1a00d400c2c440019202c1c5200083e40d581c8042071440c0f8504044440300381c08124410608000c0150300403095070000e001c6192580c81a11103158140103010540c10402030b500030344000160b210401d80300040081d10031005d81d04d1031903645042045510b030850302d042c0402e25038800a0113039440f410300d4070791200c42882541803c2e4211400b10b441c6800982144504074003282c070900c010703d0a0440c4101e03088044c135003c00b0b000d020310001801038550165044182d0703140d154010a0b4a0305209440200b080001210001b02c041e0900c100c0003500c3d020140d0003805070806140c80354205108903481030341c02d42c844840311850740d61814014540349030360320304500081c060840166036542c02c034a00d075100c660799212 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 861544541 1250 861543291 861543307
    0xc140a02060624030c0903100f05010609090902210f01050f040309140a09021308033103030f080a0908031008070501091d06030313290a1d0a090c05 65
    0x70744035050f0844090340c03540d41e42890240400008030380c1e100442400340354170344041c0400710385000d2508144c071098608000440110104039407140341210315603035a15020f603076121104000c032494608083d40014501d003580d188001c10b20310301c030010082e02c0e08a640f407050384480b00d4215407003992170003850b2218406201c10306034080460b002800039160354020360f4040301c1c00508410030500c1001c80c10b81e00450441d503042d0121441000405401c002c4e650b988400103583c24001d506201c800da590b10444140d85842030300f008040007540d03455291000519105141078035404401403048241e03e031903200c03410000340001c01560103081056104501c0c03034201784d901401c0c08469003215040041d54441041210142c0505030700d070014400c0707258038545648011030708520903031810501600721880002a270504061220160550344d42011002214000d1180c031188540d048000005500b2415074420094054625030400c0008088150b150766400788142501d0b080c070203d8002c5000414005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 861545791 1250 861544541 861544549
    0x11070302103b121e01020c01020c030301081b0112020904021b010509012403080f0c1f1b090302122b030e0c241303061a0901030b0a0c140a020606 64
    0x50415842200c521102c80140040036640360500c1803040d44c000180c00e40100586801e45c12201c04044d40c0d402999a611070b600810f6481d031081c8189112842910800d02c11002038413012060300700140c0d1604440e0003803400084c003a4201881099119134204202214807000c0d5401070202c055003800840c0300d20b4094121401c42d10000b030000749403a504108441000039005c1c401042d04da0001c0307640d4443c516500e14807018001c06620816a2143c44040702e80b0b007001281980d42901e60000500c824000088481803003914691604081448007006000620f014190301094510f00d00071285810b0401c034185a070030184466609132408901000c5040eaa0b040c010700e248031849400608001019501180725101034111105030190903086860007050301c081100e0030196040b03031245000703031030342000802170204502d010120031000941205a0a1000d1000d0480e50001030f440c1107980c1b10581c00015018041404003041201c20f4101034003281800036000750200d5074010030040c40c0180c244 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 861547041 1250 861545791 861545897
    0x21210030312052e03050f0a0b100501020d0c1509060e07050604210f0b010303050a0917070303030f0908040305010e0c012c060d02030a050f071107030210 68
    0x10315420a42000030440c1d80c3d0f10760804001e1030101c2c000070b40c059003140305070201040e00001c1c050300445c04021004d8000207888002c05024503100030881c1c4ae84060041a40b20912030640542c00606c109001c2d58028001802c00f18010303c4884907036015503440d1021695141d00403146d141e541d41c445220b02804005c0c6c41c000c1d0000707843c0103280c0782c01c0070300d20080c01d00c0007000208907140f045907210030454603803001c0c0811640940300300c0310784d61242f6000d801a0806c0804900003144443c0020702902d1500f0368240402d51900a000781a0440c0c4040340540038850108528545400d191000a4011740c018801180100700005040001c07100711405c20b6034103207049042080a84038000c48042089010070b0302c400314245007040c440800c1c007146860180c0d0042c14000c0780301104000f801c50954210300d10642e0728403c002c200f5600d001040c0c0d080f8141c3c0c524498250710102007440142040d00003001d5081e0242414820085030303192000e51109032011654030398035a55025061100d000c412 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 861548291 1250 861547041 861547067
    0x3072106140a0b09061b0f0a0615051305151909050f01030309120303060306111e0c07090b12010207080403030201110f03190b06130515031501120212100303 69
    0x520030b0300c54038001c482442c600505040078801c420010707a0354015910341e500c1c1c981200c4144181d400c010b090350201500c0b501d01d480107841a6040602160aa501b4552444141d410041c807e029003c0600804001014000e100c004110200c043c014041c4da00c0b100f4030b525120b07030205c60325200e030f09003003120003034a070040c01c98985c1421003001440001d0b00501950192038428003002e02e43c400f1030038210050f00d0b40c0c0e40040d0101d40b0300901241c04030351040090038280e0b49800b04000500321804e40c90224815007146812542041c0001e00401c00c5c01d40142c4d08141c0018800d502442d20f10300d016013280c0c0000c004503444a400a820400c254082c02142503601a030b40401d41400d2581c8007032251840028a10020003560745000d4130400e007198444a42510041c4c0060f440718070100d00c000c45206036014042c820140d403d030072000180e0540c21240b042014030600d5007404c54420042d284a440c5801100b68640c082c8021550504580c0813035200d40c00d54500c000500c0e1071420003421038000c0d000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 861549541 1250 861548291 861548299
    0xc0916090806010b0a0c03031806050906070215180a0510020c28060e160906081005091b120a030504091107030914180109020304032c01050307210614 66
    0x8010032213500c1c408103403108a20b02c0d0911020a0203030b03107130031002882244030102258084d44000301c1401680c0c3e110340c0c4110219000c840c034076120f5031001e0346c0d640e04803003c004800480100103100c00600311780440f2000b0031031003183c100d00100d503190303400d016600c4110282c041d0302041c140c0310320b0010081c2c4011051131446200e0204600d03254560504900080500203546400070070712952020844061001c0d0300c00003070700c5070a44503000c4c840500706030311456000f1b104600c0c40c00d207110340ca07104d95030186140b04020854034a1800c0380c0440c410482c2e130b10a501400d800c000040c024418003044070805d01c40d9a8071540e41e410b10400070103d40251040a82d0080e042c8078143c00250041c8140c416602d11603040128a010071000444c041c030070007004e98081e0902e00001039202002d0300514043c40c801d440e1040d49040d22144010381c80c0d601810a038145440c503600c40c0055004d0001141c00400e00e1411380108040b1040310112000c05109005a050341c402c410007140c82c206c4a040c5020000721 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 861550791 1250 861549541 861549553
    0x1020f121608070f050c0a050a02010809030a09180603080f0a090e160809030d020a0e0406061b0f17031303120615110a0f1203050a0504120509030c09160908 69
    0x40040100034003e103050203000f144c41820321002e0042c02900d151a0207602101c481418620b051034480f0306a5204074041801c1c2008504e0b412130220580d0070b154075aaa0321000c50703182a2a0800e600300b90b018850b02541c0e03031a004004031ba64040245080544c540300c0e6603440c000700c2d000501c04811035105110f5162481c0034400a0749028072810358035005803408905640b1b509100744d046103e00c21200000c148001611002250807261008041c3e0003110200b01040d618182503c640d074815600110f840f11000d202c1c0c0018000c4c10140c01b0060190a52111503c081c0000350b01c1d0358401d0300d842c420107681c000328100b0158881c041c074400701c00c054001d0040f1450001116685d000b10307111001444041c260040101c02e081140c1c0948640205031440707080803900301078070141c0e034080410700042d0031720001407910701040c010b441c00750358860160074200000c24000c5801e604660102681402078420300e003402d0b40c070f0900303035030264903c0361100f240600441340c05007414410b0b80c01112103402a03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 861552041 1250 861550791 861550831
    0x110606010c1104021e0a180807050102120a091806030506070e0901150c02031b1306030203070302010e040f0e010506040f0509120703110d050301051507110411040801020f12 76
    0x81002d421040d00240c4003d600c0d400c20082d00d0325103007500c4501c103030702003c04180d012400764030015210f016800d00f9252414030fa02c0340b115580f24040350003024096444001100702e0000884010010016507143c40000d054840c800311071190b001101606503140c0b0f9440c01c4c42800410300c03405030801c035141000c1030384110a0010440c200f005100e005d100c1c0f2985441d460107540100200c10714142c0c0241580d030340420010351403025816440e0868014a6186194020178074188126800e83c0d800500038080c0c00d1456004680e890381e503540b01504075455000c07400d0b0025540c0a486100300181d80046814604001070008403000756020f06595800c0c407041c03103000319010840360001c1c00742030b14450b664603103410256201c0c492255030b45480e00c16442c0c140b071070310360003805541030300c000304c0340c10313000b0184124405500e014a003c0580212010040400e0528059200010007c0c07068695070500d5034603070b072160890300b100d01702e26100240040e424640110388125a0747c0207071500c225440e25464 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 861553291 1250 861552041 861552053
    0x30c0f0c0b0603030f1308070e01060203070b06060c0a0f110d0f0809220c0e09010e070c05070906030b01050a0806010e0406091505041a0a020f0d180c06110606010c 72
    0x1481034040d0505000c81e000c95400d84081c822141414020349040d5aa10454880e600842c09a8032980d600ca00800c04041030801e400b184c160b04841043e401142000e109443c2c02d1106880584140d900080c10084a4500032040c808402d10394082c1d510001d20482c0c0381018440004c02c58a500c0c4160601e290304070010700000c44008502c0d07001031109807034080070004510b00d0b11800e0741006400b00d241815040c0a0a02e07088501040c815954a03c00d0f1800e480034485d103d40203005500318469440300180110b8494400c0d070440e14029400c861102e41d8614204c81118515001035450b8580c51006001608003c0b03403a400403c421350080c442585030018201c000c00002c0d20052800e42c592411070140314000c2da01c0550002c84070b004010070704180c5415a504101c08100e80a0001e6240c0012801e400034420349000300c00f41c24040346000103103903244c00246210394004a0914640b01c03001c000c900c120120001600305a103c0e816225440c0041b0340c40c2140007480c060401854507501400584 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 861554541 1250 861553291 861553307
    0xc091205011b141c0204030614090f120703080910050901061716060c1502030a020403030e0103060807060c050304150c02030f0303040206070f060b040c030b040617030f0c070e1501030c0f 82
    0x841c00407050f000481c448004d0192140364005021241007040c9a55007404082c451809040f401040b03490001b070440e0081e44a01e2030392200d080e4a40280701d1000402d000c1c0c81050f40c004005820348098001c464400d0089070415940c0c07101d6a0356600007880180300d8406d00902040c11000201841c10540c0b4003103421402038060070040083d01201038040005030380018551000140b000d545903d04003a42000a41040c44141d000969800307401006500a00c141d4054130203940190516038246841680c10020440741100e06110401c800142083c4000061020340a9555000ca10125600402d494008444500070250700200280070042c4d8518085603600ba60003012546d411a15003802001001c04144068101e400c041c9601e040c241c0c161b001c1d80c1940c004440400407d601c0310303504084507801042004043d07008101e01420300c0d1150015001071800c40c4101d4182c0c5031100641c2401a005a0380107201d00c00b0882010020341c0c142c080c0d8400011a8a080c4981602039080102049 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 861555791 1250 861554541 861554557
    0x218061903020c280b0a090b07030b12150402030f060f0106140c062a070201090504050429090114070807120b030118060c0309080d0c091205011b14 65
    0x1d0340c001000d404042c02800300022081e04005240441805a6201041030103142c4c1c088071400c170300c5e40010740e88a0b5544103d001310380c0c00640245550340c40714030039001010155070841e03015840020164800c42c3c2003001003030004540380400c0803130a040c418940352200d40c01d2603143d10341184007040490001c43e5051411910700d450a1580380e401c10710342c43c00c240710350502080c05000d50401c21545918400d180c03041100341000785c8100304c041c0c01240b101c41c01038110003400607100010410961800c0e8000380d8100c1c1c058290050702d200c0d209010b81d110600040e03012110b503000802c00515402c28230440c000200b22a060510600e8448002401d01e88020040d2041c0b14450900351810a0b256004100b0f03040c0c0035000b0842d0b40b62a05103154030b0054084120780c0b503424400901a801d00c20b0040704c00c6d86521031015400d102c4a21150701c0540b410b0703902c0c034040141070751000842c8581001040c180364010320000450795211003005202d21841c2d0218001e01541c1450084c410160500719041c0c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 861557041 1250 861555791 861555797
    0x61a090903070b100f0312140c2104081e010e0318060703020f070b072001210e031b0c041505012001090c08160e0c030c16050102180619 60
    0x40d5544803000000d0712039541142c00f0750503841c1008000c001c51040300c1c07000c50f10307503403a80b0b002c00c0ea80b5803008c0c10350b201b1030340e114280e074012a800061204510084241c0c44034280d1031581081d8655000342e117071100d00c0302644246228840e07440c8145000784140d01c0042c800324050740c60050100408240007605241c01ca0241400040384001d141c800d00c410348075202d020080d2102e00e035940b0f10f074510b5904503190030349070780e4280c2000c200d0590290b0448100d42906840c1c00041180340c146904c07d40d41000101d1141c0c503122141d81440000c10b00080104080780303254040d02141180c40249009a500710305070046207030001c942941030b50715004c00700700c50013480c0181010412551001c00301c541254940895820210340104001d8140c00344005d03100c8000c1140c04042074019102c074504503504c200c1c058403040b0701c0841d4002080e0030003190300240c00380038185064903940c0b000f44203803101c080075506070b5804501c81040382c808216009040703c04480706810a20614113104030100492204028 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 861558291 1250 861557041 861557063
    0x1061722020a080c12010510170a05070f090e0102030609040b09010e0610060f08010e0402040207061e061806060e0f0a1a0a090f03111002070b0403061a09090307 71
    0x10380c0406020a4910550142c0752614041d0b5402c1501c1d9142103403000644109280c0118110300300c0d051061920610042e501030f007006107441d24840f01c20800507200071a5000d003014030001f20b0000c0292034014024100054034161a124241c0c0c201c0c0e0407244e8650190b40104117102141c1d60301484a60001d40101c070f440120b48599421500500c40c01481c04d40b24060302081080d040300c5501d900084501c252221002440340d9107080310420030900074800007240d0040401d0150520754041c0c200c0c14810040001d03c81540b034110500d42c801003580243e855194901403102584201c0480c0120841120510200f403c3c4000900700704105064030b03000355045510406260b41d0409410003d003c01c051f010401c094081d0409803580c0f00070030326804900315100c001070884030780c0e201c141100d8105451800046144003040f10036081c0309956070840c418031101042c0500d49000400045224840000c0c0641184500b414410752a1181500c01c114540070071002e0350000c822545100d922101f0012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 861559541 1250 861558291 861558331
    0x210080901230417160c05030606030102070b0103081e0f03090705100903060b0d060504230607090e040c0f180b0d1a04050f0d0f033c0902031b09010617 67
    0xd0759005170402c200c0c00320401104030052054060440c400e88400f501a25541c1d940c0c881410b00340e05c11003400506040c08007004001040b01c16000c1c01504032850f23090051009000e40106013604039034014640703400008140880803008003ea000200829a011003403c034410341c01900782c000500c4082c045503100c0e10282d00642e200031080042d15800310f03042002e4207150504a188105450b44214054000844002c3c101f200084045c40f5881c607a0b81c40c03140d2820100140d04203000907000300c40c0389104070030201c0c0d01e600618003280034040344040840c200c0407510150080d00d20441c00580180420426103020481e54020107001e0081c1e054114202d850320b00c0d060b40752220041420020780940022414140c0d40720000d40d101e10300f00d40d1300f8064600304142001544101400003402c40035910b6202400c05e4060129003240c003145100052400386c01d4011904003815420318001c80711404012150b140360031090307540500f001d440c00301e09022045a82642d003000180c9417200041c0044280a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 861560791 1250 861559541 861559583
    0x20607031d0406080d0c050a0f0305041a0306030706050a110d020610090e0a0210211b0f02150601111606080106180909020f040e0f240402090c0702100809012304 71
    0x2104230369119001c0011035040741001007054001303004004c1300c1c000305a001030042002c0011360b030040318014080c10100b0307d000002d036010f40c4004010f01c1842802c420401e0b205030280001110071409030068049d9140011240c0d03000d00720f581010f000c181c5004105480454001030403001545d042d6908450b00d1011181540c04001203100034200d04d003102ca0001e44020b6641200300345103131221080d2034010001c102501c03102c1000145000584c407110300911152060071180c0e411000c107040882e44070614a0144e03007414800203451030001c8451404000c92584270042030700418aa20f044000170581070b80d02080c280541c404c1c654260f4650140200395a50000304078050f00000f0410010403928010f010f80314243c54034010f1241c0101941c2003480102c40c90100a040001c5407205442d6440c2e900f04030119401910f00e9100841c14000c0c140161070b15500f080010244d503e41009074989070840d182510700c100802e0b08034001001e1110140d04040c07a03025000f9621008484807201224010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 861562041 1250 861560791 861560803
    0xc1e050304090c0e04050c16080f0a03020304020a05010c08030106140d0e0f0c010819050a020d14100b121501020c060d090605060402030c25020607031d0406080d0c05 73
    0x240440c000060001030014030307580103010482c0261501304036503001c40c2c2004200c3e80200c803c0001c0700780400c01d54640d04040014600b4941c86501024101840780c0b0300d8054942004d400d07400800d50020522084d403130240c1080c0014013007440d14500d00e510640d40c10442c0e02040c072440d000d0001c0049107011200e058003d540220780031740000c0001d03000900300c031641d43c01e04030448801ca0040c1c102e1401503501c90402140300b200100c150850b20a0344105001c000e1000402007040d9a50034080c01504100600500c1301001d8025501a024100410816003020259110200301d200400c200c680c446c004101040d8001e044055050681c021200140c1c2800d501d83c40d030307540c000800034140315160155400154654001c08007007041b40d89081c1404203d10080d0703a0400d00a00c14005440825407200c1e000394102d41400103640050f1302079000c11a150415171040700850f203054480038003c207104403400e954010445080c0541450402200d0300c82c0c051801840812601031032060511104001c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 861563291 1250 861562041 861562043
    0x60e0a1e030302041a07060531020a0914040b130b0c070f1a01060906020c06090f0307030618140a02012c0904050c030705060a08070507060605121c020d0c1e 69
    0x1c0b54078140c1c5281544009030344524030407070f9a50700d02800b14252781d1000701024a410304c40800051029a0114007002d61002d140c2d0480e40032040c1c2c680414107907000e01410048440d14079a1849600b011b142a15a00c8402800d034011b00702c5440c000b1020546035084a500041018122503503914242040320048030512000340106961880c0005002008200c0301c1c121581e5584194246855407004c80c0c659069081c40c5a201d5014005140e27036251801840c00521b00003000c5400e00d640d01e903155800e076803841d09812180b6454500726001d000f412800302081840d000054010b06500c1c4d07001070010010312090581a5418480403003035103001000841c100300d0010000b01862406103400c582e82c0720603840b054028051802c0021b441e0810100740d40880c00952205051a500c2c9641110b503a00505003d0741c0d0141c031131000013015141c000017040d40c8040c4201070401915011401910710183e820709030110b6210350a40d240560f0b2009804000030350003041300300307120300c180f03001c1103a035240c110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 861564541 1250 861563291 861563309
    0x13020c0a0f03090801200a03060512010605010305010e070519050408031b010b031204030803060123030628030201050f0d1404140d1d210307060e0a1e03030204 70
    0x4089091001d901d034520745051190340e8400d203e5480d40c030114243d0307110840d6410b0f0150302c00340c400303001900a00644503290981c50002489580c510014002201d004150581c2c1c3c2d550305424004c95270f1501a043c050810000300c2c098a081008004180380b1403030142c0791020721a55039102070244030307008860007060a07004688d03c404800700d9072850b90881414840c0390390301e00180c01c03646060100d64941166107a0f1522030802e450354840c0051544000c00141c1000400003026000b000400c010f002a03048030b20b4070607141c0c6408002c1c85211001240c06614201811801050b546840a4400252642807800540b5021504902451400703406e50070580d00381040c0c1e454000c0102285505e00c1140600108038092100740443c3e0b880314032990084000030100c5020701e500158150090b02c840c01c02600e21054040c032014241048175202292502c02c0d08000360000910029010f00b481034040c04014054117502665a1001d08104907091100c0045051511084c1070281e07040c0d6000386441c603 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 861565791 1250 861564541 861564553
    0x20030106030e0f0c060a0c061104062109200105090d080723210d06080c0a050f0303191202041202120105090703021c05100903020d170613020c 63
    0x25801a001d0036600494094500c50005041034030600004c44400c8440007408407071900010701000c403602074a0440c10359405840d580001c54400142000304014855544c40c6007800006100071204c2010100d10720000c0e07420b05050802080c40c8124442c04012115070b14540c114101d0016201d901a500009620040c40040a801d1048510040c48840e101c0d50381d03d11a0422601c80e031780c0750310103a010048107500903c81e010346070760359500c184840003c0307155060400b46401201025185071b90801103203038114540c0340c0365504081d1800341c06801c003190000c0c1d200d07810b040413950b64041c030004048610100c1150000050181d05580c8210204d03000541d176075620703005e081914082201080f4040ca4083c80b02e44860001803080a00a2640f400642135031451a020010241001c103000c181d038042040c8224001001040158801400d506000c034400c4842d0034040e091a01c1c0d02ea0880510040d0444444c100014002c030682c041000c840d12107013201d044a000000f40624a400b400c0c0e88204 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 861567041 1250 861565791 861565799
    0x131205151f0e0a0b032508030310030615031e060b0105120a0506011814032a010e13020a080f060a080706080a270b010807080318040e250605031603200301 68
    0x30048986c2110095090b91006070b5858810503a2480122001100f810046d042800002e14641040705088960b41e00092120b4a0b84c54040310010204c2001142a80e01425001001000e002d03042d5a014242006070428800445080369031800030070801e41345640346c2c00103000d60f019240301c00304003400f401400c844075210b001451041d0030400a141c401c3c81a410301b24201e0341c100004914850b013030780f02141c0e100920b500540c6c500307580b074000c80c0d400161249500304041070780c07002c1c062120701a0b6a03403183d42006039103040c000c64040c060f280145642c450920070300c0d10005021003241d1480ca802d01d2540c0d06d0030b0402c00140002031140d00c0d10792601c41c40306517000800c04c4044019000345e001100c542d9903510415543c1a05101d02e0303400b9042841812041080781090f858402405400895661104d2580c50f040c480030503079045424007801921a0322030910700c3c2d680c3c0071380300070705005280d41490034090b001c01560400501c01c043d140c0031902d5021480c0941d02c1e600c101002d120b580c80b940c40d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 861568291 1250 861567041 861567073
    0x203160e03150f190203040305090405190510060e0d050a0b04050a020a03061e0b10030b0d080409050414010b0a0e07050d1406030f0303100308131205151f0e0a0b03 72
    0x155240070741140e01c11304030b000c042e94501c210782c05140d050f200c50b45880661002d100207401d0003400103c10546038a1241c170107007441e00403144903000820103180c80c2c5003400009401c020400b00550300854448010000042000a610310032a40010a003e111740c2c451a0244c60700c225114001c1d0370040300c0c80000704001080e00140c100305140e00458000d5003c68484c0000c0740c0400181551201001d0352580c10580250b0140e9040e410280000c3c180000c0c50b00c3c0c04480764015030140d04c05607510700801c01440444400c2c0341c00c00d04040c000380018038400f000142400224010522100150000300300d413180290100d85c0042c1030004107001e42180844a80b8103a2002ca0f00e542c0a0700418404484209002c41124482c615500303200d1403850460b15162002d40012011a00c4004245d01c01f0aa00400480f0801e0740d41c49000202000340d6505080041c0382d20103001072600807402c10141038840700c3c0d03003a49000c1e034595603c1c0c9a15960780e054403202034100e00030f5268250103491152411418 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 861569541 1250 861568291 861568321
    0x1804050a0602221203020607050901020313030b0a20091c0614060f0a1a030604020c1606120212070f021903020f070f06020d0f021218130203160e0315 66
    0x10009591031041c0c2c0d100301e035100f900c13014040240141c00000000d0760079400b54015284040c41881181e04000714010200b00d09140d9400035110004150100800301980e40601c2d1100381403403001481070b0682c06100005030090407c103502c210b648009540c0c158503094081548542c2007081031040c1105030880f1803400034241c4502e0301400d0002d04081c0d0340e00f001004902200e040c3c9410134008442c4801c42c15042d0009811940d00540812030003071445401c220840300007002c1d424140d24203140040140c0421140b9201c80411401440881c8008201a804603448943e9003010104a410340c1d500f00c3c00c143c085181900880c0d80800f2800916500240d0f113002406e140301141c0703152f600c60700c8000000326144039000c01170340441c441c04502e902c03e070303c10181c03180540115112410180c401d1003480d08045000042038081042c447c1807480c1030440c6060f0b070b40105c40114514100000041008400c0c2e02a001c140300d005409503280f0340307041140d40c004200076400c0c591181010320001e51000c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 861570791 1250 861569541 861569587
    0xa0209130f0b010203190c0f0c03200a030c03020f0d120518030703110d05030c011b0f030608100e1c02010b0111010c02152205010219020c1804050a0602 67
    0x1502d001c2007101d183d4000030460309001d804505204400a07400002c8606900c0b41c40100c0301071780c40250240000e44411003d601840c4a110045800c3c40025054000301d028521100c0c4101e02a603401c0000ca400c100048042c0c0390145c030880305401610000c03581914050304014017007989c007645801c100c0d42c090301515500a040c0c0d00c0d5464414224105551043e150001815500500900154030b02e030403058403403618407540c150703800c012203600354908440c010b071244072081066440c442d440c01d6000c0258039001060341400c111030f50a01c080c8503a44c14850031b0200c60960740301c2c802c002004081240c40801120700c071010b0400e20000300300a020b0072521000303501060a50400c0b41d1740d8801800b4202021003694014010b06100d05410314204001402d00c40508c0f104a02c1c20165030140d00e120b5000a0081c400076a4400d00d10307410700d111803900662141107400c14600940310340c1d90100809907001168180075101e4445080070b1f0704059001e540186030b94400a201c0e030113214401680241e0b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 861572041 1250 861570791 861570821
    0x130305060115030506091321090e0105030a120806040207020402030a14130807030e01050903191506050904080d0e061f0909050c09040c05190e09160b030a020913 71
    0x29401d9002070301a1031301a220903a02c20203080c002260502444045c40c80039008414407248203100b404c0040c030014000e034800c800140c2d070034001d000e07003045080024010301c810f8009160340301c4c66494610130128102c0e03c800400c034115003c69070540e44d503010b4031110b44d00144110741d2800c1c1940c1d00b000a0420303000c0400030b4440c0100141180752040c440d0f0302401e0304000e10300d1611000740c1d006c40388400391020041c1404001d00203c4404d40341009140201c2072001211710304e8181505028015104460840c610302d81065428000d0382c544400c17440c3c0003070740081c406460f04450107410300a802012000c0500f417241d8420032280900060121000034414401840c25a07264100f840680762804409412a8002401107145081510f9840d501c14000e05112000da5107402c0002c2c05140d10807201c0b0740c01c14106e0707024485200c84110b46a0000e036050018094400c4c801d208409846140c41941d680b1900803001400010311901128078045000f44000f160340720082e4580018280a07814100f4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 861573291 1250 861572041 861572069
    0x1e020c0c0a06090305120901120c11060a1503081608121605070b010303180503061f12031b06061511010b010305150618030604121419030f021303050601 67
    0xb071038050448002074982141c050004041c91107803082d1103502c00441a41041007858009030411214030071050111807a80d0348030110b026480c441031800e1009494010f050b86485c05c01500402010b02c900b0842e9070010445880b0f10483c0c2c012039901f501003a000d4100e0000241400302158190001d030300c00c24403003e1003a100207c20b0012070f064080c18030000c05a417145c200500c00701c0d002e104483d1210203210b01c443d03c401d4036940828100300d0f003030318075031b91864890201104484001d4203000141c000500140040200c03620000c00c002e103003c1442400403081480311080c000743d0381090300034141602050350620021000100807090440b400c105079440d148154041c0e42c8039000b820b010b0210081000302040c004410031009903c446600b140080700d070f40c4480324a480a101c9540b04a008000100c5094241d49010f0007080401c40143c24104041100528000c8590300d10010140c491034005100030005031410024810024902d861400c8103600008000e8000f035203a040e0b802c04034003010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 861574541 1250 861573291 861573299
    0x4030f0c030f0e031f020a0908030c06040b18070b04030204050c0306010c031409031506040506091e04240504110103060f050d020307030b150901140609041e020c0c0a 73
    0x40109110320014001801c0c0d4010102080c40344000001202008090b01c501c050030340c80c5c0c05805003640c10814201a008181303807120700c0d00114020001e242c0000594507140540041940b1408020401042446200f0200d48103060380801c103419031540340111589551541c2c01c0c0c29141e00035110032807086041c2400941c080f0300103000d0b00c0c020941038680a400c1103080d0390960f03420f90490360410f04080140909200b0340d40402c07902c802c4100844a42085040010501040e5800182428007450b1000c0030720510ba2042884507405c40c0000364418600e480e10701d000d030303001342c1e0031400341039910680700c1d42d02403040280d442503020303501c00c814410703030101c100c0010741c10303540d06200f0409041c070034043c00c0000b800d0404651810320f1006040d01e07603040c1c5a0303965070108181a222107610703803105400c840351790070901c0b460b41c05081040d04040544030b03400700240103440344251150249407194003c4241403000d0201d6416112420002d41d00e40c28030701c0c082c3c0d80e9503c40480d12031048118410010b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 861575791 1250 861574541 861574547
    0x60d11210d05090f10111f0e06061309050304050a08060a0501050a05010e12010204081c0324090902010c021c0203070e2703130f06030f0b1f0509030601060804030f 72
    0xa014842c01030195903080c5001420443d01e4603181030300314140140a42e88844425040c0300da00c5855514041010301f00300202a00000c54452004c64002d660020090040940e83c110300350090940310840403a00c2d480360301d03290b0300318000c03540003541280e0000c001107203c0c540070404c02d1299451107002c0055aa030b51003040302c0d01059104150116100c0001c09c80703181016a56048098544c500261400381e441c2d860700c3c034066400c00e40340c003134090540d0005041e503414080e04050240c50901129402510300d125444112107228201181e0381d076944050469000e410200101c94005045000d06001111402007007040c04604901c2401203031404100e18410414850180611001140702c040c0e100c0c00d00001a1182c00181ca00d51005000d4102104440c0c1000e00141c0000105a00040d140c00c2020b000d5964a4803881405404c0070600240313070701d40d1103140202c00c10710f80c80012f4111a030901a42c140c4650801d4a07054054034001040803070b00254040d00031403003603444c400d1303800311a9021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 861577041 1250 861575791 861575797
    0x3030207151509020c07030c06081e0f0105011d040603061b0518040e2b0314090d0f09030204050a020a08060105070308012603070b06011101060b03060d11210d05 71
    0x703030403040885803d2190303c02c160b01412034072600004a60840382c40780c940c1c1d40d10050301e6000c2000580500308000000c0e40282680b0000e00c0c440c4419a400e08100760030b07007014071050103032a0401035020f6030307841d4003031f03075800951001d50000d0700030403c150300c90800002409041401c00441d082d000d039800c2e01c7c02d105500702c9a82c0030401801500c260108010003014201c10b011141803403113018810b440c4459281003c50002113442981034100440ac0405000c2d2410408111000045003040000d00e003401309142c1707281c1009160011540040c0e07001500d07440a07540000c3e410614020030070282c08410b40c0209200c046030b840d020003a41e200001110140700e00d401c02000a0300d054010405c2150722200707140104005424203082070440e0100d0f61640e0000c0c04295004240d041c1484204c1d40c1100c4a402013100200c000e0104500340440081c0600c005041903009252100000060004200300c0881000000744088a040722700f4144210b40550080184040e00408100303661983c024800c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 861578291 1250 861577041 861577061
    0x120c03071a0408120a18051f030e070f03111012020d02092205010e13150e0f1b18060f032b1e09121704030303020715 52
    0x249080c605110904514000210074840001414000860110018003070b99901d406010020754031406418001407000078505062844d440320000c0512140d2598059010019423014480c03c50a558000c220000e018080d000703c03c5005401d4041400d03000407894000701d03409400741490b80b8110348204514810310028100204401d01d141c20325080c026005000c0440340c0303400c014142100d1703201055400301c6114140c41c1c222415204100407402d1072241c4ca026202c5224444558075083d442049002c4041101520041100075042d01144081e0400004281c00f001514040c010031000740e03a0707034000041d902d400d04404c404c4001880c10241c1d1030900c0164944001005034803074406100f5500070718401075406006440e007008010342c208480454404180040000b03011207407100521100d01c0081c41800381d42406001c540059014035800241e8403800b41a03c001d001a140c0400c0e11039440c46d6004080c04085000828503805601509c119400707080c03000812407843c0c0d203a00072070f090912 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 861579541 1250 861578291 861578293
    0x3010e011506200304031518050c211005040c061404090906090c08070f06020a0b0403030b0a173a0503370c08130f0201050f18120c03 59
    0x1402c00205102d80ca440c1021405540a5055450f2000c411810b6a101c0c1c0c00c195100c032803004518603001d54600c50210381d14122880b83c031000a044d55000e4440301090840c3d071060a020f101e80c40000f1121214a1910b90070703408595107010385a000002030b240855041ea03a00ea07074800c0000e101d0b8058020340140c506034820700d501c1e060410140a0082525201c1951004e5071070002800044000740c91002621041d4020720700310b850441880c030780328210703006002190030410074140010741c1c500301c140e04150b2500740810000303102c5000ca0040c0d00c0980c041158203034218841101964040b0342c5181c0f000101c3ca040c107852081d080ca403c144001030040b00c948070000501c1400661084000d0b5801070003c40b031310038103541980d2140d04080f542d0800c2940400b2840e038003600c442000d00c19420400000d04004d030451400b2040465903801403031026050915150000c005c6a210780100c032030090f0550320303580c0c0303d14141201c1e0002110003c5507038082d84800c7c03004803203800300013901080c0d848000c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 861580791 1250 861579541 861579581
    0x9090606040504080d05071121070206091203030403080124080f060112020a0509090f0402031b031501060807090f080318131b090b04050f060a18120203010e01 70
    0x24107000c001c0000400680c0c0c1030805001042d00e02165000e014000c11030b41e610b89010301030b0182c0160912241c0101c210000d15a0080c440c008a200026101c0d61601220000e840310040b8010a007010310902c254115808004200410903800c040c0203070603103130340d00c1f44980d05000d401070781080c8008800500c00130a0192000400f600b02c1c803540e840c0d10070010314007007281100b1014284181e0308050300f204081038000c11120058148083c0d600d80c000003504507014103041a030003103510703841c0080c107504d8888071030000242251000c0011801e000038801c0044459031f074400c1c00a22248082d41c440000880000c0002240e00340e07098034106481b08040034504c5c000203a1404007054075440c3c1c1c0c09800031742001040c0f005850600c40c0d118018812000004500041d00b8000c200e280035800424103820140030503c2141c41d5448000c10103103040d130b0000e43d03d042041058480c1d1140b180904000703031b040000030885010544034144ca03140b0030340080c00590040070a050076a010766000c904680c4e000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 861582041 1250 861580791 861580801
    0x50312070b0403182c101e0e0408030601030515030d0e120706020102120702070608150d060905030d0f06031a0606041d0105120f0703140708010509060403030b090906 73
    0x11001c694100388070f810055503030220030260b40440c40556011124814003002c880301850410004c03080c0885408036a080f031464444000d452114207400391004040e0740415000358401041d000c40043c00031a8141c81c940c1ca01403a140030360303a01c100ea2450009003040e000c9083d841c0100004880148010003030b0451030382c82201150302c6c94012000c01d91010b003030610344402c3c000600041d4003400350b80d4000f5a0342ca40100c00710302a45d002804402c21544400400c10490750f0244040340c20012001c40d4100c60343c0700c00001030501d1501036024000d40d14203140302042280010061900a0440340d00348080d14011021004035032461102800b00c00c101c203503132004048011070f00350f8851002414103007015110b40c0411401195251120030000c0c642c0010320039032070050700c00b1101d032060b4801441a0307803d4819913925819280310041c20305071045805200901d080c05800302510103600204058502144400d0f928203003903d090b0041780c502400038041d402d003c21840c2c4a50f508800074405070f250 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 861583291 1250 861582041 861582053
    0x70b0105060a0905040e0307020f0d0b0a020f0405031623090f0702030f0c010522030516060b030d08040605011202100e130903050c0f03090a1403010608070605040f05031207 76
    0x820ba10782c0b002c112480d00c01051603600c510584404008460007151101510b105000c0680708010115100d21a255407482c0001e000e41c1c2c2880c1d000c8011a07000da25409000d803010417500503500601e6140c000c203032602d1124101c0b518400b0458401440317080c030171070801e11180c1c0c181101c20305c0141c01041c2080080c2004c3c800d0340a05030030140310720480f8a042d054101c810055001064400f0780b80c3d44075030521550104070300040104016584911500602950b0301130800d00c40d11920824083c200e403d904184003065212800700c1c84043c0665002e00074111005103c081d00320f60441d80149448004106081c2c182070540007a0f0713000e40ba1704080620780310306541281010035080d604c5403002c0c00c0e0480d0b0704100d0054009040c030a8444648801311122010708041208c0940103503513105104054031a0780390780481c82126148a410400c2010b14804207001d005a50070040c4c40b84500c441c0003402690210082c812a888410103602c07042e01c80b02015110112000d00c3c0708031700800d00400c808120 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 861584541 1250 861583291 861583297
    0x1a07020409020d020a0b07140c010c0209090a0212010e060c1602095101080c0702060d06080622020f0111030c01110c0f1912020f0307060c090b070b010506 68
    0xc00141652983e0354550300141d21046142c01540f02240045818010490561001c0100c00c6050000e001000341e20000240b080d00309050207072141819601003842154240403211038036401420b507038900c400c16880d150180c0110704540045208500028007651030020079110701194803150742000e00001c1e020403101d04009850120901d00703040400ea00026a5034007821151443c072090102540180301c0014510407040c0c01010450340f4079041c40c0542e81c81043c41c0d5010000c010607d0b21070440d8000301d00c081c0602c00310b1400c001d10f40300c0c000c981242d002811034821084960307454a401e0070203619a02900c3c02c0c9e80c000390808a10074040d2001d6004030a00c2c401412150101c84c1015101031450b0700b951304122400b0140c072070000d07014103200c0051007407d00c010729140041030207954070010034000b80c04000c030140644a10001d81d41c0307040d00c00d10550b00c2a8a210381120780311642402c20304010a12001da4001080d03100c400000e4010705101503c3c8030603041140d00d90ba0f44e00c2c040c140701c0395034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 861585791 1250 861584541 861584543
    0x8010b031f180f050109020c060708090133061115060d021003051005041104030803040218041415070c390305010b030303042f1003020703091a07020409 67
    0x40580d03011501045410088908060100010454484070300c02c00f002c482c030682042c81c6050041086240d800030004019070404490300c2c100c4980d5440003091801000428030700c200018050b01c1c0c1400c1060b0745806403a02c1c1c0c40101a11302040c0c2e9a40099505801180010403a600000b0350503038a03860f012a0598020b5002c0c000c1c81c5200e030903500058080c0741051298010907603442c14403000010b211068001b030300b000d9401b0003481080300716200d00350241748002007008500000040071510740c1540f10321080c2c034590034005141000d04e44042601c4582e90750110354828601a2004048421102030251925440d5544c0d0740600d5101c2e032458202d00c115000b4811000c420798450340003c220801450101148103810503801c6280450940307039144100d9100398002d0080c400030903422401016652500803400c240b080788600702a0303520042d108810340c040481110380b10b50b81d4050f001084a00e10950300c40040a44584821480e0b0180030b901804a01040c8500f20041c2003581c4214151 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 861587041 1250 861585791 861585841
    0xf06171315060e071202090112050a0212040b01060f17010e072a0507050603041218080a060902010e010c0b19060f0801020403120f053705091008010b03 67
    0x15201084801c1c042c0c9609520031950350414804101080b80d020010106042000c042586000e082800082400100d10b076201186036482c0c0c003040139004e07140c0c12500c0d1031201c070302c1607101e500d4107007019041e0340000d114203000b2a80903200091010f2080702c5000f0500d0390300d59414245c1c0d0030810516980c0100801040500058911401840850f4110f51640b24260504d02c0d0180c4140e02d050380c20808142d002500411044c001c0c0000174182c280100c009000b18540b91658800200b00148c2d00a082c2e0b101030740328000c4891040601100d9002910440d000380c8480c8001c3c0c43e01c60044840710701d80031014191115080104c0d900705a80401490301c90011040850800d44a030304c06440c082c0554801d85040e0360000b03003082080035a807100c0344260800e0801d070079103021035600604030b0b03c1241c6035481030039008800700d03650009104014903644070080603024900b10741ca0f40035255170306c00e000b8103104208640030300c00000c0c03040c2d541a060740d204811460841c0ca6420754803002012141450080d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 861588291 1250 861587041 861587063
    0x30103060902030a48060c03050409050c04030204110c0a2a08030409230604150e100f0807030818031207050601091103070e0d080417070f061713 64
    0x1c0f82d0380c031894105100e401c3c0500b05410b20140700c1c5d4110710b81c02210a0000400700400b42c00c040a241c0000421240c160600c420040c40c940341c01c403182e205941003240300b5071401c030612251403030701c0c030160081d13034401d0f00c08000305101001203904900030902c0c4500e0b181c0c00340812500007031a0314184182000b121681c442042a8196100b851000d2500b0062031076101280400c8007200c0c2d0f0248a0080018074001c044010780100e12110910005203094000c41c3c0b2500d1804c0d0341001c2210000080c07940094a2180307041000c1089000d03409403151604d0310030f00e0040490405c00c00f0a24030122584030301494988014060f980070086166008142d05002d061040c695000781c02c0010280c440c03007003001d0400b96060a0342036049135428a201c403040c0006108200580340c211268010341d02d81108c0c1d23036200c40d07280c0c80c02c0d041780e20850300034100c00100c1c81c00001c001034001441c881500d9642c030180840941704c0b00c049070902105a40641e0360b46448000c46d8040c404441501c0e40f0034091114004 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 861589541 1250 861588291 861588293
    0x9030a020103091727040902030a0f0314040605070c093608070506090706020a02220f061d1308162105071a0103020109060e0f1011071a030103060902030a 68
    0x580e00824060340d0085c0c0000c8000441c0c80000da14139850940883e400c214460003900817070790721113007031074000c051031900819242030502400c41d5150003903040d044159203e0b2540401400c0b60043d0008440350f0b0a10100494a11181d0280e010490802041142081c00d5040e275084800384408824410304004d8a5130390100b03072406e0040c040341e4080c00044c22241880d03a01a440e10505500410440d000721881c6001a40c0340101c2040c090320784040b05082c9807041d10300381c00030250b00c160341052500e400c0d0006008025060b04401011406240002c1a605d805928500036042c0d034004154920800c112207403a000c002440b10342c81c0c01011495444495619140340c00c0d003001000d40003040c0080b420408000d41c000e04021100350400b142e002552541e0300203004044a0701581060141e0520403110325100d402d010042080000c0801303049154150001d0807040000860034241d018000020545040c14044441c1030021400b00514580c41d5440310001058103820490380350091803c424 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 861590791 1250 861589541 861589583
    0x2030303010803120a0207170a110604031e030614210a0c03110d0341041e030f030c02040902060d06051003180204111b0d09090209030a02010309 64
    0x10701030b01da06802076070f5841d030501030080419001429000c0440c010440040042c00c2058240c2c00102004501a258203407820151030762044510010f8140c03150300100000e0607409041c55140e03240e088141151750039000700480955040340954104203112040c0c64410b41406140c5400a400000c55560500308556003d420044015800c0d00c003d03901034406d0061002c2d80c0501002c041c812a030200d00c01c1c041d03030740203060020b00c0a0310790240c0c4040002c501166000c103540c0000e40c00c03c4480001d061486107681d0141340c001d400354880c1e566070194404a40c00080c80c421b400d4039042680d076502d00115540c126411811800c3c2203070455142e9844500580320308015296019056201040703180c03e1506005119403400c2c108002c041c24071080d02c01e600e00d0604c1d10543c26070181d6001c07801c4c0c008000b001940e03201308240c1c0b040741c11005943c49031a11020950149009455640300700030760b40c3e03441031000da0040518550341034101c2c40320280190f010b40d1000404034440c0c00c1c01600c03100824441 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 861592041 1250 861590791 861590797
    0x201021608071d060d0b06030106050a1d010806070801300f0b07050a120b0a0b07050a0606051917100606020a0302070e15010507030e030105011d0a05160e010c020303 73
    0x40785140e4080c04082c401c07540c001800841e0300702c04003001c58042c54468000f400d0f131800000d0140c00c25a010000c0b69080c0c4080d04082c004e0000a0240410960f03501392a4143e18103542141d4403608200002007035941d0007007000360003200243d55540d410b90920410542d02e2440460911680400c10070300d900c4209180454142e650081c904c2070800c1c911410500300401008042d403040000800c400c3d40890b41100c41d42000c04180c00c40024540e00020100e001840c0c4c03500a031301d0840c4081101400c010f00013420b60b61440c81440140140390341e880502009088078001c4121220b000e94040c4041c00d041c2e4900b4089800c03a00454402c09096454030f4200c030303119089034005030800300b949818107404206420017843c007400707008043e00e00400e401700b003041d0480140d03040040006000081c1885000e00c5560f1b004010000c1019595600e1915007118413807202d168810115000102e8400c62480780c184510b820320861400c041e48980101d428a0803604400d041c089480192005a2410006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 861593291 1250 861592041 861592049
    0x18060203190504050a0b0c150f011202040b031203090d0519050c011821050f040b0304020105040e0a090b280e03040f0e070201110406020c0f0a05030102210705090307030f02010216 79
    0x2490303603500d2001e030f16241482d623080b45800c3c0d4810782c00184800085400c407014115142d0008840c0e90060034030024024100d62101181c0c10b115403c03140001d0703d420b500550240e01c40740c040351146c204d02d40b03094130f15001c1c00e040c00189030210482c402d80940507070010b11110450500004c2c10411140e018006504590810360745c110186c0f2010448062142c0f110305025107604105090402360480e030b00e0244160700070081020404000300b011640210280c401804058152030a42e02c0c044c1c071107200a0036a0442502d407040c0c81c10114500d03400001d842c0761810392007401e0002c0c0d10450301a2502a254010007400d00f8401080009002c81010605001074400700e0351405090514650003401c0d151640a911240d217810001045135a40001e290b046603c82500c25031210041c1c840021891711141d403103640c15500000d240c0040c42c54044c1c41011000124035508040d0719030240807622406628a510b400d03a200820900104c6d003d002900d02252052044031240d126020200c5001002540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 861594541 1250 861593291 861593309
    0x30606181003140601090b030c070501110304030221090117040c2309070f020709240603091b0b090108090f0d0c1502030f07050702040b030105090d18060203190504050a 74
    0x510554003c1d107042c00c20b8002c50240381140c01e4504040240000e8072028101c030386601000100340c003c00c4420340140e4902140000401c1e16490310b8100652140e040c86400d100700d040651802c1c0030b1b5500c0105403681254103079101001c486000c903120b8609400a8015503800303841520000c2d0300144294040c41c180807895514140c01c102da0180044e10001818038824841a6140400c41990019510044605010001c41e041c140822140001e80b00c43d00c1c9461440ca4102000c0b441c80d4058220103681c130720590302c04404d0032880034210140c42d0a07000e4180b146004100c091000d41c441c0c0030341600007188500f0386c2c15420f1031300545454070028250b004080741c1c813141c1034018041084065001040d14180c10340c510318001e00c4116034420000c00640c203110000c21240190340b145c0d400a4030405014001700000e0074011880d60f030b01c031080070705a0300060901e07200d80c00804400031721404644980c1c000394100b403400c002082e00d1030f844800c0e0004024003031100007045c0d5150551030004208041d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 861595791 1250 861594541 861594551
    0xe040f110a090f081c0f03090203070f21020a0b13170a0320031902030c060c0405040e0c060307051615020307031a01020c061308010614010f020d05030606181003 71
    0x110101002000b59018030010340001c00f10780c0c1250f2000c84035154a4031146440b8165405844058004112041009e50507100d414000b140f80e21105503d401940e400c041c60108900d40c42410320100c080040000b074100503060000c008281601c000340841400240003401415141c5100c51000c814400c5c0380e0840b540000c0e0304005150700721100c004510311811001c40c170704446c00c074a584c1d00e110360004180d0030b00802e01c4044880d0703c00e0090310b00344401081924900c0c103014055032920b03081070041c6481103181451814007200000b40c200403020019004900f141da5211042e079058111444000303400c00d140074038500241d40342c26a610308140001005880b03090419004048030a00c212558542d6002460301c11541e0f00013640401808017115420b0380d4041c0008160700f20909a40803550a42c20604040f4034407074801500202c0c040c00303a031030351111820611b08903078a200c0f141d0018045102000418000d040ca407001305000a2182d9840222a4450010940804800700c2a0380000d50b83d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 861597041 1250 861595791 861595799
    0x1e030f18120221090a08151b16060507030e24071407120509100306080f03030115080417030f0406060b03190203090a1208011805070e040f110a09 64
    0x30419140700804079100a010701d0015010710400c12410b03450f4690410408101d180140c2c1e5003000d841d0150410900341c82440300621000504c150040e1400001220344440784c940381803031901602d0210019010381e40c4c6401c0717680c0380c210040101900b904201911024000c00c0c20704200f1442403c5004800003686007048810500c20a2304050490380c01c001c101c980900510503408162440e154100c0c1e91403141603054801640c2d81d200f95103001c2c2d04141404239109490790142d002c4011518410156082d0b40c07030710700245440c3d1009004015190707808544884544e449024500e0307100d8400e40304405201c2050080c1501c0d0b130400c0b142001141d42d00d9003040100f010b907001d000024008804054114141420344070401221540440b48903607011000803988003003009100c400c1d540000c116a078940d11140c0081150b03409002c0c5841c00c0c0061241ea103600019442018441d00040c0d6441400c03040c480b04100281c00080001000350b52100203114110100100030000340041ea1a1905100c0c03070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 861598291 1250 861597041 861597053
    0xa02060105040c05040e060d0b0a06030507240818070b04150c0816061104060c0302120702030703110402071a06040606031a1c0f0b0f090d1e030f18 65
    0x10581101d4011420701582c20442c0343c20406440a03540f035002d140a140e0344a03004100c0211020001510001c404424840402c400d0ba05c480142da00038025244035035152818201031034444212902002640d249400c040c904c5820265003007071040f5540f00e6454001a00d0926110441d0018840b044001800b003140300003148032900c440b419810800c0020303e141c2c4800000380506040c41c02c022048807007400403c41c03103910541c1501c0e8a0000365440319164078000f00444058442100584200864203c100c0c21079010340d25180d9000b00200146411543c0707201d4113032441003030b040d0425000d200c0400014848000080c44441d07400c2074240e41d24200c0c0c10002564801e0f44a041410b10b813150802210302a00d9002c02003c10540d0785103265105214450307901c0d0100d08019013030303a10307a550400401201e095428061003200c220044182c80e481001c070748801c0307210703403920108401e1b04030b10180001000d8815181c071030a040005251072020741c04001e440305016001a403005a400d02802c03c0780c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 861599541 1250 861598291 861598303
    0x80a0f02061b090f040207050303071403041101030b01051207030b151806071b030c062a1b0515030f090106060801092f090f0312071b0305030a02030a02 67
    0x16600c010601c500300548000d01e040d00c1c003551030150b500001801401502c85006000e5903003c050401c65039800da506000d5141d40083d0f80c8a400100c200c06c810011f090001d0030380e80901d800009140c10040c0880054004040c4c5410203818001d0a11503401881d50480c6c4a40c0308640c251404200c10000d0000c000782da0b1000702142032168814000214440c3e001407001e07101c0c001c1a501d0035680c1d544c904004004c120f4168001d0705403c222603002c01009a402440c00c00c49a0646644000050b0f9507901850703490030340c0340c08210286200c03601c004200c110302e60300b4801c81c0112140c0ea00a8495002c1000221108034607654441c0c00818003245100700d072500d50f8016110802001040d080000041c8044818440c0315080b5032184040801c520643c070380444c4eaa4103030074038205c081c405001440440d800c074408051140300d191a200446080120303031b0415000703000702218034008150766981c01c0220000d00c0c07100650544c00b008000100700304006c09041809030000c540322000c060303000b49001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 861600791 1250 861599541 861599567
    0x605041e091b111b010804050304050621070f0e0f0409060606020f0f190201080405100c0306180b030304060507060f0207082d07080d0213140109081906180807080a 72
    0x181c404041410842c0e801e400101c04e030b103002d1800140b02c0c0c56900300715146006a810441c0e10802c00034580e02c0400c01c11003100184290300e0b524452598404070261041c01507095008049280302c6407580f004c0c42d02c00e5000028280041c400980e500041d1182d804a07405500482c000d43d010011a4841c52010000342c1c0c5072856940080101e00446484a096401c41110081c18030288201140801ca018440705030100d0441a04101494030a00c0c02000341c00c49208041e242c0e060701003080c0c4c00c0c003001e00500d140410003400440c90a0318280c0204e0b069070000b40d00fa2500c555400700c02c00b80750010300041540500038180e954030368203080f50584e4101006010005418560640b0b41c103414050002c1da15151781102009407610308000601c0c0203403080350740f414031140710118042409200541b800b00040000c1c3e0700c80003416120041c081d550000e071600c062102e01d1504084002581ca504409030a015100100388055081da4a00015030400c98045070210000300d10010860781c050b5201c0142c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 861602041 1250 861600791 861600793
    0x5010e0a140108180a030206190912140c06041506050a0e0402060a0905090702060a0f11032a040b0d1104030809100306080d02010504110105040605041e091b11 70
    0x3441c81c0c81503541d5145a100101810300c0044000900c0141c080040300f45085060800e441480c11715140081d2211000c443c0550a03000319001034500d84070910031110656800b035031040390030304a05000c2d0303018445d0022603820100204841c402c403590510000d40601c3c414543c6410700034580d941c042c1580c415410081c043d5440c021704002c0b80030400c1d4000d0308150141c0d03034955980c1400c0e50854005c013458010b00e03080302c19002444400ea9002900e64031030640c00004001c1454036000d52801c1e14400c1141028669042c0040f518000440c1d140041d078030b034030b900795174001180f810380b003070050704a07070701c80600440b0200350348d5940b41c2103000707240d4400c0309140c0c0140703428110f55600500b03014007440b0b2070050503100e0600000c80d0080d07100c04054400f40c0102d0340015000b02009011b090212411201040c950809030155401103080e2402d58890340c64030ba01b03203428440c02c0318001031070114842e604082c40f0400260a41a0b109402c0d00803001810360240891001c405020500000064201 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 861603291 1250 861602041 861602059
    0x515030a0206030412050f0f07141606081e090708010e060103020a0303051803030c030d060f030308060607050106051e1009140402161421070804030308130f0c05010e 73
    0x140d0b120401c482d401179001001c82651001c4100481d480d018100c400f1103a03890008154a08a2115000d071405610078901d0f8103850000a041580702c0b4940c61202810140c031040c20b20405003c0c00c40658007000388121790346413541c200600980070005584841e115084100240840350084c00303040b1210320302c8402002c46500d10b6022036400c6015100103400c104012410445540038881e10450240c4001c08880d00c03603a1501400e80c803503100c0f40000d8011840c000300041d946095030410000c032505515011071561b00c0b0401c2c0034055102d0141103409550350480420650740b00200800300724190071a80201c1c40c441700078403080f0940002c504060101d200d00410180095503940340030750780240c8016846e8a0200d2207042d401c0c1500700300174a00344020946c040b01040000e00c1f011400360100c0601065105040c002c400c80c401c1340c1001e0520081080284082783c041c904442d000030000c0d00004a00c1520b40300c0d100081c08961003240e012141401c01c01030f541c0c1c0800802c0c8060301c01c0382e44000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 861604541 1250 861603291 861603293
    0x17010e040c0f18110c1b0103290108061804111021020901170c03100b1204201906020d2c010c150b01080a050c030a0911030a060515030a 60
    0x1c40915a155000103648520b070b82e10a44c3d00001c1030318503400c160001c48141c01c407401c0e01c1c800b034481d003031460900191602d10005059140e890350340c004134500403100780307800080e540115901080244044d0b00301c1850600000610540c880d4103118900580c00d4141410401d404c109040c2d845103000420008850750105a02c4140b0500c0350a0184424005a07182250070058610b4240e034180d0032503004c003481c10071031200128402140b20325240b481450445884481001c1180501500100d910070124000350008510b000710049090b26851018406100d00d0006024010402c0c0b260801d540918000c00800d5010022611610442d0038401d540201c1501e10b1004c081c003d104121300d070382c00d00a4140741a4065441101144e030488030410200c8841045030010301000003015002078030130400072340c04801c24401e01c2d001b141445440d07440d60712040220000b5005656080d80c1504141240310220340d010056040c8c460722412000c1050b191201e01503106000c4a500c0e680240c0010784a04 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 861605791 1250 861604541 861604559
    0x30106121a010c051c0315060c0507181b110d0f0f180e0c070c0e010e0105092e050301180302070e0a0b0a06080a05100305060a0b0117010e040c0f 64
    0x465546820302e003c180b80f003281c3c00c01c0b80c40c5c500c0070040c41d010980340c02d01c18940f01d1790503000514803100d48100400d10741d036103c10403511071450001c098000e82064506110965051410310503d220504011900c07031400c11008140b58140c16901000c00c14041c442c151b074887c140403000c46403909003481604160392002c09044081004603400c01c00c140c0b10042c52101c03580c4a625005007101c400d02890605c2e0440d0300c00d0840c1d2062005852a410b0981c00140b44000c900c480c070b059800d90b62010306140d1805043c00100790000d401c001d8850340300010426082c00001c40700c03208452a0303850307040c4240303408149030031100030380c0349194182089201d0780c011940005034a4120b8200300318000050307035a0240300d0020003520842c070f64000890840017850f140d0080209004e400b683e2020402b6443e0b4083c5401541d80714800200350340c0244000412001a6a100c145503500c18146405400c0c00310710008014a800d030040548240c1c6041401309001c507581003a000340948103024884035041600306 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 861607041 1250 861605791 861605831
    0xb0c0a120c0c021f0f0509010c051506130c021b0621010504062c040203070806270c0f040b01050d02030f010e1b070209040c0302030a14010507020a03090909020f09070503010612 78
    0x5c0c1c1c28004005041d0481d64072444c40c600d81307140c0081c1540d500b058402242244280160b6103144681981d4401007201030f0a0310130441510f90580081c0101e040a0060181c680d10f088003140d170040e4113001d490000e041040400c100e0347c1510851584560409041004030340294000c01c01c00308001b050303001c42400121a18529a5158080ca01c4a036104c0c030000385040c90381d8006105500400052040122007001d000c01c800000c08407000000310b20910041e55007409642c00380d4450f0310b10920048506295001808060040c03500f2450104030708141d000740c2e4000c7e01e056055400c07003001008110400c010302508510311185048500d0066200b11006000e103180191190b50410041010050701c4000440215406402c1c2c808000c200d00308000d0499040d10424525403d146c00600200d01c0032070944443c903810b40f50603000718144102d65000385050a0120b81010b42088183c1041c0d49208405e44a005c950307481c030b80c0d00d6051180c01492481018080880103040900e1042e05003000620 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 861608291 1250 861607041 861607067
    0xc09060e0406051513020c1b01022508120403020f06030103080708030a230601110705030a0809030313170c09010510030504030c0227130b0c0a120c0c021f 68
    0x300d141d4413101244100c01d030381050300702c0d40300041725581107480d00650040d0044003820020340d0140701d00c552140542c100300040c0380d030042e00715000340316000c40c081d54814814240080c2107801c0c140c96031902d6181c13030700410b0000c43c4640081400c0045103050058044074400c2a07a80505551450f900c641031805503050003050110040002001910b580d071140c02404070020507014160480c43c1d080c4c400c2c800c1600e241e8001081106108070b5000300040442c1201c0000c1c004044444080e2034042032504a28643e0740e1500041003607165804e0800e00c0c00c1c014203d10008041c004010051151520318440d41e0f41e4003a48800f0010001f547c2d80240c03c280404c0785060100e002d545a190440d030480030b41e00002c2d13201450300c140d201c6181c0070012454400350307428500c0841d0748070701590361a50304003201c00510042002000547d0b81d480e0b0310280605490a0a2074503013030606004c5c140507139400c0e00341007000500e4030000b03006514012210101c1c60305602040405001c40400c0209000c5c40508 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 861609541 1250 861608291 861608303
    0x1002130521070608090c01020c010e04150e180d03090c03080906120a0b180405070312050d0203071d18010302010f2f1c080106080a1e090c09060e04 65
    0x49140c12103072040d14045084200d0205036000a9142c000180510201365032264581c0b1910400d03200e69400000c603100c110302d0585070031505200c0041080042d01200c000b0382a0681102400500389440a501c070307000d5104030609145140c0c0c1c1c0003410f45010b100309000d030b04045c2450031240100d03506010660a882d08034507407581d2040824003081c454410110001e8241d50140c0412442c5030032680240d503001c40803600115800417840020071040710980340900300740c00095082001845220545803403100c542042810302c031945403a01d003207800032205600440c0d41380554040f100e90340c012000b600300084900580300d200da45000121103505020013418014540e0040480a010310b035801800c0c00e10301c22103800d80481c11409038110340c9111800c81d0900c6a410300c0310740c00307041d000c10081e07210059a84007032581c60310500f1501518007504950150b9070300d00e50401c0e50350040d61a1104600d84800c04a4490580c1ca03103520300c1d50305980000c0403d45007080034081703d4880e098954019801c80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 861610791 1250 861609541 861609559
    0xf12030109151e031202240402031c0f0206010608040f0311120f04080d140d11090a090b010809030a02071202030c03010204030b0f15010c0201030c031d0304050310021305 75
    0x70285000d0320580c010081c1c0c4501d40c08011080e0340f010100e40c007605e100e203542c400303410801041a6510a03034418543c0000c9070710840500c0324917540c1d003500e0340b240c00181120290a00b180144001060444083e0005030000112000040d01042880e00400180c5440c01080c80c06413100784030003030005801410413101002181c0035071420001911403503214407d075552100b003005042066800f5129901041c0030381c0f40c00d403201c070b40030f0708032203080d8582590303440c2c07070100d0b000d00d4080140b00e07002400840b0030050014284036142d46103080c000c3c3c454640d00085461f007100026000c0310005040d82c0b031645c01000034000c0564041508800c60781450781c0400c8244d801e10002e810065031003a8250158404180003040c40480c1c2c2542d8010700441542a007a0344504074481c100058508a1030702054040c1c0d0800e005500c04d0380031b400800b188bc500043c0d80400c5245542082c4010811001c00d1752022509000614050001c0b03000301071099070440c40c03c0500344030311441042078400d9902c030f001d02c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 861612041 1250 861610791 861610811
    0xf100605070f0c0e0903070c0b070327091a0102010b09070e040e0705031b1f1409010c14031c090f02010c08130602030d11090a030b150d0b04050f12030109 68
    0x1000f03041c4060204151200268900528183e0381e9070043e070029103003898014000540c410006040b0742400d034041e940d045004144200003001010103405039241e1035012040011022030340c0c810340c2d00445a1200c1005e041d20042c0009083d41e9004c200244250b003440c062010090300100c600c80c0200c0203481c00701c1c1002140d045203080c60f45a61205802d8000e20810b000e84030b442d94007070f071568001140d0100e0034180d102c00202c0140519400d010203d100701c00c503079900340d52000103454405414901a001c45099075a070840310144010b40c3d01c0607030301c00301c0c80d0029912403881400300444030007002c0003402959211784005900702e0101905100700355030740d8010310901804a0344c40103602c81c16072880550f0307030100270351301e50040803c00340c81840e01d841e14019a010500b1640010341c000d00e44d00c0090f0542d2107111805030702a001c02d20b8080c0c0020030b1a1903071078100700c10503424040d044a0520345424140345040101421040c16150802140d03880780100ba581501c1c10746110010005985a01c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 861613291 1250 861612041 861612053
    0x6010509040911010206010f0602030730030b040b120304090203060d080315150c030306101229030607020601170c15031605130605130902070305030f100605070f 71
    0x100c64030140c020742401d00200c01e1094007070341d5407185002039081b0781c140c0c1c0c0e07911202808480c0360700400005030002c1140d070003c60300b09091100c00350694581da00b16041801e11065182e4040c140050110740c40705200f2041d80707468440d405c0e40c040180ca46074104019200d010b07032030b407050f40140041ca0f907010010940948480884641807540b009140b82e0b00c4c101012600c4100380c2c1c02503110f100b1000300b140a40c210f041e581c241e910801d00e4800440c10b544420003008084000d00140300d040103440d4400014404440c0101144940c607110010141c559903036a01c0f100d8403520001314081d40c032400c240000e8581c009440e904403424840b048401d1100010340c20f040525621415a0052042095814107540707500114090302c041042288103003a000780540d030b11300500a0b00d080310590040d08015150140e00200280c0c01c50020007a00141c032640070f2401ca800055040d00041d0700801002134205207000b40715084030303203c007480d0101840e004000b02507104641c00180884640c7c0000c00070006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 861614541 1250 861613291 861613297
    0x21b0405130215070506010801020f0d090f020405070f0905040b0105030c160818040b040b01081803070605100f1a092808060703060e010f03030c0302030d0204090b01090e1e060105 79
    0x40c1c0203059070414501c43c03800014035000310030143c40b00d006420000034002e42c148203e40764905812025400c102a2403600c10007850200300a031464903007200860010790b120b204a52140034607440e140c2d81c10710484c0c1c00038207201346500220302903848c2201d074500583c1c0000a490703008502030056580d80f6014040390aa0421601000b403050340301103040382c0080108280351701840c60603071342000424104401c200a49010501e070f075021a00d0034000c80da402000380042c1504441030411286403804580d03c0c1801c03208101c8010b0181c5c41050000e0060190741502074004100a043d0008145920300d1000380900c5211102e512a5204880800843d9003011140c045c0320074a2038403005840d5140d01d0913071a054100c86800012349004c401240b44140203113224103072003403000000300307403429a50241c400618124003030b415448203102e511507444d0759000401c0600008075000c10380d407034440000341c031300b8500c1c1d0000c21051044600f0400b54802d460390242c07000400c0001001c4a403039100c0181c550344 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 861615791 1250 861614541 861614543
    0x50c0f070b0f1f0b03180604230a0507120c0302060c011505031609020a03020c0708070303030c0302090306070e010339030608060c0a0201140115030b01021b040513 72
    0xc203100c42800503884610b803103407030303400300314061a960800000e8070f0000702011018444000e00c01131080404a078042c6034020700828045400d8250340c0c80e42403070581c080742d01712460300365078046140c02d100000c0d100400100d003c004214002c000e5581949070002c501030031b0329a51800700104140648804030500464002e4982c0f0303070368030003062a68040e2100c1501540c0ca400d0f0204001154100041d4a001c18651a441042039904100759000a544401c80d13250401d074081c00000f5070700206202c00c0000780040c5008101641ca180340240640c1c06034440702c411b042c814082070342203880105001c0e0b40580c070307890844519612400103074020a94070380d4100350f000c60000300340ca4550201c880d0b4204000074a2512a16082c078001c11402c1d00d181c0d002d9422079030001d10101d0304800c407610181408182500001c511004c4a0300907400c440001d9224005000c29085c0d031041b116010311030106088028409441c0750203565500305500100e1400c4075002e2075440b8001003e004002d11442e03211 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 861617041 1250 861615791 861615817
    0x3030904020a1106060303041206240e04050105090316080c07080105010605250206071b0320130605010504052b21032003040213050702061501050319050c 68
    0xd48400d4000a1010600740c1c0e01c407001e13101d140e0210358245400410395007100e40907206644a900b41d540d58401500f100d440400c600d803401d00e00310800c88200d00c1184007800840d81041960b04c2c2a06100c0e081d108060070f004180e40040200107040a00250303d00300e00303900f11902640e28840c0e00c04082c58061194000b44443d440c02d000401d44a6204005000c0000304107554280702d6844000c0000b034010711030340250700c040108500700005100da40b18400c00d000d080191110b041d607949960405100c540509001c2c4178403480c400321f40c1d10380805ca444000c51000403c2001504000019100c3c2c401c40c00381501c00d02d4012444807846647c1521480441056001c500c0c07002460b15003a0060038941d62200d11150030041e0550400e48688100031000001d8000802c00d000c4015106035681e0018000740c0c3c0240060803104605103c5004040c09103800350b004203400d00c3c00103021100d00c40c1003071030035041241c1003081c06045800da441c540794194106200180c05d8807003000c0f0403c6032003003503110840 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 861618291 1250 861617041 861617047
    0xc03040f021c0506091c090815040f0b0405150c1c110705070b070c080d080c0a0c1b09050105030a02030a020609010e090f0709050a061b0503040506070c0510050304050a110303090402 80
    0xca6020070340d0144020780649480266559000554031b40546020b00d000a40c2700300316070b50568440b030400c40d8000c3d0044c52a80902012501c510701f03160021941600c05a04c80d00720700312033740c0800c084c244d40301c2480c8058500b003462b000007400c0f41000300000c0300201074a910030003684081e018100c81e012680035040300c0310035980f0403442d1900c0e04a16819112004071200001d400a808036030000c403d0020399403041240c0d00c41610f44d113540c01c2542a48200640c03500b05800040094240e005045511070180c201a403a2900d413000b920b405030070040c0240c024010880040c1c60004003c446180c0c121181922203450b0707c012204072000d4041c07640c0c003c04200c10301c100030b480c1c01c0d641c42c000e0758641c0c2d0780010903840c1c4042c80544030451262100098030800b008007007032581c544513a00d07144582c0649162030795690001d140e0350001c807410749901c4001482003000d40b4000b80400d4006c60f07107040560451400d51281c40c1c9842a1010141404d2940400640542e4060045411000c5c1c003e0003151 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 861619541 1250 861618291 861618301
    0x30b0303040303090e0609070c08070c0f090b0a090c020d202d0a0c03061e020327011109063001090e0708030d0e030412060c080c03040f021c0506 64
    0x120210261041708109000e0030301080c09424100c1c3c049116621076240c07034020b00d03031340e070b0300d544559005180590f87c9542c070100100380800300020400007460b078164041807090110741000402d440c00d41c0145002440c08180000c042d4000c074491684c8500c0f0b09001d40d00c81b01d20741c007015414494000d0808903028040400c0f08106901d071007150301500304509151200031020141e40c0d11a10504098124444000c04000147e50b580000100c40b04414115a024000303c03043c2059820035144032420765132444100c00c00440f20005080c0d058003040c000e00569051800c04880b501c135000d05140207420025444c1c1b240c889094034820f046808002100240700002203c8091030720038095140450b0901364045010180000d00200340ca910038059842e109400b420140180914058080309001c11b200020301010413000001d1101d00401000c507000b5540e44000300404070040c144501c06c0000d0051201244900000706040d40d8141c80358280c556000d64510350310340d5a0000104a4491001002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 861620791 1250 861619541 861619547
    0x90f02091f1106010612051306110309011103061f110a080d061d180f0f01050103120809031e040b031f0605071a25030c020610140907030b0303040303 66
    0x2512100141e56070031601410071000710f490704001c0c41250001010090a84c1d140d0b03030558800e60304a4070030f42d011000700f200d075610b4000b581e09110800f07100500100400004140a0040e401c060000300301e240e2661902c04c0004490f440c580f442e803403002e82240300720903105016000c0203030450613140481d040034015180c007081541c00000c00f000e80030305141d00003504214100038000225550302c2d4540c2e05175500a444001821011800300181c03040c503034604240d00050041640345d90400d03001040540c10350170071891004100351500d041103103c80030010302c07070801f01c1600d050f2000050300b0310701d951088446010f94062034000e041c040f43c001042c000320101c0801808540c007410018031040340e40d01c0e101901c081c0034a03a000740c10b40800c003e07881030101510030b001d0f03032001c64032806a805d08511541050b240c0702d50a040c070b0100e40e42d62803280800703030104a51070323020030400ca900804904003c403001c402c42d150580d46015284210108a40500980180384007010280843e612603950b41001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 861622041 1250 861620791 861620839
    0x120c060f060420180a0e071110060905040605090c06030a1a090703090201030c05040f0909060e0610030b22030806030705061305010917030301032409030903050f16090f0209 76
    0x4006644c803203000055150a1840b003180c2101e0701e92542c3c200b66900e2040039241d43c12004c40c1d042c80c600400e41440c405940d14030800010385415240083c003840c180c50400300321200508003d05c65408146440d0042e03a50008503170b40180c03811408512107001040380110000b036040030702d600103041c0080004007981503000d114824000d036014091061615002d54583c801c80c09004d1040e41c0d412024458a042c0d90410200d0301e104003030005070607158034012420184150360f44040c011a0650400c1030111a20b070203500312101c5134081040c0b0101e50b07240240041090402000c0c131000c407001540d80e907014403204c4c001705000340c0200c4c1d40741e0305107425140808039402010302240301e201d0003041d0100c0a042d420502c40f80c0038000c602d164211b446200580178400d03208240e001010000f0300c0450000c0c02000d044600c680c491120907829854a90308003900314074250110340c0521880810038052180d40d8044a003240c1c1c00160315000b00e103048020303120340350790690814240040b0000c080c403507079a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 861623291 1250 861622041 861622057
    0xc030f0201080a0b0102190201050c010c0305010f0605030606090913050f0607090906080a0318030c030809040c0e090f190912110706050d050c0d05090d02120c060f060420 75
    0x54042c142c0d1202d41c11421103011528007801640902907011442207c40e10040456005041217070400000003c45800d5072000d481110009458200420002d201c121034440031f0711381801c0050640c0340020100e031450041400749841900780d4004140c1c00d42c114011083c1980d00842640c2c3c42141d4181550355510f001d4808100242d080200014a148240f007841d054070b01400c042c1401030f03c2a10101c03100411690b680540d04206100000001c049a0312a00114801c00ca074940301c1c0b0319101003000b1203e10008407001c0c441c548000c54915640c110101e5032003001c8041800c0325882e20780300f15800050042c2600d07070382480c1c402c00034284801080102e41c200050795a00c07100c881c643c01d0a545400062041da404a10280a510b05d11032484d041981d1000c5a81e18107810302031903448a0003138032000d8410342d50701c1d04aa04004580c50781030012607000c010154510b8540304840d42c1c015503030400240301c003101008181c0410610b584942208025001c0070500911b404003040b071000c0c20350300040e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 861624541 1250 861623291 861623297
    0xa09090f12020a020a0504020a05091c05010b01080126120f090f0a030c0612230601081018050c28020c030105070e060c0a06020a09050a05040204050a031407030c030f0201 75
    0x70a2003220384001030078407165601030808190613242c40c0030b02020390411088401808014089503103151207071038001d202d40c042c0403010315238a070440c1082400c5a1200b20f100c2d0420100f50018000180308007a420300b01c1482d4190000e82900b00307d41e090134071039145040c42d1074401c0000c03600b81c8007001d80c0c00340040290031911995089180820010f038590b0a00c402455280491820084d0324003030f0142c0020440f801801003241c040790900041c000c01102010a0485482018802a964420000b660024401c103440384100c4c20044054541d00500c011740394416140c000243c20200941c0a480340800c80c25400301215035680d1260024400b0700700180014480c10101c1c0260b4901402600d000e100309450382c009265541c403e000b0245c0c0103c1e0a40a10b2003100c010f20700040d802d10003082c10700ca2940e19607406a04003400c2001070b480d660b005c1841280140024411550b802009604503640032200000c02d444050703156013080069031000c4d0811040312000414003100c03c600b4044103100740d1b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 861625791 1250 861624541 861624563
    0x50c09150c0a020909120301090504110406140d03030b06030c03040b0a1b0309080909070503010f170316020a0b030a020715020a0c0803070201020c0f0106031115090607020a09090f 79
    0x500985024051201840c60540c484050040582080310213250441005c0c4181c3d440c0392110311003017038907030f00c00ea002e5000c0580d07074000c0200303200c1c80c4000307004640804c59080c40724510300305c01080d40522090b4a148940d9404002808060103a03001108181c0050006610707850070840c110380b00e030000c4500f554003804080c00507410200f9881252500103d502c1c003402c2c1061094002c400510010340100c4105108104a901554500004501c51030746592001d030b407581044010110007495520049194031280f080202c01c0d0408000da84508440100c515140c8001d4000a03c05881e19808032034181c100200707111800c1e0700b0f074004000d128040d2141074036062014400d0350482c451060440700003641602501c0000e410715000303641140c5036100150514034480315213410014607a60030580c41c2e66400d030820802070803607c00c90742d00b071080b960b0045050300042100740d00d201d40c0e00e00314401e031000980c030030440d0741c1c0c0d401d01c901805d169041080199660b1901c0c01c0a201c581d48207a4005040c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 861627041 1250 861625791 861625819
    0x702040e030a050301031502070506040c0303020d0c150507140c15100e070c080910030b0315010e0f06041805010b120309030c1c020d0f0309091b12090204050c09 71
    0x108070354081e0b0345039550b00d00d503a1950300c500070356625100580c3d080710740800242d00480d008100403400b4038041c8054614151940c071b00649014000895181800007405c405404170b44a280c88540d05110810003103a140da980c0c50465409c400740030307844011300010804114600340050403900143c00f50249441a031500080054440714609c10310341c001c40c3c40d00003d800c07a8828000c07000006d1051300098100004013000500841d070600c83c07d03000981e81d4482c2c0d06180340c01c004441d452008034500d030610f135040078062246031200802440e40411590301243c8203880350b520180311464941c5c9c031405401c102d4070b00320340a00071550142d0320030b110005040031014800b0013101d201010080c01011081c2c025803d02400412500007686154445060f00b0090307141c010310a4a5144108442a03409d000c624018020740c0845d000007042ca40b40078210729200141424404100d440f0341011905a00344226010192800d00c40081d005424a0700340151442036001130311079004102da031001d00e2400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 861628291 1250 861627041 861627043
    0x11041d0a0c14060403030e0a0b0313020f040203070e09041713090e0c03190f05030f0c0f070608060f061c05010503010c050c0d0302030c120f0403030516080403030f1e020702040e 78
    0x30b500d4141e0340003c04000810029000e0b2a420010301006040b0345c141c2c42c2d0f1400052504d03001140c3c1c0521818800c1116411450540806042288205d50450850804190044c40344040d04174480c0207401d100041001c0c05140e01d034052500c13004d8011141e890480701c41d0340040c03081070308c0746d8601c4504108041004200200308044944d00180080c0a01500d582c22514481140301c0107886114140d170001012031401e100500d01004480d000300e0741e461004a40038540b071b120300c841a5203500184003d014841d440400c2c603400410480c0d40502015820000031858071a80218080456005400d40c401d010030b500b0160407101d00b1402000f00e20108035040d9401e00c0f941460000607000342d5001000c03280664081c0d80c002c58101c515905141d083d41040340b941038240c8402ca4002c035800c0c100010036a05004060f4440b450000c0c0d0250850186005011260b0240c001006d05880c2d50381120107005941c01208184005112002012803d0900c200254070030340d000c5e80541c0c240302c80203042d001c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 861629541 1250 861628291 861628319
    0x1020901171e0c09060414010e011e08071215170a0309150c0506010b180a08101a030a0f050f16031401060b0a0512071b11041d0a0c 58
    0x12645840120340c80c41c011111240b904028a29007100000b8040c944003034540c1005070000d007103c0c0440040511161002416400a60104174104614040e588140840d0024542040002c50402006a440341c030019a079540c20b0b181d9041e01c0b18a010aa54501c00c0c00c0980c6504840310303a0b001c0c9020618840c07070240c44440704003001d4040790606da01004451610845201805030900d4030b543c190825566150074403000303a200c00340011001c00e640d100d4001d002c070f6400c05003a0071601145040d103400b00c0d0fa6116810324940c222032603074540079888006220000c1c180c0300b10004081c0c51082e05180703030103801241d0098059840344155064120100c1c400160699414080080c840b000381c69942c9424102105c1e481c1c00e14555290680095452007040140441403419200c40d0f403100c10b5030113078000145008081038100300318a200065010030070403044980c00c2d081418040428180e0340030a001c0d0a1940710318166644508296101000110300801c40710f01c00c034803600700f4075618078040322080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 861630791 1250 861629541 861629551
    0x308070302090d1103102a09050a0605090a080132070c0f03021c0504050f1e0409020402070203070b0a0210050408090909010e1015060206310803090102090117 70
    0x600f400c6001c80c04240c00845984030240001d00303c49000341d20050620580c0c0d105038116004007106903070b5400c80c0301c900305000e00000f00c519003445400d28103000201200601d00c030301c0c014010005900041c1d03803294420180074000c650020b1040503821681c54151852201c10060124100148040030031000003035280501620765502c0c11220464407007a08264858100320154401c20501c144061400310545101807596100d064945240074140304080842000c520710542130319031a40100c0c4464204201002c41c16940007600341d03070920106000384507444d800396152092520010342c0700c032200014040c91095a09075200a400340c1c80c04001d4950a6400800703841c03040c040000390781801c43c9803e40c010b104a00200e4003c5d610200e003800c1a03601c11000e0a55601c5070449803950316000c440c04014101840200000e1a088090b21058402800c0c100a030f080098001d4113948404c020003100c00790414075450303490404043c098000d601150140b400303e9292014030245d050101c0c0d01500c15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 861632041 1250 861630791 861630799
    0x1d071401030608060121121805090906010e0a0e0a230a0507050105071a0f0a1104050904080a0c05160503150c03040f0219060507050114090325140109030807030209 72
    0xb40c1d081c800e42d00006e00180d402c0e030400030030144e1048081940100c00701030240302c80d01c888600030420426100c08002e00e40000703025030100c000740b10100e81c00044040c11200c030500e40c560390b5100c01940001620445000744070910840c10f01e141804010b00107808202c64140c40541000701540f0410384400404901900c1a00403000c2048035500400c0181003152043c184c4502130a8682017006485900f502c00d002804e100c042000b0702a0154416413a001c03903110515810700e03143c000003c1c400e4400620040200c01e0100e424801d9602500a8000c072035407007001e84544010510321a2021031741403051501c01d2056402c941c1450794060b000c40e004048100c00e0910b1079076562921502804415001c81e000020410700059840c0141ca042c800381c2410798a51340c0e07801583c01c0003400d40d40d4400c0300c08403160342081401401c050000407201441c0d00c414034146903e10184c0764000c40a94420301030904e07a800c5140240c400c1041d070110131820b210ba2a0072500340c88030b5404a08a009411025403c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 861633291 1250 861632041 861632053
    0x11040c030b0420071101140a02010902010e031b010c06021b0a060c0c022b0203060a0f140c0a0c0606090c050a02060f07050405040e01060b07050a1703060303070b0702011d071401030608 81
    0x1c5145170041c1e045511060508408264000b208040d05900c071078a100010707551650608119a48680400021241203000f020000401e810140c4110240300d1301605000720107816008100080d0183e03910140301034282803158541c14401c43d02c5181e030010446601d494003604550b00d43c09480d81143c1a900038051506081e00341818000c403c003448100c1c040c11281d406078000607a801c005603482056109000b083e00501032141d9801e5401040d0000f04801700c540030090150a8901919a960101d03d86815151498200030000340b107141c00004002d8144022201101d800000a040424a0350b084032207690303403c0ca80d05500d0360280c03500c000181b8200401c12891a05070000b118080110000103021070741d6158400c46944103003000c0700e064008001c01c000307008680d20094508580510010310b0362070450700003905c03171280c00c078018034001e50080071800c0c0c42e2003580301d031008440e091a04103900304145111560385a9a225180104e051101164040c0d40300b4000d4508668070b001c02011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 861634541 1250 861633291 861633293
    0x20f120a08070c050132040803040204050c16032d080a02090622032607030c030e0907021b0f03070e0403210b100507080a0c11040c030b042007 63
    0x245204050400403c001c92600504007240c002c0c414608801c0c80040c0c2d440e1a54000d039402041400429182440b404440c000c020220704000e0480e039215604a80005559072584069003040c02400c040c03210141c0c0440208007050b03041966000b4035403d00644544070715580c111374a4405c03c092801c0001480c0c640400c5001d0000e401900030f8942c003c0000c0c2c244011505900807500401e060311640c0507884070104244140c08601c4500203004110210800c81c81c90842912803040d004010200040300c2500e40074144912400c8602d0700c0024403002079800d103d04029500d0300884d050010718107580416081b0781c60000340c603010300000034025000c89483c2c202035400d00c1c680148298144111071009005a4040722440403409445104c0020f01850503030a11100c000507450000034070108204807800710310000c050300c4204080d40741120f25101145825a921860070072410b41140c2400a0600041d4043d04100b20a00041d5802c00c0304042c54800c0b0002d03500e1032202020049030401c8a00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 861635791 1250 861634541 861634547
    0x221270c0f0109180b0f0108390a1205061249090905361e0111120c030a150303030e191e050f030d0606020f120a 50
    0x11028281c1410301c1c045295944c540f0b410009030503150088010b54a00ea00d142e2880c03e044800f014000a2810884a24121650254180707507001000c0e03e00b16a94907181c4d02c048000c070212111040b4a101c2a100c003a4080050100c072080d482101c0c103203080c24005041c60421040c03480c1c000305820000d01c000140d42003004a040c030003440403055a00418046036020f00c15002d0754a00c4001c2d40b4a0000020790140000c04040741d5812109119080c4418400704100d4001501295160300201c001420107044810348045d00103034007588a4003402c80076910350520b040712100018400ca0003803040c201d54203012101889680142a0500e4602c004905100500d0003d507900501c090800a4110000b804100980d0072640c012400603846242c20352002000b8004d42000140660568805612503a54446000d88039100724101940050841080c080c00704508041000d040c01925581d0728000e1218000d803515024800240c031900c550b1800d1042c0004025103502d5505040d02e041011040040f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 861637041 1250 861635791 861635809
    0xe09090d0905270414070602030a02030403110409151e020c1203090f1515010806030d0305090c0a08031306021203060d150e06150103020708090f01030221270c 70
    0xc0c0500f0152918101114412140700c94003c501841142032800740030300b0030b10b241105075000365045401c1071110910039030700041550b0550f9401070700302c413a020004001c00c0061007000405450715416030311100d40708031240d03c1128031801e0302210f00c11b01c034105600801030f4030504c070064299034003000600304440c91007006550412055802c0d0b5020301c24564845140a041e03400003c00e107503440041c01040c00f012120b0036211070081c20a00b01d1850580f00083c1c890303180c0410b5100303054641c000a20041c0f41442070241c1c8000090440d000551181170855880d0880040c2d154050700088000c21240c0c0002203200c030003d00c4501a42c6183e47d90014807481600ea85012180f10b0300b10900c11825000d903000d031868450000006003a145804100d401c2d61201d42280035051510402c2028045101c031001c0320342c00e9100f030700c03482e48995411004078020b100d0075224560f141580300d0044007000c801c0e44424050034400f0301b14082400c03800a00c0b90042e034a1454400030b0307400b1848240041c02c0030701c08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 861638291 1250 861637041 861637069
    0xc0e0a0e040f020a050a15081806131b2d030b180307120201021909050105041a130605070506060411030402090702010905060108240103080307050c0a080a0e09090d0905 74
    0x1813002c240d0b52a0301007059403450750000301c1d86029a002911240f80e01c0012194400301c5848038038003500d000303001180c4880d0b0141120388483d2904d0404814840d0111601000303081204100040300d9403814548224044091170261800d10746d80301420b50a80600220f068a070803090412940c4c86117520041c200881aa000d4014001449030801241800c402c0c10781d0061181c0004d642c07001000070303800d4001d1011501109110f8110410f00099900c44165003c2d80e0360b076905c4980b00c0da1300380305100250050921003003481041c91800b0a190341d0003809130016a11910807208640c8905040209803450700c3c0e580c2704507600900c0050003519003202240c0c0c109030355000005103a001c2c1d449281c1021004d800c04907142d405a03a620740d2040d164407090003401c42c035429510300d80d415079a42d940799102c0500201c1c2084004501140041c4081c4903045801d41d12001655584010441c0135281102c2110980e1084001c0b10000340714140215041c2d1100081c0c2d950041411700781810800a41701500c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 861639541 1250 861638291 861638299
    0xf0306050301050c04031202010504052a1201021e0307020d05071b09050106090e06030613030512070801060908010b180a0605030708060603060601170c0913050a0c0e0a0e040f02 78
    0x455440070b01c00c06000700080c1018545c0d46085042c0959981404065030045a15190401001c0b43d40131602d80340400880350710248400010b51058010119014201d83c018150405070320391010560041c0000c0c00b480081000010041031800304602080f83d1500c09600010b401d000030038400c0b4000c1c01c2c05441034001d5504504e040b1040703c400c010784e411641001c2c0d91940140881c0d5049040c84006003640c0ca183d02e51440d242c4046610ba1402030800c0341c100100f40f0004003014065801d903a80c414190148141ca46001c031310050403000c01384102030202e1005c11010400d19411b004100f101c100240c40220b0384d001030f042d1581d6004c40107000e02c41556540d0f601156a41c0c081c4039041c0107100c820010301c55804c000c2e08060070084c0180586040c02071080a41c0d10204044141503801b00e0504095a100d002c0c0c00d01156405100c444616165072800e807c02140c00b4641d8000200d9052541c3c030740d55004c07455000d10011031450301074030141a00b80380000d000900050360740511244050 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 861640791 1250 861639541 861639551
    0x71a040f0201120e010219080c090d021c05101407050406020627031b160509220204021b2e090501060b040b1b070308041e1e0e090f0c010f03 62
    0xf500d002c5c2240c01c1120000601d01240c10f102c07510b0769000c0c2805811801101e941803600e800000003415a20b04480001c0c046c0110810003c0c1000302c01e504841000c3d00071042d12001848044c0c4280103008514aa641203d196404034800342e01c138409440555600742c00070407503522502a490100c07070300249072898180f019420588100c1d0140050a04048401d5a0034415801440b02e179080c0041501200400150554100015514688100d8000400485d2440104114000c00c0002c0103522400f94001d400040d92042c421140b00e20322a0004100c400d030b80d547d60f210030010b514102801d000c1d601c0e0101c0d0000013650b9240d00c0d0f0183c00d0036803060380002205660b80e04008403c0e001035004810840e004030b1805028899000403130101003000780a8008030f4115590303400140101c1c0114000b0040e880300400b10803502c4000700c0050844092401c960194503040c51490420a001d484141400e09000c03c214443c0010301244001d00c0502501060160b0301c0112003100c0ca81850070f082640356 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 861642041 1250 861640791 861640811
    0x90608060108060f061306030e01020a05090d030c06090b0604050619061d030d080105010f1b0303181403031512280c08010207021804170904020c0111071a040f020112 73
    0x3c00001d00d02420440440c1c000f0510341f810180c120f401141c4d020031035900404c0301a42c0594440200c461168044546000307200c003504044030050702c0e941c0020005880c0000c65018000402c9a5a10400c0700315014005541d0300001d102d840c640030307108818468020401800700f640126074900c500720034048000040b002c2600000d1529140d0034008020800c4207006120959001d200e280c8001440d0400341c1460181d9203c55815500920740501090f40d2420346905102d42d01880b94401504452100002004500c50507140d9009640d400070200e030100c1c07225400c0c100b100f401850100ca08000e0400e208051580d0900440e25001d0050b01c9400901c2e141c000a402c010404045e003450400181c0740c05c1c0510500c15190710b880d402500003e000007c000004100003096100c500042140d5610b1b0420000410060f004980b40989154240002c0b140300988071400344c4a5180284000f190b08013440d440e00025040590780684801c95030000103000d540101644c54901c000300320f00043d603401c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 861643291 1250 861642041 861642049
    0xc170c010f0504050c121c20060702011a090a0b0103020c0316030215091b01050c15040b1e071404030b04030e0a080606060a110705040c110d090608060108060f 70
    0x401040001e21560b03034400d00040c04002c0064080c02d0030300392018060010300c202201c1d6615031003010011072000800c100e503241481a001c1103e081c0302a00100d00d032141600d96140c0f030320404c503500d400541ca0b0034a005249a9083e0198808050251a4007411703112007500c0e10180c42d002540300c0c117042c0c00f000450288481007005002d20400c81950715903261162600900345600750026031000014401401080100801d030030440c4040120705a4001d5143e00050f00d090180c003450802c24000d5410340744404508086051160703104503111078803075503107141e9480702c09141d500d075046540d400030000301c202e805071404c01e40a554200c0074074100360340da94407880003460840e01200011403070000001c40341014942107010b0109840588071500e04100410b206000794040041048040000070494042c28030a04000d444080d0080c020400d02c144040c00000e800070540c8003500c0b49042c1b50018520036104242074461a079a00b80341911140011a81244085c00d01c0e82c0c880c10300d008050141c0e031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 861644541 1250 861643291 861643301
    0x102041d0405071e0e04030e06031005011101060e010302011803060c030b01080a050405061b0f030705030118020307121e0603050c03011518020a1215050f01030902010c170c01 77
    0x920650324400300d160070b01c1e10b40d041014603030007107298801d0b0f10099030702100c0e00e0001d442a503808590b490403660b1141403c031980c0b00201026a0400300c000300f8080802c400344002c6041e80c800ba00d5001540708112050b508075216803151484e05841e060061006603c01d51007509000313499141107841a4803078480034129600012242c0120350b071044da50100c0d50f0008065640b21980210401051805844007030300c5d142c00414007034800503c000b46003a402400010f50b0000350841080c01c0e12890010406442d66000380151181000c06005948a04c101c0c0c2c001c8900c1400c00303654404090740e04c040030303c02030710b080c0b01610b214101164081020700d12901c91900294015802410005030741d41c03e240c2100c904d405c140300b00290502e01400104880340200d491260034000040e5101780c00a8126416240b1854034240326040542c0c051001c40b2144078030060300c0003260038910017421040194111a45000001c0c0403401c150400340100b1a0305203001424034158001c02e18204181d007240b402c4607 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 861645791 1250 861644541 861644579
    0x6080910051f0b031006050313080a02030f040f08121c0203060d1202010b0108181b0a030209040302030301051008090c010e0609060a0c0b0603031e030603120a0201140a06060509010809010204 84
    0x780380803017000011038200348031500800550824904e5403c0c1700416154103070500038058403c140008400c080c1c80d1080044401440c66211419240c2d03884d400107081d5080d452203154158854690313010820040c80c011501c801000b5200c00d443d20140310b4031b4070003039003005086079071102c20500c0c1e520121b1021243d0350b04c030398020303400041d81e0300c2010009441c41502070042140c3d160406039050b1910f40c0010403202c0291704000d02ca40c2c0c4604440041d03d01c840315040250410b804078240020590004061810b8803007c030340c500ca040a1100c000c682007401150401640d6000c00f5204071207502a144da03200e0644042c015034900f2042c0e0002c0382640d40f06104403c00280500c0e5001d040c0101c542c03425401c0701e021000f8500d40f024000c0d205251550380318848480b4040080402c2e456503042021b1559040500380c040e494409440c0060300078070365840742e2519803442e0b000081c19802c00c2c1c030601080c0c658036210603090468400046460510080c0180f05c0c96508100109980c6005c20019180c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 861647041 1250 861645791 861645809
    0x3041e14090f13021c08190e06040603110705010c0507140115050d030c0b0903090109080c0907050d02090406030f020f01080c03071d0303071101022505130920010906080910051f 78
    0x140301504681f8070541214074298080080d55601c3c1c0440e541d07080d0481d0304580007071901140c0400c0c6034445882d14840d10310010055840c10301140b8030b254020f405018100c0c004c422010380c001c0991091341c203841441e007018441c3c0e41c2100701405507103801d030014461103009250203000350006946000c0214402d4650f82011740c404912840d60390781c05003880020308016030103480000e8450300405d41d50403000e0901e0701800004200380c3c9480c13115a0540310b104500400c107200d941d50300c0c01c0a084002d500401640035140139019465035501868a6902070024000a64a1661104411641c48042c0c0141034a1a050f604281e0500c0d903040010301895402001e0704070945851100180c50629104003804603000b080000081e1842410301c0032301140c0d002c0e500c41a10030420718500e170081c004540c0080051024100845a400740d0700341001348400c0c04e032500e00d24545c407128191204d9078100e0748400243d0048116000445854001a0300407815400409202040c0e41c040c428201203034022401c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 861648291 1250 861647041 861647047
    0x71116030c081608030901030c020a0f030801050a0504020306010206010501110120040503010615090b1305042a03020903100b0a0b03040b100509010b0a030e03041e14090f13021c08 79
    0x144050030322504051101c80b0f0301e0380da0300f549411000742c1c5030702a4000c0c05050541d10040001014028030105070f40c141d101005411a411529016041103800c2c060a806020080b1011425040a2086a0058030141c000f404140c0c130f81001101c203803232140c0d0009071035500d44404515181340c0a1010b84212940301c0c006490ba41406d090500b1510107503c2480200c1e1800300b002025600321041c0d40607160301c110b5003940c0c1d41c0c1c1844242402038403030b0b00540d0490f2a2a10040008100c0c603c0780102c10344801170124001c00114044059005800d8000c0d8180c0018019116000c0f02e035100780c00120f00a0010884259a29001c0d101600102c401346c1d1008038400422825803502100000500b1049038551425410421841d07100d00400c0c1e0b50805055460504004404003001940c4c001c2c00803240243c140c00481381d1014003111648911480021210030b10035080c6007a20645125019175030410b034aa030390702d6401108956404c0001d0f40c2050001113006260003102150000241c00f44203419a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 861649541 1250 861648291 861648299
    0x221b030501030605060f100f02150a0213171203090a06050f0f011a03010b0721090302122b050c010f0e3d450506071116030c 55
    0x8140c441c002c090718458040c21442d04501c3c0c0d1a429013013150035462030200b854040c052301c140c1c42c00c0521120051850207200400c9030b5011941c00601400f00240c4401e40900e5a48500542c4403441000d225201c1c1c0001c42a500032441d014040c1d5405001d07c0b084500510054448401f242d40a40b00745107404904020803a03500c03100c40d0440d00421a1448983c4030f038080c02415041e60106004c2d08842130400164101480483c0f0f200c80c038a28181548090f00c05000c4002806403400e0b031100320f01518500b01e03901007025000c600700d910491070081900880a1021808010784094601c440500c4030910041030219024410300404014040e400a02d160810041c2441d0003c9003081d0303034444e090341404001c3c40880c181305c0030115a425822100b01007411403041c0241000c00800c2c00d09440d00c005130f042000620030406044100c520b201c1d04d47d04091004009456a00c08019000b54480000311300340500c51562200016680c10a03103030f140c001c07040703440b2031600745078030a4600d0000010280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 861650791 1250 861649541 861649553
    0x6080106110309010503060618031b1005090604060e0105120106030515030a02180714070f1406131707060e0f0d030c0c0f03050903030403051f020702221b03050103 72
    0x840c0c07026040c0002c40c282650070340000d05601c002013400e4010740020440f41785151024160070060b0300001e080c3c496580b0105a108003d040c2411101d205402da0718070f03840460b000e00b0481d440001c01a21036407505041401c1900c003c48105d40ca00c4c1041810030000011000b403014640c040c0441d5a000300d003604103454050041d0b42c0409003d4402d030480c0034041c005039641c00c2022404410100000501c1c2e9864105882d0344050100c0c0a50690380080c0210401210b0b5017803210581c0b18003040c0304030f4140310030000e6035407500b00c6078000092589041c03140071420000001c042110a0200c040c603008650346c4000036203441d148245c0066210005004400400344640c40e12000146801c00207105003640c0109544007440003e44908410340d400e6003810700c00c034225850034034054226a52035569103031aa55880054105034940d000c6c0c0c8050720f00120942c000c4855041c0c00500700145000d5050144030084808201c2c2c0c1e8403d6601c44400455819036910107469451584001901c2d61440c2010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 861652041 1250 861650791 861650807
    0x9100b031207020a150507230a060e281221151a0d0606210902040f020f0a0f0e09070e0a080706030f05010504020301030f3c020319170d0603060606080106 68
    0x85040308c8403c80d603200d14000300098941140d03411401c0820480101006941410044a00d0014a20180c2e4441c210341c1917410040c034045104803840309544013555811a5070072141c00080054080f003015410300c54001c2d070840d03c4112400c03c8080c80c4039503100d040400c1444001d040e6043d03168082022202800316209030700003012141480e00f00748085440310303410106668030652255541d8400003066468030b03801020f0011004c80115078903900d44103082c51a8201c0ba040b9000586084000e51483c0c0c402ca00081311498040d0051270641c03a20303141642c030182409903141d0000c0110700c3c0020a810104034400c01003206803400910003050780011015648160012405139004100410006484c0071444081e96045054030000185106007880c505140001801d400c0518411504801c5a020172180c5200d10803021a0406805a8110036120b041c03418041c1401842d20710001c0c038210181c0060403034076419003002406036120398601044803000d40001c0001105003005026150b04040e00f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861653291 1250 861652041 861652073
    0x2010809010506060306060a05192706020d08070314011712090a030201030203061c0b0a050a0506010c0201110c0a180608071202010f0e0d03030509100b031207020a150507 75
    0x1d002c0c1e880c245012411600c00502414041c240000c1ca034031010f4444e9058941030f0123141d840c404074195882c0002c03c20410020a20f2007103841942a01c2c0c24a400030201c81220a41e801406284a15100c140ca400d1f9000304040d06042c0c0301c1007200c403102d42491481e80030388071001c2c06144032070141e00c2c010301d41200004140b00005007003051441d580e81c1c40617030741d0440794246800740e6a655000c000c100d040500c0f00200001403290b0700d0760b030b00f0000d02e010060b204ea20702c0396042100d9501c2415010a541c801d880031404503030990f61000155100742002050340d1421800c5031400f9650b5000300340c1034501580483c00c0081c3d0b141d025150094140a00002090071200401c0c9036814141196020305e0700c040003e05000100b0f0b8201c80e068007880d002c1d40724101c028000380c0441c845050103005054100c2e00458203003e08443c481504109100d884030180000d8001d01c07010f601d5441408181d40001000c0c0e078070116100c40022a0076821408605568030380c0d580c42e88500d05460320365030708810009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 861654541 1250 861653291 861653293
    0x50709080f10050a0b03060c0901020607140d09081c0504110f0a1e09061710022109010b0904030c030e060403170d09020a0902041403030c03040e09030405100c02010809 74
    0x4024105100042c0540302e80401c00030000f000e440c1c00c584103005007803150700540c050181078200300e848501174003e401130210a80075600b07140d582c002c1c22a5400c01e5580003162840050203003a512000030352112904501c00e410003031621858103106640c50040e0394907540c00350748030020082006101400500c503124261503a49441d9101c500140e200601da003c0e906070340d000491000340d40300c04608d556000301b90740c000030800c4545a2003821190425988100346a00c104003085103440741c1807084551641901188036082c0c0149090280007407405890700041d90349400c0c1c0100705135181034085008600c40d80b40c0e507481c101d9514024000b801030340a51780c0326840922040001c110112482042e41e000211400d681e02440c028a40082103400006500b02920f61404154251035038010002c0d238405c42503900e10500400c003015500e209402410031150801e000c02c11500c0342c0d40e01c1701600104d01d002513030300301511b910108021130a4205004001403042c002d60040d0350700040c80e6900820544 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 861655791 1250 861654541 861654553
    0x2c03040308031f0b0d1409071811070b011418070503010e070c17030a0b1509010c080c1b15030601020a12120e0a021009290702031005070908 62
    0x80c8804400340402480a0003005814190081d048160010318014060948101c3c1c0c856000115803170090a40740603100444488201061401c94002110720444070380728101c011240402c442140980032012401c1812030091082d140040e03d62124035002c2e003040b40320341824480d50b10030014a00c3d00b00e01c01624500e1030070144010541c0c031208403410340f50001c490304029100c0a800311000c502091340035101b0020b000c454800840200001c41c0611210181402a85481c2d410015190310510a22050180400c800748165000300c0014440f85c0c0100e100034280380724030820346d04144128912601840310f480002d80b42e803805030401c1c85298002c60106040d031030042c0010750384d0841c004004e80f4100d0001e4169041c90703c04d110340340310700341900c1061100711103041c12a41c1e00d10150000300d208061807404104120300c120004000c0b07844440703030101d40c00407020103d540014000d6840c0c03044a0100040d00c0540c03400c2012140d00e40001000084501d09100001d0200043e600068040e403c10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 861657041 1250 861655791 861655793
    0x24110c010b090708131a04150e0c0109090f060b0a030e0d08090d0c11121606021501060e030c1008040303240e2505070501110a0f030b0109092c030403 66
    0x4074044d940c2c040d111210310b410403005420900489005001c00505d040035500c1003104100c00e00e07558030085014944144514840d0424003621540d07003062960002d8002c000c10000c401e00c68004001d00004227900040300c503140c2450202e603a0099a034200801c4e100c40e2041c001c0c16003000302c891803421a21f040c1030b681c00c02200141e110b02c046562107080005c40031441043c400c4a4031481c015020042400380302c10b08a400142d15410801c604144041000e20f0000d040c900103e404207000307201c0a00e2200c0b9a09100b015246040100c911075018468a49240e403e901c80d266016812040b41d200c828040c0b503c0c0c5401410b413104107062040106420711002082a2100401001d076491703a0707003480c041d40d036a80301c140d01ca0080c0d000750340183c00c0701c29103986169045401082c040380210000c0c0311030a8001845800c03445080700400000da0718081000109100f40c0c4006001d4405140202c162b5580740f6010703060360f1405070b41d41001454081c0381c0c0c024029410503240800582005141400d02d1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 861658291 1250 861657041 861657047
    0x1216020a0b07050c0a0f09091506091a060309030405011103120423120904110d050a0c0f030c360801061d010e0708101802030a0506011b24110c010b0907 67
    0x5a840398003c0948c40c0c82c0303e00100410609185003039810b8100c200584c80d9075500d544041d050a00d20002154840f002040701803c2c81412031340716219640c02946894580b80046400ba41c40440b110b40d503000c02e01c100340c0071a240600442c001e07401281c0718103090000060121001010340f240850303a0b032014601402c800102800c0e81d50b42c1a080300c0029840c002c5402d001d81912032202c1d926485454a002c000d1041d80a47c8812403141181d0f50b901440714102c4004c3d01141d040c285e00d0b0010442507440d90031b10102d8501c44210070000c001500c214052491034038203520311603411013005a5103c1800b400f514940390246926410110003084803075142c06960301404034003910340c40804c004d800000e000003a16a407100010402c403224000c18010803e00500250015104080214200f5000c10f000f0b600c106000700f1b81d0900405010410145a81c4803600340221010700280314140c20725203030060045104071144100c01009060740c40c2c091070096421600e924030414030030301260082c004450b83c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 861659541 1250 861658291 861658319
    0x1080f07060503090f15011508041703060f040507030c230d0b150408010203010f24030902010909151d010609030602070c12150f0e1216020a0b07050c0a 67
    0x815402c10642d0390321508207107410001e03c40240e800520803111349944446950020f5812035001c43e011142c840c0c0c101404862384a03041d0f60140c11801d0702604500c0710981d040003107400100042c0315110702042c54010400380c4504039600f001081d940c0782c0c6926641d070403001840320941a0201c0309007542e542c1c0e0718000c045c040c100341d0601090350741d80316580ca034450724520486a641d00d6400c640361581e80308114040c0d8000d020b040d013007000d1a00d000840044400020000e0003c030074400c03881c00d008900440080c410240140d04101800200042840c0d66214000c103441d12a000038903428146801c0c2e2126800d01c1c9140b0142c49414001080f02d1035220058100b0790307a0100c40581c0e1400307170342450141181d00d500500b020000800030070041101103481e805041001000c140505000456000102c0b0381100f03500b9800d030800910b40c4440c24940c00104084100e2091072a0581802e801003044950581c1107412003040c00254a01400304c201b0111044120444004440600300304d08410300c0746c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 861660791 1250 861659541 861659549
    0x50c030633030a0203070f1a1e1602101101050c031611120d060627091512030c020315060a03030f110d05090f060322030c05010e01021201080f07 64
    0x44411084010180c2d0700f442082c00440d0001c0403100c81507200c40741c0d0088010944101070740c80002d0480c4111030354299094500300f480395104040b541c11078140305005130303019506c41d44a41d1440044600160703a080c0003058104040e13a11441400fa00c6030300c05003100c90184ca804040ea0b024401c120026800e240d0b103600841d4189445100903200711556131422881610b2042a10000308914000d29000c2d0f000b0012110b1540c0e40250029410500b0342d40104c0c43c8404e4003690b081c83c203040c4008000c0e80c012640c0000341c50070460700c3c990348403078607030460084a0044000400c0b029888081d80780421a80469942208100c1381c5400c051001a201c14194800202440a840070041130240600043c0c2021880c0c001902e0043c07540480c001c01171350000da40148540c1c0a241c0f405e80a0400601703a0f13205050742c540210f0000030000949000900c1c014080301045074200040c40010400e0103441c0c10562400000740e2508480441c02e4071780c00c0c0c160809001903001043c16040d544000034038108071 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 861662041 1250 861660791 861660871
    0x2130306051006030b0f0d020d08040617010b13050f06071709120f030d1104030b040b0a150b070f05120d05010311040b06030a0c140f0301030b07031515020118050c0306 74
    0xc1f079500d201294003c2d402840161802d400400c1c00240207400c2841c040a8007405000700045a0b200d00802c43c2c54000d000e503100140b01601d4080c040c505002080d450007400040c4001c0c00c1032216035800111041801c0f915406680115245513503007402c0c2e14070011007001c00094810b1600524030f86580740a16500ca00d5296155000d6980c0b9a55071403c5502854001d24209020710749802c2c40364402c1d1083e11007040080c42d040c0c42d502000080801442500d5409561070b10340030540e00c1ea18442e15a4007000d0702e00c0d00541c0142004511544001c040b280c10900c804103ea40c0341d410410700b90b0081c003078001d0081e4101030208030a607541030220b95220000a80009511041c040e04644403000d51180346881000014014090404000a18100d9104124002850356001000c4040e60403d42c203032400e10400704414000d11045005440c1000c45a10000804a803481c101c5180014070b0f0030103840d01d401c40f1854840e14103051000750b0b400324899042c0306605040141a0801c407105103c0c1c0818 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 861663291 1250 861662041 861662059
    0x2040308071e060603140609030408121b06090708010c0305040b041e020603090a150e070501050c120310030203060a09030e0609011e050c06010f030c0b0d02130306051006030b0f 78
    0x24503000000d264144a400c4001007202c2c41c2c8900d4030006148806d2001c5036248280c1000070020781c0000126020313120442d000c0d142c41c43c13003400000d0b441c0e0005402119003d408074902c4041110400ca464403c40c4101c0041c0540361810131441e084a248089a004043c20300301000041a00c040703500760400d0b032007400d0740e12200704018081500c80342d070345000354030400c00014400458000584001072074054a440e9881c1c818085016084480c2c0d51a80d00c2603402c814000c02c944c4d80550090610045840300340c84220703d08003404c051075402180d00f01910002e9020600030b5040c1088003560140107a24100143d21564501801160108001d0b92241c400001d0b070300c081d40d11035030000000c1e950080b42c1c4001c007104540b003d0405d80040c507180000d88600c100001d0301c0178281c9a02400c50781c2041038070300c0340307402d008440100c1d601090008403056020007509a5042d0526503810066028034000180b45c18500d4007001110001d030b004000b0142011561714099494401c142c600310001c4030f095007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 861664541 1250 861663291 861663323
    0x30f031a0d061e0c03060807120b041a0c2a060c0d0b030a0f02030105220803040f1a0a0501060201090512090f150d0b1e0f01110106091e0204030807 65
    0x40d010b128100d403e980c0c4120350750649203d09400c810451081518148559074a80e41100d5039030045104411307031404020303500c81c080b8140110b0f4503003182c0a0503102c40031074403808144056082c10384160b41c1c000c7c0300003030341d250440c05c506030f60408c4550b41110f070000c004d021014540c1c0d40741c0070302030482e8264006a4080542855800801340d140702034161048180f450405032003001c24406e05a00079403d0400040d0303600b12044859030152440c91450070708461070385a0200755000107000300e4001c100516102e000c44e9680a4a182e501c51b00746001410340ba0000c6c10b4800d0741c0c0103038810300541e070500650400040d40030400d0742c4020400700215803152507503400a0740400190f0b50b1150044020b040510003015148024244e41c0b030f00300024003103407020400303000045103003692056030844503613099801c91820b8580f031030b14140149045100d04062098250031a9529400303110300540d40c0d000f00108204c6550903c01294034110218109443c640780c4040912982100611110042c1082e030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 861665791 1250 861664541 861664553
    0x30d051216110f0102040f0806010e0f0901150e04110a1802070c09060b0703020d080c030a090314160506010b04032301151d0a06080309060901120c030603030f031a0d 73
    0x800705003010b4086900711a0800c030000e0003948039000d500401800c4c6000802c04500c0020364604072590006112800e50320015804901c000141c4030044a5481d50007172811182d0b0351540c4000b0304035082000d4a641428176100017404180e2aa442c02600120010403407a0710001101c020801c8616003da581d00f594540600d1808240c1c0246003168900311010404032410707405000414465000c603a2444c2000b81d0584028004035a80e5801000400000e000d00d10f240e0018008a4031a081c10030528007554031311801900f0050f210541c2002c902850710511030208011030040c400388208501d424155201c00c0b4440c1c15440000604100c0b21406071801d1109502591700702d1031400d12040c0541e25455400c0c2d08000301450500f2441f00318000c5042164144181421600410015481d082c010b07000d20501d50000f1510342d05012000401031055480c900030420740d01403a6500142c81810344c940a002c514000c2400d804162030420300030f410111600410340100310441c0d03009021000d078a084 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 861667041 1250 861665791 861665807
    0xa0f05041a03060106020609070801050f0403030b060c15102411070f0e04110f010207050f060d051305070b0a0c0303110d1a0307060e03060a1a06041202030d051216 72
    0x201e60180704a100000b1082d44c0440c80500a680e80310546a12641d02c114141c280c440589040300e141003103501160000b80a0361140700b0410014003500d0401d1400d014060902010100720b04c1c00c80c2c40300080006106030403810310301820800c2050b82031841200b024071840c4125242c40c0f07050108600c0301c00420f006c200701340700c02040c241d00011a41c0303840d0050000c07030400540301116030840200c2c01c2d040e1407611101c0b040f1001c42c180d0050182d18030b403400304010b000400419940240741045600607000c218000c83d8840c06240c5951034080b000e134034155103400841c0c0d01c80025403c4c24091806003561000554034101d41601e00895001c3e40310302005450310a104800d04070b03030301d080d00c2c0b20028001d00020061100040702507070f1155968032002d40725912804840c50380f64118000140a800440c0c3c065100c00c4407450f142500460401e020840c0c42d807040d00804100407465007400308500d000c0000d01a03110051900c142040e18202c00b40700142030203022245507404524652100754403850070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 861668291 1250 861667041 861667091
    0x170304050d050a0519030f090518043906090302061606060909050a020f0a08030409021e040f0f0b120a0b010c3f0f08150607030512060a0f0504 63
    0x183d501858680705c000d055502402821070108aa5091102285005100b25403c40380081c0401d0b522009000460720901c1000740200e8010b514801c81c01807500e00103200300381101080c0c9a00c940009240310545c1e0342e04d0964880300c10000410382c14401a1200001c2e200718406060484144a5140c60014060700c0503800080c142440c01000c40148000020382001c010b00944070025030001b1017041c454048014000ea010b9684100410444013120f42d00070322500505100445511103181d92211040c2c2c0b0580c451002d103070081105100d03a0800040660051010fa9031140c031300f1004185d0050200c400403c40c0a40607550019101c0303036400780c084440703400d6006111902d0084a5002403104071201d030301100c05950f0002d01554041042202e0000c288450388031521000e804c01001c580028008005030309200c01107201d010281c44440c0a0b0043c9072280d11026280c08101c0b00c48550140002c0a181c07143c1091441000b000321070000000540c0d1080e10040b0304901c900c040a15400d2322891 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 861669541 1250 861668291 861668293
    0x501051b1204090c110327060c01051e070f0e190b0310050306040c0519030b040506160f0e04020a0c080c0c04050609040308160c08031609170304050d050a05 69
    0xa018401c28070103400800c103561508070300704040002844101d48156010391003400ea540100080455000794810b941004610144241100e03000c01c000710b181d940020900ca1401e030744070018030207614499102c041c541d440303c891a00e52031401c1d0000a008401848000b02444444400c001c071b151501001280c500000251002c2c4650307a405110159074001c49050f1840b0749124030116061601140a078000c07070f040f4030210410f070f050104028500700c000e85841d01c030004681c400400501030602d618401c1340610041c1c0454541860600b0104603440d950400700103940c100e408400381c0040600c1c01a400a5400603150700c40d03800e0070ba03007190b040035018003ca1000300c0c214428030000030345d4076070b003a07401c1e5020320103500c54000340a0322000c20b03240103021075a8400014074828121040c0c0055401601d04107000503c01d49580b1050385c016607180004014210f80c41520b1500108410010312418440804244070f91500544034025800b41500c00c104150b207000a00a003007041c45207040e0031070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 861670791 1250 861669541 861669553
    0x20a09080f070e071b02090c091305070206060d0308070e0a17010f0c0c08042d08150603061909020a0902040825050d060f0e010501060e120f03040501051b 68
    0x20301050342d4403403900c1442010a03449001640d82c52051440d01c5d0b0402d0401110925100c0f286d01700070354414001c01000c14101d0034003090240f5034900c06000407c0354100b100085074100408020b041000081005014110300d8080b0800250b1050040c1e901566074601a01c90fa010702001034401103450b4015481400d00f40c0b081403184c04198001183d4000c1b5000420042448000c00e0301c41031829140a081c41c01d0612041200b0410814441d07a0080712642003404842041b41c540c0f17120503a41c2010311281e101e03810280c0d0340ea50320f070011a0000400c4008004174500403c028000d00e5040c00010381264a4841c0d0100715160705100b2400b51450788070664845031203031402c55646080320288920240503c0a1022504584003000c040e60009031010744d028850303459400140180600c4040d009903203000e1102e455000b0700c61980a000343c0e070385040b00405c40300100f014000740b202010103150803000d2010494007001084400b21902801c005803203d0400c55000703416000c454000903280142 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 861672041 1250 861670791 861670813
    0x213051207060314061026010f06030e0138060f030601081e0f150907030c272c0a060314010b0f01210912080f0403050d020a0908 57
    0x108001d02581c00c40c1c0e4003005080740165070b00400301025a200d0742c02032503403401e03010780034815a5800390185030a175071140c11078020440f10807403840990040071a1054030205201c082d81c54060310461070f4a8500a208250b014484043e001c541112030700302d09100342e00591480d82e01480d00041c04000200349035200d4140c0003100c2c60030741c011108280002c070b5450015025002c200d0a1014100340240e55030f150355903c2200180501014000020114101c09520705540c0c6d6800b1443c0b0454183d940420b080b2100c8601a02c0c0700d0b100e6142c0e0040c01c03031150703036260500c111424440807181e424030303504802c1c1914048003061658951035484d00030306c81010050000b03040d411010031248601302007010090615001c0b401c0310f42da20045a030025030740d69125407540c420001180342f2110b2018500303680e07202c1401101210701c920340440f1200f43d019001d82d000c0c3d400908555000e0b4040c1d24603215460659802005440b0715204250b1803540450708007500d81c41045a413019203203ca00311000003202d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 861673291 1250 861672041 861672043
    0xc021f020c190807120504030609060b0918150c0c251a2221020f06091c080d05040f120e1302160506040807060609060e06010302130512 60
    0x1090300e29100521695071444501400b54a801c42c81c00c0d001860241001860b81d00d00308100b02002d0174404001c014000800424450310950501c5442020006002040039061020000c0700804140f2903005008a0f1200800301003100450700c0710025803010150b0700c1800c0c1c40428007a418800d0945d10a450070003e03030300034101c0388035000c001071842006441d0744c0e151512038003110400403003007503601400041c030000c100680200f568415082c69064894490004100c00344100c3c691004400d180d02d00ca1080d4205268800f15440040c0d0700c10f8505449100465201c0c2410320300042016041908441441641d000303035100b411080c02d0500c12400d2a05000c3c120142d40c01e010754003114680755070708a4501810b003119015501420801095032081c20000c02900040c1c0d080c07034212000c2c4e00e030f5000a842800424030035886075411a48401c000d081c09021550503420041425241510a0004000c0b81042e40d5205109180150362414050708030b80d041c4416601c8560441120b180201031404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 861674541 1250 861673291 861673297
    0x106030c0e150f0604121410141303170c120a050403020c031c1206090f1d030a0516020d150203070e0411091203040f1805070216090c021f02 62
    0x31442101c2e102040e01c5404010380300ca01103101d9540910200020040c0342c804158024245000c1c6150701004050a5102400c01d1810318048518940e103052039020071540b46040c070742041c00d041c42c0d40c4038007007250b80140000025201c000c100540e400d00141c1143c100380c0171203220040792000586c0e58204000d404000e0442650100c000d07003d61507544800b03040011384800309104151455912034030001096030307200030b9010f6100c84151141408207651a0a0143d2400d00c4a81c003400180c10961500320b00354003241038880d030248d03001040704a02e40f96101d020754040e144801e0070324010003040e10009100702c00300c0800406200392941d05051854469028610800301c0e503c401044d01e00340d104000458603a141003205d020300602c2104520304100a1601051692804503441c0c42c0e1184180e601c2e40c100340d40803501c02a8030700b00030f0340310a01794003c4a0b00100789000030032900b8072552460812480900410281642d2118249802c1d8400c218070310301c043c4c8505202c4080700d81340b000400654 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 861675791 1250 861674541 861674551
    0x110d0c0e0a0605090f04020d0f0e0714030a031d011e0909050a060b07060e1510050103060905010e04021002100c0908012a030906270317070509010509030106030c0e 72
    0x50710300021903a002c0d000721010b1030740050240ea2880740700020070000b9042a01516002e0b03540f030b05407089284d540d100343d2001103014802410414548440481d00d00e061003d4503000750801098000000c0d0003040000c1c0a400485140e1030b10071482e80120f421f003400703090703509003003051500b1641c044e0f41120440e402d40d540e0990900c02a581c800318035041d0781c228410119419000c001120129050340c0c006000c50481006840d04035100300310b0611032520035a108240f0700130303040c4208821368061048100903c80103c0a02566141107503081d003169004002901510501c1403007034800f0300c240601c50440701c84917400c11100712a00303001440740c60580100d000c00d41c0380022081e205890708411040062503a2144180d88a04201c1100030380711510003190059242c50039010344180882000e0312440700c1c0004500c0c00c40e41414010a4104130090f50342568049500340030080354000b08840030701d4002e084c816510000035001ca4010032060780050034001e010800490301e0162103c50b0390240d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 861677041 1250 861675791 861675799
    0x908121501081014010e182701181401272306010302011b020303040b0d0c0801061e09080105042414010905131403040501030c21110d0c0e 61
    0x90b902c2680e0010101d1441c080c42034640d1603203604210740d40c49900b4035170319900003900511512100c16000408050f041c1c2d01e4440142c0002c80c034440f4000049048e200c1100d40c0d2001744240245034465142e0b021181402612030301c51a082c840760b04809411414440f08400da440d556031119454503141c64500380c00407100316400b00c03041c00b07005001c0080740075481d4000d0090801c50746564015100b95094101100704080c1400110002d682c080c40500010a04200121b5a8031360621494044900e071000080500c00c240c00148a1258041c000c030790381e002d6003160406400e90191080d603c81409500010082d0b082c5000c10040114807806001d0500ca40c4114141652040c8106816500d04800e114074448215004101d061996080b580e00991113212107000c054413501c0c0d0b0b401480302d80c841a00140d00014040010b940e0511070007400c0003242c40d03c41d1401000d4030390742c00401e503548400c01c0d010362180d400b0500342d07210740c08680021840c3d13581004425079214004d4982040c40340020301c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 861678291 1250 861677041 861677057
    0x20f0d020c01090801050f060603130b010308070b06040504030e0402030c0409110408070b0412030f0c082b020702010804081b100501031a010b07240e1b040c0f030908121501 76
    0x1540704140a22401803031f9082d44004160383c0d6200380300c8650001804410040c40b14250bc10100e1182c040080c0030714000c092040daa5840750400300c4d54500003401c41e0f0301503480d1008100c0405d40c03005500c200b041044901580d41c1d1a0545840d03140c0c01180c0100500505c1c04009415040800005004440158060315031b5582d60304d48500e40c1d40101e01c03134210100100c254050002c1d11a4008040c01d030181d0034043c41d0131031942c4400500d030b000304448518a55a00356881010750555000303c1401403040c4c400e500d0701c140b80d40001c054082c050b000501a120209207072003510700620810b0845080e0500300d48071140980000000340a00788401c0c0d949031031252010200c40864401e06060351801c204140c0b40400b0b96603405c1d0007444410400d81c44490741b04a00d0502059402005030140386800113180743c010031100100224150741c03007036100b1841c040140c0030040c1c00100740d4045c6000c5d07080c0000c4007402824441800c0c4070700a1000005c600d01c0040150b11104001050b800c641c081c0d0320030364 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 861679541 1250 861678291 861678299
    0x406090c091d0603070b0a0903080406050c1506150c0a020603090a1e020916140c031c020a091e08100204090e060c030c130b0705030c1209060a0c03020f0d020c0109 72
    0x42210410780f0541d416402243c0240080d060300740041c442d13481903240088132039949484606194005030024070000d0000101c419146108000d680d41c43d40c46684110018280840010b6a540748280411300c051000b0480c010694400c2c028050110707005000c05942c0d01d808440036454410818080f07038065034912003440d0480805410340810ba81c0501684000e0303c0e29001185442140700b0042c08212500c90440000f0b07035150050215048001300440c0c882003810300321111842012140c1c5129407041c40710360032490340890003008454514110482c4485001a429894466500016000e105101690f00b03c0c4c00903034010011a0305010b010032071075a400040c1600d1382410344060052000900200301c0d00c0c0c002070010200906034407426079a0301d030b80d48282c10b01c5070080c20055071036402c04138070500301410510001c0e004ccc0c0104290380e8078140e61280000c0c0705002d00e00c400000c12254070100c00c109030003001500d8114080c7d2007103ca06091001c80250307a0f02480e02010700003859020005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 861680791 1250 861679541 861679589
    0x907030b1008031828060311190f1731020120070305120c0c0a06090b090f06191b0c05100207030c032105070506060f0406090c09 57
    0x1609886400d400345150403100351301c0301c0440d168180d0b0035601c06165140c8500c0360026005482440c401d5a01c03070800607142007005000c0303681810301c0031901c0c181080301c5000c0104810420503416a0790801e6200360219607001c48070460201030140a00702d00320140251060124519421003001118085020100e061020504180d00301c000f030102d165a40c00c0d4010a101c03d1450b803000e40e0100442c0c40ca43d54a4540078641424041c1002e2000c0000407400c00d640e400f840f0484007807100b030ba21102e0140c81c1000082454116114551104201150444280d910b0551406604d4001007801c0e880c1c0c0415404541000302560003000807441d4804541c1c1c038203481008280c1c40c642c216412084c0e46240005211000042c100c1080031070080c0e190200001c1c01418086003e5030140384800c00c2003851440c1c90030b00012120038602400424421030300090070004190780d1000003500c07139010309106800450702400d5160050b136411130510002e801c1041d40a88880b0445925030f501d41e94100c400083d038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 861682041 1250 861680791 861680821
    0x5031605101b030b0609210118080301180b090109020d0501060f090902030406060e18190f2003010e25050d201011100e0c0d05030d050907030b 63
    0x1e200400c0710b0302c003148070340d000c4d600a088024010309914949074280c8001141064090442070001c03001e4501d08041c6c100034405c0c000c800340d40c910260a40e00d415142d02c4801d000500c07485a0064001c03525201000c140d0b08005c0640001900d1581e55503164122000607400101c1c003859124030300750001418070301c07595034420100d0041e260b00341213900300303103458020350310062068583c0c0ea02c0382400908810b80c1e442c0144590301d0a50140300b6100a28035440c1800700c026107140100302a80f0b030302c0010455040001d10595444110305e000004440074881503600e141c082568154a0403d154540303a4000c2007221102503c90f41d0446c80b080e80708d481c048010800d004040e04140c1c001113480c0095a4243c04120081989101c0d0020915070b00000d812600d15101c40130000300d4620326408071000800c01e040004403048801e100c81244112140c0d030701d041484006102e0309015009005001091048454001140105010515114035036554403240c0707104c01c0765004894030005044581038106 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 861683291 1250 861682041 861682061
    0xe010f0e0a2105030d09050708010c0f1d0306010e09010606020a08070204020f040308040305030403060612030c20030601080f060601050403110d02040b10120c0201060f051c0503160510 81
    0x507452900b010b4282c016a200d2003410001c2d07503100035515000ca00c041000d81840c0007007080102d00b40b402403070300c80e082400c4c9510031a80d503810241c500c01a903411048001d505401441e01c1362640300000291000c041110380d003140c05001d2180041840a0800507070b6106062000090001c16501e64040b6901e881021002d4441c04050140b440107203441e17002000456000c4451500b041e440f910ba5184542c0254000c8410764400141001004100c3c0101d800518504032a0003581c80075842c003400c00c10242800810707101000c131503916640c141821070a0450302c0502120b000d583c480c03883e1903540d45c0184044002c0d2003020000381d680d40c428011103041cbd950143e1700849003007410301400306241007414100e9005440c0d900000041c1c884030007a080c840e110f03545040720485800201c0302100c040c0203c0340c6c11a4180442440350285c41c1107150200d41e001d940052204080b10800c8065a4149c400140f0502001a416803030900780c0701301c08210780c0902c050394034800b000c00d2100c048400602c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 861684541 1250 861683291 861683299
    0x150b21060105100e190e070504141201060902120105040614060708090a03080f03160e0f0f060f031003050d0504180b03011b05130902090d0b040311010c0e010f0e 71
    0x14049800c1250700f00810180340d040c0540050718001c0002c81c8491030b08101c00d004111400200300903040c120385d468000f00302d407c1c038618003401c0c640c0c0306041c400c2c00c02190b4080d0b4501c0c1503245d149603003544141c00809485804640f611220391304030904010030300c02c1038811814001c0114072408400d018803080b42d00100f501e80751031415500c00480760400850320b5030081c414003000000c03924890050659551060902c0d540f40b41a00203c00380c1c1c03240004080070031401c0000303204951184c05807054901c4007101c0315901c090721200000c000344103488800c801c10001105212818241500d04003e4138490000c1ea0046a00c42c60304580034050b603ca45000040c0304000c00c91003c0480c0c0c40040c2030180039001249068400c200140c0009880c048c000001d17030002481003003281c40b08465406803e502d4000d40ca0040d2581c0040c0c019600c500000c2d080c1503800b00401c0c2014041e01269403071910030390090221407000c0402070080098603001c5404590b81b0b00c0019003240c03259084090800c03000f0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 861685791 1250 861684541 861684553
    0x21611040e0a0b0403020f07090f1a062d0c010c0f021b01030506010e031b030d090b07020f2209062703050c150a0b1816081003150b21 59
    0x903c0f820b03054a006031060b02076000780380b1070134002401070013000082c0214840c04654410301d44404411690000c890f000d068018442440c1c2d60b681d40000c036048004110741c810752074040e52000400418041c16009410540040c1603802c41c0419007241542e40041d40f80c05121a02c0c9181c1a03894625a42c0c0b80f56104c80290101105503000394089500440180f4081043e8203d440c042032a03c1c140400803480415a4481804207160800c07014201380282d107410341c03030907250008813402d030301601c40000c0c407556002003031031056113658092100852117404109840d496844460004100800d4251107442c10841040b011081c0f0107242d146586507840d41e4020005c941d1000ca491ba0480c160920a0b80034000119090b5005d500724140200b001110000b1400c0c80f680c2005502c0140001e0079284589010400034155512180101d68a003181081e88150b03940c078003926a4401943c2004081d03800150603154220a10703032013880640301c2500d070310850341c101911131542c4600c04030166200d68010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 861687041 1250 861685791 861685793
    0x7051b0d030e030a080115120203240f01050301031e1a040201020706050f12040303110c1e0a0b0a0203070207030c181119050c01090203010c050c07090b01121e021611040e0a 76
    0x1f000742e030b5541c0001c921b00400700003140200c10f4181d90068400300001450300507002110008001032000c40901100c07508044880b920000e05680014840501380810a070b0894079070706180701485005640c0f10103029440094401098018401554141e00510800d00c0102d40a8013030000c69001c1440c91403060300380200c0703240440d2001c200034001c50400d500d4540d01c421100c00000500b03181540c40029044510100b680128881000e0b07a0b000704507448103101d8004900242e0406400080b400000360303881d034403500e043c1e18214031035200428aa000035400196603c68110a40d8044154401842001040101a82a4017442201b41c40c07034242034051607100d80c000e200510112424000218a109a0f900000d0840701c140d0b200c880428800108002860424001c0b00c0240114002c00c015640d440780000b0416002c05240f081c0c103a03a28500410388609603455920000e9407680c1c203641c1c1c3c3c0740392068400d074055070790740480e218051009260510301d01750081541000c0d456004069034991 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 861688291 1250 861687041 861687059
    0x110f0a08041a030c0f070c0f080106090b15090904111f0206070903030905061c0c0504030b0a06230409170a020709050402100302070c0b180a150909020307051b0d030e030a0801 77
    0x20b0303001f25048a5a15030014440341d0b95114a4000e00c0380c040002001c1d0715007510b403000e0722000c1d0307100e074030034243c56001c203038105920030654400d402e00361440e00080c0e030380d850007104c1c0700080a5040e0f0302245503060901601070944807182d030016140d00b66941500c614506503808240c601006020072541d08081c080350901c0e0016042408118400240e102c540c03901c0c0e402119411140500020f10024090041c4034003021072903081039030b191040050324034201d02410488149003801c442800d407090300442c03d030340755003050000c02d400441c0c00c84003080c8042c0c084040d81c49403500b42c000d80206100003510880714424141f1483d0064000e48100c40d042d04106c00130b40c44003c0450f502e400680f4086014140000030346103022040420b0704c1c58541e0b100411815120303944c0401c00da841d00c4400006007960049807841250000c003030150300c0c0d1710f407010103842030301600d9001042e410f064100e014402c0f2002808000c00495a10104500c49a0851182d00ca00c90302c0011f0011400c900010407808175 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 861689541 1250 861688291 861688297
    0x20336120d0b011e0807051e03040302060c070c06030209011224060f02030f07020a120f0c09020304050d0c020406050d0b01092f091504030f060507110c01110f0a08041a030c0f 77
    0x1c10300c2c20382e01c1d000d48c03003505030110104410b40751304110010040004154041103510b42050072000c00504102c1c5964034403120008a002e00020503402007584852a4060102c0c02207180c0302c0079040c07155598104604103400c0c02009102ca1148154000055480c003482409801e1001c6601861803c03080e8280318065601c600310880e08000075510000310040254414151a40320700c44240e0400c40762309061000c3c0d0820703080101e202c1c0c41041444002070340000c00c0d42c480c1030581412501d241007400001c0040a90f64001500010341d10058801c00518502e118140d59060404200380d00b6402c1c0804144a210a0340070300310139091040100d500d5503c00a4130340c140c0c2c010005002c9100000f080909a0840d50085070a5858a0303120800c0104d0b034013403035038814528602491154855009556651041c210860501131646e182c00815042808a0a00301c3c00e10003c03100362443e40d02c1c0080031544244585542c0c940e0425134200403035408012240501e00c115001400c1c180c015a001c0721f04c2d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 861690647 1106 861689541 861689551
    0x2011109010912030e1c05010e0106030b010b0304060e013905090d06090c17150603030f031e010906090b04020336120d0b011e08 57
    0x30342d20242d031008480e240d0301403078065481c60805940401000840a07044070680f4502c0d20040b40c0c1e101e00c440300d54414402000000c908014440c00c0b00d0707483c0802003030000100010001d05a842000d075400c540200c10005071103000600c0b481c01c440c400c1311071b009220705003c003501c64aa400415a43c4c0e000c6041502422020f544c10014000d01c6601800fa200c3c005e1450f807441070202c642d000240c8244d10410444030103454000540b9082c113582140c1303101d48240c0404103c81240d800c0d5050041c0e0b0050011820900758800300302440d00003c161607a2116114900d8143c891140800da00034002d0200c0002d241c0d0428400205450800f01c0b042d005d14010000d200007a9070002003203d020901d94041c80c1426034410b00408440c0c0740881980c024450408078214003094040141000701440100700078801e4940010b5414140c1042180300040034035503503403030340c0d809020925406 = true := by decide +kernel

theorem cover : BRFrame.Cov 861510791 861690647 := by
  have h0 := BRFrame.cov_init 861510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 861510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 861510791 ≤ n) (h2 : n < 861690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
