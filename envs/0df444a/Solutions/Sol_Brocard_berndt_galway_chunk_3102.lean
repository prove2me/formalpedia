-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3102
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:39:32.890255+00:00
-- url     : https://prove2.me/submissions/04ef1d6c-8879-4034-91cb-bda6a8b4fd41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 557733812 ≤ n < 557913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 557735062 1250 557733812 557733821
    0x21c1b060f14060a060c08070201030f0f0608070f0f17071503022a03220b0a030b100207050604030809040612080310060e0d080310080a0f060b090f0609071101 70
    0x1403041e0340104448550700c100b040e9016001d0000b030b214a43c081c03010040e1a8103d050106d80580141c81070751a6031040c00160094009160500c010358606507030208003654a9110006503689402214400741e12000e070034038848a14000e614039141d0490007049541250714804081c0300c08031041c1ea06442c0e0f1030b00014480d2034503555480100b81c001c1064025081500341031500c001e21004254817140962965680740d1160809481c1039884080300017080301c0c100001c5030001c00b00c0044440ea220400b1000900418072624003500c51940d07101c035507407414800a001c5044e20f800038040c0c1d1816203075603181d51681e4019540190040e480d0075001074904509403403a0401401049061340d40d240c40d18150038842140d41140c1e0901070100f098004130303104d80a6541685a01140455581e1541d07002d03030f0782804644d4007021151081c00021820030085041945446218150504c0b00741812130400480c031004544e20f8426910f0040020141d14103a51410b41261b030a0900b00b800301c0b01c01c8081429607 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 557736312 1250 557735062 557735081
    0x20f031602040b030312041412090409050a12021014010b0301051c0501150518070f03021305100f12020306010210110d050f1e062808030310060f021c1b06 68
    0x2140000c020500040d03040f481a01c05030003001d4409627018846c2203410b4010900300c00d000c0c3d42d9412a490800c40c0410804400b2a04000d500d000c01c851690700a550310984c5585011440c100fa80c02020040c04005c0c0c54140c0f0000c8803484d0940c0e0031f00301440001e2a9801c550346401c039a8000000c00308200788145d4042c40c0c0e142940c24036041c10181440035144400c003004c988241200d04115513251710a21b00300d2061482d103400759503910b01d444c1189105a00d9008a43c0c4440d642d42211407094011441c540c060260b900c50054290116950104901088480d81e000d600000020b55004070168000001c000b441181742e810311807220404002c454040301c890040d55000c0090084411f0201064180c07641c0f105012400d616110021032f50003152411420426028080320310164413509107458050007000044131380300d141581099401c04010705c10480850090682c0d24a480d2000c43c0c1030b82d03080014402c1ea1000741000e40c0489400311009a041000c1036070050b40f0001410300e002d0740c2c0a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 557737562 1250 557736312 557736337
    0x80a020304031e0c09050a090804140306070801030f1b080102190305090304060c0f0c0302030a0302071d06012f03040e0103020f0603130803070509060424020f031602040b0303 77
    0x300c0b4114901000c2a0921882c043d030442c40030207200707000500603030841c0c0c25501c0d021404501511802c0b00100504000d01c0010030481010401064541ca85810440445012022110152100d160990f582282130101800d1241c201029802080c90b00780b003415520480f20030804119a076100160032a000a05070481c0310b0142040b4034941a4140203c81e001280c8501a524091400b0005080076007640c00007002179031502610424482d8000b00f140056401600351500c2c8d40d40d0f0718000752909444e000d403820b40d034016440201104070003103040d4402c00d41178441000c40020445071002b400240c0143c0c0c1003c0400740ca8011083c0307404d1010304018502851101002d5040d0720410843c03103414610140500818001c114003800386451104400360080b003110b039251694075041382d80e48920446070741c0103000040c0020310b0008101440d41c610240b0400c0404128020f40126103d00300034140030034030741c01400200c8042d007890525032841131006000041d1400c051012a00b1030b000600c08140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 557738812 1250 557737562 557737567
    0x51503040308181e0f030a0801090501080106030f0809040b19240f0c080d0603140606010804020102060711100504030f140909190f09140c010c020f0d0807080a0203 72
    0xc054104005030381110200e06044030450f03516010a55800c903600a40c3c0c58030014024001004c076081c44448103400c20313401913036070352420941c001d80314007420b110302d0710b1441c6044000642e8503018443e000640e503204401c03907419103082d00c80b501d082d040400813960280d03469014010744e55980401d0a003002a42002c0b003030385464004d800020404015034030700c62100000c2140642540075031040c1e804040e41c20402c4508030b050078481d5890060b00700c0428128a499004401c3c0040c170300d600c01c0b170001e000003205c1403996010011a008101514024050707071101d000300c2c2c022802065030540003071852040300d800c1d03007006601c1000e581054400381c01040b084c01c410040a13074030541403a90f0808031140d0700d10341501d10020840d00358004180c11507201c17014550824020250300500c0130000c1c05202440b0556103418100d400c40e50050405840c0c0c4030b2030022504d29409010340b01c00f5a0f030001c02c0c4032001d203000018010100501c1e601115140410001280016420f40185c038401080364000c0d034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 557740062 1250 557738812 557738821
    0x4060b0406120b0105151c1b0215040b0a0e16050f0604080a1112100b01080a0b06030c0a1b0c0e0112120e040204090c0c1a010303021203060109051503 66
    0x401c550440d04181c0286045a10640200321030440160443e00b05494880808084250b804050302445a0b104840c4441c01403603107101c034182e0010480c0030104200010481146181642c0d1074441480c0e03407211446010001d80443c5000441c5079000c04100d8010a08072032040c00c00742401c0c18462108e00a6070801c10901c400d040400b9040224030095680a15181c2096070107a40d90034000d000410441c1c840b0316032000c030345480640f10205000780c0c0c202d4481c003d0201c0300e40c02030200c0c0488107002410580021301d400c103090041c2010f41c40c1c090102841c54072500b20b0390005a01040162050141c80002c0b0301089000130f00c2d040303001d0f0050000c40b405a003810391690b800d003c107034802062214080850004603039400754080305a402d41c01c001e1810b5907a0004a4040c0c001c9a10000d01649440461b0201d0303034100d0380346081140306140001d030716005c1000700083c1e20000e000280041c3d011007001c0603500700c210300640c2c00c0391050414a54066651000680c00c0040002c80d035450b040110920 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 557741312 1250 557740062 557740069
    0x30216030315060e1c0512030f1b0f07261b060c072f0909030904060503030a0c080711091510030c08130c08190201020f0f030307110f010504060b 64
    0x420141180380b84c85400c1c616080e002030f104600300e1800d0b81a8440c01e03000c1d4002c02c50100080c4100f15069411142c8034078104040f035445040881c0d10421581104040c0807000c0f0303c01c17044a00c00b1440b502e525080514945076103400c81c50480d060b40c0e00344104200124411800b501418a04651140540e00110019961420070b4001f0740f008040307010501040c030000d40c006075120300c2130407990100c08088008040c007200306080111455005251041808066140440107084000e0199401c0c060103548000741543c1c0c9c80f5105152001030518106440000c03001001020b000b4007480d4421016280b1070000b43c0c3d0900c040d00c102075141c02e4000552001d040c01c401e80c84044909003010810381c1a404d44c040c1003003078000d1042000340d0325a0040d0701040001c1ca03540c80900500d104485020304140a00f0488a00501c402e074094881c94259440300540000c40b850001d4040300a5811b6480e410b90984940151051109040c040d03010215590f071001d1188601c80d500405021920f800e820050 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 557742562 1250 557741312 557741351
    0x16060c060609062c070e040e010209040c09061b0c26100c1413030204022b0c11070f06050306010c0b04060603030e0f03070b130e09070816081c0302160303 68
    0x6084113040000208031403c1d42140301c60300c2a030030039a000300c2c80d5250050203d0080c402c00a03c0340c5d00c6450b14400c080b4495011001c0015520961180002c406d4243c14105460560f001c0051210340d540000f4042c030441003e510200c001044d00e0710440f503418281d00d07420440f1030484140d40d1541e403080860400d034804641240108110070462511a004080303002e00a45804041e00a6400003000c0504801c0d0540c500200c03004460303500390495a0355500000741c004050144009810a4030f0046440d80224000007100c050b0b101c11000f66182003401d0391603400c0100200c0c1071140750014000852400003901d8812480340500041d42c0741146405040c0c0c1400d801500d01032481c440340c411140d28009624820380d030b40c0d051301503180d4800383c02014810030290413803020000440188400c46034000b60000039214064240e80e0842840c0c0b26105074600d480c410185541d100f04501c80c5c070b0740f40c210004041450949005481c0054076441d0030045040160b00b1400641d684e6010140307000101da4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 557743812 1250 557742562 557742629
    0x105010302091c020a0515070212030333090a02031906050a0501120b030d020604060b03010b0f060904060305010c02070303031a18091c0e09060316060c06060906 71
    0xc045081540000100d50f5180c03010420081d8102000c011809564130362021a0060000419006004a14900c1a0740c0b50708034000881c007c030f40a00c8409441500401039030710441072244011404101c5403031106c10b40321905000714480001010b4a40e0545844841500c188140d00015a5900b480301070f1030820040003d4509500740b80c21800d11103039440b481e00c4001c80304240781c00a503113041542c03664020404103542d65458440c401442035800d0f00800c10511541c0909802c02000c922041418240d8446200c40d80c0d108162214404d80c074a01107000c1c0107014800f5100040c01501d950340e00742110500311421016031310002040040541c180640c011000701e550710140c1a100d50400300f10040c82c1c8485142c04148180001401741d03100300319840e001c03c80300501890321070b082d0340082d012602440040c2e02440c0918002042c9040028140c21419003c0c0080c100052811804942d2450058012a515916403034000307510300c0c050040320044c0c1542d4003100f140f003115503500c8400604034030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 557745062 1250 557743812 557743817
    0x801060810050105030c131701140f0c03060103020f090307270912050304080f03010b120c0307020a14010b030a121e081b04030f060504020310060311041508190b010501 74
    0x740c05000590f441400e40750408050384280e80c0300d1001900310345030f0070307041e4001303403099009151070034a000d005401c40b13030351061907000103100c4d5103c0e0032a22046240840341080b0500c81000800c02551080d4001c1c0040c0c06400051420a000c0717100190512109074001040c2d03906a0040d41e0040010f1210000180381401082080c40002d5454038140d248594903c001c4c072070040001400d001c03104003180c51000c000348070b045e81c80da124056640207400004140c400401804000b0b10400f122070b080b80d024214540042034610416507901440e040e00c041c1500b11952600f03c000c20380c1d00c0c100000d0150a100d45400603410004440042c00094a4004480501050400010015001745805402c034240307410340c41240e04004031080d40c5114584c0000d1820030402100010311000354040c03030080c2d208909a9030450400b02040c0103558280c003010386047c0c40c2120200840ca00b50340312150001617100103d44580d9101e03642801d01c03003003003040d80c007101e80c0300c000f03400700207411000034050030090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 557746312 1250 557745062 557745091
    0x9190603360507030510050106020d050a0c0b220c05030d0503312f0906010e060c01092f0102011802091f0f170316020d06020d02030708010608 63
    0xd0081180c14410740168107070500840446810301a0500011020b03607008002c644d03200d6240c00060000f403038248541401806140000c00d42c0c54800c4040322103104da40c1d0b4840c0d042d80706680321010a2100a404c1c00c80460031000010034844400000100700c50240000c402c11914007800d0508085000e520441000f50410070044280184205201810144041d1152070352006030211035481540401410300600403144110101500c003075180c5c4281c8002c00d0522465251081c0a000d01003a158103002c00c100501c06102802d22130044c08958040d2000803030650211b0721540108408400d03008880700303041310100065014030862003140e00c000e1008100c1a400d0301c13240b04d04d4551002c0002d00c030310001d502040c02c000a07074040c0024284c083d4030030b0f06c4e00740d40c5420000f118003107032040d00038118200100103400400401951505140a40034a0b90481c0300d13401c01c0035100f0700c0003003180e00903820b100b10b40100401e8070245200d00903a8803040640e50600c0c0c1d01502401c0024136101c00c04184 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 557747562 1250 557746312 557746361
    0x80f01061a0a1101020d141806042f09040506071b08030403050a0507022e0801080604060c0903080d02030a0b03030717031021062f09010509190603 65
    0x1d070480d040c6015030b20b00814501480400d0501a101d6410481c10b45818045410404003245031154020800980854030310079490955031746481003100c2c00340100000700c5400350060940d800da0198005135120201e8901122400128101d00a440c26039681d0303c4001081880c90300a00042c820741006480321147c80071942c1d900d103441c44020070080170402e01284c0c2c0e100c5280070b0301c16200415801054407508881c040c1688503400c2c220710207400340e100c4131a00c02001500411420703050702c1201d0003500700381c0c4d0340f030f141e050282114181140412040d40000404100e4450282071702d0084900c02694a0620540e00c0d020340d510602c142c2d100340c10400c00c0314006800314600c010b480d640440226141c2d540d08100d69140c90061b48540034000c03c0b0903c0c0c2c1074010001800a4040e07100710400c004214014000801c465081c0045078110494514060802d060100260600d0b81d8149041341c90909400b000c140741030804003501589025006003030101c00e406000703298400f44640c2d42c40d625008c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 557748812 1250 557747562 557747609
    0x90801140a1d0709020f0d0212060f0612041b0308030c04030c0906050102060a0b030c12010905060a06060f082a0a0201050703020918041518030905030601030305030a1a0a080f0106 79
    0x940f0304c50b1a1500d64002144d6800b1a0084243c88092444100440d1526400b649000ca40202102d8203849600c189458145c0d80c5442c605030b40041000360412096560389030b551401c042c00f0881660781d046039410000001a180000551140c800d14103201c1d2260316505d410781d89084503030090a00d590907c8414442640e00091007640012000c00218080d40c1c00000701b814080c0c80c503a05600b041c040c4008025102054001d07144d50762042003124100c0e5212000c100407102d079030203a9800202401c41042441703100d2070003a1b8202c469481c060011190b42130400711400c03088079100344035080c0881d0100109070203100b02c46d40f003601390074103510340118440000d1401c10006040500c601141c0017040c14404e0703d4a0001d01c00c3e4454a042010220840f0105050020744030101e0000f086044086040d060116205041700c3c0c0c50303120359003580c550700e0009016002607410490710144240c0c20014035500d03440108005d0a040d009030140020b407228280c00d5034190f40254169840000e10079051a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 557750062 1250 557748812 557748823
    0x2040609060801060f05031501110d021605060c030909151c03022a0105130b070c0302030d050a0818012004090b0d11090403020313090506091f030b0601090801140a1d 73
    0x1005029641c1d01c8c07048560050b2a40080c0001d40e00b902c4c840c1c10320340141d291700050f903642c8100d4a400c0704410540e4900400c402403040b5101424190028046051141003003006a03030801000303003014084403215008110704440d20503d0000f0b01607150445028960140014400480ca2005105520000c0708854000c5004100205c1c100080024040c6031048146285405001c80c0881213075038034100d080c014002070141c04207078464000d080c0d1140300180610122110090140c640d15607030703540d60308c6807075589200b00080b24541d5224035200d00c41d1208640c904946102a440903511a410505641c08540c554801e8a0045002900310008542404d180c0c856100382186c0e003040035681c0d450128103500075000980d400e40000c8001151a203a079800041c0310320b2050340c1a0f00c0c150303161801203490301d901d502004c121025802c41030010035124517440d03a05c44d40c103042c54468150340d11030807804c48060a0600c1d182e040c0702000d0180c1c0011500448503144a0307041010700e0180210529625035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 557751312 1250 557750062 557750071
    0x2100b01030917130b0c03070219031e060e010c18091a04020a021e010b0906040504030c15061511011104030203030a030b150a020f15010803121302030102040609060801060f0503 78
    0x14001050090320300504c203030100060000c5038405a00c4900107400a80e0703981010200700d20603242c0582260341c0c00b8900301e550049941101c40700c605060941000c03000c500403060140c5000b0b4480c181a110101e00340907180041009540f81c075243c00525849890281203038000c0c01c8804e0405a24005142c42e03115041ca00d500c1c1110700590360281800e0591a100300030f42001c51440d00c0c107050603288031040d0b003c400010801e584205043e5205006c200c121a411a002004106412b6030b030800304003130342da0451a4031880000014141d484041c40421303d200c0c002480d000400809020007400d0b400c3c0288101035001f182200e0416081d540020746038003da00b0b0303042c105030380d640710000c40350703261110040241c81502c1c004daa1000c0f5500000c1d1100c001c0043e113002e40c80f900e05240703025074403400e456040b01c4402010354108004203115811020b000303407141d07a05403203502900300565420700c000c1c0020045034075200c01d62031800038081e28601c4140d00c40001d100c0040328803803500307810100720780e4030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 557752562 1250 557751312 557751353
    0x1e0507021c0501050408040611060c0d0e0c09010b09130209061207090e0123030c0109060f0e0621150d030e0d0b10091a0607030c170a02100b010309 65
    0x280500300c2800c100d241c00940160956003000e081c0000e11016030b000704192209030742c0e02c078032507003085403490390300c110540312038030780320300812241c0652022540f0002104801c1001d03076402400d0400010400e0000307030007000618200150103c0350745404070a41c80155a4210203609114850300081c0090054620403003030041d2080005800d94072808440d0042c10800c514088a56102c0c3e125000354882040180448101d4220203819850002100c1207002c1e03050b90b407040782c0d42c105001126600e45204043c1d09000b121070801c001550703132a0281c510055048290300e955000a000c0c103440c3c881c0980302401c8040103120032042920394051003407601e5054240100c3c1d030106000403501080b00400b0260203503034201700703021000107880741c01d4003290007980080c84004490642000c01001c24800d459110b04100003900c00203000b2400868900d0188004040201e40011010390540c000306c0d1500068010010041c880e11075131243c030f136004100703290401090032150b40314a1102010402c5104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 557753812 1250 557752562 557752579
    0x8060108030406110f120901030609050f041403160f1e1a1003081b0c01020f0715020c101128030305180304031b05041506030c0302090a080606011e050702 68
    0x900c440130884500c401c2c03a013170125500410301c00b4201c001c9070820000c0a000034182040000c001c6c005016140c01003804058100031600c4540e104d002d602d14840a00946000501c400d0006440101c01610020b002c6c0c0070f8080506540c0c0740213600c051407078920b480d9007188407100e0004621000c1820080c010b0034008082181c4640703d141e0003100b55031380010b203103902c0000c020003101521180c0080f0805850300701c6107544110801680c6840c038192558900e81e1204000b005110020b5250200c141c000d4019241c40281031004900718006c010544008074817401c81c01c04411008000c4159034881c0502045012012880340809000300c0c2c0c0e10240c100341c1c4400c04104000c640050441c20b0030100d0044030707551591fa1410412031000a41d2021900508550000740d50078039000741c803515004004001c0110341804c9c4107400501a1b03614190425900344002c2c0c00b40e031906040703d0003030010800200198500000014485940706078112161128107104085032a00f1400f95071409504507220309 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 557755062 1250 557753812 557753837
    0x6170607050a0306050a140f0a12080904060f030302031801030522030e061318091a19150e090c0a05280b0c0f03041d0402061c0e0708060108030406 65
    0x10050013950300016485800e02c0300006052440311800d04034040c09a0b0940e204d03006240400100214503c0b40070f20f03c400246040d00041d41c80307402071000703040c02000007480503203130b03038443c070b41c142c00d0b604110003503400002e0520b00709424a104480728002442e09001520709803003003501c2c038001c03c06428201c0400d8440c40782054025100700002110213085143c843c181032442490480044c4210762482500c000306441a15450003025601a001f140030b0700195000001c0d01600100280300041d80d6103641a20820030145000d80d11400c100e01215a44090800c910180d803090084c12003c102c0d4819081c104040e01e03910780c1e5600700c8004032110705000f41c40c83d600c4515010a2212400c4803070b034002012070814001c0c002307031012000e280121180c641e4110005a034a1249014420900300c3c800919034220b8210703082c0c41c1d4020b2028114904000000c5440b81d800004000c00316410b80d1100010010403004000c490f000341000d00c010805949415101c0d9103e20990141404001c0c2485492 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 557756312 1250 557755062 557755067
    0x303020a050d0905070f050301060317031e0a05070f02061e0c040308040f03030e060f032208030a0606110a150b031f0209210303070f0323060406170607050a 69
    0x2c2e0051800060306110001d594504a501c034107650141021440c01002c0101d240d003414800c2c6401d5a601ca0b6803682c051002440c0c04002d9000148142c00c040e1007a10881d010340580320205000d5020184080341908000801a101c80c0102404004551080c010041c0e00d2804405451120814035400b040d04d40f258002c650316440f481d00040c0c803079600050000765200303400c0c030040d007101d000381c4d104214800d40504200c65841076085108000c1d6051010500c001d140780380c443c0100d600c200d80b00c40020041c1e594410301d5001101c00c00c0c451070b40c6600c104a656000b000c10b40f1400000d0003c2e00144ca89235450340c0b4103948400b0420790150b40c0d100322200649041080c034142c0100d10078500c0082c600300d45610301a500400c601e6008080c644107181c0150120310460f034118a4110265046a03a036801c104c80f507800002c440001c05480e58041034000034a116510845603050708011344602d810410300003501c190307074000000c0c443c40386024118907074003080d4660041080e1130f000f0741c0c0361040c1404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 557757562 1250 557756312 557756317
    0x8090a110a0b070318060309050709020c01020403060e0c01020114090d030917070c080c1c12090b040f03020f0a05030c010f110318041d100b040f0c11070f120303020a05 74
    0x24500c00038001003c80906400403040d4405400319116030349900c0d1514003c40582d00c0040e0b00400c158002c85041c42403d0b103d070058026000300c2ea0005080039aa522040155211111007418a4012a0003c011941d0a006590008a200d140e00300f40d400d0114030165540c071318200000c10140e681010000f001400c860003104101382140607900c603040e0303080c5003000c0345403485800304078402d10000c0344090a02030401080b0101e1400c0c4079900072242e40311601d945105044880811400b100c022442440d0040600040c010003031141d076270345080d0b00c103006221aa150303c0a104800c44030f0201f02c0303a07500040200e8446020301c4e103200d03032008000056500312120000e0521500006c58000c60b80d8207034014806082600700c4d002e0001c0049041c80c0b030500802150403444d543c02a200c0c244041c86140c012001031480075000103000140d03e040d00049580300040000003a28000c0b12100405080082c40090503500e84401c801c0b07440c00c40c001c441d60418140c0102410b401149600340980103105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 557758812 1250 557757562 557757569
    0xc0a050f04061d2211091e270103081c11090a060302040803091026070e06031b0a090308030408030109050c040621230403142a011e06030606050108090a110a 69
    0x107d440100012440505085208880d5802101400b045001c061010071050207845c02070b034441c0407181d00b1501c41107c3c40e44943d40409042c400d500064000740d141b80b161400c400d007440040d40d00c0f015100c04006000728154403203400c141c0144014043c0410100031030703045400880d80f00340a6500028107903500c1801c2c0b00d150030034031941c201c0542080081040715200c0c038915500c2c0c0b510700c1c03400c208025280c0020b440d501e805000c0004241884a00c0a0003803036881910305108004a41d207555146180d481210f0464804230080010000d40540e0700940381c012000e441c104d4100b90400800500354100110386800001e5008901c114029540c1d01c0b441500358446129500809900c80b0a180c18006940c11800030b91250440f817800d00350807003920b241d0b0319048a102103c0515006c24440d8121b10a00d9203695542c60251100120700608040d0b407032201d8000118880e465420508100c81c00c41d4080c906000e00c1c031007000784414012480c03801440d4045c020100d00c50012000c618038402540 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 557760062 1250 557758812 557758819
    0x51c02010e13050a05011a1b030d0608010e0c0a0303050a080402061b011a0301062102060d02120411010207050108041407030c060c020a08010e060c0a050f04061d221109 74
    0xc00c0d8242c54141504401d00c541c80b80d04003401166038410000c0569219106038051001042c0000c1030600d61a25159181300310403000c0302d00304006d150703182040b01c1c0b05501500d41031b0340d9000d681510413400e00c81018143c00032141402140c0c5507442c0038040e40700741c00070b50f8200080280042c0465903000c0903559002041000c42010100c4c42c1e243c20b00070290140c00c44500c104400c41c5c5091032405006100036545290348030f4020440320700e150741070b0070551401245d1150091142070320041240c80030f8a9a070314922229602d9007000d0601d10190715070040c0141c1150800300003400140d8005040541082d808021001c08181000b1100e00300700f00e64100600328641c13a440010352550001c070090f081402210140b08165903441600d08980130003000c1195604070000040c070000100700a44100841414042d00d84180038568801c03d6201d60044804100210800c10040034a00010b900603d01a105220000d6400c11000c0080c032581000003a01070311480c5400c1c01901201c00c1c5c034040d41014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 557761312 1250 557760062 557760079
    0xa12021c0f0305310201030e030304030c0314280e5b0215070c06141003060b061e04090c05031902031012150501050a051c02010e 57
    0x84000500410000800c0e20000f402d010109806440311340ea01c2d180780d03102c02245440760604581600ca6070040d0a0140d05240d0b403400d82e44c102e4070302480250301c035500c41c5d5902c801201103850040d01500c20f83c11181810342e0306100f110010322800c40011404030441c905203510a240d00c404840c1d040345030100075080520302c41201044141d0103000d904000f1014602c1c941b840d0b1900340c40701204283e0703902050072a51065422801c54104060a80010302441a20118a6050344020f081403003510705e000040e9000c2e800c0400e11907948203501c581d40355101a00c0341030410412110000d10b090102604240d80d0311090125580c50208807036811302460f5154041d900308004d07180e0150044d02c140000b00e810304854012049c41102228400c111102f4003c07254010054104d00130340000b850034414420301d00000c100c2e074540313000407182a0300c01c0d6054610310104201c814141c40040e88014016514444c040c0200e6407410003e030741521120080d882104940d0004890307055500c2c40054200403030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 557762562 1250 557761312 557761363
    0x60a050402130f0b090114090d0f0c050103110c151015020109061109011d0f0d0f050c0a050f120c0d12170601080a0f14090a06060f03050a1202 63
    0x411000000b12116881c101140344d980d4499064140720714030344580000e42070f84802c840103440c0c5000d03000400d00506002d003540c0059443d4590010480ca0a50714800812410420b942c1c1c580200c9450300c0e0742d00d96031810a181000456524100c1c0303e080d9085100c00e0001a0b01e040d0010b01d41e400500c9000c400f8100e040000001038020310180ca801e503143d600301810764240c1c19440e8215010141d06969140040701c680048504000c1c2c4030010300e41c003001d0030311103c5c000c0c1d880c2c041c2010b9144c02006019040c0c4418503001d442c0c6034004000c64007402800380104060740e0cc2e0308440c8500d060683e15401000c22444545007040c0007810310755844a101110041482241031645030089a20b80310f0b0907940011084407420500c08840d02c0e0300050904000491000d996080455000c1e070307514000c9441e11390090380c10b0303520302c045030503100310342c400115101845068043c1500420955400040e041c0c00c6480301d680f075201c0c00802034515440043c0c901c0703140d4401c2010b0704c00c070b00519400b030004604 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 557763812 1250 557762562 557762587
    0x60c17130b090f0c060c0307080d02090913020105090f04020d140103020a0902040e2205120306130e060402190e010902040929010320040b0405210d08060a050402 71
    0x105041034601e00004800681c01c01c20010b80040c00040301c0000b4400c0110b610100005540085c8100041340400d0080c10002107544000d40248040988096100c801e48014426410302c020070160050009a44a80c0543d03000400ca444290082d55010a02d24503000400c01034407640c180319170308038503041c408250b100001d42d40328182c0c1c0c4222540d020096440c0c034078000707a009074052048015071070408600c5845030924005003000200e2020024242907464183c28180341c0490140c030342c0c01c008200502441c207401c10102400c0714080420080241170030380b40d03490000400090194118060080c5464800c0c1f000100030301c2d0a40059607076603100d0301040040e42080c0b0401c0582c600348100d01280c821103403240c49030f221010000c00d14910030750b001100503081c01c0f0780985001009107881d111403100600240080d111403149580d44a28240c00e001e400c061010407400300c8188000b015041e00004501c001d2400c0041c0350060309a00c0d800002001401035074041503015100048907000e169 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 557765062 1250 557763812 557763841
    0x1e09091f031a06120a0c140a03060e010c090801060305031e0405030316020406090b03060402090411060f0702030d020706120e01060b180108010b1330030519030b0d060c17 75
    0xc0c20b132885040d04c01c5107030b403095580c00c602c08000c03c45e0301010014003541c48005001982214000c1c031180d0301179941e4649000705da4903e0180700c00c0ea5151034190503110b8000107071130010144003000300026032458850588134003944044e00b41819610502c402085505415580500300080c103480d0f583c000c0181c28a030007001c4410890080e41822000a203e41c224456040d05d17104c003501800003580c2d40ea00f000000d0400410481d00310610300040701c402e44504001c0c041880d0010318a40d40c85240780101403400c810f0b020708030115488084184100355100c1b4051014080001e404241e1405018660f4050202c5402c082021a00403d801d148030040403071a003103544003038843c10300c08c1c0d0701c801d0b17088802e204886140c940310b50b1100d4108508075503c80e91805845c1d078441c007605495600003800d203d52403045016030000340702154207084000c40840090302c402c402d0070704120750071045012aa013041c441c2c1c0701500455a601d008001c0c82e00619640b1031040092500110900d48020041c8400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 557766312 1250 557765062 557765071
    0xc09131a040b0f06010503010e070306081e0111090105160302030705100b042a05210c0c07060302070f0f02010c140d020708010509071203051603051e09091f031a 71
    0x10303801d040880c030191540c03d045401218107a642c180346a0034040244841c60015001d08105907907060002400c81d0203004010100b251030403d4105000c0c20381c0e0329400e5521003145800e00701c50810400d00941c1e001800c9465504444100c0b07814881c03a81010b9082d4000c005018015010300745454000c032503198000c0317030443c0c0b04880400085103404240046c0d1030100220f811110315a228852a01d4002d0b8081d00c00b02e804410f10b9160a0f04001280382003e800740d0b040d85400c2e8020400000c0d0500600040c0064082c9250441c248241a110742200e141a610040c2c10104100340c0841964800d0031083c0c410354011009001d0103043d00151591036002c60301120060041075004109580103002c1c2a003c0c0307180324001c0000750f003481031011501caa518022000d100f001c1120304002e500d2149080c00305406900e8403512901c1414401c14103e008400308162420100403d0681d5940e4040340f90300400012441c1c1c09215150303c0500c1c8140b038582001e0032030442c40500740c05101900c80c13007902c038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 557767562 1250 557766312 557766323
    0x5040510030209010f030b130e010c0e010c0308010923070c050f12030103021002010b22150b0a03150f091a0a0b1804110301120b060a080c09131a04 65
    0x1998403080088080b0300940d0a00c5000841440a900400d4482e400140b411100101086a41c00030800040103c0c0e06680d1404d81a03515140400c1103903070441c45040d800c090030b08042450070000e60b001401180305025035211075580b10084500a00c0c01001a0039000104005041c1820300640144c141c0081500c00c541d984195101c4034050a8082100c10b81100c51481d841e0869003154204440c846450101004542d030303c030440c07420795888546a14a1084148030791440c40301102180c019220008001468500403540402c0840d505e1401c41e0311aa42c245000154503010307083c1a000d030200c03a802110003221709840401c0000243e40701d10031284142d0604402120141d0500c20002031610130a49811820711081000c20303d143d1264034000c800900014820400c0541204250803e81100e0b040c0040341c50100100041508142d40000c3c0450b500800c152405003120340d40d0700440b09542c000c00c00034000c070b02580384401c54681701550200501000019207008041002000c0301c0c1a00d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 557768812 1250 557767562 557767579
    0x2113210c14010e040f020c07030b0f0f040206091c02030d020d0215090309100201060308070803071209260c100b0901140105070803040807150b2107050d080c01020a050405 75
    0x524804104419440c0071040c0c5481c03a018803500204802411841810900c807074080003c0501d0044c2030008038041c1d8402c1c01000391504000700b45103403880300181041200040740d800d020151707079040180d604040d800c6500c4440310b08424421580004100402501449008060300300150042214000944039608907a1203081025040b11400005d444481c0d850b0810005d01e501420300740c0506415040c41c0c000480caa0303a0320b40e01c6a070b00c0c0d40800e00c10f0305c0c0b2803c04818000c01c654401005106462076242c00d00100354240c40d4160a5003500ca0002c0255019504401d821410f443c140c4071034004c0c00e41900c681e45200c42205028001036944d05102d045034400125070340d01414039404040c0c030180c1d902410150303039550b03100c5031f54006402900d0214050028400098500d096001071501170080802c0c14a2054180007042902203180384070798902da54035940d0f83c040015480100c0e04100c034070300c1a2064508003800305105845904016500014480171420b400c10018001c450741501c0c07a15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 557770062 1250 557768812 557768819
    0x1060809160f030303020a02030408070602011514130b0a05030f030706060b040e0403030b04181406070e18041e030819090b1f090204091d2113210c 65
    0x66a50700d000301d14540800800910203e0b204c0e03809401d4054150040381e05c0c054840c0c00040c03814000f54400c8005039140d544404e1030105580b1240014138294004600701500c040c0003449042e03001070110421555090040480eaa0b140840802000c02506481d0003042c5883c0c0e140d142d41c480401540c075281420800a07409000408843c102c44a00c5008500c2d52201d5070210058500100c00540c03141c0c6400390050802c10500341c1d00300d018400c041201421200c143d100f424440010561001c0c4407015004481c603480d45400103031846a203640e400b10300e950742d10b05003030141c032202921101559100d101c103003010382001c0b1081c0502d4a04108144c0662060300b214181c0322903030002009100103101240d802c0e88080d09030720032880c10340302c1954515210342c0c0d0032049030495403220032210f40700c160300c00b030701048401480070904030030002e48410801a24000246801452105c81f40140000c000142c03070360190f105000742a50000748210007912242c031072125812400280d5000da401400003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 557771312 1250 557770062 557770093
    0xe13051f060e130f120c150f0b01050903030403030c022106090c032404050a0b07030606140f03060607030c06020f04080d0807093302070617150402031e01060809 71
    0x210503400b480702c0e8041c5a00303680d62101e0240d0385ca03070f000500c0030b945d548500103101d10f0021584074046007070004418031100c1401e41951801c001843c18844200440221503c0101c1103406617901800c11501e007a45030301c007080c40b0324000700f00c0d4400549030785e0709105103040210b82507026010200c220355140b00c3c10820181c951980b8000c0b40c0c400403074580c0f100340407140050800d520500940c00e41d00c503a560350721103c002c0c15044501d0781c0000d41d100e1050040782d41081000d00070101c014035030b9003403c0b02c561822029104c0a851548101c0e80464001c007058492848901103e40c4990300350b45903649003010b50581c0c0c00038004d80001c0d02071050f8001c0c00c0c51040e0400b511071601030342c032400c0031032400d031200b80880c178500c408100034561030807251070084c1da60001402c0e601c035640c020204140f4054009114403088014002c081c0c0c189824459a80d10f00e8041b698402400c440c0140d884d11143c401720009002d030440141031094030000011015080740045101c0e02e46081500c0c0c0079a07441c41c14 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 557772562 1250 557771312 557771341
    0x1090911040504290f01120f060c02060a0c0804121803080c060105130b03121b01140f0708010605030f070c120c2315090115030c03020310060e13051f060e 68
    0x40170a107103140001003100301c01100d110703000389000b076011031802d007000d403940c2060362a60388180300036a0118040c000c9910140c4900080e4060310702c0d040c60306040940da580350b90320309250484102308103100d425202000c0080d400c0011684209000d680f0000a58440c2d01d6100074480d10380700744140c01030034050050304c1c042c2c4602c480300240a4050113640b83c21040103908005484902442500005c485000c0301f44200c2c030300d40c040800300081034a0b1440354001c8042c001084982000424001005403a40150551350030240c80c0c41c03c1c00d42c81e594000308943c500c6e0105000350450b100800d11400305504542d41040c1030340984a080000f58100d10200504544042e0401c00d41e03001440f418a411401e440143d00320280d41c0020074129018041c441c40d0030401e8206a40d00d0010850400c110b140402125500c610b55100c28045503241c03510326000c2010050100c00350511041c8154100441031201810804654030140d028504041900c1e000f000716002e0700d40500085c40200d41e440207510724 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 557773812 1250 557772562 557772571
    0xd030204062001060909050303100506090a0608090a0c0308121513020304060e0a05030c1b0f010c0f060c11100905032203060c03050703050a0902090109091104050429 73
    0x16070395154901a8103103022462444400000b41d540e400011850240350301035a00810f00440086499052000010384041495440544140400c21400c06151a01c08451084820038148284241d0b200c20139541088a00138004100b501240c00110810a0a01c040e00a509052a80d00c1044e41c9140b800c2c40700d140401402540002d404041c180d900349580c00959005100e8370300412098501000a45041d0808000716038030741011505079482da0007000310354405500d500c05600d040c078040000c900314078200300c0407034100a180c030481028484900199115180c0c4004104203846d60450014280da01c03001c00c00201c0d00a001e02100c84d03082e14001c880c0d0003a041400355140000c1c0c3c107100103110500301e00400080c2d4411400001040a42c490b2000504494602103582d141054005007140d0004224a140600c2d1603032000141c0c9810b030707030341e8159010300d440080c0321800d908161046182d80d21895070f0090030101000304100c200c0c1100c1c007a2021200002000480711380c1c01c00018082100e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 557775062 1250 557773812 557773817
    0xd1803090806060901230619020f191502030718170c010206010b0f03180f1b060304030f0302030a0e070f0503120307231603091a070b040b061903050d020d03020406 72
    0x6d40c8a40900040c04a1b800f41d00d00620103072800306100104445031001010a10260b000000c086040610070f0098041c6000502c488403040c43d01a48d5004407500b445000034a00ca50200008000c24081c40c810b4590075482110004030a82d1064007000700203019030903030b40314001c2e418080025400080d101d0b060b1014060182d081c2000d18400700d40e20b400c01004103200c0070b41100300340242e41041c01450351012400d8050031034644100035010705101c00c0c8400300d0089404104100c08260300881071981c00813645800343c0d03651210b800030030242c4559100f06043c1d001b840300014400c140e64040038121182034007a100059040c40401d007103404200c0d44400420b602d4020a0b480b10800c1c0031100301c101d070b410401d80c02c01c5504c03004900032101d444400c5004c1546104244500900540200b2142c49807080c40c0d4035112144e40c0c1e4400c143c0001d400140b0b00500000862980c0c4c0d0342005001950301c82211103240c0e103036030341401942c0740c05001214015010b10007030b003038501e4842d0088406682194 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 557776312 1250 557775062 557775089
    0x90b0a0306050c1201030b0a0c1d010f030e0d0509040c0f0c080702180a150f0506070201050d0b03010203070203190e061b1c0e01030506040b150d1803090806060901 72
    0x10785901001c2d040c018007a5018540801407522a60808454140038600070390404d01a403501d48803a4003140c070301c0750207041030141000d200c8071002100c84054020290078a0084031001a107241038010b0400d608556059004950151112a80c480050040d44a00711070501656514050070380301c1f014020b0721000002c1c803000032100480c1c030800084c46a24805000410030b28502c01400c14a0b84040d0751440240341c858003032444035420051b030580a0403580a8402d030881c90301000584610408600a06018001c10208a400c200d54001c10840c03034080e009543c0c0745409a002516030b84540783e0084046241c419181d0203501c240e01080308041c0107005517150001d02565070b4291038131407646c6040ba00ca0390366648040c400000040700b9010458590381c0c10040044005030a803030008200c6400303946420289440c0b603845080421002c100001030a640f8240900783c503000d440e480b1030104503a40d100079400c00f05640503150f40d04445008054401a4485078100700e03100c82c0a11a200b40348464 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 557777562 1250 557776312 557776319
    0x405040807020607030228030f17060d0c03080a020d080109290409060c0f09090e0709110c0706090e010e070c02190f03062a021c091d10090b0a 63
    0x3c020310079140a80100d4800e0340c04a401b109035a1022602c2801c0c4c1d0018084a4040580000d2080400000c03401c1184035454403a02c1800401070003403c0b68401d9500503041f030144820681c048016682051070360366150111240a03503149c01d80c2172141d00003004100001a020154455160b1626a15000482c03000c6032000020b00c26603548403107a03006136644002c000040c0144100321243c406502d07024080d207058980640541c42550200e01010700300b1b19807a0540f40086100c00540360f1010300054004c1c820301c010049405100600078062050207404070301150481c100e9800c440c6000341045081e0388511005400c1d04058882a011646d022404001440c3c502c501413144100885504507980d43c4000c2c0304013090643c3d0003a103210b56a210095401080d4040c00d41140384102084c000c0301c20100070082d41d070449014186030ba0041e80c5140305c1c0a0f881f580401c0c00030202d102c4c20031601e0a030000001e0140310160340070364181d0400f0000048103102c5006028030100010007030381c0150300c1c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 557778812 1250 557777562 557777569
    0x30d0c03021b0a050d020d1407030201140901090606090c0509041a0d062403120c1704150e0a050d0b06030a140304170c060315040e031602010e040504080702 69
    0x1001148009040e0240140075411400c0c0c2c02403041d2000040c010903103d125400c06600301801071001000b19003020501b9074070180c01038a40c1190240016455503030744a41c0c01c6c100c4c0108000d001038002031074050184480100705400c03c030f6805001d103504004441d079959207481211608401c82c004118140400c22480c545a8483d4400c0c2d22000c410200d00c2d400a00021030090002c0801c640a40e51070342c0052a610400320000100f407554030388007a03107600f1742c1c40d5800c2100c40421180d041090314440c41c4104003903640700c1c21040000c0040b0985458443c0d280c09401500f128229000501e00240c02e25140f40181c152401c54602800380c001407207582d02c3d141e070201401007149405201b03044680d03001410f108002d80c040300c8007c01550300c0b0b900344444d0607003c00f41080080081d42c459038035401d4595419088a8108282c2212000c4544108010402a10b814000328040380000b18516404082405090840320310036a10040a840e90208220880754240e50143c500c9505000c000e00605 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 557780062 1250 557778812 557778821
    0x72105040e0118090606151d010c15060905040804180c0f050d020c070308090310092001111f1103040f0f03050f04080106321903150b0a0f08030d 64
    0x1068013085440054035401c1c140d82c940d80c06450283c081004040c8907035803001610380100452002e800c50031100d48002400300c094410042c1043c20b0b5040c04100d52241640900010312110406100c0c92a080c200381c07400e40c00074450940004039a24001081108621600c4503004040d1140715000000c800200c60b01d404c824104440c2a80c00c00503014842801c001d440c2c019440f544a407a80c444041c0107160419465080c003c0215080406082c00242c3c804204a8880520032840c14141d0350345004a461110b85001c03000180520310124408100d4860308903030320080c42c6e00510054806040d0850750740b20882c1e01a1030502c40e42c00300c0700041c1440d02da81041d203000b407801c0c0381421319000815a42d43d009a001e1011a0740d00c1c20f0410910300040c81c0103c20205808402032114040521040c41c0c800c030200030792103590082141c4a2820020091001840d000188040d88564240a010047c051694007a1050401001c009094110b407940f40040e11481c1c400355052091803c0d11101a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 557781312 1250 557780062 557780099
    0x30606210a1a060a060804030207050d0f0b1302010f09080709020f04050a1503050109060e3408040b15180a0902060d090221070501110109050102072105040e01 70
    0x80c011078030810041201000060740001e449070340748440342418410014800103a0f8440030138810002d08010210360082200c00840e141a507003050b40b1102490000c00b00c065042000748403440503028403807e07004290f64031600c0c40c402e894140b130405d408202a43c3c180f10381d1150701415400301806100440c144c2d0040c01480245112039030529855100043c05a00c494200000384034031030355140e403400c1d4507014560040c8040e001c104070302814101706c1d4040f044014840c501c80511000462021140b601040c800c20030780c5109074940101c0c0500c0101904400c0e20255101201c0c07601040300130000e0411145440703001420000355034010140c5149440703005145c5d2500d65510390030726002da01c40c07038018040c00c4c4e01400002a01d0b081d910402c0484c054880088000d107800b5210f41ca00008002004030950383c003424190005040f440b04a8090084060014071030750001c1040401c00441c0c260500c8120038105900121041d96402112381e405948a00b80c41c40600c000100414944100442c802 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 557782562 1250 557781312 557781379
    0x80906090a020d0c170f121c020a0c200301050901020a0f0f090302060d0905010e0604020319050a170304120201020a021b030f1608071e05040b01050d090b0402040506030606 76
    0x212552030217858405405070f084c10031542c0040400c86a03090b000d0000c000e000405074011404d00704c110310b5041c2c001d10003240d1554840d900140c1101458002d40d11038090551202c018203071054503940b051214039410f40403030300035030920011605010b418001e40340300405a6981c0329001c00e481c0c00458012065142060502581c01808005612100c006248014036207402003810324143c40c040c0c1c2161040b07912580d26410400c00e04c001607802003200e8a400045504581c13200445040190a0403000e0100070041c0030302400c404a00400e2001951280e4000e1002c11042000700030142e0a030320519520310010f0308800f42d503a581c1300141e01c80802c0310201604807038040d00100d518600e050356914005001e030a83c641c0801c03500783c1c104440c0c8060507540703204440292160140643c0c981c45800391611550300c42421301c00d50391181c025035910408100091240c00c0190804141e248019103083e401282400d00285050900007034460050802803c1c19080e0044d14444503240016100508ca2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 557783812 1250 557782562 557782583
    0xd02030613060312080708040203060c0309120c0c030708060c0304020405070e0d0c0312020d0527060f07030206070e0907230c060115090803031612020a05030403080906090a020d 78
    0x14442810300c1610055031240d00c5041040d204c240c2c0180c01c01e03038000e100b0810002c000c010003005803400b141d500d4001800c8000c0300c0d201e4503070740c60660030a05080c223031021007900171a00302d1035010300081c2014420b40940c00c0d50100c946a00b089901c81c40b04499000c04180c00f0000b00d4010f0030603030302060344280c441c03411540d4050010001419060824016200384004c040c0c00e10034018030009000c080c8070307a070000b410102c41d02d0b44054020301920920601c0c0c1190b851554000d0b085032249a10b1403074005040c00e80c0c5680003c61451035030400390303081c1c00620500c8001000d41e402180310009510005203050029900c41408030b48000256035034468072090306801070000d41c1c41d42e003d000a075407060081c04156051844001c035014200f001c44040185895080003140030110840e60442201d0715020540c5c49488020303540000c2a00c540f459181c030024402c0c165960107000b0358000d6101755100c4030f550300c900c0705142c1e8401301581c01d005a60131002d8140010b01e1324000741541c0c80e209001410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 557785062 1250 557783812 557783839
    0x71407020414040c0b03070f030207140304060906030612031b111207050906030c0105030732040503010f14010b0a03060306050901021b0706021f0e01050a020c0d140d020306 76
    0x1c09441408001d815824004024081000501382c10325014140070f0100078158074100e14001d01c04209460702405060b03002400030181710072203d80341d403400300940459036070385e5443c90010043c80380d81c4548000207182c03550200720a1180f01541100541507a540802d039501410340e10140180c06004880010803042500c0c4641c40340e004034030702c1440c0440641603543c50001070045e03030007004000314401c0c0c01c81e0110701c0c02070380c11070103407a040806454011165404049008002c200030800000700f072440625249001e09148001c1069400a500a0112008030a0307080140d030046c0140b40380c07074604580140b00c1c46d4100e0001e82041f880350b15010890301c0d9280c035140d0403540c1c103844040d00f69400054090780381d000031041d5010b00703080800a010091600000a4403455600a070a81d03102d0014514a55061160804001030003000000c0265050403100280258800c6000020600900c0c00f54400d203401115a2900c101216500c249403440310300c0844003d510062406a21003105500c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 557786312 1250 557785062 557785069
    0xc0b041d0f04121103091306180209060d0e07081213080a02030a06050a0f020409022208120d0b0618130c0905091b0f040302011e05160201051b0715020f0607140702 72
    0x2400300c1f40560030700244107820b00e401c0c0d0a56614641c01d0189090040100d5600fa441c0e88040714000103c10400041d00c000048656003070040e80c2e440040c052051400045400c00014010103c944401c1d0a801d0302541d07903a0748c60346845903020060341c55003282c0d18110210f2001c0d0011a448003ca450005041450086000c2281c1054016242c0c055003c104040780c0c94071210715850045900d81040c00803803034542d14540c0c544508004036101400861164800e40403604183c280f400300506941d00d41c0c400700402071849030140345c1c0e00e22841d03030b805220882801170703c42c118500c00c1c0c50f661105c0b2035040c8001d01c203950101601c14180160382041e0a80b8802e50700f0042e200c0402080c4c00036a84602e14000141403060108131040707102c0155054008040d0041e0071107441c110103c2481002040038001a5054018808507090394002c001140b0030440d40400c1e80402d54004424605030200f64460490740c541103c40445055070042012a0420740540d040e0703480c02d0000b5a002d4a0490540e010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 557787562 1250 557786312 557786329
    0x1a03030d02070510020f160206070b0108010516050901021e16060f030b01030b09160e0a08030d0f06030b1f031a010303020d020105040b070c0c0b041d0f0412110309 72
    0xc14440794007103090000c108003400003404d500d134524070540c00c1030041c42507091684600c003000c01c4400b5248020070115280d40c001c5d6400d01f40c10483d4280c43d07684d98402c1134060f000460742e111412110390780e201d044a02440c00d40c2c0301008103900a10200000121070350525a01c00003014692141c07160b04640c05241c510310340e019080d19554182000e04656020f0269410701cfc2100f4145418801c10b410540c40303903602540d100303080c51100900c29200f00002c0d60b80580103860340e500812059804221080008020400c1ca0003050041140c07848000c40c00301110f09901000b01400f4900700414840c0120411440032012588541c000082cad9035500c0200400c112001071f010411803034010024550144006159404580000e02080c6041e42e0761081030075008003180c1c1400207544001003072020500c11080540200706480381c0d25900c0d0541000000742118400f44010a4000010307289072404a82c54060340e40000113032096400b00340280e8648903a022111310390702c800d00400710039039101100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 557788812 1250 557787562 557787577
    0x3033614060c0d0509150306130b01030e0109080a120506060412140703030801051008100501080705040503010f0515030a0b130204181515182f040f170606041a0303 72
    0x102d65585c0c8015005100158060a142c6d010702e02d000c1c0104800c070b4403000528000d11601c1000060101c411000503001022034241c0c546030382d0b213400e034020108100c180c0201541c00598898010410424400c8000d481044904942010050008001c49103c00300c601070074034480c220640e60700c2201c0c01402d2070070406504c19000180c16100400c00e505021075004140317201407410780b5070343c87c1291441d4000d10307071840350504005130b010000307032154440c1c001e48010f480020003d008400010f5038044c0500f5065034924400022440b41c8022031400040010340144c1c0700c10000602c0e50340345074052804081c008266002034849848012807000c003082e40030814071035013603280c0b85481c1904800449010b48807042d40c1c00d21401b010300c40d0b100e03100403c45215801c1c42d00495400000c0c002c1544408000a401329541080e20f01600b130b851205000d04150345120754512107446d5125000ca21040100038210a541c00100101e04d990500c0e07000b4002c0b541c070b44400303c407896010f04003103840d41d44142c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 557790062 1250 557788812 557788817
    0x4030f080a0e010e0f010f121e0f14010311130504050303040302250e090109060c110c0405010509011221020c040501080a2114030103033614060c0d 65
    0x740340700070190041a006100082841d100e455039000e04041603444c0441080075040c4018582c0c16480c040c4a1440150204e040c1c6a06200c0e201c00e240003440d0100785d200c468a1002e04001d8444903450a0348249038001e20051510070f043c0e440d60f200d075511801640142504074100041e08241c4c10018001c66009a200e4401035569140c0703404c0c0241418058002d4004401ca580e5004d000c0600c0b6402c20070035100c103829101d1094440d100c605004210044000b0042410614805001d0790400407a001181d000000d90707818034910340c2000110b440034003a00d0740c400350104c01404198084e1a52428442c130031510a81080c1d2172102c507110301d002560101005911008040303030703942040e004160040040900600342c1c440147e80f0f003014000c0c45540951100100e031507540c28a84968104d0503101c42a00710107540c1e50b100d0078002d14115410030401c00f40140389140348107011408000d10f0040c03141210b2002843d051107104d14980888485c901d0340103030700f808034200154062080503e245401d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 557791312 1250 557790062 557790067
    0x50102041424030601030c030912081603050421020a05010e010209040609091709010215070f0f050307021f020f1b0c06040b1c060e1e0a2702010504030f08 68
    0x1000200b20b038640b10200450554009590000b00c1041500c0c3c004209080100c0d52250480d4200d00401d0030030b5025007104844003600192903048003138075000e02d84041600c180e03403104460540c15902d0964004141c3e5443c1c5441d078045001502c1c022402e62610f10644241218a448140c2910300120800361203950000e01d5a1142c5854459980284802c0006101250490700d50303a02400c040700c43d20821000000c1e02906a80c400e0110101741d403000c4910000741c0c1807d440050074007800906410100320b10343d45210300680200d0642e07110751490b0303000b400502100e030341d540b080d810042d0003504100d4003403105102101e0070201a22079555414040c00c41c590b00c1c102d18a14080c4800925401800d0801c014072984034148100c1301c1c5001c28040c030041c00d00c644602c24004100030b6105020b504107020a1010703101d85d110780012807032240d003140c0500b03031610101a011500411101c0c08d0012040c8004440340305407440b04401e01d40141006410541d503078541c42079048000e4000c40d04803800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 557792562 1250 557791312 557791349
    0x30a1104180f0b030f03180a050a08060402090705070f030e0102160e09070902073f0c020301060f0b120907170703031b030e040b030c060a0e0109141008070c05010204 73
    0x328882c8000e0b500f4200c004107041102c00300b116440f17204011410b9810702103440190216206d106500004001c0601000c0c18230341d460040070f80300d00c42900d0403031260540c03a01268840348540c003501d44490f041a80301c0400205030707600b5110f005080c025a4190701400c010b00c40c02d241c900d41701030001d00003007015804d85c1c81c12892150410340c0503000194564814403d0307a020035004100000c40080030700345031400340080303a1080da80e10248407403101303c1010030f00011082a80810075440d6640700381c000b4411241c990a4244180481e0301800c451028144040c1200e145151040d03500107803000300361203425889580e81c40c501882002c408840f9800070b0740400400d40c0c40000414245800c03c081503010071245d50040141000300710072031107162144440c11855505201e04a010007004210584d02d00d030140c805040d004c0c4840c1020b010905d21440002e4810262800603124200284815400c10010b5000e40341c07883c2c041c201900704a034070140d850005009100810150444401c120b074003402 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 557793812 1250 557792562 557792591
    0x306060b0f0f030a14011e080f0618070902070825030e040906021213050f0102030919030e04291e1c320c03070e07020c1801030b09060903030a110418 66
    0x1c0d1988800915800880140e66401c4041150382c0c20be030009252000e83ea0740d03a49000d103000d02e203801003605540700045810802a4190003042e61a0710140f103141f02c20552005c0c0c4a000f403c41c0c0c00a004152188180c0ca40e03490298041181141b00740750050070168801d4a410f401c20040300d048808144220481080c00401c004100700c0b807a040000354030b18507207a0750058582d4600e00325680c904810040d1801010301900441220410142040180e407003050fa15021700c40c01108a01007004c03090341e61070100e0400c4140350017501e14070340c02141026091000d000101c0001d907101070340c0c1000c2002303d90011702c15915550050590340064681102d0b00d00201101140c641ca030364a031035024020350010b940700400c001c81240c4064010b07104075035400006a0812a180c07501c02d60081c00b0119182c1d021010900b42c6d8141d03401400405103941d01d0f50b80040d0303540c90503079010409600070710000fa010405500f000c070301401420401c40c1000d9460034181c04030100c800d079164140c1d446807840c000541 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 557795062 1250 557793812 557793869
    0xa050403030e16052101020d091101030603020105030f04060615111509060f0c0f070312050703180809040f0203041406060a050d15060b040b040306060b0f0f030a1401 73
    0x501002414508040c403058001528040c8500d41c040e03040c8092800340c2e03203456410170316070300a19070080d0743e103420150001c4028003000204a5011481205403040c2d948240305007000e4942c1038503100c0c519111100804201d8200070812541662640000b140c0e02c44203011b079044803582a111203000703101c1c0d502c900741046450300480e5240c0032203170300300407609034005040e82d0440f4071402008115142d03000d01c0e07000744c407450418510300c190000d0718a0805a11880b040d80101580300200880d80b01c2010440036164006c0311001d0b00858100c0c2c80d000319191000510a028000300001307100d50030340c061642a6042110306903100c0f100b0b251003081c2da08091101c65807141007100c0d03250646050100084100b42c0e0b40c24007030302400340d0602d89501d00c00c0d0b661011001c1c120200c11145c80300d0f074a8560a2141d4424081128454109900000d400140106581038000c40c0c1c090340341000d868a0070101540c0005180d58035141c1c44641d40580c281c50007040c1d074003a100c0d89000000e16212a03007104c8190303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 557796312 1250 557795062 557795081
    0x2190e090109030c02060c0a0b18071502032b2c07030b1603110403050304061d0d0f2307050a0b0c070614120115121518090b0a05040303 60
    0x740d0605241e400040d078803101450809a044a02903160348a000002d4500038540000a0201d210941441600c80b141200f104144004208980500d5280c412007031a0800030800c650159006209e88041d5001c071134403a00d0042d4603d04000710510418401506444411030039080d06030300104419000094404d440040c3c0a99400801c3c24a141d6943c40c03a040100a00701c1d5407005003032019041c06840794208213009604a10944e49030b6489003006502c0e42d1040c85000007194441e04503940c5031240300380e071060001005021151111240d03e038000007600c554012101618038002510b000c141306040c241c1a903425000030001d460500341030180d0103069400102e440d0310140f0100100b0345d030000340c100030703250700d0b103049110460794906a40513402902c4611007003886410021405040c103ea544070a811250345014030081010044403c4403c0e10031a1150701da2825000c1c00301080160030303074150a071070307402c00100a00c09032074520b0712410a83e000c1164076181e00034841455414080c6a505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 557797562 1250 557796312 557796331
    0x17070e10080f010501051c060e060406050109031121011a04110403020901091a090a0207120f050307030b1212030103060b0603090613020105090604030501090317100608060a0302190e 80
    0x650801d500340035800b40052042c94100300001540004580d507402d41c3d1111090110018811507413914904166850203c80881c0102d107840c1c00040c50358030890083c000c40e0b4004040304032000600e400d02039101007040558040007080e0780e084214a03403d1003941c02c407031012921001840340c0d0f40100016507580300c143c11003221080c0420f1001da0f85044520381140c502d1840005d071041244007440289010b404050390150410303041012039a2180c0080410750701c5108101c40302504420f05072244410000c0103400141705200140e541402030780003126500c0d00506200440c00c03038002482c501040070300c0e00030a00d04040700400800110b4056501084004c6403c2400e41c64204003440d0703603c400078000170804001e03202c9041564007910031104240c001400c2c0940d034580340d0a10a001c3c141e0341404800260121080e1a012001000802e0058a65480f00004c1d03919014080750b200b84060001035209000307410020060792158065071314076420341c141148d100d2410381480319412009240c41007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 557798812 1250 557797562 557797577
    0x316020309121e0d050a0c0203070302060f0c07051804140f121803010c2705131e0e0c011d030a12140406020304031529031006050f09060117070e10 65
    0x1100740d00704054506e41103583c5050180901d8078000280391248907840039401020010303585056804042c02084481000c0d02100d0581d84e44800348500e03000050040c00700c02c042880400c001600243c1c0c03445e810511141204c00c0c50b18101d03051400c2100414010842c20070008a06410010552001d41c50b05405c80c02045000c01200c006002070741281e11204084a5800a50840000c0240044050180500042d0382a880e60840400410419802c1c40118580301900480c02c04107000710042c502004024003107800b4014015680c0c0d02440340b81402d0b800c1d400000242c075407000c211010095028100c40031414003c5600030f0284804403d1405451800f00804d101d455000011101140e0703021180c01c015030100380c11440145400c0b981462a040242403d28621503e00010010404100c1c1503d400d00c2080007041c081358500d10035140c0000310103038020418940242d00e02d512540604051004019003000d039000c40004540050101e10011400c91030f608002d900300160816a080282 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 557800062 1250 557798812 557798833
    0x22091505010201110f13080f010b0114090a0504020a0306030b0408030f0f0c0703140d0f09020f0a050a050f0d0210260f0a0507020f1002030a050c0f0316020309121e 72
    0x307004d8801d800d07111908080014440c0003080000c0c2e801c000808200c0142d8a03100d00c4161410b010300b17104881c0e10300190f00b00180001c150035140c05c0303074184100100409041303840c3c28140300203500000096402e1603a01e079000008500c041754054030940c401c1050303030340d249460102f0200300e00f001f80079610b034807003000308100f81c3d40240300449840b00d4041c213194203414260413100c2e00600c2015201d0140c941081844046802c0030b42203503185510840702c0311500140b06090000000c42442110752201c1c407507400704000e0806e0070009101401c05041d82c071f00d12080e41c0201d41c80d160500700c02c1d000240030454402580d0981200f25038805074040090000d1b04140200201130040541320580095561020485c1c0ca40208a50f01c100d14a0700180d40008115408900003904101e03107221340304d8201000110340303212610403034607454003d805d07581c02c2d0723100d001c4c0307100741041d048440030305502c02007200603216543e042894050202941c004c0c0500d408841a1500c0c5659085003201c09512550009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 557801312 1250 557800062 557800091
    0x1807080a15090206040905090d0503090d0311040306140405010e010c17060d0c080c0901050a050108070c0c0b12180105070e011407080f0316020c10030222091505010201 74
    0x5050441d084560302a2079003969110700c000308840d5000a60010000800041c2100c154008601c41c1d00d40005942110305840000d8034070788801c58528415801c801d03840042d00e4041c1c1e1003280311100c0d00d03010364103003034032a40e4038002c0f2594101c01002d40700c0c41c4010402001000d02801c404104c0380b5009019240c4400d4000d000114410030401d5402d02e4080018030030b84501c0c04611a00782c001110402c0c16542e500020b490b084840a41406560703040008034560500603244011140c041e5036134806590b50300003c072400c0b03900350b80468130740100c4a030010701d0b409000040c1540c0001c41c600143c40d424180c5142c0d060381d04800c40355000c0c4e41040d0400240079000340b0004e503454001e003041c0800340c1c00d8040801e5a0300c100c4a00600a940c00b00d40c82486101c0708000d58070550203002418220321800000360307036032421805203c0e403106083c0c7d0b044000d10b209401420352031b210441940d5294075661301d41e60000e2429008880290381c0c5c3c0241c45040800380a08078000c000a000800100c1e042d01a903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 557802562 1250 557801312 557801323
    0x7050f0d14030603030712050c0c0604230a032001030c031a040f09080d0501060f0c12141c09060605040e030f21090321060303090d0302010f060b03180708 68
    0x60300e4407903004000111152024400c41303021550291031121900d03507008003c0c1071500500c82d080c5140c843c04056001c1414580c1c11101566042c08000c140d00300c1c03811303d40c07180e030010010040e00000b0303e120020000d03114560000507140f4951106121181080c00102150000c40d44001050300340754020000c100aa030700c020f034198060300e000caa480c801010041c0508884003000300703241c400041d0121101074691106060782d10542c2c42c4008032040340c03c1211444d40006010340b4101c000f0002d400d80c68050040c40501503c01c1c1b2000e400d10340c003c01e4401d241e41c00240d6008880c0d8991903a8400c00044d4445c0c0c06c00391000315010420f2001c20f41d034660b941e0140101202c0e2803080010400700c06285040090204030b4030107228441450b18100d40e940302c1c1c2001400c1482000802200ca4150b01c18113000c621880000d00158108004c003401c1000c441d406100a400b9556a0150603c1502d86070245101400c1c20364009640c0e0b050a00c200b20038140c51950803070780c81e0040e61050102080100340d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 557803812 1250 557802562 557802587
    0x61505030f0604020301140d240e070509061e0f1e040c031a010c06020904020a0507060510050f090a2406020c09011401050d1e09020102060f070806060d0f09030507050f0d 75
    0x80062040c1c1031427500612025400700d500030381203403c0d40802160b00181d004141e58400c4003007a2503003140d5410074000b965a0030750341c0300c0d880b0f40e0f2400b4103402449801007510000900501100c0c01c0381c200300100d25211003d8601c0d280311060342c403031f81c060750074607000e42000021a403504000007481c41460281000e20041c415040004498803034040c07040c01e805442680034000c008641d00c1c1c0c3c002e0005009644201e4040300c490b810840042c3c01c05c40c5211451048544c00b5088100c0344d114041048008503000303040e8442203903103000c298174000020341c3c0c00d01d4202903568024195810940064a044501901144621100001800700501982c51948008804e08005441c1c0316043c0d0002c01030900d0b9105541d0030046803455500404854000410980c000e07026248503884d0802d84e510100c208450300c20101c0c501e4401709506090110080080c0c03042c21b500010564081001c00040e101d10b0101580012030116149060010901401620b407000600800300e02d5500c100140184d2001d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 557805062 1250 557803812 557803819
    0x3252007050a06050a02100f05043305060105120702010b01140705030901030e0f0604030f0801050301020901140d0204030c0810110309071a0418140105010c0510090303061505030f060402030114 85
    0x1011495170b80204104180c4500760402413010700000d055042c02084221015285e0007141c1820412a00088041c55401030810007102c5610701480700400c05040b000d42034504015040260701e1807610f05850490003500303503030300100b600901480010a014403008201c0c407005000c000880000e0400070072103400d45000c3c00c0c0415100c40c048030f050b00308007904d500041d03d400343c101008201680244803068640140e01e8121361072740c031003090500f00d00410340d82c0da0210b160121035040d1200071401418208422442c00741c41c01d40c413036a58020300500f0380e00812444d030240108242d00c9141e40a020800080b4104040c00c610f41400400d45c0d50015110b0b5142040700018010540f0600d0b40454020304004a42542000c080a5001c001000700075120860130003800004a01c0303620038844a2511a0080001c0c00d001083c98030340030050500c08011414540d88900000c4e038803c6820b0403607081100303920380544034a030001d401d18021900400442c0b06502c1040140900a40b002e2180803480d07054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 557806312 1250 557805062 557805067
    0x80c011205090f030a0906120204080c011d100c170a1d040212010b0c0c01020d0c060b040e010e0604030810150507150518210f03252007050a0605 64
    0x1444070b0b4141648205284281d000002d2503826860f048441e8104a40b4140d40d26002901307010019000c9008902820520380c12610070075007d50b202e160b01c4002d07102d8026020748441c004c00c4c00070306010303440e050b03a0000c030340f0700201a01400481000350440ca07501c1203606103440000040100011648004124440700a902c0b0f1141901c407603050303402d04e5003001c80c0c10743c0950310307150081000c1e041240920407602c144a4000c00343d510104070b0a0710001580c440494405095482c040542400241d071904a503503011075602c400c0c0d090040031000d66103580075081c03608250070024041140100b4103828501c0b0800208044402c020400700e143c00c0030300d0301c1038488040746001e2000e6110705014501c0d282c180310a000c12611b003100701c40d0005582a044940c03a88411581c030080060342c0002541010f4180302207840d0502007401540d01c4070740520165100f200a000c001102034107a21070740005540383c425145001800401d2405041d0f200c8010304050386010002070032003040d4000c5000b0428003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 557807562 1250 557806312 557806321
    0x503030402090c090409140f1605100c080a03060501080a0b010203040303050313052d0c0d06150f1e330311040b0712180608150d110a080c011205 64
    0x910b00b504e8004000030402d112120960510074090403042c0e126141c10300480d07045c40504070000450000c442c1401e41c012403034138a0070382008013048500c02142c040c0181125000e000401c0e11303004000d0224103460000b04c2a061000061203004010940d0743e80e40d00c2c01901084030380c1c000042c0c90480e0341c9807401c1903036036950001c032a001400c2000001c0c4584034041ca001384807485842085c652103880d44460040c461781095959407200f100760070941041107410508007040301504110000c4108454400f2210390f00c017491002c141c22030340045002900400380200c0c281a20480038002c117405201206141060b261814041400680c1030104c091070040200805010750882c01084200d01030342900d03140d440340380006a620070b840889628808640c86880240285400030036416007600c00d8030f406081c540161056a00541103640300c599946507201595140407501c2a543d20030912050114105400d0089107010303904645001c0c1c00901c3e04d180c4c584d91100001c040184011004142e80d200c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 557808812 1250 557807562 557807581
    0x30506041106160b180a0201081503240a060b0c0c0d11031e1501080312070201060909050d030501060203040506120a02120c1b030403020907030c0207170d120603050303040209 77
    0x2140c2c04100109031008015050010481d44140b003040d1043c550005c1d040040455500c030700c005d141c000d001c03904030700c00300342d00c0340700c0d0081c000b00800064100c8084001c0c90311841025a03071000d00e28000b02c425400c100403188540600070040c00c049410901784401d0102154540340e01d040598040c48251083d20140304003920300d854100360103020341d0014004062141081042c4078a402c42038850125840150891440010304a405880145007001c506c01511024041c0c007500d840210364030307950041910f030360611552860703a1084004280001e004100901501c2c0305a0240c0159081230000b046035032100c00032990b44a10b43e03846201c940d40c60781c1c4070311300034002e10303200303800d80e044207406c00542130740600007412002d007008407003510348031050401641c0c0d11560000a41242003d00421280d6009402c130022605850065844a6480d80c4031540c01000d1490242c58075409041d0700c800d0706070000074800c08034244401c140903041c04c644850303980340300103800240140340c604000340c400c88 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 557810062 1250 557808812 557808817
    0xd0b090c09241f02010f1503080913150b030108160602070b0c071203090e0f01030f1e14100617150601120e010219020c090f06011809140c04030506041106 68
    0x8501000c440e0f0418100028020008954100410384ca003c40310f048690448090748112517000c401c044c600350804091020701c0c05541000452540c44458032082d072001c00c0d14010107000031044594507585086c0119161142a0203c100300c0d21140c50180030003076010841c0b000ba90400c429582d90f600d07030005024540b84142d4003400425407104103010825074403134005011074003004803902160b2520a205808044207200003000420b0711100c00c0c00140c2c40700c3c0e09450703a55038507500c040106c0d0389032240180080c144082090342d0300003e46220305408103200304070160100394104040d9010b800c03105903403626845d500007900d044410010b14241e10900202c413000c0c003803000c2480078000c1c038030300d0718042d401c0002c200384569240503048103070b684000382580d12008000d244890945030380e85040078a00010385806d040064010745041d00c43d403e00c00820041258400c001750035400d003040162440005083e400e0000f1080100304041003000540316007154210004000380c440c128006a03451 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 557811312 1250 557810062 557810089
    0x12142d010b0307030c050a050702040f0204080a05100c0306052103040b0a050a080f0c0d200c060411010f080705090406052e050903030d02180d0b090c0924 68
    0x1080000110710303204003002950184035561414400041400c105650314002c8040210000e02d0a020304405860150016151103900110040c42c20761921040303418805250801d990b5644050404070f448629440780c82c041c21464030301004454100000628801090304586481d2000745016500500d001d000302c030002e02c43c8010041e500c210300c420181181c0c116110f6180403540e00400500c0014607003ca61384103070f541010b01440e000a0f40704500c010140f104901e1108100000b000c08082c0c1990700800285214000602952a107450042d4040b030800c00c10604004050318000041900198650303007040c2142885503d814202c0c002c43c0040515602499104c00c1840841c034507840c81803210900350400100e500e1a960b50f91000360b500b88150340485406a000704040c1c3c8203440306501078800e000ba1044004804640c0c00c0c000380c01c05000010a43d0711540c10024040f06003420003001c40320388030903550204540b41250450116003e03181000358080d4001400da50150303195007108003403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 557812562 1250 557811312 557811391
    0x1c05100606112406060a0306050307061205010812120a0902030307120305090109051b04021b011b02010b210a020307080705120705151c0603121214 65
    0x4940d9600740240640084036610580780110b40c021070000000300d01801860350f020704a401c0c41e496010911489511000d407110070540d5945010078140e0301030050350010400d90b0b8401340044404e0000100f03c45060f48161401e5200901440c005200c000130b0750b44080e283e03044520255215000c00018018141000b50b050200144030f00400c800344078107510240c03032960308100941e54040660700f2200c4064029003994841c0c03089880305a01c0d41e104c001c1140c0090300240c24580981d0b1800802c2d05804e06d40c1c40b07181d440d00d215599402070f0368010444600036100900100b811000480e2102040d52164640c200222080703281d030242c00c100c2c5001c40c59003d0203c40400d43d40f0300c10341d51184002d0003045d01c9a07002d0b0514080c40c1000044002c151080100707040b890711020700f000b0078264009244580f03152249002149405820720401d0011400341080c2c8602410003640140900d200e0140003e51a251001002c185101008402e0f4001c80c2240502c8110101c900c03100e00d03d0030701e8040c0343e15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 557813812 1250 557812562 557812571
    0x1b1103070213051b0d0218091b0c0c03061305120a08040615080d0f020115060207090506270906280e12070c0f0605041a0a05070b1e090c1c0510 63
    0x1981441c0d0040c5940251303c421f4048943d02c0c00b0030055103610568010f410404800b100c107c1d0f500052004010181410b41181c6140046c880803e00303104045950b0030360400002da5007014400240590800000489030091404d81540d901800005010340082c14080d80c3e944240341c884c91030741014001d05000d20454020b884200401462a2002100100103500300405000306114150104084d68900d80280129504040a50b001044000d08281d880441d008007400d00240095552400c1c0b170507410644000d03e00a0010361a000700070300031801003440c4029010504d42ca0200803c11050321007070120310504042000e40c50701e100c40e00e00d10b207240000101c10381042940ca482c0e00072905640031503009540c1d10203040d078807809a88103051801c0b8200b1000f040c400007020080c80f40c110103045c020300707180e440d480f00d461510080720b5201051010380c1d13000c840010403013419580950440c004010100890020903141c2030501110303012070708002d030058108101482000c1c0c030500903003000c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 557815062 1250 557813812 557813827
    0x10180c0905040c060305150f0f0907170f01050607260309070e010e0c120c0d0f0605040f0e03190507050a0506010312050306090f0703020d1b1103070213051b 69
    0x100501007550b0844680034100000600e03140a130085600c103110743c0b0754110310180c1890500010014210040b075015145410b50a440d56030100c0e25800746041d651200344070321803d00c450120003005030150303000076a40d00041010381c5e600002c0710203c0e98842e2003440d1510408018150042d00c0c1c1542c500c44400120030807441c400d0029842c4120b4820490040740b99a1f6070180f0851f203a000d5914408045003089401d186130070300080d80e40c0068090315400d00e00310000c5001400c6600c001200005230b516804c04001916040c00340c2030230760070800d200300721701e01c40b402c601d6950b8440e00070840d80a00036444051151401007050b1540107800600303442a190041c500365841d003109020407291001110221040c0038800d200307480c03041c140680482a06c0d140e815a501400c40c0081c004003c040d002c1150b080f0030252406401080e502003c10807000d8410141d01034400079240c0c00104107540305000300400359031502403040d000d081446000540f0b0300e507400034600e000317031140440038404000074060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 557816312 1250 557815062 557815079
    0x507091d10150906030b01140111150114060c0607112109030120180409061410060311030f04020a030b0c130b07081207031d0a0204050106030c0210180c 67
    0x800c900500440742c105254494080d242251414000503200784c0802c001807100000c1c00040b141d020005052040078a41508001032601d10240c9854010711080d8004002c01c0e0755104099034111811500b00c1e0034102007542c03055076102c0c024007050401c600d0140b8018442c10902c040c003820310410b0000107421002c511044c1056201f016803034001d600c1c0c44032040540080814504807074103c03a0300949004030740320804441500c85a04a41d2040c0d4030b08414000400c644030340f0284541f0640310709110315044071600040e500c1940300105041c02c1403800240300000c0412294404c0f45440c0c1030182c4d48482c008558900d116800040c147c1c403640341409250b5204034003500403404086d4882c481c054031001908802c0c001c00c500141950320600907614000004c41000e54000784078030307000405a100d09a119620034205208a206805c80c441c40d00a50400b401494050205820180036408104034001d527101445698901c0c180d5036032001900d8482510201d82d410781e00082405403040d21620304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 557817562 1250 557816312 557816321
    0x1503010806010e01080d030c02031204050607080603162d0e01180204030209060105030a0902060f0a02063919081905010605030c0903030f040305010209011b0507091d10 74
    0x100d9403288034810000548025008801d8182c03103201014116030a10700b0015006840c40d00c4203202540024005002e944a9107110548928003410003801d0a06050201502c5820094420f5000c1d40040b242c0d510318907241755285044074000c80f00032403c10803080740c400c840012240000d80841c0409400907400e09101c0a4074103031ba00c0c205121071500840c07c0380200f28030841c80001d4100c5030190001d072080d07000d00d014540c02400c950010a0005440e4000343c101c0d4005168810b00c032001141420030b541e41040300c1a400540301c0b00b00e0000090b018109685510b0100c8580c580071407146080003181010000e840b1111441066001010441000548010b01c106d0703441103a038450030030000c43c0030424000c0342d04070390458a0313880c038503200c070060b42c2801d80c0b186603956014031040088000c0c0d9020300c4020b00065014000060f202c00107040014801e500e900900c11003190484041c101084000c10100100e458803000062504082003900d080554151703103420700350140106440705000039800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 557818812 1250 557817562 557817569
    0xf1d1002010f0e0307141f111b16120f0206070311061014010302030712110913060302281e080607181a030114030309030303070306080d171311150301 66
    0x200c0648170081e0202598401d81c400080c0c402c1d504003510b114548a00d03510807201016100c008c585400e0b907520214110855405103d111a403000a83d03a1142c0107018070100a0031040c0404c0c10600f0140d00c9080b00c1d036000f140082c0c440ca60000c1c1000826010700c403c041d05003101300643da11443c0508010702d480e5054880c6403904003280020251540c480c3c030840303103d005075840720800e0f5604442508003d051051303200c2402182000728084070b0741d4400709a1600c28078940081512411071042c0b1801540c01c0501c2160481500131440310240c80c04107100990b43c0c07201d000c580c4880881c80c03107071903203030594020720301750003a08140319070f036940240a1601000c24180c01480590b995001c1c00c409a10300004800e02e03481031005000107403000710325046455008003100d0604940c1d000183c03e69000740d6180c1d02203555400d0800000c5c808ac0010914000a070814a4030380030070402c403002e0724400034603a094007018038041c60204440010911584c03100a040030811100241064010703600030302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 557820062 1250 557818812 557818823
    0x20901020709140a2403061a0301091713031a041101051608030405100c0906020d02030403080427060605071e081c021215010f1d1002010f0e0307 64
    0x42000c50321003041c0c00b88001003944a0703100f600c00c1d0303207500050f8010104024920842240141607401e0108030070107460155000d86000510740d14030003543c040d00c40001e01000d0090b418031003101c0c04200480307004103603d014100322550314070000811196011860f04002c1802d10043c8103080d9000c00c0c42c20304c5100f039221f0400c40352401c021000640e083d001789000c050071102488034510001c7c001c0e001948e041031080003252000c481110303007002130f2150515880001030350940100901c941c101b0001c6aa1042800903614160a544900c007440c03145000300d0780114810640b074040b10098441c0368046a883d48420015151a00303401841ea500200054401c00c0e500c440450390141281182001107900c000310300d00d2f001d00810010301510071807640c0e5030300a50a0107010001d500c0c0c03c031483d104140785450102d00d05840d40004d01880341500b42d00c42001400d520880700b04110144484000d6800c03240d0300c0400e6541201203025140c40c0b000c1121003400c0010081d42404000302030100349200d803 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 557821312 1250 557820062 557820073
    0x90a080c12040f0e060f09011401050702041d06010b13150e0301050a0203100506090d0f0201020a12080f0a0c0801050105090604051801091b020303060d0f021002100507110c06030915010902090102 86
    0x5c0200003100191204013540b02c030740c040c01002300c003000c80584a034212040c101541441c01da40c000501b140c5000812400580300d5004102c4141c000b4454903015184450107141031a2404904100050950040092a0f08080103403011580512006140108000d0082c405480c0051448000c1c1d0020358850f4a084140800803d803850168181d031076189001d80440d000002544901120019104003641940103074000c50300070441043e600869074149444080503420b00300c2d451400b01340c00902c1040c0c0c40d0300d004c201e15486a4480020390444000341b03130903038440e51000700240441c42581c3c0440c2c1c0c0034091100682c6a81c0e070003c1401d040f9803901c1802c01c4480748071100d000d1072300020781401c80140c1003000002c156207010031b20b0b0210075000310b8414201ca03ca5070301003000d044120b4048009a8000e00c118400d490f82030103819440320061900380240781107149a0740e40e40d0a00500e940c4142008000218038140800a41c0c00401d0110684081541d44030304140c000c0d0700043c029401400346 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 557822562 1250 557821312 557821321
    0x302090a0c02011107260f070309030203060c0a17060102030d060906170105010501020d050d06030c0b0c01060f0617150603190c0512151305090106050414090a080c12040f0e 76
    0x130304040d6004a604410600c00d03021604901c1c10302190021103411441000344000d104d81e00c41e0601511416110f520740413040c81c254010185406401031103181c540300108040404d1560140350085205c1d110050100e86031150700040c3d086019007046004840d140142c00aa00d660940000084481160314001c100b10f040c0400380c2038800034024039000da0700445003044880e105d00f005181c2a0400040014226142d641b8901002c805602081562001141c1200702c001300384501002058a040d40f58402860040054071007001c10303640110340c2d50f1480010f0f03150140442000394104000704025036910b4800440d000c42c40c03000788100085d500e06040b540180e809041100c001031040b01e000310f5550703621680d00b011440000c0301d1300c5d00184027403050780e1054021b0040c0750043c00c10000105240c1e041c00d045c4030031500c12894164840200e8001e200d40101e0210b03c50101c00d82011020382e0701e8418000d4203103810322051240c0240c01d07001400141c58001d0320400c4096441c001e030004129240d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 557823812 1250 557822562 557822591
    0xb06030615011202130f06180312030225080a20060411030a02220c080c030a0c1407121103070c051c060e0606010f0807080f07090302090a0c0201 64
    0x1007198056031016070100184010340c01215000e032100c004400140c80c06000010401080b41e0300e92000406a04002041c00b0b410703001402030398900f0005155000252450f190028440b0050001348145540083c84403421410002c0100100d20700d00b8100e20600c5241c0b900710419801185c1d000700141450031100c1504003118114a4001c090a0050070152200c1d110040500c81d08194941d0601c03c601e10000182c0380c050300514120410004801c41443e070803219825a42684080010040c42c20200154180380b4401d40f0340002d498680000c01d02000c0c403080e91a600200c04155101d10045080c000304600304c5104034840308207603542000c0d0781400654a540b4015075600415480d4841c0d030501240c1083c2120300e03605101c2003448088c40345c0e5a1206021502036400d01c00d0b03107401c007004101b8956000a5400740400c003521705000240303020b0700300415050b00600740f0b0700200c0a032404100340e90b10a8031345802541c0c000b41010164100810f00d10006c0640c405440055400d02ca4211440d42 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 557825062 1250 557823812 557823823
    0xf0108010e0c0307030e0d0807020c030d0207120c050901140118240e100e09060f010c06050c1c0b031219030f0e030403080706051b0412030e040f090b0603 68
    0x445545a0304401c0e11042c0d050102504024101e10805596000f01da00103201045402040012a140c0020074106844028145041c400c50f141c040c0e405080103000306640004c4800864084404100d007017a020328011481e07a03182c2c0d010650105c03400b0f00105042622000aa00c01c2c0f400341c82d007070034840080c040080c090386a440341d8621034500030740c014000f24500340b10869410f031a20302010603884030f0700094080c40340d50350301000083e0200f8076001141031001c00180c10181c21585075801000680000340b840c0901480108850303110300215040e11501401d9850401c0c7c882d60440c0c0d0680706803c0403005000c100305980c0b10740b107031341c00c0c0e18440c0c4141400c46030310b000703620041c2c94584c90f08441030707004c0c12049050502039552000302611803481440544047d5104a0809950b0410303402e1803816141c024010700449415041c48c0c0c1c480c2e815504c121008c50b8440c0001c3c5480c28458202075079040051004c0d0380e081428081002c4c0e200d200b6030b200c00b018500c104039040c620b45031b440a055850 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 557826312 1250 557825062 557825069
    0x80105010f050603070309140a032006060105071e081923090d0206040803190306180911090f010f06110c0409080c150f0105030f06010306020a03061a090f010801 71
    0x21200000c18882c90802d58000c2d5070107103243c1801b040019640d61090901800c854051100703412111540c4109544995440307503051a6006411010744080398a0342c885e140500080c0c11311000240c580204502002e240c1210080410a003c4a161606120125503c414a82100c1c402441540700105000d45640c0d240c07400c00c0191000c1030103001d5101c11150b80312046a070303071000a1156000050741d50300c000f04040c107031100c050b588460300700d090403241c0c0303e0400e80c0506140c10301c4000d010700344902c0f03050410103090a02c04030700c140140c14008040b03a050414107130045d03212410401105c3d420705082e4100c9002c1c0d0110300e00aa550501100d060b804054401069002003403e094203280c1900014541c40c003400c8030615003000314000616002409210a0660046d142004440c060000c285401014150094038490340c0002141e40c03a5941400003c080950115190b00314511961011000d0b100180c0c141140040d09416290303541c0200c2540c610480e425554046994031950780103048 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 557827562 1250 557826312 557826329
    0x50a0906020a0c0e090c0a03061406090108030307120f0c0c0209010506090109050603070504120302010c1b0206070b0a0b060a02031312020907030905101d0706031a0f040e0d120608010501 82
    0xf642000000d40c06000003811300c064521400c450b0100b80e0f56550400c400641c030032003000a2128912020404076080113040510540ca060010010035a011040f01d90182c06c40c54220a0400c07450001f2006080c1b08241c94030291818000c444545d0b04460701e41e003403d0088403003124503030740c0d1010064280300380700e045400142c1886080000341485405540c21403081c0c101281050b46450b0002d011041031101680140c2d10348000d040d00680140d074484e292050400d0000619116402044040c0701c0c5180050100d0b03201400a2400c8180b0791006d000600000c10150380c59141030340003035a03900044000310007100c2001c03001a0b52071813440340300c09096012340841c0050b0b40d1400c00344c0052002c000c2c240c0319809064220240b1100700e10484281c02c0c1e505c60a88c100d2101500300905e403031060740142003414940740c440c20703604098002003105e140080328058085849100824058840320194000a00c5950585081c594120201030100801040104001c580c0d0700080c40c2a94800e21078800b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 557828812 1250 557827562 557827583
    0xe15030c0711030309040203100e0901020f1801200a0606050301020304050c0904060906230f04050304050f0f060f0c0f032107030b1003022104211e050a0906020a 71
    0x78000c0060741c90410b800034143c0e8184401513000c201a030740111801d00c04184625400c1c400d14660105280c0c1292400d0021802d00c80755800c0c2e04581d12446015051b4244035914851041c0c2c4030300900c07468404030300290039903041503003e03d5075200403c107811542c143c1407000220f0541414420749102d6074101d0000d211050f040710a01c90036550181003943d051f1303141c82010001c640b10303014081601c42145101000300c0c1140280b61003500d00a0030107013401c41e810007400301241b000402d031800d0b108126541161741003010b0011746a03030380f10005a81c2100d404500f007a100f00715200504003215607501a181c006000400c515240e114054102c1900410f116003039448541181c040c552084007400c0000d4904624000101c03050b000643c158006a0001403030500c40c03021001c200072400c0e90a000b260326052507903800194000203089590310307100410040740003510505114041110811501c3d40c407840c01c1340b0050695010051540c0480d180c508000741780c2e88009925a003035a04040c2d00315 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 557830062 1250 557828812 557828827
    0x120109080a0c150504030c03030c0503191509050c030403020d081015140c06090c06040308120a020f03090d08010609030302062406121009060f330e15030c 68
    0x7220b403103001c04156a00d125564400d00030301642e1080900450094840e040c06684528000301a04c001f446c0c50300c2040f005005211003200b003141322004490035107c011500e0b00515100c940e83d0400c640c400030b0709904040c14004e526800d00c0003140114007940c2520844148140e05035540d850644540c082010058000c101c0382c1840b1640418044243c6803502d43c80c0c07a1028440300c113070000301822225411500900c403541001f000b0b1f5078001c6805070340c46400c0929649400416014050041000f24095030004c4c1e03030b1100540c1201e0341c2a8001d0415078407814541304655450511100100c080341d200c01c004200d090098602104036541540100116607500794031902d000fa15000740d00c00200c0004d02021a035a5890140c44000074100700c902e402c2c90802c081a100c04410350225000314a00101880000101907641c42500d40400c82e00003000c1880130200300003031070010080c4c1c0610012006000141c0e1080b420080c1c0441190b000f225441c07600b5200c4c05603c0b0540384406d201c1010030110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 557831312 1250 557830062 557830067
    0x130b0a0c0b060316080303071106130204050c0403140601090b01020610090b0d06020406020f1e06040b10031a0f06010f021e0a050322090603030f0806060d06060e120109080a 76
    0x140e51041e4050113a03508040c00f010b0401c000401500580c416800100400c00c184c1c3c0c0c4865030110a00302d070343c02009107040180200090f2081000d01a00454644000842180c1e54504680085a002c499000b08070300d003031029a01e6020a005041c162030a154a40c1e80740d40c40080c2c0346000d01091551190f44070b10b00118100102049000a81c00145107030028000c1945072010f40010002600601090740c00b40d0400d0b42040e00381d001074000c5d0040c0e808130080f040b20014000307520a5200512541c00c2d181c48004015180d99a030005003042d084101b64030400d4082265240030342d14210700200c181c0c96020040d03602408110038100103034410032442c4082c0b0002c201d0403801d0a40c040541d00ca02e20f881e1100d41c19944041c25001200b03464064100060840c1c0104078000c01101c0f1701004050700319030700106003201400501d010422894017083c0b4694075001110f2403110b01d208100301d0543d8984001d041c1d540030030801c51091800c2da240e2840440180200c0c05244d500004440c43c250350017805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 557832562 1250 557831312 557831333
    0x3021f020a02070f420801050307050d0506010e060a0b040906060f0302030f071b020604030b010e130804050105030a0b030a031d0406050a120303060509070c20030a111f05130b0a0c 79
    0xc178072a5558804404161401c41c11015903d4026550b544582d60421061501d48050340d4813032030260f1107100c030b508007081c0007161050544181e400054040c1d00d0341070008620787c890b03400009030070360001000503003101c0b5540203c081791600d803074510788010300a07001c1e4200d0200702c0310800c0c4540148002200d481c850300c02c036000112401c42410300c604044d00407692580254204441401980c0018450b01003d6040c081c0c3c08403842d41c41070b0501d02075030368005641c052481041e041c01804404900365549580040040141c0078003180c400c50b6290400038407014814009150344d0120034045075450415000300826a18090002542d8a00d010070013440485451415010165695000b14080e6216075000d0700030110340d0f07140d2016070011306010100c11300d101d84800018a90300c080f2840703031318081a9000c0b07e6401031050f065100c4c2060202c3c004943c240c6c04100072070701e045030700509240c001014209e5944462007800100d51580b503403a0b824810041c80300042495801c040000a004504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 557833812 1250 557832562 557832629
    0x240c110102010f0e010f1b1d030a080c1b3a060504030518090708060613030503190306090b03120c01060302030703080a0f020a0201091203021f020a02070f 68
    0x10720b040f441c0002c0000c650390a41c4100701a5180e0007891003031131080c00b41095010b000d038058200c1e0001e040010b00703070701c1d150342003621491040650030929580900061043c650400714841d50f50b1030301c082c03043c2c403105500c50500b048a0b044200703407c1c5041206019804100407000305040c000417010482030000a00b05003080c480d00c100c4228000381da03901969000e1031080d110641c03240440c24000c081402c00c0c00d01c4c00c0c000e4410404000b0301c41c2c1c0c001240d5800150a4036065035441d042030b255180407603c0e400141040c4800a0b001c095010000301402114407980d90030807450317840d0010b15040d9044a02c0d583e81c1540300b2000c0c3c0040e03105000090048030703440000021000c1c0c2c0d0b603020070304085495105490f50381c0041042e40220ba086200e200342c204052024200c0c1c40103950000e01020854020702e11250b01c11051501050b000f040100c0f02503108940b008510444140c2c4031b4065803045115100500401e440011480c07015101d840070313130b24081d150580045007000d000001d10702d100c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 557835062 1250 557833812 557833817
    0x70804140c0307090f0e10020c101104060804060b1230030f0c0409090303090b0a0e0703150225050d021603060b04140a06082a040203040f150501240c1101 68
    0x114402c540c6d54200301410400e124004090386a4034080d24160030448185884401c540c00c0c40300d078495044101c8100e40c2034a50700c0c1044c03030541e182c1d030500e140182252005c0c160800070303007005200601000038507040b00c6801c004c3d1031840c00c4c156107400c0683c0d0301b00c14000c08103100700340003142c8110400a031290b8002c50b0904000d0400b6034801e10350043c1c03484482c0640c003095680004da02400024604141c1c06443ea510510511040d4680243e4492507444050700044062144100101254048818008500041300301c0c6c035a42c11051545047d9107681103455205400c4609035141c00800c0d00403c40e074041c000d40c02002d1a5403284405081d00002031548603543d003200c0e10030200c10316502401780c220014005151810509420716015510100382d01030103007e54401c00100c0a001070100b49082603801580366160f40c6006000340034200340042c135900a402124543c9003807640150304035042e210030042c10145000308142c0c604e189183c100005010004071a011407003844c2001c0070384038180b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 557836312 1250 557835062 557835071
    0x62203050414150d0608010c03020a0c06151e090b010201150e190507050903010c052d070506010608040c0504090c030212070e18010f11072405070804140c0307090f 72
    0x43d0b140302803681c046034003c0f80359580c484051085103424880c10342c1280090a085203040b8220102900b03440e0400750007403001e41c4400300002040e040b11200e000a1035101050000c540040384c03203000c103202a02a0700c801e50300c0c000c1c85003001d40c814000d404010b64106401010305081c850400c4111000414400403001c03812041c003460320140c03244621524542e5a01a1620380d20000c050070741c3d481d02140d000f00401401440040c00d1000b9240c1190404001c420919140f0400508001d0184003000351440c01020000980590854540e6205074407445030f0b404120707202c008020441d4840c41c40a040007078180000c1c00103003032542141c040c070f00c14102211240c594070302c5a82207510301112607900d404921443c1c0300d4440c2003401009017101310081c05100301d05454041e02d019005004010f01429044480407070009540c0ca00514501007008091001d0f1601000290082d4010b071802c58200c170482c04650146000494401c5503490010081c0c0881c0340307818041ca002c0e0141d02404000207566 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 557837562 1250 557836312 557836339
    0x1e05060703260709050f010801061b05010e0604030509013506121b040c0503060d120512010f031109090d0503150901120b0105060412030309060b040905062203050414 73
    0x20381500c40d143c50f54803520031078102411310441d6100483c8003030502c5603000040c00f26a4100c01d181d40e11a0341c580a108030030b00c2505001c3d000d40901c1350300c2c100d240101410b110a0590100041020f000f0a807101c0d2080c020300650358520360030321842d98181d07880803540100804045006c5d950801e00c01001507220004552207141400b0340703a03910480d140aa1000f801d00b504090040c40c1c4035803c641406411440c102d008a030902c030300300c40020001400c1124102440b80568140c1d07141c5075001802030f45568403a402da0b0504070031400b0942e942507101100b42c40c03500d00100c20314810304060020b0320705030800307401c1a90b40382c00151000c00c10b400180c12200380c54456505090080449101c0309078090441e050220b000c40301078102d14010301040209200a44081c0080030003594580780000d030a046030708203840140710201d03003e0b91090402003102c00b070002c0061114000d407696114040b10a26100007008052034843d00140807130000e000404c9084001300140803200c001070820b107118a01d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 557838812 1250 557837562 557837627
    0x7320c040902120118051b030a021309081207090e22061d0a020f0102010603080a050c07090c02010b0102160614070203030702060a0c060e03070201050304060b24041e05060703 77
    0x203500c001d80020845c2c0303403640c09100080019890031000240306052600442020a40314000540041d00178180c02079290a0260598410005250080c1c0b405854404503441d400c02c018040d60240b0000725900408100800c04000d02406142d040c0c4d0b0041c807d409000254280942e115001c0e12aa90348120b5076610040310b00500d40e490040381c0140c581040c451042011100344034881c03504581c5000410710000d80b0200c1140c205a206041c519210034003d4600c1d480c0002c103802451000e41880354940b2040d405422184890000f40c00b81c0d1007440303ca041002220762984a000e0000301d501c0d0400d01019a91001031036128005426686040c0341078011501940c0007210507000540400c3c100401d208282c480e01c00040340c480d01440c90016a034000034024003000d0006000c6036510396444505546050014038828405803400320f03070178021210300001750000e00c20b40b0000350200544010600b1002404000e5990061203641400084e4070116083e6680304050b9a2460002c09460f04214 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 557840062 1250 557838812 557838821
    0x40504060f0e0a2303030112081306110609150112030e090411030714030a020f1206070f02010c0302030112030c080f040801050604061d07030507090b07320c0409021201 74
    0xc00c003001801440b032035141103800b072409903040c2012240e00210107102040040100c6e411142c480025a10441903400c209805224411954904120180d00040c5a03074018840200d00c0710300c01c3c00c0e03600d103507507141c1680d03115145540b0365412141802c005100c07107009000784650880c02807a00392401d1110002260811005132001d0769075403414446840145820401c0c00c014181803132134005d40d4000580402d030b580d0107090000b480740440c40d900150760388448000780303003512000d030886407542843d020151140c01c021100e000113500707018944000310300078001c8034120b400c14524442c00340e00e9900c2c11641d00035182c10859500c5010440301c0e611103081800740001d4424070700002418148082080100d0300103601100212410700c858080f203140003820700340d2242041c180420140d40f902c0c0d088036188081c0d0064456040089002820301c070341d015000810200040700c0000354421075485001c4141d0600752a102c41c1c3c410b4500c40500d0415030004803001e880941182004507100d080d450075078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 557841312 1250 557840062 557840081
    0x71206080601080703210219021201091a060a050a1a0f13050102060f01030218070905120604060e0705150a1404060503070306091e021c0507020f120a0509040504060f 73
    0x84c0d00a01c41030041c4211140d9604040740158944050b512901b50302949072070700628100d00c400c2c040b00c4c45c4010341d110040d0000062050200821850285113440f4101c000720451880a8201441c0021000d041c89401d60040d038800411049000d46007403440c1e80300100c0b10909031700f00d0360f050010031400038000c005052003440c40c0091002c0c0b02d0800307000a01d0450000d19a22000e80244e00400c05a1152640e4615480701144440d81030340c0c8006081d42c01140a501054102d80032070a002d02504010605c40d0145104140901603003402c0413000c0e41e10181d5001d05503000300115007009040803240010840f120b203d06007160101c65001010300903030170a600c0200403c0c0004200106194540703d100c0181612141c10020681492203090003480465a900c451746e50000700f10403521050304146401c1c100124085c021441c02d10f100a498100d460b40e00300040c800d460919442c490044140c600b070001c0b664825060020040400010b080301a005031355245d40c504130408003031030501816110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 557842562 1250 557841312 557841329
    0x5010f030b07020d0f20030d090b180c060c01090203030a110f010912030209060d110a08010b0703020a030c0f0605040506011806050306060603100e0703091101030b0108071206080601 80
    0x8251035400c190a11a400901540840d0843c1c0c4c031145010b41c11000086400c000c524241c00d424850050340700d8040c3c0030100d848500d01c00030829061107010f540109030707440d1107500300218503124200a800074103020842484560845203950840d410510081c0c0050054600042100001a0082415648000c5a5000140b151004044a207a0401020501080174002001010352507140c0f00c421f0403c0d101e04008068001800d030300940d96500c26a808100c4601d0700f08110b079110b1803d054103501851000010610000001416003802e070165070900790183c015100e003403600d03074048070350450b010fa01b1a1102442c500310380100340325200d0107100c1c0344520024291541449107440740c0c00032110104c0340071800c0090a1056880100300d00740c000000356240b548035240c030641d101c407100d11a00594080e0310040e04001d81c55905810401809010340b0a060401100310011025100e10503805070120b201c10340400e000b41d229200a201e0040c00200000d41c96854404450a000c401e0340000013 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 557843812 1250 557842562 557842589
    0xa030306050f10110705040f330302040b060409051006140f1206030a080a0201091b08030703080403030b0d030903050717120702011e08041a070516050309040501 71
    0x40580522403800504000c903100c0481c0005000002c0315142e00a8181c010000b46684100341010104000405060001d005001880710150008024801e07030480e8598114414014009007a000440c24091094450711104841c256001d12014141e055005034210104000003d4403042c18403c440c0115140c15120307000c240703066002000c0341107546006100d000c00708a030071000920002118809002c0091004595480c81c2c00642407802030f09025200c0c6030002035101500e5419403200ca10b9a115082c0390b607603603808004490105005000b080300e113620800c42030000c00d00503228035500034400c0c0742c00720350041c1c20000b00394810150758085000c509a0034043c810403c050048601070030984150410101a08407a130355150601521241c1030a40002d001c1d09591140e00b4554208294213045480f421032a04002e0003200c00711400c1d290302c0c000f000761080c0402c010f041d03030f0f0003080c4a079506400c200310742c40301760102a505c10040315584010806501e0365102c600a00b802001800710056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 557845062 1250 557843812 557843833
    0x20a030b0609060307080c0909070305190309060f0903140a06020c0a06050619051905040c0f081308030c0a090e0a23070804080a05120a0b01030b1801121e0302 70
    0x300b0040c09040d80e031080d08030b0b203814001000c0010315001c0c140c4080740c64011903142c2c031134900d00b0203040341c1025045d4000c4200c01121020f04c3d400c50074840b442646e40c151441d0340c03104202d60000c079662514001030f2034480100003213007100701134000005440c825500c3d000440d43d6004202c0e031107451610402d411a00403070b8180306913441501c0c2e22550544000607038981c4050501d100c0d1201d401118418111524015080b150b1284c000000c1d040147c82008090b0f42c150028220012002400000484040018015110440c1600300d40c0b54450001811904d5a074640c0701203403c1001f00300c081000201000444036000c00303602d03002d80c0011200080d000090280c440101400c007441c0d11809901200384058546d1040d8020780c442c1e040044640c440c803001e0005c596512039413055000712811003080c45441001079003c800d4411098a0400c0080000c4040c0041103032801d4200b5210900c6100400c05403240c548400003141c8205c29841d0340d192145065003024080903015001a0321650300c0300c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 557846312 1250 557845062 557845069
    0x5030103120e031b3f0708010218040b0d0c090f150f0f05120d050a0c12030b030c030114060d210206060a09020c0c0409140a14060c0c0613020d020a030b06 68
    0x24102485c01c00b0740080342c4000250706050041c0a41c805504880d05036911000300d240a02000d005052100c00940d91542401c030031307000c00724414855a1080345030130175004140c80e08610001d072842d440701030300c1100344c54040c818004001039580341c1e4a80340c90345d000100c00d8131304548400160844c1c000710043d4a0804100d800f11a1103504040d00807224010304042c525000200c0e1a0949403d103000c03543d40c0841c1c14220744104114034000c113998000e80081d081c81c0d4040d04003d10510041d030846004400080030142a01d00c10b103400c0e0360320b200001c00b141007400d00d1001038003a076008046109907414154401d00e091050811302c03138016006003051109030300c0c29483c100000c02144106504000c6090301c1c81d034844512500b0588075070740e1007a00c001003203420710460380680755140c207803203441c441c0c0d0414010720788207035100050380e0191500003009015010705940c003181004004190315900e61170740a01006801c1c1003a40e1040f41ea1002c04010780c2d0f807851583c06035224421900d030070b041140c2030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 557847562 1250 557846312 557846329
    0x1b17031e0a140c0a0605090a030e060a0e010e060c030c060f0a0b0906100e0a08010c080903040f030f0303020432010804121b02060403032d05030103120e031b 69
    0x2038141091080080301c200907445400c1000303101d1401c07400d66448a10300c0020386060b00c9080300800c0b10f8201410806c0800c000b00e82c12904070b0113074035101701c50b601c0a001c005a81c0710b80c20808004c00c00d1130089182179403044102001c04040904900e00d4140c07a110080d00c0c2d0f4205062110b00317035200c401001100f40d448050250089900c6038140000c0924000203a05114010440b030300815066246508c840c3c0b244240004205c000307001012015101c6500c58003130409540d40d01c000c0398480c004600070203400022036040310000380b5649085415540d620078071a00845041d4100740d000d01001c03901040a00c99008a20014510401c081c060048c10700902000154204e0600204004010100c3e1560760340105d01c0441e0b24058103d440c0301180004544c2c00d100029402c107101084c040209504616000140070a680458840382541614940003410380c000c0c40c1d00080d42400100005550308260401c400c4060900d00601107103078001c240740c030381d59105c4011035003904e0003a143c441c00d00105 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 557848812 1250 557847562 557847607
    0x1302040515040b030106111e011a12070b0a02030c070609030308010501020105151003200909010e10050f06120405060f07050c0303161803030804050111161b1703 71
    0x74900d082c1803500f10b0840b02400b0502c103400074084903401010741090f042c4071085500f071010b107041b01d5800038150083d00038500c2d4680c0c4038540101428000c12880d24207104160050400002c044003801c007651049250800e414060551006000c1000122418048a005445d096442502c2149507080080c031210041c0e12082c1564500020720007034814188216090074001d031810441c0c0100700c40101c0c004c1040c0d6000d845c80000c80900d11041c108800000c2038a600c1c00c4074200716507600c2c0d4468600407602901d600710100e851400410060800442c04884420010300c0141409004902e00a83e01c00c00c4504a8454002d402044010790b402e51449420044030310f000350410030010003480d940e20018060211070000300c261f00c60745a00c105c0070030f0400401d040e0b40004050352490f02800a00f42175a0850f407550800c40710600c444000f0041d1000424900c0407440d080c0029200c500742007048030003060b03401034650004100580c03409105203225414074021555880000c1c10f0104991011a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 557850062 1250 557848812 557848849
    0x30f11010e03030a0305040c050d050f0c030d021515061204030f02011802061e0a02070906240509180705070203010e1b060a02010b46210213020405 65
    0x4914410b0b4400109840c0c40c06998200014103889900300182d0520f40c5502455002e01d0300c0c078558040107404039080744000204800c90b80c281421900705038130780d503200800e100142d10034528003902d01060761450381c12000c000000050000c0305070104002d5031000e0b184255a141040c244020075500050180402e0f80c1d61000308192805820120b034150070b20700d07000c1d01c00c038400f003861401644180200b6038014850304c1040e41c0d0301441e0a000e0340366510361150070850f80c038154000805400021055480c0c25114080c042c2d0030008007400e683c6500301845003604069900a81051a500d8252079405440316480d525103942c0944100741c00d5860304c50b040020794220803000342c8210007030000311400003411200c8585812014208034018182c1e40d00c2640c0c00100c10310003d041e850148041101001900d032843c0c003002c1503081000d81e00090b40340108004145400801c61041d40070760380808550b00c101c02035070a800980000f04054a641c80800403554002020041d9103000b00156200b410801c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 557851312 1250 557850062 557850077
    0x7060302090f090c030a0c1106070e01120c0206010501120902120c040b0307080a0f0f1a0703050906070e06090d060501170606121c03060e04030206011a0c1b030304030c030f1101 78
    0x91101380d590b00001d000d0600d081c1e20b90300080e405a00450003002e00910800c200e40b00e500d08000010003074150070708280e001c01d2414808501e4020b0741e0040540a100c690010308999180500444003102c2c4405c80600040d03850142d0310042e92501e1201c1c0d074924504004003450f0300c00c1020017080b030300c0e143c2196100307911244c8100708904000c1840d02006e50070058150110f02d441c02d09803480b004040c002860408800710090007116414031081c007948040c0e9042102d0340c0e41150300c50b51442c0594180010071050091901c0034504000200713024080a490002ca0f08003e5403a042611001c1e01720380848040c1d8498030003084401c0081c2540204120342c0392006046031174100e51a005401c42c0840c00e600c0c10000c010301c080c06034215900030b0060000600030792030141802500c8010a014241d280080b440007222084a49016980341c46a024054099482c0b403d1101e00b80380020710701c03907816000901002000c00d4030b140030302000707501070284c014014081e072820802c3ca4602d500c41e103041c403004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 557852562 1250 557851312 557851321
    0x1e270b040606080103020f0a0e090f0d050306011b061d0c13090c0b39070503160501081f03050a0c0504060e010e4c0e0705030a06050307060302090f09 66
    0x103ca40c1c116a01903880c402d40611050200d4410f58441d00301d0b580c0e50945005000d10702100050001410030080240d44200300001c070b003111144802e0b145e41d400165840550140c0505c00803400361828070030000000c0d140600e4021140601c444840f0f1794041e0415845482981421200300503622248070080064605554607020300341c0c61b5006410032103001040b01c90041c1e49103010002045102c51017481181100c1c1c00400401a81d00203280e12170003403d6002496050000313010f00c4031040c028107008080d003403030011200d80c400205220100c4030007103159041c00070806802c40140d80100d0151130601c241c3d0500c1c000c40c410f142d01c8a4062440d24004016600310501313801d040d183c503145550190346600a080410145201022101c5c004884900c03c3c495500c0a243c0c1000c02c0e04900280000503801c2602c2d065211846030305170000c419000900054030460055a011907903034000641c00d629000464176041c01703500f041c40403c1c2d00003584030700e40c42e03c0f01e40c100d40d50f1070403101c040c000d152 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 557853812 1250 557852562 557852567
    0x30603140a081e0706020304290108100e0705100c170f030402010c020402120f010f0803030c0d0b0111030c07231003020309150c040603060509040308011e270b040606 73
    0x8000c0001603060f00103120200f038804210072200764a070000020354a03400d0500741217601c102c1c4a6409851003411690302d4000e401142034450484420b40c010b400700000d1000c032040070344400d400c03860700c50080e80b001189071340c2c038a803a2030380d10704542e520240c9801d09490711481174040340c001181c03461401d21101480308a01c20885e07600c00d90a2030f050460030b00f28404603019000f071180c8178020b260300e031040018404018105d0b904031045d40c030150803070301c0d683c1da0b220740c413880b003603540944880e03082103014841e0303203150041040610103140604050301c11044007410341d0803142000c14207403c040300801030114040100a00d0720481c80c848180e0092600018100d00600c0d03403094141030b0084001074a800d400d10008507a40200c2c0d41180041c50013000041459105010740f03008286000030110701400e00c044020302c1264961251500d41e42000c103061480b40d8402c010544030420981c01050300d40c22100320315002c04040c0b09032021600c0700511142607405103046140110b282c58801c124503603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 557855062 1250 557853812 557853817
    0x9060304060506210606011209080a030b101701090b060f030c030a0f050106122018090a0207081c0204050d0b0a11131a040306020c071503020315040b12010507030603140a08 76
    0x600c24248000c0a0b2140e498540244c0100c0e28050041c5070700bc106242119015044100d00000841c0d0580040c800c4401c26500152401c031401e030440406001400400701d5503000c8646010001d0510341008081511074140303034011201d901040d94003200340158080702c0d0295051020030400305000660409100422420740040e0f00c401040d2120f5606115000e41c50300c0c483c1e0300d220801043da4a0742101054840100d0f1001110701075075040700000c0c0c2d10041c610035a0000ca510802007440c0020901b000740d900f00301405410ba03001d0f4200030010b1180d5072008103034a4944101c4240841d03203480134074441100d084100609080e101000000908044045103106a50f00303001c035000010410b5220300b42038002c940008013180e10005584600c0000010700a04403a80203140d084a0300380d115044050b40001d43d03404000c1c1400780c0c5071a85524154000b601c2c60500608040c030300e0140350703100c1825928280c5420001ca0340d501018820b2180c0c0f080001031403681d42008141d081c040f07035100c038040e1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 557856312 1250 557855062 557855071
    0x40e010504110a050a030b0a06180914010b0a020705030a0b0f070c02030d03090c0302180906090106050f060901050d0501030c1401110c09130c03060b0f04151505090603040605062106 80
    0x136002445d1881c45020741d020554984010304032110340764031088090b00700911202844030300c0c41c4c00342c40050313881903d008081082a0784a5041200c6c1d00c0d10994600c550404000c1d1030650140a01c0401c541e18204200b50000d0700a82e4100990308140c181c0902000019080784204007000075280003507240054030107039040f003d10700080e4604080c1001000101e03d6000203520282d40755101c00c4000442c1c6085010f225a007041e00c01c41d03212840d0003070032107189100c1c0701d400035407134a010181c915119000d807144c1b142c10305115251036a80da10741822a00241c004903100c6482e00400c1c0207028440750903a862140030309044002d92980d1620903505c91105c22480d11038911000050100c404810103800c4081d800f508448490742c492803c0b0024004043e10907004902c2c101c059003c2d45014020b07a5100c1910083d07141c1400e040480012000c002111030009203c8100008842074403220000d512460140c040059141070442c1089400c0740f440d08040e80382984044903191400020688d540c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 557857562 1250 557856312 557856317
    0x160303120605031005040614091c110a1b0b04120b07090503030a02060919230f0a0c0504060504060b0a0804050c1002060906010f080d0c060b0301060803040e010504110a 74
    0x120030340e1001605203500915010300406013403e5140d605a04502e024600c01c1e00103000300c20600805100180045400078401d41c0404106159100074140f10700741040c06282103003903d89180181e9250000d61007044540001c8048250482c1a070791800300060140d15003001e1501d40790012500c1c2001520744003900301c132019004980160b005d642e41c0710050070b001c2c00396503c03130b0316044029440c0c12048032052494014401c001d1007059420071004032082c0d024415181340342c0c07608c079080c8903401c0b110304d6666240f003032440182880c1400c000d01107425100c3e1070411522030906092000391095070740020f00480c180407040c4184040e143c04d517100500d140c0780202c03165442d4140985081643c01d0001c3d00820300c415407541096000c603200703220700a1101120400d9984180e030503604607045c4140b0308642c104515401d401e621030502d002c0c00d00c1c0158000f0481101c514006800c46101d87c4c0f091800742e000140401080265659450061100301d801700b00e10104d07101410301521030301440904 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 557858812 1250 557857562 557857577
    0x191214060d110a031b18110304080306010201140a020d060b03070905060d0207060f051519170304050303031e070c020105030c03042a1a03010302150c0f0d0f0908160303 74
    0x43d4560078000b02c003c0d84c00403070081d441c0061301c0c0c03201d07180c151a015511040d10303480410440500745003d1190f480b40c4041c803a515503911a00d03031094a4101a00c007504654070b4544100060442e00d2815006070140300c0e0041c0d403960719007130b00c20450b11141d1005a40e51024410001c0350341e0404c8000d000c41ba015550142c1c1c07070b0940001d40000b4883c0b400c005098034a09082401d0b030310100e5001622514424049582100c0b044041003208801241898210703d03400310107020559141920911442c0351204032400d194641000a04503041111500800e00b00700408400c2803032511100c9030000030b1400e0030b0110710010380000700a88130003450548100800000325040010960010400c54000281c0304100d9120b0025100000380c40c0c80752895a0141041101800103200203c9040701c1d0f0040c0340710031603642c00c6511003071074115144201c1c4901072a00043c41f00042172010858844071781d62104210b1601000c080d0012086420203c1103610040810f000381900035200c1041e1781e0141081e11 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 557860062 1250 557858812 557858843
    0x3071704020d06230103080703141c0e0c0d0605040b0105010c120f09030501090c080606041404150b0a06030b1504031203052a090a0816060309030302191214060d 71
    0x50b803800e0306030404d1000c0001800082071000f0321001e00f034400e200f0740c0c440b0185014240b2151040c0280c2441d440d0280c003d940b1000300442c250312000b6186c03000401c0d90807000c0c4080c002140068050001e8502c203848008000030480044250341c090502402c1c4281d0309001a100e624100385026072480610440d100001c190302c2c0074084450003180d09c079000340505046441c011104c4a10351154840358807441000c14582e01c0c1078054209203480c1195098010b940d2611002d8a1120015100c20745950310b40d100308658440e440504013408040d1070120381011804e05200e180c4403150418000914148821301c0021044208103a5500c0f05280c0030485031902041a1045202061003603001032441c00c0e00d00e85100d0240107810b41c03042c12294180d200342c0e64071040d034a4010340e01a40300f41520310f00c0107000310750080d40a04510b50003840c006003000c103068401e411415400b8148d0010230300b82511010050064042da0500e0001c4504980c21410143e01048084001440003090a201601c014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 557861312 1250 557860062 557860091
    0x103330510050a020d033b07060305131127010f080c0f01030b1206071d0a050105030106081e011701181e02060d0203010603050103050f010b0a060e0414070503071704020d06 76
    0xc00700e00700e61029034140341f039002000007480c061030840008500401000180c1d0b1402071180c10304c0750b590489000840e5282e595088007107599132841d00da2190000485888041c3c3d01010f0307902001004540490650405451701d0401c031450f403040f902039000203400c002d680c0b84c02d00ca80401140a09003c600020b480000031403501d038000101909104101c100002a903000c0d403070521300e000000003644004850300501035110014000e00c4c1c0403800820041003942d02c110301d401da10010403204440075000c02081030000740d000f81c1c09821222079280512445a0081c07140d00030594600032031104210181e900d88081010402205160460860025041d07440764000c485901404040442d500d40e110080500200403c1c0019602c0d44a40900c0c04143c0005210b040e01d460b5000345001c2c429480d1140c02c894607134000450503080340c0c9030101d94200107005450107005903182d46405489140c40361006059480843c402000c009404050001580790700d8180003c003600301002081440108090 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 557862562 1250 557861312 557861351
    0x6160f0609031806080c03010b0903030c01020d0f060b070f0201120e0715110d02060f060a08191709090c0c010912090f230103330510050a020d03 64
    0x140c041820901e226040650141032100700c0d07411182020356181c3c9500e4125040310b0100c5d6280e01c4020200014448c20f0592006062526401400c403460314440d44c01c41030a982000040180441c0c40390178140c02c19040d80202c2001d00240844035040096030345550140000030040a810700130403115600961010781c00079a4400f8000045900003540c0c0c46c02c9032011403070000f260340007420419204600031004a900040162582e0061040d0b440e804c40450445d038000c0c0c81540c0c40592040c000650aa05004070100007a100880079000402420104000301009100480184003046030f10740641d11211040e412034180800c1c0c9460702c0c2d0100c51540104403034000902454150b820101e10b1035881303021203096425040e40c44600d1076072000c5028000700c2841000801050b048100e54603544603074000c8184c2c0155003544800401b842c0c3d800c0c01c50702c2c03c05801c2c1030380d07500251081c08242000003c1e0110100140750581c50045240c00007034440320b042e1440d07020143c4401c10398400100e407044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 557863812 1250 557862562 557862593
    0x1e1213081231050a08060f06060a0801030618021503061207050a0909060f0608101401140d150c030b120d020a0b040c0518042006030105130f0204060201061d01050616 73
    0x181004c02e40c6800c00195549070440d40e41c4164040c030030004510307050540070f8a6820209803124400da900795690400a032440c0841048052540050840903a64460700f03a400c140c0400c0f0b110741c1e00d080035003d00120051501d50302a15038444d84003000281c07109040f220448000704d000203801100747c139106000d451180703a1900001d05058000c82d0a60004c5102c800401c004101005200800720002c0c4081e8004d204500040e1701c1480d40d00a141031110056420360f1040030f0490524512520900440d40c2c3c082050700081d568014200c5a802c0100242c454000440300514007604800c0c00250b990040300c0c0c00507c15401240800c00300100000c0e14405400010581681a81c07007010920401d001103405440403c403007010422078004109100000d060013a00230f92441e820310040c090b01c00000802040819035510b602401200a031020b04003810300b40c2e0020035450b103094012004244000d890b40305800c450001000380b551800202d0f0502042010441e0170000c0505043c2c100e0b20b203401 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 557865062 1250 557863812 557863819
    0x100209130f05060a0e09100914011b0e04090b070309020102190f1a04020d140f0105040c030c0602030c0d120908160506090c031e121308123105 63
    0xc86490025046800540c8241c1084e40c3c4800002c4d540c0d1503108a642d010384aa901e40c1d08003004140800000d9001190614024070390040000542d100580c212180050150083c242240c0d0780aa2298041d00c5800001800c442c140405011903c40d01c0805070041c2109080c160303205080030031a402400303504d4903c0c10300b000d44a0000d003030341403e018030b07c42201c0031600780d041e0a68408404112009180c01260050101034404900340d0743e40503000200892100b082c440c5074001550040240a0700f8404e81c4a01e095039071152440c5071100c9100081c9d000310055400501c0041c520040000307503c070401e541c1d440d04014403185440311000a25900030080c1c24124000340c0c012111191510b2551000d1007901280c150ba40c40c000b0745901c0301c00030040385030301d07403c040055402c00514443d03040c019031214041d00e804808501940140d0762050b080198100342809003001012414407200003844202e000c0c2500c0d20b24140c04081030108145100f81c0e021000b211000407015440b8001c5c0d010b0032015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 557866312 1250 557865062 557865071
    0x24090907080a0b150a0303230408010c031b0905100e0604090509030307140f070b040c0b070f060f05010b0403062003090304080c1017180303180f0a0510020913 70
    0x906000f0755020b4101c0319050070403480300b1048030500f4980d038a64200c2c2c0e0166150651000841031404a1101d02509002600418440403850150038400c400000d40c2c152000500d42240011000040e514110654144505c0802c10041d2b91102c4200d0344800001b8a04112450b07000310024015001e190071007800640f9000801155800000085004001070b441d48019040c220305920160301c82c41940c4130b02110309001510005400d02030703082c2c00503c10701c0c591030701303c1e01c50011041035040480700b41d9103020100070318070a000051103559081d00c0b80040511a035818112680110f210701c2c0b00062006035903101c0403010f0400010030009000302c80c1c00b40c559a080040c1403551b01d07005402154141e010b001810f241a1034100c80e6418000c0c00c5441da11100c8a42c484004600d5000518030440d06458904081c4000380900c01140304008043e0030401041c5401d95107807814070f148010000d04c0e4041488940030580019005142100b580000760780d640703980000c2070054a82159900c001401d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 557867562 1250 557866312 557866333
    0x1603090c030308010302180103170f04080604052b020c010804030309051507110c300a0c030605090303091213030b0115230d02160206071a2409090708 66
    0xc0003000c0c4c126030080716880041c000d200e60700704920b0021300c4000d14004020b5040c4000c41020005007854441000d4000e04041d5240c05107401c00c0b00480c1c003207407140c1000110440d8a2a81e1100b10103c58102c5102d4074030158140e0017079650100d510103107040c4103250000030200740c481d4000685540d8881c0c02e5403d20882a140842d0300030068458001054192040f85914030b800076842d60300400c024802050700d00b031000c1d00c04079407403007002651351400700700348007420700008000d07240045204103030414a8038690700700300f0300b110406010703500c0b41d4000700180802c0d000c00007080340c45002d440c0e882d1680c4000c00702c0c80000b020300c00e074001032600b40c802e800000c01c001e5801c2440d1a101e126291425000c0b51040501003882c3d8440071403004803c2442986036558207503001d00012980d060722900340703107130b19000100250005c84049030140a1142c10890030640d0310340041c3c1207900441421000c2164010002c0c44018051282c1e028010300c1c40020101441040820300510b0002e0903500c5004030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 557868812 1250 557867562 557867567
    0x216030809010e01023c040e04020123031801150803030405100908120a0f0e0c01030c0503220c03020405040f050f030901080a020a09170d030609020f031603090c0303 73
    0x40031911000c003035103811a00442400117008031054152031074041c0c01d0149024040003c0c101c803903c42880584e1030503c6413132045041c3c10007071000d030007448608046890b062000400589481c0a0920404d40144503004984031601c2605d40020801c00130508030082100c200e401888008425223041d00d4114000540ca00c0200c01540103e0044003a2a094400e9141080c103942240000400072141081604000004000302e03681060302c03103402044030009910b25205548190407481e050740c120080c15600c96030188541e01c010403060412600310714000340e120101d2400c4814402d00082c0c00d20a41d01040a1191020040e6a00610402583c02c040c03d1018030030081c03110450b4103108900500444180010030356250b0700c2d059483d50307401c0d0f071510103d002a400c03400b400c4041c8040c0071000301d01b03541c01e41c03404001c14404400034440c100194000801740c420780d07440010310381d20400c100b4020b0001c09048a07400030182400700c0038458800400c038014081d680014060740040d80d8040101075 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 557870062 1250 557868812 557868827
    0x1d04240f050f0301060b070209071b12021606021018020904030329100309140f0d02010f06050618011209050c0f0102010e15060a08010e0105100f030c0b0d021603 71
    0x300c1c00e8842d03694a20b051001c0c1404ca0761035000b4200e10800500060005240c504100e036070048083c58000f22102c4604501e110040e082038044441000034004080e0300340d410005880307022403801c2025034191a054002c3d445140d804003030030466480d801e2804500d80be401800710302c3c96019000c240c007460319007401801030084560401c03ca80c120303160034840ca0030f07400085101490003444c1c02101e06042200342e0043ca000502202d0b00107042ca42c0c202d0980c014490f02c00704580483c0507041101e0401002800c484800380412001490114240096103034901aa2103401280c04840c0380744824000598140064210b080d140302d0604604100700600800c80c038110010680c1c0160621038140016400e90300300e405c50781500d9021042c952640c0000041c0207030032a0015081205003078036141580d003034460151012a00f6911042030150301021500404d000b459140482e003d890304507500c0d0a21140184180408184042142c0c01c0221060f411100b03003031000156440c00d404589805001c54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 557871312 1250 557870062 557870069
    0x60e0112030f020303040507120611030a090b0702190f05030c0a0602090306010518040b0a0b060d0b0a080c011d040605120a1101030e0304061b0c080a11011d04240f 72
    0x781c0b26004840e120303800001564000e59000000d407810301e0420b080800c40900b43c580c2540d58036124410390440c000000001d6000302c40c14100854122142c0c10205100b244c0548602b0455005001034102091068036160078140c0c13025a1504e805580d00b0030f14954000e900c03890106000d01134005081160a0303000307103403001080d41598416039803801000303d601c0710f2030103058142c124800000e00041c8500d0041c0c1e84407038410000030b01040400701160090700440141900380c0d0f0b440d2201026454840341020091032144001d202c926620000204104184804030000403031000414003283d8a81c0c07c00e002419002d0035003900e00c4a1141a2640c0c1d0402c05030039900e4080401a1404a52181c003803480840c0c80d0302e000794039080c90f04904a4880149048400c600080c0c1900c040000341d508403890018198040102401501814490780d050111042c0e11b0500101c4000c8440742010f1a041103054001201c0c0055103c1081f4035054504111040303600300c01840007808180704212041c0203095 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 557872562 1250 557871312 557871317
    0x1810020d1412010b070302010e070621020901020c09100b030f01090f0b0f10090f090501060807110d08040302100906050702070b040f03260403030917030a0801060503060301060e011203 81
    0x71807114014464030300c1412003440d03001608a0040c0b2064080000400700244a40700000790030f20142d080600b4104540c22280010b06030202c2038427030741131042c0f501c1e45c20728400c10118070f82091000080d607070703c030000e010a000c1c4240500040e495802008500000c000a08041e03aa81c0b8250b03440c4030b8901400d00418400615000b00450012402e1241003103040025140c0048802000d0400515000313400d440350810895038001f00e00941c41000c60402085c0700e01020500d54101400503101c130300300502880405c4080301403007400800c0020001400da105081c0100c1c2511103080890415030703050700580c543c50a281444080008a90081c0d2089001f075081c1c0d4009521079809000b1480787d88100942ca04440c5014030103c0c10b0740e030100c12000241607061032206e00000425403541c0140d40283d02296281c10b0410052007003041e01c2a8070000c0c1c0c1c010310b00d050707540d580c083c15050301030084000300070010002030750030345095211001034000c10300c0c2411b0303641e51080c3c0c20b81704850f01c0c0c01c101c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 557873812 1250 557872562 557872577
    0xd0c0b07080702061810020d060503011b0903020609040e011a01022e0b0109150c060501090204050d061a0301020c1f090506180109020a090f0617070b1810020d 70
    0x34141c0c4150541c6000b071042e40c0c0036010503100d11030310448900c6114001d0107140100c090414038040c0d984011b0082d020300140c003041ea1458541054215400180700403c11124142007484450b03106201105032a03048400c81d49a40d20000400c004204c100f255102d00c2d0301c0c1255094565040300c0390302c003821009908640c050004241c4100340313240002460100c904450800420a000c150051245200c06141c0213a103142c0c1e41100c0340460011002d1103010520003031000007807144601441b405400080025840d2a10f4100415803a160144014240c40c0e550b519000c0a14850301c106103203040010025500c4491a0044039210014440d920721317002c2241800440103460703401442c600381e403c078000c1c2c100b50ba1210740d110303a106d10801213280f655589200c0000107a50300d0200d0006401503560000d6219010741c03400c0e0031030b10203400083e10017850010300054003a00094920540d8101203940751640400c0b40e8065813401542007480d031200c04904164005580015102032400f1103564010703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 557875062 1250 557873812 557873821
    0x1b0801020406050f072d030306060516031d0411090420190203040504050403050a030b0315070f050c060103030203070b0f0103170c0307060f1e18060513050d0c0b 71
    0x18200d10480c401e00700410801d0055440340744140000c1c00005001d400c41c002d8264000500080f0112004941010494000c440e00705242d03161241901800e420300f002440e01646455145080303488050040c100469920040071340b102030102080c0c80400500300f03200b48580e41124010341e41001c00c4403801030b0300d8080c2d481d032400c14082c040e4042585001c003080c940900c000c03940803910f50301c203405402c0d4401040000b500d6101c0f841068461402680c0381911124014401801d03200b42e541c400e0b100303a100e9441501e03080c0c05640c4068100d90541065801074114603401c3da55802a44010441360083c1f1000000f815004030081800b140700d0305549441d99101c0c840c8000c1d1010070700001d0007081d1719606200e040742c00741e0010b00c0030b50b4003a02140d041507140d56401c0280c2303007600c030105601515030034091000500500380420942c0420018001c2030450300300d03941c0c0320250100c041c00351034403040490390340c4043c41619692160000141e558105120001402035000154101e40714207600703002030f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 557876312 1250 557875062 557875079
    0x150810110f0d02160f030203071a0f0106030c031d07050405332b020f03120d020d090507060203181020070519090e150a0905030f03041b 60
    0x11441d2900d0402002d080c840149507040003074000d02e041c404050300c038005940204010184c4250113611075170066070b584996190000f8249800d846498801d9100d000748904680c0004129041d5211840c001401a400c00801c90141c000c1c100c0e16280d80070700016502d480e000105a110a0318820740b0300b40415140d40780c45440704642100c1c01c880c001c0d00910082400c41c01044445c032006001021003084501d128100000901c130b4001c50101450020004811130801640b11110b4100072000f600801e180c880e50003041d44152401840026400540888034031084d6201c2d0002940110468801a407211400f03540d903805203024554240403100e0581e00c40c0740406805007070310596a15842114105a542c016060b500e02039004d460140d0700380400c054440c0c000c10552071844000381121246008080e40840d01303a5041041d03d6044000d04c04030070104c030940d032508a40c07402c2001880e29614205035085004c2c150f200801c07044000103000c10300c4024001c03005031008028180c41c84036501e0055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 557877562 1250 557876312 557876317
    0x506040303110f07120b060a0512030d0c050f0427091505010909080f0d061502030901080901050609010e0915072c15161703090f0d0c1515081011 64
    0x40ba100c441d440e481745000125a48500c54000380040c100c003075110f0715040052012510340300d4462003a40046050099058075005864a40da81c9041071440d25101c0d83d5406490700c5580940c00304d002110407201120042c182818000c0c0b02c10403420000d080880c0340039020b041500b000d100000781048000b14915007988586c1084d154401942c40c504402c0340c4040d88107410204007800306a40c0da0b90300250030000c00351450007181190b406990b880d001a0005401c0040c0646241801d0789800300300040790700c0e03e6840906403101100303c0981c0d030707440d08941c1d4508103071a04200d220803640343c00d0020403900194692000020008040040740b4034020380c1c5a103402d4100740503030100400c8020203052025000403d00310102c4201c124040f581a191014816802e814220b07000000004110104605100107501c6440f039201030720600d100d0300d0000345203c40303101c8050428880b004c50400d00d00d00d19132140340301401c0301620b443d51a035a0210241c44040388080c0c02d90041c140708200b84004118000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 557878812 1250 557877562 557877569
    0x80117030c0a060c02011508030d0f051e04022e090b0a02070506030c0405090f181207230604030c050d022b0c0203030d09170304111002070506040303110f07 69
    0x81422125036111100130f4400d10b0608000e555848940d5000f461558414201410030007000b1a030b501c21400c0951308035001e07114568489441c207001d00c0007007440e8030300204614070a41032548540d1210300024214000f424010b200703c0d0061070030000120004144c00c000201c482c0c0301c5070141d81c2e85030164480c520a0039030000042e00000010301c002d141c03041c060341e000300c096000300e420140c17560003140c0e00100554000c40d030320f880b40080200020300e1000310804d240360700b8050421080204031030000303401040380040c1091280e01d100c1286941d00203c000c8585543c400700c901c942014280074002201a4506981d180108950060840d00000e01512414410503204483c880340c4c89800c03007401140510307841001170301512078003da0b500304007030410580741500015880a507031401800d4810f00006d4414084c50600422010641000e06030319418010b580f000c0f6607031000107040f41080c1e903507000242c0c010008100401170641c4140441c8003860240d007100d489084080d070040c0c0c0e4000520 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 557880062 1250 557878812 557878837
    0x1401060509030c0904031202070b0a0f15140d0b0408091008060a05130e0f06071101051902031308181c081605011509090b07090f17031908011703 64
    0x16222005013403402009900c00d01914200c001e8805034100348003030740d10604050751301c4003480c8148149040035101c0c081031290004070422201c1070041411042d08603d20400d016072101300700860703045c1c8076000c4a0410540c0065040d0302880c051a00300056006200900d010740071802505040501414880d8040c1074000c1c4010300d00c80c03501c42080020950b680b5481d0a1589601440c500043d0401c0300320820706006003d0800340c80c10110090422202480f09449a8100001c0c00660050302c0c510442601040b000075070b580da560742004000075040b0710010000140020103030070403d1420b43c0d001c1541da003102c64105003074840c03c0e40040c2d9002c60070064480b6004000f51015034081c0d4800c407464520520000c02d0010b00c04014984041d415032104e13081544441c0d05100300182d0f494a02d5005009040486486040a428622811460060001c0c0070303103020301c4688101d010416034520300e40801030308050035160480140400780c01e1003850307032031398810030b000c56800380100594000b0352142 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 557881312 1250 557880062 557880073
    0x30e01140411060904020c0d0c120503040c051c0212071406130b07261b16031103030d02073c03050706061e0305060c0f070609080f030a140106050903 66
    0x304100c00b03075101c0d0130380a44c0700340d0030010303020075010901c182c0c0140304081e100c40f010701342e0604018440c8a000d4846000f048bc04000704000181c903514810b050b12016502612616142c581442038240000b001030343c028606810b4484080c4001504070541e505a41d03480383e500c540ca4240080790043d1184101410100340c018811038250354040c141541c0541ca48001c0c42c600c1c020160748094914480c0340322110300140c40f00c0d42e500780120b0789142c1845c000c0200001400b400c51103041101c030340001048100c0c4544001c009690810076a0580714009400f1035883c000f43c98000c0e90100702c204181c2c7c88000b10507140d46a208540114134000f1010b60102016160030743d000c0f202076000b417004a0f2015901c801c0441c80018584d050b100601203560803608890850070300a1501c40028140d00721160300300b002c0d907552100801503540080c0e0004010602007401c2c5020034050040c0f102c002c02c201030100070080790004039000501d00103801022056280d81f42c403c01c907014032810f100700390141d006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 557882562 1250 557881312 557881343
    0x803030402090402010c0b0c030403030506062a012004050a0b03060102120c070e1503010f05060a0302011206050303070305040906050913080a021f2003010e010b0c011803030e011404 80
    0xd0398154444d10516015400149944d524000e8200586090440c4040030041200305030305841241d8110034101c800900b42040d00d0403d1901e00c4100502c8802c000034402010340805094214914000080ba40d112a100220f1500150b40e001807185600c0745030031403400910a80c8520440340190705c1030740600141414056007000f503500c480e03001e030400c3c410800c00040c00641440810300458080da18807450100d10b008060030340b12516003108800c0d00d4001400125540c10710a10b084030350a0070034680f40e112000d807440080c080c560000b42c05001c00034000040551001c02042596118401000042d0310382c000d0060840c000c440050312011208403460118841801418012407644110b44c22400c0e003140c000700000001c4100700c9066151204507542290b49207172042ca000000f08060305661408491074502241031050034110381001500040c20031080d000303c14129045117034002308052902c1e001f00109094401c10405501e0b162420801045540310030340602d80002940040c58034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 557883812 1250 557882562 557882569
    0x70b12070c21052809170f010501080303040b010e06150d0e0a140d0309020609011b0c03051b010f0c06050a150b04031101050304080706110702120f010b0102070803030402 75
    0x28034809480c100d610309881c20486602881010b10011550356164441c0003541c00313945203120300c9180c600c0315107080c9010300d8190790025010045134104010364240b40c1041400c40c0c20100b600d0b060700090b500308000454903800000003503028901c94540080300d60781c2e41d8882410b00c80c0c01e480f0a50f005101d500c14ad005030800c44080c00520020714400105509013148141c500381c1c1d200e004442508e5000110144030105014150f20000d86003020701440030750750300084a81c4101c4031941c2c1030102892180c402c0340104010b100e0190360000d1030b2000a5100d0601c01e5844810080c410014084001e1420155129424070f0806841a854600c00c5021310ba844902a04000b400010700c5507640104045c0d41c85805c4503a402400d4020f20141c1d904c2c00e41c01e080421011031490141480790030014000007810b44000c460039550130410006040101046070b01583c843d001001c5d61003259048460700406c2c000c600069408007404c02080940541001681c555915124040441d0010b000203405820b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 557885062 1250 557883812 557883827
    0x70206060f01110f0c12011505040216020a030305070b07030903080f041103010c0c0b1303050f090f06030903030f06190902030c0408010603031707090b07080c100e0a05070b1207 78
    0x8070504108904000c0c0c50034461601d4802c08188002d617101c04c84800440c1801900c8501c05040750009200d0780c15080030f821880100b9229645c09942e0004071940140401e07440442e03200e500801c9040a5696030500903d0398000c03240a4034200100d0000ca0030302c034002e20031000c030341c0da0644504882da92854034108445800a0007580d5640745104108034079034080c81500412107064651980c02c402c1400c1c07401a51070b000f0800c501700298030f01508003180c0c008081e030310b1001b10f903a880c50742c0e0809074006c104002c602040040d007016012040c440803e10103c00b552080c1007044100c00742d6602d11040140c2ca1020104100100d46018800e121000c240e400440e4090641000503103040c1d56125980e0231540a584141c0018003401c510300c05448000100a401034050301c2d100d5542818074051103480c0c821181d0003001d415000842d0340401038240032011116041404c2009110401d080c07403900e880002c40112001c0c010050041080500c2000342c692213503c4284038841070f0f44000c0f0541398030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 557886312 1250 557885062 557885089
    0x1061d01090503070f0e01090501060c140a08160b0f0f07050d0e0f0d020f030a050a0503151206062b061503080a120b0d02010c021909140f070807020606 67
    0x859240e20202e6a40c0f02040315600070001c000903051420b1504100400d00b0006821403118103040c40010000305900c21100f06003103822411600f2440520080d4a03d012410100202900c801090010015600501e68001c1c00d00032480040c3e2556161100d0281006c02c480780e510055148021886452107003014000c1008409000201003a844810514280000c2d441c010690300250310308403040e034103120b500043e480070801142811101e4a0242590245440c0d81e42004008000224541103402010110707800180901e030008150b504210703198481158614055001c3d43c500114400603403042e8501c1e0280000003550000e0035a5849000d000300090354a1940321104022020496840052609020584500c80d030040d2540c620030030380d80304503c1c8901c10840e070700403040583d800180c4035901c2c81d4121031141900b008004c40c10031080b62a000642202d00e09800c00c00c1520b9450416802a0074440c8405029510150304681a200c201c3d40c50005820410115002e0708156401640f03c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 557887562 1250 557886312 557886317
    0xd0903060209030a0b0414190807080d0b0d1203050705090f090717090312010b032505160506011d010f091a100c14010e031c0207080705031c020301061d01 68
    0x400b0a6880b100c4c0017003c01d4500390740f46054096005100b002c20018140000c148040d04c03010090300351104219070146040c041c0800d040015401c2c8003040c0380d8840051400010243c2035007038224140560a516012004000700303140a0101d091180904181c2c1d002c90307001000f0303005c1c0540c5402402071041d0064151824451050403240d03d00b40102603031441404000011900c5020a1000101082043c0e01180a05608106100c4103001c0140c1c08420301440700100700e420590042c0032100d9200746030a0615403146c0c2c1c0c60710010005d000c038559049902424210542c0c41402ca064040e0450a10070040c180c144000100310080e1700781c100480725204009075402ea5288040402d800c1d8010181200014040f01034500030401e102d03c0f204074804441c8001c100f658403034041c50750369200d0506031344400070f9200406005c00e1400c3d0100c907041c1d40d0014240383ca801c00c91520f42d030351b50000c84035030621400c180254103502d100c901c00d07603040700d40c666942e40e1800c08581080658140300140c2504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 557888812 1250 557887562 557887573
    0x15031101300b13060e0417070b070c0f080c0f010605030601210312020d0b010206090105190915060305060f090d020a03030f14010e011404090b010e07020a060e0115080d090306020903 80
    0x2503625070351044134010800c41c03107110810b141c245085850010f5882040b5425074007441241c010408a2400e550300c0748041c1020100340566040c03603540c00000d00e100510300480000c080303c850001082e003c440c0105d800080c000b42c0c0c2c03170314101504d8220034001c210500e10701d01c2900b105c00c40c1c80411500310500908069400124072503200003643d00c030801c1c0d61280c54440c5000030155a0400c4110342c400c0f0315200800041c14448034054001c10f03525908000e0f030351034424903424000308a1606a41c94003400c01005020340e00c1c0360407a1940750442d2803078203020030800041c40c00e510104201000c04c409a000e068490402d039070640052080714645164250350f00d03100300d0264123801c03645000c3d000106d40031180350700d002e40155641d26104030321809281015031171000544100c0c25203041d54400c007a450141e6482800807071414031241009003c0c0360034211440c8086906510403280e22004d140310402907911404101c6d546e100140c2d0000015911507010004948a54040e00015100a0076100c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 557890062 1250 557888812 557888839
    0xf0f0c0303010f05010e0102030a091502030d0f060305070503060103120f0504030609050601031203110f03091f090201020c0405010e1f0f0311040b0301150b0306030115031101300b 79
    0x40c5190426000b0840211000720284069070b0414402e420300c00007403008500d0201d40ca10b00815081542c850100d000407400d000b0440c0b0350083c001d45020304a40d190411107002c4003415980a480d15100c01c0d510f50044040100e0b032404e0105283d810f89400200103c1d0051303014208039002e607190400b142c2000310070720001c070025500c0d00500606a0003400201455411418400440da4a04040409151420300500001015001076841d0403007080e100075101d40e502d00c105800e0070902ea0103140c90f501c50280d00c828011031a803282a03400c1c000e07800c980c0301500030000e010031190280113646103a0500c00c0003405008410080b4181070030043c1088085691340c103d1300a074031095030021620107803515000d005500b05442980c00e00c040403802448510851160000118154081d000c03802c03400000007002034900350000390100c0c0784100540b2100f40e03241425485956940251070005007010707003909402c3c1400203001c8a98205c02c8030905100541c4401c20014071220321420b8100c02c41c40c4101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 557891312 1250 557890062 557890087
    0x7021009030b180115080d3513020604120b0a0c09210c06020730020108071106010b090306060a031119090e0a030f0c051e010e0106060e040e060105060f0f 68
    0x203030051202000400d10050350103006070002c0303c01084082d0b80c0d464008508211340b60810041500c6014258042d01500d481001c49c1200c44503140c040d4000c035000070001094941d9038540b019242c0149400e1215484040b413840a61380d03061314140000b001280107020445540b1106880d298540c2050500c0300101d0b9a0707500c95801607030250015821442080011000d030025543c0e03032002d03040090444440003540808101d074540006410400050b00144105000d140f90b8011000f440c0d080710069a5280c0c0c15070204c2d8480d8020300e0181c02008080340391030030100a0070050385e03800f1511000650388801070110703524402c2160b0910f8107642e00e0010b000250352141200603041344d0081c005604c040d090140038a55004860b6042081c0c5040380e201040d4045034021806090ba8110305164426500182c054640e20201c85103d500c3c1240000da4682c00080c40d9114280989061281c20a040e00350f54a4900910800d50006810841110f103ca0b42c407004013003210200500d0350a1410b0082070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 557892562 1250 557891312 557891351
    0x803010e06120a0c06032007030e0a210614101512020c01061a0406140304020a08100b0108060312120702150903070204140105130f020f0d0207021009030b1801 70
    0xda40740c20740c0c2182440001d500d4050100214440360174a00d42c8501f4401002552081402c05400c106030000501040d036030f420700e002c000b0400964800c01d5403858602000039009505012915030f0b16013840c03000039501c0505824400d224010501c4c0409180010010b101c810380a949810070200144e017664020700c0748080d00d1000541c00c00001d0540c00d04120340b100c0030143e0164032035085c0601c07003004010b46c044020003250f03074a860610f8481e241c80c4081a4004e0304c50b006401140601041090403001d207034009550300d00d0903a14111aa00c4681c10b040e01e03201400403491240c1000c00440f914400d040b0301c40c0743c2002e002d1044401504d0103490001c2480300a80e02802c01b41c000048403c20b500d014050503000803a500c0311040d0552411001904404148188400e1281c1f19500119500411782c1507812250400700301995601c4004180c500961148404034401c5501400c401046440380d0038010681b82d0000030003002e82c0f24032a50400000d00c01c1c40c200010340d00e5090810a40c3c20243c41d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 557893812 1250 557892562 557892583
    0x203030a0c050c0a181d0307140703080c060613020a020d0e0f041b120c0806131407020709140c0f0c010b04020403030e1002010b0a170c1e03190803010e0612 69
    0x20350381c01c01480c1440c03a0086d0f43c1107142c2000e405030002c1c0031031110b9101008582c1801d9000620f100c4502003625628201300302da03030000e0031340c0b480031403805103044001c50110f02c200001c580c2e600e031103010f9103e900e04a0080c0b824a0005a0191410f180300381e000740b40e0740040b040d00a00740341d010001640024282c0303071b00c6072111036000c820b00a11040b60b508824103020703511f2007a100384a0b5001501c0001c241c3d101c01440c182c440c6c504e004150518079060303440640c124180414124181c0f60000020b0b582d0300d081c0c425507861514011020070080c010840080c011800503910514000707000ca00380049801c200e1151203035568a4101074419039841c4010310045205e5102e00d17030071010790000c00480f01c1400a114095905141074550305a4a81600005940d025003403541d400080800041c500320311000402d0f00002201118880d00d82c04c0e10b54620f00e0079044007201c00c281503a2a4081d0100c65003000180400c90500c014050044e0b0390b15100c1c1d02c00340151070040301e89240e994042c0f80c09000b05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 557895062 1250 557893812 557893829
    0xc06130e07050c031911060a0b030706020f070e06130606091d07020c0103020f091905030d09081c030e1b0301060503010e03070204050a091211010f090203030a0c050c0a 74
    0x44041280c0e0901185056001c0624203040f41440401000a500c920a461101c030b182010001000e03841c6005600502c202082c0d03104882032803800308080d02c0103100d00782405100b40b040080014040784001500c1103012000b10103005200e2824001100c41d440251041d41e200c0d1445c003100922510910038903009180696816170700d01e18040c0108000c841400424024010b030204225406070009420b0500c1c150030b180040c2d0320340c0710800b550010b0041c01c140070750000c1c07811401c1244079459041603080c1d46040b0142c48008030100070907154118148100b00c01034102000c07080c10783e03a0303800a000100d0702d64100407940d86141001d0608040b6000d081240a40047c1d1001c011401c0911400d00034003020381c000c0081074143d00001d5640d000d030000081c451900c4000080700c0c07c0e074a0704500c980f2036029000100320508a07501400f080c2052011482541c41c00326140070b030014900403005003580140c0a1483c2c0300c0e8916084400e8501000c05849502c28401502c1040d00ca80d50b0707a00040040f903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 557896312 1250 557895062 557895097
    0x110f0d0b0a05060703050a0804020a150c0501140108070e070216081e03042106140c07061506080109050711030a030b01090902070308011e050d060902100f020601090e0c06 75
    0x300801c80514259000340c2c0c000c0b8414001000065040b00407502c80c0003070303410024402da030780c2c0c4005490b0b08016001400d29200c0340018101c12600306038540e00b00c03442100284004814000c3d24049400309100c1d0000035070081c2d1003000800d030113003691030704451503105a0340912105000801003a107540d000d58500ea11858035042e0081d42c0174140801f4100d000051880c2c0b5240510302c00b140700c82d41d0226424070b048400fa0408204135a4810020f00d42c03288090012868140079181c2c80b0f0704080802d40b031040c142070110307100030a10210f6100350340c1e0680f51040c10f642004079070030040c5001401e0750140b01c0506166030341c1180c200701604107040260f03000b03c3c0020f0a07000041001c0340c0303039000f02c0086005000040001360004c104c1d40c155407070440d40c03a4140c101d204501620060540c0002c0d008484004034105010742c42d00104001c0703000740c545500ca072514030002c840b041443c418047c0181c00c5103005104501998004160540c1c041e400c0b110740c90640c400180f02507010680000100602 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 557897562 1250 557896312 557896331
    0x60703091403120a050d0902030f03070b0a0605100f0203071a2406040504020c1c030203100b070f02010e03010e031207020d0915030513060509100e030a02030706110f0d 74
    0xc078010410031400940180c00e000007440100380f1103000700b803400c00500c400420b070450542e01079130280c8145a00141103c50000c189080a0b4076640241c034180d44ca14112000107400c4038803130255104890002d494580b409c602031314100d4900c2c081640200841c003041088101180c5e0344002805220096030743d051450810302c910221a45a10700056520741c03081c0521020303690f54000b600e0444105580140e40d42e8106890141000c01107520108413207031803084440710a6041e0f001d10310602140e40c0d840803035030b110410850113004102000b020004000701c5040194405c403004441d6081c007030000314040214203400c0e82140c11900c0010003541c4071004100e881070341040f51150700c5a80d400c2000a41c4d0034000040001e01c2c40302894014103840d0000318603418210754505101c15049842000b586c14005803a948034603911442000c05814270369008807028000c0201c50458455800540c50308520740d50350005086100c030310a115880521040b540b80151130001c1c03214040304240024003192 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 557898812 1250 557897562 557897579
    0xf071a0a0506010c02090f04081306050705010c09030b2e090b0a051203160521180901050f040e07030b0403080702060f070c031b080406030213120c0302090a02070206070309 76
    0x5004040a04101804c81c811000d6212000d2880c1c0100803040580040da69608044020781700d8500ca819013260200400140e03a940031000c5c002d00347c4107400a00500c2c2d414601101c146a090201401d1900175401080400641e503c00d1381445001400301d0a4850038540c9211008955510482000f034888840c41018600054188058182140c41e00305c039030900d09100e40e4238080d4107064515600e8a102890902030100901104146258805500780490305c49c13003601c82c1c201200920000842d20031201c1d541c40c0c5440c140381600e03000307083c0340c00c0c86040104110103401070700d280c1502800340b200040085024000e1040c0720f00d01036203407042503041450f0020702d010401840080c5a00e00e04051048080d440030b441c088040d01407901841c0c1d082046200790f1400780c1c0301030050140d480094001042901900580042c3c21821003410901d03a0790a44a2a040c11a00004180d411101070900051400c50744442d00290b25000043c14422698080b80140e4410364086c1d0108400510800c824907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 557900062 1250 557898812 557898821
    0x60e090106060c080307110a11030d140904091a040b090d0207060f082203110706092616080114090102120f15030106150305010807030b04080f071a0a 66
    0x440400200700310781c5010002801800300c00d1005084442c00404282c01d00d208081c0c49184032181c10669164000c185003200f0040404a1520b00070300a042c40c0f0205240205181400444603541c910700e026408810030000301941d000c121400e40110007809150030030007800c10304c180d1181c0c142c014142410070855242c070803030700120350866004d41001d2210700e81c4001c144910066500b005425900c030940403c411190000c81c0d54500e902200307034074040c561b200940f09140c040c1c01054590545d1540800c81d070700b5086005100c80480c892400013a0740d81c000e000c1c078407844400001d032500c0b0400d080c107030420440c07a54459071789a9160a81c0340c0000c0d0b000b4a040d0f8111400d81c000711300d070a41c4007500202c03014004000440140b10000008c00c46001e50070b6154404200600800c4401e482c6c041e2640800505503507000028a1b103030012950034000660030040c0c9030419000b0806039242d0f51184080d50219003c0040140f060095100140d0f045049000b1805074803408295460445c0b102c40459 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 557901312 1250 557900062 557900071
    0x2718020c07051005040b09120d0c030906140318010605060f040510030203240301060803130f15090b0c030d0f0e010b041503030333150815060318030a03060e 69
    0x1091180b0388043c1c0c00740c210040b80d048800c103007115521420f1840004001500d640d812815900981219040e00c80d0700034244002c0a100c1c2e11500b8546440b800201c0394031030010a5081800002c0001c210810340c401c52401d2032004200c0081a0f06032a00d0200320140c000c020482181e0301c1c00b00d0144024a082480d22400340036614045095141c4a03c40034035410303049641107510024280b80c8040e903103081d00120040c2c1902e10442c0d5071030a08644d03001d16031000d80719581c14407403004004100712226500d2a80c10940303c1c4e58040c5841e0401e10f07054429032084a0781c0d2074610040001c083c0f8040240501c2d034410b14007480004a400c010241c85080d5002e81048030f02c245d1500b501c8000c1c1c541c0101c0ea182c10781e9014070b4001409826480c0383c400d07250300e0810440008e03c082140c6000f030030001444405541d480710b4049681e41c2ca41e10700340e5202c2d1301135841454000800388820700500704100610381c04405036200b2001d8180c049a0681550301c1004510000b03616640180b102c01404990b06422 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 557902562 1250 557901312 557901319
    0x2090a1e080d0f05030601052d09030f060103050a1b05100503150a06050a0f02011e0b1309020105031303020c09010f1a1603050306010908150105010f020309012718020c0705 76
    0x72007402400501174440103140506101022449040c41c0808000c001400042c16071400030708503c3d51000d40690708040092403107480344030040820340e2404030707a56040702d9100000b002a1078695450400080c80e10324001c0e8040150180094195103500380c0314107510302600e43c41d5407411b08030348010b09041440340d030600401480c0c408000444c3d122049461a003500c1c40c01e40401d8001c610708030f026064100d0702c0c007800b0ba1188074881194145a12401301da8108403003e001049031101e1420a6402c40c20000c4d000c00c5050000454031050b1020620840344280305440790b10072400300103480500b081e0082d40f043c0603088418001c01150003440310744807603505009401e1004241c00a0784035900014005c2c10003001001050250340140c080c1c03400341c04650309550302800581011f9400e08801d00c10503000440740042c5240300d60010089070300310001a910f01015211510080d030007102c0040c110081b190b8869070002e010342c00300c0000507039204010030140e42c0e16618546145060042c4d000b0511 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 557903812 1250 557902562 557902577
    0xd0504052e0f0b3a110108070819020f09030a0606080c010c051b030304050607080904051308071709061303140616080a1401120b01141302090a1e080d 66
    0x400350303100001413201120b40f0360409101c1c82411303d07000765280c0ba00d00c540020300340f010781c0800b0080c030b4240c03502107a1403c0e40c4065941d0307a01482240c01503070a40d44450780c9044d041c041030851f03410341c00801503820a00019840c002d00c002c00b00340750030900103003a01d00c540c0d2150244580901070191201030074007480c0000e26113001d501c2e8a0b89030040034844c05000e8508142130511a04d060040d140101401131405882c1d244074200b01ea2244d011042007407050b450000000d4580c13900144e41041944c00c084060b091000595868449099111600074841c0c014400e0260581c0d036000105083c460500060b0341980c070707614051200000d03204605080f50446010040380024040b02c03560340003e18030b881c5005031100d44503a401003180e010300400131040382c9d0010640454451030300070100d00c0703042c501501e40e98821010201c410b40000c030560152009002a9000090741c0181c054007800070501a01036075501d160003413410304005030046203942001c007008012028404d51100c00c081d0304040c903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 557905062 1250 557903812 557903831
    0x61d0f07020d1b020a080d21020a090504050a0908030a020a030e030c190809090103110310060303140706140a0b09091603020616060501061e02030f0d0504052e0f 71
    0xf0244902e2406007070300c0c0c4961200e84003c0d503603510300c144010456042602c69a03418000c000b0400e54a030051a004c01c60441a8612410f5440c03003103d1542c1c002d60342ea80c64a508190401c0040e10000d40121701143e01c6000c190017240e160001140190310140c4d0069840b510b81e0382c040d0940340e01c0715602d150b64105000e02e800380040400c04500200c140800d0030005112842d140246005400000c4d800007100070010040041c4000307000c00020b011070469982e4003000d046641565003600000300050080058130302c202c1c91901c00740c80c102c1d10802c0d011500d0103540c100d143c9981d104507102c030203840d2a040c0e000c0203400c1003000035030041e031030320007400c80f000010900d4203520100b4880240951000504000000c1e00c00c110702c4034460b8040c0d010710041d41d6030000101520303070b00c15124040c03078050101200c010780000100d03020140c00d04441c40c20144485900e100520703005005507150700483c40c2c0d100c81481114003074005c480c1c0798005104505040071034082190080c0c020190103500c1d042148 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 557906312 1250 557905062 557905067
    0x50c0f03160f082106091807030b190e012705070605030604020f030709032906060c010e1c0e15090906041b020a060c030b0a03060c0201061d0f07020d 66
    0x30440c2d40155400c4040095450300c2c3c00d56100f4004980405000303a120703000240c100212443c01410200d4004409449450340d10268503002d019003103550784105800c00008620f000c060f5442003802c0b180e00010703003a049d04001503656171060342300107075510402d10502d00d840d690000720f0704c01c6080241e803105c515961019079030305a80c014141840008000120721340e563741c0440c6e0180f040c0172610307a143c0c2400c11000c1d001d20b10300d00013100c0c00c59061401815000d190480b882e001480501000050380740e807418040b981c2d1003001108020354031000720b200045010002594040d0000c010a020103070380c0e0000a01c11842e001c2d07c240b04c1c820342e100072404200802c0c203a03a070340c20b02140d200340c107034031114001402001100c06252040581c00115914560007107070740005079020322800d110300500302c4000c03007c840d107502560350f0050b9000018400b10b011036004030324a0056000004404c2d440307100d20500b1900700d011011317010403400304101c0588683d0590603040901d90000703009003204104007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 557907562 1250 557906312 557906347
    0x1401050709092007051605060c030412020d0203120d0b01050a0801030b1503070906030b0a090c0e1b030f0115030b030309010507060219110f1902011d040507050c0f03 73
    0xa41d01e40646a0305038120526805820f110120502c400880e956505031038466100d07414444895046034105400140606280b42203071003c011b0a00514070742030400201c8055118040c10a0742c110807403807e5540142c404014000c0e81740f0300e0641c8603841b0340d98004400195180081d586040100501480c64a19040300c3c1681c107490f03122803420015911034a21001d10348610395102d80c035100f482000100b242259003c070f41a03d0240c0c124031100d03654600300302c0940740e4000c001800c88009210405c0b662440c428082d41102240d2028880f03807440e8240c40005800507625501240c411000401c220a404100e808039040e00381401d120300da45910000c2d8480c01086401414040e0004441080101c03550440710340d000c106103500c10104818030000d000036520020b542c114410b80f01180074181000644501c20f5400c1d696084012450360f0044031703410034070060a03140f181c641505151036603c5001c1c29100d815140c2d6a251510040c0c5807039403600d015182025000c0c0c1081044444e4410310915 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 557908812 1250 557907562 557907569
    0x516150e030d0f020118080409060b03010b070b060d060603060b131a04020a050906040807060e090405250e04030c0201020d090b0f0a170f0f0c04051027060c1401050709 74
    0xc020b4000041e11030b01380e000d0300300039400740120a0385007149001c00c5191000781c003e80740c489800301321807500ea0302040c40c1032101317004600b9108004d04c40700001403d46420320354083c1024001503901501542c1d41c0d4160340075900110b0707a00c0d444207041e081900700109a0403000c4042e0074140000c0141074000d550b0542102c2c0c28501458000030a41c0d03010340644200e0f40780c40c04c042c0105545e02e43e0b07850042d441d115507000326400211107152151152800d124400e0042d41c010700074144c81d06901c07070ba042c12140c3c2e40c81c80070090491003a001130300343c101e081c03c03d2080e4026281d4001902c0244002401d0041c81280c01040c81011881480a07450240a03104503509950100c0d40d19400340c84d05031103008070740d0b00030000d0141d480200104110821031040c0200d00050850250f5100e84a400d441ea00450064640091032820200c41c010320074038503250b840c0c0b1203080c0707080c400c111220f1703d40b0050303000d400220100e0320b050a48004c00c1041a40300b03040b804038030020001803d103400c006008510034030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 557910062 1250 557908812 557908817
    0x4210804150c1e020601180c1d0418050a06050f0114010e03030c19150b060a031505040c02010b0a090b0a050118080102030106110606030105060a170a0516150e030d 72
    0x368448007240c0140280c1c034040800202c3c1c440d00061141d0000c1d40c944090240540780140e040601e041a640c9000d401102034240d00c0c0c03203c2604d22440c18030302c0484442d41c0b42e980282c88081c501e00d500c0511100080e41400b4402a114001c0d840c1405010ba41c005044a414002d02c03000401640304440781624114009282842d01e200c140c100081c9940a81400507140b40100d10b400040144503200c8800342d54801c10300c00c0001d071004108102250450a08142c20a60170003040130720074480d9209031808820791120401032502c950101d000c4820100c2c030703080940e66881c0d52405929000b87c08400501c40c9020602041e100c041c04501c950240e40b16031411300281e80100400d500022ba811005422000d000319125a0344000c01407181902c80100c208502030707940459018141070140a00c101e40c042c0080e00541e1801c0115031007034aa810301590700740200d601010002e0002e004421000003000d0382c0c40036039400c0244101d900f04c0c4d81c40080c03081c00740d5600e84071301c6ca860202d203c9030a69010b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 557911312 1250 557910062 557910071
    0x10030c090f1401090606021c02031c0207121d0d020a09020a0207030b0c070b010b1204120c0503160204050601020a05060a0209042307030b01140412020312030421080415 74
    0x1101c02001a207180b000d08541201180c001090010f2030394480012140350350300b00d0354280004101000c0d0307070070b41001c00d10040c1c0003000407001000b0300e043c800055840080006203018400d403140c0d8440001030245a00040b00e07650002891440a121803410a00855007804034854590000301080034074490302c0c0c1290380226041f114103000348055002960044204256447e0018212880768020b0f05c00700c0d80d03200d90f00004a0012141800d03500700424110615400e9183da4072000092920040c2080400c281458240000f030070a00141c5400c01e40c4600c160382825441c0b04100a07607000400703250455110503504000301f44001090b6400c07452a001c0180e60f9941d107404100900230300030607034250325800400d210b070f540d40000d40c00d403240d00c065508100b407180c6000115840c1c681920b240d01000003e10091000c8428603a002d040907100070101d51105c04175610320307090782c0c008840c1920f000c0311481034680d0420961b03100050070300103407a0020b01d81ca46651941070f500c01049030000c200307544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 557912562 1250 557911312 557911331
    0x50120100c0e1903021306150e0a0803040b091c0503030c0711042c0d05120c090904050f0d03090305040e07090305010e0c0102150f07050c0102040909060c0810030c09 73
    0x5182821010740002e04180e601d0f520058410881000c0c51204901481c80c45000c2d0032242c4082c82030b9419941d0030184a02d40100091040b1480303e240e5425aa101c0c0801c00e0004e0202c104200420041c91b0321041e11384c0b030b244038400304106111603641c0142010600e40703030b10001880120031a60f001985803403d076142d401c41c3c140181414981a13080e0b41241c5400c6e104085041500c841030b6001c0604000c41d00301d4000904465180c2001804041c0403800500000324001c14000c0b82642c4035155000003420800c8200c00220603103c1980c0613115604200000c00000c1410b000c01c2040a80321306042c00700c4621340e60002c001c2e116030702c540800c5401a40c04501064803c8148100554100340240304c0368003840c80450310794118407016800f6201c1e1740350401d2190b111002c3c6d94461441c0c03210a041a0340c44210540f06039105440402c0ca5550030880401d0443c960700c48e00305864011440001c500301c02000141c00c0a074003500d81c0307020401c6004100002000f941c541001c0e18034116000c103000c0032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 557913669 1107 557912562 557912567
    0x105010f170c0a0605090d02040612020a081603080a0e0d060b0a0501081506031317040e060301050405070302060d0908120f0106110a12050d05040c050120100c 70
    0x2c0c0030b083c1005050300400142884e060090b05000480d0001c0c0c2c0041c00304c0d40c2981103000303040c0e040072210055042048040d8050042c0000600441c1b4102018990041c0b0911009006440005800105611076061000c00c07180140a40d00304c1160343c074041028007102c484450080d0450000016558030500e20140901c810101501c0007001050600205900c02000408030710024900034000440c8401e0f410280200411156100e03820010800800080500315600c81c0e8144001c1c070000c680081200801c4a03030482e205540e540308050354002500f03406e00f000c0c05501d03002c03541160340c01c6000003a07407041c0b425031803100c92a03886803801d4403417008881d44011940d02c95101e07000041c0413941c0200540c801403c02e60b09000e4105220340a99404850403101030700c1c030103c10442941c2281c9030095800d50f00a074600300901064110782c1c0d0740410300c0000c00150321007808400050 = true := by decide +kernel

theorem cover : BRFrame.Cov 557733812 557913669 := by
  have h0 := BRFrame.cov_init 557733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 557733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 557733812 ≤ n) (h2 : n < 557913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
