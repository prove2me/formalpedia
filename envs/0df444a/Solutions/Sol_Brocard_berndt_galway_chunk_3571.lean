-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3571
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:00.908218+00:00
-- url     : https://prove2.me/submissions/5aadd13d-af6a-45fe-98d1-c36cb799a8ca

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642086330 ≤ n < 642266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642087580 1250 642086330 642086339
    0xc06010e190c05030c0c011506051902061302192106050c0705071503090b13020f03030a0f1d0d151104080606060f0702100509180106080609100b0c16 66
    0x140c581600542e0b0001d1001c0c400304100b020341c2d80040c807041654600020310b010400041c0720300c4000951084003c02d0000c80c0e550f28604c8410b0340c41c01c0c02c1940d44060521840c018400d02c2031900c00c000061f006035604080400000c0c000201c082c043d00c800e1120400a070030700310303403105500300720300007202c055003020085a81680c01001742ca80e00d55011028284003411700c10400300300d05290061608040c5c0790003030301001c2200c00800c64012045036040c01010b00c00f500500c00d21600300c040190081d0b00800800340b0007a4480d2100c41b0001e10740c500135545448488110710980845075000d43e100384803641c1c00080044240a004507038101d54030601c418444d441d001d0589005a01c121000c0c1d4002d440060603a24020b8020300155400048281c20320500b90045051201070400c00350204c0d00014008005203030081c10740910600201c1003444540c1841f400030100300c0082c217114054440e0a004ca100480401244405400c5400406488810491015644443da84a4000c4002c4000404907 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642088830 1250 642087580 642087631
    0x4030f030c020c0d05010b042309060705030f060f0411032a0a05130305030a0c050c04093f09050108010e010b040509040f0b0411010e03010e0712020103020c06010e 72
    0x15084560750043c0552403504000c1c018003480101c0111500d5507101e0b0b119403d0358851203801410619580c5a182480091040418030800600500700f0380e4089400c01400a0f807200c11240d0104180c0a00c925640701d4101003003c1074841020300d54050f00f800244002840342c107015520417406140d54a1950691000105019001354216a4001c0007000710303030a01c82c020b02c002c10a500038070340c510b0401c607504d480c1c0500356040104900005450f0f10500010300c8002c101310308413450100c1d0100042d80072550b44000800c00c1d007240d800515442440d25480100016034019442d211986921035000014001030040b10340340141c40c003007018039001080360f1540022460588880314400b03482d0a007003904210001c0001001181c521580144a4000a907540b185c907000364441c170707020741030085054009010550001d060701d020b41c1c0b42c102005401a000580304045844804070143c0401860004030046d10442e8480c02d400c0c400c076400080d00c8c801581c14944120103003403090310201041c06404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642090080 1250 642088830 642088841
    0x3011715040b06130917130302120303010806180c0103110d060b0306030f010b030604031b05160e0a0219050a030605030102040b04090e1902060a0323061f0c0f060e03030f04030f03 79
    0x1511000c4e08402840303c0e1200c00c07004000f0154800c0500420650313a0340040e00001c02c00d46032b4440380d0008001000340403402c10105401480071010101080c0e82819565614504007200c1410191944200034482c41c258045440b098104402800000d85a8080305282d900513510540a44071314076140d810b00070107101c0c2414241c001000f802c8240c450f038070308680159480e0030340c0b020132100710612000600300b00701c1c2807503c006080149000901d81800c0c0707160710b18014041c0340b03818010001c00d031105540aa0200361000740707040880d150204044201d000f00200c0d0406a015840082d001c01e602038004082c000301e580d5007500340008400b40c4030541c1c0303e005040400003940c0c0151103520052400902030540e91070f80e03190000c1d0f14000c2d00c2d901039042e40c803108400c01181300e80003480181e01700710b0007a06100103840c15a0340059984a030091045002d92400361860350030350b0f5040c0401505400c00d407101802e4008481e00c0f0306144000b400c1070342080d2000c401141e00040400b40450203801035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642091330 1250 642090080 642090083
    0x10906020d05030c0c0f061f1215150918230a03050a0201021225020f07050103020306031c180503060105010c0303020714010c2102030c03011715040b061309 69
    0x780b40c01e60b1225201d2100030342114030780c0c2c05035005880750401100e0307007008080d00c1090100100004801035442c0e01c040082590021545405201000004113003030b082180c914150b820400100b901400080c2c41400b591038004a201c5414484101071807109000f003d42e005020315000300d45005040c0c3d64959001400340040c29a400003c11000424080c40140040d060b2500015143c0040c0180301100300400b102e0303011140345036801d02c10380c44030050380c1034020030b45500003090203010210880c0d0781c51300c60b0300c605030402d0303000000500300d178806000d08440401708020729a260741121001802400c0b14a81c0c0d0880412008400101c515000bc0d80700d040380c6040c0c40742c4000914603201100613603c0407505aa000c00c000c04420501071007442248400301c026503030802c01d917506010b42d50800c0d4a503980d19851900600030b1000380c1c14444110781c1142c1d260403a01302109091034006003004ca40c0ba00103645195007008002c02e01c64080c03c02803142c0800c54241400201030a5900101c2d54400c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642092580 1250 642091330 642091337
    0x103020a0e071202120103030e010305060609041505030303160f0504031a040609050604050c0f041b050a0c150f0605030303040b0103020112020405120d09050102070806070810150e010906020d 84
    0x40810600c001041055040b205030701e041001145080d009074140e07400741d42040c0714140590010024194000c10030b130802c01d024078080c13040e41400000607070580a40c21074075100d91303030301c841c4a203c80d4092950b070401031802500b45ca450f491300460214402180d036a010020480c10043d03145c0b1f440c0700d28121010f61790b2102510001002c84c00054044110003001101c0ca141da4081c000c000c503104100c19441244a00c0c000d001c078044420a2082c00107900d15010301407400d000c00344d4508600807200c1017280c8172510300507032078040c451800c0391250b8103144040d0051402003610300070845560046106e150f989142480710581d03410038966244000c44011380018503030320040c0010b601c43c10365080c11003041c00c1d025042c5a2540300041d2601c00303807108200c2560042100c3d11229401000140080600340040d2002da031400242940301c3c14024104020031002900050406181c049210060902c00c404801c003c8214100a442031452510035804641400000240284001914041c0c1d00701c558 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642093830 1250 642092580 642092599
    0xf081b0f250302041505010e0a031a06030a0206040e010e06120c10021e15010e0c030c160605181e070306020c030f030c22061407030c021c03090e010302 67
    0x103000c5054100c07644010078500001003070010142c0c0c0c1d18010725220589441d02c1d00e1025142500141c20807980e60780300c41c0640710b544420000309626054154444949034110400e0342d443d680001e0400c0c05141c0c0095000304081800310756683c1240303285050b41c140030001c4d903494882000300302c6994111f0b81c803008582c2c06461894003070300b03281c0424003030f001c520300444201c200e800e504420002e005d081002841c0d1312010054280d1002c3c50141401007401400c284994201000c114510744001880000611743c0000d0700c015030303402e45411a98443d0407005c104501e04010040d182202610f04803003519106011000c1d401c010b025000046c480300000050002d20300e55a6100040d40121408034214081807114100307100c852030095100f010004241a1f40d140c11024480b443e0040180c81c018914215805210003a04455010046040042c0143d21101249022204201074050085d000810f40600022804a800390307400b1003880380d282c00d40416194109089040c41c24840654000501ea = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642095080 1250 642093830 642093853
    0x4110708071109250e03060a140a20071406130308061f1425050f0601061d1c030e0a140a030f030519090e0a050f010311030a0f081b0f 59
    0x1c407180000c02d207a400c280ea14601500002410034101f2949a600e4940b55038654100e45881c0d1100d907031100c0901400c00014052640c00c1c8042c0c502cbe00c010291a42000078078030300303000111041c840c10f16031603403c46510340b07040101c550320305d005143c086010902c0d54020903ca460110f00e00490191035000d0807011301e00b29982101c05582c198103086e4080340802c00a03000041509200300e2031203001800036440780d0b882c0b600500e000d424042030300c443d4000000500407254040d6003601010500304210b00070b400800005680c0144010403401d03058020f9585900305508020701c1034003144200d489442182d0758020b0f248103003180860241e4000c50700350051000442103a0070b400d880307000e031505a00b403d204050a0359000c03070303480c0c1d072002041848104108558840f8603082d4807848050081c010360401c2c1ca0911292001800010180c040300099600c458a041060b601d01540200340000315184604005000e035000700d02080e0340000000341002c50120016505280f0b030b44240c000c00c6020100d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642096330 1250 642095080 642095131
    0x131d0601080604090f060b030c09040803280e0601061112040b07050c10090810020405090415021c060302090610050703030f0b0603010801050a060503070b0a0e04110708071109 77
    0x2c0c5803543c841d0355407140d80c000c50181d0b0099801588140d500042d5001820101440c0039017240180d840f078200306040000092081003500d4005090780140303035211070201401c590b035135808843c0090300f41c5001402621548000343e42812100f00d91205451510112101c50702c0b00e81d401c0d42c40c0c01c1c601e8104820866000850000e1a5444c000c0301131f41d16030107a520004404007000e0b0100f00011b10790802c1402603050501615002c12a02d4400318130b810b10745400b203139130100007d001400e0b0100020881d02284400d404036075500300303100d54420748030426011000051580740002d0380101690000a03241d810090040c8082c0b03502a22681d003864070310b036002c0300500507e07074542c8041e40d2139408204032511180059806052650004281440c2c060101021200303d940807511035400404200850076001c0c0450f13080c0c00e49450451001d50044020501070009198003e00c215030019502003807100744005000d12601c115000001200d103101007024020054502c0b803001480c50906410401c02c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642097580 1250 642096330 642096347
    0x4020f041215110408010b0306070c0219150c050c030309180a09080708120a09031211040f0b0403151e020a0c060507030209150325050c0d05131d0601 66
    0xb0560002100ca952545000d0980e00c0020050510480124003031000410a024806010f50300f60000e11851504104c002c024402c10039019004da00d101800c2e541114000b41c110010b4400d92010044070035480700d0003044140500c4080c0ca1354000c4103007a080600d004412140441c40c020005408400305102d041c0300313418054403000702c2e00e68400c002c00001e040755015000c041c0c0035a031419200c1d402404151144040280030341c0b00d107454070380396400103500640440003000099200280303030303000c0c500300c024076110b15040826100744014000a6900c00b080c010310550380708c1c0800b000c1d106150092102034451050131850004504c4c15501d006002c2d40d400f40c1080042d51910290307038082c64807294120b44007942c0f0080041c0e00000d06c1d201034106a2111000800121741c554a589485861031a041817060f03200c500c4102d01940c039480880c450303c10341d0392403030800e0140c446400c4540f8002d04143c0c08403141411030300144074000b82c14104045d44e02081e80900749844c415680300c40c011543c094 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642098830 1250 642097580 642097583
    0x40b0d0f0c0f0e040e0304500d0203060a02030907030c03050a020a170601060e1c0b0a0c0e011b14070b0309071703091221030f0903090109060e0f04020d1a04020f0412 73
    0x11441c1d44103584022000c800a40d8484103125210900d2400f00824180c032307201c080b034060040d4142900d078030041c0c80005078103a0008502400503201d80742c10040c0c030b041407031301d40c000307400030b202c05ca03000c000e12001158a001c0c00d4400c0b00e81e4000309070350742e8121007003d00c844090f108039048000104103850042e000100c440200034070380f9101c0c00c100d05140e007181820b2002070700c29140140c100210024a0702c2120740020403400d002020210b0040024110380030300003100c03004924240c410080008013139022100c0840c80054999070be440b0004119181c2048404441c0342c42202e4000580c2c188106c1c46102c0d402c030300d070040d600d4010b4410610441c0e40c0c0401740e0340f00901c90400b48001c4440e4050190614041c0c54503043c0d66414004072001046001500110741e64004020300b02807681c014101404a425505000158442510006607002081064542c006c0d00001c0d49000e0300807558040108044000c0042e10304025030000d0004034007594200c0109002e0400043c031804015001714240607 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642100080 1250 642098830 642098879
    0x80d0f0902011d0612090105100609080c062203031e03140606180a0f090e07051c030302040911091002070b0f0c03070c0306050f070c0503040b0d0f0c0f0e040e0304 72
    0x2a45c0703c81d070400b440c00101c030080016551002440b02900200441e47c0090465280140c0101e0410341c4141d2541041c18100f03200c0c80000039a980000c00a41c20000e803000303015003000140d9a20f00317015000280390840f0744c04007100302580d114041c0c003a200d21010040f80310300b404074079030b42e240a11145074841d0300020507080410880f5059540e809540300c2c0030380203070001000031528101c400400d0765030b25280c0400350341158030103100c203403504081c4001035042205451800b01441c1015070091140e03800002e5000d05101c1c403a031403401d603031004004640c4244c501803140001c3d4401261200d0240c0150400c1e0070080080b00800080034025040c9043c0d2042038a24003101607940d0704021544d544225010350700c40c410001d0012030070a910758001501e041640b04010140d030355580300d00c158050080008800306500040c0070140d07202c11a01d20709220304000b51784c0c00703003000351070841d1a00c411030005042e02e1010109090a0080020f8403041800440c200703401c0046241d54444440c1080c0400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 642101330 1250 642100080 642100087
    0x40b120106031b1d130212030409021902011802060c150a060305010b0102030a0906030f2309060105030109080409180c1d01090b09041112010207080d0f0902011d06 72
    0x1150000e1040078000c503c00e00d41d4920740245124015421005a8002c0044101420014080c8004030100795441540e44032030304c3c4000341910000708116522009900644008100840d110782c00368014945c041c00b1660120201d090008101c0c240c9080301040001400c131107181070014105000030707100c03c0328050140c4015200c2599800400f541c1100c85481e0781c0e84540041003801020707c694000c002c002c4c40914948194464007070140302051088208140e950041c01a094025038090221481489212200310b195082c80960a400a0b20254600d002c3ca000010b0203141c14802d8061450340010b846040a1500c0700c0500104020201090320a5120b624070b0005505030f101d100c007412a1011070b0311003003c1da41d99541800016000f80303490501c1c10100b00f20580c1d808403030590007503004041104070449540818444288990000b40544c00070803003408100c20540604030048801c0c0c410081d016944a0751130650320103840c06400b040f1504803400c80780003034a0b1300000e0a800500054075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 642102580 1250 642101330 642101359
    0xc02041b050706060819030f09090c0e0102100b0f0f0d0611070b0106050f04030605060111030c0f0105060f220207021f0f0f02030a03020a12020304080403021207060905040b 76
    0x1149140351040d00001140020398400b00442c1d8071510340500411402400f00c13030101c0c081800000b200c0f48018003030003a1114406a942d00c1036400c1c3c0e004e00322070340c0b050000212807507019080300c403140c0c10b841c0907010f003601100b03549180c0e110f14038034070400400e44040d850414060040703c0c841c1d20701454100307450302202c2c008503610f4010241300c0f4412000b0f0603a00d030b06a01346250089410b81251040081c10400641d502542034192410750b500503d0008054681800503140c800003c10440441d000103c0c51003424040442d0210b800c95091000380010340e141010001840050100d065100d04c005551060179100000b081c88200c48002c0d0052420110b43c0001701c04100b00390181409800e1900040440c540c400c001e00001210750801840020061101035243e005a04101c410950701180c15a513451080c01428002c1c00023074011980da0074142084010360f481804142d008240a030b040001ca4440013601b0011182c0c15a1040d40c1c09083c401040040c1c00405a1150b00440c3d00d1900c12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 642103830 1250 642102580 642102611
    0x40b0f070e040f0219180608010e0621070602030307110105131103160b030703110c0a0b07090306050103050606100f09060f0c06020c25050f240313110a0302010f0c0204 74
    0x117503800d6840b44820880c044841c003400507444d030070000030421000010082c000c94101d456401101c00c841c04d1400b0464102201d035000b1a511282c080d9100c0d040e0006105500440254080c1c4a2540c071a6003200750124130500361601074508034100407086e410b032408281c0c0b145060000040050903510020740c903640c00481e00c902a000704405020010034000b2054062103605070350294131319101c0c00e0010548050341c0315032803038801a104000000004ea03020348100c0b540406543d1012040009503100d0400c155102403c0b90210300514440011030059405803001d51401221652884000ca091120072580100400068020b0150300090500029900c0c00a86140325200c0002d2240300d2080402c1d4982d40126500e82c034130707444488010b0095480301e080105880c0c000365450324a03109201411852030f800c2400200441c0404000e001103180100c90b1260300390301411a44000c4000b40c010003410a206100081c04074400619103240c05000d001c0c183e8070140004c0c8005940d510b200c0340c10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 642105080 1250 642103830 642103867
    0xe030301080c01090f120210020f0a0803090105010b1e090d0c030f02040b011b0605041a0f1816180902100903060e010603080702091f030b040b0f070e040f02 69
    0x51100d500445009802d0f0359000035420000c003148100030251915014000030820800311020b406812013400803080c181c020800022140004021507040d071043d428111040e03003090307a43c2c8481d5400c160002030440f1210090303443d290008000c2c3c5178000035020050345151712000e181c5800882c0c02c080c0c0c0c000f041422002400640c02802e00d0160009248100303c101c50303a90310f44505001003500c41000c02a0003000c4441403e62103940043d203622203003060101031441c0071070f041c0600c4029003001182810b8000a501802c0a004145031030b0044800e4507840702061003e90003207000b43c0c5400c10400007400030314141c1d00e000d104e000644021030740102c5e94107204a1032141c080741c5030040800c100704092081c03240b42d44124000f007040710300b16a00c184081c801c01d00041c0c812407240c000b24005008440000103000c8803211010081540c030718224100340c1040f0b84c1941c8010711000040c8180c074400c48281e1280e40e982d0f9502541219101c20400180624155240d0301642070081c00220f031807030200d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 642106330 1250 642105080 642105089
    0x311031309050f0c0d0b0d140706020706030b090402090c0c0a060c0e01030b0a0b070c0929030102030603070b0c0a1b03060e0d0c030507140102030a0506040c0311040e04060e030301 79
    0x9812420303040c620030205032070b0041c0090304030100e803c0400c6407130003100c020703110350302c001c44004580420400c001641aa44040740030b048030100c0481c0311030000c03000440340b003150700383d03001c0d940c01d035075210300541c100c680030041c158114580c90000750051a00403001940b003c050840c9174101503045000c5072a087c5071080407121507075583c00021840d44c2242903504598801d00c0c0a0003110310300404a0b243c440244900000114041050340030010030310000d001501190508010b2921344030320f08480c10a04900c03041c43d0000241d003401c4a8201802103030b00c60080a00104081850308040c0c88642c0d1103a500d80885001d030040b590000b440d00542c00c0243c4603035040c4000c00f0741c00c43c00c004007141c1c500400003001d64000c0c21050441904507419070f500380e80504200391501c2e15814440000418401307410340d554400400c0141d0448144c2c03111340552800d0750100400c0007581415421200200d620000018052004000059070303140d0041d4400c3c1324100200340c1030f2603a144e05246030800c1c1c02 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 642107580 1250 642106330 642106357
    0x60203090106060e311e06091118120309030d03051f3b090a11060306060f070c0510021c02060613330302030c040209100c031103 57
    0x500f0056298040401e68408104681c4802000ca00c01004110741c43d400032030303012225960b0304510220b030342036200684052443d1000300302e000c1403140400040c5040d02402944628044601c0e000001020955903180c0f0100064103502000004100340c8185203048800107110802061041e034505024400c4003c42545012407942040003004071200e050701c01c00241408681800c0203d0440d9104000491200e24044005000c0125603450440424500c0f88003503910501404030704c1d0000618400b0003401201d00d141c40703590280c00c100c1c01c1e00c401e944d419800030044c000b50000304400c100624016104041c030914031a55000407070541800300c0300080168001202c2c07071128070034100003081021100c1c8090290391401d200041c02502c40f0440c940c4019036650300784404036004903001482100f01d0765032600c0c201d04001100321104070500080f0701a001d07041c070302152810180252448144010903002c1c424005c2c45044402402c120400e50420101e0010301040e41d0f000d000405004060742c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 642108830 1250 642107580 642107591
    0x902040f020414030c030309010f1725020a0210200106080a050f01020703081b0d1e0e011104030f150606050307170f19060b0d0f0c0504030803150a030602030901 71
    0x914a01c50a40e840308a0f0b4003070f4000d8915034400c1c0c0c0e000b01c12a10050070034200300124000d8a00c0031a10384210400c003000081c250b6081c844a0a0704020444040850b0360141d4100c11034844103e8580c008110f000390000c1d01003170006405401100000c080141403240754400069605030242900c0381903009820b16004400e001c41031000c14880c458810307550034025883d2080f560b4009042d02c00c003c108125400203140303201c54030614035007215405d20709880103200040d0621441104c0c00320a4440401715072405900030041a018002c2d0f00800007c07601450038240395884410101a029004035501000b5040001ca0703a16035102e11405007485694054581c030303041c0d1001e0300b01c90a030070740b00360f26000308402c02040c070150840c0c56070b1105181d14604803035142c21080760050000380e08013101d00b20010614102214055000d00360120a65105000080a0301e805031a240700307601002d0080142040043c803052040c20402c00c400c40090300d001800d55483c3c0f5100c0c100d810030303a02e81e40c040c1d450740d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 642110080 1250 642108830 642108839
    0x70c030b060405060105070506040b270114062b03141603030f090b15030709090809031b090c070c0504050403050c150919290711160e0a0902040f0204 66
    0xf0320503142d0150081c02d15038a0403c9980340c1583e104402040200401c41960010300701e840305407000000c0d10030000c41541040aa1880c1c40d001e0f1214201c06000002000c0c0016014581041d031003444982c00c0803a04401850000002e0300440008010313014012008880c00040340c0306801040c0c50844600070240c40d42e204d1400030140d420034120605514101450301e4041a0403a0290740c1204804440707260080c0141c0c04a814540c0a62080c407040b032402c2151400e00412000030011000110700b52510031085144030808403658001c01900201d011300024070000440000386881401404000340f01940c500c0001c0c240c0f44101c0e070403800a4001315500b414041c0810180c8044440404846010b19046545542daa0b503000005082d11400041c0040ae10140f4081d8100d05407202c000940003031044018011201d4095400d840090311481100d0311404010640142c140004e40507001070342c0c50103d20700e0010801a10b4002540d544072200c0005a58a20031f0b48404a00c6000150300d80307180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 642111330 1250 642110080 642110089
    0x2090c0a080c04060e01080615030901090b090d020a1410020307031a0103062306070b01030503130608010e0f090f0618010c1d09180f0705100c0201090b0f070c030b06 73
    0x40c00c00e200404040c803043c46150f8105d41c1040d10150213103402c082d20380d41c600000c2c03108030780c2e440341c882e60100000034085506019080b40c41194000c0144260b19203e0045690356440d00110000040c0c0046002030005418032082c8010002690110b07400e008603030b4948400c0785c2c02500d54001081e5030322006800212211403080c2c00741c0e800d00b41000307424070b040381880c40c4403150072156141d0001060f54614580c0c0710010350700c42036080b5502540c6580c503071410603500d91104003455076040d002d2000245040c0b04e100120b0580d0b105242c8500f00342c59143e0001c51a103c058102006070046901e02e0f01c40d480c0c200030661040548025034112281951800390031590401c54000401c10020a07182e004901a08016101d00d030507248030086560301842c80700c02c8050010001c2d828003820f0b00c405aa50700015900c02503610807548150704000065098880300c2981c400203001c51078004042000b0042c08010381427140859071300c03e2900307919984070402d01405070030407a6115016014024076092 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 642112580 1250 642111330 642111347
    0x14010c051015150909050601050706240f06020307112d100e0d020f030102093304030b070c060617030301181509050c1308060f0603060601050a0309080702090c0a 71
    0x3c50324001900c200340050001d100031000d001e9440c1c466100c0000c01d00c0350348100101c440054101504103c940300740d410040c0c02041d54004e0840c0440319480102c0c9050a5800003801c03a01c4e41d400840ca400c80d15078403007030001400300a01c2d40c408040618a0002d251040548400c0404820741032a032410b030408000c141c00a454400042050760100381c83d0948a02040035001074040f124091403400440c00a03019200c0c0c2d0360301a8001e1440149c420030b4010f100704040350501324411141010308001234000300ea002e944406000000c0c04008903503410701584082e9a200d00580010402036101ca846809086000034600c2003548008010071010f10030108241412611000a10030b14912841c0d041040308140034440100382e0321804030741112054030171100f80006804a821107a44e48951040d141c4030100e03a21546129a4170000700b003450007207141842520142c5030303582002e14454088004183c0e01104413881401002135501503600c0804040c807a47c00204165500d0300d0b0b02c03d0040c0b81c00c5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 642113830 1250 642112580 642112589
    0xa060b01030b06192d0c26180303030609131b082404030504030201212309060c18040b03010906020717040807030b090a0c1701060f0b0414010c051015 66
    0x3030a52410801d40c060300e160450b50245c07518120500001e01e0801c4844504031480e05201c2c0303068080c1840d001e2900c000a42101050354407542a455585814980c0300d11040b9090b950203560440041c0078110280c64040580c0c0c01141c404110032208240340842c1e80403904110740c0caa0080d2038000140c2040024600854422030300c0100c503003069034000c0c2075801075000090521400301c0000c4c024800c0d41c000c00607100300e403040030310042c140061440c402c02c2e00f20f01144a0407c00c10002080c14038005510ad00a40c90000d280c6e00c0d21405800120701540100c01c3c80b54002c2e10b620364900181c1e001d0162680590040700016030743c0030303a440d04030b003407a540301c048000c86141804204800080490364000700e0b50031850700140d540c1da56100c0d508108001200a150301003444c40401c084803400040809450307a44000c002242c1c0380c18548808044500c584a04013108200502c0103521080f200c038240d8506041070780300b1900650350182420000280c41122035521207051a542c1000f1a0910041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 642115080 1250 642113830 642113867
    0x303061707030c03030305250e0103050a2f1e030f060108011203080411030607031e2d18110901120210080403090b07030503091209030a060b01030b0619 67
    0x5510710380d60f404060909100203002c4c19a110005280303002000e40c0e8564003c158003a5040a07500c2a201030007080c038018089002070302d06000940c40c00c4191294087c0e1010a9064054100311a024680300015052804419030f00a11403585213000311a8110102c83c601d29920b40c0b68508110300640e02c0400600e450704111041004200030a0994800c980345a00740c03400c001d0980c0e450a15000c02054084801c0d0144a244108802680d0507402800300941c3e86841e6904145c44141d100269500380c1c050302d12105039a04201c0b10b03100c080c2403140000c0b0301280080b6110b60f020309400300c10090365505a882c04e5843d17900040510303000e25241d000d0200c2c1c0c4070f105c0303c020850700030401d1511910311034024031403103001090500d80500d400310020003922440703641e1341d042ca107001441500140d031148614401c40101840e4041c0c41d4054620348007000d0f0061901b0340c4a501d0f100007422421150702d05055484418504644680c0020201c4140e41c0262812004290700c00030506400c0d0001c4044c0b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 642116330 1250 642115080 642115093
    0x1110c0f07051e031f0902010806090c1b0f0303010303090303090f030c050607060e0f0c03010b1c15020f0406090602161a07080f041706010e090606011d090403030617 73
    0x6a560b03c140e10099802c9a2200441e500700b14000c64908070704040c0f00c001d01d41202c8003000c0b541400703401c8104081c1c403ea0b40d841e80d98484170709105040c41c6c103586108c1c03444010301a4030342040c080e0070f035041c103c0e49040807a000188004002411070740281c10960005201c0b24060090507003048640d030041a00302c0f0f4800009103145c440041441c01030081a219800c00140c0070184411508540100810f035030a03200e0b0041640c0c1c030544e545a488100303c1c000d5003001c0d0410b0192801200c4410700d55480c0c24170043d40d050686e258156000c4144040a10030385c2449400381a0020102a00c060b0a140d00e4603101241484c50281c40c0ca20500000d03c0e034a0401c200c20300421001c9851a9405900c0c03200d1103450b10010714111540d80220303002a0003000c0080340c00101c100d54620516170003170030002500e5031640c13030b40c500880c800812100080c55a01080100301554407418107100a0107503400101d01d802c06401c0090245035096409400280d11141c0500940c0400010340d2078078450000203061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 642117580 1250 642116330 642116339
    0x3f0e0307081f020a050d1d0f072420060406050c03090a0605060a03060f02040302012613030909050a1407111b0a03020d03050c0d05161502040801110c0f07 68
    0x880b50700140409012580201c0d0200307413035008005445000900c035200b0b00c4084840601008040e041107070450452003107441500c0706240109000c07003642e0a9041200c2c101e002c220500707402c00809160b18041150030803584544998040c0c0c240000c601d601d001d046207081c10b0400001399400605075070030203513041050100412000600355001913000c00c02003803d50b2000009910701d0031a5002078011414138101d4203110155900500c160791003600c03180525a0001700c0c003107840d00c2c400914130036041000081640144c15082e0a21414070034030307240c0030083d10782500360300fa034109894912942c0d80f610826401c50322a0100a6800a521318001303031200302600a295445c9850a54070684400c00a8560129140c80e4407038000ba42d00030b000c640b014140703481c0c020320b580e011400f980c0560180914003020984070341c0403558501103045004011074040c1d00d4208800a00e000030310f0050703508010005140b0002e0260081240b80301e40700d40c0e1a580ba2104c600d06111080149030940d0700000c80500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 642118830 1250 642117580 642117613
    0x13060201050720030d2a02010608060c0703120209060f070308070e010e010c14070b1209070f050a05061605070f030b060402070317070302070c031113093f0e030708 72
    0x50041110445c045045040c250703408040407000e43c00030b50511200c4c07280c1402c09405400c810122a102c104540c040d5440b000e04d100300c2d02403407600400040e1000d21400211603075402030081d02e080146003a2900105c0c00b030b83c0c81c2d00d902012048001c19107a50421450b240c0000c040101e440c0d00b800d00c60141c0c600280024541d0a210100900100801c145000d04400c10081c0c40c000d480e40b40c0e4190360301c2d1500001107c00e500200c0710030260748200000415070002ca001031608030390019103c806d61904040c00c00c1400c0d005070207013100b100015150b1001003801041074800034820031501c402594114100464040c1c1c0040600e8040d82c01007182c400083d600609260410221344e00303410160b00d6030007040380a4495260041c0400025038800710904c0b40b105410b078080d803802c4171250394203500b4829142c02c3d981c00a001924440381c000f40742e40168500ca405e02c04400c940c003032019070341250070041c0c0480401d8150b0080091006049901d150808000307903005004488c0c000c160075950b003110384 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 642120080 1250 642118830 642118837
    0xf1424090f1c020f030703180609180f140f0901230703050606040b030705030109050703180308060f040501141513150c0b1503012f0f1306020105072003 67
    0x2c0504681403070b401a014400d0010007180c540030310949130340d07200501f00240005101500c400c0030b89a40080003c0c0d460007040c1e001c1c216510704817003d00a10750b41d82040c0091075030b86506034001d078130303002108600c60f80c1d032100c503103d80d680e00706010b01810300c0320342242104e40c10030940111415003225010410303035204c0f099500c0909454003103200c0d501ca1010401600495211407000722012050105060700311020310305130303940100100301d1580c45440031402d82c0c10038017680039a00d4500300d413007020a1042c100268464005001d00c0d10300034000c80428100d5100741c0c0030401c240e00000c410030580c41d1400c1030305035100e000d40100e801c08001ca1490010418544611b00444140c180700012080c001d5211405c019003080342c8034520328001840c0c144084801130030500c00d5207040148210b45000c2e200d402484203120801080390309202660b90340c0c035800050000403030101804030024102c0400610006400c4d82d50001c200c908103010b020b003252001d20601001e030064800003d056241c00810b6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 642121330 1250 642120080 642120103
    0x24020906090d1e06020a0e06030403050d050a0216030e18010b0319090233041d0903090d051e030a0f0e0d06050c040806011401020601030f1424090f 65
    0x10700c0c0c408000e40c5400e211580800c40302d03e04084009400600f4840a03038060070b04812651603860a519160b02002510720085500401062007880501c8003a01d080e4072403030b80603451100c014640042917003030108441c0351f00801c074001480c043c4001054207043d903503080b85030044c81c0071200650511345400d160307000040000164502c4408c0d02036410483d904040c2900b40c003e003103c1020003074041041110003148003040d0710b0b40802c201d5001c3c2401860101d80071508040b40105c3c03d13102007a00c10302e00100241c50400e15120a1240b07001c9540e8160952401c4c034800c2005100c0c04041500c4020481c00e41c808581c1c031904203011007102260829943c1c04411300d6441d00d003605011a10024881c0b040e52035014080a21308410041d0b1010980010420740d13642c441225001da0b81c0c0c1c080110300720301c43c1c05000d0050300900d004000007410700da01d8407026882000c60405000741c3c018024a00b07042400d4101240703035040640c01c3c41340d40345c039441600050248042c011446030a134004d03a852404550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 642122580 1250 642121330 642121339
    0x406050909070513150f1814011115061009030203191a1006180f1e090213210b070e0f1e0a062604030e06072402090609 53
    0xc0a01e44290300700d504c2c00d100d0f000320b241c0064442d8050740a411500050700c0225124601c11910070340514212a4a92100c9000024031420000300d2103002600c3d0800c41d0611410101d21003405009000c4078070100c8a81410507030929110b0100b101c03200c50380d4070180910418a00c00d00c09a00e02040c200d40e0a42c5041d807034070f506800c40c644103103440840402c0980001464040c8800318602501c64011101203540f17420400a000c04404c01d6903032144140c0c4105040900c042000942100e41c010390141391030140e4084696554003601a0b90218012507a240d24a09061000c40f55503080e003c4030800b0380004403c00005a602c1c807540c40c3d8080d18280c140801041100800c2da2400c03130700c200700309000d030107015524032280545100131095684148550662580458058030031010049006108592800c1010760600025200780c0f001c0d0050302002030f561132994a03922414024401c0c1481440d403080d442c150341c000c54403000c800a000140040c0100500e50b5039964207401e4075000c040407503 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 642123830 1250 642122580 642122599
    0x30406182a031b060305010501170105091302090a2c0d080a0b0a06090e18060103030813061e060b030108072d060c05061e0c1b06090f1204060509 64
    0xe6480601d140b50302c0182445480214501d643c0b40940c0d40c0821206107440c00d1025903210740c010340da6102112100d00840d180320004001601e172603107849402540300080142000d9981d0040384100c0c0c01220820a00c3d034651079442400083d18003210b08071076404100080c1110710794142074481400c0090141080031110100d01e074409564041200c00500915014a4550300c0c0c6001e0002e00c003c0c030070780c8074416110000844450701e00d02d0701d440301b43d06d0074003904143e0f096035001d0360907a02c094020001c411800500000007925441081540c1420503c00c1e070300441103081c1d400903108941c21503603c640040c00100641d03000010000196041e010040026110254894148142c0750040b4060f42084220008040e500420210703406800355007035a03219540c035285401c1420300d0040e00e113034281c01040020340d00e0503000e014244c0040901010035603031544c1d0001c1481c00c2401d81d2000440e03000944815a074607801c21030ac0d1000c0041740002800c00e8030303018001e0407501030781402c58000c03221310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 642125080 1250 642123830 642123893
    0x9030f0309050a090b090a0204060804081b1203091e120703210b12030a050901050d0902030d1d010804050a0f0c09050405071401030b0d1101021f0203040618 69
    0x16140e0710040d140180c42c0010043da51040b000107130020180b1180603006200114051000f280200c07020b84900303483e07040f03550b2620750303407041160b015003007c52880300c2400703400108190070700c081c4a2400040840c15128107111f4038050610074440000314154500c900744400c41d00002c602d813110303615642d042c81d8550320316007400d59924000c8412140c1d0302c1080840502d16280700c9c2c0c40203040c1d16043d101600300903003924000341d891242880f03910114405010480e8190312030b000400e0751581804010500341074503400300f80760031b03118100e4401051500c18400a01410820390350500c100903c2c0c141201c4c103050321540d880b03080c010b40151a0024081602c400d002424010f80000d00c090b02d020802440d040c02c209860b0089030040005150700d03c2c000707600f40c0d8403902400000715001000440f100100c1c1c0d40d000101507424020070b06500a0703400458250388000c6109140b803942d800c0241e82d030700e802e01e407100440c0c0c00d100002e160559180740c404080350b11810061030148403000207240e00c511a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 642126330 1250 642125080 642125087
    0x3011d0f0a0f0e01050f0106081b04050d080705150a0b150702040207140703081207110c010e13090809041b0c080a021e0a0b0f071b0602130f150c0309030f03 69
    0x541800020f917007400b041c4100f10410500c11412518943c2d030740720303082d261440b0008a2007051510890b020f401400140b20510b45aa03c403213089214801580c41e0032025511541400d03814809031200030402d504128904c100d60188940205044660007241c120086144805028011020303000303643c082380380720400c244000c29140c000041422039510554906d000c0d1941d038020307242410408104001304070114003c1c42e080b03000043c400e000c2d222130300600c0011111030000300103d66002e0010ba84080e1040c54a04c1421010381c01401c4555071103d0384001e10041d038428240e906e0001454117501000709901840f030000c020790162003280e40e4400e4803412450a80c01920822122400741280c1000c407900050f00201c244c801c0d201c09007140e40e007130010f900c003c0c0b086030b2220109542000980c1a044555441100c4070301c510801414080413040c0000b0007282c5810010700a02098020701c1543d592120038000c10b982407a000c0140030142d41c009008100754407000b0003002e0440c50080c01c0501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 642127580 1250 642126330 642126341
    0x503211b0105130519030c0f022e0905120705130603020303161103070b0a03020a140a09030201021002030c0909070c0605041b05060906190203040f03060203011d0f0a0f 74
    0x1606000740510f04280d04100d100002500b030480f840e1042c4540079014400f4500c1d600700355a01078443e489401c086446a86104480c00c1c42280d00881c5201004000d0300080c000c4808000b2265113802c0921030360001501000341c0d60040b42c443d9800354a0107144010014000d02038503026a1030703a004405102d0140c0281c81c03a50002076050102027104c41410f030704100d041140303d000301040d0241d00360b54024581c84285602403020950000c02c132071440c0e5402078004005c251254600041d220f840c80300c0b41181600550103001c00220791070300c10002d541c1d0421007880c2280a050003141f8600b060b4030040f85a108104080d8010740300080080c4030a4040c0040c2c240280e002101400585084d24007050340d500144050440401c4102000c6600d04104081c1e911804010f484107141900d014400300045000682d180110302c410000030584401708030784070000314404e020140e165410440c0d4200c0000301d50030088040030382c1500f004001140c1d6900385030001c107203400000300c006545002101800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 642128830 1250 642127580 642127627
    0xf120412020d1703151e10020c091501080708010e06011b050604110a0b04060516020a0302120318060a0512040312090507030204060e070f030c210213050321 69
    0x1041c49051004204500f8010751090140d191007260025840302080103001841d45650115130090440d958a810000039800a00c421401240d551060300b10001d0b4280707108440c0900007581c000840303041941c00c00070781a0400ba41e410401c8840d81410003a01c0710110040c03030941004952000c040300c94812601c810301040d002070580350302d4a05402d1169074102107240300c500644407044002429031244050740c00340c880507600c091400d16855140c001119111707000303a902401c0c04c00d0000050343c5410701e5803031550644000d152616410b061511209414000c00c50059008025000c065903004d0103c451207403409101c0c800c61b44403404c040340d4881320403a041b441c0d1494100c4c00014018000740c00011248203c070240915600c0c1c4000046541e0700303075102008180c125a000128034065008101510700174a841c070b0561000300300e075152490458844024081d03001480c10100b048565080020b0a0164001d00f040b07019032031681c1e4510300309403006041d8000400d2400e0003042154134404d100 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 642130080 1250 642128830 642128843
    0xc120304081e090a060207050a05041a03150f13241b031410032f04050a0e010e0d02100b030c1003020a02071d0402091e040c05030f120412020d 63
    0xb001d8400301078a140c1d02510165105000803c80050032070710003d4450280c600182c040e02889240405000240121041d40081a1000b600041050310700b0080001800c082071840385840c10700088941ca07142c070140c1030a00c481c080f40d0306500031517980000f0084035010500d034000315401da80c01a40051000c0000e40708442c07010340114000302c1d41500a80401184602e4020040d185d44680a141c00b609110051800c8900c604202a00394040302c46107848820745596943d0200050000302190003c4030f607011107541e60b408a010030442445011004040d58009109103000c016019540b4405da440c00c80f900f5450b00540780d00303900e0500542d0b10540c0d01902c015940d22040348081c01075044801003d00501c43d0702c01c00030b8220300c0c0950714401c5c542c407400301c4603032901c0301d80900004280c01011283e43c410701e0406100c0c0502404001b41c0301e280505000d03c101418001054140a203056240d2015440078080084260008003102c0480d18400c10104200c0c00382c1c80440c0721010414000b074410b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 642131330 1250 642130080 642130117
    0x703020a021f030c03050f010302190e01090515060c0a1115070605070311040f0306020307030b12100e0c0a120c0510121d06070e041e140c0c12030408 66
    0xa00a40100b40c0e8420303420750300e0602a403411090f044080341c4044031030021002003800100301508180e4a010b01c6c4c604807501a450300b030b0302c038840305014820a0340a082003c0c1d03141c0400220949040f81c000d1500012903015143c04e440700c0c40c00390350b41c0d110500580080c456034100c855a0340da10f2080395220032007003085a121113030b500340130f001001d08603088004242807040034a5421031001c1120103846294034261138040c1551100d41c002d4100070003407014907030759800710115950350180303003132000150000500d101c803a01010b110580d54251f0408143c1d6010250b08c0c0c00741d07a103140d150030968800e8035210208221a040a2401c8081d5034415034110f28605201c148441c0d0000748015240d481c0d600a200754103070003003d04012078640c001948540c001c84041220703140b086040d0084a0030050000c00c5000c0c1c410352400742103c484203418807851756151203907005100e444059074001c0031113100702d0415148032412616031918444030100f00100000107005c00050340c042d41c04100c0c0196420b0403 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 642132580 1250 642131330 642131359
    0x50f0415080f0123070c080304110607060e070501080c0f090f040207080a1d1806030a020301110d0501051801030b0c192001060b0904020d0902060a081e1b0703020a02 73
    0x70038842141e18000c00d00c040c010710070300744c8001c0083d0140b400e40d41d68a24032221915410720750740010303200310b602d030004102c0800b8035510341c00580340c403034091100081c841000d0300d504c501c1d03c049903002a05220010301000b2420191005482420300300c400540d0303489a00c140000c404104140c100c560081c03000c100301062104000207003140024076102d00c1010511405088100d07070361000c4180e48003110b4440d4a8880540d43e00c0c158008034013808a54007400c0c0c030b81c00a420340300e44214004000201040b40000050680507da004110580b030607a40c55030208458000c0003414000030300092541e4000c94014020b410803204003078801c02c2d4140409800700b40c02845204840315003d80703008840078045090b10306104803011684081c8466103002008020700001c2c6d04020002c0c440d4a980303051050141c1c6491000b05032a1080e90388801e001e2812140c185145c003c2c0100030b6014480b1007007000f240c002d107401310000400850b800d558a4820ba46030032440d0035200300000713400c000d4000c01242c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 642133830 1250 642132580 642132583
    0x1050f190608090709020c0c0d110918010b0a03020d08071a01080102120c280908070905060406230103050c07050a0308010e07050c06011e1e06090f050f0415080f 71
    0x74068480d0794190b80b4842c5e52040300304140c0c042e114800341d45070040ca40d400d200785454001d00300681e100d500c8003190186000000303407801c0421070381e02032003032104a07452901d0350085c880d07401c0142086034103a0b402c0c1d0840d004a240081e6410006007200c100088040038400700d0b421070600510401e030381d000c803580c40c0e2401c18040e400c80c418113988500d6141c082a9400c40703003415140682240c0c1900c05205040041d44c05c0340e80d004d00d4180d810301c4507007840414284414082240644100c800109a5040400a01007200c550394406900022990900d80c5000201c4e02460249075003482c0105140d140e1030a051020300c690301c4010042e00c1203180c10300815400c900034504030350109501c0d2a02d0303a110301041e5958498000c4c1c070040d0f0f0f0020360040c07110104d018504049000d80c207213218503540c1c907080ea4214480242c00c0c3c07081e40785e4241070200460b0394404158000360022041d5240907a1400300403646c2060b51541e26807080e5212014840300d6001c0200000c0242146022039482e20190341505 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 642135080 1250 642133830 642133847
    0x11030a0e0a0509071e0504090213051e0a03030e130e0105160e0f0103091109040c030c0501020327040b1003061a03010806070c0305190f020d080c0301050f1906 70
    0x50103507841c8400010340f8500440101d1281c1041c0d10f6500110510120f241c84400c00d003c000d00911600f0b100c040b4004083d840600050a1080000c42480e8205410480d400d640036200c0866994440c24541c805e4450801c0c07001142d03418100012400d1501e80080d9010041d14003000903d45043c6c1c40890384001500818042c0100035500c004241c400001204c0840425603c150081301084070710741c4952107980040c1e0003601a041c844d209000140000d01d10f50001e40b02a19a0302d07808400780103001c1604954402400700740021440c0c858180104e800c0f100181c9403c0c1c4035481e588203680b117180c4a0350458840103000821014400300350f0200980100740384d010b42060a0300007440410f40d000c0c00380841c4c0c140c903650300041c1141d6590980480e40c0966070312307003241000424130013030b840b00318511111000056141c0740c1c1c10380a404a2002858860229101810040314606029406066008407415100c2c2900d2142142a008000c07404035010015022a0023014030070018200d94040d100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 642136330 1250 642135080 642135107
    0x130f03090e090f0c01180b04090b0a090b03072106050901060911040b07060203071b03020c01110a020907050307200c0301140405060f060d06090f150603080f0a11030a 73
    0x900c0c445844280c0303032540d43c15001a549040c0c1d4000c1c0c461400b1036004650010394284160381c900b611a07100c0c038180c0e1058120303a00c88840261039018098440c684266a000501803e12042005c4014080080d56846043c40313000c215030f034000301e0f0786c00789170f134000c80301e0f1626811034828005410458845402000e4911404410610f400203032602100c01104a4007106c641041160130205247c507884025800a02200280f01c40703004500d038510300d00d680041401e0300076000b8040c16903080001400103604021082d1058100e0900f038030050381c9015505e500440c44d807401d5070b203070f560302541500c3c0c20b00c0c066002084081c1080c2c010298046c0014111041e071000d900030b0100044061081310356880c03da03401042034000c2000941c5c0704942034441c991280004043c11070865207501c070103040340c07007088007941d00958040342d1205200d0581c903c28605070f10201e00704400341c919203603240780740110350440784526000286d0140040c0314030381c50102d2149620a0702c0d40d400030507034051b00c4405d10012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 642137580 1250 642136330 642136349
    0x2040302061206040b030a0201080f07050c0709060609090603150c0e28061806080604150306090308010b0a120213242304090e07212f0108130f0309 65
    0x21742503807400d010400003005941030b11011051340307031000c202030120350042080c801c0080a118030703107101d481040003000500d5802400220142800b90041050b16942c0040b0a0207080c40c0301000000c201c140800d83d00c1d441c0190004a160510398122000c05000c4800d42d070045844028024000d1160002c00061800c1180d440603680d484109072650010440744400144911307004114240c02489602d0780300c00014030015488084502d0900c0c0320446070025510190384408000c10944c11001c00343c05400255880390400d0450300307008000b1010000035940c0c094000c621120606015444136000d0241d19104000300032500300d4409420b601c5c4031042c8002014003005c0309a00002c00084030018800104040c9001d007820710701005409000b518101c0e510813000d0004c0c0c03910410090040000c5209004c07005c2d0605404c0000b507991001100c4070841181d05415800305210310758009640c0002e003041340481e511101d580c6500c0030307903200240c0090408000d80f82055403040a101c140c1d0748401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 642138830 1250 642137580 642137591
    0x90c080f0c04091a18010908030708090f0c0d0201090e0901022106030c0d02030f0d1e0318060513120e090f06030a02060c190c090e0d210204030206120604 68
    0xc1100340e031841c483c0a840050482030390781c200c12100d682141e201e13003410b0340343d41d55045090282d07013180d154900540b0011404424480301e03580c00704000c0d80184444004000061211a00c1d0340c4820f90f030302a10748110151800801107900604003240100030014410450385030420525010703611030001d003901103a5151000101e03c3d046d240340350050501a0040136040860018030680e0602c0c04820f99240c8a103620f08130810104000198079400e540e59450500c104078501c0048904406803020306060070020300740500044009441d04c5660460000314203504c628032100c0248044020103004a18003400400340c154124403030590884c8150f0380000280c0d2180c022900d0070b2416600c907540742e00607911020240c42c206c3d000d0614881c208055840b1000c00c0b06524624821310740c000c4460f1782c4180c904110720091441346904803031500c0083c140c901c0716070300c00400a040351984885002e0388507644071480f562580c1940c0185a0140c0555a41c910b20700d4100c200c840101c448520aa041c103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 642140080 1250 642138830 642138853
    0x332160c03060209091f050f0d02100306031101170a021608040305060f0a050f130219080a05070e090d030c09031205030610020106080a030e1903080c010c0c080715090c080f 76
    0x2400b44651480c60441c6c08034040c100020003220344660103c060340b00d030310002807001584d961107500703444940c1510700080c0070345140340210f60070346c1d003000443c14441d031132540e00244680e050391154408107078000160b4440c012003e440305540700b040085c2c550100403401000300300c80003070001e0241d90041c1074420507030395002d11038040e40c0017102c007000c2c10f42802000c0f40304103042194405c2002d1000340001c40b43c3c4410030303c281c04032180394000c0c00583c1c000300b480350501c101840110007404851103110760a203480302d04e5a0b07031603100552080801d40d489a004080c2442601800c014646c8a000300d440c004c0e030705038000c2040e001a10003600c101d0205500000c03140c0140300300000c84032a407001d824072002e2a201511400349558049400600d5840643c0b550003584140401030344c45002825294111450030b107084821a0241009009400044001041050b01a80c0616a1240203a520214160914000b0b00152030004000c80c0350030364040303010340300450b013506c54080e0300c41121602c1c20358 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 642141330 1250 642140080 642140101
    0xd0504140f161404060b19120b0108010e0406090606170d0305070e0415210311070602070911090d03030f0f02040f050405040804031e0332160c0306020909 68
    0x1120508002e81040500800914802c200e090942510050001030450b58641d02c07100554000c44c4410f1041c02489180240d158008032848038002c00a201000303d00d80301c400203801c0c1d40c0c041c051400c00e000700600103010031001d60003070034880d6440305d014050a0380c0d03030200c4c200c0412064003580c040d0280031050340e42c4520a1207960703c102c009540e5400042d0f4428144002003141a540b510704400f2400042003000c403144c1107400d011300f80340c0d41c20703000509410000c043c444812501400c680120ba404c000305503000a8000540d91403110001d0100c040c1c4403421420302c04c070000f0715000422000e1030014960180e0003a9141c0c084c0b20014443da1a451130315000302c0c80b45010f2000c1d1129401814085401e1a0740b149900520548085180a4032500e5050440506420080d082142241c10714105544502c2916800ca440e0456418450300e80c1030015410548138a041c41c0d00d0004201d130403804001007240180240c000500040d950380301c0c18458080c0d80102d03440b40c01042d2800119091580 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 642142580 1250 642141330 642141343
    0xf161202240f011505040305030309071d0c190314090f162405040b0f1c090203100902040b060406080907060c0302150a020d1107111909110d0504140f 66
    0x40c003500e82d940768200074030250403d5a0000c00740812005210100002c2d2007000154040c041c2c0600900034107248c9000021060303100303416500c0d001c0032041440510400941501e5104020000021294107850b0045006024000120020808c1030050050542000c140c0d203407000e00c00741c1070301d00702031721124404480300b000c0c400c4500300c00e0300c0e0353b8903901182c04180750f0200207140d10302940380c665601c65491464002d80041d070340711400014107410201c0d1501d1070346950380001405004070b285176000242c603818814030039610603484903031034001c55a0b940d201c021140c0004165030b84803512a0300080242e8400c8407905403e100e91540422658014803402c1c51042c9c1c5039004210b147d0680c44940f12011000e081490015020300c12500809114000c3c0d034026090100c1d002c1d01c81000b424840e1a403515060428085c8114803c5e204520440c1040c00302660704000000c00d00c4a04112429070fa40709007012400b40900d01001d1008200b201290450b4500b031410454620b12258030715592245c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 642143830 1250 642142580 642142591
    0x91a180105010f0626070207062a08030a0906060801090605010f03080a0f030f060b1801080f1506041a041a0301081b0303091e010f080c0f16120224 65
    0x120442003009140d10801080d8601c99500d00305d1400620800300091054a0a40303c103005078000340d40500c401c9a120500d64420030340c1070415001d401c0c51207030035541c050341c1c503401070304031440080040c6450310250081c0a030640d020310100512079440007094020001c4001c1221103500b0400001422281000190146c90704002c0c0d45180603544882918800a06070440081c5170300c41c0840e00114040b03202e45002080602c1078079545260000f10294009c0380700004038140301e03c90b0144081c0c41c0c49140e007590f0112840e00d035018041e2005000864500595220103882400034526151820805026008840c0c0950401100300c2551550a03c240001d0142e40e10650101115003001d8001c40303600c143e008005000d1380d291004020100350180403400380400c02c0740c030b229a84241c0d5603010200800c00b140303d00c1e01c00d0650400da40e4a07040d0740b1446001d4541c048001c5251724080402001c00c0c0b20340d60f80b04d86c1a0719548890200a503e6000355100d1028400c050058504000b500c00491407052 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 642145080 1250 642143830 642143849
    0x40b01050a080309301b1002060f010b0a030e0a111002030c0c010828243c15020c09090a0b04050c19050f03070e010e0a091a18010501 59
    0x1202500481d0b10a034400100038280000010540d80354080300b4403d0180800928003101e140e060f003141400b040162100e0309000319402701c0704105c00000101261819682014401a03540c10190011409441c552002161602940300c81000300840d64110141c101c9041c4c60242c10491000800e90b124000c10f4600c44440e00150460803c942c425041c06030300c1959054960400740103c4503000340c00c0e21080700c1a0300c2907070b2408124a82001d016031600d001c00345541181d00103042540b00ca600d404c0c0340e0000c01a80392408000050740103103881115a00c2829171036248000e969030040074802d80e0b60001e0720013501070070340c60140500b0900b40c09407003080000c00802160b4100c1e0346460301d400d401401560540140600c4c020782d40d45d0fa140d221038010010300402e46c40790400781000b00000708181c07450711a500500c0100030344408909228119a4520004940b0703944444043d4042d0096107401403603030180c005890411108100900d0080e41e0031032015803a40c0001000c5801c840080c011411607 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 642146330 1250 642145080 642145099
    0xf0810020f03180a06020703020105090124050d0c092405010507030915030605061b0c0a05210c030a060f0b0d080d0c0c020301050a140c07030e011115040b01050a080309 74
    0x40c2541500301403050f00112080721845a038580711541241c0202004400503510354040c04a11a0240681107203510503c4100c102041c0403001e03201140294481c0a0080040070000380034081090813240040003a9034041c4062220010344100c540043c0c46c0c12100074209081c04500c0354465026184015415228410402e0811400032190b142c43c0d80c512003010303103e000c0400c01351100c5000d42254015050b240c0800303c03001604c142840c03051611036000e6000c06070300700b100307607121001303000344408060300b03613550944000800d4200510302001d141c240c40782d840101d0401845a000e24070801542000700400a07030202000040f440f00e00000d00000f00a0040e41ca40343e20a5008082450803414800031101907540032a00b951021241c00f0801d540d10003400548002050229600c0200101d42c9480e041141e41d001d08190020310b880303410081d01d0143c0072a059420040c076056001824940e040e146484d14103118201024042c4034000c59041900262401000041e10009400204503280303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 642147580 1250 642146330 642146341
    0xc101802040b130f020408010c140304020d02031c020304030311061501110102040f09021206010513030b060d0b18100c02030712050417030d0510120b18070f0810020f03 74
    0x3401450080b00e60002d0141030510060a5904c1444c50000f0109805a180c9150040160031030740c500f079981081c0f1480049808098503c07000f201e501c00d90456080410084600100c1d24100d810065140c1c4640380c0070240d03100c1c41d000009001100d110742d48140c1010f604061103611001c090380c904646c8070f460900342e000d660041200320000f40a941c001030800f039803440400c1900d80140c0c4401340c083e5000844000800d41c10040355400319081c06c0081c5040c41e00c00c5540903a44051201030003080c3c0f55004100302d58bc0d004400040b0a030080f4081c205810311164030b9810030702450107480d2a02c1a024010030110071030040040044254001d98105503040e25484d40c0b104001d640001000710800c008210081f89101000d0304400c1c0e50001c0d0f40301c00e80a55004100c5c2d10140540e0380603000310104000b2a203c1c51160f4440a034421074540d6140c071802540f02c0c240d65200e0800d00c00e40500800803a6803007100c03190070100d502032401c80703107100c08040c910b404911450700d91001143c400c200041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 642148830 1250 642147580 642147589
    0xa1d030d09151509060602030405060d05041a0711070608072007170714010c080307050c0a2001090b040f060815030304090b040b1008070c050307020a08030c101802 72
    0x206690180c9450010b4080700710190003220145507100c0401030028000b8400310000388150005010b03680020f518041c02c040000d400c0b03010704400d0624190b12400060100100350408500061030543c12000c0c5003001070001d4040b800c0c05650038101c0c40b50050008440340f142070400c0c01400d2a8071024880b01405068200001140d01c4448c054440c2c8000041e580484030340c0310b000343c18840b020b800040e0400e02e68003100c4481c1070500d0704001c40021440c01007a031140450790420014180a41d803a00ca1025076403c003036401a014205035983d422030110980505030b0036080a80903030351564005c0c0c0382c1229480038011030144041c5200002d2090003a1390041c2906504011032000d20048408884c000900d9a4071541040341243d03143c1d0340e01e0410741482d00904214460803261001c23138420841d00100000e030020280802c206401c00c50318140001402107a10b0035401030240010300303407185e48840c2e9950103d4009200b610503113014a041c0d1006200c3e068002d542c007015181504c03101e40811 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 642150080 1250 642148830 642148841
    0x21201081c05090d1e03050c06010905150603041112010c09080303040b01090c0c0b0106030c0e060909070305100f0803030402092202150d02030f04020a090b0a1214030309060a1d030d 80
    0x32217840244541c1d28401207811903140e80020304c41d45d1407541e00c100c440c00132030a00030180c2c000b040f86420b240911407005040107455040700f41c107440c0310307480340d40e00d0a00780701141c014400e00e504650488402e003182107040d0480011911192542e0028581c2c6001c1d4695038402190b000c2c1031084100018007a00f1040d40003080300030000d10f8119080c02d01c0b42c5825404680a078400c0e0082651010b0714130803a5000454440787d50411140076051050400100d03d01d00c030010248001c06d40d941000a800341440c0c00d0200140400c3d10502c0c2d000c0744c486040e680d4a5005032001c1c0e1145000a00140c00b60810008000c586d1004070341d0b160040605509000003480c80c3c10340000d03005018858034004112900c0994420703c00c020140e099030520b030040c0311441c0e2685d0031081003e420001e02200740c0c1c8403444400c0465a9803080e90762a240e59061001182d40c0401640d03100340000424801e00d52400100c40780500040501042480e45044180c0c49031031104840041c160030500c0f21100f442c0b032a5005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 642151330 1250 642150080 642150083
    0x5040e0712180b0f0c071b09061d280614030c150403061a09161202030c09130b0901080d0e030d170711070b0a02070e010f05190504021201081c05090d 66
    0x504e810071b50709564494001030314000c01030700a111143c0c01c100003c580e0103140010010740141055070203245450260080300101003685080126005110001042d00c40c4c110140460000300701050311a0052807824410841291191245100501d502d1902e80302d0307159104510303d4118a040e28507620350014254000203240d071410072107240d02d0141c031921240c83c46000802d0800c03002c80c428020241040c52840040228188140108080310f40150119501544203d80ca003c1c040c20354100f00307028000315081d84e038206107207900024402c01c0c001040300c8607200d95164407038a203400b0028503a49144031100040080c034031f000410724240074003400c560041524038016030004d0b0362100b0fa81c603015240d031000c4410000015007404045c0e05000020240481503000d46440d4076080c1c030501c5991031070040510689043d6400801840100640c1c00101340c064800e54a8190103000384c004403400b44269501c901400311841400034500706500344200060b101e05080087d46000e010300e820b44c0390300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 642152580 1250 642151330 642151351
    0x7051201060f0e24010e01140702151207021f1a03070b0405030c04060f0311010507051605040b010516030305090307021c330c05040e0712180b0f 64
    0x200800d0249403605010701800c45403402841901300740d00780544040f1400c0d024070300c10010f03280c0400d0b0380e80d1050702c4070840d400910b40f0030b0200d4003010304501c0b44d10400030300130750140152844412135130801d00a400d6440318082d800318541c0e100326007a40c4a042440d154084d0640c02c9859545443d00c0b82d00160b0301441ca2480062510100c01c0402d14100c0c030354002c0100b0100100b010000b61800308a03900019105032414000d517403501000c00310706101408000c0480c0c040c20490681a4494815035864640010846494580580c4041407100030760040600031802c0070000700f4194081c4007159140412079100280405d8507860031801048090240419400200b14180c0541d0302c0c440f00d25581c80c5012107103400c0ba42d00e03140c404050f07032640010804c901400264450600d2122000c1c00490b0024a03001c105200e030740000b211070b07120383c0c0c01c0300031560810740a10018591082400214030040e1000f003091080d036103842a0f4021004000070b05a004c90f030001a0380070800ca0481cad4100020f0361 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 642153830 1250 642152580 642152591
    0x210f0209030d0e03010b04020403050c101b0309050a1d1f0801090506100e071d041514010f020609070513060b16061b080a0207140f0106230307051201 66
    0x800290900402080b0140018650790100c9154035081c45607004d06041142e045160916507601c4584990003119020300c50109903c085002c6405000c0d080101c111105490300340480a16001d0151042c0c0c0c05524020380403d240030921a0300e5040c941242030b0b03d1a800082680c40303520300000000600e0694043c1c0398085000502c1c1c85c400d01604801a110760040c00003468450200c11403440d8a510003034624880341c0901c220b040c0c200007600361a041c110301118945041034080340203014000103040c2c100e222654002110303411400c100744040d01c00d907200324100c00782040c00ca9403110181d9044a064006076070402041c5860004001d040801880c007003811030f07a4075160001900144a065480021b1400200030001c00b4440c0300b41e015003400025203a941d2200c0c00800f0400010080b5810701d500040a6083c00490900341007041076110850b201480c807104280e02034040c0781300d240000d200100030a0315020903101c1b8402483c4018000340010341c0f401d0100020141d010801c2900da55866 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 642155080 1250 642153830 642153847
    0x5042a0807090204080f0706140a03090f0f03020f0106150e0103061d01030c060908030708090d0f081804060e0a021c090606030c06050a08010e06210d0807210f02 71
    0x18010140203002d040d10050300c4610704094a802d0906900601039240c125000500146800c07044201e606050804e6003a10b80070541c00580c01801c0c00c1901414000700d106110080000c441d00c0c00d14240d100c0e40c20364801c040150081401c5c0da0180c0218a481520325441e80120340c80ba00c84110010414540480c00c1d07071341d80010442ca40c0c004002d40d15080080001070003840b04c002043d200502c40c0740b03040401c8902e0840da40e41c0702d01071031000418041d400289040c140c0e9448603c13440544d04000302c6682d40205241a000c3d176800803150301c40b042c01008116139a40351511511003158441140c0e20700315619428004020f5000240640506000e94504500070420380b2544901034860340001a4003804c40c1030060302d000c4190300020400c0403c101c91311100ba84202410704440d150260b058040d1180340000d0b091008090040301000501c40100a49181c00618101c00d681107884011840d240c181c0200c0700d1240c000320060500203002e10070195081d4550040282c119446401030074007015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 642156330 1250 642155080 642155083
    0xf0c0b010e0411090405070909080903101a060406020601050f210a03090f08030a0c03110a1104050a05160e0d21020709051b09040b06031e060405042a08 67
    0x280c008031180307405801040100000c4050a0b020044121190100b620302590b031603075112054000d014582d611a8040c20410840e08152110300c080201a2402e807205640c9410003802c4041001c1c0381e1a01800d45a100d50410504031015640c2c01e5010700800e03030800381405201842990042d0f004a148c1030300c0c1400b8045a0300e0040e1410020000d408420070b2418020856140358105000c41002c1c06002c0026150010885540c0940ca0034041c1c4075400034203007039403c07420019010b070081c0610081d4808000055003414642c41c0708032010001611251416422110f08403080bc100344000c0c02c0e04445c2c98050b40c00c8801c1b03100000d00c10340780607020b07a507610300a4880803075038941c5031b91000d00c0c100c07080d80505c540d0740a048012420421880c092500310f5170402d4180d0303c001821000242c4d01030341d403245c0e0007412904101400e269a03e0410040d4400d03c05851101c0050444902c00401c00301d00d80340c011240100d07080455440c140d41c00e03076040d0682c1070280d000c0b9090004038400000d9140c0c030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 642157580 1250 642156330 642156353
    0x606070503040608010e060406120f0201021006061215060806120709020d021b15070c060b06030103081908040309050f0f1e030727020310090e0a0c1409070f0c 70
    0xa5813044403a5250004404940c08060324091196061207000d000b00d041e410400c0740442e0b00b180d41203024291070300060341403d000359010000c19040c0a404100c8540060280c00c400390503110810126080c60010100b0304d500d40142800590440007050291034442114a20780b415003081d1645c2c20341c0c50304001e00b00d9000c9203a0140050b0003099030403000d2000c451204441500d0780207070598100300126000100700007461207060000c200d03800303000c1c415a40c0c454004007001070030260303807942c40b81003500040e00041406203c0210191500c420b06d88600340301ca0280b90704ac3c9802450307a0606042004029104549580080c401550602e00741e5681c880219a1304446810000b1a0201c02c141402c0c85100d40091643c003413489240303c1001f80b0072120f41c0400000b543e0051708d80c1c0302c4007004026000fa5074884003000d410301d035036810100e00201d0140304262051040e5040569140b034001001012441c47c640d018a44030001602d8600811024011005603c1c0c000ca144003141c0e5034401c85030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 642158830 1250 642157580 642157589
    0x1507030801090b040c020a0b0c040e0108060f0c13091a06070606170c06030a18020d030207090c0318020d051009080301090f0b0a090e0a0804030501150b0c0703020405060607050304 79
    0x10301040040142c1d11043c86282002c10055605224007802030501070f5881541d0380c0002c08104241c00010030304600307a000d0b2000703000e9411015149594030b0b04d20656a03007003520b6140444110320041125954603408480050254624440c4440d14010004004000c800410305a5a18115a00510345d4420004040407481903500045590610503100d4000008110028003940040381c4595190350381c40c01d072a0b00c00806a00401c407803201010461508400910094103c00d07803c060030b00705500441c0090940720800c904000000303000608130140c0d158408801080c0c0b88401062025082508130780e8a45401103086407108194002c07241c013240c4000100b40c50100d4040014030207283c481c080c002400041b200c00748641d00c601c1e00085d0340c404c590322990018075510714440c1c0090b0303010700c0380842c0260000c030034079100d0390390b4103106000c0e00541e03c01000c008440140400c40300c03005c4007580c0140100100030714141c1d0950f82844002c00d03001c1c3c1401e50200090100a0001d102040101f0241 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 642160080 1250 642158830 642158837
    0x6050a020c010f210e031606050f01050f19051906021504110d05070305030d0c030c0809030a03020a0309080a05070317220f0b040b062d010806150703 66
    0x2850040002400c1c84005506507042000c5890829075041e4481c04100200300d40b2401050040f541c0c031841e00003000241c0113610703e4000480c403003c09212505000390014061102400141c1c1c0e843c410301c0f2580b03000d0203103550102011442c00040d00780181640140130074441c101e000980c6550009502e0241812140900e50140500b80609a41070041d40d40d41443c0301c0714002c032400c0544e10081149102105180a0300032484018203001c1d0030070240008540010039240c0da5043d503071030781018001414507200402d003408140000680701e0b07181c1034462a0324001950410142d80d20440c007a50103032440d0b83c03c04d921410940302051000008140003a90b94455603601e0400740317070107441500e071402000e601a186000704100d01c4038a031890705504010b82c048940c48521882c20008211201101030110003107441040b08011041c0c0026025800c125210b041c0b820000200c0321a4101840644000c07042030f40317661605500070004280c10130401000384d04442840f0701588990b40bc48901500003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 642161330 1250 642160080 642160087
    0x120706030608030408030a050c101a090115020d03150e090304032607031202120f0106110c06181f0806090703060b0304020d0305090418021306030215030912040605 72
    0x446805100305001422610051800e107845c2030015030302c3e8080c41e080c1d44140000020f03c44150039080c401107407058002c500402c00c081d034001c3c90444100f0400342d2940500d000c1000841d294001140400c0e003030341103900400710204412001c0b0060001da104900407076401d103c021452860b1b04014900c1426007000650300c0c1e0380755003005c04160001c0d100c0c410003010b002980040c1da01400d001c4031740d00340d0141490141070803c40c5000000384682e403980c0442c03640c042d0070302080d0300010b41c1c400c0c122401e507900c03001c10382404030741c0a44510f00d040d800c0e1b900080402400000d459201d918422242000b4482c00c6001c507043c02200760490b030352090300d0010742540100314451411103c903d400115500c0e08000050500c418801c8a10025001030310900d4440104402c044c820b800310b03400a20060801d0022800c1903a458640300700d810350891103050103204a452610081c89508203ca4004140c117540f44031483d0b283c982c95201401140081c013892011224641c05900200700070402582e52555 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 642162580 1250 642161330 642161339
    0x30c1c06050621010614040303111f0b0312030c0d0b040e01050c13150c061806060b120c0f040b030c070f1406060d030e0f0102030d09110108091207030e06091207 71
    0x1c10307443c160000d206100c102401d01d9010640700d0282c5003900c0d4103081c8a42000305404189280c52000103044a40c441c0d0141c410419410750380040c4207140c41641116400548500c3c4104a408125020b00b2400700a01191110f0b1a00b50400382c0b403406c002d00001001c034040480d040c207480c001c41d01c3c0300c3c0d0b8141c00900c2000306001c0c00c5403d0b005003006142c00080100c0f0380700003082d010b134880c4040d00d91a01c4030340d0303605030404800041c58825401402000103c1c0c0d14550341d050303600300026100c0940641d070001800c08516a0480f1003010020036aa0711706800d00c85030f800d56030006001c28481000c1070124000080c0c074440302500c110700a840d001d2141c086d00c00c641d80340c00001031619016180e80d00c04400001d17040350100081c400102d071282030300c846040040345540181c2c07041c080708a0a10114000f400308158050b60101800e9071046d4083e9550140c042c0d84203401200710710b0f0031908000d5800072903c2040403101511700280b800e8034005495001814198510700004041d4101820800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 642163830 1250 642162580 642162637
    0x14090f010c02040606091d0403021e010e0a0c060e15090d03090e0a14090d080403030c051c021905160f0213052e140909031c09110105030c1c060506 65
    0x83c0d0314500c45035001501d03090760002e45138200c1152074054400801032001ea443c03030a4100240a06116080ba498ec070614281481c55001910900c030110b480900010000d06018555140c1e03140e80460a40c6001d030102e013840160a00b00005908128100700c011400c404034009183c01520701c030300007088c81503980c10071000208018100703010329072000d415a042c51f074124400940c0640c042c140040d0a94644105451034803038010003029403e42e518030422080c0207039010701002080c10940c81c40c5040004011790b0180310700c6072242a0304101c0002c0000080905104882c540d101800c81c5c406101241030074821382d0016034200d40c1004100200c3d2600114451340300d152110b500b6100ea004900d00030000c1c9044000f209000e010714a2480041d05e1050108222003444107114480148074210802c00001041801c0c0e048550070032100c01f0458a42c4583c054900402182c40e0041ca03110041182803e100d2070300b50303030990443d2940f6000455903103030805005e07503201011250010305440308099 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 642165080 1250 642163830 642163859
    0x30040f0303030e0c09060d020f04020f1204060e032a07030818010f140f07080c0a20150316020a08041d090109050d050c0a0f030f080714090f010c0204060609 69
    0x124001c2c0c0c1c5c40810800c899445081132208035805036248401c00240b040400e02034407803580210303a00c1d03800154144c00116800c1c45c06100d01d004000c00c00a00ca07880031010380300c0c440d031840340420040c082c3c10b0344a00c034003288d000799212103402c0484a006550b50b039810b03034075004080440300004041c1010035080d41c1000040c0001d99052811031300c00707041d400003040c09000d04030742429a2140490b0074820803034076408940000860500b118400c0c0803610f040c8941510b2901d500984d84100d2044020b6030500c0b1803071143c2041e241540d6421569400c00d02c420908400c1d081c44110700c100d4101002140303032017004101a0407080181121480c1058410140740009080069642c0c5002407410200700003040790900383e04907140055883e51060903403890b100e030301c11015086003040300941c000c042d00840801c2c441961034980c040907644006050356005011544088484810010905603141582c00d00042c1181414005117518598003c14200c4d4101e800c80008221416014413000f000d80550 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 642166330 1250 642165080 642165103
    0x6080604030906201b01021504050f2104050f13091407050d0f080708040914011401080f010e0a020d050c03010305070e0c180a03080c1b0330040f0303030e 68
    0x70007204c00201450700d0356920a18030050400c0907900e0b00d2191171303807080c4104401c8001c0955020000c0c2000d00340700e511980c07071407240e20b41d40c4110355003103420004041001407800740000c136a034102480c02040c8500f028104400b964420f0003c8104504c030060b0344074440075180500c070100c0401c40d20340e084030324251083e00568400c1040c0796140000402140c050032005a102174504c1c1c8030801d500d418021409207401020856040103c6d20a40388603a0b803526040301c403952a01740c1202149001911420026a50007000d40e0300a4014090380c00607039030351a00032207428801450301035120b8038001240c034169012000007400000400a010b0208541e00181c03803207800d4000c45007480c0e803400c0354900c10101c600c00c29416904c5c0c4501b0b260b0b5480c0e03804000b560020031080e9a0340b404044603132114807490042c12031040c002015405404c00149400c55144100110010300e9500710724126a4805072541c0c0c0b1700b00c1c004200214000074080400002140b090700d0129859445d40d082d00e0030524001c0f407 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 642167580 1250 642166330 642166367
    0xd030f060f08120a09030210020307020301150e070c05192006040605030f04020301110c03090a09150603020f0702030114160e06031503070b03180f03030f180106080604030906 77
    0x50a100641d400720304040f40c1a100001c540e40c0d0215013400381d90340d100c0c551005e5448007802240715201a004001040054800c40c000c101501158045d407080e8201e6000d0250044140c00010b210035008040383e42c48903000e24100d4031000d80001718800c0c5080403110483e810b01c51640c803402500c0d45441c0d82e5807050703c210f620303600746420b080009141d400000d0605090500a9021030190340342948a02d090300d0078454050794546844140950700c6d0301c600e80d02c1d40281c103030740c0001070610024807400f07050002c1100c1b4080ca481c60241c0483c081d4000514120f0000c804014500050783e0034410b144250a00c82c801c0300903807810b004849071965680740350006000d00341e0984183c0d95039401c21682c3c0801c9004989200082a03400301e858201d940d044500004000424041c40c4107000380024404d2584d101210101c50460300a19141d00058400c91b82c1411907102103504807000c051070480e6501d01e10000540e0650700d0f40380c54a042c42c10f4409030301040340744409101c00b917442044007050400419 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 642168830 1250 642167580 642167609
    0x319020d1d011d0a0b1b04030c170c0f030709090c090614010807020c090115020f0d02031b070e041e0512070c060c02010c02011211030103050102040918030e060d09050d030f06 77
    0xc8607405d8641e402084020300e041401c1c0c400a8045049041d04c01540d08004a405461b0f26500c000035074084900d400d550760b05c00c00c200c2d00e00510348540c500c1d0402230050080c03d066481d00c0c107000c0241a051908403801c01d100040030804800d940308480050180207128088900c502d8000b401c150005089001150001804400140c03901c441c550b0442d4440402500344640f440400c074101951445000068000c4281c0302e000c059000014140700c4400b41e0640840e00c40010351103a4841003485016600701040c0006000310303007040c00750151070706005c2904c1f0250718287d0b01d0909101c00100c02161501c004101042484015480c50b0050406814028860042a0006090650544002410810032111001c4c0700f6405410880221190104441e181c2d6143e10380036005c0d4210b07000d00b0700c040c2c0c40d0402d400c1c1d0b00040c00011401840c1c06403100b121440f01d034407e001a9900c11100340000741c1c0c07036211110001d4800c01454420802a90340003510007400389030441078500640c48040100100c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 642170080 1250 642168830 642168833
    0x121d0606100513030f0201031b1107090e0709020906130306060f15020a0f14070f03050d020601061e090e0106114809010e0708010b0319020d1d011d0a 66
    0x41c1c4815043d07a17000b101058001d407061004134041c00503c0b0b000074034801140c42041070280c100208403400c15811094881d031686440d039100459822588000041c2e0004108004480b1141d000f0030003620081c0070300346020031113060300801c0d01240d80121981e6649030380c02c207c240000b082d0749014000500000403100a5144001d50b80c8121203400b400c0c00c4d403030301c000e0001c02903880600e4680d920b809083c0c0d0049503450447c128403003614070042d00c481c01040040b240e19071001c107520f8140c820396240c042d80b084a1001075000c41031031403040d6007840381c2c806001c24030078500e0340c1c40c900802c03150755000c1c4950410003100741041c148108003001404803064004116003003000c440d40b500c03481d12b030100500d500e1844e00300c9001c4802485680001d164400403030148540c0541c80d1003521103460710411a681c8459a00b035510044810200584040d00d000c1c0740c040080e001042e911800020206405201601c074111168090f5031b01001e580d9505c0f0b50301030321041b1111400041c0c0c07501c0050305600e07246 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 642171330 1250 642170080 642170107
    0x11502061b0a0f090f06030f0518150a06030506151206060a0501030e0309091e1302130f0f1104061b0c120c0b0a02030a0e0306070f121d06061005 64
    0xc440c0b1242c20b00240009038040c05100e110b00c0700050401080c0d00310b005d6569000030b00146102c20200c1c0c0f4540c10705000460259608030081000300300000103140c109481078008a5081c805003030080c0740c64403500700101041c2c0030800c035030241c80c0c24180621900e05c2c1a041180d02800c910014040e0741010301007001d80c2da10441c21600325070080c00c0100e0180540039420341180f05000c09244c2c448a40000c0c003058401141a1918802d1203034070340700b407586954115921801c40b021000b035000d11500150a09407169810095040240140100e01d00481229800c1510700c00d10707111601400204041054683c400381c0c0d5406e03d10070349a100c0701e825a135202d030140c00765507002d110810f882c2d07200e5200400c65860004002000924240c54640d841110025203a1340075514071000100f11192040d20fa150201d07804e80549441d4441c000a61007500c0305644030402c2207102c1c881d095a030100b410051202e034000c0130480026802900851400c0303420032865030a45120842001414400c41004504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 642172580 1250 642171330 642171337
    0xf06060e0415170f07081005060616060b0109081b01180b0306040e03040e10180b01020a060507110a0b04140601031e0c030f0b0a0c0e0303250209011502061b 69
    0x80d200440746001c0c0d9100619403814220042c044c00c43c0c4600031000414a201044c80c00f004004070074107120b16100d030010480c0314020380b0400100340b12450010000a00d80b68080601031006040100d07140c0c1e0355080700c500f007900c015080007060a000c100004550b07489081348100f40e001001e82c002560410500c1c0c6e5881c0002032003103000355502d80240d44400303402c2060781d00500009031900000e15056043e440c1a800c1449454405010036105d22140021406400c01c0e035a8181d0050000425985510000c0c1c0400b400410900640c03805180c041c40042c028403452600511440b06281424a080008840c07075203615a0150030100061000070010540702c0041c40c3c1002c10b000c0011040d080c44103080e41107a00c01400070868010b03020402c00c2649046200d0000c1c03842c10401080821403e5409400d1083d440f03a02d07800401141420b0400150219125402c00140070804081c0342e0100c0c54950302a0000310342280074042d41c95603584d04100c0e4651040c0440103000030411030201084a501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 642173830 1250 642172580 642172589
    0x13050907030b1f030f050c071b2d1707080d050412061d0318010809010b0a2907061d01270602120a021b0a0305040e06040b10091a090307050d080d0f06060e0415 70
    0x1d00d0096808514010586e000680030702e0b000359a401d281d600150707a80e078cc220300c5840240c1c060050340301c01e00d034029400c3d5021914219808200c4a019a80d84001454007020300526017010030128811494204043c000c0001d58090305051401100c0014207803030700050081340140e04250920301c0949403880c4030001c171406038402c06800c2c1d50700203408c614010f440710341074034008003c1000014000c0340e0b004014029080404400c2d01c03400009114241c4402c103540a9204020702c003801c42a005e02e20780c081c0c005c3e000d1400181000c0501c1300d6011703e01011f03070f1100c140301d4001c100382000c004003104503034000f0360910080080d02555a40075180340114030450200c410070384000f800a40f2580c0107152401703801803201c2c900343c40004c1c0103031407003520307014a20741c170414070030481400401e6008441180c0c000800402c40e45190104200d00c1d04000c2c3d100315801ca4081c806618103404c103024082581c003113110003203091401e0250042001d050b003181d5611803800e0030303c0c468894040031914020384 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 642175080 1250 642173830 642173879
    0xf09050a030809150f0a14060a140f0d0f060b09191d0319030b01140f03070207030b0f01080d1416030905030313050907030b1f030f050c071b 62
    0x1591140d1902d82080e5213000300759004c3c5030810402040d02c01d101e0f4a940702d4030b40d140040010342d03044d08201c01d0895084407666003040c00100240101643d405070405108801002c4480135900f00010402002501e0000ca070103050f9080244100000c6000c0d81204003002da070003c11902d800b0b16021581210074204d4210b181c0d894501035010146e2406280484000008880d501c81082d8540380305203411007081e0001034504070a4025640c401d030508081039083c4007500d81085452241d0740b080380c1c00030300004107601c1400310000010764140c4080e0300c201202503100c102585440e00780f034105480c400c103003410000360700e61300100e071182c1c1801d81d4031200e02040c001c4407d21651a06540308041c0d9042103074544004502d009061403c43c501105540082d10012650744644000f50107403041e901080c1d51000c031a03801c4d840825039400350882d00c18594071300880e400c180d0b50948001c4400a0360701034008a000607603101400040140c40084041c01801100920301e032880c3d03002030480106900310030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 642176330 1250 642175080 642175097
    0x71e030c03120902040c0c21090e0a0b040e0d020114040305030f060f040509010204171914070f1d100b0306010e03031b1e07060519051b030d0f09050a03 67
    0x4400c42c0d038094000b840d406481008400d11034400504164541c01d421144024184005080d070042118111914103054644410150402a00c420020401015003a109990b2100181d5540c1e07030303024184100c411580030304100c02d00b160009007035404030380c1100b0704600034a040c440080c0d8003504aa0307000c0407251003020503885400c001a030b03150346010840d6005080005010b43c0f10f00641c000d04c1196a030148441c8000926442980c50300c011241d9a940140031007240804610300c5800c7c402d0808451003070301c1c08143c59030a403049100442d00b040225881c7c41401580c01080101160b42141c02d00d0038aa2006103801c910340814803004180c14104004030070200e040b03480410949940c203400c004404811912251071070780d90350a10300300b0703813450880701c07000e080c40c406c003017940400d82c1c80031b0f5071300751403c481504031900504103e40514100481008203507030401201c0140050544c0311000346980b4410f24440f68255881a130b2403051281c54a50f49900090340050308041003589402e11281 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 642177580 1250 642176330 642176357
    0xe060f0c2e18021e040c0801140111280f150501080c0a0603020d020f0c0d030506120a0f11030303150a1e1a0c100e1209031f0e070b071e030c03 63
    0x503c404c030310303000c240c20a0918017040c9800e030704403500714161903850841d6100c00071a500111502401c1e00713981c11b0310350824100546100102c120101c0010168a24000b04841070b90f5040b10000254209480c0540340002a06404210303000d4903004000b03450081c0a01d80040e0005004411170b80304040038544d0002c1c0c84d2300714000640588444c00e03500c1070f486858000011000e030300d4072100001680002c1c17801e40040c2c0b26260034109032000c1d0030544020100c408203540d07103180000d4a91001d540302102645580840c1d81c04000651143c40740c11100d40c01140b881d0144411a107c3e40c10440740100c1800106030b0080340003290707000b19508072240e03c80540f000302c20759086101e011031078100c030f0141d0304034050401ea95400141071090601300716a11810f84607500d01581c007558050903819004000c0103616041301709080d85c0102c2c10030f0340004403202c0c1e0600f0545010b201d54044000a000424a0804c2c800c000500c0001c0554107001c01150902030394004100001c0c502006081c170144100c60710 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 642178830 1250 642177580 642177619
    0x161e0c090b1f02070510020a1514280c03020c120c1b1201060e0907060e090f06010e06130303140a020d0804050312280902010e060f0c2e1802 62
    0x400505c4040c240036481600018000d458440128090328818080760064142000034070440c00b07400d00040e030a02c0c00e03031038880a4861f9042d80003142c020114a46400400842ca84d110702c11901c0880c3d180140d40d0140e1101e603509002201001c03050411061151007000c40c40416505884800e2504244000d038004000509604209075000c0c1950700e8400301040c0c40722600d005d0b46c001d2103064210354440340d55510454a00d0700b030751845504050301d00080752044a402c202983c1002050420000010b050302c0400d2058000e03035150804507811090800038075401c81641d103032888100c00d40c40c1c50b0218014010b5515030741c01e60035004004400c2c00147c00d22509105070768002021500c9030f000741c106105484201d01151032a500180a402158040d0529503c680100320368103865403021030410790200b0030a13070081040030704496020401c070400d11409100b81a41c203410f50a88240600383c1d10042c3d8a04c40c1040811b511451410b665418014800d8101051040c1d04907008902d041100e150303071 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642180080 1250 642178830 642178843
    0x50a0e1507050a140d09230909010501050406090b060a080705040b0c01060906050402070c0b031306050c0d05220209040606090f050930161e0c090b1f02 67
    0x102a00340108010041050103d00007500c0d901403a94459a41d00201c043c50b2a04028005840403d54003d810051028500882d1103490f442010004400c03220001007129410126010304540c0d658070014446403805124290160003002c46c1007211464002c08074140344190010030b8140700442c000101d07054819400c0790003801c04080386030380f100d120650710b078044d013014010541990304005000c1100c0c1414400e81d802c3d190800030750b5034054030340003d07000590b001501550001501c00030610100f4014065240a886c241c402540e650046001030f20850708041e01c106000c0c07804000701100036064007109581642c0440fa940da0176143c51034103030000c01e20307503001c200e403141410040d0400760307101e510142c828a90740707013900d420701c01078031582000d04100310150300d5115031009450103207007010380940b100c480400600c5510041a80f181000b641d41002440d036055402c440c134100300b241102250005245241c0c1c18084517480100150603914003206040800c0d05151410104a100f002403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642181330 1250 642180080 642180109
    0x70602030c04080a060c0305130b1602120a02060f15030a060c0c0f1211030c150a060806040c09060b0f030106030c171509160f050706150626010303050a0e 68
    0x84581140117407510902801018551101080c9030070002210800f0140c82129040e43c08031128030650740742225000c0180d24100803030114072501c0b0503c4081c040e407070020041c0c1d205603002080075182050003452007040040c45504012030070044c05401742c400150709800243d001e40c0124030b12520355402c8841001d0880301908450091000000344030481f11500b40c2541a030f69444d0441c01c02d807840c19500d12850b9520b510503401455101c2080c0200402140c002150314000310720700342c0d00c41600340f4002d001ea40039a0142d020850800c04400103100d000018100304420606140c907003204031060780414880c240600d9103c10700c0581640c41181a0016200360201c11100b074100b4a95a130240e054600180b80a54070b00408140700500b8801c0d00380d400c6145603a42000403691100881d030a400030b40044030032030380f224034540000107555000000341003141e48422103079401c04410143c441c082821114000c954800600100b0b40c0202200c8039050681800c100f017124640210b0908121500e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642182580 1250 642181330 642181333
    0x604150b21010b1213030206011202060706020a180609080309060d0b030109030305071709060610020f010e1c0c051b120304030809010e0a290c0d090303140f070602030c0408 76
    0xc42c079041540c01070154201301d850004035aa0b80c0c00e48071084096081c80250159014000400c000782e00c1010110006201810039420312600395502802e07602704240c4100411508141d01c41c200007804070319001000286040030802d0300d4402590348a1003181512030107010700203842c510350300c0190041d5481c3c10020707008122012090070002d00802003510a040051082c054031503282540008860040c081400038020340d441d1a01046490a081580c0c5415402109a0070001044c03e228600048200c10054884826440d6140c1c002001000440042c45040c0c0d0008000c640c0015a820790190920a5052031000c100001354002204010452407480001404010010810007508804000ba250030b05211035810802c00045418001e00c401c0a413101840d2419002c03680014160810200d8001c2c03070564880b0381a82410207803403011001c1001d000c010802c00d54450010705000c2d09002404e4284526186032044601c1414005000c040e004000b181408510008403002404400c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642183830 1250 642182580 642182647
    0x7080103060528060501030b06040518091903020d020628050628050f040908070b0a09020a031101080903031003020d020a053604020112020d1104090e060604150b 71
    0x3d000c03005844a4040c081c00a8180b918114242c10058143c40540750010440c881d052402d40300d08900703c800914060711031080c10035940c0180032441e03020700610f020358040c1500840c4003402900e03201014011080403426210141c1500000b081c0b014400c00b00410081841d40707134080001c01c0400b01102030002c2c2800a03600c040a021048090401c40e203040d00c030381107420079400421080310319411002d0000c501c00c10140d000640d05034040c1e6400089070000240c00c8110782c01060640500b60402c9484901d6080c0b60356856801180b120382c000404001103145103482c04480c0080411440003e00612081c05030a04540e0707000492005814060034009400c01514140340c8144982c00217402d0518203003200503403107104840c450380300d42d0b010303151000d180140d084a03400960001e8803c00d1016626081042000c0741c4000900080c242c1c40004100c000080345610b00300b010113031180d032145250441081c1756141211495084548040d800c035120000a0040e01c02c4032842d0040640c0c0780c0805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642185080 1250 642183830 642183901
    0x10090f18060503010e060c030703141005090a0e07062012190c08120919060203060324060613170304030b09150f0c0c031c0b0603070801030605 63
    0x50204584405008800780003040c1c1e5501490b0881d01d804015001d150820000038182c000340d6001507070025024900000c02c00319050080c8610032090341c142c00b01c076400420401592910240c180d40001e040e110070415070702003c007040e03036910042c810201408002201c1c07102d0180c81411002100b8502c40a4404500e410407260460354820b8580441c1c00d50401c6403181164800d105646803941c2c06480705142c002c2143d200c0d015490002c11607005445007000c0080349141e003254200c504d034400c1c000503807030b814164200f60a250f6400340610000e603062090500311448000a10f42203035040d940b07507a541262501c903002650068005404504020300050001c00000004001f00da0280e2102e003419269800d0035a00c072060100041d0b582280000030a0500031a90503064015240751451841d2400b160003031404c0d50840041140000324094451010003924002d407500a40c080b25a28a5890150340140000106010241030f85584400081c042c24011803403c4458807111005c60110805 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642186330 1250 642185080 642185099
    0x3061514091501140702061218150703020327010911040c0905040f090b0108030910110a021005090d03080a050109060501020d05090102011517120a02032712030d0b0d08030610090f 79
    0x540740c01024408001e89c06643d240701207200410002060b00b1002192200c00049000e074201410503421069050442035489072000d211006400c0311900100b41c0b1181402d15400007103600c603d081c0154144040700030007d52020700d44040d2801114005a8046050f120400400803147c0c000c0421522800100e41d1a0300040980302ca100200d038000c407400305200d0304030344841810340d4400c3d20f03501c048500b0b001864040c0285a5003c41ca152131800c00840c2400155010810075003134000c03039103190902018001900a881c050040760400740011450000002d50f01d81d00b50700e442d8100000070440c0001e07603200790020b640d05807140307469000194a40091401450050801110b284650800600716000f0042626109102a0003035070a001801000b01c55840d6886100e0007810118500e1941da40d54840803000019480d0004644034001e881043c411151100310461048050a0301d407000520101c1c03c0305da02c91016100030b402207200d95410740795100160050300d0f6988016030f020802905 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642187580 1250 642186330 642186367
    0x20a05070648020a020d0201080406110301120606090605011b0c120308090d0f0816020c06161a060a150e181b070b0a050601090306151409150114070206 67
    0x100030911040482d040400782d070f45a031003090082d0891000c05101000d5802500d0555103c1d0240c1c00100348040300c50101005a0301c240c2002816060f1480c0340000d0040522910300901003000c400c204d00ca040c2000a400b500c0b5420320241c850249844900401410000210091845940118951003c0e140140054408446440ca40e1081000d100c68042c85280d50142e1013006448890a42d141c070070381c52010450700c040560562159580c04015074480310020038142240e44150440b00049103815150b050020803c1002151043d061080c10380d92080b5243c1103404296840a610091301c42c25900c0040d503140c50307544032482c030f08504112401404654070030120a00c084c8141403980d051282c4c280290b0034050070b500040d00c001500070307075694000d81c0c0107107050400d080c05583c2c0b40e5600c026580c07000886544000701c4001000b4021001c030310300411510484008285182558a1000080c01c9250881c100503119039041407007544501203034100358001c1c0509079580d1000720607070100300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642188830 1250 642187580 642187691
    0x1502032206020301181505010f021501120605010b0a0f1b050114040c060329031f1407030204080a032f030417060f0406110d091203050901020a050706 66
    0x1da2030022000c00d121544a0301c1c0032501c00011b4400154105001154010540c0511030103521507201512a99902614018020030300c613041a034101c40b092400c2d00c1a104180d01c9261181002c2c007580b051260811602080da644501d0045070004c2c01055045121204150241182d464940e42101030020010164481c0d8040c80003400d40c0341e913401d000c4088410210342c07846281c8840c000d605000c03039414941411303160020102c610180c0c1c505000c22500d2560b00e06150341c9956100c600c564941c1030700c0900d0f0300c084181400c5007401e01c0c00754456282d401c0c010b00182000211251050800440800003491b0111030058541e0710005458181c0c2d02d41c0603019540c00528020711082c00384030f000442030b00c98280e1496030441c170b8807256102c2014141c60264095240020b00c694042d43c1814031410031414040c21403081c07407240e060703030140807600094090412a401001407040c455005800c81e000709600c00b00009685001104014030360542804e0761005140c045012110f40c0642c0b201c01c2c8030721 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642190080 1250 642188830 642188849
    0xe030a0903031803061b0e3114190e0712020405070908100c111605062113020910030201022503080708270d02060702130c110c0306041502032206020301 67
    0x7d45002c0421148100c6400340011040c0710401216000321010760000c2c0350560300c81d0103c4c4030b0340c0d85003010800c5e002c00c03a88000e260f404040500141c213403902600840852005c0940074190810115240d6202c2e12000a0f015544134030204507801e100361608001040c4172416950700d10360000340140900030140040d03000401c07107808010003650101e1180c0d040c801600160200501d4802806410741202070a184609280e8029410000044010620031384100240c28443d100c05e104000348190058610072010310404001c1c00140d8000921020f904240c55440e400c029400040104440035030700000d02040c404101c0c4401c0104c0300c4040c1c81402521007030180102c00d0654611296900c003005a80d04c0b02a0320001005410403100810065001500030034170708410740b60042c10342d0b41c200b1081d00001c8414281c055816400e011020200f6005c50180c0b00e241070035116950411140c1055007840703a400004204c441900c0810301000420300b03148101019128104040203410034031444a90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642191330 1250 642190080 642190097
    0x901020709050105060d0e030412260313020f03010b0d080705010b03030c100c05091f030c0216140f0904061401052b02040b12060a0e030a0903031803061b 68
    0x1120781a0280505031600904510b0424100d01028005040549211141130004000201d104003081d0319040080340960441d40750110485a101c808620180d21520404014010301c000d8001c140c41e5a40d0b0150112060315004050100180c010242295040d034013800c2d21030401c003000010702c09018010b00078030080080703013001030515480341f01d00c140841e080d411402109182e100942e010507111641450490f0030a5821808591344900c50107156040704204000010355561500800c1e400070024030240011102440c030401c003000c1d03680a0008441805000d000d100e44510254000040e0f004003424000d0406c2d0803d0001400036604001141d031000c0300100e001d00f8400d040804140f411081c2044c06003500e06100f8440710761b9001207030b02a89480b0216040c4d680c521980c2d54262106014143c0d500344001510704031805440f40c0e0406400500030f48401e15040408501140d0309400d0509441c0003c4a50441e20305590700000e04107071608001e04134004081c000e4100280f525220140c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642192580 1250 642191330 642191339
    0x1b07140706140418060509010602010911010504060516060906020f040305060f0f0a0f060f082a090103020d06090b010e0118110429030405031c020f03070305040311011109010207 78
    0x15451211009030007482d1041000300580442042404e88145000780e0000c1d0781030704c400003d04488000c1c0e210b400140e4407110a00c3c284489180c82c1841c0c0b8030300342442483d00d8078215015100740500015205ea00001c0b05540e818002c00781c120146aa5000354115900d20194600ca0102e030041d020580795441110006940c0842421451b801074405171200d440070790b54026a84040c1a00c0d45107941013940380c000c0016800725a101c842c0c09030400c04d0191000c1c28641010780703280011281480b0640001000c0b00401742c44622120307041d07907011345940003101c10504103280500048040104090a4540001812172940544038103840034400a1081030810301c0242080d40d0031440c4040b06039900304010080c8500c0c16650310710601090303960076a20070840018a5094104460540d4540c00005e00382c500c1d03001c2c12034001040701102104500b03060410206210728040108003406043d91a0045402d15001c1e1030441d071041100002402105d24183c0c0000751034201e451100e02600c02e0b43c0d030115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642193830 1250 642192580 642192587
    0x2010203040302060f04110a06020d0e2b2a1a121f09090c0e06030a0b01030303020d110c0106030203010506040903020a080d091406010609060c03171b07140706 70
    0x24091034255000b4042619005404516017402403c2212080300d40e000710b407400c0c0c60f420000da00070685034000d000c0710315100102401c070085051009101d48000340c80400c000300c1c0b040800307803180804412080180414604801410200d64000c04c03100e1090300c1009400545405d180291058640c3c1d21028010b20b8820354500d00907510240902111040021007203e22064100c9014101e91201480300c1e03980c000b90310440742403080544945801d501c050100c0400d0310003040d008182a0700901916125442e501540181070000608054000450001c068440d401c03030700044281c40c4640350340750031080c0071078000d10092104034029400c100007c0d01e2882c15105489100e030301a00608041c040641d25401ea41d80045400181c041e903509043c808a4010100707403c0600c15640100245d5040220250500e82d103030f4003c1c800c01c840039072084006640680c1120614294a0541e04152281c04200e80c0c00e004040e0501c114920124455080c041c041c1090b8940803004000c1e10306498545204030b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642195080 1250 642193830 642193837
    0x30106050d110f010e190806090f0a08162f09100501030209030f0102160b06150d0509010e0105131a370c05040303120c0806060a05070503121006020102 67
    0x14018544540c0c0c20301583c2010f1040040c80d90051408289111140001400d0f401c800c03c0224120090094217010740041000210740008011000300510100507003410b6664905960041c50081e01041c8502d2044030068082402544403c1080e01c01081c040a80119151800280e0200345000c40010300341c00c008141d540558003100b1810b4034a0301740001980658004500f6507014440c2c120317004600c1e8402e20103002140c05906060580740d51600b002a00e515003d405c1910400302074218003042010001102e126103881c0b900401c0135510401e500e401402c0d51182c3d03030303540d50030b003000c210302100c40c0420400440d114004614002c0c0d408046469142e204a4202c0c1506070f5042910007251030315511030198120041110b8480d0036009462000e1301c04185140c0081503000c1020700070141c200600c40c00b1000006030400003000031400080840380d01600c440e00841e07001503d00078484c0f003501101d07103550b00001201d6450140508603528490119282c00d2080180c68010507042d1040c000c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642196330 1250 642195080 642195083
    0x302090c1c0510210206040909050d020309030a0b130507060909060b09090105010c080c1f0f2d0e1504030905030601080d03020f0408060703140a09240216060209030106050d 76
    0x1680e0710b10342042c0d4100314110043d042c80381c80740c0c1050395030001030b40d4030001803001d04104207000c42c0d130103070601d42b036403034203406204840941d00140401e00d034607180080c4481c4565001a4040881d84541043c0146101070304d00281550040440100d07044d0f80003017448086038070005080111079a5242d00c5110341c010500400d52205180b801080198444d00c2c0795981c59010707140243ca01000310a02625143c180d004406488003c088105110111072203042040b040940c424040d0300340c51703d035401e40c45051124212241c0e4106090464405041c0d01260800440608452204042c0c1c841801441400c580c210b0000e03412100c046001d05012a4042c101c070304500007485c901c108150146c01942080c04501c0070b80d0b4003170200061550b420012280030380c4c0705840c0019207580041440b0305240300180b0101c0e44a05002100000842c04881000c414101c16820405031000d00c4030302c1c0c0030344070700f100c0304ac0103201c07030407520090101c5a8020100c405080380200030059842c0280060a42122030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642197580 1250 642196330 642196351
    0xb0a09030b07110a150c081303081503010c0306031e030203030c210708070e03010b0a06030203130c0806010f080105060d030309150609021213080a0c03090302090c1c05 74
    0x8104001a41c940d1007035001000ca00382000141110314140345400408402501c010301c41c603805131401000f91145c1124604580340c644918a00394000410500e501ca0009082000b40c41c00102e414140d00c602070040d00d0300800038451020740e004028040c0c0842d000946d182e941d2106040070203038101c80410300059040c1c015609581c2c40114010300b0740c10603945045980d201c00340e1540c928582007401c07031007a030103911504503d041004008118040c1c0040c041e010f6858414012403d50341e4140d8030040794002d10300907039070b55a1480311000405580400824182a07a480407441c01d0000c254a0305889030401140c0e038031541ca41145003a03a2045e1015500101d4003140358004c68401c0e000b405074140034640403022800120100d404544140c0c1c0580c41180e4041031010200c813080c24140d401c8034a241d1032181911040c0c5a81c4a03500c00c0c01c6140302840070f007000d1442090b0090b0728400095400404c41601e600c1e00d44030641c041e0b03206010080050a6017648140140e20b180b0416000356480c98 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642198830 1250 642197580 642197597
    0x70e01091406060903070312050d0906060e090708061504060b0d0912080601090303080402030a0c08010b0f04051608061f0806040612050a03051c09080d05090303131104090614060a0b0a 81
    0x7200c80c8c0450b841d004080017084410800201a04000d0040c00d03030b4940701c3c0100181861a0246030500080050f290309155006580b04111005000a809070000c0b100c0d00344041e007a941c00000b40003440c050b0b0001d6410400400c0110215071103074010900d00340142140488030b803940d20308a504400c101d030070601294070b424090010a100e41010759109201804896800030f007500e03174500e29980b0f50301981d1641e4403100c3c004081d0030180310350300c1d1442003514244103c0c209441c03110f10741005600c030030b4200219200040c0090740d0303001080390b4040f02150401169210180001d0071204200e909a002c0c0c3e041c1000003691551545107003e1094000010301401d00403550112000e61011f140740aa4032250a966041c20105101d1540818440c13040300d680c0d1001c9414490a80d08010303c5e011540e04103008000c6221079140d1046025a800081300900d9075030000064010000400050034841c603001c1884006006c3c011181d001c3c00c0c007110885007481e0b4815050025100d918240380000e0b45d1007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642200080 1250 642198830 642198833
    0x160b030408030415020d060f0f0f050d060b0604030803040b01050f010c060f0e07080601051002070b0313060609050f062119020307120503120a060620070e010914060609030703 77
    0x5190000d00ca60001032440303513000c0301c001c142e8018480590450b5580c580400c048818000030034000e010002122941d13503c0d00c4c00002c4054414802e07540140079145010042203a00e500003d0089001132216445585905040c1481c0e00215401c8824100c19400403d09180c003c000050350481651080750806d05c0f42d0300e90f0003400c514550901d00c42d881d041c0c8941c00c060240405405803100200820b000e6140208200003d51000030940544d0000001804807811510072268003203280030b800c013036030580c41c07400030000c3c04540d12040f182c0d403503d020300104041101e281400340d80d04940501c14a41da940c1070888050341404128003d071300803c2c1c2452001010352030786a046000070140d5081694480c4031403c2c2080030b810464081d00001894800e4451014034982c1210001d030080203600c1c00d1050141c2105c480c1802280ca298120307203001c18138641004160080e007112070464000d541c5d106200f8000d89202e400400b60300d42d1150010b6142c0c02d01c1029201d212a0090003803046070701c0d6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642201330 1250 642200080 642200093
    0x4030209010323030301170606192603120124020d18030c0306020c060f0106080c0304151a1c111020032503140a05090a03050708160b0304 61
    0x164005001d03519000844240189030130720103180240754107105001011001c80c0500d05080c030060140d4030950307030804011440510702600100317513031542c1000014010f02c40103001000c0c11f0044c0b48040b074400007580c2403281c0341a005c214120341d065820303502d011a02000c400302d2120703801c500c10010b078442d501d8003e03018820b41840403105000032880b016680c0302d8a50369000049500261101500040c4440b904a000c0140d1544289105c48018542d41040002805518080e201c1030307116802001180030b005810215000c2441803100c10400340301c0750642c0c201400c0010000502c0742c290b000400280ca646064029603140d40a84160904660881001801c0d42410104401c1012883c900711007a40d401c0780303070208201118011f54650900740e51003c441270320152042c0c1c0f440a00c13442c550020340c10112541000700d0903406180c4800005108a81c640140007811307600000480c0c0c008103104c40030600c81c080d5680030003550b0030044160b0760004d00710100d100700c0321042410000100070541 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642202580 1250 642201330 642201353
    0x110606010e0607050601090c080907080705150d18050d110604020409050a080706150b0405090a091407030b041101080c070f110607060b01080105030c0f0405041415160203040302090103 81
    0x200030b00740340c200071040c2c030380e1413030640c090f002036080c5903407807409a0b036841d080b103000d580c42007074007004211042c140b2207010740320041c51042034000d600014018280000c440e00f038a604a122420801c002083c0081c0318801c1d40a00d074080c1d465024008440791021321072036240e80c440300c1340e60003414a0b443e140d081c000248062041030b04c0a0084c2c40900f000508a24000c0820502135030002c501d008115001c02c00441503540b005072910020041002070f6124240c1090384000c81c0c20000a0120590401c2c0781030111203180d104150246134004400c210050948600039070080b40c09107055402c0000550b14001305540540410006201c503000007040000112911840b852108501038035003070100d00f603a008418111101a2034034800901540c0c00360300c042c0100000c4000300003220401c0b02003401c42ca0b5211042d40500d488000041c1400400c00900250b03031464000c031102220704290aa05840c001e07075001c1c1d80c031581140c40e41310462000081d501078070340040c480d100036407031507640786000030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642203830 1250 642202580 642202607
    0x406050102071a0d14011508060d020616051f18020303030c03040c050306070f0f030504020f0f0406030f08071712070503070315030b0105030c061914070501092111060601 75
    0x154108804041000c1341d014030064200c1c014036051443d4100303c4c69441c000622000d20080114910410107240e4031802203184854040e151166030320840811010403142c64039014266106100f0034002c0b40701d20072100c0b800f010809500300a500c01e40302e624080246904c0c0060b46c1640300b840800d0040000400854006100b502103294290b550000f20342010b0040712501e0216511141c41d10040d500004038440111007850200180d292a60028014441c0d001d0068020a4028442101900c0300e601c004040d40e000b80030520003400070716003030015a10280c0d04582840311035201101c4038503160300751a40c28058005000569580c010111095000200714034100b588406441100189000d031140c055809072083c2c10080d030406080c58941090303814134501550040000841c84105101d04220243c2707140780c485020301460740b41e03090380c1c001c800e030240213035103400110740070086201183d13040300400c0d04d88600c1081c103203401510040340c1440802d010383c000c600010001d41c850403441e41501d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642205080 1250 642203830 642203879
    0x9081c0f1106072f070b0a0c1505221502070326010317040317030402180123040b011211041805090f07030302070e0a021603020a030e040605010207 65
    0x590007400e071610b070000944001001c214400c050340c1070001941040d0401c00c3d0b1921014072203a002c40031030b9540760828440c1d80e0b8211408908902d402d485120300405094000300f001110380d03a207040303000041000361020391402d0380c20001a0344490028240e448081d400400101d40c1c0443c07500c07280701070351001c4022410003440c0d42240850102c05002e000701501d1b40200c02c1081e40c110300e4140078000d071000c00310946170810b010400020f0480c0d45840c00391025240700035101e40300c52000c901d030811440c250700d2001c090b44001080b071980341403030880300103070700c01c0d01c81020100141840704a8581c4892680045c107040c2c3e02c1c42c00b406903a000503103101c0002c12094981540c0da101d2003044541d80d00c100030318948603000c2c040404400c01900c802c00701100c0251041510b59039010355203090301c3c4241d4043c2c0007030714005103c0740403a60503200c601743d518204011406451a0082d2550b120303450440100d0b20002044801c1e003002d02c502c100703803407040c1c00401c00320f82130814402482c0c0202500d880c88 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642206330 1250 642205080 642205097
    0x1171903080a020d0e0a030f090b070f0c080d0c0506060f0f1c06051501020f060609010e07020f120436020c01021303060e0706080403050313050f0d090609081c0f 71
    0x20160941701c0e00007101000780140051072820f00e00140f110381f50720120f20030405003401c14000100043e04940700c040e407004a0100c1c04080d468050783c0c0d01902d52211035240940d02003040c0854201c14609041441381c400e507100b956800342000201c045d0b8100e010380044904400c61810b08100422412903040b84100c55180340304da1b40d0781020b88004031500c0380001c1c01c1e1020300c0029601000300302c032600d0040c00582014a00700001c2152074005114002d6015001008241228024440140c48224407025940c3c0003007a28a5116a41d000344111030100c0c155170302d04102c5c40b01044078400e0115031003000d040455010303047d80c000b0750000038405525550800401e0604d0040c0c40c4c0c0301008511404000c00da201d138046403a418265030f41d100c4c0c41848032031820800001ea01404403684000a82d902c803408001e02c2c2891880c0250324070561680b442003c13141000d046d00940c00c1d0301150502d07600c140c94680c03101e000c90749600c411018603400118804503500c5450040d8500c241c0290741d450a04103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642207580 1250 642206330 642206347
    0x19031709010608120c03120109060f0f050d23060c07121d0603070e04050f012121090504020a113306060f04030f150b090613021902030301171903080a02 67
    0x71280000c9c0d210b400e0046c1c1e13500d010020301c0720100412700100360549281d5001850000400c01c0e070204071030000c182c01c001101010940e54001100d01c1c900054200300c41261600c9141900a98440b40090f91818004c9010740031a038429200040711030600f6206641034002c41062001640014100c0c500344003450401c0040c5844600c541c600ca080010a0140c455142030000180c285203980c0500554501052001c0400c0d005841c006100c101c0414904903642d03440002c64030103005401507039009000143c05800e4a5205060320048001c003001e0391b03394440c122440410510035112500f9503107010780c45946040840b020154018005003115190140014400310140e120340c104071103003c0050f800a003480615035201800043d001020400c0c460620001108c2c0c0000811381441818481c1601180e0201034044e52a10001e01c0c94414042061ba40040c2d03c070b820034090b0312110310401d023085206000000d4130003d02c010701e600200807003910b51412a041c640003082c1c0718a0580030490b941c0c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642208830 1250 642207580 642207607
    0x4120c03050c010926071a0907050d080c0d05130603050c090a030807050c09040b041112030d0b030c0303250807020901090b010e0406150c0519031709010608120c03 72
    0x110003d220f4070014402c100300c0385c181d0b1103181c281d04608540349802c0c0701142c00118400c00a00384514080441c014680e1110062840d01009811081e0400b580410700001c2144e1003001e001c0902c4c058041d03500d940e60a80d41110075004003000c40c21000d20090303042095500035400541c01800080c0c0c1245003582750b502080c2203200c80c0c1e00403100c1c050001091303818420240a41194410111403280d69800d2580302c500502102400140030a21001c810650b41d582d00700c14400c8051030807042e280c035145505064401801c05d904030601a028070008542c2514010040f500c0d0150045403000d49403800711840f8400c07080041084070442400c102000140c4e843c441c0a5000748111007000c59421035640004040e52506a680c03030289003030103814407101e0081501c99003590385601d041d50f0101b1240c01c0c05490b080d0004003d9814080c0f04403005c00b8564070900c5410014941c0e001080700740c0b2114081030807030301144580352141d00091340a401400c0100d004003941886c0341c0483e4104604a03070240c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642210080 1250 642208830 642208841
    0xa0c0c0b0c04030c0b030402011202091903051b03011104150c06021c0e011b03050a110706051605030f0c030c0715091716080705070807060206090106050904120c03050c01 75
    0x81c8100c007004141001040441e039a240d001d00710b0050301504500309036002a04c1e00c074071210600d02064003c0b4030701c0403d46440c2102c4807261300381a0030502d020ba0320b00b030003a141c8c0306000510032036080411050340c0a060500941d01a41d0801e03424a1074185000203a5200e0042200803504102d501001100401d0081c000342036030314a119447c4a840880c07040380d20455458065074811030341032900101c8900d440400740c68000c0024100403c40b65216103070a001080060702e40c6140d580040741c1482402826070020b0311481d400901454040500308060352240011180d03005540c06100004903614007510156400100980c1d04901304911a92800d144100340d0f0100b800a564801c824010305c0f503010b150301007516204565900c3c25401e18000003180720b0030310016110920002e808020014200071b8400201210002c4d614050f89546001f91110f5082c0e0f07225480e9800c20102007040e2078440200390281da0301c03850207040d11003206000d841c48502c0030800c2e401e0210a104d210905a800e0003035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642211330 1250 642210080 642210091
    0xd020613050f010f0804062d09020f0a08030406120f14040515072a05030a022103060a14030a050106082406090c0f04030501060603020301170f060a0c0c0b 68
    0x5054140e00340810b011880c104100d03410704200f40b03540405466508030703000030b0b003081d0054000f00711500d40340307009020340c6c0d80e000007020340f9407941d010090075864681c07081988038421940c844980c5100410090508040e000d01009904204800c104450003680c00d138030300c54480280890307500c40c81d681c000100c40b00ca1a0107029611600200001c004043c0300042d400d441a5140e81ba480c2003940c0c2c020708641762540369080c040044050700145954800707500201d1503110041320382da100c044500949840039280010320503888003440e0b00e801e941030f10960380325020140c511315040e072401044034080b480c0711a0050f00340c0103080707041c0701043c2d0a0041002a0010350003c00c04400c0d191100160074840050721110b688109090103032a0341c51701000c030b4002001d4002c0a4484210581041d058412540700078000d45c40d02100113480d41e05500518100c4120010405184132824007807078450049040d80225900070380c00282060145512030f8a41d1a01c0e460140c800345043c0e1f40f030042141083c1c44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642212580 1250 642211330 642211357
    0x105100f03111317010c0518221d010908310b0901020f07140108040219121712012706240c0f020904140616020d180e060d0206 56
    0x30305121158408290180142c0300c0802008510b00306d490081107801207100e00310403603460242c040a95582c07011048096000ca407000c0410300d010510b07203002020040903124612000742403c2ca9489010312440101a0b0400d01c901e1074015581d19187d0442041c2041444080600c8910381c1943c22300c000321406040c807107400d155074201810029182c040d064415022640c804201401441c640060100c3c01c03503000c3c280007015841e1840010781c4d0342d5440c00c14140d8081019400607105201d028131110460040c400340801d500d03421030707030401740c8200076120240c501c05900412a405417801006490801e0001a20091185148410589195900c442c80c42240d0090030b41340c0300640d03050035441c6121401d082034100c0341e03596180030506000e034000c0e205903598070008051060b07a10348040000b0341002611414035020070140843c00000550200600ca00002d03140c24900549280c000305107441070000c405440d2404211401c01c2c018542604504c850a49100584505002e824441d01d44407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642213830 1250 642212580 642212617
    0x308010504060f0b041502190c0e06041a010809010f0207080d0f060303200309180403121a0409060626010f14070302030411060c1f050105100f0311 65
    0x1c000a642040e00034110404100354100040004401200c2c1111803a05081c03040001006084e0305004031030807480003483d030842d00e4404020354842c071b03501540d00b0501000c01d282c4854060200b250050804003112601b60f03010414198002d044c4103600030706203400032502c0e170b42c40b45241c1c0c00e03a0000541150441c0001c02d1140404005010f84031043c00301c0c0e00c0411443e4a0341c2c50042c03814004408003013045042c07800b55807840c44103100300c90b590517000d086820f000004a0025900c100200e030241c00054444070980c498007204d0050148111110041c181c40d429101c08000007401e65440807580b46541ea1030014044040d001412800b00c4110103040800c0c40c0c1509850039912034204000318180b40c00303040e204903103140e42e0b000d8001456240c0140c49a41d80e2520640c1d0200111034a0fa125002040c0807080322000512000301c2011032108100000070748240310305494080c0078250380400c00249400b01c081c0f003007490100710707281c615000c00c40c0c0c10111103403e0550301a40c445600f170040300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642215080 1250 642213830 642213839
    0x1509060b0406020f0111090d0c03060203010e240f0f060c0613120c0f0b13020901090e010b0904050303130c15020c01110312011707030b0a0905150405031e16030801 72
    0x5016807500001302e0002849408041c0031120654070488207024801c5444610103024040d0f2001c1000180d03901c84001c40d41c80d615200c0c40ca107880403c072000c07001014440c909002d6102c1482c14031040f44005401c110100c1c0d03c0d0750030000f0b80d002c5440140e4000314180642298040200521400b41d00040d4510110380e68600b803201051030041c01c03400500564030300e05c2001550202c0c02140035900180c45010640364640c1c8885800c010010103907019180b4000400d405e00310358001c80301c16298030020003c1d01c4514060001e40c003c00c8034060b055403c140002001c11007424004c41d1a2481454142d1890b078031074603141c407407010640d06007006a20004840c1010b580000300081d0840c02e907402542031041d4821020252a81401000c03042001c562820380d41210030803101c0055035100a14105d0340c54400d201100400c8982029030390352144122440ca8901e0100d043c5000300d0f00180070703500d08100310702945005101c0347c941c0d4204140030080c0412015903c0e003c0c0304018440c1c1d44559555141 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642216330 1250 642215080 642215083
    0x11203080906071704060902060a082d0a0f02190f0305010b0f09040c1110051626070c0b0403080714180121020c07060201060801090b040201031509060b040602 70
    0x200216420303800340040c803200d40d1304070442072190414020201c04680d00c0c3e1400c2005041201d00080d00450049602188560403501962260050721100d040e03000341100d140d1914800c4005080038020048041410b84101e604051000b2006039000741c42d20150b5404c080c801004171800c0e00c0000d000c103107600744955050081500405142c46c4603418001030b000544010710030140340d07510482c1e980108841540c000d114408403084110306541c1040c020401a02c068142214200b0003000704003115100c99014858165034410030310040c3c9041c14100000f1821540054502030a202d1605040400991031800d00f620540c402c0d6038070380c424108190060100b45158400818001040c040c030682c81003200100c000c02042441c0c500200300100c0da0301003200181644c900c0b030300d030b000007107007168007100107203860440d2a9a4020002c0359942c04645089800c10303000100b88802c0e200c0840c001d0342c4640c11a0700c683c040b135170b02c17901d000d0380c0c50250f5011030300c2e56403100030b000700081020412640c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642217580 1250 642216330 642216347
    0xe040c0b07080c10020301050a050907230403050f01060e01170c0411092d01030c050912160801020307080c0901031409060a1401050a032613030b0106260c12011203 72
    0x703e13100a505650400700020002c00c0e4a008050040440740e000410341071140b814841c03175030010055581100c035146201d060341d03031040c00186c42c0c0e441803803265080014144030b0345089400d010481007140e402c092400e12014019440046940b06001412405958910814050958418030300b580c80b40040300b88481c480c126000460700030100d000c06001115061490403240c8400d10b40080c00410380c05003540c06016035800d854200080000742072600344005000c1c0c0746280c02d011040c1141d03039560003507402c1c1c1c4801c0320705000159802c404104c07500c0b00b0750041c001120b414100490000030745812103d280c0f80c1114441300942c0228203020442d004c612400c10383c0a030341003000329158100004180d5040c0036100c000c00b03081640d11221900840240c01c200b2000e4204040fa60300c01150300a0341b4032509a0006866080f04d80c1d00010790700b0300030420301070348000d401094140011508146042c2290007001c3c13002c841d0b420024590240324500c40d80703010f088072204888103441e0b2402c00508000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642218830 1250 642217580 642217603
    0x80705010e21070f0209180a2a0803040501050904090b070c260f0d1404030201020a021506011709190503190e090f060307030b04121112040e040c0b07080c 68
    0x8020461000401c4c01c80c0300f40c0d2420b68054804045d9516000d091010112520f0002200f5000341001d0074100f20b103810a1180d18503c042181c030340945d8a0205003a440c03280d10400e81c0039403040000300f10310350150003d04007511000300300064240b599180d00321603000846114001401d418002c01c20804100c20b4113580c070b11450f04078074642219026a8899110381c0d1142d16440d40003080a400c40c1c60107400c500100740c426800503140782004e24002e0b000c1d4100851900160059540c54034010007455251886070b08140d48645454401220800340040c01034400000c0b4064000080a080014140321007641c0c41840115510f2244605d6113060307a0801a01c0700400100115030581581c4540d0955084808400010038580f98800002d1400803540d20041110009000704000c2c0f22201c40c05d14181c250a0b22001c6030060f10060740b589940c2030300c815510103403060109004203000410b20302d0344903103d030329900d1450383c503032540103100d411820382156800c400003041613519100703104494030031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642220080 1250 642218830 642218893
    0xe030d03050c09040506030c0d05030a09091803230c0703060501082d0c03101a030f030d0e24010302100819090213060303020705180f060607080705010e 67
    0x50074010041d4400340f281814840c0320740d86403c041951680c3c240011507900070011710080309040c0d985003e90300d942024000e480400c1185000254907041400340d1300c0320709154002e120b2401a0765809407900c4480c295044850244051189a03040c00c083c000e080c1200280d000301002c5c0c0c03552612805592058201d2045a000385802501710900c80e8610203070030f002a500d458601281c000390f00c1c607145403034004940c940700b18950501c247d40203900c0400c015010000c00c040d841213131303018140d541440c0d500410941d4020049800b08003007a40c081811000706500740c80140c003100400c002004403000168101260751001001189801d11506464601504004000c0d1800040c02c4400b9040c440e0400c80c4035480352070b540308540d10b12a030030b02001800b0408005080d01d0f42402541c450603801000d0059400d00a003020b150316220b000d43c49140150380014141d500c2c3c0040c844a508255402c4400b450309001c01c000040081c007c0e0341413605030100502407404003441640100c0403007400510b08 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642221330 1250 642220080 642220091
    0x201153b01030807050f03040e100b0a08150f13020a0f020a0c0509040f061409071221090305122d18061b0a05060705030720030706020a0e030d03 64
    0x2810044100c00d8110b94100300003c1e12449141899400d140c000d80041c0d1540c0000030340842c00c465244032017401882d0707203107106540c0c6888050356000c1c1c1c46826961700200c0c010000083c1800c2805280701d00c00203025020380710035200038004ca180111805401001c0b690040740e030036903240d4080e078040702407002440146501006501c0d4540300425038000c0600904084000405200714100300d05c050f180c2c865070400a8a8483c4200400007a0039111450180904d50000400c40b01a850392206203800486420162050b222000a154000b00b85001800710340d603000008030f00300b808240640001380c0d540d0703990350501c5074440003450700380211418840006018186202d1200c025603075545212034409101c161520001081402086500c1c415508000712002d03500e003021486102141c0700e0170071101c058541020969190004843c03005c0010703944402c440303008480c01d40f41000c04100d074041e41e1922245884d81000e03607005c610710b540801d80b800c410022904080040402007140c520b400c100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642222580 1250 642221330 642221429
    0x6121e1506061207090510020d02061b0d150306090807030e06160308090106031709010311070b061c0516051c0312020a030e0f062502060105010f020115 67
    0x6005280f96841c0001e14400020304041c0110070b00340103080300400100c903961018100a58814501c45800d0041c05070301e0206c1c8034071504038200c001c0050140d074040d060524214181d00140010b665410101220b0440080410150322800f048140a15400c951b0f4811508020341201c0d04160b07864003410302000340ea14540401c0c640c1070b624640c940703400c01558803142d41d428007401c3c1c15040580f8040207414207040812800c3d0040018103802e8030140305144440c00030181900450b007015001007820000182c03070b0714200d03a94002e82c5004400a401603131850f204d1610300000e0a541210088009078140041c0c42d0409452620035440e4800004e02001c5940052081c480c45450209054000c0740f0500c0c0c02d4002e811000382d801e08542158000b42003100041c1c1d4401042d1029400a1041c5000e6602c0c064210100d4807900101d400601780383e441c0030011104040120850360840d5038580e01480300c0301c4d2a900181c01001c050303059407513820340344004040d030a000d0b0080501314800d0718039084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642223830 1250 642222580 642222589
    0x50411040e01080a11040c0e030d0906030606020705100804050a0c080109060e190605090a02030610050108070c030c0f081c0605040b0303070c05100314070c1b05010c020906121e1506 80
    0x91100c1c10075900451407c6ea410b1042d84e45592503508103501d4050a045069a00c1d03000b5155000c0351525070b8140140742d80c0d560281d8580080780112034102040c1c1c511480003900440303403035810070312440856000c4030301601d481d2500082380d0412829031751100408400c1c450702c3c1c01080800e0440300301500e002c1c1245200c0310340626911b034000309825103460005030200014003e583d6510740203400c2e1035044c944114520001003170707070003046e012480100c0401d600d940720300780c800c200c26455280c1b40d000c00c40302d89807a0100c83e100a8229450ba0b03041101c1040c00758120041300340c0c9000b600d1f0124845080004020075180c4615405c0d0007580144201001b00c1c00000c074450860300142c1740c140804c0e900341d90031800340c284540480e2164109400307002503142d204144a00341360055100769040d1000019400c0c5a403c41e200386030015002e180d2aa0162030711002c440d401407001004101041e00c504c4205040000280082c10280141040c0d211801030510040081d050205445405c43c9040c03000107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642225080 1250 642223830 642223853
    0x60b0618040f02040b070302150c0c1f06050a030501020a08010902090a03081608070f030e010309110105031e13020f0d0209040f0804030515190507050f0d0204050411040e01080a 78
    0xe40305907120985681c80b40040d0741120040c0154611090f41d038003450601a5940c581900c400e50142140d0f0000f88542c1d40b501e003580d0311503c00e90081c00c4a888284802101c42140729424a985079441790300144680d500c0315aa0011403054001507200c81e00780740080c085180507401601214010010603901d50337107150302401640d0f400300a440c2c40c1d08902500e040c11010503440102454030024400003070214082030404024800e95401502c0f0041800440a0f0794070a40000c08100c2204000301c07040d8001d00c0690361041e0740360300200c0108842510814102c1065480c021070300703038100c0c5443c01c3d81415a10740541c1034003640c9009120400394082000e42c10014009030095404141d10410400700300100c0700190303081001c03a0610300e00f0041040c000c1d90207489141e00c0500d00603198817841e1480c064107119030040c1d211182440003000c968402984100440d40f1640d0f801c1001240580d41c5101b010303010400d1200e240e4079541044d552031800d41043e00300403c079500c503101820000303010b038400303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642226330 1250 642225080 642225127
    0xb15090106140a02030f03040809130b0a050f01020a051606020705040603050312062d1e01200a210f0c0c090209040f0f090309060320130509010305010207060b06 71
    0xd15581e42502a8101d003140a820213000346d01d90000140320a000d440700c050540306004450144040301240365a02c200c0350054241600041b0b4484200070500d010100b54220b2541030043d5490740c0503a5807140d0410aa00824000000c00c4110a002076541044603c01230b0000303407400c0040741e086132100c0ea41c902490340c05040b4110000c1c00524036031105c44040d04c1207407445106032100c00041e05501e18100c914255280540d400401e40381c15880400714401200348181c540a81407251071240e28404481c0d541c0c01507240c442d415841e4001004005816460920318034240d2850020180003000c41c001114100100140c1c0281c01d00460481c07c8c2c0941101d6504900590b110003010101d40541180c498100c1031380c1c680302448044000307c4e001004924440e55a608240d510b403641036080712061a142000078040c80c02c80205014641e0081c4002e0510713140e0307000120394030710020f00031036400d804c2224141d40201d9500100b0000b400343c10140201210001c2c18201400f80c01801030944000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642227580 1250 642226330 642226367
    0xa180804031b0510021f0501031a04320f120d090219060221130e040609020306010815070e10032004090902030c0306011a0c0106120b15090106 63
    0x100500440002c1d240d000108005803141d44031050340e020194942c1c0081d120006d03441c60f11028100c0c1c034901ca03c41c8030306895002131040c404c005d15003201e02c81d40000600440d007200640c11409540100c01c8540c0c480e001c01c242d6000b501d42c1540791060708040c400360044015510030b004c07004c0306003907007016a0b00b00d0320b0b00c284c005950b80281c00040c4e40f5400301000c5c1c00c0d5a400444010070300310b5000c0740b00f2a03010341c002142c140c906100040e800c601d102e81070340112081151502800034a1501da5084c1c2c00501480300031030710180070b80009040040c00c1e400b0030750b240d11426480300c0e00c212070250305520607502e062164904101101003001100c001c040d103020503550758500208089480000c001602d09007030406c0e11151120b416200400c4011016882842103010f0502c8610b000100380381031700c0941e82e4190070501d2010480c1c0c0030750841a80c5442e0355403a0000400c510074407962090059004801d01d6040d0b0400c02401c071204501c601000c3d005061840060109a03042801080c1a010030715 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642228830 1250 642227580 642227603
    0x504030c02011b02040f020903011d0303060f010e12030307110319050702240306120106050618130f05100e04230c09040503040f05031506040b041e050a18080403 71
    0x34101c001e43c81e00100020341c002d180126a4200c016554007034100d43d03100303a0080007500301c00c1c00c05c030541c071a65603250030180d8010000030368503081110801d826004107040051810b00071034001101100d07100c01c038040c1a0310120401900e682d0041b00b00520a8024002c0c501d000c000201041ca0410045003500070721100043c1c0c0021034803007920032180c0c80c190f0600308003040c40d014403401301a03005580e6184103050305280c6014000040c0714010440700002c03d40303468456168455600c080d40c0710f60345944038909503c00300c5110741c079010f02d404542034042d0006961900d140300c500400c400d038001c40383c01c00e615010030001a84080514842001a6102d0748554502045092070b02d065148448c1d000303201c5200b03100c20004008081c0094900c00645028a02d0b15441030696502c1c84e9210000b200a00390007141590500b0352014880300b20181c0081186034240d144a444800b1458070f10b41d242e5078500401c51050514404d5809040d04024689a03020f1240c468051600aa00003d0a2107404d070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642230080 1250 642228830 642228857
    0x1f060b0f090117011809110d050607020607110c090a020c07060504030308130803190204080a050303010509071b03030b131a0f060c0a03110712080319020a2001060e09010c11010504030c0201 83
    0x18147c4102111008141d04454001460302e240ca8100c151181005171003840041601503010744010304500002100510301c203581030042042d881005004510b880c0ea01300b04840d005e180034022a0044c00454885643c3c8524515000b40280e9004146d681d44030249602000041e50010490703400811415480b00e01c85001076030b034802032040d40c0c82408e49202da45c0e40b5100b0448003001031412110b089940207900e07074030700c03100703842c11380254030812010804030340000c0010f070007039001c000740b194064000c2061011110052040742c0491030059200824202c4129141ca001c0a004031194400d54038181089030818000d0b0340c54034a482e004080c8101404400184101088004000d05880f00582c1080342a0304125041d90f1060340c0b12462056450000b810b040d00034021030b40003143e5981d450540e011081b1660204035a4202007007825521081d0000301014820f45580c01006488000108013010100c003030400100740070b240440340d051800700302c04250489907950501e0303020300b840c04214941c03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642231330 1250 642230080 642230093
    0x105040b3627010b030d0c0302150c0c011808090d08090405041b060201050105060405010f051303030908010c0e060304060213121a0603030c1f060b0f090117011809 72
    0x50720400191661141002000a501000801d9100c8020850b0740e060003003001d99426a9000848141c159003d41d00ca030110b184214003160740103000e441035a80c0a80310450010b2107240541e0f9802c422600442c0c001c2c4096001e01c1418456400c40c00c4a0046001a54038460799000b0098a17078030a0941c481040203000c1d0500490f900c0c040010001c020a141c14503098100b46080000005184883c1c0004622107005210302816500000c0a4505091410b401110300302e604540032005c00205002582c10040c21413102005117210b6100d0188540c241010f40f400c4581641d1003204010341f88003148066100ca208682d00103400403c0981d072080c89400c01c0080590550020242c2a81c40748110140051011602c1d40d0702c8688034050440d440710f108059890180b021001c6c042d80084404503540b01c4030345160509190400c03004101304e603903400300015603040b07060741c00c010000010b4403e140c0d43e4050310ac8a800320003401c02100f203505040c8810081d8414a05184801d56248402000d02c5807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642232580 1250 642231330 642231409
    0x1002030c0f0c0102040f1505180d1a0603060a0b1309020d080307050408070f060e190b0f1207020a03050d050c0904020304060f1d0d0c110306010605120105040b 70
    0x44a6580b40d0310000300c000706000350700510840c3c0c0c195111020101d402103048248900c6502180e403480e0800d5111445c1c040e00160245861360301005544109000919858003a036450454000d403010302e1424800307050610740010200c0c0c111030b2404810700388a0784c40161002218001140c001405a068030100b1581c4080480290200101108101c40e9030350010040c82604c000d01c091355055a41c606c0042c4000045000b60004520b002d01c61100341d041081501c1d0745400c110340c0e010b49203541d507240c002503584400101c1101c0c0c0303400a420710b40281e903a2512504007540d44000c1c0849001b13a100100140200150115000e44950124800c010000180e801c0508001c6c13045580741030074901000140801c1103400605420200c3c0070303003601003500f0a0340c91054520003801403019400401c03282c3c02c034401e038126840c00d035108140e900c2d51000c00420b40a8955502c60303d40c0d8101242c3d0400b04c29034140c0c41144210304200c0e003c07290f502c80500511b25600781203c84601c10010071610100e804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642233830 1250 642232580 642232597
    0x1e0a1401091a04060b0102010504020a0b0706111801200a0f110303040b07140604080301120510020703020d1803120f0e040c020d030b0906150702131524021002030c 72
    0x1082505980d00c0e034164000c40b14010380c4204030402c440507010b00164240c0d0011203020b076012011410070011a454038001300a1203100f8040020b00140703e4043c5076464110100d082c1e40e983d4003030b01c05d445658014035808076642c9018280c4115134103142d1b000ea51000004002040851000071b85801c001514442d10000000107050701e44840c0c07103200b10002500072610075a41c0c4200d40382079030002040807504500075904a00e056285a0a000e80400c6072007800800b01c807607200380c041c2040764100c98400b4110040c800c2d4084c09024680300310052440c120441f40321110b50101104000040c0e400c000d0366140708250900d0100d03115900c00681b9003280c1ca66449030030030300b0b001d00c0d034001d00e5020501c40754000c0580c40401103000005c0500600c50000c84900390484c0180234500f08d40e500c64006460031a10051405500c180540c26400a82c1c0741c00a125480315000c0c07005100a00c0b014280628204030011030a1031b1141c419402581e030744040028002183d40040401c0c1c0055204040b06c4003003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642235080 1250 642233830 642233843
    0x2030712080f011508060f0303070c0b04090507050c0d0f20060106021603031b0807170307020601050904050d030b010504050604060e10050a020703060b01091d091e0a140109 76
    0x1040300000c05030064038215100c0448078a044004916440040d04041c5040819520004503580d01801d1110b10415840c0241d030502c82805100002410f8920507005008910360080e1031300d00e08000309081c0d43c4042d003260b007400001e104400c1052400030303890030246d085207089a12003440030003e03500e08100c0210310b10040003100c50341041740d00000d40d442c100c410583c02c589100141d00b1480d800000c15010050006900383c4010b102c4c0d540390551561054000c10629103004029070780c2d21820b001e46400032010b08008020844619018051039005080560340080340303240642e5601d40b030351002c0100300d05140d07a800c080c06860748100259000740c500a02503139919034030345602410341c40348440d00a204400c011140020544100f00b0755844810303680081001d14116514600036026880119041142d48040040c10003041007140d0003203030380450004418209140d01c5401c0c0707c01001070151010502002c01c2c182d6034002104603440b600590120480003101490501400c520340d4042d100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642236330 1250 642235080 642235103
    0x312060423040302071406041a0d06030c0303110c0112020309011d0106030203070f050102030307080c0c0307061410150507050a0209090c0315010f05150d0e24010b19020307 76
    0x94401c0c108814096030190702158001c59541c030450342c02071610690701350001e400780000c1002d41580450640b032030403000012810040e400583e4001c0b1a099401a00c01d082c6584082080c10703041a100786048541d000580380035900640083d01780c403040180c05400030760000016485050070750060300103252105d403035180c017000d0903004c80c040c2a10b404168800d004030980020300c103510f03c00e80c100f25241a000746042d030fa0745500a0382c100d1001018030907000710420425206035010300060200b45e11458002803030841414100111030801001440644110b0744280400280b0310072680844100346020b90780d50055162050400124803002900000c0d035006024080c02c1c042580b810b0003d003642240c42c1804c2100220160034020322604801280e600d006200700e040008400e0301e9a410041d01501d07059404040c20102c600c410808a4070341c0103407110034080300103014628400c0c49801462880d41d4109540904c40d403081071580007003200c030340952001c510700030310070b0b02c100f5a08030640602 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642237580 1250 642236330 642236381
    0x612081b010204501c050d03020703090b13031103010b0a03080306010513170c180103061a0909060901050108010209010905040c0c08070c0504050708040f02010e0102100f09020301110c03120604 85
    0x250004c00c0301c1140d02c150081407035480d54140c0d107110810100d42140003007a440240c003100398029408201d0030b0f0b041010074000070a99540541c01424999007242c0240c8465185080c04000203a900a01501c680d040107032120032940c0c3c02d9031800560f40c0041c174003039498403940016a40c611400b440f14803042601d090000d03030171103031a481910015511003070b6100c00300c071b080800074178480521004418140c01e50040c004600c0320350050809010380c0041c1c8815a604c4030021301c5031141243c2500307441c3e00c52010400707809030a0003000e0051405000035800d2551050002c0d1005007180203441c0259030b241c2c41c01c11a04d00c10b0360f0040d06903400940007641e460792400c1c25802d1403058044c0302e005a040601080646100e503d000340b00d20b4008050200880c4c0a6004642c0081c19212090440c8a007400c81d100410740383c480c50f00c2c8143c0d07050b03000803902d144c1c9c0b050600b501d01c0c640d1050117001003802803506944010003100c1080c52009a5a0900d6864000007001816100c121641b0f5802c010882407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642238830 1250 642237580 642237719
    0x7170712090c030519020109090c020a06090f03021209030d031a150a0e01180b0703020f03223c0b03070c030810150c05010612081b010204 61
    0x82c262401801940c2c601032040e14170301c0810020420003400641910307400c004c0102d6603800348071000118410b9650042c803a850b05025201c1070f0303809640004050030100d080580401c80e00e04201256001181000c1103c00043d444060701c41e056024075807144411503c00e09180b250030799010009160015484684510b502107400128417000481c1d45d20708401c20325800b40941e0b0722010103103030000c24018107009006000d900084c2c0d04800754824400e4081609209101500a08075280c030742c082c0211081420454070150f41d170206e88844502d8201d1031a4002c064528070060314805052000164000d45515100070340c0ea21031001d00c0d0f40131080c4003641d40c0c4000401041c40c0607a680700c6440d19140b451030309560651103840c001645020489800034055040c4d800c10500850000400b80c0d940d41d040c10384000400000c07a8800f400207400909007103610100344100240c94021801d00c1c3c241600492614902408500382190141125600403c0329003440d2518840404207921990001200f0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642240080 1250 642238830 642238853
    0x110717030c0d03021303030309050a14010b03011a0a05150f0406050a09080f150c090604030602030402040c08040b0c0702041d01050601120c021207022d01170717071209 74
    0x1c0c40d014582d800c0240a109000303660202050201540700c1ca855640c06500400c07014230200c2d924040d071004203000c100d121414084241c0e101d0004110000034004150840300740c445840302e146000c2c4400a02c03900d030000b900d015110203650324201c08400c00034081c1e82d80184059003040980015011541035400750241601d86800e4035003c14264035040259154100c2d44c40e0740f8035580c8959420414801c03043c101e00d42069000914a16110305440450602da200340c200356442a000001c2c40118105481390038a102241e240412060900342c0ea4091403030006801034000c2c5201103400010342d41e850340322184a0904414100c000701824000706e02038141151000d0210301441410403482c0d265000d0001810001c2e40030700072400080070040c400d030300501c1301641c114510920031a0881000e40c20448544201450141c1d110700e0786c0001408401c21048e45403941904100348004980c00c039912207a10103021803090b03565550010211034410081120004d400d0030507030207109009219070301c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642241330 1250 642240080 642240097
    0x30c040f05120a030305061906090f0902070b0a2301030f030207060203030c09061b0d2c0a120609020306011e0b040609060f122a03050f060111071703 66
    0x40520041e901d10400c10b1103018105820040e401c00343c461400a8032980c03020380e2060380113082d03015a80c1480c0e4051840401c81d0001c1c001310798602d00c02c0c4203180551040000a0806400951816003141d0320712000610161034241441c0d01e40d0018402000d1441ca40382e031300c5549400158480d80d5a0905005c11070420005170058010030602041180c80882282c0c800d041c00403a2038a0102a013040c010990301c0707291213680d00002c0d40715032041d10006200c50440c1402c80d5650000c0c00740313004e03a00c80c116440c1a51790f003000b41d812022103413072b43c80d0780340c02c801156099100302d4550005070501c54064914500025418002e6200108200398901004283c00081028002e10142c440400c500c15210b82c2c0181000314028507000c0010a02c50402801e614101c0e1810040368809a21541c05940c500c1045008c002050310400c2c4100c551801c0a004002c0c0f075140074812814800020445c00c40c01030002d40c100003449045108100c000c004010040200340b500c0104242072007526620707504444072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642242580 1250 642241330 642241349
    0xf09060c02012702010509030f06071d0a091d0715020d050412020603060a09020f04091a0906010311041733160306080a05010b0102010b190e0601090b030c04 69
    0x4609240c0e40305100d555590403508400d54110031240d00c2401d10104a1603040341003090800c0b52441e1614140701c07044401060078010242c0741020140501640400c00b1452245c036206500010b06640f282822011500c01510001d4004540001c542e26130300b40540f206500e216440002498191190324a1352003000c50b0700741c0d62002c0014070b084845200318403500307600644c0243c144000d072900030000c40e0080001448100b540341c2c1c2d19040410307600142c1008102c1d440101d01003080c0310241c05080c161845e41d0aa03619004035500015038600d2000e02440c1c1010340e40d808050312400468122000751003d8070749030340d0030b6050340d0a00390b840725846176807800400308125154440343e2000101e442514800c03d04880c66440820b0510906908940ca60401d03448890010303103a1380901c241111140074034000b04100721b940300068250b9249001c014020600380c0d1003d65160341c80e0100105841c0d00408a8070f00d61a8000100c480001a41001280480010601060a861100a208541e0f0110 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642243830 1250 642242580 642242591
    0x1080106031104050906060c060106030501030b18031e1b03180307030b010e1e090a05150105030d0c0819080406051b1b0703290c070222060302040f0906 67
    0x48114181e400402c1d58056046050009000a10b0283d1000703a0184c0054070141c01c052035211542d1500c14282c0c00f040100340e507180103005000c0070100060340b00b00310b04c01890f1a400c00c4152607560380308000070340d11f10b61a51009444d543c4035a40440300036141d0280300f00c2082c80800c44040c1c480c5e01100c2e07206d4169510f0702004069040114022089940040056010783c0c1f81c40d0b8100c86000d002440b080420740c905404117400800c08280c64002c184900007003440010600d0124500810b61068081862100004021941c0d002440f007094040300c0c580f00707a110001e1320380324826002d9084a024501100d01e440800540e00581040c40307207000d22010b02c400d407900d015268491030712003d024410752080102500810880600b8405105070400311002942d07203440f0201d001076640d5010300d24a103014410400d84100b440010342140c1e5008216207400410b0380015a007014504200c02e2801c1c80c405034955200751170b44071400441c1c000d8820322510305108400801400c0e8010105d07031440c07800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642245080 1250 642243830 642243839
    0x5070e041e0b1237150507020c1c0206040b03010e0601020d080c09010e0d020a090b130b100c0311071401031b090302090a0207020607050a170328020c0109050a02010801 74
    0x444114006020b4054000581c0c01001020840d41c0d980c645420107104d4008444c80f040d4090a00b00c1345400352043c15189060700b01d5140075118040c26500842d8010305510000790351381e190000460880c00103a00e8000000d10200da854069503014145c68480800000b6050300000c008a10402c401d07800c1d2031614a4414003a0380011701034800d84050a02800741c100e05501a981d4450640307402841e41100a0180d070000c0c0c5403955540040b208182c488480120328202031041c004000381801c801d0140c500ca000226a07100540c244020030420000308140506000364196840c41e030a00c816500480e0f140e01110705124894203066000074074205582c1910940e680450346900300f9980ca50918500e190208000050041d052504042d402c220032001641c50500800c0224411405400c0140242c2411048078007048180c0c2c180250400421000926078601c10030b60705110034164107600a400c01002c024000c00204003491b40c40c00c9038020500c14000f40c00710320613200f40c0c5c84d42d07010303a00d5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642246330 1250 642245080 642245089
    0xf0d0614160512070e10270501080406020304111905010906030501050f010f02010f0216021003050108060a05270631150f060b130503030909010905070e041e0b 70
    0xd8036100301c00a00c00f400340b00c80384006402041e8000c0e00518007000c1481c00310000540a004640c10100130403100542e84031800d64807036200040d0035081000400c61454140080c000e0140100000d00b02540040050108200000c401900b4400a805103180f8254008003000500c141d00815000c501e0840000410030710901496040c1c500c041c0010000c1c004010056802054040f0100c0a5540f50069107503258244d2020f4030002c0500c880d103400f415010b006200e45201070644500405080c000103211500000135501c0d040701068a000510b582c41d61003da800c0d1000084800c80088480c1041080000000705140a0a82010300e40c4000c9020302548032544100c040b12546008002003207804504103034413200c0005005417002c9903030440310b0382003021115942c0054003850000320748055000303841c0c4122409004250f00840c5054109400031f03c070300e40140b0849900f070780c40c0c0000404040c030401b030300d8080200c042c10601a00d8003100d119050b4030302080c400c150113440c00c1d00d06522407a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642247580 1250 642246330 642246361
    0x40504150203010e07030e03070215030907080d051305030f07030f050304030b0c0c150601020c04020c010f0f020703140703080c0904090b07020606030d0903080a081018090b0a050f150f0d0614 84
    0x14020305242e10b101070325905098bd41c01c000c180070064041c02900003000b00c010b104048044a0a41c0d950740ea583c01000840c2d0814806d0700228042d50001c15106081031002405034103407500014580d90040007854000e1852003240c000405100700b88060003010503212001e4184031441c00155000d02c0c60b8526440c28034041143c0e198010390190a1014403420b1541c010a59170304564004170f44000e0707409601054ae202121010052580041c40742c0038107900c03460351010740540c2c0b417007a80750002c244c030010164403010305400c0361058002840071866440354000500030398807410440e841c2c5803040d400b0f5202e600c2112014001d010b000c1c802000c071841040501d054a9006c84a42c0c1403421031002198114030040c028000080c42c2c0350040750042954810103812800107001007400c3d0928a0541821a406010001c0701800c003018051071a18007140150f000c4070702d00c03400614900020008008640e05400a070308080005e00210034006a13030070001c4410112020b078541070f02c4110085004c0301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642248830 1250 642247580 642247583
    0xc0106090617030909041209090e0a0615320d0614010501170a020d060f0306050714190804081c050402030714030a031d062205100e040504150203010e07030e0307 71
    0x40fa845c0000d4002a201e400003418001585800039026498100304012128002c16004546e030103048000c0411450f4014070704c4810710324140540f514506050708140c103d804440c4451010301120001d41e00c03007030a44801d00a84020100c80320010103040201c003c103403510aa407140d82201c2e0001c50f03030754041d540d120781159040303140554594070b948514009400185980d2003035a122200022000d020842100c042d6000b400001110300344404090121a00c880240007109410311015003000c80c000c80c00740c1c0d4000903041501c1d9640d1a850711703081d070340b0864400400001c1036643e0280c421102d50b001c207218500c29002c0307071400703520b030040f00d0100d003086641c0c55407643c800740311200020b00c6986000144141d480c05040c05011150006580c1c2d002403002650740c00030700d801c200d8155179440700c1100500c0140c0300100b007400d8840c0c0c01090310a2450101d030085450300c0c0802c08101080c80351368144803c0c00300c115100e584407034000b04544020740f40350700021f003043e20800c4c242c03202004854859 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642250080 1250 642248830 642248839
    0x2030904020304020f0402031906091b0818030301180b0f0f0d030309060912020c010f020706031805010c08010303080a020313060b030c0a09060f0f0f0b0c030c01060906170309 77
    0x429041044080c0d40b00a008980281c0041d4a241181d00c8a0000c1c1d0b01421504222642040d40f0312400c0c0202d424950280110743d041c20816202e40d01c071002502c0f440c007404c0c07514265580d1441c032844480001d00802e0310051000000020340503200802c03180f8003200d2000180185580740003042141e0244140d0f183d8808200c02c0c110342e691806130356469040b8270a09000c601d041641d104c01c4104c03050203005440c000c210702d00307000b605903040c010350300c80b80802d003080216415007010081d512806801100c041c5990b8030340035864000e0a40320101d071980d01200030302544030181da00400e911001e00c421070114000c00041070070105207001b0340f0b2099141d03031191a5802c0d440e0700c813500030301845510030b6054050720b20007503080e444600020000d03003c40c200206001d07140c950104080c1480f5444804e10500040061040d8070045070301e00d0460312240130250700c1e0b4034030949082c11403041900b450f00741d6281c08400102101c15421240460b800c000f1405485e1008402c86500d034403421a00d0340d0300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642251330 1250 642250080 642250087
    0x15070e0109081f20030a05060f04141819080c0c0904170913050f04051b010c1103070e0103030908010c0309020f1909020a0512060307060804110103110a0513150203 72
    0x558840d644402c6040b0800c00d00c4c0c990030101c9401400041c1c1c030a480240c8801d840300c0402005080c1080b2251480e5000c7e60200000006494004000396025202520000440c140102d080301d0401070060945030424146a001031640b40c0b46415500000c0c1024403070088045909003454008051846140c0125003000c0b100107003518084503078800c1408a0344100c3c0c0c82804840060310340b14440c4102c440340ca04080908060070510702e005a400100d110740314014900940b03a9078032110140c0015800000700b184054041e0010b401c02c266038006c0d540311021a0000014554012061401c9488410080003091841e602c120296156548041d4002001c000000501c1c24030381c160074101d500c0e40c408010066103800e401000d980c011026000001c1001c130303011001e50600a13034280c000c1d60890092200d1361a02c000541030050003071020304214001e0b40250516402034001d1418a0400d800ba03c5d56160150b8016009402c40350b00c56030201844807000c6000c52016400d01c80c660f049030020350a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642252580 1250 642251330 642251383
    0x6150b070314040b0c031b0d1205060409020301240803030f04081303020418050c0415031e080406110d03050c03180f010218090f01141215070e010908 66
    0x580c04900c207080310440b80208400100004c440c000707000001c1c02c0c24040d698408020480002c5000800040e54071a0080100c41c40c0b2950401104414a444034901040320303559940058018030503030300d021303401d5401c1c100000c010f0600c01c042c98441c010444e0641c21155292405c87d0340d01e00048501d00041ea80301c501040108108030060012140c0d4401202107590b200c1e404070302900c50f0f1f1480c00b82c030032001c443c46604001e0148603142c160042034130100300c44c06c0c3d400070300720000c1c405100c0503041c2141310050032920f440640c50b900819400c4000c1c0c1e170b591951000c00a21f100ea85070b07451005402100c11120006202e400303554000c01039141d0403070450303c6e150003d044042c80080340e0300d003501c070b00d0070a541480c0080c00030b020b03072801403504180141454010b22600e240700803c5a140d5100d500018044640304403229042d41d00150350740482060a44400c41c50800c00d140c07000c16402d1400b0030444025401284282900406c0c2c1e60b032914560390b20300141c1d8850390351030150104503a8509801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642253830 1250 642252580 642252587
    0x91e0209040f02030a050d0504090b1207050405040f060911100309050c0108060d0611090f010f05030a0b010c081b010e01090201140f040f0602060406060b090639060406150b0703 78
    0x1410b0794001400d891080c8441e5603000c1c58030210081002c0803900203e03003000030708484e218040d030360038017a07910b4000000c50544103901c51590f4054240308640d0745e4040390902800205942000f64841c004020007401da0410051304103040400a01c200704580064481e5442400364030700c019403010041201c00c9040d001994100310040c100b41e00700d10311407005800b14603580a40e00d58030150b03a030742554800308001404001c01d01c1d0180c20381404110554103418070340c0300c0d0032240e0003409800f001400c51041310040384d0314950008042c01020b4003017100e407002d41a0f546103c41c40801d101c000c100100d1805900d41c2a12603010340603001c119411010782007540080014030140c1500b08200d46032030340310b140700811a1400c0c2c21034030050340007404000400401784540005400c82421042c104810940026050700c1003050840800400300010741c00c3c0d40f448507000c01060b12602c8104100600494119611391040300d007560640d0400c81500540c400407001201900d0301e112003113191118584040c2c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642255080 1250 642253830 642253853
    0x3150507020102190305061c170d0b0a0b0c06010905011824080a03080a0515061c0e0d080c16080708090904080a180b09011803060c03091e020904 64
    0xc00955400b008030010703086801038201940080b5840c0051030341080c00500800c1c000040160b0901c602446511010038865050651010100f440c82a520080300492600ae080d08100040e00601c1750140400c103a07000341c0141c25420703840700c100c0e002c0d81c0e6102e02c8801074031001e1180302c030300740b5400030000800d070665006101c1c00b0083c4c0c0c800c40d41c4202ca510394441c5940041c1c2c00008030390004c941040c01c059101415607041801e0040a01c01418110241040d04000140851180d50300040b10321100000240812010407403410400c2024100060152034070584002c00002031110000506601030300310940b41180e850881f03501d01c60000d5a1150340300e43c0102016200540103000281c680e5890184940c4694440d001d8241c23511030300b0740003400c9401c00d0041d240c0d5826910f10b05106905291058030a01002480c0017280c403400001085009101900044d00c03290074503112003025a00f642141d04c00c01d11540c5401c500105c102d1120583c403582140080d88030340c0000101e404035417550001d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642256330 1250 642255080 642255091
    0x50d0309111005120a09030f0507031242050619140c030310060305070203120622061401090e010e130602040b03091501060e0303070602030a0b0310020c0115031505 72
    0x1501d0207150394001d5240380302c100c5d002050349880f480200c0130154800e01d016110b17405400c100d420a8840d0360054800d4145002e1900e03003650310048440d1050624496a4140c2014010b034600d030a5054240303c90300c2941300c000c14000b000002d0028031410721108540c100540128101a4040c20740c41c100c1381e4040005982d20440e1003481a000c0380d41c000c1c00214051000c0c94000c46000d443c0400240940e0310040007241503400034064860500c51604406a02400c121405210ba2000f40902c0500c041b040c0d030f00c100c0700c62803c207000c00e4501d8504418040e01c20241c0383c1ca0710f415503030000243ca1143c2409265941104880032986d04804080c00042c07441c854a00541081d4590004031010f420840e43d9030320952000c40281603400f106501c4501405480c94079007000e00850780403d07a00d10038010001d000b00d60020001e80c5a03060360f4840682410000c0507580070008030310010300603400544d803d00082d480d112101c6038050031210701104903540f0442b031944079a03451507848002c0500809 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642257580 1250 642256330 642256337
    0x61c0506060c100510050a051804020102010e43210204050a1d0105060f120f01050906040302120909060d0303090516090e0307020f0613050603040f050d03091110 71
    0x20a5815070003c1c42990042400c5450018051410004030000782c2c2e950380c4458046c048001c4140460740740c01480c0e00d0041200b203100c607010b403034910040740140b4001041c210725014a0401300c040801010400540303a020b0408103900c5404020400001000508112143c0c2d007011001c010000c600007079041900b40c0010035039107440c2c264001c50203503038003100d0849809a031450401e0303400e005440300e002d4007010302c0000c2000f454103201003940e084240d22241d200303200580d80058814010499007000c01d400300004d00c4903050040080703550301c60589040300035000d614040b07000c04607008251107401d1002000d402c0d0750748440c014040c410a855105500f09901c1d40b2100380485c40c2000750005c1e1003045215030020910f4401c21310102c81c03004042c9081500301300900005a980d11082c0034000c2003c031590740d520540c1301c40e110220069a480f180d00400e02008010602c5205500c00c0c03125800317001580c1c0c00b001c050804404a8100c000020484030340106800fa850070000041d0804251904 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642258830 1250 642257580 642257587
    0x1204031202030f01081b130b040e030703030b091f21061d2418160e04020f010219080c100905030405040b0105040b040306020d021612030b061c050606 66
    0x1003561003aa84129031050711007224200402114508001e441490713480d0100c0814521400b40c00070740c5001d4400081403080b40c5032800000301b40c0c1c5550064034030b50184000c681c1c0c1c8000714a009805003506044a520403070010000503140320300700300b0581c0c4001d81e0840021a46040450400c622844c0b07030004000b000495024500145062242d14440041c01601d4034101440d60250741c0340840b140300705c1d10103854901e0b01c44c07002c0c040c2440c84c139080f0040030f070f84101000724401070a103008483c0349130001d540b01c0d403c0009401094070300c116014034001d490a00b041246a401641d440e0106210302e40e4500f409031325a00814140f0002c0d0600c810244160380e031071718110840f81c054403074410056505400000c0c0c100b041d0724140c400c2d0b2102c0d62082c2011070426180c0b526802042c003032480090086074000070840da003142180c4c1255240d256610003140380507001e003810b00354003039450009800300b8603040e226800c5280a01c281c0d0741074407240b500c0c040809242c5603900080c21b000f900c503940124051 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642260080 1250 642258830 642258857
    0x120a020315040e150606040e0a05180601031118010501020c041a040606051207030e0a031107030b0a090203060703110f0c0c06031608010f05010f0806010e1309020a05090c120403 78
    0x3d020341e0002018010040a402c011001c4212100300007614180c40b8100030401040f42038410007109a00600e108400551030391a949440c07004060480305000c00c2c020300d00017000b003040d148985012072a090342c098000f804898002203080c1422300485000d6401a510303400c1500d0705810950a401c01c034086844400c4007000443c060312002c4e00b0401c00b066010800c03d00c00611941b40031703030014007031405105180d503140c1003079110240508046c04200751140c2518880728100144401958454a001002d190a00c9058024944114124440d00800010403400ca1003030003182503220324020007e2502842424191960b40405007016283c02040240181980c881c40698482d078036411402080140c0d2410081c42c00c5416017001c1c002042d90740042c00300b070741c2c01400141000d9107800c0250141d00c0e200c0040c0c4640000b1040c880d84042d000b0400440710402c0d401c626030b024130a0b115419103e8540e400c0100024045a05828202091090424014a980035035401901074181004264540c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642261330 1250 642260080 642260089
    0xb041109010b07051b090414160b1b010c0f05070c09020d0b030712031707050904050901060f06020304031a0415050f101403120a120615030c05120a020315 68
    0xd80c003402c4031440225007801030010034024000c4100c1c1422007641c0c0da00d04c4c4800109030760340c050405040c01301d032640300c0580e1140800842458080c04240c0900456480c0301c103604075030041039840e250f44400e03134680403400c6050103181e2017120310303490310071031000c03102c404a5070380d00150070a48680000c507200158400c0c141c8002c00458841c1880400d04000c05e00c2418503010203540440c464045c4000d42c100841d900545000100031100c03c0301003140c590040481c1d607801115600f0307078403d20b0430341072184082c0154840c104450304244a0000143c0c0e455042c1e840b0700403031001511a01a20710582000c240c0f8032100f56000e4800d0060100aa01c400828004ca440c21202c0e1030b4034100c1070040c4185818618040001031518a00d00540b90080b00c4c0466200ca0241040c0c456000020a0252680d070099166081081020318104141c641d1000e2580c840e40d03c01070084040b038030380040342c01080c1c4510b04594040911540e135010948661440e003009510090804000784410410640590754 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642262580 1250 642261330 642261349
    0xd080a020f1908060904030c081b06250203270301020c100f110405130b041d151605070318031e0201020f16030605131a0a050a06030b01030b0411 64
    0x35540c40ca07a10b2140451409041c0d144007600c698451141e1000704800a0381c010074801c6401c1d030002c11305848130000c0314101d90290804284054501849040240e21590503250003014890303200090307401014004141d07142d00c209450030505030602208144800c0030842000e080580c003400051405003041046414003280200e000c80158464407800810b05540c0120640e0440880740c103850680340c41c00080451501d42c4c00000120340b16100110b03141c0d82c1f5406920044000c2020203880200c078a0804e84480403480264a2401e0b4000071036110380701288054400a1070342c44080c90010242c40c25940000b58081c02030443c1d0a9003004400200000d107800800701d9002c01894485d45248006800d081c1e4400344800d240d03020315000405608030b207802204903500854001465101e0350840e89445094000207819074009599401504903075850107440780303880d40c03400c000380d8580c072000d4810b41c0c1759480003420002040d0014004204110449900148900d83c518003003005400403d41c0c441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642263830 1250 642262580 642262597
    0x17040602071403060c0a11010b090106020d080a090809060c0102040f030f020108060d0b01050f0d05030f04030b1b03151f0206090d03021303032007030c1d07020d080a020f 75
    0x20021076042241c2202021648503102d01180600741c1480c10800100641c011800d0a804104247d02d61080b415400e501050280d20040c10b8100150b0316800045d50340c0b14100b0103e8001103c00b8009000c0c4100341c071403521030603071001c3c0507454101200c042100c150041800076407155420440061711404100a4000440c415210051b01c801680005480f0050040081d4001d40c0c00700206c030005100d1580050548104841c001002656003010a444203890720006240e0b100c0014000c2014510130058400c0701c0c8244050719496840200040d4200d142c0030203810700f42800d0010805040a42207154400070004e000b004182c40c070080c44500031040760f030341903016821010501c05091400d01504191500e0340c2401e51400f116003d00c110440a14403010742001b010b01c0c803a82c140c100c078411109122800100301c0300056244d04210011902a01c100345421a25861403105401d10f14400b521406441e000340249010800e416140410020000b16a950f400c1100c80c06811a1002404001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642265080 1250 642263830 642263833
    0x806040213020a0801030206250b062b06051b03070f020d0908030d0b0301020708072117070e1306080f10020f300a020304050d181217040602 62
    0x18101030060042030000701d00d011408600400c030401d00700390040300c003504407507043c0d4199a1f40c00c600c0c03981a46541168200c82c0c210100ca88240f0240088d45903103501030034049030300100101507901004004110881d90100108034080c1d8036020856076032050354000001d1903039110300320b201c0d400c3c0d2a00e60700c00c45092000c07401c800c030f000541035030410030502c0982190031302101c1c881c14a198255a40a61a01b904d2400d4039200050070a0303c082d010750325082da00a070200e4948805250501c220226800c0207002c07000050b078508074141c46040d4010310b8400c0b00c002c890301e58407450340445204400d14500303904214400c1c0040c064103120f00c1060010700c1a88007030f201510031850711505005c842c2c0c0752854018010700c401e4204200d2034003120402680703230b0248411400403901c3c41c11040c0030130f29182c081510f1481000010001134008600c00c070b1041098840c200b59000c4180c0d44401c138840040341e4005403003003e001d400300d001c01601c8121300074985800000c0d601c8000e0030180e40f01d504440d006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642266187 1107 642265080 642265093
    0x2030d0218121f020f040311010201090821100f27141e15060702040f06080c0102070b0414220c03021806040806040f0206120108 57
    0x15070201408880c8003820004400c0d0711001c003464001c0c2d2410b8844001601c0000c02c2c401c482c24800050784490420703040d074584c02c0c14203404040e0311741599624000324010640a8015040b484109540c110030b45c003000525a1001e603003d00305008282c0c41c2481800901048002038080c1c030444e8100b40b010f0400c8e2603900c080152010b81b08455145030819070708a883d20340700402d1140580e50000c07900c200014200c01d40104040b55802d0410400300102149840c0000090106600081012a8680b07000108408440e0282e02800d150340c44001c07541b4055805206250007400c1110034203082c6482d22031101c0d0344180400741e00384030b03060072080c40341c035001b013008102c80404149400b082518003030380f0060000e42c0b080c1604800000302100189851401401311002c0e500a00b028205a84499880e1a40081c10941c1242c0c01501444540400c0c40441041030003030030f4460041c81c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 642086330 642266187 := by
  have h0 := BRFrame.cov_init 642086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642086330 ≤ n) (h2 : n < 642266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
