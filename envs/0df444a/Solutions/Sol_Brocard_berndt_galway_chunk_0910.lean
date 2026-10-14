-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0910
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:53:25.26199+00:00
-- url     : https://prove2.me/submissions/5058b28c-2419-4fec-9e6b-4e9f76a5b352

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 163489208 ≤ n < 163669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 163490458 1250 163489208 163489217
    0x100e03060f09010b041407140403120521010f050d03050705120c01140f040308090f06040f060c0c0308010b2d09010206220213110a090806010b090102070e0a021909030201 75
    0xc940130786840e00410303503030400c8400310380f00d60303207690700141c54890845046800c540000d00002000c100d00c2104103544820070340f201e5540e801c403901660050100b548034070304610082c0d40184649003ca480850941c0c40a845040c01d02d80d190070140e90703501840e03000030140c0c0b003080382402c45070100720064280d1412000081c020a02511080c001c0c00504031111404094100006000b191050180b00c0e007022011054991402d448091035003000411502a00c04001078035002c0108482d9210b14541c140a610301941e5034016590020200d110611501c49030000114400c1c00000c1021802c00da0340d00c0d000c131100c456035840d86020040ea000b45402c03a015010f1b41001814600003000b400000c850304a242440d03402180d400c00c000c4424500350003401030340e24000c0310228181702c001803e43d900701d511088419403801040924084058000300303145441402000711590300000d550042c0d4020201da5501a5686890003009010307800c4044031541e44a1502902141c1140c1c0c120152030003a86c4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 163491708 1250 163490458 163490471
    0x9060f0d0905061308090907170708010f150c020108090f0d08160201110d0f1b08090106080706020d030e01090b0103030503190c0c110a170304050901050907020705100e03060f0901 79
    0x1e145000501300b0140111400f000f040045241003141c03176502040c0c03030030866a03281c074000c00210300f0a41243c1900202d83c5000040c1312900e142d81c410002884040304684451a079850010b05282c41c00c44001d051019420120b1680e403800d2041d0040d200400d8104c40e00140b0079500105035000c1500c0101304445e4407184140303410700c180a00c010341c800b10041189000d0003a1348410003042c10198512280381d6500382001130a40c4040c040d025002e55554845542c180303a100e450031a1000d9100050540c800042001100d4010039182080d022900340045c010076001140c50141c000d00c0c600030010320ac030f04004001c00d6000005540240303241c40c108010a80f80310900da044980251035100071510085440d00010060740010344600000781040b11450764801c0d040000c14140380e2055030a03003000c181031240b41030410300755005020440b82c90649d07052600002c1e4465245000d0140241e042c4191000e005000302e245050301100a000c076942450031420324003000c40c040d01d220926500340302 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 163492958 1250 163491708 163491721
    0x702040e0a1e14070905010306141005060904020706060306020703090603050903031303020c1509100c150902030304030b040503120903070b0c09150c03030103030206060d0c060509060f0d090506 85
    0x400c400e4940c1c0c4002c1c11031041d504004410509109010700f20f43c40e44802c49401014981400583d000300840720b4042001d50440c60710a080d40c402111821261a10b03c04100380030070108100001c80e44180c415035916410351002c40d000c2d104100c1c01070001400e1100000c00c1200503401000c03064003d607105a8040d80710030088082d00d0301660201c85550080c400700e602c0c90042c00c0340302c08951180c01210103508690021400403400070b148072003e01c102103009465402e1984001e502803101d441c5c06c8101a103582d40d4048100c149030150092607a0307492068003151820002c6401035500441824201d20300703450325a650398030000813403000410000100d040c0c40c00000c151000700e40d000c43e09140642d1500c49821281e041402240d6100303006410b0581301000c244000c080440d0306001441c2d4a40c15403c010b4502400500582e00420900f00b0680c0411140700081090f2400e174a09150340303503071120002e84140908500420040800100030315280c04aa00401c035142c460380c01c0e2152a079548 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 163494208 1250 163492958 163492963
    0x3130509010312030f060302030d020d0f0207122303030411030d09230a270b0a0803040e04020109050a08010b0f030d0906030504050f01020403080406030b030703020a030f0321020702040e 82
    0x80c0b01c01810512094000030f40640290490518424118000141d007a6641c00092070103480242e20f4003d078100c2118a00d54a0303200c00060884803080c001404240d1070710000002c440202c03840501220032416040c3c001081031501e440d038145000d000c03a6101c4c2000e080c05c5880c42e40c00072103148a44a03001c0101c8149016070b200c5411540e0314145410106140010500c1c500524100d143d070107034a042c40404c4903683c1900314415847e0b068110014030780441e00c0442195851000a48100d0f1422410041d20800000712026209c1881070207038103407514401615100b102d5000740d54031038034070040403c109105500c02140307600c0c00c40700c1d01000c0c01000f040c1a210f44411101c10002a5000010300105009400c1326801901c1541154020040e9050807401c903005501300f1240054002420400c065050003084d0300c144044002c1c00c102c07807031580011041032043c400113103510700442c00d200030302d4014520b600c0e20102981b00c0310074240501e203640c4001d60007414202c7c13145180004480740d40100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 163495458 1250 163494208 163494211
    0x60606090623220e071106010509010e040311030409060b120a05010b090f03120f0702090714040e06010c1704090c090b0406051c0c0807080610080f0903070b0903130509 74
    0x12400200c2c82c265290f406041101d80709243c8501c2c4006003000001c134180c1d1159070034031800c5565285491000125038282c00c2c80700603440710340710f0298400103005d10300040c014140c1103545414111207018802c402c4508501840c2d01c0583c0f800d07d80000041c00100d2078009062545034040e420f90700e0350310740c1d0801084070400c0c01813104508081c000c040300d03070400c95901000c44ea802421191040341d91201042142d10a0118180f901e0022642408504050400f5604480582000e106030200c1c070301c14050601442c428056140c9450300482d8803640294400340d20075030080003508414240d40982c020700e51051203a40d4000d860700019a640921500d400c005039910a0300a51400b4980f00d02110706800038880301045c00d810b07100701d030315806030361241380c012000f182ca80096518180720068010030000748143d009007012007540340519030004161f80c2c403480407100c070880c5458000110346035004140004041140d03820501614007000006004160381c03610060041c0d0781c2740e4051003200e000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 163496708 1250 163495458 163495517
    0x5060a0b09061509032103062d060d02041e080d08040b19140406060806010807050a0504090606120b191404021203090a080102190c03082806170c010203340606060906 73
    0x980c101c80c0d012b1900c40300415803005003030380241c02d0079146c8880c0002e001340c00945103000d46290360100044070041c80b104406610728180040d0601d0942c03112082e400c00142000303072042d0300001c0448515200d61010010b100180080651741c43c05e803800a0003000c090203204481e01c505c40c000030342e841001170380000351030000d0a00c5045519060074440500b1003a07800710b4600b0b407150b00c007080303c06803035114094450007000d03403490074106441280c448482c906a9041c0c0386041c1621a034083d0300c2c031401541c0140d419035004c840c44202c1249203085001f101c018590007440741d240020300c0c80d015009040e032483e888504003507c220004058406000c0c2d890001c02045225001884901c181507002006206c401c050000c91001c40711807400b01ea5507500444a0b05c0002e2141c680f1400d0204045040e0380000e000840c6230014000255080110361865041d800303081d042881d200c0c5a0341c003481580641e200d4002e00400307031034000180400d40607002e01c0d000543c0514444450010201c00c601c2140d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 163497958 1250 163496708 163496779
    0x4020f12030904150e040f0605070f05070f03021c050d1505090f0a06030204021308010f0e210f04060c020108100b030708060f0d05060a0b0906150903210306 69
    0x51650003888058654800d0713441e610107041100082003841c883c0f41d984194411159250320b441a40303804411140c024000c0010801ca68090146071600681155115034010030300785402503441c0713001c82c502108541e03020740154644003010b07050f0781c2280107440c040484a00620110034010055018002d062040a82c000c07280404200e1000c0c0c40c20f8050780048031144081006030f266000311703080e45e0120081072003030703e00c4030400c10441000f8401d135004600f412000340481180f076000c0c6603640702c3d41c54900e00e001f0000742100c078010810100325400b0ae10726061094941d075031940080c1c1580b0314403d0503408218010001065485240300a01c10390b020040940c1c1540c540709002c0300d0505000780380a0b0040c4103601c0c000d00c907640303003002d40c648144078400030400f610300000c0d4101920521990a8000c5070384d0b400b4061240c2c0e078245080c4c804106402520f0303c46c5410400641b503c0940e4506070005000095140600742040e4000d5218400690304850300b010300c00d01c0c11a0010519003440c05c03d8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 163499208 1250 163497958 163497967
    0x909050606060309070305120a09170a08090a0e040f02091602030a1b080310051302180907170415050c160210031b0201020c0705060406081906031a04020f1203 70
    0x40c90502c020719000741c003800403030703d4054503070b0750ba1403a0a81d0404903100c00c04021400603c103d90258490340601481312071080a2403d01c80e482d50307502020800140b85980108284003661030762969400248880b0030082203a04003800e05613031108005000382d000e40c80101c00a08490080c540c11b40c58800d184d0300441c944600303040101c070060514012494030452540c3d442005c1040350010314043c4404e070281c0c8040a00d00380420040c03034003005c00000040d006000a0041c120304050000c07007440140d414201a55500804a4209801b0b400f00719046020030148014020007508048001100500400550701c41000e204814099408000c4034030381d111011034018101540040c841c84000c1c01c0114803542164080101040c404910000603940450100c103a210200101801080250780141c500b070300740030000b0600c210040190a22801d1060300b80b070b19040fa94422300003141c200302d0921102c1e00003107510b41c007181c050380d042e4419420050030910514145400c528102d410b0002107250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 163500458 1250 163499208 163499221
    0x706020a03060504050a05060907140a0806032d060c160210140d091b0b0301060813060c0e040b03010501060801090902010c0b0405060f0c0f1b031606051009090506 72
    0xa980045408001c26865080000d881c0d200e034042c042c041e07000c2a0000c101480c3c090240b18400d8001095207003007240884412a070038180c032045424003140d40c81e02c46a1640d8500c0441e2404540c3c0c5806450340012000324522552103e410300c013541c40c0d0005817a0140c9814007003480074011004100740300c1140015590041c540301c104194407107018240314640f425140c031900007540040d82010f03c8681c0700c00d03d01c410068000840c0501401b4103c0f01c0c9011418042c044000e404140214018011050041009144454002c101c002da02080601143c60401001030484580400d030601881c00c11100d094903103018003d0ba07069a400d0359444d9881d83c40d0080440180020700c50a030305000a000491000c1116070a643d8812401000145500d0410034000b500003d00244020400b03c000d2080109a1611804540b642000c1642c10341140e0b1030008414214071601401c0f4040c110100618420403c90b43c00880c8200c030705990261203180d03265569403e441400c1802483e45e040172002920 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 163501708 1250 163500458 163500461
    0x2e080415020c25080709090503090405100803040305011d010b010c0318030606090221040f0b040804170604111804060e030415020109020405070e0d03030f110403030e030f0a02060706 80
    0x45220050203c03190300509040d2040c04205031800b1030014804000180542041000b08a0061910a00401400b06103440f41501e038080d44040b180b0454840012845c1c00340c0c920a0b10029101800070340c0d654503900e10740301e40200054000046030190301c41c04030710111410f110342009400180c4501e400303140c550394111408290f09010900d812404480803020841d01e1040001409080c0f10060b6103803403c01c4004a260381401901e4010070103d82044005510003503450002a802101008039450b03a1030081c0c001e0080d82c0041002c80c085a00740c4c881380c1d40018004d40141e00400b06114ac0d082000700f401101b440e103100581c10300300a94082000103d1640c0301c401d49000c0c42c0f05490404d515060210381c034299006660b00182e4440c01c90380198035051003281c4e009501d0b800c211060750703100e2020034480c554207513000e41031503990700c1c01ca40300080540150190f000b4482009998685a25028140311076541c0c5460003841454854038171600009070101d10150010007031820006183c0e00d940 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 163502958 1250 163501708 163501717
    0x9011203111f050603012004060809190b04020a0905150609040f050112110a050a03030c0203010f0e030d0515030622060603030c050f011103190b2e08041502 69
    0x1081482441542d000a201040c0c0106804060340404070301e40c241441050301f50b86400c4040941000380c00c0b00182240c01c900704480864000341000b84190303540d042020700709041500d84403014458076044104103c60302208078400c0740b00b10340001045482d03107141000c84d1030440791030300c40c0c812122008905160280180c40c1c2440010401f10300f0480a51108003070310420b9215042144120a051040290700301c2d180c201d140080d0380840d0780303510b081c0002c1e45c0c0c008248800ba05110340c0f6140181552003e4101038038460803100180099800b250706035a607644008946000c0f20300c2d00c1c2c080f403003000c00c0311610014218000c0c0104401c0d201c1a0383c80010200141840c58224407032900500054000e0040000940c00ba842d003010709402414107504101d4900c000000703e924000d105505140d07040b0903650810901c2000d050030a51001250340206a07083c0001d501590901a04280245103031001c8a080c10300d600301036111070442029a00c181041d20014101e0042324541110061240e0107072 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 163504208 1250 163502958 163502987
    0x60c020d0507090b0109060509090a0203150d080a1404030c05060c070801050a061401050309060414010f3e040504023106030c09030c12111008011409011203 69
    0x18009000303541e62546001415805a844075440300980000e84d0781200010b001403603241822860030007200b0000f011300c2c4005000c40103070355000c004120841c00407149c2d1114880c001d400e000502c60306051150681c0c000301a49000103900410000700301640e5001c1c0c40489600502d00a0600d080104009481d08441d2007001248200c050000e01030600340100f60107104078600010701d030350030124051320b072100031240c0c02c2c14072000f08284880e4030742c005900c59015030401c1c0007005850700425081e0240c040c038850020024104501070410215000b407112503440e10720010f40c0301462101f191280010002c07010107010000307004c20059428550010011010300c03140303810308201102007600002c0610070aa01e5441c100310710078400319405100351708040003e8102101c003d0300c0c5642e070826064580c0510507601c11000c07107841c100208082c06814440c002068400200340800e001403a05800344a04011040b2204690755030b810030042040c1600c2908045861b41001610151214008681034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 163505458 1250 163504208 163504219
    0x80304060b03070e06030d0c120f020c1020010c08040602090609120a02090c03090a08071a07051806090d0b0411030d020a0303050109051312020a061803030c0f09060c02 74
    0x105042d5800d200c140c02a0100b1544c000d00350400000b41840c0500d14000741060242003809440444c424042e4258500c44510340381020402c0002c04904006040c140ca1350000790402c00c000d051030f0801e64101c038040c003800002d1305258204a45034242e8008100002c08140b1000c04640495900d03001091101c4e80134128518180c1e510010a001004070f0710114038507044054000c04500c0c100c1002c0350007220b4501c80390705506007502101c2c3c50380c0c4143c40c000c007100c00000d003500410002c4403804200381c4601c440820940303001c40015140380c0c407644002413981032484100700e0703e05e04102134130740c603410241456018103110f581d8600712241c00762050742c01288041040c41703240c1d01005611070071010350b805007038202c1d80740c64084c00b9208180c100e4a590b509000802504500407012440b009401682c1c92044031840350050f030400c0840b60020380702d10f08258090000008400380c25000302e00c603540c108048800f075401150900444649240040e91003030003006100c0c40342081c014294001080c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 163506708 1250 163505458 163505471
    0xb100302030d08040b161d0a030b0a09050d020d090603021b010501231c020103020a14030a02090a0603020a0815030c04050a050f0f010e0c300a110705070308030406 72
    0x3468088051021400200d50f2010402003210284041da0008818144030075035401c0140040c02800b120b024005c2070160300c0076078841e80d90743c0c0311100c401181c2000036078956003003a00585004d0901c0d0101582e540c4103522541c0481480010740922550703455403000211070400344201c01a500c440002c403080d11401c195041030300c8081c8915402042e510071701c049450f00720840c00d44080c4e00404014400c1d02000c2480e144120655440d00190360309180050340c9440c041415101180b00182a407040c1001104100783e2503e40d1740240151002150020f00c600e507240c10450680c8a03000d0791100041d04103010804103904001c030b00d51030f854010305444400c0c440c07501141c2210000c517455003c054aa0701406440c807003076403905401c2030300490103054035810030320380700710b0070708040c094807240c4000140c0c0348560304a2540180c40c3c0c4098000c4d8070412000b071111002c1007001030b04d030100481d1909054001c150f0303044d011201050b50041c00762180a00d16180c4c3c0c0c82070b40004206803100d58a804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 163507958 1250 163506708 163506713
    0xf0901050315030105070201090b0a060503061b120709060206161b05010f091113110a0804030e0a0905070207170a020f03030f03011229060d0318080106050f1008040b1003 75
    0x1e0311b2140340c050b800098403801e80e051200d40342001a20924409241030030511840d14081012648103013854603000302c1558403003601031741c0c0c0300c1c032207110321450440d0302070100300da90102e8001c04441c035a40c00c8901e940c40e80701c0c10060914100110801041340d1020394110310f100d01282c0300b140b84c09400001150001400f56009482e50450101d6002c0204214840b491520458002d61060306543c204114090174225030084c2c46444031035002d004000c40040c0405129103160680d904019103001c01c0b581c1e848200401400301a5602c0c2c003d4007502001181c1541d407900846515540d8400a00b000b60185d02888400c4071903c1b016505030204004101d4180c1c22500194001c0140190142550b50036042480005100001e1070604424511184c4407041c0200a410341044040f140810702041d14039007512020030701a200400c8180e104e900044100041d0320140c1103401c1629810002c4214408016042c05150304000c04500b01c1000308022031143c02d03459600c00e1000030946d0701c468494 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 163509208 1250 163507958 163507961
    0xf0f01141504140112021e0708040b04030303052208040b1309050403021c03020a051e070b0412140309060403050901020304091e0b010c0b060906040902041415060f09010503150301 79
    0x190886451844180c02d4141c85503401945d1441c281c4240c1001c50a00960091801c0c103040791400c55483d01e400803582c00144000c1c1c40c00c642c0148490009541d640b540c030b107006000360000304d400c4c08030209d82c0b0600400031b00d111041851820390110301c82c1e00c0d042c2069105a62034020b0a09820b511010140209402c4154420341d800b171030203500240b450725000c80781e03031649821195880007018014006044226008803d40f400c40d07180403241060000c1c0f524160005000f84e40014041800c50f01c01e11041c000014002544d00306642d8840804407615952095148800d0390074940d641e00c41030006011a03c2900903094605052040e1b0389801d58405682c02502e0703144d0443d2a00c1e00e902141c501c4220038600c40c0102d070720003c1c2001210307402a0b46030f544110b00003c14490161900000050302c5030344a13840a041154001c104200d00807980c051420022811600080128441403030655207240407401d5400c042c00340900f07a4035241c001c00044501c2d40000d802c00c2010b1311081312261139560203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 163510458 1250 163509208 163509217
    0x10603050a050d0203161101120f240501021203040203070b030412090f0b1206032109240304110102031207120c0f090306021803010e0303010801050f0f011415 70
    0x40004080d0708200741011030414a03020140d4055510401a0440c003410061003a10240d0b0084000e0b2a9000f0600041c1d40c036410030340b0400c840a14151801003042481d61041c40c006445010043d00d14020696900388615140502c5002d64020f9000d00c81c00240c240003568414809825940b00c90340d50f440e102c5041d0403c1d10125860a4a4183e580410390701c9019040184442042d80e00c03443d103003500848251284112046114880000103246030310100152a421301d01a115961034080071a040e1403160802d03500541724491425102c4503c03d40c00440d04603000e1410807040c5952241d03542d070307421011030310350b454150302060201c500c009881000003442049141c0300e030132000291003240d000b01c40c1032040722401c0c03041840108804690244d101b8003941d601441c0141d85da40d45d16000c04850b0341400e5166415030811140c0b1103031a4000c800345040300c500030000d100540316031401c3e21900c101218816101c000350b0004200102d40852740500350ba00140006400d000791b0304184080750700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 163511708 1250 163510458 163510463
    0x80403060e0a03032714010e060a060e100501140c0109050a0c051206040b160909020412020a12020f0d150c030501060f0206040c060f0210050403090e06040c0905090711010603 77
    0x403070b201840c245034144c0a5100325103840d00b11401090010141d07004204004000500007248821050340d01c182d09501169142d00d0802c00c440d4545045014000035100a01882d4002e043d02008140d11243c03066041c0240c0b981612581c0d054020640944c126810074441e5004543d02c9291603808503005000001190380902031030f00d001ca04200a0180b01946820300e002c140d4003060804c800305052065041d0012041c0280907001c940b00d440c03c0b5100c80458000510040c800940010800010003034060f24520a9403000082540c40c04102005480e0080203500118080c0310013200e40340607040c1ca44414494032200d0840040c10710108112075034044032401003559440184002504030040501d01d084502c003c010529060b076469107604c24611400c418080400c605849482c02409001c0c200c0086940401251a213810000d103141034621809580c10390f880042042c5087c02d00071200521400e40329002e50a251205000c1442002404001048002d00d070107407c025080c001c0c10010b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 163512958 1250 163511708 163511713
    0x2070f030809120c0904150e06180c010507030518060403060504050a050f0f07050405090c120c13020703020318120703050307211d0a03140105090c03070f050409080403060e 76
    0xc00300400d20940110329003c5604650103881040750329914012030541c0142c1c4000003003105008880c0a078040c000002c0c00603501d014074400c010030f045000d51030100984490086900004407000103440d140701d00600900010000c0045013000c801e40c29404040800241160340740640d40d0b120030040b10805d40d0101c5aa17084504e2800a01ca010090110b07001001c0002e0218002010b810b03035519501881550301490300d51002a2691005002d240703603414015020352040307001c181001da01c03130003035200303d40c4030345a2203120018071003c0d44207039404146e0540045107000c06a98403031074503100e6000321552003160b401c00c09461078010712489005512030001181c071019140b8210a200e071a0140303902c000001e180b080401c2c2c0d40d100206099030342030706541822900300000803035880a296000943786582c1084144d07120001540a00e10444c415415506400f40341c07003c154449009100d44c42c20720070818018042071030503500c401000c40c42001c116144c56501e5642c0c3e01914500440701d6205c0c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 163514208 1250 163512958 163512967
    0x222090207170a0c06050c0903030c0604030314010b07141e010b030c041401030308040501020f030709082419020d1a090907050102060703050703140c040906090216060c02070f0308 79
    0x100d0b0541c50010314a2280c4441c60a1201d4000e000344162200c1501601d00c507281d0740400c105e14a4041200c0c48441702805030380e5107000c0b44080950b40d207801c1c1d03800c0380028075024a20708003090004109040c0c80c40803444130b20b01380451320f4100b5003564807480c03101c00e4010380d0a050702c0c4241d58008401083c170400c002140c940d40d54800c060505e4180d09030a401681012055049020b0b100c501505595050410500030380703c6091075802400346d4000c40880c400000180501e40e5003210300c84040f01c804000321070000c0d01800d40102d91407031107030203003040001610114000c5200380041c1071070313058921001818410506d80c0041915801c030010a040a0b0f09e1a0420440c1403040c080d9074070422900080c0403851800000070f5035004010040000c0668903070101308000c1c8241c10440e8101c8420350b41041d20b080c07601c0d0000407540548244506e0354541400064000583d000751034400344025148202c0c0c10f0240c03200c1c0c000e0014064604114001d030300000c18042400f8030600c010358041c0003100e868 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 163515458 1250 163514208 163514213
    0x6020d0306060c0f0b04030c0b04080306040501090207050727020f0a23030c030a11180f1e10020102070c090b10360902040e06040b010f020a060222090207 68
    0x12a10182c00290070002c40b8000180824a10748002d00c0f59a0310141c143c1c0242d8943c1004c0340d41c50072070000141055440c4080c8030030701c10850060b501941f0b084400708803c0e6a120142c030b04a116401c00102140c00c50401084010b0703c900d070f42e54400450401d5420900c0003c42c40030200c5c1c0c0480e200c40d820700000324525540a83c0840c1c0061076954940b03114550028009401e1010f000c0180442031718070001000900034002c94010400814001401c00d40b1504d000d1011382c840030110507414021002402d60401c540340c05481c0c4480007200455103140c034102403052294004443c00d1600544d074003004200001003064420300010007002600045406000e410065031f074880503021030400106500496101345640b01c07660300070462100b0405103180e111002c100c01141ca6002070b0385d0707034808900040c001000c104070b544500703c00c0b036003000a00c07400c0c801903804011034010940141d1010300c1d0b180000311f803640206441000c5219410006001108519000500750010245d80da000700d0705404 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 163516708 1250 163515458 163515461
    0x230304090c0507080d0209040f0e060a110f0711030a02030a241103060d030c0501050703020904150303080c070302070306051e07020105070203030a1a031204030b0903041412150106020d03 82
    0x5100181d0724285180500b252501901c0d405013000400903980d0001e2030004a6903541d10110100300705420503c42403601140c540d499940c221040f5907000d040000807005032103080100c50031000d1902d5a10300340b2426845000080c503404501c03640522483c174041016079000c10401c0100c40c400c0e210000000d0640b07146014115010201c0603640c1d060101d1544030280b03031030599500c0311094451400e10013141c18122f800c101c072200701030b04a518080034000010351680013058607810549050005074500f480100d8245828417018000070b00c01004100d890124400800088d0300a104840581d078881d103484045441c1a104c2e03680c0b0501d4101031040c1443c0d60100d10b0346c0b2090a0008110b0b074501010041e4503440002c00c03a0314200d6680300000a03000c0c060010071669000502142c10140c9000343c8841550b2140c00103492070031158001a008032000001c40d0151644a440005038880110500c0382580202e03081008a00800e420300c4801201d00c51418000d000da5801403255043e00b00c0d0280 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 163517958 1250 163516708 163516721
    0x3120903030403020f0309030a121b08040504150e010306020306010903050102040e0114030f060114060417030405121603030518091e01090608210f0307020c1c0f02040923030409 78
    0x1a994200b071180098913900411103a90307594000700c912b800c403d2552402c8600c10303d02c2216252134400803200c1800d001d40d0202038402d60308140c0342000040c0c1c0a01418560f16142d22030410341e0440d0700014000a1500d802840d04504181000d54540340c44e0307500c1e942a80c0044c0c01c02000e0342e402500410007195181504000150250701030b040d440c400440340d50315540705000b81110950303000d0b0190000d464400c11140104001c0c240c0f0f08a021040d40059121341c017611889100709041035802c950b440b008620000c03194404800c02411915555003035445030011054200104080044460180c41e0004010301c20748042c056520703000c2610102504003207068022240003840e0900c2030100c02e1000410600444199125500c559540c2450a005124650032201c08102c0030080c022440d0700001c607814900310444806081d8820840c2d01042d020304138030050301301e20301302c0480009400c05a01204186004d9250540440319166140740009641a0b100d03105a200003800c0000e000c4510070300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 163519208 1250 163517958 163517983
    0x50105040606090204051e01111603050c0405091009021507060f05100803040519120c0e07030c0c03050c0708060118110309030f03130b040312050f04021e030312090303040302 77
    0x4c60806040a020505021010382c286110072134035050386160f82c2c001c14001410141080448240005050341068114100d200864081c8a020780340205032600340213151041c41e010380103288220a0000000150100c1d02d01607803c1703084410341d071845011a00003041c0c614040e00001c0f9001820100c010100c4000410101a6503603041d824408084003008403021600120b80310107010038212940c00c540c2e207040c1d014000341303c0c034144404100800002d81074200e414001c129241a980e42c1019825940072000401c005011b009045001900550241c00740340c600301c00312039480361920030305032800c6401c3e0003030f44954180c08020320800006004a0701000c0644a40c1340c1142050900c00b55240192241100070f904084002091803d10901d510952034025100c0021400c007410050041034041003000360a605041c009041c504030021414025079002e00200c1d400b4540c040d108d034120f40700407845503140c001003184c010b031169030504c5980104004009036a50781800c1c50084d140039031003e0003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 163520458 1250 163519208 163519211
    0x1206130902060906090f0604030b090610082d01060e0603010f14070c1a010303050310060e0a1a1303060e07050a240302090618010809031c0f11040305010504060609 72
    0x400060b02c075001682c0c0e00c0f00d81620203a444254500004051140ba01000c2e41c100b0030210b00001804500b0807841e008900840c10f8030866120010440c80c0018a4040c2800c568481c08442e48400c0506206045480601d07480d1988002141c0c0c10500b951281d622030f517008170120050098601d0280300340362503241d902408101c070001d41207420f01c036a00c2c000e0032034051000c280c1c03c2c14203100310340e060201e0b484080401d0742115a101c1ca03000d4410b0b041075031140601c40e540f820106070180140d070015200907000705408543e0b807901100070500401040082c400c41c00a1025802c01d04510700c20801a520035603001c15500300740c0e00a540f80105c0b990101d071182c105083c08005808240e1015194581038804100b0303203101c506019406403050350300b01d030307001000002c81ea90800a081501f41100e10242e0f140074107500da40e80704d00d68a001e00822030045142c0b049030b03030800d0051075000301c40c07241c000100805c0906c1040c10f10740003500260300544d030594440d800c1100b000001c1c403420001d00201d41c1e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 163521708 1250 163520458 163520471
    0x308040b0709030321061505130e0f060d020402090d080d0e0616050706090f11100503012d03020918010e0d0f05130e010b04050a14090426120613 64
    0x20f000340b944180600c114904031411405c002c0c0c16595400400c0500303400140844810460640108039a0000c1000903442da80900c0100d9401d249200080c0140040320310114181c07542e40030030540c010f4000b422644140c2c03c000750300b00c2d61182284401e203a1302442001d070711100b20810f030005580ca4507071029000e4022a00300623580c1c000110102d000840340c602980c07030340d005140500051914100240005601c22480b20030020b80400080007d44d013642d1065015036414010342d0316000c00e004400c3d20060035118842c1a840b13184e4400d411106031801051820b65039000700c6c4100000340c0c0e44064060200130300e503104082c00d0140300c60f01c958000041c05125807103030009140104043c11031040140000f0000c0c200d41c0c40010900140080e40c0000649503074400c0d04a01503801032007228041c0640d0074000440d13820465803402441c80c050604031941c2d40315a1a0011420003140f182112945021030700d16448640c00030f401c8000c0c3e031415a8440d420150104004424030100c2090080d082c0704 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 163522958 1250 163521708 163521713
    0xc0112050405060f040303020d0f0203071107210807020909010509071208070b070201021b0d1803080304080f07050a080706050108031e09010c05030c0a0c1d06090703180308040b070903 81
    0x91041d0707000d0700e082900d144d542c0f038518089010f881001c069014141c1451180040c6107890340c0254061010ba0700d99920748036140f1841515034801e0320826510842424400c648602c5925002070b40602c1440000c3c0340c0000b907400035280400544142d11280e6495042102c0726004204d607001400c16000418808041e1341e80c0c0e05654410094010440e002d000e01141505000350181d070220342003070790f41010a824003034015039a400000c107000c0c0007c5202c40341c011210802c08002040c5ca0700004d80380e103150b82e0350729000344d15842010744050031042008031002051050040840d914400c3d07100310342e54600c6040c26800e482040c0c0010585400801c1400340820110050848810807500d01544840ba44c1e0010780b1007021521025095000c0042d40c0c051800d0003003850401c49105400c400d42ca103840c1c10314402c00800c0b401045215a0031400450042c3c47c200700b140364010000d1402088928a00202c070080c410450000c8011442d10800c1c0010840070798040b03a401805480d203440f000c1d2668 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 163524208 1250 163522958 163522963
    0x320042306280903060c0c020a0603060b0304020f010504080d03020301030c2106090501200d05092d0a15020904060801050c0423060c16061d01050a0306030c06020c0112050405 77
    0x480e8201c050444142e90409090090185900a54214030104510b076035658000d445540e2041e4103d215910164000c10309900a128141c140c41c0690a00742c21591940c2c00d0004500d011124541440010321000a202c1b804100010340e50403103a401580380e504d503140c2503141320400d400c190140b402d6038400601c0e102080c040ac3d014a5080980400c5c2280c072410030754010041d185140400c6032100020714900742514006042c410200d003420400c81da189260151540d041e0400c0d44d01c0031081d031918034452140302e0052001510000e040d5a2860f40030360300c2c4c2d103442614030b1070103d9458001c42c4820441c981441900000e006c464028006464921251141c52086020700401c00382c01e0b0315582c1454610105a0a00d400d025244640d29a03c524540b503582100c4a0329441c00141e210021030031920802c0c0c0c0c0c240114030089800070000c141001914180c002e2000070782051340d1217030000085424440500300034106600940700030444440010401520f00f0341c0100e4060a0170280800103500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 163525458 1250 163524208 163524247
    0x30e060705030f060a08030f0c0609010e0c120319030c02011b200a05010c0203120c070c03030509061905090f01110703020603040201170703050609070f0f0320042306 73
    0x803182c0682080d51a00c000521710740d583e4100505034840401c00141540e840801019440e407030340220390440e6200480300d804e07200364003185000da03005104115602c2c02c0c03054140344624a2503040d20304020807030340c4072500c06c000c400807000002e4440d50000c210035028480c20340b10821300d2075018504c0e5403800f000382c204c07074188902c0e486004010562140003030052106800181e130043c0244240143c40c0d00c029a2038011040004c2411400741c0810b01086604003150b41d07031980400560002440c54405903501c1c0c01843c100358001604011145034010f84521140043c4203d2303c0d007545070100c20b01440955175410345458180950410684169400001d105045950407a115a9656990301c0100d0f10a5a207800311410005000244501c0f80e030541c00480c441c581c2a07806500564500c40b0032a545201305074400e000c641b80c0d10004a00c40c1c031a402c0386540c1c840009120032010300b48511080300d5409503226900380862014505081c036440c242d0400c400c601214018102420b01000c40a4180d5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 163526708 1250 163525458 163525471
    0x1a03042a05100c06060f0914090a020f0f0303190f0207050604150201020702090901140609131205160605010f05041104060e0d080d021206040507140d091b0303030e06070503 76
    0x4003102c000788800d11804201c0d40c0954062000c1c08810b90700c0d0b00d00426a44240503100603542040008480c0341611802284030300c1c0310000410380e0904a400340303d5071070248807456800c202e1258102456823000c10040002c20200380945d1492a041034000f0720f00c1c2401080c5100b15000307910104440e984420681d000e40380500010075151110010a900a00c55154000d41280c0c400c020040c4141c410b5011904a122404034401290740300d008100200038111140d0f1a108440b0b4842808070b9032100f80034015070b080c0d081c41131400b20040006461a103007a10221503480c3c4640043c08445071800c0c41c10020002030303c080c048146029543c0c44180a5030198904010710541a074030141d64441640e00119080030829559010640c0050042c0d40420141802001c030040419400e013040c1c813500d403184000381d440100020080701d030721400c0d40c84648440741c040c3d21901c01d0000f0480000409100809050144455a2951030098180c41d0075584c413140070341000e8204000f09820408aa51040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 163527958 1250 163526708 163526719
    0x108060a0c0201061d090715091a04060c0816050115060e0d030c20060403031707080105061e090303040603060e070302130b03040f14010209040b041a0d0c1a03042a05 73
    0x9560035081c911f400380e554488540e06103012070101038242c01060038003d42e914100744010b500b0031013180c10701d80d114500c202030010348030300501c1e03000c42d84550240000c41448040c1c07040002c4551500c42c20b47d41c42103007403800502200c000700302050b042080380d203060409032043c48140150741c40251010000030000362001107030401185130790820044504000c00001c000d6521a501c0c0d0030010041402c40c005108804003130008101805d000700704c041d040340c0d0003c0c8518602140d54115108140c4004e818189900301407040e180c89940510103000a000d469400090003840c103d0300c006030820182101051610400581c090312006180c0041030b10403c540c0d032541c0c0d456600c0d00d1650b8200701d54014103510031890703241c158520190014480c020040701c046c8181c400c000308020444010300c080c070180412140386925181000d0507500b2881e8003c00001080ea0ba550b81c1000c4800c2c0c0c09d4030a2400c40000100b00000c11220700011803589220100381999060b601d14940300040701c9010313152151 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 163529208 1250 163527958 163527961
    0x90613030207030f0614060603060a0b0a0e27060d0c09110c0a060c0801140102100504170403050606040f0204030201080619091103090d03090c120c0e0108060a0c0201061d 75
    0x5070081050400655008070340100010503420000b005250f02d50021010042d8940030401c01d190100550340a103100419880d1031526040d142c4805a100309075803008c0c072042c190b54400c96614804088403000f02d02c0581a8030014040000301c2c9000c000300305502c910718041d06c075004030f540c000008050700c0e80d040d40061000550449801d5501503c2d20f014040c0c41201c0000041088603003006020701d045440300704090342c1760703801079840310b450300c000e140181e120409003500e028280c7c0060782c11500407200310504440041c0514440c0d0320a4000307480d035521030303020301025003032601c140c108404400900f14249811980020204e10000d0003107880b407140d015000300618040d8100344018007400104200e508030680e004560307500201d03008000c500031010070180c020f001e4010303071021a07030010b204416a400c00790010004000114180d0304180c0707244020480351003121102e1b019009060082c9114508210b0903000e440324881c101046905040d020030000c84003810110705c60031616085000da = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 163530458 1250 163529208 163529213
    0xc10050a0512132102012f160203010606090608010b120705180307151106010f170c06030705181207060c0201171609090614040e03070f060e0c0405090613 68
    0x141c55015405441040411341e28480342000d5480c481c10756000340c00034440125102400114421005031056080c50320001c80c01c00100454001d100409030030210803110041a00440d00b11a056040140800c0006609001254000d40b82c90700500650204030700d801e1552454091008000c0c0002007441004159034124000219042c4a4908007908403100c1d60356503406001070f118100f980c200440c2004e601c245102801050350b506942c4102d44112035145440c0c04003104007140e60040b0702c10300a1a030308209030313514400218062080c03590b6070781d1224450001e50001070410348100384038502905080b01d400701c0218070913089030268244200c0200080c00141c41008a0581c2034611000d14003c01505411070030940610051765500d0b10590344e151001a401c4412034011000040a05e424142044c0380a41040c42c1542d14103040c6c1e810140309640d0b5901e640c0d000c00c1c0481e0b130540c64507031503142110200180c0740008402c036018003483c18441102c98507001c1c00b800c241c00c5000503d854030103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 163531708 1250 163530458 163530481
    0x411040b030c09100518040506070e03030f07030801140301020a020d0f05040f03060615020609070e1801050a1a01210506030a0b0106020c03100504030503060d060b10020c10050a0512 80
    0x502c0d08003401d41101850003900c0e43c0111074103401024418140700340c03405941d0034240c80607441140d005004003825201c5403400d40d9030301e440c020800c0e0705203c01c01513800e280190001034000300f81700391607401d440c0d41801112412400f000c50000d0190b0300c180148008564005500030301c5680718245034036040c031080e40c1114180f0464106071018083d01c0390000801a803030f80b00b601100e0042c0414201c03402d903800e0403a2161020b81b500c007800d03448500f040c0700080f900d03041e070307500b00c00d100c0000c04520700b8009509003507540c112202d0b031100755908400c1d20000109003100c0007909007440d0101e607088240e10030141985160080d00209580c034000603070240c90802a01d181c4a1300f06644403a55039550200a41d13455040140e10300070b0280e0858846008100c2c000e0600403603254503010706507550361042c441d60040d20201590000d1722600f01400d2a21408400708982402d82c0c050314011180e401030100b40980d00071050200704003080b68004142c0e2007010b90b07514041d420510701554440008000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 163532958 1250 163531708 163531723
    0x30106061704030f270305010b0906090a0c031b020f070b0a090605030c07020409081e090d03050309010609230c0405010e0d06020c10021b01090201080a0e2517060411040b03 76
    0x411115030740c105d016030b86200109078201e910980080c030648200c0010b01c0391000c4290344658100b0288008030708917803c16080242c520b412031800080d408204070b070008040d00c101c0c04910158116050790380f0f07000014801d800143c2003024030940741c11f00d40d640060000c4034038440c55040003000b10200701181114005c0710314040c0c00a005000100c0d150070a03014a500000321080141114042001c0c8030990f02d042e0f071484680108840b800400a89080c1d882da0b100030140380180d540d4a501090840c681d20420040000d41581607000345090601c9040190001d04131300d520071002e0104001c5c07680d008002003101d00c8141c401100c0c1440750301d4000003a0003940e80c40c20240c0211050200c405a160340501030a40c0c600680003002441555003500301e0b0556a0080c1c001801c000018448038001d400c00b064070a2414100c1340300000f4440f050055800180c21240300020014041040b50746034107031003800e12109005000281095941c118108910301041802903071180c00e940d48550b000d10407403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 163534208 1250 163532958 163532987
    0x114040e0a05331609080708151f080303070e030c1f02070801020a0c02130b0d0303110c070305060a05010e01061b150c03060e0106020106180510051c02030106061704030f 75
    0x400c09401c000c60328134420f13101440358100203242444001201e0300001828012030300782d80c0140c5410300480e074041281a40040940c05c404405084100707446c074042111200034170365403000e95107a04002c5001480c484401211620aa00c11196440c56649401c1c0800c1035035a501c0c03142110182c010f80130707402d000d120362045140c2e520101d4501811078200884105c1213108403080300e01600e01e800320208580380c150405400102805a4070f00280c0240d1000000b08805001d490500700c48484680c5010300c3c0c1c0d00103c441d13400c16421301c15503030140e000d20b13400b608514454280541c18803100601a2643c2d00d905c82c0d10b01e881c290500b080c07103030082c10340e030fa43c5059280c1400049000304016018001c103100d5810101009000042c00c00d2041c480c110648090800301c03c24005a0940100a040050a45034164040e1240015165650200081c0600c1c0c0d02954085032012801010300f12142540002c003030101c640440040502c059400d02e61255050030032800d00381c80c00400b203440d2544100413 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 163535458 1250 163534208 163534303
    0x2702062703070905040b010501050c060610090f12020906060301080a030c1a0106050702101b0303020904020f03040f290705180901081f020403020d170d050114040e0a05 74
    0x102e24020140c0004e445903000c0c0e0040b43d096607913580111080e114000c4983d4090f0040300208043d8075015540d01e200240d41d20b0040341c41d40d221042445004882d9201b1a00050302151401c03c601300345202e1a80314004658140c115894502c3c655290002c0c0100202000f01e880ac141080164452101c2000340c000e003811640366031212400b600590014206038452050546044034452003040c180051184140d4940d22010403680c090340650010007903140e0158003402910000100c140c040c51140d40103003004180c10005080523050308904045c1c5528541d10400c0e904803218103081480e403c0746251a1030f41d5900211403819490000e01e180040c0e10001203c00010221000640c0c0380c08041c0500058200058501611040303104500c0000c1d0000c020610110105200c8100007145521203601580307031107031240f0315030f08580c000d8120411465141107003604070b0030107100362214603401000600e83e8034005e49442e03640b2046542c0840c10b044481e8031404402c0f4900b1071480022408019 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 163536708 1250 163535458 163535473
    0x7020d06140a0506010e0d0c21080307030615081014040b03100f0b031f02031f090c0806061303080f041d01080f0304030c1a0c0a03032702062703 64
    0x40c814050f000654040d400a00c062070304184614141c40d0002d6081d600001059440d40380107110184020328156401d030003007a82d5404004103001c00300031840b8411a940004e482410a41000917411016200100b08500c5008100088500b908400c082d9011080340c0380c2d40b06000c5001401802015111030f8040c001c1040781200049960401e13200f1303080000c2c00380018503508050569071240c501402c3ca008004451410803000d069000b150007650000e417509500840108000102010742d002295082e5114030310341c0440d80c81692030350007100c00c43d1524a0079150652117016001c0d10300006d0000f0200141034201c0d00c40100c1260001c0c03c8006400c1040e00488a41c010b021100744500b41060041280303a146071035020088038103480c2e00112620215091055441e0803010850400e04180010049084003040400200450502c00d65000c07606400c200d801c0d14011022407204203400301ca0310000c00050b80e03a80e0558040810309441050041c0d19044008030074040d1301001c41d010b004144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 163537958 1250 163536708 163536721
    0x3071407050f0115080309010507020f0a0e040f0302011b080a0b01030e0706120609020702150d1122170c01050706090206070c06030e0a0b0103030e01020c04020307050d0f090807020d0614 82
    0x100944e80c041003c4640b010000e40d1400c2c00d43d1039100d01e1003510300191080214800603d840502c0d0756241101504589074280c035503005441c0c02c0d40079601034801c001991100310805074240a141900f4205051804103c0600c0350080c04044014042030f05c00c40d101c04203100d180c0d119510050809d03000a086620a07075445001411455200c0d424604080c106440803403543c0850007100ca400d58013a001c0750103c44d00c82da900b1100d8020807018421152281c84200030305c06490054a140c80303140c240340c1e0290100c1e100301d810601c80c0c1e1380320004aa0030100c2ca6401c0000105102400d13403000c2c00e00035514400d6103000c40c014840300c10002e5000d080030996009004517011513100361003540d101002000807401c00b035507482c142154010543c1c02c40303100520000c0d00c90700c02e081144c08180110b9007210aa1000141607070811503201c40021004111000074211901444000300140c80081100d13409070740714040c0700d201da000081c0c0200410701c103036020402e0359407042c980c00d010311182880504003074 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 163539208 1250 163537958 163537961
    0x50303070c05120304120c110a0603021b010618020c070504091218030b0112020301180b09010b0a030215030705041d040b2521020301030b090601060507050303071407050f01 76
    0xd141c1503400d40f0503610366050782052a02124000c540000c00c0700c02d00c040d1103c0440e041e00b0700c008211071040e100090a2125210b84030524003403c020f807005030300d50300030f000425010103100e0740c103400d140e0400b00100208c011030421000300795541840580c0d86c0c81e0305100503141c030900380d0100d50824902582c0c030052105071801441078a549a4800456030000c0f03e158900300075600010b0302034810100100301d907409121605809920250003c5005c2a5000c500040450f029800307807408082281000198130080c494078600c05c20880d0fa82c00d5140c11600440c031405110009490000d10000100c1c400900800640d0014a03514061032150402007410080381002903070110303500004c040200300c8003074040310210003a2019031800641e0a039a8a02141c032001d07030414444190000c481d01c81c1942d1110b00007180610701503030f0703100c035141041d04a162034104160b00200030400e007070000200080002c011a81c01500501e8000c18400c01051041498410f1300c02c02032052066010309040640107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 163540458 1250 163539208 163539227
    0x150c0e0a0e1602060906011202040609021b01061703030c070302160306020d150513090c1205070503060f040b01090504020a0510030c090602030c0a0308150306040302071e0e010b0703030905030307 86
    0x30703242041002c494041a40d07140030035900d0800a0300410018003080c11242c5c0900e0b07000340018004106159195401000c81c4d00c200c1d0200c42d620a04d188010403c6000d01030303080141119404203c00f040f1005c0059203d0002400fa240442000a881428940b0800c9040300400c19100d5210506580b0301e48000254000441445d1041c101600781e4200100c003620003003202c40241c480d00d03002c00d480082100611404400312092809140041000e103101c00e5141d0002d88070380000c0440c141050205461700340028805a80c00700024100000511140e0420341180c01c020340c01700307668a80f4400a510035120750843c0c0c0e009150709951040072503068000071500030317441d00c4120300e07207031030744022602c070b100310b0450400c0343e4414424400007d00c00c0d174000c2c2d84042151480c40d01c41491400003400d160050700c00303800690004005100c10342c40108420604000b2002c40101d091422003a10b120320014407800125000c089850001d0501035000b24440d40d40c0007098070341d6032803c03082c064408240d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 163541708 1250 163540458 163540471
    0x2150d06140a03020904051203070207060207140a0506031306022719151101020703030203160801050901090908070c0e070e0a0e06040c050c0708010c0305090604150c0e0a0e 76
    0x4108000030450208000e4007518070002d4582c102c45402c580030701000a502800894551003410b81081d00803004401560140c0041e90103421400c1c94210004c0c03814082c0e030803500501d01104c0d128096950382d690740c00100d50b01a03d00e21740782d903101c0484e035008298108000c4d000030700004465441c1a0032003a013410024442e43c408107000208800e102d581700d020b81c0d1554442c4c220354014071466840c00c2c21048218028076210f6a101c05141c902c81c00c3e0b8000c2c020490100382c001c4140103c00c00301050107a82441c551505440c40c0d0b2414000854486040c440d4003100780d40e9181103828404110212103800d50000d41c882c1940740e46e08200c1500780c4044846500041c3c034420102302d94078061612004441d11804170351305039200c4030308000c001c2200d00015001c2c0b00080200320420f0006101c520000c10301c8000008940e503601d48040d098031001004140207402550800000400c5000e00111450280c0c0d800541c0c8000480c0940308507920722201a030054204030001860034400c2e284030300c01d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 163542958 1250 163541708 163541711
    0xe0312041214150a05060409140307140d05040b071e0c05040b0409050318010504050a03060506031209090f04060b040f02030a390201140a02210105030c091302150d 72
    0xc0340c402c80c81e80c071000a00d0900c0802c194400100756982465008160420b00090000900800c103684039030070b03410554030b50b00a03600003007680c400344a07000b1030700d01e0510180000f510400c100ca05000b8028499401000c400c0d0402080503170a024081c942a2480c0303030615400c02140c1d0350350609202440c5180305941c4114101109804503042c81e00584100b0b5902000841c18014898000d404405120191034100001444002225030780c41c3c042ea0020342c051000007600e414100103050411214010110000d0802c10002c0d40980b24841010792242210a101845e078031580742440142280c640b4030741e4443e00b40b0341031015400244d4020350203407034405010045450140701142000865002c43d82d110005e100180181c1c3d0100b00c901001201c4500c0001000f41038002072000c451401c0e54000241503011500035a45032620b10801c5a00b082c07080c3c02c1090350301d0400020b541c1c0c44c06406070380c000e040c404081a498011841400d940d00d80c002c080b03800000c18a080190150420f41103a12252b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 163544208 1250 163542958 163542983
    0xb090106050a09230306072303060915030f1e06010e13020126040c0501080a050c0d0906020c030c012c0a03081302090408030105030d0e0a05010e03120412 68
    0x390061084400c0c02ca015110401107a10344054100321105400241c094480401e10041c42e0344c0c1c0503c43c00b4800c0c9841c3d01c40000040000c0c2121022400041803c51040b0b42001840059925a41c2e0130754041c031601e214040e0454550046401e00c0e18903900c0d940b10b48034046000c05030340041018030006d4500c200850b81560f0b070b1450300c0c3e015003105031484040400e001000a000d07500c140002d1014500801081c030039038100c000ca40604240803101a030741c14110709014031003907030b00c03203c21908041c103108248640c0c00d0460b00c0b1406031148500c02d2030314650300d002004c10000d5a07015944a14051002d4a40b10161004170360f01901e828018001101d070907002141e1480d043c000c0851000741c001e002044401c00503503090b10500009001c11030107060100e4110f0059891889003031040380b0650000340c903075251000385480c0c0700c0c0000f07040b8180711402078044144c2d264040c544048410910340101e07408400300110342800705202880c0340b00000041e000c662580b040c802202c440d44074019903040f4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 163545458 1250 163544208 163544219
    0x6020303190504080909060d0c0305072102031b0a0b0f09010807090e01030b060a0e0711010b1e0f150c03030907051e1e0406031b0609051507240b0901 66
    0x100e4004443c02084ea003405e2015542d82d041540710651b00c00006800c24101004640b101015101c0c558412550340d4000581800240145d00780040c1c0301c2c65a21101c0310f0359445030b000a0301d503049007203450080d81c1000280201540c5019100c0b000300005142d8036039501c0304400310321003079100080d07950104800e1004140c619101d4491441110b03802444285980d0843d0b84c0d801081c100902103d5000d0303800c14010500b058800009030091485464950b101e048010304182502c0c003510010740f140120044940c0c04881606113810301c0c0c0c50444036402540d40c2d00f0000303903a40d0700a1041c3d184008003c5444042010004025800340d0f0317000c0116405c00b640c540400900112440c411800000041d0b9400c0742403c2401c108040f0480011032644804807401c0882c00700c0e112070744255a13818070b01179040341c1c5010010001018200c2c030f15180000d07900749008100486d881304a91501c030840001d0800038860034a01d20885103001c0003501101c031200d490564080e1a1800120340f082c090540009803 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 163546708 1250 163545458 163545461
    0x3020d0c03090c0f0308040b0c0709020f070c0501051309270302070303020f0d0e0105030a060512030a030b0303030403050702120f01140603011b080112020301060e1317040503031209160602030319 86
    0x3146d500c140201e1400781007010010541d08a90301d0325020f440b03480760106a00e1003030b0014284164510455944074080350a0810702680140e00050501204118040c03024180380101010346403d0340010440f144140040c50f061404560a40801521a00ca8a042650104820b02180e000303a085450074242002c03820385491101c45028040b8285041c064455400b41c4050350740401034060028449580360301007801000004903907c0036800019101d88a540c0602c41ea0307003922030960085045203020765004d000342c03003000303c003921440741115a80001e030003c00050149161100080c0101171140061030319201301560508e119508000310034a6844030b06130301141d4004aa0b07942c04050b440d10a41070320391018604143e03003654071400b021401301c580c906010700900b10b90401f0040c1c200141001290b12000300e540d8003039410104410001a0f8001007696007110050f4a8003400c2d403181c00d0382c07600d0302800442d80300760810707000b00000b00f084d00800034501c04d2034026048415203900748500d00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 163547958 1250 163546708 163546739
    0x130c0509011b050f0717031903020f28080601020105040f0b0603101107020f091905100e07021b010e0a03080c1515040b0d03080a05040303020d0c03090c 67
    0x500084050003051020340c4500c0c000e040ba0b4101d41c0e850041420603803a0541026450080a0351a80c0814000c00681202a0400550041903400b40d41428801240c0e65920015990400304054001c9a4039031318484c1003007181c0f0b041114190114000300300002e5013141c0c0041d4201c000101d4030790400140c1c0d41d40180980d034070555100038808400002a541c0d0f80695002030102d0f42c0611440f0345169040c0c900d403040f1101d0340c910400682e20303941d251041140c0c601d01c0380015401462040d017032103404e541c0001c952043c80c6040c02c000c2070030740c2c41c1040104002c80d1544441c0d0103d028505100da13030b0b600481d0480c148030a007411815003103009001542c034107980b100055042000c1c03035001c2011a08400103048120310900540f0310540c03001c40c410414cd20b0954054050110092000302e6030300c1c1034404c00420720000c1c0c501040f0401151409000d11800901d0614010f8aa20001d01094400d504035944e820458000300589540c4000040040814010403581030808a9000c90101b48008501 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 163549208 1250 163547958 163547981
    0xe0a03020f040e0111040306060e070906120203040f06230f06150702060c0105070504060f0e010903020d031110020c010609060e041e0519050c0d05070b0a0e04050405030913 76
    0x2401c00001c0c4a05100c01000501c880e2010b82d50384098078203c00d03162030000e00040d80140c0022500c94141820140e2403500a85a0f400f407041e4440d04100444d08416691026903103c07500607101d90b2103003046841e601107501c0081c4154645107580d098040f0301da88014961003d21000019540c80e800380422043d030943d40180d00051014804e01c0d2510800001e003103c0d40301410751418001c2003c0b0f51825140b0684080002c650702180500020fa0701540c5d00720340340850b04d4138810407004580084c18078401c0d804064050b0408408030310526000d00c244200410a941c02c0341d00300500f0080c108000d400502c00c204d80d9500f00000041c1c407500500504064070b5004010308079944580d603800b1321041d134406002107401c0c0f880e0391440c08660b003404060402074251003041180619894030a0600b102c0403032103441a41402043d40116900050358010384580418441c1c2c0c401861105072800d1284c8440030340d000d41444200300c00c00c44044050046200306552515400c03055012010a40e0320b00442c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 163550458 1250 163549208 163549219
    0x604140f0a0323040306020406080f090102040302010c15150b03010f064103010801050402041b1e02010e0a08040306050609010303051912140106020f0312010e100b0408010c0e0a0302 80
    0x100f0700e030156840e009140c0008031140c3c030307480e0507641d0362048181d030000d03405070000c43c50303020400c15201100d0780d1880e404200c5c0c10085141509650004c1c0c6041c0c04008081c2c1004141d0302052140707031643c3d0284515400c42952800b55a03603901c58219154401d015050a0740020341c030000d881d900682c94a041103002c02c0e840540114200403104107081104c414028070900f03881c014007070021802c01140a8003036103001107120300c0c05005002c16108040c8ea044245081c20341c949016650001c6c0c1c5091010344811311210078154190304a01625280281071340e07600a2480704000c010ba810020411a885000700b80305a503503c50030030030801c1c824030025001c11000c01c89954a0b2441400c90503c21900e030900b0442c81085c5000e240071681c501e081e4540000b0841c1c018001e540e01004481241200c3e400198a00003282d160f0b501680010f2040030910411100818091150202c0134000313803031103e400e5903c3c0c03941c580e107203406005100344200c0802ca4610f03250000341064108101603d802038513 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 163551708 1250 163550458 163550477
    0x5010f090e03041206060b160218060306070e010e18040b07110601030305070503040308041805010906050d02130e0d0206070810140108090a02060301150917150c07050604140f0a03 79
    0xc201c0c0c074402d004d8004880090340c0d031001003081e4600030080d040c0d0700c1c0d602c00c40b0a0704116a2060043c80c40c405105d07624250440070402010350740004515a00006034034201d62001c0e80500140c03803500307413155000d910a210455100410540004183c411405006480180d44442e00f064516100304072001c903050304660014800f007402003005000d007503c50002c0704d02c0e250307032910761540d150801d400c1801d400c205206003803003800c21401214003400440d042041000c0c0f03024001030101c45292802401400000c43d01c0c058043c03103a1001020b69001c1098403401b100c00c000094071070302c08640c0314002c10716010108409a0f01460001c041d202071404680c0881d001e500151002c2900030031031031640c070a9507907040041c0c0711100514024034400143c1811401c24541c013400007081034205581c0b103245030000c100e10060014034080c100013040304400207501c52440103405c6106070600980144204c0c4140702c10007071080812044100001e041d500301c0f00105800b192181c0050102800260b40c030b85 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 163552958 1250 163551708 163551719
    0x10b1807050c03040e011202011d01020729040b1c200d0219050d06091404062c030a270608090c0406090504020307062a03030b030303090105010f090e0304 68
    0x8000b4060661460112420a60380e5043c0a90001003600700c200c204890b00004011940c0192000b603c4c0c000480c8200391203120749000035540c00440c8951441e154030f000c0340e140038031a041c10340c28000304000d44440d522500c52881d0700465000e00c00168108001c450914001011881188021098001d0710000c1d24001d0b2401485900100750030f2000950030040b0b41290201f43c071006401841d50b45906440b041c3c98800c0c142110b07081d0340484105800d09410303c0d0b102000c41c544950160f07001d14000307011402e1802c282486580c0210641d48026860340c1660040c2000002d04003c0c1e1066030b4000802c00c0004c54034899041c1082c1c80184448500411302044c1d000303001065100c001401201d01e10080b0100180565035558440d0350400d90b100305100039400d040c41203501401c00c03418003201c8950000b1400301800c00382c281201c0c8481c405c82505040502c01e403c0902c0c01c0304001c0803039889003071114055000b06401e1240c007050700b44a8500041000382c90140f59000505140518180ba1070507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 163554208 1250 163552958 163552967
    0x140a0f050f040e0709062c04020a03090b15041505010e01080702012301030c06110a0809031207050f0606030c0d14070305010e252d0e0a0c02010b1807 66
    0x31079594080e407409002c041150048444840e12909103035843d1601d15150180c0034203c031a12818420310703c2c41b8800c81c104003419002c01100680401e58006035100c9010000b00e000786a000c40003040102001d052102100c1074103070100319002c084038104041c4000c0040f0f180580300b0346c4190742c007041501e9805406503000d8400d1961109450001103008003044c1d4805101d400f6100c244038007201c90100510070f01c40541d111001030506400d01c880294120341c0781d1661a581010f004100110000d2200c4460b2814000760605203805d1740d03020b403120654684180ca410360011080141c0c0702e1140054580d107400119008120401342a00b40411000d403951b40011040306000c06080c4541500000060003d2140102026012000c2c0400850607902041e5841c00c10460280243e00800284100074a0f0000441030800c60702c281c1c1c0600e90355801203c60000d043d0b100c280342a0100007040140d0207141c002001100080e0300801c0318540b08020003c1100e08490850440c0203014000707050140207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 163555458 1250 163554208 163554217
    0xc010c0b06091306020a121401030201020c060307020c0d080409050603060c031603110313020909070302030607030b030a0c0f14040203090717100e0106030b07020f120d020405060d0c140a0f05 84
    0x4042c0b00b610f40f1515502c8680c00eaa201160641c005160118201034030100c038131440d0648044600e6642e0700354510340000b0755030030012038900e10510000010070300160080214044405001d4420b514076903680c2085d07078264000d84140f5454505040c0018400d29020138000c0c41000c414088509544688100e20115001c0d090003170141aa1040c80e0b9911600e6036020f180718512100d6000007604103441070042c0404090103001d02c56211a4050006135400f040441e0302c42e951341740004401040c80002440d001c4110300241001034424000700d80c4507581d6102030242c0c0e104111413221b101511082c00100d2108403804511600150000d00c0300044081c6d90b44a50202841150b1740b005403021104220b0f44944512070b5a41e540300b6007001005a0150100e070b10440781d0019201d482d40140e180d0340c0703c01112151015104000070442800c10055066034040c0c08040c01494544140c0038140c0000d00320581080089202943d80d82c030591619402c039101c1e420113a4400500c10280d0f0380a0703c084c1c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 163556708 1250 163555458 163555471
    0x210a0915110105190c021c030f09021201090501050903070809040f29011e050307030b1309050c150906040e1009020d14101a03040c0b0406020f0c010c0b0609 69
    0x300030700e42407103074024010540141800c40f070080502480c0702466040300e4901c030000c010f540001032002180802503541180c2d88a003030a01194040d1303032035440c100400981c1300084d448880030b890341012480c150702042506100341c1c003c019030344a08912a42d0fa0190000050201e4410800685142455001010000c540c0f000210f00c3c0e0102d01c0c46d103000948d50300100e02c43c0501e840102070f855a4031000e115100c61001048450042032058020000d100040500003403580f250900401900d428083d000800e40c00c5008102d075110a103040380d03e9003180e010035407042507a40d048810820800c0c0072078001102c018803c62415181190b00d081d654801440c07003070400e0174140005800c0390240010318210b4134450000903082801d091040500030051b02d681006010030360144040c4004030207a407100e0003104241d64603a542da281c0011510f0682d04440551034020800085542c0c00080202c400b510340f006075001d1403030b00740044401b070300640301c098049004907000c035100d030034112401c40d000b80303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 163557958 1250 163556708 163556717
    0xb07020402130e01080a12050a090e130b0a06081209061b01060918060507030e1002091507120912050607030b0622050109050a0b0703050307050706090302210a0915 72
    0x5545090f104002403090713020842540180c502002007040800c3c21030110310079402e04508058800f035000704182c40301c0c000d4803241c615030b00206140d0701d240512500c0182e40030403100594a0314003c0d01c00039001c10f00c80c40c10715218043d02082c0c48034207001500c2c210700e4080d243c14180031500408074012401c0742d0300021695a01c1030702140d110224007505206c2c411031034010030381c240245000300407640d008120004051401d00c0c60200d40a011640684c000c503000c0c005a107400d0490300040208038400f4105161440020b0300e902080380c040ca032070001008a403501d0041555468a80d10b0190703a44800a2160f0401400900c0c907500941c010a511a00504928104021043d00c186e00c040510b400501c048500d4804000075030303000d24100d01800e4240d0b00004198038010307115107580101440203040c0300d03000c00042c41840c450320070740d43c1c11074002105020700011810040e445d030720351040c0310750b020418192007422042c1860498840310f0700e5035641e036290f500c0c1c05250000c00c0034880c901002c00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 163559208 1250 163557958 163557997
    0x41805390301030501020304030e040e0c0402030601120626060c090405042109050307050d0503070b070513121209080a030f03060b0a02010608010e070303020712060908072a0b07020402 81
    0x580080c009540070750310600005a4a04160a000c0c21003520805401c0c411401c0c08688212800c0c00301d694080100c040d0740260302d07500c03040016210328003441c55500b0014a40000010000543c3c2e01e0b0190705d615000c0724465103210340702140d894010840b6481e203104030400c010318103030034607510043d41300d40248001c01418a0044648c00b80d691000c00f0500021200741c070074441450b00340607240003000d045401d2400c0764150303a5555240e002e0b011000d0450454080050492401402203031554245041c651800c65151400341a0244525409582003c12071068943d254050902700d002e460080700204139140c1030745d9003206d980301901a400101500d900000402d81480b1025002d40c580a40020917014180f100382400c41d880c214161440342c0c407403803003040440d4001c203048040c0c0707480b010f0341c0c21240014142500903141f5580020032507000066468140405203003084111460482600c2c0959011206d036040a1054046c25001300e000b0080d940c010314260f8002c0100d10702c00303442c450b403a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 163560458 1250 163559208 163559311
    0xf032013080610120305041809020301060e090a03030e0a0204140115090f0504020d1409010c120911060a03110a08180601030507061110060602160f0f0909050c03070b041805 76
    0x35108140f810800480d140c0452402b10b00d000e025402c094600080c500c081803604100c1c566131400d03e10009000c1c1550f0390340403420031909105014059030040d1003803110b0302d04164410f150b64070911071000c0307801d800f104211060703101c1c2c040541101c003c68003001d501404c0808010081d4449141c0442d499913030780140a4000f00c0380c6840e4400c0700c0b0f140000070f00034505000a00340205014481c1a01468411001e00040001e03206c65012042a601d0301d445032030b0103006034010140040c40c03030162000420100c0366140e1014070b0b00d00ca441c45401c40d01d0001c0040300100d5642c54280001043e6800481061081078410402d801c689018401255080007140505c18200c2e1910307000000141c000084030180c00727620803a0301e0010a00b804041c2c580d1490b115046c1001003030707030203500001920342d0181da042c801e042002404c1d5403402000d6076841da0340c80400c00c1083e0300c54410a01c2080c0911004801c0d80454480d0754401c0318402d1000c050344142101e0701d40755881c01ca40c2c0712215041c281f0f00b410f4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 163561708 1250 163560458 163560479
    0x6010e0d05030a0324031b0b0414100f1211090604030b0f090f06060d151d070501030603150207021f0201020c010513050d0f03201308061012030504 65
    0x30a140104040c543e1200040401000c0c3c50b1400001942080c41e041c03d0f004410400003d1800c480d00f080950528400049140349000319550000b405201d01040c00715270140110346081881c02e046410b01c000000801081d142910001c18000206141407959240c02080da00182020600300c080e162a00c00c2e40710000b031441c0c100340c10607101e103c003c400300500100e61030712a94111141c00c008041c1c1951b40c8260541c2c0d03d0b0300030034140c02001c0c8080d494003002090461900b81029120040c03282000094840c14501000e00f50172030948124100003401d0350003403159a05882d0040910003242d180e00402601a5101e080d0481e0051260000f602c04041d0008141c01e0768403070f5900140c2c1d20702c40024070038207450001d8100034000c03681070700705c0c0001200050684510215424111103640c0c0e03440007500104a448400e00c40321141d80c0020401d00040702c000c00d50070340c50544405016895481d00b5540f2201225030514100c2c561009100e00141004081d207038621900c1d10510749900d86d2020035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 163562958 1250 163561708 163561729
    0x1050c070602010203010801050109050402060a110a02090405010944040902040608180c0a05090702071e0612050f19060506070627030503060d020109150c03020d020c01020705040506010e 82
    0x1c0182d42c040018030160f030080c0111401090340210901580c145900051000e2107800c02002c1402540b020052400c0003e001d54205160001d004a00d285007909040b400380900344000ca50744d00070300680301550303400400c1c00c0c0c0d10305200b20030320350204000c42d40e90018100791942142c5140c00c00d010006500c0b000d4002480600055500c21540707060140c24102d0070000f51103001c0c1d07550040c202c101d0150329041580310403203404a603003a2003a26800e0301682845c190f0380011507200c103410200036045a0755842007044494070307560804031101c00005101280c5007554540b8145c052080480e030b1455507840070302c040420300c0000149440d5120000383c01d41d800038008440007131715240c1141c4007403002642d01c00140040358456890860a80d4014a10b200040065114000e5803241c0317825a44510903400241c0400224003a40010102d8054482c10040e00118014031810702050f00b1588085800801401c2c180c00411403a420001080b024010040005040054544030304915982e03005040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 163564208 1250 163562958 163562969
    0xa02030601410904030c021003390c0203160807050f091006081905040f05011b020d031e0906060509070201060f09051008060f06030c091e0601050c07 66
    0xc2441d00090b07118254000100c148075001c00540c0c5050340140c1c404944201154004403901c0340c0f1560f482c0760607520001500000b9400007034007144641c02a803d94020380305c2c4000c180d08050003005840c0880904191450034488210007006600c034444d01588140c08514801401d4510056034200081d42010f001d5000e0703c2e050340040000c1180c1d0404110032050000d094a21b00c81503d0401c1d6001c40090541c801c0b40104058031000030204111240f82c1c05025903282c07414422803c0c5400d003000c458103003010585840d4617010b050800c4600850310600c00481c260050312805410403826001005c440107a141c000031000c2410060441300d114065040b0306c2440d00141403400c2005101d412a0018549000d687c5484402d02c14410340855517800c035444014041140e90720360810007201c0d40240c0c484d44040c8221b07028400f40400f100603107845080306504075680001c480b4204020030106540d0004080703c000c94078040008402c1c52141c4c071050604016203030103038507080b51740742c004c459221 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 163565458 1250 163564208 163564229
    0x6070f08030717010b0307021b0f0d03020303060a0807080a060203190603081b03091e0d0c0e0a0f0507141e0d0623010f0c1703040c0302030114071209050a02030601 72
    0x101c507001c3d081007805014160b0340c80910b04502c0e0042010350340304542145e41042c48d96200610116684007400400340910240020a64001c00c0c5130107980d0740c00542d8864802c01c00c183c00841c2c05080020354108442070356005050220703190700c0705c200950000d005828610380341c813003a54040341390740500d000841c8a04003480d51540380c101990624410207a05840d290420010181103954100d00b02c0841d61440000050b2614800300041c01360710203000080690445060014840300c44c1202544221803200d814401c8403e005205021200111031000c04110034803000b0401c980b00c080508088501720112501400201780704500750741049000f410103940f100004d001200d540f0031920210002800002e92604009001a04010642aa180400c04c1900e41a411310125041048000e00c1409580307a40b030800381000c007810032041c0001e0b8081d40c2031000c0c101d4a0502c01c060148607030015a103035080003001b10340e03400107090b0809060f54903106010010006d81d0b81400320900804000c00c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 163566708 1250 163565458 163565477
    0x30703080a0b0406030c030b06120d050a0c060c03021c06120b06030a15052a070b041a10060914090609090309030613020f0102070b07150609020d2009060906070f080307 74
    0x10700723080c1007400400c0780f4007d00c81400c1503113000e0400164030707211400c0d60400740e40b580a21201150422040383d40501071904150006040076059401003800d00010790b251110481411400783c2690b2140c0304d048040440c2c54000c00100b8000b441e5190019001029901520419120256024a425060b190003540c0d8024040c502601d07003c9840c2101d069040c00054200d141d2840e800c074050000f015000344c0f407500c002810001d07106d1404030803c8600b0400f0301c19007000c1038807680304602d03406031801061114401084107480b0303601d01c0e500c1510050452907260303182428007000c440e02a10070b203072510040c8400c1c400c0756010b01c10705128032500b4454425400362801004140c680005902d81590414071080c0b0180d020b5000b10b41c00180c208191049001c0c260f4803840040526030b0002134100d102141140b4000526006104071035402210f004900c0401c032005407881c40b5a00741c3e65030005041001c905a401e00710040d1182034000c3c14500401a07540c3c4848681d030b8007c0310b134400001c901c0c81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 163567958 1250 163566708 163566713
    0x1805010b01080907030209011511070b03040201090b0313030c050c0303041202090c0f072d05010203150a0b0406030906021e0a11010216020121020f0c06150102030703080a0b0406030c03 81
    0x161100d502110040044c00c840389141c010a940500601030310300e0300ca808100c0704e81803d00030160360100e0070314070040750000fa50f11080b44150341c0003603800300c2c0001c46401d000030b0a9440b0400303481c0200e5030805e140000301d250350f406a4070702c00c2c0610704865a00611005444a64080c00078000a0003907030051650820144100041500010502c04840000f481008a0209040282c0f810181d0040d45d190200c40502103030002d1400783e00980d05400030031176204040041c190007442c080c40a141100d008414100100b040001c0c0902400100380003d0104115051182d00098043ca00070b0400600c0c20707010084500d800108420510b1450200040d4008102e40c400307009580f10741c4c0c1800850603e05848000f24442c1040c1c48081e04016900c40c80c0c043c54440412021314031102d0803411903803109644125021134005a82800403070160b83c00007555051030f103410100701801640a140b410305259415114440041c000151150780d401480351603456a2161402560086000c40710301c0f403662 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 163569208 1250 163567958 163567967
    0x2104050a0902070b0403050d020705030412060507030c230f0c010605150f090409030e100e100e0306010e0705160b1902090f01080a020c03030a0501050a080f07181805010b01 76
    0x940c00069110b104001d150003142510100c9508950b051822555901c04c0035110006030040603006001400006000980c00348400c80046116100e60000d10080e0b607190801e80480345140700210108800405040d12030741080c06000781414421201c60402c0441da4144c1d42d40e4100100c42c00042e0b45d5047e00380114a022100000f44d10900050285408001051680c80b40a0885114083c0351100707901c45c00c06001e4084091518000340140c90445940c2800515420308481114002c042c00700d80c880c1c0b40d9108481e071511021010380180140d074600b81020040040081500c41003003818440403048422021100391074030f0040c0c4102c0b41d07a0401141400480c0240d8080c9600f0f02c0c070400a018141d11014007007804c407402401c060740c05075180b4810502a11418020305002d010000420005580d180e02c003c0c1656019139000d400c040e01d95014684d0f4040034030074003050382d0114100b00b1560088080410400002040210b0000018114080100c140c2d400c204c9599440c2d01f00300e0751031b5910 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 163570458 1250 163569208 163569229
    0x5010e01030b0f0c07031d10030f050a09050a08030601020a0804091401061e0c0c0f08030d0b0103020309250b0c100b040b060a031805060106050a0e0102030403020f0d05210405 77
    0x901e0031040f081d0501541030005881a880000d00340512266001c0140300e04031468000d640c0042c3c800d0100c9858840020003c04008031110b02c0107143c6008500c00c59aa0300c500c081d03541d8090014a0b4180d41a00c1e40030141e08003c1802d070440c402c10a025001640e000f0141c0001c0030121400310b00c103030300a8190600340e4016008002005400c00b0b0500e0b0410354003000302410340c41418901c08010075400c1c9024024081d800c0811400204840041e020b075001000b040400580001005221090801181644030580f8002c410380e02406986007a281d5030020507503020fa1040742038004655071a242c250700c2d040200521502c2d00100c1c85541000658001d1107002c48003184d041083c0b00008000411500448960383c3c10143d40f0f6881704a2519030112010b84150050203c40c51580e5640700182141d111086900c006503214141440030b50001051350103507507009280f1610141082c0034419190300180065409114880f228040321010492813650820120300c940c0d0788178209024441c0d44481e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 163571708 1250 163570458 163570471
    0x306061707080109020d060218090106020309011d01080105090a0902090406091103210d060513020304050d0503100510210b01020d080c1210090f02090a17060f0702030403050105010e01030b 83
    0x1071400c04d10059a4600b0820031040c0d001200685502140901e107004011401c0c4061304104c01c5800406c1c071f50380010162000072802d070b0790050742041c0320400b40705007450f0600a13800704511307130014007040c602601940c2d40709400080001d070700d040c3c0e500000c2c10540191415114540d441040405200c074070018525410025402802d006803407408141807842903040d8a04d1941001c00c89070f002c10340b9500860001c04004106d503003241000030741940254000c0da411a07181c45514541c00200303015100340ca02c00c1e14840fa503004050b107041d0500c100314a10b00d45a0041161844441720039003441031203840700080c2d00e0b600041c44104c060002e45401010711000d02444143c9013080040080d10080307512030307041c42c0340a075500c0c0c85182240b803c54a2a4010700c070883c1c03d0401081d41001ca0354003401c601034045912072007495440c0410030b44441d0010703a02c3d629801920005881c50500316050303170040315070f01c1142c0ca41a601d88802c0e084a6083e0460056105400010014002900001c1e5000175 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 163572958 1250 163571708 163571711
    0x140f0f010c030305060a05121b030a05030a030207080d020c010504050f03090604031205070f030201020a02010c0c050c01180b070602180a42030902040e010c0c0308040c03060617070801 81
    0x146000190400c00c0300500102056101c200151031520303050420002000040c1c06a100800402134042d00e41150030041030003500303050140000c6140020320958000d070405d020354035200103100110080d51110b40f080e508003404100d50b24901d000740c401000300c6d1406400005542c10a441c0050500200002c5082658401e0001c0d50040d0350755801c5804995101018203200c0c101d842055809004280010b44030901041004d402c6c50740640083c94210800c1d402000103c04250082d130391458800c2010b00103601c462028041e0b540079a03600c3c1946030204005d540010b03559031911910394420b101c02ca41d20380e0045051b4050030004846601c0240080740c20f6003000e82004d050801c03140100544d40e503c0d2a0302004495400080b03590803000d40790384003c014960350700b10341c064054089120102e0280745803516100e020207040c445d40c10f0300b4400d40e803a00c0700c41c2c40c95141200c004034050419035025405900010005610748551001440705400300030114a5000402c0c4c10301e442540002040d9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 163574208 1250 163572958 163572979
    0x15030507030c0e12070e07020a0308010503070b030a0c020106050303131404020f0910030e010903080f100b09060d0f091b0b03010e01051005070c0f15020102040e060103020c030d06140f 81
    0x10b4010384043d40380d001c2902c041ca000c154085200d0b1400000e58482c038001e403c0502480600c40c0d0110f1808155406a01d809450781d80c0d075400e241c1e40388100d200301c80100ca414408241140940e0300443c00e141d40300d00c0007240303040d112000241140e02401c041490241040e41c10052060034407810081142d0803181141824807483c000c0c8428803c0302e114601c220f9801e800c0c4c685140c000d034000d029124030040200510866490044d142100640b4840c88400c01c4000091a00c07094010b000e0543c4c151294039820724943c9818000e040d003100a032107080c0b64a0b070480b680d00003800e1090940c10360107a4560340d14500540c0904090101f550081c1c0580361007080180403058130b11041d40e04684040c0c410f0200c01420036400c032058010800020f20b07000303488100050084103c41581c055404c1049090044882900e041c0d00b00c1c480e40c41114031101c2e240000615030342c00795010704000400c4005907480e151180307034190100d588541110446419410311440c0f1420551500b581c100710a0740c40b010503 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 163575458 1250 163574208 163574231
    0x80604020a030b1306060b070b060f0d0b070207050303070605070801050604120201120b060a0807020f010b01080c0901020a2301110414090907050a0305031b0a03090608090114011503050703 83
    0x4110242c000502408407100c0480c01d40c010740030400030440e0b00710300704100d4951201c24045080d0710444040c1d8010320342c0c5000c2030091030118043d41c13070600c2c000d15011099820780c0c0c40c44150b060007021642540a41980022141c505100422609101d00c40010b81440c7c100781c09403000d02d068118078020402070006209550742031010798045602401c101400a010759000d0700030307000c08208250045030114800c22240d81048420380a611a902502c20b41c07014040880e081f00c004a40c81800143e103040418050084031004011462061060318162003643d12182400341c103100c070004111400c40d440c10140039003807140606080410689a182070302e40080f1b000010401100344d0300c90304001c4089501d81d04c041241030010203010307000d80c48055890074130b42c0d00d942044130300c0d0740d041c5074201c0c42914410300030815000c8198107807500340034030b420424111100b031801001000959610860740312000c05001a0a0003044c0e028441c11030f44c0001c04000701907900241c9100d05160410065030403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 163576708 1250 163575458 163575469
    0x2100615020618210909060411090603130503210109090b07030b190b180303040605030106110c0d242702030111030c090901060203090112020c15100f08060402 70
    0x8100c040da40760104000d583c04620b900700401c80e82d101006000e0520160050034214010f4050410103c82c125900d6894005100c140c61900c200d00c902034070104036035001850200051500f203400da086070344034200d840e602e81c3e04c0c40e40300449030840250401c1c04103089503034090280340504401003050000c41c045503075030045014090194405c2c1515040c04c0c0c40262140c403c0c40940303000d1412103003000f580c0c402e1020890381c80781c42d40c40410120641e4205071410000700b2a81240d15a40e1000d01d140e1920703808442e5003021804051040c00f5040440c083d82e40e980d445148003a004142c0c520f0340900500c1100514542c003c803034032545042103030003c0d030840c000b400141d180a0b06041c0d22070010b034a100190040010104642541d400841840070b88521270010b030000c0c090540b8043c02c3c40c0d03210032060ba44c0b80100c14685002a2511004100300c0680d80c01030081c0d40b80f090308540b00504201c03000c0003400c1d022120f1000b5006c0600341000044492103040004111150180503941410740201d0f1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 163577958 1250 163576708 163576711
    0xc020307050108040f020907050c0106060203090f061b06070f120506090103080a020106090204081006060504030b01050f040b04020a0f080a140619050604031202011a0d060507140a021006150206 85
    0x90600c1110f4000a0034003550460350b4403001c1c1d00404000d898076082d035020b4603640020120111640c42c0001c0031945a0001003280c09180005200050808108081040b20b52003500b41d000c03c1c42c42402c42e1401603500704102b6000d0b01d41c80e101d03540320381ca115000400040120344500b076064100303020302c14507844c0d04101034150b0360840d42460f40c4054483e0b081c3d014280d5648440000d9100140001d007160001c22450540844d103076081c450107a444408a81e00d0295000c05848800403c004000f40c1c40d1950003044c003039002510100c0d4218540001804030307000b0300d0005000c50365240c4d0307035101161701042d06540030900c4103041101110480704034030b4000008107018001c100900a110203054212007203801000b001f02946c1da200c2d200e181c03041280c000481c0391000356080074061070700d9034042d01c20509015005000f900f560304103a1900d502500003d8003034018000880003680c0000421700040c601300c0c44030b40040c505500b031001007800300d03041c9a011141100e1500295056140d0104146 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 163579208 1250 163577958 163577969
    0x30405040c03061d041e030e101404230a1e08060114040506040212014707061e0b030f0601140909070513090302011b090621090b090d0c020307 63
    0x41c0310a544901e080d0685002e440072041c1b18241c451141810168412000402110103403503030340b90f024001d0300664940b4078401500011352824030040c003c50a82d0400e00340100be00c00d444180003170b10f0b24003140e4922101d400041c0343d00013040c1c02d40805203040c4036680042c040365000f42019850644049072103002d1044051080352030f01b01250903070b07945406a0310002c03030607219800c9c0c03540d5441c103100100c0320074500f2045c0c82c0c1c41782c9a6520902500483d9001c0c25088940c071a195131902c01d1409001c0c1d0102e4012a61140c0da8001c003042d980035070051b03001e0b100d9444800511620402c00305840d010305028400c8040d4040001030116883c00e071002440c0d0041a608002c1544503600f62070b090016076000b02c2d410071030504010070740e0744454204c5400c3c0d500030f400800c14030036141c08240a03c5201014000400c4c030340300040020710f11512000c014820340c00505950f141358800c0300c0003911025417081d11555840001e0140600060000da0312180d132a04014044902d964042030b01d0b0380e60f070300c02c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 163580458 1250 163579208 163579259
    0x30e0d1706190b03010807062d080c0c12030106030f0204081902030a05011109040506010c0c0b0c0c12010c020c100806090a0603050607021b0616060c030e0f030405040c0306 76
    0x400c480c1c2c2e00406251010340105103019889686030001d0982d2a40544100000a19808407040d0388e034211400c032006901e0401e541403060b06c2d05d610140d510100c0500004103064003000840e000300ca080c00008080100a011590349516040005041d40c2d01001030640c0d00b4810002080b0061000400340030000325120090400c6881c1d00010741460000d80c0090003c0d400d00e50040703454000c0740018201004111001c004988540d0011608142d8006004112160803c02805040ca005000e000310340030346802c6079200318402c0e0100b100e0322002011426169100c0540300d00c0f10740c05000480380040182c441c0c4607400003448009114000251105008144540110740c14100d90b4101401564001d4101d80c19428002130080d900c0400070590549902d100c0d24140d883e02c0c1c00001c488403285480081010791000741c40e5100103126418026051558900c0a540b0160042c4255544000d680014584607886c00081c881a2158204101d007050b18001e818011010541c810261286403840d5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 163581708 1250 163580458 163580479
    0x20c0d050a02090906071404031203243f06020a03060306061e0f05012a0209010308070506070c0206070b060a2d140f100e10030e0d1706 60
    0xc0050401c601c200c000307034200b407022040040703416001458a016201701c1c0c1d1014054408101780e07400700d020b20f010084c140304402c030511600c54420340100c1d840d90304018194280e00c545070305102550b08603510182c00c05003142c0c03509843d0a01810a2102d407121719205041d14801c02e10303400840726070000c000b483c05c0c4d400f041c80c10007248242d00050203168400e40410005071102800d00c21100100008c21030380b0504030012a441540c0c42e1003004540f0103845034141002c19007980b142100290a08500c103904084d08000580d6607251154002c1d40123a41895480950703090071420008020403200031b00062000d06801030701d50301d0465030308036000f088100c180c0d281e0a0006040c4060356019400e800040d400b4000c1c1c907442c83c110640602d40c00c09031301e03d0302c1c0e50320310899500c2c08070070f0001da0f4008664201030440d81828060b00300075808618042c9000d00c405000141c0d041142514440080c1d034030404610b0051003008860098131060402d409482c5450341c200078105001810f06000740a88003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 163582958 1250 163581708 163581713
    0x30b12060108190f080f1c06050105180d0804060f120908041203051210080c090c0f03071b060603060e19030302090d0203010e0d020105100b0f180d03210c020c0d 71
    0x4503d0240a540702c5ca1095a074034031401c190303060b03401020038410304045a040d400540e80c07903841054100c1d2010385801b03082c10503514141d0b80024100c2c442a0f0844030041c1e180c0700040c80c880080002c0c18150303c0d00070100c880000c1c01000c440202d0144002645000e0003003011482c402c00b92001c8034804100760040810a140c120b03214052500703544030600c1540180201c1c801198011400c1c1d03590340301160368140710354040101f040d40680c2c0310390381d0300700400c0030311045546a0015540034060303081800d000165487c040c3c04070400050180c61381f507690001030040002d5401140d040641e1a0000c01004032442140c400180c4002002001e065001400403410b80711828000708058004000700050250005220f4682c04245520701c019440c0c040092101e001c0c080030b4009403503070100e189050244c1180120059404042c800348044605000100c86540d040c02986425110b5a1582d046031201000850b80858a504507507006051800156040380d000036640400e0000b265060044813050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 163584208 1250 163582958 163582973
    0x1003090203190203060705090a0b180d0f061404081b010b0a0305030711010c0827090c1305040e0a1e062405030a08090904030905030607030b1206010819 67
    0x2004000d40600a01e89a40e208414441901d85518000e0302640d146075074100341250940304520720359900550b8401c0038030400c800032019054221240c452400c1c0c4141c08000180f00c10242e03082240c01c403000390302d40020004a0300907420750706181c13131191403603050a580b80040f81c0a102c1085000100d110410420400250014446020040c0c801c000f00c640f83c0c01c100d81c496000c0c013400d40b10740c90b8001e14585154400c1e524851400c1d084024241484100c441c040304960700c18980c0b02c40807550110809280d511070700c07414040c8280c20549a540c440100081c407500f1203035030203c3e200d68078200d103078141340c003010070b800d20300940c00215031000c1c1040b12640000030101c0302000d4500d502d070001131044280d00c411100584051481c18001c0d0035030350801c044d036810140c40020807601c0280090100d509192101a4000340310342441e20b005034a40700403074681f29044910380c0c00680c40d540800428104003182c03103840c0500c0d0020340003075810600a00d030364040e01c080c0c01c900c583c000096403040c880340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 163585458 1250 163584208 163584221
    0x190f1a0d1b081b0d03050403080304111011010b0301050403120f06090906050603160b070305160f080a0909060b040b0702060d050f010509060118050402130302280b0a020307021003 79
    0x2140021030761910386400c03a0f0f640400841c030029403d400d040c05960f501e0b110300a074410710303856a505d41c40c4c2411076880034001e03080903200700c0c0e417010095044042550f905087c5800e200580d9540341041040e90185402d480c1c2001c044c1d40a40d02d0101444086540252824000c882456012a1403041100c0002c01440c3ca0b5212404581c94401d018040203000c0c0c00040c00340008808072007a003801c16515580a40d01d5114a089a44007002100c00107801580580001c00e0301c5e003101c64040d01185c0381d480d81110800c03021600300e00005001c40c4802d4011800c500503100c012020020309042c414a100309105e64042c7c240314460104540c01103503110b40031101c401c41c14131410711031802c2402282d18000c0c0203019052003000d00400040d017a520543c1102600e0070050800d013241071521042c40004c1d0b00801641100e0b103000e000100160b02d4902000040c9810003030312034403d00081015050001840d0454110380300100030b480e0345641e0001c00e4508090301291145c0410f1111941900180710707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 163586708 1250 163585458 163585493
    0xa09170d0915271a130803030f040f030903081c0608030a0203070b0a02090a090504110105030712110405060403080d06060f0c150b090a0504050c1002150a0f05190f1a0d 74
    0x134020300308084c2080c03981c09442041040b12101c20240e864207440340e12800700700c803a01c2c034004044002502094410054022150181c103029080a03280d0310703000c0240e8040c041007841056142030306060580c242c4607001c0100510300245003005003148000b0345a10400e076014000310006404618039108950488410500080c21004100c4d0740b080700b180a40300c04c4405464801ca82c40090400d540260201c0b4800d00d443e6449100d0f84004c2d01c141c40007040c540707001410b41c0809000114171502c6500003030019600500001d51602818040d40044d26260341011080041d1a00d0502400da00303c1c00b180130f01544a8980f02c011400d09000400408100c207001c0d40c0280c900c400e001e0030001660001c0e005034012402d17503d1801c500d505000811030710291140050703010340920072004c218404401d0700b1054140b00420500803840c0f209040d1407003600c10611072950510000c800d89103510400d8102e40100c8012b11807004050407100a40c01d290702d12a002e00007000b42202082101c50341d0509211 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 163587958 1250 163586708 163586729
    0x7050c030106060f0f0c020f10030902060a0e030f0c09011a0c070f06030b1e010c081315200c12030909041101030e0102071101050a09170d091527 64
    0x150f445a00514000b0034580700f0000c07030790300b0b40c20405440c80740103446a065005040110201e9248080c060600411240302042668440f1240b005030f0f103080c0240350519244e03641c425109203510070103041c80c0000303205082c3c0d03502a120050264a07903200980c11a4203040c810070380180e1142d03488019105001c0d0000c1d250049507c00700d01c002c07010112009031030066401708a141411070500010000480c2540c44424640c2c441e040258804c1c6039a0100a100307091042c00c000442100c060081010740050080c81320740784020245c623600108041d03048401ca0380b05034000c4501c0c09420b4590848040050180902c1070820040c14400c2048520700304010300101d03c1485e02c2e0a2209603036040c0c3c011907001038105103000310000414000c1e552001d80080800f40c07941038810055419502c03000c2114140303c0400e1000414401c055042018030b41c0020180960b0303001c010004111016a800400304c0c06007800d2125001940f10132000340b500d010100044610100d0480805054065400f102111 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 163589208 1250 163587958 163587971
    0x60503152412070801092d090f060c0e01080c0409050606190305092e1505060304080c0d0c030e0f01030608070807150201050103150b0a031e05060601090609060507050c0301 76
    0x294034202c1c0252203100316035110000350740c841d007104050b03404a49002c04a2a001003010b404003c900b00d00e05540c108048000032031301219941c4001c54550a4015503001e070f03445c96600310b096001061019051400d00c0c1c001c1481c40c01c52041e4982d4043c80c0114151543ea6000141003030710740714120380300391a030116004082d074030329000200a0001214540b000c4e000309800814001d01000c00c1d200d02454403880c0d03142610440c1c10150080c40007500c800b0030040c4607000051640c49078401180242d00807442203235696a0303404510f1500703003020000000c10591900a01c0402e5105044a248050440c0c02403041d10389940100c0140c8016040081903005030f910000b0358603070014482e401c50361280819000c50158050607822a54240b00240000c00740110880d440180ca5200d500c1440c0000c060403e040d0712516010100c84242030b0b00700c4008151041041480403c0100719030109091800003592401c1034001441c01c205480b9080034424003141d64010403900303000d0078400d440007034020003d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 163590458 1250 163589208 163589227
    0x4020405060f0c15100e090309122808040e040201030b04181106120c0706060806010f050111010b0604060e0102010603020301140f0714070f050f12030901060605031524 74
    0x442c0d102c0700058640344508070080291101520032244900104085c120b8000e1924400010b880001403280c4818081004072200b1940c461418811800044000b030845000c40c0c200b60548041c2450340c44131541003000104000340c807040403103042e203010b203c1000a544131031005a018102c03d07500254014101042c58a0440c3d019030020115170040c2c0903007982082e80000c2c0151440703407074a140c0b1164400e000181f24200040c0090900603c80e02c000196141d582c0d01c000d05101c400c3c0c111101211068504010315a400a64050350b420a00c00800540f503151000404520480c4159800d00c0321003010600c450707000f90f00000c011a0085c00030710880b0307519100d03820f8040003292000d0003d5190004112040c0c4101c1c02c00302444908051149403c50503155007851003400c450880b12440f5240c1013040d00f0310241300d038405402d500b00030262a0b09180c12171a00f51140c80d00310701c04001c400e00c01c00000c0001d04403e1907801c4001c0c0e0b02c2480c111a00c5800020407210500c0c200c0c480a00011a44807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 163591708 1250 163590458 163590487
    0x1b0703230316050f090111150c04060801080c0d20130c08090304030c12060204031b080f01140613140f04060510030803190605130209090a11030103110402040506 71
    0x10424880e10142c490b211a01000c0d6240d000d0b140c41040009070900c000702040d40603c4140c210350313103000c1c100c07005820703007018090115030110343d540c80ca002c0101b01000704d141c04c000f0b094050915080901018108140800e945803c01100075020084020184a00384900c2c04840c01460300078105503e48503000e1303203000107840d005000d1400288400300080c094440803041c0e809507644a0f042100c03d07442c0450082d94104220810b4611990070440000040c800220150241c2d01c0d8684180b4000e12f0003c006041c80320035200240c41743d050079a0183d13002110081680e11100403100c80001c00030050741c44008001c8100302000340080038060102000c4118015407242e031056800340308a5950f0520000011070502c0f00404110051020803500c50414601c1581c3d04a420400100079648000250101075100c0315000d0b4560300140000403428002a500e81c0510902c03424801024010101c00c024881440043c1421041c501c1d04803040c1d070307150122002000c004020390b072078503003a44e00f840 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 163592958 1250 163591708 163591711
    0x20a08060a051807080c0910020a05070504110a0c05031b03030f01120b0103060507120507050d110c0d11010f06230a03080a11150702010e060f1b07032303 68
    0x140310702801000050741d0303c2c0560840020003203d050001c044d480e00c000039240d40c0310103405111061014450000c2540352084982c582217101d500501215075141015414600690040e5000358140b4192a00010304541100c0ca0b80ca414601800042c0c082e0808074118058440b00320141501c500712011404400030295000d215075021540721643d0b64840c280303241c261b5007002041c0000280040000c101c4550126a001c4013504040c4298407020f100042182c504680b5007001c01c50100d090340b5440c0d8580b0401208604000b0041c0c50700890014460741e40000341d6041c0100544100c0c000c5c803081d801e41000400719604001884003545a5000303540c200100040c2c1c0c40d01751b50b0010701c40000e1404611081c1186d42044025140441100088070f500b81c0c510149540761050340d410603c0d02c00400201c500c40c0c5100d600000314510040b8200b070030aa4060043c8070042c0382079080c05104403841044c5400820400d00d510b03980c0b41185801c0d10100d00183e0558100740008954404607081d02c0d0081d0b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 163594208 1250 163592958 163592971
    0x14040801021801080a021305130e0106082d060103140a14010b010e030c0a03022b0f020a1e09020d060e10030b010602030f1206010311070303020a030c0519080c090301020a08 76
    0xb4013160384030440e4008078000c0e00f4015030310b40801242040582408850181d0303225003914003051158000c0c2410f802d40714290702000c0c0c1303544400f200c0310741031100c100d50003071703802c00c481e19605410560007100c1d030344e08010702018046016481d103404040c20100800700c00c16a11002c42c81244288141d054020519005407901103441c00d00e803020185804601c203151080010300080c1014155024008154207514200301d102d1a182c17900000761125602d0001c106204600885540700c03d0310500003001e511741e0240054001e282d900303144258440a007038080e00e4801d00d005172101c0d00e010070301c009011580d2141a10b12031060500c82c55409200421064a01030828011543d07a240000c0343e40744900714100260480511442c003031804044005a0400c4051401140d181c07030300701082840b0350084a0480200380e00107061742050b41c26024076000c4d943c4606155003098046c0003410100100c1003a600d0402c410480001d00550350201034803d500e4005c0d008549610494601412250b0143c0348e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 163595458 1250 163594208 163594217
    0x3050c010801050a0303120b0102030c01020d090c0506070b040b090307390803090d060906060608040b06030604080d23090a060f060308041206090f0b0105040b10020d14040801021801 80
    0xc40c640c104002e044c01144e501d603a881240c603000701240001400e103107004074110f003c10030088006000c24000340c112080000c1c0f0000e120300d000e141103604207400e5800980120070501444011440b0304d419036606c281c0286205001c1d640d0784080600f9442403d400030302c03806071a200c0041c01c0182c04100802d080001c2d076a03002c1003094400060601107644114a0302d44e00c100040451428181042310459208010110b07589082e69120816500350360891030016a90404210a02159880c401d8001c2401d07006090303241440d40300e1840030f121300e0044403e03458403652200c09007001c910040340c00d01003031004c100e100d003000320820ba102c0003c504240e640ca0b04140c0100e50081d0309218407401c4131390000c0410b00d000d20704000c5d022400d40300d2000340d61013a610886600481c55900388031000c144120030b80215503042c4400c003c00c907046103400502460144c540702e10709980000d46c000350404070b4140140c41c190300c00a051000e1080d40c00024083d4004284483d40c0140b407090720b0300001c0242c88 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 163596708 1250 163595458 163595461
    0xc03080306041a1e060c010f090309170a0b0408070b0106030c030623190f08010207060c0518060c19061a010f080a1a040207051606030b0307030b130c03050c0108 71
    0x114400409403c40c0d4581c000113103140c20f01e40080c040c003034403042000502590308207822200b000b4210780310703900301c80543c0703840f41c0600c401c159201180c0350181030003040031062880030713aa11540c0d038685140b006125285600205003400b1211055804156111501c07090640c0c40d07070401400341140312500b002007401c144d00800c00324001101c04501501540b01c83c4800c1000c0000c10030002c0c8444000c01c0110031030304000c81c40100c00c0d926000500f070803000140e0385480790f01d049011207988540740020031405011031802c540c01c43d06072017800ca4045503004d031901c1141c0c06403801c04446109040c8582d800e4a211000c21080341c00c420305d00c20075140c04041a0507004010b46074002c1d1200da80d00090320070300000308401e0180c0e109904c103540703141400380340c20b0420000c0b4003243c0c81990b00343c072154452070b0b000201c3c180251112028102c140b4040c8103090801c07000c81d0f5204064000100342110000005126081d404a00c144841e08506119821950b82c20002e40701d4484925080c00a040c450 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 163597958 1250 163596708 163596731
    0x2130933050102031603030b1203071b141210020d0905070e010302030a0b07141b01060801060f050f062803060504020a171008030a030b0f1017040804030c0308030604 73
    0x264100201c40060300654a00038824850181078414520704030280742d504c0707040700d0307a40c0c4130289103100c0058864011a512280d071b042041d484200039042c04404403102c501030059000a6400764201802541c0600100100e0010241058011018440000d10224044040042d560041d40c00720303010b4070585581644407500425040001d020181d010f03030008200000044520010b180c2c0414145440a50391040300340b001074131745c41042c00c144640d0401c02d06086e190710a1190310010710381c0000800c419803410301040342c40011445014400e00181000000f03541320081281d407000d030b00b0901212b0202d8940d1080040801500300350000078a8000b000c6140d013030500c202e1749511800d44801400c0300c1c8482e40318014200081500e50302000e01c03040040c0085c2d04001034009604e80d9200420741030600014440c80010a8035001e12442e050001d100125400040b0300a48200000001110741d8403030070f184465100744c0d40002d01c036a030860130000c18050501c010754088c120448060260340c1880 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 163599208 1250 163597958 163598051
    0x30106060c0813030f030309120c0203060a0c030b090a0204150e13020307051605060601020d0206010b19020f030a0201050a0f050405070b180604030f1e05030d021309 73
    0x240150350210340c05030791040105080801030000d0350340c6240c55041864882e03494581801074044120046500d402c083da0810082600100d1a2856841c00c0700d500c21035900065500c0c00c024209040c000e41d1001013aa2992180d0004400c001c0007400c2d00e040c5003001c0700d030403009500911072f12245040421440c0d15861098052070011880241418140c8006040520003548054816814080b0030070400c86c0c2041104d140f0500c40f4054000740c2281c0c684400003a040140c1d01c14074004640110005004a0541d038056810341685001035103484a0018005d0740340818901035130a1601c80172039845aa168150021031245400ca4001d01400b9800c050041c2515010f0303a0040194208520510031540d41e20b0113001e413001e03100203440315614081c000c070391981d015800694114881c440d02d40e0030b010180c0c1500d441d103c602c04100d5040b00003521003e80324000c8003120540d4940000780284461046580280900342605082020050340401e91000c00d403c003404132204062401c00017001001e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 163600458 1250 163599208 163599221
    0x309080d050403081308190203101e05070201060b0433020c0d05010209040e01140105030303070f03050601201606030204140108060604080a0f050606060301050d1104090b0a0605010e0301 82
    0x22500d4040c02d00d8115a50300255812998501300001ca1203d00040c100c0c50801c200c02c401070304110100c04076981d60040c1414a040c00c4405145641400b000c1c0100e0b00f41c07043c20000c02c00002400040c1d80c1c5071454201d0242881d5030111945940c0860f0204901c0b05400401012511950300c0e803589180c00703160407d640040401020160300402380f00910ba06200703103605080d501c1240014540100103000804861781451340c41001e80d55040100703000e110f00c00d030850140204030000c42c10b52403d420001d12486094400c842059141e10215100364050788100f4202c640c1403400c00c103e55002c241d040d543d6103582c03050a9084080080010f0194024421a0142d580c40c80c00002d10100c400019541c3c0034010304840d4119908100000d407900c010303c000343d0403521880103403074440502c1c01c0080c41d1600c00b400c180d01c15801080104107076526483c28001040e4131101508903003644d000010300410310090080c00003482c2d2402c012802401c0e900482c190b403402d0303d41442e0740329100245800c9482 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 163601708 1250 163600458 163600483
    0x60201060f0b0d0b0402030c040602061021080705011109040c0f020618100606020d020d05040e06010c05030702130e100e030f031b040605041403010b13020c0c1804030908 75
    0x1040c1d0703040c40300001d840014544501c3d115008102c88010300041400c87c0d100b125039003110b65010805102c6154140084d6800c8880107d41d000008d0409060920b501120101000c40c121041c02c42c004112141342512050340d0840c1c001c00003101d141400207410341c040900c5900c92403800c0804041c1c24028407104600e00031940c01403407150b03950100c4800010055100001c1ca01c030b414011f061075152401100040e01040e4080d02078031110b018040d00d0490b59031198010b020303052005010802c800829140c0c410703024640321400c00a03501f8041c3c01d6102c0d140001c0d404c408518189141c6503548e420011740483c80c601100e01c044062400304040ba601d911807011a13800412038a8034205141000c1c503004603000c0c906400f1002c183c035610b0b50342e60060b4000b41c0400d10101d1b082104010b0300c180740081c3d0300b0503030081c01003040c076500140007100000e01d0780c2280c56001c100c28180c504104451504994042e141ca400c2404000c0c000c0a0030030200d508030000340703a5800c080341003c40401c0c0e649441c0d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 163602958 1250 163601708 163601729
    0x20d050612060403180e0a0204090605100509060f040e0411011e0503040b0601090e1e18030a08100f06020705030607021903080702010906050f07020d050901051e070c0e09010606020106 81
    0x440e913960450f1203002e10301018203008a030503000300d2030b41c0c0d100d40058080c0b0102c1c84010f990350f00d0b0001d50350035115503501c0369114002c0c4544903800705400408803824040d003190401d56610128070b803100107004d6a0044003030140c95808010400c02c50500c0c8400c400401d0300d40d112404451501a10072840712800c540004006001180c0001c10418281d5081001410804c00c2da84d200d21443d28800784c2100c61400c0700101090589000710650081a0040761000b0208040171007030104a550b031186d00440702c20040718500003080302c3da40100c0701c0050301e2441901120955181e01c020b658040078001d4034840d00810004c14111800002d00794880f03c1c0110b6002010460350b00d040da0404801005e1200755505c1d680a440012403134498144201c00e59407040501d0b08204100070729007a802414541030140400401085a070098260b80000401c5540d0815140034800b0401c100d01403000c0003800b08000d80004950b402c2100c0140344160346c060020817602d03a484008034240d510f23603c159550303003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 163604208 1250 163602958 163602961
    0x19050a18060302090907060813020108010b0a0c0501060902091513121103030a17240d05150103050a02191805060301020712090609090e030415090e0703020d05061206 73
    0xd5080082551164041000004200e42d590700071400c0380800300e90307001c641d4000b001c0610410b40c0118003a504040700b01910b050481559001034807801040c080d0750039031200401c62076445403003a007500001c168400000e00000d5541d525070300c081c1d000300c5141e0b48601581d05882c2041c1952905440c1c10b04140103403900d00300c1c070701088802030707080500c0141c800b0074807075601754682d480c100000c00b24208955280d130540d003022642c6402050000d000e41e60203013070503082e00c001c0d181080640b11040c0c00884200e82c55041d035261292034030314502480780307030000300c840008140300c000b00f800c0c2c006600031b0324a002c4d05550861800c0d2242000d0040305407a440b0415944200c0c026680a82d0703011b4809800145082c5043e00e034040d90500c120b20300720002e05108028014198486d0309a002805030b00030078440c1b0040142055100d0240e401400042c518090a1a800500c120a00001401044410f524038204114010040e510104682485034100310219000b4107080381390758a0f000c1200090306c0d45 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 163605458 1250 163604208 163604219
    0x118050304030b060109090e0601050f04142e03050708010506030d12091e0c15170103080f0403150203070314010501120e012019140d020703140703020a0219050a 71
    0x4a9028013003d041003001140841c1c005514403500700030119880041445624282c00c000f04407003040c2c410f030700503420700d10140044d950300520300380c0200103c2485001003c089000e1580c40d0031f105015031240078000c40000502ca40828401d0590b00514003c0c4040d6403154141a541c02942200c0070004084001c2c42040012603884072144c1c40c8a10a89034140c14500c0300d08a10115140003607031002e03030314181000159001c940030410782a407410100d0710080b160b508600007200501c009011600001041180c0702d0010040394069640003081840d6201082503020080d003080b42c2c6440400c0c0740c0400c218105c03100c2804d260484005a40b520294441d20380241c01406000601030341c150740320028034915142140302d10244840c00c264007903c4c0c003900b1085000944848162800303100e0b0944800d40c080241c08115a030503003100c040580d8402c840d107000c44030b10201400e458800307030011441100b00b44d40854a10b003c2402210b51041d510002010f01490352518458207500601c041002c006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 163606708 1250 163605458 163605473
    0x3060905010503060f180a020d0803061306080d14070204090b0f07031104091e050106031a04050621070e0f090d08010806010909110a0e2505030601051b0d11011805030403 75
    0x105e400306c80141c13800102554007040000002e050115400b050110030001242050b013030903140d2403040c0c0c00070b1108074541119543ca50071980d4081c0d040011101c0113000b880e03529801c42d0a036641c05003042000c603c883c01c002100307800c103450102d100b81034030f00819a0344c1d1182c021a50b40490102c00c45141a24241c4000000c2c205c40c40b00850246e0700c65001d8501c1d03000c40c403c1c14000c05840d1004202c198410301c44180e005814065035200f01c0ca0070003403040540b40c00c1c1041101e000f002c4490464a107220000d54035000150f400001c0d0b4001c0c0c2c03030400c54008003926031a03002d1180102107501c2c11070b0b80007003940e0306031090082c2c0c40980d000800401408035150024194280641d071960010385d00f48001c100403081580000d08072034214400d0003443c20403685c45206541c0003507940104050074500040451201400040c10040045003144101c01150048140c11100f44212403107140b0030000982054001200745e940e6501c4c1091948500191600803607065034850050b5103000e045948000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 163607958 1250 163606708 163606741
    0x60a1406100e040c1d03011104060e0d05060406090b07030212070e0a08032d040819080c030a0e0405010602070e010b0c031c060302040b0402040b0d09020301021903060905010503060f 80
    0xd0070004804030445090b111803007100c260791300c90340d19491031031000008244e20b450300700c210900980c90515204e822065040c140c1e0255145464104402090342001400d0380070356880c080c28502030b0006000401002e85d0190b020688a400d004c0708a90b11000c00360120b0051301d5800503001440c0340001c4090344030b2801e1030312101005003c601a00d440318005495500300481d054840032a40900c000c141e141801840c0d0b0031440318a00c1403400d414440516100c5c0710010120300c20305a40310300c4400300660307601520780c5548001c1c107c80e03c0300f0600c200102034402c0c10b1040c1d03004a1a010001c40c4841c4049582d20076034442c6a4001d505034a0891100b01d40d40c098840b116460100340210b01c10340c0c0030354440c84000e68201201040e02400c60040204507800000d009114503c1000200242c12560f0140c403c0281c0c050400901082e640c004240039104241d00c214140320342402e01c80d881074160784208151201ca41c0100456a00c5a00f0b140e80c1d4034080c0e0308842c20b243c42400240c0c0705122040c020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 163609208 1250 163607958 163607989
    0x8040803060922030e180709090f060e0a0f060b0301050a0b0304080702120a06060f06080613060b03130b06030109031b0303140109050109050f0c1e04120605010503060a1406 76
    0x10524545a44a412042440c0d101200080c1001c4217440300c61404042c004000c030040b00d1155410300f4030030b4001e0305146070b81c41900701c00d0b034071041072074140526680524010450300d901b01c1400c1c50190702e07407001440d203112038030fa09030f04c1c085001c030b00054140203072810b80300082c0ca0340c50211700f06025041e140e000100111030301807080054500580f01d40180e40e101da11480000c0608201601d0104140ca090f5000041014480c102c1000301039400000c07190000030545441e401040e5219240014081d00d0f000304030b034250000180311038800c0c1d902c5080382560088030100000d441e440101400c0e1400040050005522841e603949103181807803a94103294841c1c100001c00d84014450074007162000d0740a80d5a0664450041052101500074603501210142c104412450070801d0750445004206034003803400c60602c01d066041452500b00d41c00340c0002c2d40000b541140c0c4d4a0490003900090003418000d01840b0042000d10400f4050304500340111440968280c1d03401c41030080c088640c0822 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 163610458 1250 163609208 163609231
    0xa06030305092101090f0209090a0c03020105090111011a100c0f0b0910090f0c060f020706080a020f030c0406020706090b090607030c0b09070e1f0902090a030c0f0602060106080408030609 82
    0x5034821100f09208080d4281e00c035400030f00481d581070042100e100303030060a10300d264000c07014060010310003c01860640fa424280741c0d40b1861110012a00c1442c101850b4586600e00396168800c030b840d0084502040d4821604800624030b0190101c0c0d00801155000b0018400351000c000080d400c240e41580c000703901c604560101d2048919502610381c1345000351101c0342c1882d0b100061055182c8401c02034011420030014804007075a0007590b40c4140d224000800102d07a010512a04454040300c0b1500c07401a00b0303548030f04000c032039240543d201d4444d020151141910026106005e000007000715110740d90b0650134442c3c164240f04041d03000c14411001c01404451000005821850217802504080014041c0300c1c1000c924820810002e0480304603225482070345401d090803040d020301079034800b140147e1203001c81c0001c44c2404010341c100a042444440c404140664400c800401b294081d508682c0c407070341d0301d4030140c40c1e1180076100030700f210104100040a0b4207140c42c1807038001080540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 163611708 1250 163610458 163610509
    0x902090721090b07110c040903171006050d0b1903030806040617030702043605070501050310060302070302070f12200f0d0312020a090e0a0603030509 66
    0x82a046045510501040c89181d00c14407140a1600c20724800428210420214099460390402c003140105558108009815495000441800608400300020b8070611003d0014500509040d94500188144001c4100020007550792018020101e4065443e010301d0200908004030141c400f10602c960800015422940c41c80b0075005500019402941c8601c0300c1d0505a0401c029200c40d0ba02a140082507030103501c20780340c4040103e03011a0b0b070440c3c0000c4e659451903070185600410034200c1c055000340340c2c0c2c2540c0032001030794070002061140c404c1d291055100c00c01034503e4001078032551201e5000d81d0302400001d01a5004040c1c260281c0100d4414a0b0ba8a10800c070100c85034105200310781c4007481001c20001100a160511008907601030b1481c8100404205800b018a04081c8200e00402d0100107160203200140c142c46071181d0199550740b00d024026040442c0c034494a1440300f80b000c00144100303420b11617001601d5044d503485103080c80003420056a078509a02000030360040e0031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 163612958 1250 163611708 163611713
    0x510050c0109050d0806040e0705100c0f0506042901080c0d06020d0c120e030708091c0501050c04030201140313080a050d0207050a020108251d03010c0206041110080f090109 76
    0x11440321311503590b072040d2034600310003448143c0e00d40004041545d44540000d101e15610f02d80b0400c9804541d15141c001750820781003c2d50056002c40d0060400e004400510040c890001c03840084800c41c880140b85045003a501782c2a542e009228050a86d005011180c2161070042088e10180b802000e015040c000c03003280c07180468034001c2c04a008100c100848940303a03c0e090040f40d40c201d416401940c204105a00d0310314140c03040c3c0364554800d0483c0c01c0c0f1f0403641c01c4030030b50023000141c01c00000c03c498500101c1c405145c0c2d01501040e404180360340f42115102c0018030440344201081c000b5080b01154558500055402c182e0019050040034003080042c00c0961002d0440603001d04020900003600e0300000d0510a0080c054011030810002d800b018144010504210454181382150f1124404040700850b0220150096455401c0400702c2010703640c001103203405540100020422101003804000e007440c1070840e484c000c039000301c002480c5151044102503128502e2000801c05240300e5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 163614208 1250 163612958 163612963
    0x2030a0f05070c140d08060f01021c17061203070308041e0309170102040b040b0310030204020d021206010e010c020f0307150206180d0909020a0903020406090e010f060510050c010905 80
    0x884403540007815140f03946007072001001c1c8210b02d115110028018000c04950004d1400000508460081d182d0b030360341e100542d20030130001103440070801c01c8420400e01d0440060500c664040b005002c0e04180300429028900144c4102007580843c000b549001180e42d025503402c000140142d030050b06115a010103421144200303410030b40302ea902c030102036042c05d02801d0710080007802290143e00c14402401204041c0c02240c050780c5607174810130380f00d544075042c1c01e40111340c541000303400500100e815038090744180c02030000e01c4507050b401e141d030340d49500046500811481d0311a0010b03104600604c050709020048000d140000ba0030755004a40381e2802d401c1256a039030316140103a11880400c140c0c10500140f110600c0e2502002d000301c42400360004160b0380c20f50041082040c0e00042d0356813581d0260712014000c6034040c10a101203981e0300c1c481030041c01c501807480299424108494402410f9102d0501a982c008010950500c1e10101c00c984c5500020455641590f85501d22004203004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 163615458 1250 163614208 163614211
    0xc050f0d030e070801090305032404020a09090e010b240405060c0d140301050a0b09220b03010f0b03030304033912020303090c240c060a0b030313060302030a0f05 71
    0x115107001ca00c058103018042e140072032562140407140d1600200c040000c0e03011040f60f811204110f04c45400c4017079a9000b078664100c07040c8456110b4800102401c01c1c507041168030088510402c0100800e03c1710009035402d9421070007580f9448807800001004001c01c50041d80350101c0c807030402509090f03c3d1030200c0c4072a440010400480ea001e1052a6040c0340d010031102c030400241c40f9201e0455260030040341c4030080a010721243e010000c14405000d03211700318212146c2c984e0480380c4104581d26151200100940b003a094060350038840f001c1008182070058040c40e010185c011480c1d83c1d1592400c464145400204d406e55940e0845640411001240701c660503407403540d40407201c00d2180c9090107030203904144134010341d0010300410880719400f01c0c1e01c41200d2415a04001d803039600c41000315140384443c4c0441d44c001c1022861007038001000600383d2040c0c0b800a070400082d122030081681c0c900600301c425500c81302c1758a0900c41e103482034001d1608440350b4503000c1119400d0440b00420b0720380 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 163616708 1250 163615458 163615483
    0x13090906020702150c0a030e0f10030c0201050a090f0213060b0415030c0e1f0e030703051e030c06071206030c06120506041802120f03030112030e0109060509010c050f 73
    0x100481c0d90b0042d4034010301044030b50080349140c03600c3e03c00605501c0f40c0f1140408000390911504c03150108280d00d905807176000c080c000408024150760040c001900808015000364015882c00000400f2140b840c8113074070785560403d80c81c40c130041c0d4560806c2032181c1e041454004207600c2d00d20001e030805d070444c060f02c05007400c1c2030303000310070b01d1904d400a040b103614000100810030342d1428040140c45000c200c0300c03959011080070b4a1800c0c2c1c20025030307000444212140d003502c00e4000002c24040080b500d803030600c00f600b1101c0391035000110407035624010304d15401075a4104802051038203008524180302c098500c040455829501d48682140388415444000490341e840c15450b00811148283d43c0d0200045078204120900d91041c501d0310340304201c009018440b80000000ca0103001c1180d00944801641161707525038440548010403809808114040f4011000b484034540c042c9000c14141c0e4050703513656052211210044511403030807a42614640103900d920380c0c820809110340582e004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 163617958 1250 163616708 163616711
    0xc0219090606021b0901060c060903110627031207050307090b0a05041401030608120a11160305060f010303080a050c210105190e1f0f030b01050a06030c09060513090906 74
    0x1c0f400c81c0e03002d021490b603130518403d4400400607c142908440048500358000800060f078407441e140070703610f251007100e00368114498a8100000c450b07050038500200000300304c0c402c1541e010080881d642e8041d1180303100b801c607140c40000d600a031050000e5a41b001d810b150401d80c1c240e8440c1219900c0d80240e03103101c00507000040c1400030030040101140d44010070720781008420b1406030300c1d030384440813805440410540010100030302c074810301c9400140403040094a8070340500074001402e20442d40300883c0e040c040c40c00014281240210924105e030341540760417110383d80da40a0400101401030640c010b1a4040c02540c049101200c209030f01282d49d10b4a02805505180420032000c1c1450224003401c121103a00707010400c82d074400700b0b8014501d1440b0007080714981281c1203201010f40c21000c9031000100f0b0000501c10301c800703c1812140251001441a500c68600702c00361107500807124045860f81c58200710240c850001400c10f100c6c86801c3c41005038481c440c01082c0c3e012303410b0071354186 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 163619208 1250 163617958 163617973
    0x3060509130219240c0c06110307080d0e010b01110c0d020607050607030b011107032411070f06050604020a1d03010222050315161805040203070804030f0201050105010c021909060602 80
    0xca03544010440c24256041c1122003c17850f40d1202c5121049014074020405c0502200d05108810800c0d1865550300c0320509464641140f00c4400408110f40d50101ca0b60a00c001c8401c40e5001d400d03c004580001c40140ca22007144400340203081003111003c03a0004400c20102000c58400c1c04218010b440a5501041c0d0f108000001040304201400d1006d0383d81081d031301040015400940003a0038083d1901d9824075086403502c8400030700205542c7c00001000142810800c071014807103400e10340c41080c00f0440b43c0c50b00000c1c00201c2c02040f201502043c210044070b0540214110240c8101d0001000980b5201c0c0c00b890303d407000c00c0806d5000d200b00a84c1c610622040c034040c41a1618000c0c0a411010180b810446440f0061203103082c10080c0042d01da041701d07000054404420103030902410541d902d041580c3d0052014004440550005003480c00c1050924418040c060480d54146d4500d0000c550346e80070041c4481d881100300100c010b041100042a141d035000322002814940c01900b441b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 163620458 1250 163619208 163619249
    0x16200105061e0303040303140405030a0305040e100b1605010b120d021c0212031806010b09130605010e100903050601060f0f0e2b05060103080c010c03060509130219 72
    0x7540c10882c0618480000000e0810264600009803801c503501454161000100301070622102c1c0f190781c00c02c43e00340c042d0a13806424150420001c00468003002021403142c0c1d100b01401c514055140202ca500b080d08005113180c00702c818448641590180000080905030070340003810400f42c2821114103a041118541189601400315490b9551064074401101c94885802510b40021403040111100c020020480c140c034145100207411181350300302d800b5961580940718680e00458241807090641003140d6401c0201e6010301812a007060310b6460306c034035410b010481c0100c0d240001d0710800016250000203d1070407c486030003440f00c1d0300c40381084045080000c1c00c400d088030340e0a00703029543c3d98003003040c3c079200310031030384104003c141c8203148010303400c09071890309020400b6210384a640000300a10003188010b2001590201c002c1004c6004050140c050f140c05104031540108030b400011140c501d6260f1103101c02d48002c24905d8480004a511000308441d034200480b1601c2400b080c4a5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 163621708 1250 163620458 163620469
    0x131505030d08060f04270b250c06110f0301030804050405060307230402071b09060f14040e0a051c12060305030a11190609060605040b01081620010506 66
    0x48181c010700c1c00c4001450f02d000480d5a02070035103245405103035a2450048a044c440c90450000500e641030f4103c408950f00384840d00000580d045902c00b09444880d80840e13081c1041540040350f1178807070000585003078a41c1001450210000c0b04001400c02004c2900e035809401940607501c1862610740f150308100038003040319001013166000c0d50242c001804000480d0910300c05501c0c0d40c5294003e80c1c4035002c0030401034001d20314000e011070f40c084800d00165000d900300300c068640040e01008216504c411031a050320380c1e48100000c00305110b000c402d1605003900002c2e4070000040484640c0b055550f00c075498160101040e611080e03031140703c1c030400e561007076003022106188001884100d0031921025243d2058a040406001d42d242c40790661a03400c0c40505c401d02c006000d00c08038400c06003082005400d03020390441e0220302d844000318080c1341602c240c81c00c503041a1b540001c44d40d164445c9500041c010a05001884104034a000d00301045160b0494682540300c00861a405c00780c00340f02c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 163622958 1250 163621708 163621723
    0x30b070318150f0203091506041a010c0c1502030a080f0f0601080402010207031415180304170109081305030d020f0d0c030c081308060702060c04090b13150503 70
    0x4041504004150305154031400c0c40844035600035200e100c00c1d00c03004000400520f02c07040c2d250b01441c000700400100410100300800c1000b40154040302c542e580804003c12a218004d104a9001881c9190801940320722680e81e03900c0e104400180c142900c1d4000c41c110900c0600310000140e000041302d69540c1d602a6000d50030400e5400c2d420032600300b0540d60300321440c0c001d1503079040010540024041da8030820031400110b400c8034102002c155110035030341c1c40701420000060a240d00401081c0800504003c0850b489400c1340a1401c25040085071104200c003403507550682c0d9212058007011586c1a0f0013402c05080d8a082c2e6804d89207020300b0b050624000816020a54000d0f203e01d180c900b0300414000321642980c6404500903e56243c2514690600c980c00341140300003083d80a0304c00c46010340303881a01c1c2000111801d0b03540c0c9603022a03072481c04441019001005000811103217007580c00440314000010519034944903400c1001040741c20381c3d01507202140303606108112604041c4902c2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 163624208 1250 163622958 163622971
    0x6020705010f0e0d170927060d050a0b0106020109060609020315060c0a0c1d010f0812030a06051c02040507020307080301051e03061501140304150507030605120304030b 74
    0x208041803030600082c00850800c44103100380315952040244030b9507820050742c0043c2c0d200301113210f0149484004203503034200c003862600a0381c40207030002440071101e1010543c3d25036450030303000990b900d4052240004001204030741a2059443c803000203100383d06124083c0c4401d60000030014000e040c0700c0180c0700158030500e0090300c10001d02c0045450040c20008156040c4d031f4043d600c10464003424609801c0d8180904450001040441c3c052001c1e06014012480080d608080780d0b00c0b05205985410305226090055010f1b035428881d0740c62140103598040303c042800540700e41c1d548081407a009d450300384144d206034002d0f00c890451400384182030300840c40e44003c608050450780c1d038120920040c0a1a4030035040a01c4001406a00d0100742000310405429038849050840200f00c3c186404043c80d4082212610141d0289402c4030559104076001503250303207014036108070301c8010003010704807004260f00c0f0040440c4540301c20300560354901c403100c011555185103080903a0f0414002e07012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 163625458 1250 163624208 163624213
    0x403030e070509090d0305071b03080609060a0501050d090302010609090305090a06020601060c1e0c0f03060605090717150a060518061801050f0d050408091002010510210c08070f0602 80
    0x50000361500003e0302d0005e041541800942034850f040141d801c160102e00500352408200001c100705980506c206008400c252072601307094942000b000302326407031801001d00003907003803044005c9806140c01c82e250740c0e8080e000001d519034554060200742c0302010030079000b041c800a132401c9a41004a4500010210791015050742e5042000c024160082da84015018134595802c680380e8220b002d82d0315030841c0e480306104a01c0e903600d00341c50030203914520054039818039010001840303080c070002c401d1140c080d0741d4a07800b10b00b50318a05402c1c5040e01900d40018660041001280e81d1a402240310150816452340d035120450044030400030240514900d01411082c00514261040c032035208031010403d0800640300c841c402e00c40084c5010b1284006040e504040500003030001c91002000c1000080d10098699440c0035000d9080c0c4409940c600d1055600c03600400252100403201e00c0804400c0d0700c0c49103121010344420304a6041d9400c80b030000d8001c1c0c41c0420804a03400b41220040030113001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 163626708 1250 163625458 163625461
    0x1502010504030e01050d02040902030f0103020109080601081f090c03061a0a050a0302210105190c030c0804060e01020c01020304082505030a030b060702040f09030f23210403030e070509 81
    0x400800d04003580203e1418040c000c5121039240740c1540542d80034216001c402c54aa1419905510101000388410b0740803850b8cd52001c60001400702c2c4c0309043c0e40a1100601e200c0d030316022025082002c0300c2141504584d00d0001200280316020004001c50040300049100c00e0f60603c44040301400940151040c1c1c11042e00308180e890701e02c000300c1201d4049600c412a5401408202c06006500529080d2540782c802002a803100d01070081d0941a0020000c120203070000710140d0032125860310510102d01400001030001d01682c00103d1422215400035042a00f01c10b03110f401e981055400300c0c2e00b4440890500b545610140300b141e2010000716040400d12159100d094403441100c80c0345d01050f44941c00d5101c2d0303440d944100c1700c5855000d402001a40001c0d08c1c40b1f0700a180e4024101c00261810fa5811103a511030911350306828005c0b5191b9a003004210b0a80c04164024076512010200c0c452403012141f000140d1548981d000b030b2808906082c3c1d040034141014010340009124020301c40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 163627958 1250 163626708 163626713
    0x1a04030e0f1804080702090112050706030b06031603020c01090303050117010b0112020904110f180f06041716081c0c080301030b070903020618010201150b0304020616020603101502010504 82
    0x1d0a40703005000b0007115051a031550b042140140c8500382c0007a400918810001903803107901c90200286a0080c0c003a1f80d070a546401c022400d0355203507000903a2140d001e0001c01e1070399903c8081e00081c0c0f002800e00519294110080501355902508140c0c0443d9580004201c0010f07a0350001d00826900b030020011071034584c0001c0c0c80c1c00e66200220b0b08050307021a002545484640c0001034168003c021242c44000c05a01028182d000032040250092034581d9140700e0b00388002c440c0a9182d0041145041c14106600320710904074500c09520f00b41700c0c44401441f181c680143c000080c100d2640548908052000a02c0b2405404284001001081c40310013000c25698800d99054a9119110002c591160601144c8a50140d04080c1d8410000201c914020800c00d9004c00324004c00c1e0024000c811a010022382e40b400c240c80759809040c01080004c00515010008001011240b43d55510f18106600403c0403900100c1c0e41071802000365900b402a41d000360854080200541300a105d246440da = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 163629208 1250 163627958 163627969
    0x30c06020706180b030f0a181101030c0e130207050c19030311120403080702010522090605060306150a11010204080610270b010c0f0507170d02030306010c030504031a04030e0f 77
    0x4d100b100d0006d00c40707010500402164000a00c10040d500080c60480c8090030052160502c406805d40031902e0a00d4851509016043c1e61240210003001d08400d0141d02d80940041d510042e4112420b0107502c452145039034988000c010f045034000c0004136554294175000e00342200d0380620b40c134590311400c0c034503102c1d012402c1107078252a80203034555180c00c0b039803006803058001c04d840c0e4040080b5440e03940b0a02c411218a8104640013004203110030703560b070401e0041a200513140550404481207043c900086031358000d010480c80b51620f8842c2082c52264a42240c000e034028800d160050400d0040100e540070081c00640111480d803401d92007000709a039201c400c80301c582c904594807440d508020384e01891107a540f003900001d000e021405146429629100c4c0c50068011401441808607040e8800003a01c68200907941c004520b1916460f005441501c5007140c114100f00c0204404000a0405190300301100c0120500b55214206454040c04500b82d840c2c005001d1a00805150903d80e03e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 163630458 1250 163629208 163629211
    0x501120506010602061003150b03060406090203010b100e0603100302210c01030203070c02040b0312040e0a05010602060603032b0c0201020a020709020f16020a080307080c0c060304110118030c06020706180b03 91
    0x440390302c44002000a0300c0c407000d0300c40540c00701c0d414001c2f80200310600c03217280c00000903a8400c600030001c0050413002c10444000b50000000018031218900c0d00500301036000b16000459115450141666540080d00d0190500c0980032200228400701d064480308100c00c4600302803d007410b41c01c526004000800e41d1840c2c88004c1d220b80d81354004615641c030b043c80403400c213104080c4007607070741d40c0c0f503502c1c40c45881810348000c65000d1411000259892002c00c125002c1d0400401551a01c901402c4006180e2942558581800c1c800030301079581718098420480800791340d070005a01c072034031201d000c0e080034060b50219510354010401541c5005020044845000c03580f81401a0038a060021500c6515031380c010000520000a004d800e0141c100040c00e000d190702002c0f00d030384030a183c06101c120300040d01e000306040a0000c0c0400558012280050f0131011040d009101e0359807034444c026040041e512200158000c01c40522800d0b034080d031411000e506e02050030301c403146030081c0640180f20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 163631708 1250 163630458 163630463
    0x1502160b030f042123090603010b0f041e060305061002030d0f0207050111030f010614270306151009030804050411070c0602060604182001120501120506010602061003 73
    0x3a0710002a081141360078604c501a1340c0d0003c910030304000c40302c01501c0f1000c800ca0403000f0303a895600007010389024000b10707028a00090403a0f411a480c01415600c0364004590446070000103220105240b80301030340c80000009101c150141151070b0860180c103d600c050324171802011200062107900e9000022221000c6c4050750010381a0360001c5064000e001307009005001c0c0d424280e440f1100421900554001d0b1018014600141d80e01c61061710703035880d03000c50280c3c8810140154450000c2e803485400030b18260040144100708507000180c100381d011984d40808000c070207002029401c20140641002406041c48070701281140c4034907810b03000c0c034890b00b1700c11907e6620380c911200c0c141080c1c80010f1703441140054407644801c000382d2105400c4500034011031412500a07100140e4800c0008142c0e0040712500d00c03a584900303250303000c4a03404001810b02a803986143c2103c1400c1c0300e214020040d04440000104040c5441420000103a002004642c850001d101d131184110705003004895 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 163632958 1250 163631708 163631731
    0x90a0201050903010e0a062408150c070b0f010f080a0819020c09040c060f030b0f0409020a080a030c120507050d050306030114010b0a020f210313020a1502160b03 71
    0x3656000003d01516440785e462005001d04421301c0d00308070303450300031120030403100107004440c80802140340441c0300d1758800c508103a4441102069652903041c000382e00b0225649500b4a051f14503150440210400e45954101d808000010040c580044803400041d12070341b4080c1c4018000f1b074403031707000c20b0060b2000c03205002100e40c02e08040d030b4020002c01d0404813003d440c2c2c10706850581000c02d46044a8400c3c3d0b00070907802003501d00510310912802131582801840815080c02041c1400000c0865110490704800800000b048200c0304010912401d4425500c03d41800319600d00140d0000c00030303020000b0300800317100d0315001a0000c255540710600c5807901c01d03103d42c1c8450020380580000010243d882070410004580031110100600803c5480d80844400c400e104003215680c030f0a4202c848540c14087c480c0151960002c0020b680040707484a200900e003a070350700056003000c0344c2c0e440341c580036182c0c81070801c0fa203406000304002d0303511100800d81c25910340070380c0b41c6061000802120b07010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 163634208 1250 163632958 163632967
    0x709050c0f0c0a05011d010e15150d02061c0605060304020f010804081201030f050f0f031c0e0f0109150b01020a03140d1104090f02090a031209030813050f0405090a020105 75
    0xc090420024202c2c44d005002407010f42020036002c8840d00d11075003108515401c00541400c04000058003100d16005590b011031030b5510300c002400d1419035004401e501020340c080107009030741d4110191080100c410902000307250019810400c864465100f203010f0f050904c01c02001d0b035540440348052942c20b09000d00c107030399603252240c00c80c0700703035812103806008000000c000d00814440442250b4414400c850400e02d442401c95903841e102548160a6801003140740000040c241d10360320301e02e501c1f00002c1a040050b05010703080080c4070804a901c0ea555656090034888089032002e4a1614800100041c00b80b000c0000e40b00c8810080140c140210102910740345803020301100ca0900c3c01000030000d40521407103000c1c80f82d0091050f030089508158001d50702030310038421501621401040c109102c0d01c0d40e982c1c108070802220981d030a0010b504000004690700f44000c0c00134a0705150340201e0f060400382000b041140c1c0d07074600b40c00f59242004120035030000180b4400c206409007009902c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 163635458 1250 163634208 163634227
    0xa0c0302240f0403030807021902010e0d020a03050c04051006080106030203100b0d060806150d11240a020d0903020105120402150408030d05010e0403050a11010b04050403020f0709050c0f 82
    0x4228241541c41c1800c00092211815842d4002600550340300b961000025101c0c0042283d40c4c401c1d039a041c2d400c43c0042c503802d4005601500e00045141030280040701141407130b400084403820700f03a1065074035401940c000084c0d07140c00d00c40c0c0d41d4002d00d04007102c00074074241000146050814051017042c1980040485c1c03016200200b40d00041503c019807556035800181d0300740181449100f170308050300c54140403e0b0602e40030903192001d403001801d00030064020b41c6600d408206024442e035045001c0864144a800e4500315410603610201c84c1030799600c03400e000083c0703014180440c030010407119220910060fa4004212484a260860440c1550700c85000203100200640000d078410b49002600061591020000c1d040340003519a0400c8035a80e04c04c1290031074181150000d00140c81004440d00490160b008580c1c0120701c600000390300062000810211507041c2c40c160b026130301c001c0720004010f104110300005000400d07010702031424040c2c108200c0d4000d501090881c2c071801b0680707811 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 163636708 1250 163635458 163635499
    0xc03030712111903020a02090a050903090409060f15030b070228140d0f1205060f0603041a010e0406050a060609060509041b031506050702090402060309010e120a110a0c0302 76
    0x20841020483c0346610041460065074611540e08104d00031010140003401e2604188101071050300e2120240d45001d2410f802c1000500c1c24000c01c82d00345030340707a0594128820a10a03c042410b141024201103803e60500c4111218000d00d107200315444180c615078801644820240384443c100b40c2c0c15068003d900d0002c0d503600c01003802e5441441016034005d4500e90003c035200b00c4010541b5a2117924080031401c0d41912011540c05801c42c0420100388000d007020001907074054060083c41482050000b816010180c0070391003100d903580c0c400284014085944102a0458510321041040505c1c1034000341c0707400403a10034081400400314540c0f07400e4a50741c01003500d124032100717007014095140401400030710018a00090b082c0103402c3c04110240107900702d4040c04c0c0c00400c058103d9030307542c0c2000300c15807006003000f4195403161981400c41e04108002081c4510340c00700b442c0c1760100304000424403508020300010540c0560192808240400c0e200c2c03003526010b503440320201500260302503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 163637958 1250 163636708 163636723
    0x2010f0c0203010507050307031a15090d050106030b07031103060a050907091a0a170c0412140a052b0c0b04170403120e0603071b0510020a0309050c0303071211 70
    0xb5010f50a040c00c2082c1e00d580107005521482d11030314100502401c1b101a420301c241011459a040100d000036101000141809041160401825990390661030380c0c0703a60940c0c02a41c0111101c0c4aa00d003032101464042c010307007152802c08c240c0c0a00f03606d080d10000301c2da01e8040c41058001c103090300104001da8400c030369050160100002801072000301d40d80c0424180d109042100c0040c003500801d034002404003c2c1e060164440c0c0445904041c20030506600c0030000220407118a407081c19080119481032103640312581c042c42c090024550305201203c0c8800c81ea55078000c5542e041d020312200260003c8403000351a8019001c070110340e465240a03001c60b101001d2120080e50081030010410110b8103117003040700c000341d880c052184804002d011541c001500c0b2a400b0440348880807482c032100001503a1000d02820403038010b4102910660100d0303020f0141c410006c2d1300e8080d5041808000c019540a940090340298074101c01912840c031000b50342c64100c07041102028000340455820070165 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 163639208 1250 163637958 163637963
    0x51219032006010317040e07080a15030302010b0114130e06030705180a0e0118023102070203070803071101050a110601091a010207140f010201110409050402130b03070302010f0c 78
    0x51a00303030400c61040d070ba941000d21089545c030008103030328107801d0b1801c815942140d0411400f1506610341d01015100d00000801c2d101d150740c2d81c0c804146010f0003161100d00210b00903000020002501000101041218007200780c0d42c4d801042401e40d1480725201a1003202c84803040c0412a0700c600001905100c0d043e801117500030364035221040300b4192031000500031007403054100008090380906a098a104a042e02c034000c1d080c41030380c80941843d05280b03010401d60704406a410552100170b820810580054122565004c94140c045040c01c016201c06070025000031741c03d051103a44d90040c003000c40000c0c03604108005c50569801401a1080115190b90100780ca6056031940e00e288028502043c44426070700f9202c200714800e5001280d0035058515004048291115440c180b0116a03d0040024110340d070b07600048806440c080054809000500702c04946810b00340104154102602d8005010503e0b014032102940d90005281e000c60303a0a0074100040f0303030f10360b105036501c0c003062101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 163640458 1250 163639208 163639247
    0x90305040506040608010e0702060708041e0b10170a0809060c030c120a0f031401061817150f07080604050705070510060501140403020120030c0307080408060105121903 74
    0x10035025082848170781a43d41c0c441c40d220301581c3d800e000301d80e246816524003000c64100c40100380460016504c4e44001001c2c502480a61480d07a40c546880e80ca0480e807140c2004070501c0184001a03c0c6c1c0007480d040750b0301d03c1c0201001c0751b503510780c2e41b4a031181000e19032260400203034525110006005940880640005441074554840c100c1440c6900440040000a45124601c2c0000c0c1c086e104140c0f9007102136481d8a0380c2ea083c5032046e07a8149180c01e1454414946075000130b1042c40c1d9010038802d48400c2c402034100b02200d01e0301c01008031000b900d2030500e00c00f00c0b410441200c0d0712003013255200901f214041601e40700e42000342d5851080800103005805a444800c44517140790b0800800c0750000e0b80c901c50040816049a043d6010714040280010024100e4160750701c648018040781032040000d59240c80541404145544d000344011902e0314004542005022004d01800b0f00403c4161b41210440c15842c148a8456081e4981610006082c24044e018107108400b00510411501038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 163641708 1250 163640458 163640467
    0x2120306040902010306051e19082508010c05130b030f07050a0306030803010b120f131b0b120a060f050f0d03022509050105040c0503221a01170a0201080a090305040506 74
    0x96490f58908c5049414001e40c1c030007662824003099000140b080360004009402c25410a10680140400b8091340090b01c014100020070095020b100b07810781d104981d00d407a82d481405450b24a10304a056008180c003a0080c030030000c84c103d140400b107502808a260075980d40c201c40409800030001a000a071031040003000214516003464001c0040c10801711441103559211441820181c008407242900030400c05a0780002507000c4200143d030904405501081a49405c2d8807502078210b1101904101c003024240b0800d54100d102c0c0381c001d80703035502e8540d0241d03003840042900d4905003c43c841c084c0c62464420018184284082e009918505060a880404819000f07580400034000c45035000d140500004441c03905100300c400c909110b454245c151f55074850030310aa552020520030b060325107003140360009081441c801040d6031071005084200c0d41410a4038203000310b008020001c03603000300301a00160703801c4412540d000c10402c0001c6194101c0f8034048035107000300e51000d43c20650105 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 163642958 1250 163641708 163641739
    0x1020a0f0515070e012d03180210020105061f0e0607081b0c100305010e0f040213050408070611092805060c011a0109030b041217180c010212030604090201030605 71
    0x11390401d80c24600742d0341c3c4045603e129a0207454040039400042c040c1d41d40c3d900d181c21080c080d4000c40f200034480640c0c45144041500072510207590044d410005035035407000c00c4414642207001a18102030f030710311035205d401511005042c1c80c00040484d4803030389002c40c0c500100a0814112104010202424a280083e12810360355601c45900140e110344c3d030560408c0091352291080c58100c0d803064005041c42c0d100c40021a22121003c0c0060380c001d840070b6401c510070080c1d405068002d42c1f01e0203200355a42d4003420880b003103500c54051120150030401c80780442d6a5a0340c0d040e0120f5403480c046500c10b82002030501c20704000d0703a0003240c01c4140810001e04100042d4000b075000c0801c100381c085d5078a4070100445c0c940500b804004c02e50900380010602080500351742641e00340b41070400159000907450350f5800f8560498000c021030700d00011040b0030400900010f032001000b800203105001d4143e01410403400010f00f00d0b03014075aa0840d034425603204e07401410003860042e05030700f506400d10 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 163644208 1250 163642958 163642967
    0x903160306052206020f0c0313080607030b01020606040e0106120b090d0219170708030405011b030c020d0c0c0e0115031a0913020409020a0f030b090601030201020a0f051507 76
    0x1031005a0340350745844005110050201c00d01c01161001c040380645825040d5180300003034000c2c450024040c00280100042c8080410040c00d480c40c0d000030040e0307024680140240381c004010228804c150401d100540980d80020304240c20980880c0d010540c42001c0c20500e005180e5548000d203424a6907140d4000e201040040b2809800c01409541100902150030f9035501e14803107071451280215224013010901c90004012040400c0700d002e440c1c5603042c0c56180322904160f4041c1c840340d558041d054076420484038190402005400d0030310049401b050041d45a110500303010f000e020140031550200151301c100880900800e01d1003184550312905800b00d0345406a00b54004a840c1170b820900783c0441365134502002000074540482d5030340306d004400700501500012a00039807139151007070043e41c0f240c0c42d050246c4611683c00031954958100b5818100011b000c010040c0c001c0001400980d9011600840701600912040110151407901d01e1a040d6107a4059100003111401c0c011115840b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 163645458 1250 163644208 163644253
    0x524060a0504410a090e030306101101090c14010e0a050f030705040c0e0a0b070f14010b04091103070608060a03170d020429132601020f0d18051b04020903 68
    0x113580040746035448900010840d401c403200d00017540e0042c0001102840c0c070074000e00c3c0698031807520805058104c0551400d5401c0c5803811240040c040708140190001c140c0d00b009144000d1816044140801c000b25501030030130f0284a0041c03040c400184401e450800c031460040001500c208011800040010a82402d140156100c3da98a0f40c0003e00e41d14040255182d50340c1001e00c03441c02800c0c940da40707420030810b407a0001c411354030341007514070703c1e55140f18071400d440c005c001d544005240c0da0201410105942c002c0b406006070f032000c7c021a51141c04006d0281c030362100c183d0126810500d040304640c068100c80443c1203000040c041014107949140304100d035504409182b00c812201c0384200300380108840d240f0100b500080810803404200d60400f000c20505c071101350098500260f05080e0b0303202c0c01c1002000613001460b140c01103810b12858001d5041d9080c1400b0815040d0388550b191203132048445e000c19480ca8030100a50388545c1102d905031401012134030201030000c03c441c840002c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 163646708 1250 163645458 163645589
    0x909060b011e0804020f120109060506010507030914031509010605040612020d0308360f0d08010605070c0509040b070e030c0a0303051c0524060a0504 66
    0x18035022000c0d55000d120400d290040d5035200e95107420304410300b103a0071140200140d03400100c074420b402c4240c60301c41b55400c0310481407002150404150400005844003d020b490400c4001c00542c0040380c0d201d444041520001003030f060780e04040100083c0f400d5002429501d11822038000e000d43d000055004400b11101510140685030b91081c500703180300851840070790014607100824000074800c001c04c40e03102202a9201600760091480001c5044614240150021a010500080440800c00005014400c00040c0703010201c00200910201041c812078003071040102e4a00f0400070710303000d03a2020b480c3c0540030341c40600d460704103c22241000d41d48280070810845100b03030903003004510305083c924080c003102c011516556007196141d220f031a0b01d804080514280703200044160003400c2c010318043e8130a86034841e00000708040302d200442e1092098504011035041c0d241c1080959044642c14040134102401c85003041450f001e5404900290a01180701c0b1417489000525020b010f06 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 163647958 1250 163646708 163646711
    0x1060b0f071e02060f0310091e1401030221010f140403120b06090d0f0f140f0115060e04020c0a060f1526030c0703151a280305030301090906 62
    0x11014070b070460701c902e50360401035000380d030400c01e032824045101c00030340e00700c4003c2c4000300c03909540d02d00030002c8030398042ca00110752140d585062032034901401400340d5500000b900080ca5451940052035095041e91007291019400c0c4400d00000002c1d0300001d40c2c1800d42c0c10900c02401d100094502c640c1d000c407000c801003840000340d0310b61503e01d8441c190f8048005031500e032a1a21240c10004010308801d0115040c42c00d050800000500018014044a116140c14078460121011040c100b03150a440009560b140450b03200c01c59520f455014100c4a1a0814070f00072030122004c90081e201e04100b0000302d202c0c40d00468100b000d00e601c94400c1c0018404108044030f45451207244034203040c400d0000d01c3d41c040800c62070900d01400340b6000a02803a00b241d1038984d910070f0550800056920695195240c6014200c0100d0107000d141a002c062800c0e0710200e40340740c2c0010343e40d00c000f81d00744a03403001c0c0400c486040c000301030341c20000f80d50403a04490f180d6964034400c0002d01480c0030700301d600342e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 163649208 1250 163647958 163647983
    0x23070f0f020307050c040f1509020901020609060702060604050c070203011d190201080417070506010902030f1509130201180b070c0e07080c03040f0f0b0406140c040b0c01060b0f07 79
    0xe44044195000c0c3c03607019000d4030520300d50a0802c8054090000c001c28220740d241c414003c030038940d0350964020100d0510240e2510b03803030340029042c150020b0540c1004c4d0000303c20001040d40c04600154800700480740010191103202817103000e03004800c0c00030b402d07601e450100d426080b0b8111070518032003542c2d000c590305248005103d000001088100030b011955501c04500003401c900b0043d040c4580342280c050401036a42c032a40d140c0202a03010000c0c007540001400340226880903442c0e4004804031020600c0701042c0046402000c1c01400c24801c440181005000c5a108544000c50b01c0740d41c00c0702000e040d4032000081010790004200711101c0140300b400040c111001110343d0f00c40d2125407030383e50066962010070b18a50380020070032a0b45860701c24080c0001b410b40215100b4060040c10451854907042c82d00c0011030301480348440c008070070780c0100511800014112400e0320025000b0a40300c840c0e141c100380c050001c5400c40c91860b8004a100300c00d01c500e04001d004031500854a00805 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 163650458 1250 163649208 163649237
    0x9010b0312070b1b070f110108130303051f06090501020f071a030403050d0903031d060c0a030b1903030203030412080709050d0f05010c091805010e060423070f 70
    0x150a00055803a001c0c20090040c0b0010405540407140d1007a01080c6071007918007860310b140340f103602010048a14808050541c0e0a01c000e8000030b1002c10002e0030104403504103001d00f07035022500c440c402000c054460001a4848140301c0c00c59000c4108405469003164481030050401c002078010240107100f02d07562100c0e000d03000a03020b4100d5840710320300c44920207139038072254499100034829002d124007003004880000f0780303100e2106028000e5400294400700c5440082000c129102e8142c0b450f070114007800a4606030718111034144a450a0000311442118041805250140310a040341000154000705050f0040300440c071840c0b0983d80d00c83c83d42000b400a8641480540d001030000e4124103091002d810080c40b038000c00b03401041c146040006e260303211170a4444c174140381070000e007079508100078004843ca40d00c074511402803400c1c04a581000000d844480001340250f00c90b54840002004070700d40003540001c04007a04205420a1620400240101c11050600800a1581c0410407075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 163651708 1250 163650458 163650463
    0x70227090f03192303010303080105010801121505060a0302030a05011d07081902010c080a0f0f02030a270510030213060903080a030e030d0f090b0108150a0e0a02120609010b03 77
    0xc0c00502103d003141d1207108008200c4158034040300425503040c4000105190310743c000b0185000314400d40c1c0c0e01001e581403200040c500a0180e0200443c01800034076000020100c06a41401000b0100001040e0303446800140540303269500294140c0260038440d0103210040d0407040c180c4400f0940c0c0c24042e150b80703050030b554401d0740c03180c410b441d00305884080340541800300050b00f0500515201501902ca510f40d030000740e218a006401250701103024480c1e4035049281c102c4011080d0010310300303003031103507c001d44043d0081c42107100481040a89458000762080440064140074090103071106001001800a521400e801030b82003601c084001545846611550107803940403850500b040c140080660140440480c211614082070200e2604032040b4403852030b4101000c030300450300c0c0030b69007010b01001c50b06030065076294001d500150403a10144200036007000c0c084d03400240004403100c11500b008400c1200030761000ba40c030b410701c2482e0b0000603046d001c0c50f0040300801609262a08260b03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 163652958 1250 163651708 163651717
    0xf0c03040203100203090c04020301060305090f031e03100902040e011706070906050903010617030d11090904023708011505090c07060b13150906030203070506070227090f03 76
    0xd40c1a44001095002c3d80750303640182d0741206522080755040100c440014040c2d8000360811800650340f1400c1001c000b400300501d451300300400c0c020b1482c14110101c07605840e00c4400312400c0b11880000131418800560f01a440103100d0648210349071902e9003c04401c40400b8452540400e4100181100540c0081030340c50040c4002c1d180c020402d03280003410380b81d681004020580c555078070307080025aa0a030034000d165103681580915541c0480948800441e06000300c0c00031f03818010300803002c142c1c5030082c202c6c0d00103804a95000001c4141c003c07440c00280c3c0041c12441c0501018120520981c2d030f42040e0b0113480e001ba00900805540e8400314582244500c2402d41c001c0c406408100d00350748403002401502e0284002080481e201c4010803180111380c10360800d2155188090404910841c541101425108009100c80743c40c3d0b4000964801e40c41c000ca520400002803002d0456549041c80d0300321070400a032804c1d1014101c003407201e8500f400c4905c07010368021140c60a040003008000c59 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 163654208 1250 163652958 163652963
    0x26030f0c120c0703030e060909070e130b030c060306030f030a0306061b0c03021e0901030b0405151b0307120510030312090c030f03050c160906050607030503040605090313060203030f0c0304 83
    0x240f160500d180c60484001d4420710f1700640101c0108911500c0da191410b10b2482545076484582c207050011040c005103000c1c0d00710a4010038a400f0300c80c40c441c3d4021a4205c8440700488083c5d07125141c0340002420b000400103400182c3c4000940c2c20212a05a00410215000703529022a96140450b50310303054084040c005080351b07103200c014001450541c2800c0c2940d000c8050300d00e20f0340c3e41c41e00031818840302a0000c0d1203070800c0100708020020200420082c94040c115841c00390b05002717440c2520284008041ca2424401000080d0700e14442d4800c1207200e88003540a208902b40b000342d03070080b8542800268000342c40b200040351084038a000d140c80ca1a401191803002038910f440709648034403640b0003141000000c00c010400d0301410020152011a1003030302942035490040307c4800c440d015484070b40500c6c4c082c000c28004c240c0260a62358483d03004507010455641d451b040368294494080044044503600134041805a40040510720980d10000b0840e4a9110703450252400d00048400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 163655458 1250 163654208 163654213
    0x150105011d091015030213050a0b1e0904050412030509032b060305120d0e012007060608030c030a021e0c010f020307060504080c0606150426030f0c120c 67
    0x850209003002e801899100482c1c181c10580c042d00c400103441030700c0c3d101c9621300000e5008643c1190a0b00460800d100900702194501c11041c6840e05d00f00840c000c8808c11050340118900300a5010349445c100c410030301c40107004206503d090b10b40b001e1300a0080c894100000d00e48400110303004400803c640070020505124400c024000314031806910506061103402074072804d0010000b8001c00504004005000020f504d9059a24800040341c00c65000000d01c1d84c10031581c60529000000140d07440e2160400f95503840e0403a0500c100581407950061a0700c0c0310003d00f81c0303181d0402102510040c00c0c030780d0a0314a80c0d10610001164103030740c4c00f0000c10b5034000c0080c14140d50f0003043d0301c880c1c03a4000c4c01501d0070800e042d100c21007240d00440b0261034150000802403203200c0305001c243c6c0c2c000701c12505003003007100700010210f681c0034074042d00440071042e0038142401038400c294081c840245001300c940c0d58001d1174400300c00c0d8100403943c140601c00d05e030003002828410400e403135981059000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 163656708 1250 163655458 163655507
    0x12070f091a13031208061302040506030105062503020d02100b0303030a051e130c0e0f0105040509010f05040609060605180a0b060c1c12090c0510030b030f15010501 72
    0x344101654000000e080003285402d0000000440000c0210a145420b49403142c5600d400814840030b51005030b1001c8003d44100300030b100981d07460082d203041d0b0310300f5a1202c0c2c550404001020340c000c0d44045100c0747c0c8100205440401d50300254200c04081d640c0e081e40c1a4408558404013542d076113006441e4141c200b4400614101401d41c81070340e01000c0b084004462555460840406a034113607011405001104121000c1c84419039215005010003008c1c100c1c1843c1c4031480b080d0080041c02303520710070354844000c20b086200942103041c0004550104003c01e0410b480d001c40200b443c0607041f5802814800c0004103407901111141e10820303641800c8800d965015022030060240c200c141d940b0180500ca441000c003000c1041c40d0b002d0103816800c8151480240002d803c407500030b8105900c2e503081600c00070015000b1001402160f60036680310ba400c60a04106030003402d950342ca89a0588035142481108000c0040c580c02c0c0a0310070010b600712641c0725401101e0b1702c480600071b03050a031081074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 163657958 1250 163656708 163656749
    0x30311070b09040506040207021908060f1311011404060e10020c03030a030903020715050c070902271503100303030b011718100c0906030629070804080312070f09 71
    0x4001680c0517000600c018544407940d40041c401302540181d90407800308079082070212140c00c10040d500800b420040b0411850801e0700d048064021900007007500c00e040b02400c48a034010581c500c1000340250a003500c4a85403c00241104804080d0502c80d14800200442c21800854030700100c0102a01079840c0c04501441a00a0241c54a045003148500040099401d05d402d010040c0c0440c995030355613660960201e41440d000c519000040c24920412815040070f514007550403010118a03008902910b030a0f00185e448007041902580c40300000040000580d080081c000c2524841d4504000b07450243c001103d1102c45400710305030a0007540b0105c1c044450685460781e0000840049800300c050080305c0d1800c1c2c80717100000f20003240910314240700300c9415000c2c681c0031380501e000c940d1418031200c8000515a0800401c3c82645c10001240781c2804030040440c0c001c0c03d481d000302c0c4c0c1c0e0341021f02000020f52600300d4202c8001124080c00003c040d11901e4a9001c50306000c00c202050394054 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 163659208 1250 163657958 163657961
    0x307030f050c13020703030c020601050f1003060b03011401020d050711040f0f0c0203030130030509060d0e06010609051818011409010e070e090d03050606070203010f06030311070b0904 81
    0x42040c0c40c00d00c01c00d031841c0d1150f503842c80301a1800da051280543c441e0341c145000340a6994006944040d07401141c0103000381e84401c1098250a501194090909000100c083e001015183c104a48410001001107070100046190108691003a82114180721440704125802c1c00391200050020403020100c844525150704480307a40b10403d080064005444103806080721503a00310000907800201c0100301250058402903900c4840752403228580c56182c0c3ea102c10030516600080904c0004a244000d82e11182c003524469809584204518a0030440c034030303500c01c0300b4807443c0001544c00c940071900d030403c030b100041d41c8400000103110b50740701d01c24071410181001d00608069980c07075920503010800e1159043c02522400300010f011000070f09090708041c841d4010201405943c0c00b880130351400000c924900480910700080d15841c0c400005007184901c07a0040c1d415806c180717440c40c13016000d92106045900c1303074540311900508601c18079150744842c801c003102e03100300b4000e50107141442e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 163660458 1250 163659208 163659233
    0xb0901050f0d09060905120c120307091a040816080a06090503090406030c030b010b0c03030708070c0c03140601091107030503040206040504141b161410020309031e0306030703 77
    0x104007041e0814501180c0d031011504003c000355030490302c0e40d080409000342881000c902200c001c2c3c80914003185004140e54542c1c5d43d000b0b01142c0000040001e46013845000000050601c04180103e4a0101032004425400a000302c20490144240b895980950503103600d0441d9800c80c0503113050f40c82c1c0c1c0c64074001400e80d610b0036102c9000c00c0040204503a01d510983c0301031340c851030100351064190b0401d48c64000c0140c0103a00c3c0c000d0b080040b40714005001090b03d41c0030845240c08409580c9580741110f84814001c0020400359413036801004020740403110710400040101110b20503030783e9a2820301510f400800e4001c0601041081c040881e118200660b03105001030a8117250a94540200c1e00700c03030800e011100098044418800c00506100b400c3e6819880b40c01100d04208580782c10781c0c5000c4404c41c0040554082103241002050240181100e5915091003192685800742c03065449038440050b80e02201fa40d2003003401000e202070709030b0f070007103c000c1c1c003c245803819a516007122004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 163661708 1250 163660458 163660477
    0x5061017100b0307020f1005150613120602070201030b010f050a0516050a030f09090b06030a0903020a150501180e07060f110106180501080f060f1f0f08160b090105 72
    0x14100d40403403000342690045000b03801e650300030300b04100c032142001e007408924440441c7c140d0525080c041c40802d802602e06901000b251b0300e40e6500b44a21a40c0b103442101da0049901d42c80d210b400a0520a1907409020000c0c005c0e20103200341d18005004581e40e030015119600420340a01031407410a12400c06071803010411302d03140c1c28112040d00c5052905071843c4003100024104d40c4080301003603100c0300d00740003400f01a80501103a00030500003101c03030000520380b00c034044c0c0c1c0f4042c50301818800c003d0325140c6904840c540c0190540079100c8005401c09001d90f00d040b9107450b40c8144082d03900c0c440c403444503031a9001f40c00303018207104044400c00701c0d070703400d41c4104140c448042c02c03440000c0c03081c00300810300c104001039000032a06200c0d09842c0140c0c02004181c0007402283e0807080041003003076103c2d50036100104a662034030b20940450041c00110803264030420404269030064000400c16182c0100c115140c00c1c601d03c41c2c404c22440107001d1110020024802c841c411b500030f402400d100740c13 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 163662958 1250 163661708 163661731
    0x70503090a06180c09060f0e090714010306090203090d0f1103090d030915080601030b0105040e1612091103100209031e120c011a1509060f0705010e03070605061017 72
    0x8681c85044c2c4c1c60110384c2050282c5560361b0802c2040094008040c0c0040007810710710360036444c1000181d52034605521441140d0712403010b1699044c0c0c440c0d400700c0d001d420f86540440d00c80c10103190720740d600c0c81859284000308590540c0320a1090060f070342d410300002c0c2c2000542c81d00254500748490414034001c22002e0000c3d400c004500c0c03c0042c403525140da04582c3d1104190303d0000001002e40381850410742c14000d00704000d102c244810941940d0000343d0f0085040340501400c4101c400e01c4d000122010141e140c1002c8004000304c01d0484850948118210342074034080424440480c414000c140c0c0d41070b80f10986248000c0d00d45208800240341e440e050781e0154900403240c0481d07034000307048091540d40d01c0b0001000b424824060075007440040d1800810681e44170241e24040c8280d041c2144940e1010801540781c0c10103000721858270398008000c0c420300202007d881d54a030448041195164104000115070b420916040d04c111046640c5144036025103501c00644010090035011000307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 163664208 1250 163662958 163663001
    0x2160315020c0607121401050603010b0a090503010f14010504153b07020d090b031803070602071112010e06060f0607060903020f1005090c013014070503090a06 70
    0x304080c0f1030385205403e103480f1030004e08918040c24088907081007800c40c00309960801880540c440038107036810b41c1c200707201c4981c1d9100b41d50f900fa036241499612031507040d030900540c40003258850b0031407400702050008000d05030f62680c04206c1a00c40c080b20000d102d07004200200721034801e8078070048640c8118110003c24410340751050300000024010180008030110078015080e50400020258448070310340181d00700c3c00c01704149000c0c480946410041110040f08110422050040b80c80d9268402011940d814407894400c4424212410b45486461a440e01104091040c01440c2284003e503019100c940d485800b000403140000b48401d400072020f100d1140010740720710400241c10701035001801a8410803a145242c05803801300cac461a50f04220a1180d0300030009001c02d02c1c0c60b82405d0142c40c0030407483d424514551803208440c07215510090340c40c507850307155101c038400c12049031599510b940c4aa0040d00d080c407058541403541c0d440550594046007081e80540c0004001d2021081ca8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 163665458 1250 163664208 163664227
    0x30a080918100e0a020a080103060b060c0f060a111305040510090c09140a0608010b0a030e1501090f050915060a09020409020d06120c12110a090218010216031502 71
    0x101002220104504070141c101805050343d11410640c0c000c00350003095143c240901001844a6010b1200500c0c09440b480e68440d240d0b103580c00c0d00c4002d41c210040700c2e9900788051206941300710076a00208a6840e1032002e840100780310044440e0780341404242e80d841840c200610004110041c42c0303440318503203a0408546400207005201104400d81d03601c006950502520080c1d06100400a601c00e5681030400c100c1c1c15005044941185d60400c201521012625000d4001d04038112020a42d80542c030010550034070b04482c140d0503078070051410450240c526240d00d04680c402c2d5042e00301c65001d114003000b840180d0340110341c4100094080754a082d61061784031b06982107a0040441507801040281011040d40300e0700004000e1104541c0301044a0f88038500c0d0f5013018003500b01381ea2881d00e850b1043c05046444a5007003c0054541146075548207280c000035084540d503142e54100d600103180441d031000401d4590284440600d6900704d00d9036a41c11080490550205050f94090060300f00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 163666708 1250 163665458 163665499
    0x204030816150e0a141501030c06080a0203100b0306040b030d021f0501050d0b0a0603051605031c0e012001020f1b070b09040903030b0a15120605030a0809 68
    0x141c8250007800749550003824941091040750341c94202e07800320b15024004403110800901e0030b48442c0c01c1000703034500b85030b05100e81c1d044c03c0f035200c05115281c41402c000010404601e074518201d6842e136982b04225110004040260b10051b01c1e1026440300542d8248000d004020040d500300c44018400141189480c1c0803a0600d2007012080c009a08503030310274201c008a0484210407011076050801482d0705280004058400d03850b000b03001084080001164059658800742c061a0040d04641d40e42e80c5d9000b10154074010b82c0100c6000e40180d402000c1003142210003214484516203d0031801d0000c44011901034500d10701c900e415880320802c40d01049401c4c40240190f4002804003a6540a01c0345200c0040740401e620045991155500304003c007207040039142640ca04442c0820f041c540f50504401505050030b03507035400080d04c800040d449000e0381c003903005c55416888842030010300d8003103c42100c1c8140f04044d059000340c41c0410001d001c2d03100504000e00001c1241c01140321640c1200d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 163667958 1250 163666708 163666717
    0xa08010c09061d1e03010b01021c030c1b080a0e09060a05010e0402070813031202070f051c02031902030c040c09090504170409140a020a051b0f1510050f0312030a02040308 75
    0x258091140c1c0c0c02007a04e42805c0c001c201d0801e2081c0014002c0300715106180340c2c0030192006104c10903a9a4202410303c81c4150742c04074604510030b0952040c0005810b0004d819840005c42c0e0000c01c040d41100180d50030300c40e80440c405ca9001f442903162138540703001500c619030350807609a07002d42c3c05c0103030100165030304d0090014215015990940c1034114901680c035103034405010019980801000c200785031a50299509543d015a20600500c0c101143c40b090050203500c0254540203d00b242481c03010040d003944580b40c021022144c00d42042000c4c4400c4030b605101490000701e1100b8188500d454075081507801c11302c1454079441d8124002c1c41304c907203078001b030300500501038031001008000040e02420309d8000c40288021490003003290300190040c440d018001501c0c0403c0c84102494010610880035900c1d600016241c070302d00d0300344080c0903620040b50a20341100c0b80305e401182600b444410b6804401000c0c004007200e14042d15500fa030760b0402400498400d40810000c0000380d511000342 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 163669064 1106 163667958 163667989
    0x10201020705190c1a0a0e0405060d11030a0b0c0307020d020309060412110604060c0b0a05010e0c07140703120201050a1a0d020402040f030b060a08010c09061d 70
    0x16200644c1c076038841c0b1021203d96805201100210001b060600030990740c0f400c202c2041400c200845105075030103500302c2c506840c00000035900c642c81c01100ea400030201c810900460b076849180d07107012951618040c5010050082140d01001111300c404400d00180d07007807103881804241240541d100e03064042c10f04031a140d09000d850751246002c90b1020741666a50780d00c803a0090400f900541c802c0302c40e40206400105013078110303c00c840c16650250b8004a068075001c50b00d20f066040000e0940706030f18510700704402c0c140c1c10043c5000031446040400c010409140d4040d0864200a084540359030a0140484a40841c5c10008144260494894444011900108000340183e40000c0781c0c61503480c134003000b4030003041520352080e4021102c240183e0b85480b00c10f401d8a989007105d00101d10300460501200740264800a0a880303460a04c90581c80341c000003441505564049 = true := by decide +kernel

theorem cover : BRFrame.Cov 163489208 163669064 := by
  have h0 := BRFrame.cov_init 163489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 163489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 163489208 ≤ n) (h2 : n < 163669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
