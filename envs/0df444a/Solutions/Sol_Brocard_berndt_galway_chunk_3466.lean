-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3466
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:44:21.138847+00:00
-- url     : https://prove2.me/submissions/007b58be-7a2a-4d6b-a992-2691d84a5fab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 623201438 ≤ n < 623381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 623202688 1250 623201438 623201479
    0x705220b0901030c060f051902070807080102040609180b090405010608150606071211010216170918040314070b060f030f100506040905010e0607170c0307030b0a091505 74
    0x3400001c00d00340b072024045c08401d010381e02440020f6414030f00345243c00c0c15142040400c16914121401690200d1030600c0b20b00d00500490006c1d14034a4002c5060030725001d001002c6004510440510003021220300f0b545102030b0700400890000a042240242000d01e0314600030000d40c842c2c0c106900819a40500c040580d041d494080c080051402e42085c00a072655800c9101600301601407184080081d4600c010070f0014220701c054405c1d080a90310002d05214101040407031100c48603400170401e0101d0381d81c40282e0b915642818150618032a0b459241c00d481096090854808500000c07c00c80104810111500c0c462031060302d08071801080344e800e050391107110710410b19040d04450550f500201325640b00d00d07881900200045201100c503203800d82116a030311303034115454000b94100039903160019080c0703a0120f10005100c41a15117541850003601018000008160300c900400c41d00340d4481220101600c050b20b4100800d84c100c1405481c090054404c5078000c0d00c006802ca0b603a00c460 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 623203938 1250 623202688 623202691
    0x20304060806090a090c061d0402040506040315090b01030f0203100e030301061b12092c071d031f0b0405041e020a090c02030a200a02120705220b09 65
    0x60715404800e464810400840c11801031aa01101d43d80b61120b00114684040c44c100408203170701c480e0703410020380b441d1403500700390152100d0059004000421840e19440101c804803600547d1400480300201840c3d00038060f03040024060480790340c00071051041c1c42225145071031007101102c020791280b81c88501a510303d07042420f42c6400c00c0c40100400c034021040314100030444044c4c680e5140d5030360303210000d0102c004400000140a990140080405155400200052401a40e03400114040111b12584005241c001044415895824066214040c04140031401000d58101a06c40c0e2079000600f00c1d0309400748522800c180d41001c0508103407050500440d0401d5821700076510781c401305450b0100e00101260404040000000c41041a10840c40040b0403940959580e6004500040c4140982000d0800f15016212440f0845a000400b0305249506546800f508040344c0b0905051115660103582c1041449240c1c95070a200c400d05445070058121081141d07d1440c000d200d400c050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 623205188 1250 623203938 623203949
    0x41e0812060d030903140a020d06020304020907021911120f0f061308030109020f0f0307030506010e04291311091201110304110a050a0e0a061401020c04020c01151d0106020304 77
    0x13220802807000c5803100725080780e01b1905e202215546045603010851400c8a05000c0d1072041d4040207000443c9408650181c004540e40300802840c01e03a003118907403000e03074010010302d0326241d403007094080c0d26002e0f8810140c0154000ba40d041c41d50042c0540e4072891050650044d0340642c8000501001c0009104200707550800d80315800d50f0301301014507000754011540000e58907003e204040501e049803000b14443c0f100344e1380101c0c0604001e0005130500580104c01c0b071281d424040c000c0382e00356000031100000e20192102c104480c2d1088082492051700658247c440d5090250300c40c10354a50400500301007900391000c8805c0d90503150414200c0311403c5611035801e00820104000c00d07102a400e50241c0001400703619515500c4001800706101a4840b01d922840b401c10844101d03248d00c5100001c009a03181e88219207400d2000030745030501310fa5021720481c0c0c0481d08241302c0c07000350b01481c4803400900d00d00e10b070300340c8a60900c01240046c40304686600210f400110701c1610200540d0101d84 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 623206438 1250 623205188 623205197
    0x50a0f03120c050a150207050f03030c0a1404030b090a031218061d03030718082b030b090f010305010b040c08070f2a051603080703030f0f050c3609041e0812060d03 72
    0x10520404880640e053b09010392920b0040c4800300100760750440d0705001d50f0b042e20043c05003550910300070b0040620020804d6030f481c582a0f01e04074142c0c0d608103086590b584443d002580252220003403035a40d1580078156014440402007100311600285542120000e4420381c811259a6030101a55195030018040000c0c0f20701058586ea9103021440c00d0382e14020342000f050404141c4042031000108944801c4001c1180300100706002d1f0a10950102c90019a024000155100c0700540106e00180811040003258000034860900c5a19039415102221059441d41031414016442c115509802a50705000f010400000d0b600d10f03019990460390300c04100d0b4101a51920150000d04480145444040e1200c503500f0048181d4171845100d070b61907804c50341d25021504410040c00581481804400d10700741074146088132045c0800280e89800c84800c0c80c540d84070f1502e640c2c0c0e14030690543c991400d86020000412500c4c1c1c0140c810365040040c1d0148550b101000c0198100000b9405000304 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 623207688 1250 623206438 623206447
    0x8160605100e06031002030c0c030712170609150d15091a2a04050d0c090e01021c1d0708060108061506160302010b060403060501050a0f03120c050a150207050f03030c 73
    0x5d01c00c0c0c0155500c002e00340c1c0e801c2e00b02050342450904541c4803443c11107060301e003880d00c0054a9001952841c2401ea1040b030a000e0781341c0000800d060000241240b46100c4800204407120794400f00785c080a2a4404207030070901c2d456401070006020100d80c02c550441d0408061031100300c007481c0ca00d100308071112114a0641c2c0c0c00c4c560004c60100e2482207280c0e46820000460b65494004d61071a5842c82a004650030310300c0c1010b042c0403180015608052a40100303e4006c010744480414095420032080c00140311000031910030b071020034903003044802d001e04200091030410100d4050f040725082800d17a0500c0e940c03c0801d0a00c50420102a40d100c0424400110100000e0700303540642480f9000010b400b00c070f40000102a50015031048420507160b400601203070400e007004000901940440d82b9070740382503a07158444210302aa0740820460302120a80a00c84100700c000c0b080780e0401c10754039030f60742c641c284203019500c1140e00365241d00c144512030b498100d0000480e4800c501450945041 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 623208938 1250 623207688 623207713
    0x52211160b0c0720031213051905041b02061e010324150515040803090d062a02160302060426061e0106030902060f0708160605100e0603 60
    0x4089000d48240748204040c44030300c0003d641c3d01d07020000d00014130184444d050b903680c100351406040450340f03518100f09012034011900d00d45841d02c160368080b00c002d03051360203107007011001c41c40503400150300c00d00b440c411207040c07203400780c40044a106542c00da4645503070b0a600c642c14000c2201264464202810042007c0303450510142021450400c0d4035007017058224800c0c007980e45003d510070f11032911007001c0049103480c1d01d5480c444d6040380c00306418541b07029201d03034490142c4105d29014008612000741046419881007503100c441e404c82200d500c0307107a4510300c88400c9d01500d54015120703c4554450300080c00e0001c0084a0b4010b02107460a030070040b5841070b0395250b0b03054049004040842c25820359052003d1482a03055030445103074075241000d940031401060784502e0034945042d00035005a100d442c119541d00c642c14404580d98042031800d0700c15441083c0d8010364006448e020241008800d0300461f0243c44180d900304a0346803a508000600f940541e40c241d856402142110300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 623210188 1250 623208938 623208953
    0x40b0c0301030c140609090a1a01080c04060f0c080d020715051b0d0f0516080c04080715110604140106060f080604270812161b060605221116 62
    0x20141e018050900701b402d00d0000c680c40f03580641d0f1000f6082c1e1140c840300c0c2400080300c03031910004401d20b044212420003107500d070403e110314081c02c001c0142000f01d05515501031590a270806a01c00b95640c0e41e1590580c0d1a00250840007046454400856401150b00414081c5502441e410f0002c1c0400800b80002980198400315940c854951a80c04808901c2c2e5607102d8188152541c0c24603868818132003800400740c5100800c0f103800800140410f03c03544000164100698800000c40400c07004090310030b8a032060920a181e1b054840c1c8400c00c0104100900c102c001404518000e100c95502c1e80030503102c0c201b0b941403d20000d0220400242c0600d0a500322100341d01c12409419102060034416081c0e003210460191016040010420500509640842d43c004640300d11038a20314549031000700050b2a0949000740a82550b49840501500340d001c0320003080010400e1081020319502070328501c201c03014446a651500f030f2000181d1743c03548111001201c410420300a051510381d180207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 623211438 1250 623210188 623210219
    0x60c0e0a0e0f0a0e030406080105100503091e0304150e0307290313050715090602010c080415060e0106020f0106050414060d1515080d020c061b0a020a0905040b0c0301030c 75
    0x120011344800840d0b0010a00340010b001401c01a03a131008950b05100500c1f0440a906074454200b10040040200400c80071a40505c0e03403a2800305c00c04000b07108170b111451400703180c00249048200460703060441d90040e051146510047d01901c1342c29640b020501080b20100d1440c084c801c03c41c10706420160512001150f008441350302001c900803031a1942c81c908201380c1c005d402c01c002c10350304072a15250007400a4005215520007840281c9071100300134020000988001c0035a500a04011511599508007501914860101084969450b0300080d034503015000c1219003541b90080110700d90900d4003a010749480404070b85082c1d5203800090251034200550240c41418020310f4008012050b8001c1081d81d000c0c09500d00c0d1024104050142001810307000740c001d643c0109180c6101d030b01d5034025285058000803400116a5142d2000c41c1400c500000087d84401c0744c20011850418076400540501d009071284000365071046044040d80c0303c00c3c00050070a4a13420001c001c0c50042d0760344032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 623212688 1250 623211438 623211451
    0x3070e040b31020402040f1d0c090307060e040e1506150315061b03210c0c2503051e0d0f0504210209091c051809060a08030304060c0e0a0e0f 62
    0x510f4151b031040d0110707c2d4121900502d08403880b609a200007080c5001c25540c1202036551100c0c90001d1610020f030703440d0740501c540420301803440d4407252180d850740c1c000c103d05603008050740c3e842c0040000c120100c0d00b00f181c41b1882000382e48442e007448a001b034281ca110710b511202e56000902c544040020b15084504000c0803009281c5402c2c074281c0090018000e050034a080000c0d80c2c03c940c032504c0d1100c0b100200714809082041c0700300030190400042c0d50124503286482194103c41c0d040c00b0b035441a85542001c0c00a02c991035071800c2810404a803461124540e005482e000c8510020496020040364040800500140020300c42e0281c000880080d00c48641202c1230750191603408034100307902c100c540d13160342c0c2c00c00940300d240003c95000b900090095031800d00d28000c0e00d440f9902180c0720b0804503034010400c100c0020199118100540c0c0605080b40490b9142e2404c0d1034000050022081d201000454402c00b404540c108000600251100841e00419541e40c812090206200c000c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 623213938 1250 623212688 623212691
    0x50a0b090a0f0b1b0c0102041805060609010c051c080f0109090305030103320f1b130e0307240b0307061e0201061e0e130206040b0a050903070e040b310204 68
    0x44c0d02204c001207004040c1034006900268171280340c50121850201e00c42182c051440c140400c0029941d50402201c4000c482400d000e00c1702942420710703520f80384848000065807100307003c00252640d0442041842051320840d01700d19070786c031030b4030081c1624203a40340100032407800e0005100041c041d055826a6102840c40040341191031802200316100c912091038898000c112894940c0205114180c03100e003001002d000301312400c101241d4807450680c01200c40f9030f5070749028140190b06004684041d50803201040301c2e01c0807450b01e170041e208000c0041d54101d00d4024001858180455101c0c119805904c821031039071102c45400c1d00f001d03e64440102155600c02021500340b201c1242c40c0c0031f2441c41c004140100f0709100300022041c00241450000c44503080c5004016500c5604031401d48480e1710402e9102c0300d243c4425905401054a00d5505009240020540941c0d40f07039414800c9000d488001e5140d124511005079081d0a55036403007020410003040d40102c201d000c035503400310340301800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 623215188 1250 623213938 623213971
    0x1090c020601060f05070507030309061701080601091526070e06060304030e0d120206070210020301210203190602130e0411100c0503040e070e0102120301060807030b0d050a0b090a0f0b 81
    0x4a0030f081c0508e680007140860007002c018802d03203a0140811074082c031001e1011149504104605656001c140305034404280c4078603005442c0b610001c141c40051811060603d0201c2c101c000180c4c03400c440c01c0346082039108810002a00708a9192898007441f07000d0203540c5541c503582c400b203074150b00c44410f0076040b10703000700348500041d201360818401d00000c0e4007a1010781842a0003d0401c1032450036002c89a0061006004035003010100442e1140c204d04c2c05c00003412240302182c24000e03130740003642641051004907400e014582e0010840c26140b461f80003485c40c1c8500010321f850310291009054600b407104602d1807410101091100d02829050044200f5510f903100c0b0702e507a0003038011032020320601c07051002644d084051004642c000340054040c0244035012010075000502c0340c5020080d0440100e400140240e200c904110b10180c403142e400e901c681000e65035611008400c40b0024140300008101c2d58000c1101d2643c0c5902601040011180381c0b60201a404060310f66282c1203010340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 623216438 1250 623215188 623215193
    0xc09010e15181c05030d09031704060b0f060414041e11070b06030d05030a0506040207060f090201080c2d0919060e010512190906022101090c020601060f0507 69
    0xc000d4120704500802c0e07420089454002c3c0419008040c10080c82c000d2410100c8000800c0807068a0552850140014034403d03030b070170116041814012268800f50351801070000744403081d00709004114042d01c1580501074100c003441824031842c4074030052190651040c0c5650318064010f102403902c140d0840d1408890031504804640f000c01d0348a000a0b0000b4501d810089500069540038108401074184601060f0303018215210081c52000260f03515000103406039582d038143c80815801210400c040d911303c852101c02802c0b110300030fa022940060000714002c0b400021580c004003e40d051804a030660b41e03042020000c02d2500f850018414000c020203600d03682091041d8600a8082035007071880c0660141c405d1800b0301c006410007508000e204002d0b00c4940807103030042100506882e2030350401d41404020504400c0081c40940000f90040c4880c4045001c001800d0300342e000f40e41642d84c1c03000e5030412a221290740801580140004100d03890140c0745420180e0091b00f001450030038541e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 623217688 1250 623216438 623216479
    0x706200c03061008010501090501060f20070308070b0a05191503060e01050117010b0907080612100501050a2702070813030501020a11030909040809030304180e12030c09010e 76
    0x890301030303c0c25142c007007003007124803001d0107142e005084012040000f541040d60080c14003c0c03044034a003c2c00a080d6044c1025200f031084d07100d040f02c0d45802d988410362a0320b09510280c0c0192800d464074002400407138004036652080c24090752119041b00e01d41c0e071001d10f005002d404104011211100b15a40010110b034060083e28413039244140001155030506614130100b00000244001507031410107002c65a0b140d00300b81580086030743c20405410b55803400001d2403244110025129401210300d1592440c40c240c00c0303a41603940407100c60040e136031a082d0480d46404900705030a41f6a03401c02034140e240c10a40c1c010b20b039041c01840c2c510710300144040072070f240e0501e0360300403a4560b40c0000d68448140c2e00c507c817054003881080246181202c00000640e0840018001a1921600061544080d038040007160001e0240aa072400e05141c910301c1e14006000031084403000d4040c8001c980030000103441240c0c8144101842c0f142001e500a0045410701e9a400485411050150605003060b410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 623218938 1250 623217688 623217691
    0x507171b040e0124090b030f06040216232b03020702060f072f10121a10030203011d07020a0b09210f0f0d1d07090606020706200c0306 59
    0xc034418110013221029803110341e814094640801c03c1203144c000e02001196008880c0c00480c600700314880ca80700c0200140c028415104650103804480e29081d0410480d56401c641c1640f0303030b4041c81118503091048076142c0c0103a082e1000c440c01040b040d18445000503c00501255031445c0050400410f680800c68650200640d00d10030040416074204014180e207901c07549541074001803001803170243c1070380d4400c04611100ea00c03a00425880500c42071080084000300f001404083c40307100848201d111341c00c03580b181e48900640f00d0b02c60081103540280200c038102c9a55a5403403440d031800c000d240348030f504007520600c11402014503410208502c456041c0c010a5018040c0946130064150307284184441c84030f8043c40c0c10240300c0500b4419444e0300384e508103902c00b02c455546444800a00d0001e04075490070b03900518140d0302c110360f1544005840400c0e140e00b10303410009291034a00590392413440c1e12039080042c5d0a10a5200207081e041c2d8a54246036211003100d10a80d01c1c0c2c1c001a003441d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 623220188 1250 623218938 623218949
    0xc06070308130209190605031605010305092a0f030109110108070207090603031d010e0112110f07240614150c07060503060f0103091208040c08060109050a0507171b040e01 75
    0xb170515001d52090040c41070314003c2c04200c1c01084100c5900701610b905400f00d1240714141996080090078188081c014040080700380051413403030003083c003448610380c1002d816407805841201240c40040c10140b00310300460703400c0031450b41e0b040e040030011901174600074103a804601910a000070b14052500854010314130907103c00c2803901c1c1c01412040d002026a00081c10015080031309801641c008020610b102c510110209000d03003211101c241e280718a01d805d41c641c0d01e0028a03a030500c800440c4840d04c00d522030b44e280705000318042146050703881c0c41c010641c14040d20075101e00307035103400740301c20300b040d4183e01010b42818a000060740c2860107a50120001c50000001c00190307207070404609040c0308090030104915141610780c800302018418940c3c040c0050180031030306201c810145032000300811401c442e41c03076845401c0e80002e0300303040c1d074802401410180841d0009000d1200fa911940305610280309668500c1607400b6080010304c0103014400003000049090140340303411502030072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 623221438 1250 623220188 623220211
    0x70f05122119022508090a0e010e0609070c0503070f1101031e1d0304081005010b0408030a0e0a05120307020901090b09010b36120c06070308130209 65
    0x1c2240c00541d10150800144420340351001c1082c014074660704032042e01e41c04640140c07611450201038600e1009102002d4140701450842c0302001424002880140341c1030ba00540300c940d0320718008004c100c007801408400c0000500052403420103286803a8400464905100918401e4481c2801d44d071000c0801d8400c01e06c507440380000d0164244910007080001e00e0100f0140d0150003480c50404509074401c281203844082841102481180d030a07038003020541030f240c0e01e55540301da59640301381d00c00c44654440d041c100006004504441900d04a410030006545410b50000c170864006c0e444040d90382d40109050404280c030f0f2180710114080b84208002950b0703940301401001122501680038080060900085440d9500d41034242c0d07044a01005d42c080d01d49000400025001485015440e1340700d290541c0303405508030380381802445400c1030704c00ca034901d20352241e82ea4986036148502038202504110320000a4880d150003076006014440b030942c032048903030000b98814403d542d0214042c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 623222688 1250 623221438 623221447
    0x50d030c090512010e0c010807050702010c02190b040806070c080a05091f0306050f27040c0b0307121404080412060920031e1903110111130e010515070f0512 69
    0xc01c17042240052110302400c2c62105440e040c1f00c0180030b40303d114402410021160460011921180300540c8050601207080300200d85544000006822502c2000924440c8202180150380a008414120f0340c100e402c4a103440001c0c5400d80c2c941c2d000c01d02c12504000a400c007002044490640f200e0100200d6034041051440d250421030b129420508541c4502c132150b10a40b9103440d0018181602c40c1c0d00c40350008503580c0e03070034102001402036001802181c2d0000411841950100b2418540809444104114025040c032001c016104403001000b5003000c1205112800f611207010f50102d100c5e90b00418110f1641d601c800120380c09000c64410a00e100361540d52900d401e0054a07228001c220b0440c1403800042d038050307510b0f0b032000c801e480100103081208040c584141d0403590160107960080c010699418800b040c65408007040c00e414201d40300c000b254030100e200b001c504035031008103c400c40c900c81d00c140c000e1552242030b04a6401c8103800e401e00c0059000c4c843c0586100c840700005403035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 623223938 1250 623222688 623222711
    0x120a39020106050a05060403110d0c0e040c06050304050d050d09050102041401030b27040213090f141f0c030902090f040203060f01050d0f02010306181e050103050d030c09051201 78
    0x949145820013845031580b21010701040c0c64000a036403c482e007080006000c0010301003c100c52003010748000c1c20080300b000c0081544001300c1441400390307110310803100d8440e55510003251540001c9e01c0c0200a44c0003460004000d62040340030b01881d1028080004003400d413582c1301401c90b440b0354802d82c2c02c074141d10110a803d40e01482200700080b810340c0c501e5802c00840454120180c0d110404500b14842e9001007000d6403265482665143c0c42c00300300300410055400c0030f444500040c00300f114151003c106a000c0b8410216446400c0327544111038010502012880c0c101400404074603808040e903550311440560380342640940100509040c240417424180107043c20700b10020508103100502200420050f140d5003c0c895446170030404d0104841603500c0101c01500c2036034070200000030450b50743c04003240254410b5000c040415521090a0240c0c00300c401512024440070b00580c000b5000051040c9c06904030100d01a104d00c0c201813144c0e1124009903010b104980c11031035030ba66030804c8035030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 623225188 1250 623223938 623223941
    0x3010c110606010c0510020711090f06120d171f0e01080708060f061207050402190e03010b0919020c011b080901060f120512070b1b120a390201 63
    0x10021020710385401c2d8900036031035107980e03461b9052040c05610b600098560504c0000100905009401880c00c03201d0b085c21001446401001d4440e540b04406261101800b8600011181c1c00c800d83e60302c0d03040d082d1140340405158400f008144050620182003116402c581440c4a04094542ea05070800349506155516242059940010995a0085003402203c004040520381d224808035071081010018090607818001c4a0344080e80140c0081440c4028143c04224140f2a13080e0780e82d001270030f002c00c0c0105400d90341c844144a41020521000c0b50491010516501101a00d020090710b41111400d0440c00c4905140c0d02000c3c0b54503007031445805c01d038880c21003900f0002c02d81c000d1210500b8035821608603000e5110301c4101101e0341c0f20480400c14107010004280003840c080903180e03016810030800c50403040714181035a000c650003130210405c0d42c0042d640b02c00d87c8102e41d912950f680c5218003006016071500b800e111011080c000c0323138941130b03003c0c036210100d0b031201c406c6031996640e80e0203030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 623226438 1250 623225188 623225191
    0x1030b07020703030509040209010509030703201e15041e0e0c09010210020901020a0c0902281b020a03080304050714040204140f061b06091009110d0c0503010c1106 72
    0x4541020000f040465803080c1603842503182103400682e1210b601e80107031039502c200c04c1c07410303091700034804000b052040c00c1c3d500262040020b41031014414680042015051100905640d030414854001076142000c4141062503c514021140350588130900030b0645618000d102414107481305042c05101c47c00c00481d60401c420303d0741c2c0d0381001600000070303455448589007009041d5010981b5205c582c030070007060120b160444040802c0f6034860005101a50200030190b000c05a800070b00b0019403128030741035000715074175540c1054411280a80c0030034441d43c00c00070307a40b03c043e034200480440c4144004501503885030004100340e52505c8549051100e981301c0b1640703c0c0b03105000c20441603a400c4100000031500711440003610320168002030303250140ba290a141128403c100c02006000025002d01802c409800c94a2240100d40010706440c010303e001001c046103103003545054140b581d200e503500d0b403081000044160b00e5030082401c41d00044508000190980d20b0404098011301c4100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 623227688 1250 623226438 623226451
    0x5040909060225032607080402060d0f0603051e07031709130b090a0515090c0c060c070521071b05190e10030201020a0b0a0f0207030306090f15050112020f04030b01030b 74
    0x514101c551745204084040c00614460912006000140131996900111200b191905404105030540e5910b090000e042502040307840340f2540400400000c0c0d140510010301c801e120041c400b40d819652400c6404a0180e02e001d4184014041015166601d500c02e00d0340007550030340000c50304020802c000003140050100c00301d1b2894030b0300b030240c400460607450380c102c101a6a00f2005489074090316245110342c00301c01085019000902c4100004034008280300381c013070f004032501d40702d075009a000310302c0c1d650400c018110700400202002401c007111100c485980705100c0803d595548001ca050303120f81c0b201c0c400015040203014880000c40fa01001e1300690044480c0207800d0450b030010350395004081c03000d00a50070070400980f20200781d030441c40f9441400030302903490300050314001d0054a51401058a4142801310f582d20080c1e183c440c81c295640c040060240701c9140c640155a0f8450004a020320313107400f00680ca44c806920f02c01800103510078107507102c117985142000030150038054032b00b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 623228938 1250 623227688 623227727
    0xd080d1503050601061803020333400305040f080a02031513170706060603020304030f03020c031209060a06120b28050a0f0b01050a0504090906022503 66
    0x1d1010070800100a410b60b040c5003016203200c4c0d0300c00410421041135a000030b525115500c66044101d61070303800394a0141c0c1c4050881d24401e0b07001303190640c04204440c0710880e1030002403200c1950718001d0581d103244a070301008000921b050050348105c54800401176010030800141002240b460350004001040000f0142180c100141d0019444206001c099103c0008180108091054907040440042d50204035082480307004d54018900d900320355070030b4501074580080025564040c0c001c80340f0031075142e82c442111038041c40301500290420200c94585103c1440150520080080340a0155085600400e05460120800070550b552030308130f00014000c404000e000100c008440d9500010030030b1058854018080141c44e880e071285d80f9030103995040c6030600501c030300c00303901010445442c10b205004409080c4010750700c0d4800c800c074080020303908101c1081403d00c1640001900b070702c034070809440d00400c003200c62644031000903038008071045580342c50300b059001041c2040c1e54003803600c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 623230188 1250 623228938 623228981
    0x10e0f0609121204030b040302070515120c0d0c02030702041a060706021c020a0c05070f0b040303030e0f12040f2313090813050a0914070c0c050d080d 66
    0x200c0d0490195058103030086201040c2d0121810050168150314024100c445031500da0300d0038441c0402100b50703801c5d0701501840e100810f560902c0d06402c05168100c100e0946481084a00c02051020041180c0340b000400d01681c07414068901943c84101807640c0219114031342c900400044412644107000044064104651036884040555070016045200140c41f00016a401c0900005203840412182d200017194108203400c0440140340b14001c500711a2078946480941001c00c219004114034140140400c000091086d044811010071040c2614032a20581c06840d01d41030b820300d40030740c80300e401140502c007002e00c03c8200030043c0310b041c0c801c004080e01143d143c4c244a5110341514091388400e1032050400c4001e82040002503403049555035220444d80e0140c1c0066a40d01416100e02c59940c4006440344490041c4d410028110529180d562034010b41601c4070300c1d407108204c440300440c900004040c4e88400203424031a000b501443d9603540c284072490116100c115284c55500350740d030f0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 623231438 1250 623230188 623230219
    0x1050c03092e050c071104050c0f0c12030c1b06010b04090209061314010306120b0a0e1009030801090b010f0f050f161104050601082a070b070905010e 66
    0x540c01d100c2c850164035500c41268004455400011003001a10264242418000302d030440900a003092401918030b0b501203502003003088181c61082d1001030a020742070021401c801d90f0f60005000b000c40b01005c48122034030320301e60740100c1d400480e15507003201008107001c0030110707045288488404040e005050a50304141c10940c2c40d00480c02003411256010a00d00520386840003190842d030524108a50a10381c0c40d1001358031807482d042c83c1400641800e000181e0b480505101640d01c552089410303116964120b00f00008000c081c5a602d0140320b090302c1107001640341c2c45142591341c060360b2000e01c03940c1814042c901384c40440c80224100300d203003500d0140c0294001038049a04245290240e075034640782d04544014001d4605010600d0981e00e005c104120342c450b0f001800b400b081d142480641d035020015103200000319440c8021905a40c1104a0150010300c0d030101e00009080b01030800b0181d440d10b20415804440c4600441c088020500c003540e00003c601e46100d00445503840c0529500c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 623232688 1250 623231438 623231443
    0x41415120601260102180a1406040e060a0b0a020d08100e040b060103060503100b03010b0604080d030203090a0c063b090a091406011703030c070206090a05100504060201050c0309 78
    0x14843e5407004030380e0601d540c5040201101c40711108003c40029502d40400044840801c00d50000c494450494003c001554545030f2608000e9880001d1900f0305103490030702e0560b05400010030060303001c038480a01003034405640001d002905110350007440c0001002e01c0c05000d401d0054420210103400710010411301021f0b20000e540103600c0b407850800354485800590260090340c0045030700d4000c41c1402c010340240303075001d001003070b4044000388038503181003003070160314412030140002c1504108005d211a074000d030001c0d81c20600c1081182c0c0460383e107480c0e050f48600c49030006000212248030390ba0455001c400c0000001000c48410140c850524140010500e00880200e00070180c050014485a1840d844503045030340140340b075032030158068411600c0350800d02850803083d43e084c118000b8214004107880c86801e1000d9007074035081d19a003c000150f005181c0c1e055004202101c0800c0a44609420050782d81c000d485041c0c40b0b608155010f030942d00024006000c1c600180104030031030400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 623233938 1250 623232688 623232691
    0x7081909140f0f0a090c0e040c050f30010302130c021905070305010e06010512070e010b070f06090c06030b060c21070501020a0c1208070921020414151206 68
    0x440d04a1201c040d003001003083c03d50300784040c96105480400000c0d0400d10350300942010006507540c0803001021000700821148410441f400066050081c40d01003900d060040035103241900c107071a421950358514846102444019030142c00e010801001107003004c64140c201c1c810101d038184285c204d4804002d694035110000040c0d640000c82c0100244042800800040c41d0443e000303100240048142c2980c82500b8030500d40241410042c3c020462000704110b0103a501c4480d040406901c3c0c50201d44854214035400da84c26074203941c0420001e5000e00c181c80800e48900c03046031882d0b19001000d8112290000720764000e0804000840007054041941055818100601c0b0100000201d284d00035002d9604d00921562002415600c416000387d00c1c41480d51081600b021100081041110082c00c01da5a40d400300300c00031001e01a104050480c07103d6001c1c0320203500b41c40000d54000505a03400c172284556003071426024008980010440c80581140907134030110340b004c00310480c0340d42e40f10 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 623235188 1250 623233938 623233979
    0x60c02090412030e030c15010b030c041806091503020901060c1a070c080301060216060f08070f050f0a030603020405090307031403060f04050f25050d0e010b0607081909 74
    0x150a150700b80110700a622078148600c0c0d09044035103074a050311900380ea80c0b0000e1140e8521042038400024212101e074116489005008003250406140c821650b1020444c40d4065020030785030034000c07524042a1041101305107107088a004c03610b2460041c001c0144040c0c011100300102d008005010400040110000f80c4264606450941d14000226010f40c58940024400540000000b600310340c000b58900150480f00e003007100465031000151002c07201c944900010030480000070b66401e020342070002c2d940c0b1880c2880c5207400707040280c03540b465220010840109558100c10300075803e151103034a40c4070300c444004601c1c1c502107440180040e86c1c0100100b4480000000185454a48504001446502620500490510038940d4442c82002c450088140c501d01400d103a44070711040c2c0d82c600f00b042c592900c074036120f00305000c0000b0b806c3e040182101503407900b0b107007241ca44400c8000e0101c40d0181a8443c0c1b1582801e0319850700100d0340c0c000d482041003409050116185c500074651000c403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 623236438 1250 623235188 623235203
    0x206090d0c1502041806090507080402090603070504230c0702011e09050a060e0f09071b060e120306010f020c010e3d09053f0a0f0c060c020904 63
    0x845140c6180c110401e442c4104a1900100340000d4078040701142d4182c603400040c05101440c1c440e200c4508690048903260000f8004401140141c1820100b050700840b010f0281e0b0402e54655000c1b0b0b083d00c00343d40456050340c9203800200700408094020741c1d085010b0304551881d088003900020054a1084500001580c0003451003083c02d0280c2052401000c000d45421031036a500c2e00b01400d400c00c2c895072140107485840180b6202c0c0740111071144202c141d501c07200c0312804007081c0d4882c0d41c3c0090904844003030381c460036103446060800000038808101014241e6038176042000501c1050359004a80a5600400d80c2e8100c580e0040007aa40a5000343e0700d62404803c8000a420310300d103c0d00c16105071520742c0c43c5807602c0e100f01e0300000807010496103840d00650703030303403418410404600380c60440764040c0314180c0e2126440d0140c62440440000108800c1101c821078850f0904084030400c48566031010004403c04c1403005c0000e00511150806425210040d00455403021000300010a0386 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 623237688 1250 623236438 623236457
    0x14100c180b1306030b0102071a07120c02100f05070b15030c0901030c09090f0210080106080903040e06041109100504031b05010203031302060d0c03050a0e030c030a050c01061203031a010206090d 85
    0x2030340b08012301c200900d00300c001c040c12001e541c400750900b944005820b0301c083c00141390030021503000745042e20300c50350301922148117056158001c840d40300710141b010041101c100070b04008640902c3d032050280071900001901841e043d410540303401e2021020310b0042500300010400f09400350501000c80d026a900401c0c10304061034801c01d5000c074014000d502915030f00d0700801c95907101c1e040c9410780c0c0d074a441d644203a8035007c030f1007079490041d440b03020b0480c4d4445000034010f0820350000c505400d5404403a82c1086c920800080400c044958440300281c2c000c20208103020300110210402e21403043c490089504140001b074807413000406404c9400700180b1210110348554044509004003440c081001c40d115000043c0503101c00d40e40c03030300118100b1030800101c64012003284c002641e00c3c00103618040514605030f0342c0d50410840b040983d542c596001441c400d142e010000498401d039000120410f00c0c1780b84c09082001d000d01c01d411175105400708805400009a030180c0044a8240744411 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 623238938 1250 623237688 623237711
    0x80c09070e1804052a041d102f1213030903031803050609011a0a0b041818030c050d210207050c0316030507060203090a0314100c180b130603 62
    0x3008458054001044905940506114204603e482c440f039000c403000e1158544c20003284250147d50710703c0c1d2440d604602d100f0401c4907210b905c805480c0c0e810b00b5000507109032107070341c47e001d400384100c2251b840740d0005409041d82c01d903455542d034003140d0320040408007105170314020720100440c0001400d0140b034640d00c0c1c20502d0440001c1d001560f20108548030340c40d180410324046d01d00102d5200724902c2c5250800305615016071042c080e079050311801d50030245050000031002070009104481e460340d41c08201d1a060810075400303400c5001c1d803a0556100750b2450424034201344542c03090108180c144505800c00049168204580b0080c2e0016032141e11600742242001c20081d5000d91601c00c58030410b80c007000c08450b40007100c1c05202522400703070307913003005985078400c00820551155210f00700380002040d030a00c05a1a44082044401e0048840c40786d400721039401410710003090101d1002950348079100c00c000090041900d0b841c0c204075403166220482c90003030140c10b061640384c000c80d204 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 623240188 1250 623238938 623238943
    0x1e06060a1205090c120a05030306040207030c06060e10121109060414100509010b030f0721020d24050607020409030c02060a0f0315060e0d05011104080c09070e180405 73
    0x1120407034504010504102010f19a01c1240d902107a0140e00034403c0f110100f8008a582c400d083e800c00090f61660b0703604800c01000307502201c01181404070100c1c0004c04035065100300c6014203400d07041041942008000d01d040900c0d01e038080d00c03004000c02c00030f600086440002c58651041540d0b03004003500e800e00018050310340030007000504240e083c1000841140e02c002d0a007250b4007502c18040320390b00c0b00d4455200784000c40e00c000000c0071000106032500c0c4102d1004010b191690103241c1c0e43c0300300ca0118401e0740e01c4400f104c10501e48902c18040080502e14440440181c0c03000c110f8840c80c03900b40440e11500545102a01c510f60301e10031103007414002c2d0b0a108246d58020310942d07aa01100358060aa0002c94500c0c40000c1d28254000b8511031030100d901c000d48810307442c1c1c80312010420081141107034140300e00711090b5480740c2880050b11401c0e8050b1000d410340300b02420780c41c02d0b40d5080c4680030f94010500070400004a8278429070b0788a0411600c0d4003200340c601d0071700c583d49500b0080d2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 623241438 1250 623240188 623240207
    0x1504020f072618130c0c0f06022a070f050d020402090303160b0a15030206040b1308070807061404030309032d08180d05100b130e0a0b1e06060a 63
    0x2403a4060000d04191202d08448000561030012100c070345051245407040000c45c1d80000e013900105021503200804070700c20a24021110b0320076a030151900b0390180c414816010b401428401e4030340e82152030000e0b4002400f40d800905049440c02c11400e00e00b42c006400c010341d81030007178000ca070b00141c64010b584007442200d18500b01c640303480202400d01d14016048500403900c0d81d900072720f0b212803080891a040080021250002c0484d810300781040c3c0041c0c4280c4c401183e50080328070250300040d05100034007199000b00350342e00142c0710b01762501c1000b03040302014070950304030740c40c0401c0103100080c0c120041c1c1c0162a041030443c0c00ca0562040720340e1050740c42c601e501462851030513401e010004520000d00c10301002c070b98140c0300881c0c96000d0042102c0310400c0144550001e6188180103500c9500032058401c0042044442c0b044000e86170044421003001d054040e08100000428001c14246140e0001c0c054840107000c040341110815041402070300443c4529000510300d900e241c0320b0080715 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 623242688 1250 623241438 623241503
    0x60c03090406060203030106180608040b060d050708060a1a0a1e08031317030903060f090111030901063002040b040902130606030c0e0109030b04020102241504020f07 73
    0x800000d5160240a0b40c0c5c0c2e002485031400142d13404000303884403200c1c0c4110343c0442d01c4548807030b045a1160b5445910092000308000d80080950303401e0f001060301000444020251480500050700f001d1940c00300b503965140c203620007104000ca041d1980e03181c6448060846a10108c00e18001c00c0c0589502e26905459203c0d003288c0c440403841401d055001c14180049604884084141442c1c80300100d4890094036000c940c0b5400c0140011082c0d00ca000c005540b0480341000001c08954101c22044950010355118010360355a400500071801411800d00e00b54009501296510b00282c1c60004e10441d503e030b0084c000e0b51102d03907a8205445035000402c14a50060441c0090205202448000c00c050710030040003d00f88a10501070fa802420310343c00252041c0e40e01c0000500319120034116080c013900c12030441c81600c254198400e01c05600040c615000c82002603d41000c0010124011025400034455841082107007035240c0701034129031049038032048911407004941c08a0104803000ca040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 623243938 1250 623242688 623242691
    0x1081f0e010b1c0b18100f080a140a080f0f04050405070e030c041a0d050c03060702160b040e0718051c170c0705090a0b10030608100c0e060c030904 65
    0x2180394514000030f030400d000020075060209109115550a40d6981c90b40e058010800c0c3c0c103260801e00d4011085980070170307414280003200f503941400d408206202d030300c443ca06810002550080150001514003140c018400078020305101d80c43d4030003248208090070302800c00001e07000c1102c0702aa800c2e100201402001007200345040c14000d82801c8685815620a010300a010350349443e02c4e100e130104044076a904080c8181805050200c2055149800d4500c0d00c6181e0100c0c10310f56003001454410101607020b0050310500c0c10341e450740c00c1c0c03071500002007002c018403040c809401c1403141140c0c0b00707420746403400c5140000c4140364a035200c5500116045007100f083c403007030304440c092528016407040c2141c420328500c0d4003465040d40290105c200140d01b100c01c080101e49441210706070054508040010840c0031100058244a48041d04a02080e103e4100704507100c02030000d40b9642c10b140c5414840d01001c640002c00d540c8012800b0b0748104004990355411000c10420394142501c050b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 623245188 1250 623243938 623243941
    0x1211030714030d030e06160311040906030b010e010503030a052d1e0c102004090b09091b041104030f0503040e07050711010807050d0f1a0a0501081f0e 66
    0x140c031039081d01100300441c041e105444030707041010710078403031203505d811140d01400c80c1e03866550395200d5803008401104200b580b142a03100006c009280140b00414455000084061944c6850315070364405a1250440f094100c00400003518040111103000358645042540e810b9000c050303410f03201c1544400d948801d0440840c6034181c94981c02822a0381086100d2501c5072045c81400ca4903201c1d20700c04034a1600030a0500c29280144e8000620039490b1314650902070060f40b58100458200d5480031008a8440421100c68208440d00507040307001100503040d81492504a451012a1000382d14012513941610304c241402d0201501c02541d48510849c400003c141069035403070700300f400744d200034110050100d0b20850040c412200c40079400000220054140300054900b8040100004140441008003001c5c141c01c9201d06001ca0f60125000038144038101c40100d200040190014000da14241f4144850389c0c000115540c025104000903500c4414011040c54002a9600c82c071600d144420 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 623246438 1250 623245188 623245199
    0x70c0b18010c0c060f090221031207170f1302090901020904090605010e0f01051f0c02041b23070f0f060219020607081605070204060e150f1912110307 66
    0x4103e15030640c0552030602c050008181410101c40040000940c000c52550384454000d800341c0c0d20b04910151501070380c0c1041c00c140c08442c0c0b8048111451030004005001440b003407001d90810a800405c80d2001843c3ea10300030a409251580700784003e4400c1c581c110002d50415003d4040f50b640500113807051203a10900d180407809010280107810305040380c1e000150402c202505421f0485034018007030f9822403003402c00e50721003100a00325501001081c0303801e00007580351405809048200240310060341c1c0b28007100103054030168926620141c0c50000380c102d412003100156026142c00c030304502c00c641c1d002e01d4100040c00307464400900c47d50022444400030449c1d201c080c0310443c016000d444090b640d03110110340c00102192854810a1a0004060020302c200098000c03c1c0c4050800124903861700317460f42900350102c1d07092816400c1824002914140511703007204002d81914030b8440c0d001c440c55080c824034428016850080b207802080000d12001d089013100b0100d02500352403102d07403200d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 623247688 1250 623246438 623246447
    0xf0302010e12071112100e100207020607030503040c210b25030c051b06060111061006110f070f18060506040905190519140f0601050306030a0c0803070501060e070c0b18010c 76
    0x255032254090092365030017900300c0424000c03a000242d008140c00e152a81c80c4d1340a507400d410141c8261403100e094140425580c0e0180800c54008040c20781e0071a00400034905003114600c028801071129a50640882c60364011104c800d03401502c50034081401c84903403804440764002c4103681c641c440300d03144034170844510100c0d0140c000c03c02a42e03904611481101c54540d60032064131807000d05200384030b04000700b0744219034918007041001d06903507030ba030351541d4100d280bd0001d410014000c40030f20000c11900300780c1420488aa02c181e0000e008045ca0000001c01c07500940c0304054101d616080000c419aa204100010f4146002c0381000503007040304074108401802000c10381070a2811001c0b0811310202d09105200c0d803102140600b85d81d039440011180340e0001b60800c0d40520851905030000703446200180090542e901c001d541f42c62a44c01c09030b0a407485035001015001484c4184122a030f0300c40113607268260810300d00a002c2d290782182c2c2c01d0652500795840c005500c0c200c100007985502 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 623248938 1250 623247688 623247701
    0x115030201030c05030c040927050f0c030f10020a03150b090307091a01120e07090e06010608100b0f0d14070e0604060f080c04120f0302010e1207111210 67
    0xc0c0d07001c00c621480f4483c25603c0d4407061340d098210041c2070008200140c015008114007460440c0840b07881410040400413034580130008581c160082c5d0000b0303030708900401a401d03d0400032401044050b100b002c84640303401050104c1d114036a00065460080784c004c1c2c0008a1100c41001400003041d42d40c1c6410300c2c250000700e0070b81c6c828084c0001c00100b0408501508280800300716156900b2100a40103440e0b01c0f80034001170b1551515420508803811f02404280000d100200010403a020207500683c10031030141c000c40144004681841103040e02d144402e4280c401c4118100c0e40c5402c0c106a642460040c0c422040e045410405c00c00360308003114175010700454641d2202c1d10b03040100384c00c20a25000f03c0c040c0b2741c0043c0e2032400246a20b403150301c055401c00403280981d80b8050305c404010321602c0382000c066507960070f030100d01020035030709209014194804402030200080c62042c1022203208090024101c22060700c6041c2c46a81c0b542007411000203400c0480311001a448662000762a8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 623250188 1250 623248938 623248943
    0x2a05030417010506060915090a033212031f0911090111011b0302091212030f161e170f010f140a120c0b0f03060f030c130518011503 58
    0x70100440c00c2c5050840640c0d5040b68024004140501f0703007400c001094110310080e590043d403840000000c100c0c22011580001c18180311542054148045a05484486d010700304c016845400344c0345c103502015046e00c0d013100c0c0203842890070000e21991030a044446801c0b030079165281080c00c070715280a0301e004040030b61007a240e10f440c000c02d0340131890889008041c84020f0381031a0211100711407003079000340300303446005001c030300c0000014010603e04006101822411078000040c8018a004910016840b25181c074405c3e48140780a9030090a8413030401c1c2d031141d401c0a8003507001c0d51a004998680b140400d8200450062429850805002c0c2d03080c440e8030040c020911000c101c586182604805008028280b070110a00e0040716060240c1d080c6000d543c81c0741c0c044004a92aa1168001c3c9801031881444940b80c1c10710344100076400c0c540e070040302d20950200e84041303055221005004400300360359200107219692038848080403000c1c0f25200f0015481c042429a414a40c490070000b90b90 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 623251438 1250 623250188 623250191
    0xb0f030a0e2503022107090b03240a051b071502091905090106020312010b030702010905060702150a0501050f0405220f0605010911031504090804061e0503072a0503041701 75
    0x800e2013084071522685d0880c9103400c010302c20300001040790000c0c0c051000107030071985c0d00c035188134010220601b050711035140c041c000e4091010142c01401040e8005c9652040c086071a07028509441e031038403580700010406100540c0a0810142a5041c0c0d000100302a101821941400c0040c2203100100c0c050300d44640503407800428480c0c8000140c6001c1d150804018a11340d080a1941c0d64076000141084115900d403010350001170b4052101c1d03405101c19800030940112000c0302001c51100091106050603e0613004001d00e54440e011010300c1c04c800d03070700055075486401d0040032081190a1120300c10940f1500d0324104456007460034a118001e410030080c07640c0321120340c0e040e14044500d180d9440720520121f5001ca040d050850581400100300181c80d010941e00c0c144990003a5012001284a40c960361400010b1245c034848880c000d460034518500d49680c3c040e0030f101c102d80d15140c0440140101c004080c646800d02c85d0a1034002e03046a868a55a82c1c0c3c04a020303000360b00c420b4855 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 623252688 1250 623251438 623251459
    0x9240d230108010e07051504050a0b040602010506040c090608060f030730050a1e0b1512070f090b061201121b260309130b0a0b0f030a0e250302 63
    0x888040c40313261484068800070f426924540410000103000301500e0401c0e000301044005070941e9100001e80c0100003003c0301d6a11585041000390031501d000302407a01603030030403d05da04d0307039580001c41600b5129a03040204c5a5206c0c000807410186005807613a8040c400c03500c0100d041c113070301c5a0900070721422100d9840225070300032003208900c83d00780b0014400d0f4081560381000030b1064180030304409100c0d0322043c044019484040074504161481011008112013041c8503050030910541011245070051240ca4507080420a05411a114184082d0341d5442852005d40d13600c2e04032501d0902001c00d82c4c1d0956182c1e4148401804c400c0c000f110030100841c001d8810603140070201048a48280980f41c4a030500044a15642c0a00040740b180b40401c000140e95907030b51075000072001010401c0040c1d0007100005101c2074041c1c90b00f14144400081c0103500301d11301c406d4122030b40b0490008011640c040101c3d0201d1501e0407545000000c81c085104c0c2c0c80c10f10b215040041e04403402260944000e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 623253938 1250 623252688 623252699
    0x20d0f0e0706090506340b04020a0b180f0f0d050303010504061211010507210801030210090503120d020c03040e0a05070c050a121e090f0b09240d2301 66
    0x1c203402031103000c0e00039201303104070b0b2443c2c1b800401c004000950351000b0006581082c504050112403082c084603076684034018801917041802d03100c03002e4960184080d00d44002d00703852074255094049400d100d022450401c09207511b40c6c041d4200102d2010744082c50800440c80c286403207800174092980641d180141c00507c441103407554180494101c02e030004140021340c011910390744028026154400720f2a40812001400701c840a0308802654400089504500c10402007001c41c5091104001c8a454140801e590200f000c0f1000300f00304110603035840803003500320b0207030040c1d2280810790b01000c60001004030a0303124a45c070680c0c10744400c2046984a07030301903801c12505240a40207510500080d40004c0c618240c1c04141b521504003101d000c2024003459a0b000c40d40a940d000041c03894004002580c40291184060a490240075007022481c41c0400c03c01c0500000214000020004681d00c200b140b2089420142c50b0080034403240550810a0b40e101030003a941c41250035125000054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 623255188 1250 623253938 623253947
    0x30a06050f130c0902031005060a121d120c0a0b0106080108010b04140705030603010b040606050a03060f06080402090705160602071101081005062104050708160501020a0312020d0f0e0706 82
    0x2102030f809251420414109403084009410051000c42c072610b000c040416159664405804412029580d4038481032190310a03d0541700c480b2940b00542c2c20a20481c203101401007420720320307007003070001c0c15855001d1680c1040c9044407512002d805c50309028008074105a10000c4d20741030b9a4400000d21800112000340401c5600042810021110079030200302c1c0148a1401503030812130040004c25000b2680000400b180d50b40c0c2d0104000c62000184941c0c0c054142c05164014103020070042051480d0420250144000410013449503280c08002059180270310161010815426001060754640d8035002000394000c1c50700b0f8400c2105103440e0915580b140b0342281c40788041011010900e4500418005680c0007240c566540900744a0884c1c000d0b2101900d8510036400f4200420350b4601d803006007400c0000080031442e102c070905200b032000d66000144447d500343d02d031400702600300c3c083d0b800034000e004040e284100ca0742440c080c0b441400442e0002a80c0041d50000c2d560841c1d40e8500c00e0700d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 623256438 1250 623255188 623255221
    0x90d08070c081608091503061e060f0a021009110112020a021002090109120f0b1303050a1b0f0f03020f0705030a0f17040b0d060b090f1509030a06050f 66
    0x1e10201c2e042007854401e00d03c4010520040e03101d5011035080403061700c00034541120080c0945420000031041051034035005400750f070045d400e084070403018030401e0081030a9110703841144503100d02c0064442c107550b10820039080340c0c805040042200311180d2404000344615509041e000903290010347c4c00308040340c800c44283d8045900200700300d6960200080194016030851414490309c0080061400c0301040e031075040354460803000e80080c01d5450800c4e10194040c0081e0b50030548940010b00003a044001c40d0040559400c0c0984019140c11803d005414403640c020034141c408070503041005103810455094500c03d0b000c0c0d4408a43c1e1046043d91200d00740b14440d0305a10240724072020510a00b2048107007401441282840650307841c80c400d1b90340c010780c4420242000010784031080b03180ea20402c0082c0544100040c070b03210546d0000b071140c0164403c418454116007a00041701543c1000b01e801d034000180c1621940180c07810010014001101e0a541c0404444000350385004610b0114 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 623257688 1250 623256438 623256443
    0x50d05030a1a0904020d0606150e1504030b010b0c01091410050105030c15030a2a02070b07111e1504030b0906070f050a020a02040f02031914010626090d08070c 70
    0x100034a03504c54081102000c08030b4002c2d12260354500c0d001c10000d846580641d503c1d255034071a000c20441060178020001c0da15400c20034180380502041c030004075480e0136a81114081044251502a6061000c3c018070100c50010304107403010200c40c1c030102d000725580c2200100c4c142c040200d03aa84400f4103440d0a001191554864080070800846043c144082d5800c85e9100b5400600d450303003c080f014959540111001642170144d020b42c83e0710b90304001da03402602c0104145400c1c0a942d035a0b401641d1903588400d4410b0b4032a08003002c01500703041c0300854003400100086101c03405004606000d900038001950822817000026804542c005035440c0500100d9960b0400c200380d0400841d40c1e5004885400118013810462801603525401070340041601c2140050341c07420100b19820601d461500140b80c043e0402c40ca01c10355000350b44a60b4116089030038220900e200952800006440b10800c94080c0000d0341c00340450540d0029116107010031a45980340c140e04c0d031450a964072007024000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 623258938 1250 623257688 623257699
    0x9060f0115021e0304050a0801110904020a050d1508010f05041707020315040305190c020a140616050604060c110318011b0302161202010207150903050d05030a1a 71
    0x1008104518920300910071014410f071511400c1100310100078401c1c0000041050b8808602070159150000006000b000d07418000c1161610500e000e9030b55004100c902442079902142d0300b43e00a0184085400c6403011a4081226004101100c410008607000300d504542c601145101c885074140b04541c0031701d420600e13900140029641c0d014055115000c100d070036024040304c1912070b02040d514180503a10a485843d140c07080f4a2184180b2114056440b0400a4080040015841b000303500c40c151211060108004152800803504901c40c80d44906040141081500d00b400b101180c49800b441c42003000380100f02c00702108503042c07070501e014075905400c100b00d800310b54103002c511f540c14144c043c14010810030741141c0303110703140c407100030b094001d60440c0105a80c011600c55404000c2d0481c101c0b46410395019400003942e40007140945459052808000c1a0031801500e164000b0369010040f07400a890700c840c000d00c280c20580d03088480e0ba00b884030200060384400c1803d04081c102509 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 623260188 1250 623258938 623258941
    0x1208073e0d120b0d05071203030528090809100201020705070b07081b0106030b040602070302250b091906090f0b2502040b1c0b01050a031106030406180b040b09060f 72
    0x800e20010f1090b140181c3c4d01114481042000403010322501d0000c00b20050380e003440c415242000b130140c80d0010464500c0c0ca0054050b200320b504401d40c0707030505845084000512402518041c00c1900c079001401c3d0380046c61210f10b09040e54150010f0000074031507001c0e100300341e6803164204040e0203040d40007440084240700410705c0c0482508a50301110301140003043c215078944480190181c151000e8460703a8000603c01c0626804114032140c80d000700701016810096038521130410450350060300042c0c00005050340c615230314800f0f0600c80440e445100c4035042d98400d809000828079101700c1640d111820000141140d0600994030a010304070341610742500c81084d0401416040f0342c0c126400b47d9910802c9600e1385804004007030f40d003402a600000c0da095402c01a07007520b4168000751082c0003141e802c1c00045c800d0180064912021780d2119241c5d101c6140010160150002c1d804143e902c0300074580c180155016030301c1c080d40c003c04a03808140c450070b4400740c407043c0407901282034001c0c010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 623261438 1250 623260188 623260217
    0xe370e011401050705070f0b07110a030b060f010c02120708060f07090302060703170115020106320607080307050a031826040e100e0f041208073e0d 65
    0x1e1030300b184074600f86c4209503254024481d41c0e08458002c3c443d10710000c1141010490310140034401400201d900e002814070b1a41c54012030b40c03000302454000c0075500c0c0080000c1e40211040d0344420f84c01004040100060894545d881415101d090b0251041c0c0010034001d008440c40c0d0f90190920b0307550007660b01e0850b001e020242c4e01802d811403c00c003c00081484032240301500c90b001e461407606c0000001c0e00e1a80003401d6031042e4000d01d400102c04400c2c103010444103052142541e42854600c10b1181151001417014054110701502c003110010410141e95407040041100301c4040d20104820b60b0b040740c1c0040c160080890080c0548803400701c4501d100b0402e019108240584078220340360580790111400712580a903101146000d589205003d8505800c1059500956002d020040c500d8030352508044c15440c030303140c9001d004990010070b401e140710f01202d9030440000351400207141510908001124841604c0b0010001030b017288001c8000080380140c990801039456400e282c6021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 623262688 1250 623261438 623261447
    0x702160b090108151c02043801021c090f15171f0909051002120f090c0904050a0506091204090e071d010f1509060e370e011401 56
    0xb500400d40040c0001d208003039582d0300a0704c0170b001c130708014030b00030b10036407030310610054400a200106020900900080b41645035100d030481001002104552443c80c21f030060b418030b0580c008000e0b18900301e4560140039038000c1c002000b00c507803060408403003d1787e0b50395200d9014059002800090300041d000028040d101c2c00c1e590704040229a103204044150307610000b000c10540c01045d10a0701e50104070305006c000c0c00190b252110781c0c203065203042d442c0c1460084203c002880c80c805881e03103802240c1211020030580803a03100c0600960014201414115691071010204860301e00c43c0000040f11751001080b005950405044c03010b062900304103200c00500a020740c912441c2c840e4140018003012074003251104210461203040e05541805101c0e905079449030810100101ca03018041da405034092002000c407551441d002c95560501d2001441e200c41840840031040d0446a51094080f01c050104100c0c82c440c096000710f860b95468030b210000401d219104589003907105040c5694001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 623263938 1250 623262688 623262691
    0x3120e03010b03071508060a03020d02060703050405182509090e151005120106080304151206060203040501030b09061027090c0e0f10050c0a06140702160b090108 71
    0x100080341010700e080209150400310340c815145c000b4100a210f405079042020180c00c0707941510704421840c11a00810002d4a91120003409a0f90019011060500ca00e090720090000289003880b1908035034510b540031b2380705039890401c3c60f00700400141da00e04034280d9050102078985034003008518101c07035034005110701d1160310b4090084096841422800d0841e041c4512222111400424203100c240911002294154003541e13140c024184100880003050f10700f01c40c0003280b10020058020740441300f45503c4050420303000d00707151f4080b58060700480078000b0768000303903001c1150099902c100704420b0301c240e0f0150703000401c1030308003070440744103808031441181c5506111588960050807181c0400c80b80e8482c1264540d07607085000b0859100180d081c06d49400c41d0100d402d4840c00e00040c90241b04031442c581404000a00c00204000620900780e42c1c3d900040b04000c195601150040c01400898078100103015803007078201b0b001c100040040a840c040308565050490003001035400810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 623265188 1250 623263938 623263967
    0x130302130e0307200a080604080f0405100e1c1e11060a08010501120e1902031023090a053f0c0d1103090105220b1e040312 54
    0x100d804416190103401c100400382036106204130003e01c0222083ca000d03159135011210302c10550b0318001c00c14110001806900a90031000f015aa5440e5000b40074881c8150340c00581c2240d00c0704113020000d0341291014000000a8644141101c040da1000080f640d580d00001d0104c00f9038031604140c6075a610501c41c00500c203c4ca01e1030104880760001b8903c0d08002c50803000600400010300c076950f4400032400302c1000102042c0302194080c17200740d03140c0c41c00355100c8020710403c901801c150b640030000046203031a0b091080100807102e00d00500688001030780507982c00000008944040390000d01400c0c015001405030181010111341c110500d41088081c400c0c0248030b410841b5400a11540c1c2c02d01c07c92200d03200c642e01c07420204107d04080d10b1900139800d0100c4909180d039040004401c41c0c030204424a025030383c4d0f169000f100080e10003020052405001c00c14008684401600000c1c4040403203030891802004003002c0741d800500c1030380001041212030044114410b401000308182d00d11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 623266438 1250 623265188 623265191
    0x406050c030d2f0306011d031e0d0846050703020703081311060c01020f130f090606200c0d06051603060e04080c1011120106030213030213 61
    0x1c880031011002d40b0f02211944049608081c0703402d01e12401129810a52510709055504600c0d1110018220419002a5808840c101c0a403072807a07540512901c041000c0300031001640c001403000d0b0541c2c070030075042090b000c1040d54020a0801c4000a0310010481d119a680100c2464241c01c445a901d04030b2603404541c40d0302d80051040c1c2409000b841c0c42a041c0c1da80042e00d0703403d2030400904505020701140c540c041c101c0224004200580c015640c9420240c0e03600e07542c0d0300942f0480d40244a054443e140a81001ca000500090403030441005c8502c0380c039400d0103641d25801c46008440051084401141500e03620003451104096181da4004000042da410302240001050385510495400c9902a68038400c10126040c007144201200c0d0461500304000c42c240002210700c4540640064103850303012401000540c0100b00121000c84a000184500d40da100304400c9107802558014100628841c00801e14521030302c00d0390080c2800040c8800c100f17140d80c00380001d240c81c8030203107910107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 623267688 1250 623266438 623266447
    0xa0e0106050c1204080307110d02090a0b1201060305010606080c0f0415030b090901140c0c192303130b0c0a0609031e09030c05101d03070314010e06010512030406050c03 74
    0x503243c00040c1009040b100003542d80c82489180003030407028140721061288c00e04440c54000b40e1101907019900607030001340004c0c0d0707c044500046418140c20040350301740d82810b0001c810444190050750450b94203071905242c1d41c4810b8500d40c41ca0044800803007030a40144020041c0d034450307070b601140d01c0d100c1d403d0005c0c5040b0001c0c00716120b104115050b4240d603440f1000882078224440880b54070540d100407286c05c0081e032440158661080703034103c0f004054400303010030600c503582004203440160f202c01802081c00c440c03102a269040582100c8200d61845000201c510101007194050204503025000d000380583d10500101850401942000440c0041481608814540000e4001940c64511040389103203810305400c425034100c140a0030402007044801b503000b1040c62620040d00c18054103246007800842e2070701c9501c2e40302402c6001d0313a0002001490040d8030883c48211910700b594100c0c0e03298028045400c1c03495036115030640c8200810003d447c4070342c005e4403801c010007080d41e261 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 623268938 1250 623267688 623267713
    0xf0f0e1903030908072f04020a020a2406030309080f013c020417010b0d02012a08030c0c0607030c020d1101060506040308120a09111c150b0f0a0e0106050c 68
    0xd03039414131881c6d00c4407101195004d0784030300b8038a0045030340c90440e019031800c5241c600003516034550078001032000c1c481c0404450380d031201d2003090441c1d245039881044941d40c1d07805c0c02071640c1614811203401d40510b05510703020a10600615500740c0d1a0100140e510001e0b10510716443c41c800720041d0611211010310488940c2030008100804400164a11280b25908050f08550401c4034451013241915202801030740c001c0f1403003a5070076a42a1110705040035541c8d0500a192282d0000c18940e0008100240803c0f5680640b40c4c1d91090011140b03a603803042001c1d01141d0500440c0340140c2c5c00000f4041003103100342e612a04880c401000405c8250351813021807180e0b00f040d04222104140820011602c114500c940c540c041d1815806100d00b01c00341d2185c03a03680203084200c5004074140c41d19001400c00040000c3d0041c0d0388000c002d01020b40c0a61240018001001440d11038026031030000a54030300941998240d03422100c0c01d51040c0d203003807000d0b1495840300c44604218024942c0e10841d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 623270188 1250 623268938 623268953
    0xf140103020705060721050415020901090312080a0b0909071a04120f02030127020609180a0f050615030606130b070b010f05010504120b0405100f0f0e190303090807 72
    0x81909071a1100740c00c1c0506c5948044c0040410304021051901003044040748a952003d0300300300d5410310050303a84490000407101d0842076000900841101008003880380c0c1c0c0024007030300c610140e8100b00704003400c01003002560300058034a14050351084009226200c1a019802002c1540c052800d140c503581d0a4021210000380c2810f84100180c411618250f04082c05540741440116107404508171000c3c90110841c1c0356000e029009150100c1d03003140d01d456100c1d003030641c0810031940840301d00e011031000024110000810421505081c00303d000b9040c00310000f15030350f0384280410309540d42c980c107001240d00500254002107403081c90008500c00494011b00d0b08a0095281c0a1150b040c02c200b5928601c965018078100b000c05c1000f00503668407480f5480b074480d40402c101c45a40c49900b003c40ca054a602c8441103a80c1c030b010840000003440798001c00f241c4942d00003d00c24000700c064030a48a00f2803c89481903850200c0a41001034400d5216043e0244204c210034203021031074031800c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 623271438 1250 623270188 623270191
    0x20c04050a1805010b192106090c120210020c06070f0c0b22050d0b0106110f0f030406020708010902060313081614060f09030a05090301020405031204030b010b040f14010302070506 79
    0x1583c1d03954440706407100d42072448181002201411218844601c2c020351010080c9a00c3c6400c800c071241144101d08003c41c2d80c121901164100d10034081140d181d0224244c000c800000803407290b00c0c2803110909140c000b1a00f4602035030001c0c030150615281e0b0304c92190520050004030380d00140c281c00490030800d030320080c2442c901c2c4104040c07010360070815a804c0c0c2c215aa00050b115a644562401c0000e5505609a05540c0640b91036059041902d02c11482c00e600720390050000d0066400070b03414500008045d0044901a40c2114100c90ba15200c1310b00b03c2c0c030745010182d0481810000680c00c50000700d000c52599107d0a00c40c0d00c1c0c110140d03451240c580c0ca40004070b410000e0046e0044102c2410081c958202152100b050191300b8030b81c000580d40e1141020b40410f00101007090702140c1e4080d030541d001020007806589450703000b0b0b062412240d205010880c0c00d1281d20001040800310242580e040d0340002c15140c100504240000c0c50b041418942141019000c02aa0000840c00c2c44890f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 623272688 1250 623271438 623271443
    0x6081b0904060e0f0f01050604050f0414250e0303030c0901050c03160b0919030e010918050f1f060c060207061a03120f031807080618060109020703020c04050a18 71
    0x700b41d600300007000200100c00501702072440e000b84001801907a03110b00848003103a004958201c000070189000c0fa000d060444024071440e1040360401030040c540036030040850050245000b5881c030f00c40c80035a9600041c00c441b503015441030000800450b13002c002403a40c1041410704900700364122880920715400041c10200011002000c1c0c801c102610340032640290649000e01891003488550756490801e9400c007408200242c184403a940e40601c42c40c0020745001c40404880340c0c0e40b040ca000c050001513401d01d120300c0b02003001600001c031195501c450360f0100c024010131545000300494641510200903175007260708012840003e001c40c407400100041c140286802d42c0511020581000041e402c0791100c0b070801c2249030780030130460045a40c01106000c00b40d00250000030014602101c1341c01141c014400e18040c814601c1d2120001e076560b0f503030941141c6c07281c1e803229482020303401046030080140c0e004240210312841d02d900140d5007c02e0394000003071903400419880a062100c0a4103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 623273938 1250 623272688 623272709
    0x3150a0204091a0105030718080d02010b0f010e0303040b07051005041a0a02030601051c0e1207050601151d0d080415090b03041703040f0f031e0906081b090406 70
    0xc120070b8000e80124502000000d500340c00c1c029924002070101c0c1710007840301040069a2181454008502c0030300800341544100310780d49401c0c42000a40201540c441d150300c0303506008070100d220341c0300b51a40c01d00184045c02a6050528194001c80c090300580d1307080b2007a000c4c01001c00c1c914529482980e02c903a014103280790700340303001c6060b803c1c14000141454511350700400801001ea600081118003070807000304a80308200b09443e071480104138103841440d40b070054060160344403c0c0e55001e03140c00c40c051801d840d8242d130381e80548804610300c11100070110b00005415248204070b008589800080034004641520040c2d581314400c1c0d0154100c800c440c2d443d0103800120a5100c80c40e030000e4480070031054a182099140c18800305020200040b4000700000000d080000901102d50152b9012030040c03042d9100e1314001d030004030301d42c2041100c00c00c40d1903019a1140f15000220441d10313036442e407003044e8903a8020321840c40100000070f07601c003504000c0c00541c1d032507501c1100020884d0350302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 623275188 1250 623273938 623273947
    0x9010912080f0a06060206010b070c05030703030c0c06030615050a0c14060916030f1b120c170a111c080f040801150807060e04110d0507180f1403150a02 67
    0x2c0e88441e102d405401410400d240c04410301005030002011419142000e494a859007840d1801b400307110841d40045403d809662800001c250300003e0b1202c030703541700e403100600b110b450f0342045040b900d0b0b9220312a40b00f0240900c0c08203036809080148407140036443c254134401d14035102c4034000c0e804680c608460707034000c504000c06030070240030400807080b044c400044c049146440f0f500d4070010045002c2d00031000e020701d000e48640c0240104008000c5040529040010b80c104007102e1000340c0b10782880410000400e40117a2400725640d02c4250384101e10b040e4128410081c006051031400000c0742c104c45852154011419880c080c0c810380b19000c500c02d98550070041000e003034880ca140c400228000b00311003400241004210b24041d54064540721009400400000e00642000014004c00910000329100c15103802d401051080300345071075810081407000c0350078075800c3d00d6101e2005280f007604001d02591000340044502c9503001000c40c1c00d103003c40c1d4102ca103032000c20784d4001543ca50001cac = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 623276438 1250 623275188 623275201
    0x40902130c08150d08030406150e0a090203100504020d060e100e010209030d2d02010f0c0503060a061d04050c0c01020a17010b030f01061b08030106090e010902041d0901091208 77
    0xa000344071283c000e0b00c1c60301340b21149565106440c00b0141c0700501c01d5440782c0748440480720b045a00c0c80281180c1c40303001e64a080078040140140003240c07040e40030f070050500b061042c000e18018a80204c0e40502007900e421540d0f01d4881c000c0c40d052490000c04d01400564400c03013036a50003080c54180000000580d5290340104044c0b03004a110032201c2401420030352440d20322216424541103003081c2c00d12030010500800107d005004000b29910118648101c2c1d441055220000e94440c0100f541d240c43e40c04e40b04c6074140c032500a5403426007031a9180000104541c04c00b0b4001c1c5400c601c0c9024441e0421200c4d2900e58207980002d0702090024132080141e020070710785003003045e00510481003258a941099400b00701003840500566041c828100303840890310000a9030405d143e40c0050719a5102d5071595401890741140d0b209546c40c2001c1c40e070010801a240740b00f154101c510031b00040030f003400449110803c07904002c14000b4103540e0703502c114000c140340d00c8840244000782e58135003c0310b00c1c010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 623277688 1250 623276438 623276461
    0xb0a120e0705030a0213060503120a0f0816030b0a0b0403051501061106010e060d0510150501020321250503240d0308090f0f10060806040c05040902130c08 68
    0xa4800d8603107034041c210400c120f03100450a89034080d01561366036191407001c503651026088a51040d034052041031007120180d4143c4001d003107002d0f204e03074400c00c0700400800c00700c40050064030030014070f0b42005804200300b0300a83c407003540454090070118103542d079802c90401d660401d07803041d201500f0500c02241d181e0f800240280c05003609003030040b451102d0940c15581c07043c0502502148506000206200d9540c2e00100000158490106c1e01901400d500b010081e041080211072200320048003c155980003100b035841a03003030190041403480102d6162101c45002402d00340d00141036040c03055080ba803038a4a950800c03100e40b00c9582d00e0504180c610100c0b012045e03440202080c0e8154012213a84c0e03508006141c42d01494903c1c0030341c641041c1903013015040070a4205070310501088210720800480d0790500015064001c00ca65959040b00d152110340c00c480090444919160622a601d07142d8040c2d1040c60000c0c02034007003908031002d8141290050030340200440c20580c104191001407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 623278938 1250 623277688 623277701
    0x2150c1929040c0e060109080d0c050601050a08060406020d060f030501020301031101030603081b0f07140a0f2405070c0e0414010c0c030c060207021c030f171504060b0a12 75
    0x11294100e29501d007503150001c02981134040e144a044d2103c021900f947c2c4a90703040c03000f52450106880700c2942a440c0a0100f40742e4801c111804d0180d000000340b5842e201000c82c0882e0311100c054005a91903544a0b0000d42c010342c1501c4105980e42004610f032130302c00c80041d0213103200c1c800040c1d40354154100204008d41924449041500b4030001344001400c01c0e0690726001c601c40b4407000704441640c4468103003407441c7c84d0510396101d600000900c0c240d002001c0b040001c021303a440d85855840300850f5090017210b0040550000a0b0403004840c0b000b038501c03a159001031440c0031410806641c2c0e40140503138840c4d02900701c2904e203c081c4402d200415090001d80e030407840007080030200010014017620450309000e0180019106c2500500a46404403050305600034030b07800a0b07685035124001c840da0b0030300042d000a58040f210039000e42c0039041d4507042c0340340c0c4040c41040e599110901074451011030100c0d81c11648506000806031802d0003d094007440c0754072008080c0400b0407001088508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 623280188 1250 623278938 623279003
    0xa02060a1109010507151e02070b0a14130c03020916030b0109061b0c05060304050d0f0c03020c0f2d1002010510030204180c03050606180402150c19 65
    0x204000b100b250b030703070400b084400b595444418420800d0300024003c00404042d00004005800340c41902d204003101e40c020100c0d14402c01d01d40c5070944400c0300303010032607850f81c8103420800303d80c202162000c141c13294100302d014072801c01d103010f264507503000c69a80c40301904e460100c4041d110121400c1609801135652000e02031030b1680322185841d500600d6044240424151220b11400d0302090000b4955488050030740580180e0380e0b810715141007555411030503143c600103070100301518105d40c482c0b66a9039486802d503004016908400080105542340b0300700460380200c280b050340814a40e008101c003042c00000300305a80300c52660044c80009141c0c042c0001c116403420080143c180664854081640d4040d100000c400700b4460f5404c42c203041c0c1800c003a14800d5035180c00800c101c070000c3d49911071041990452110b01d51400444406d42003510020b602c001e24409814021042c140039001c540640011189072038404008d004003401c21040a640c0d130348a2140b5005802c8440440008291 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 623281438 1250 623280188 623280221
    0x4120503040b0106120603082805041d18010e0d0906090e010909020d021c1e050312060a091104050405010b03060d080a02070b0301090e07060203030601020a0204020706110a02060a 79
    0x41d181e52419079120050203200c0c24400c00d080501da00700d000d50b00070009150301c595466034894807150b941400d020003540c082c0e4620719481c070180c5550b21800990b012902410030010190300c1800c40d0f45041c4100800e01040383c0440554904810401d0080c00f2115500300d0103003100c116210030003040030981d90400300034400f880c541040b080130848407450441c4c490030350004940380c0c2c03880055001080902d02035880b0301d0559140844008000032b500555108114640d651186030350120265106860058001d810501002445a8000304060b0744a180201003044d82600d03403203e202150b4076800c1141003182d0102e4184007a0900388a5280500b000114540c04c601e00700e000151010308480d4001c0060034003241d40d03040a0300030840b420250010061640d12580c50300c00d0031004107010719290b000c0380305d010b01c00a14580080100c03070180d84180d000e05071082041e028070000e548414800c80e50310356102c0c0c04080c4901d405d4090031550000d50701030401e134100141c400080d140c0085241e842203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 623282688 1250 623281438 623281441
    0x70b0114040b1f0c021908060703060807030305071101090306050a0b040e0f21070803010627050f01031517030c07080d0e010807031503061b03060e06120a1a04120503 73
    0x10952042a50f42210180341c4441c09451920105a0f001c0c0e5075681c0038104c011400d004038a50001080c0a407007101c3c0c0780e6040000035a152241c0b9610541d51201230040345041100a021604402405142902c10b0500340c1842d40e5070356502c4201c070300071070301d00c4122541c13092180c0c140d180c18040d18a01c010410010f109200c0e905407202d403a0003402e0f40f0300070120000c0c401c0030a002802c03416644080c0d040903201d41c9944c1d4480c0041c254211001c50202014243e140c4070000345000f200f00404d507000500b2199540c000c0800540003030800030f04440b01601008400640845500c6c0303400d05034600c40340030b90349948058107485d15000b150780013014143c0210282101582e44501d844a050700240307044a60313074480d0fa00c2503004003820071849802c0c6101e01c8020061040980203500d007076208115813442c0151900c012000c4400e50301a01442a01400c040b038072520f01718543c0d20185e036100094540c00a003651301e0704031180d840d0516004d100c011600f00404e003c0c2c483c020752750003032031410000e146 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 623283938 1250 623282688 623282719
    0xa091d1c18051c0203150f041e120509010201060504060b070212030a0c02091008011817090108060f150403210309080703030c11070602150603120a050d02070b0114040b 74
    0x3601002c941e683c80d501c0c004800b8010f555003040b40030280a1402d012101c44d0800c20300620340840d00700c030f003661b990704040070881244c3d42e0386d410989030302d4100120804809030344a00b2140c0d948900043c1c0e046640320480490135944a01c02c0301e005007411112281e6420301441844848954482d100c04107400622980500e180c003d9020610160f044403404040da45101040d00000d00d40c0c1c119214a6203856050314000c2d141e03102d03004074240110301001c4d00ca84114240701d446c0c440c640481c0d0001f440c14001c20b0041c104901444917032b41d402481c0c031640307014845820359242c12136441a514100c03600c110852004204601c00002e081524090043e40101d0310703512124841d01200404160395010074080d03203403040f15a00059001d6100782c1c0c804035544c400081d40d800300c0080302060342403c075000c17070a107140018942000640300609541803002c18a41555690001d07810032110756007c00000c00041c841c20f07a42400380040e0b55408c0c0403c608241848200c41400003c5409100c500007010300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 623285188 1250 623283938 623283949
    0xf1701021606090201050706020a050d0510060c241103071403043201050114030f06010509070525030f02060901271103010906020403021e0a091d1c1805 67
    0x3a0250400c80128543e20984012201440b81ca0009840c640c408182085032a60200040841d2070701480300340100c1d100d0103020080414184100d5020483d080c900d80006031041c1507040c071a20004c0218041e4044102c01e0800791b40f010991840703000c20000801c2840da40241100751131400c01c000090a501e000d50750240c04541e411385000400168000380d0412040000c24130041001120090010b540c0d110110103449141c20720445c07290007038241d001501580052098100d42008203078410a40302c2000c151180c0d44040320903149810010400d11b100090001c0340841a4401e0340c0f0030b4028582d00030020b00304a8003400e541585c1e4104485280440c5c08000c0b1442c400e244414503541d000b82d03600d0700d0106070201c91400741c1c055003000c2e848000c0c8100c960191040303d00a03142c08459411202006180000402e69150700040102050100302d040b40e102c00c925000c080d41601d04d50b2400504e00740341030b00c4500116008400c1018106405900ca990542000c01b80c0d000c0c1035142e030a01c1c0001d003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 623286438 1250 623285188 623285227
    0x30506011505030f0c0c010c020c040f0509070e073c081005060a032d060e070203030a0213080307050a0318080c0d050a140a020f0f010221130f170102 66
    0x1c007001c40120103c1c5c00c0145140455405014400003006144828135004e51200c491042c0c69210364501a1080c0300d03a04907028103031080302d02c607000c0c02049090102d418150400508028200148503c1c1c051f810760401030301c50040000002e5458612440c0907181c0c003148403038100703a000c111100046c8200801c0c100c90550503507a044030440c0e150301d000c44040300100381e05030891040202c078110101044e414103105084240114209020361504c0c2e440b151741d102d00596490300145d1003000000d0f0700c41d4060f80a0543e0880001191417665540e0030114655009030b10305503805d0304000441001c05412500c040c1c0c410301015411156946072032013081e200d041c070501d03950058103141810410854144074074500b5913446105249258080c8054035501ea1070818224050440303080d102d07009183c042c0c611a20128140d0040c0460350002d103010400c1e0f006032010300841d020031712004a0880440ba001c1c1c01900d205c0703e0004035145464070301800140a0707442240c40d40d00c104a5104c030340402c40f510701c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 623287688 1250 623286438 623286451
    0x90f050613022b0f0204021e03041e050709180206071103010b1c031101150602150108070b22030b07030209011d28050a06030b030c04060b191202070c03050601150503 73
    0x3240d401300302d8004140684901c072034008145040c07148140d441440800954080d6000c0c110007500e11690030803400c1440e00f20500903000741d000c640100020082134100341c0c45006100070000500701c080d8007040c0307550058071044030900a1513501c1030550800748101d003240c1d01e003240e82840841d0040c204120000041c900601040414003e100303804100f50858642d024480410b2144180c0e550380007522507807815209020610403100010391010005070300f1003a62208040c151900800550741c0d507a103481a0480244141a004004081041051054403500040d01c0140e43c903100e000006160b4582f075440f5049240300282c2c0114103032500c030b07140290300a19641d001225031a010b0107554019017540a00e0344201d05200105400794180c00018560900368201c901d20101c40301080156002401145107480c000c1c07000c540282c150280400208035203051601c07448448404290aa1b8007241060b99015244441003007084020400d007401042e08108180040c040050000c0180c803018149 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 623288938 1250 623287688 623287703
    0x4210501020a050d0515090621060c091003022502030c04060902030a1d0604060903140307021b06071709011407050309010906020f03300901050703200904090f050613022b 75
    0x2140f091014140c40344085600e03020848ad42483d0180d98041c072588488500d0f802145000000c01c8590300030700a40d03104148800584507902c031111000558050040c07001e07a814800c5000800090300d0794811f01003c3c06442c80c0c0503903640740a00100c0281c80c080382d80c50f06000c59002502080480114200f500300740d0203140400c01c26680d081c111440429100191441c02001050080705030700028140042e19001030134095100110040003640d026000c0c000d082400552800f01c445480c0c2001424400814140200540760614003540150807002044815900004200f00c5943c2c110076207100a04130b500c0100440c070b4082031015100c0c081c3c0d40216404409d000d1601200360040c4503010714400f45c18613080070034030705030340300701d0182200b60380303031004245400601d2107007042c00880c80620440aa40603454598041e05000003050080c05c1650b0320b403640c14603d00003880901040b03000b000500102440c00035030b801041a00c001d140724140301310b842c0c56040440701101d02c110320b0b001c68010700c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 623290188 1250 623288938 623288959
    0x190809040e0337050a03150801060303050c06010f1d060607060921080603070e060d050d0c0506060121020306010c050303090a0516060504210501020a050d05150906 72
    0x2040151910700c000240030701010912494003411440c034059480c0f480761007083c3c1581803003104802030940c0f00c18980000d0701000642d00c128080e8110035000c0e01d40148120711071b0340c0c0b1941507084989641003100018030020740405403020400440f03026059041d041003140746003e41c00701c0e001c16454090070801500400207a025a240c40540e1002e54203d2020f0101416a00d00103e2503100e105c0d0011158400c41a803c41051040030020700c1030710064010700125040110104201d0310080c0326039803100c00d4000c280006281031003140c210710707102d4854040000345c91411a0034584018012410041d047c01c0d400a01115410840e015003028040182d0781d4503071b000122103260b0000d82c0901140b00c0002405001c01c0c0003d84411224028000e0343c0b171510700381c0742e41d00030f2050b07500c9080b000401c144818045803460382c0303040101103216003c09801d2082e0b5600c450aa03040421660301041c030208030f01141c0d150500520ba44098481445440c0b0000b840014101d100b0280c8502c1c0039844060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 623291438 1250 623290188 623290207
    0x306011101022709130519060e0f0a0b010e0601020705062d03010906081605010305060102030403050d0306090b01020a050a060b0a0e01030602040503010e160501080604020403081303050d021908 85
    0x5048032000748120368010040480320814012185042c3c020f64000c0f159440000e8240210000e03d820341580403024081031082c403905045903401c500c009035001a66200800c0d6001d00400c00541d0032174149000c0c0c8100d8040303040c400c05641e0160b0201d0090003402c000c0001c40e82e400314003441540c104485060f182c0c00d020000c036240c0040f0a144000540681030740e0003036420070102850407070b080d04405124a40e1182400c90315a191003505032005c1c41010024480f0358020b030071203980311a041c4101c900f0540d0b251034252920340101038400119545d42c0081c4641d002c2405040401078080c0000c2207140b140f50b6402d6594200040050074281d03030351040c030000d030f0740c0c40c08148001d101558203c2040c5d61241401c100030343c00341c850f0031b00c650700c1c19603140200e600124050b25100c600c500040c65140c901401507070892002081d00341d0080d800c200200008240c04050909207444d804251403107802c600e4803604c1c20014140c0101554403a18130b00a4403000260084411944141c0b1151141d4503034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 623292688 1250 623291438 623291441
    0x30d021c12090302150a0b150a02190c0e0f07051c0b03150a0c260a090f0f14070b1e041203020d0306090605090f04380a0506060306011101 61
    0x1000341d54042818a2090810705900082802e00808400619581d80e11004a9901200c00d610a0030744c0120007416801c0c003000010003d01203d100c54010384241c05200d80f405c1001d81c00c0c4843c00c0f240354049400034010203165026542c0d101e100d001140c000f604082002404031b02545150700e041c000e10440c4041202c0040d0001021014040c0889070001010340b13013070312801003c0399500e6119190410341a15030f442510500044a071f58564804014003240c0303941e02144000300013211554640c06120001000d400102c04c000c1c0c0912101c5000f03038028a010304aa01020503000155404600b00340003e424180c21a423103da0034803004040e0000460030030b0058000c0b0b80c880e0b1840980d003414031040c10707008520707281100e90300c0d9000c00100d600c40388443c040b214540121a0001c500000040f441120022440d40181c0101801d42e525a600640750901001c064213a49170000c0c00200d02441803040c0c2c045a400105000d002d11a528040d00405e49601004020743c1c1000300400f001d0121a00a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 623293938 1250 623292688 623292707
    0x40303080f0a09140733050a020106030b0a0603150b0a09091110050910110309090c0d0c0e130b0306040b060a030c08010b0a0602010b0901050f0f1c060605030d021c 72
    0x42d18400d15900e41055601c43c80c05200b004181d01d20884030320800c10b1040801001e040300c01421b0091150710200131650350300000f21100a540d61900c000c004902c044441e00c1c0b080141030004103280f4114900300114000c0001d00d00601d909101c104640d03a99100c0040081d294035080001c0c0e0003400e401c2103042c034491a03051942010b2010a03041546a122000f4600c480c02642d59015800008204503444400c5c129840456041889680c00340c7c50000c01040d000341000042504007071358074103098111101c44060001180000700c0e6500c25091022a40b00c0643d1010b07000c0001d0140c107800309445103402400106290840c0000450356920525098060f64201d6100b1a50540b41d0f807601e4020500400d5151040d8847c0e440011482d1050250400f018400382101c1c180f82d20340018002407041048506600111040d80c280303458031802c0400111f031003102c2004800c0c1031241080f0f41111030076004039004c0d800006401c00507a400059840444061424840c0d1a401d0f405044411410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 623295188 1250 623293938 623293943
    0x21090219030c05010f020a03030c0c05030a0e0a0f050d080703021c0f1e0f080411180f060301050103031e0905040908090405160f0e1c0f060e0102040303080f0a09 71
    0x48010a030800501154114000e81c0c0c40303031804000385a110001910608041d042000050f8018955480080d200e50404c903003481c0e49061005120308195111030568010184400014001c6c60400565160604640c402420035001d001141410800403601e05400c072400588480c80c0010311a007054800c207c411070907045081100003d5140c91802814152600b049e00300240c1d0b1620101441d03a40c010104030207908517110030040c0d0742101001d032582d04000b4810703148601c4134124800c030f0341c440100c00403c2d801c48800025041c03815100051006c00003401d43c074080da2400005000094001481c01e40000d0741d0068484115100c46044501a0f01c81c0c001c103402c181085425410408000c020b4480b0480031102840546c2d14070302a40c0b145c1c8040840900041c0c500c100e074154580c01803c840c0d01c03181025151a40124184481c40301c882d0310120b00b224407400300c0c4552000d0000e144100e40407044064003c1d03140c2460741e140203211000190100030a01c2409020031140a582d9020300c03800ca5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 623296438 1250 623295188 623295199
    0x180f0307030f152f0f0a2708030c0601120b07050304080c12040608060315160309051c090f0b04170c1509010f020f0a03030e03162003010c210902 64
    0x41c4e085241c007142903041d82c10b01d210724404071100d612040a079041e141d80307201e59031a075410310310100f004640340390179001c0c1e0484c08900c0011030759000b601c029142d0007600d4500700541c0e03588524410285400d4050340009888140941c6000001d084a0309aa8200c0c80782d1828580366103881c01c04103075611130781d00c1414603881690441c0c001c40031804d0191040320101d40ba055001d946c0d8400703040c0c8071003040c440007a0768070101e00012441d01401074407060a0190340b0b400035645a0b07541d51b8528043c1004100000c08500c1c400540d1529400990341016103d80303030010507900d03d4000c500006014a00071100054004032901099400401c001d40d14144003e0500030040e20000314440386901c402225800103100022902c2e5842c0001341c00d0750341e505150010003804000d030f1001c400500d02e181c030346179140c08100820100162801d1080b040309014102f008007100c6150b88154441408020b00d03406a41032541024200d900201d4860000c1121b500d5200d80d603451081210050000440095110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 623297688 1250 623296438 623296451
    0x50307091701061401170c0c1207051501050a0e01090c03020d180c0f0503060c0a030207020a0e09060a060e150301020c01020a081f03080304030e0d1502180f0307030f15 74
    0x908054000004031495011400a13819070f01c4011a0241031403005d4001d001c0b5600041541301850070020851244a1019142c2c14422042c64030b0465100e02003d55107039221034441040003901980d800d0040c4800c8a00041280c034005a94030000014403910746040c0d500d040c4650390a019404441c103442c0f190904108141151075509139841c07144109958050424001040d0182810403003401d5682c0280145002e030f680c40346994965000724800e0b400c041d000d100100c0103071180d851540c083e090021801d141890100245031070008000c00d0020030741d003030a1041111a006a140981145042503042c012107203800109001e4400c0d02507440856100154100c11107512244e0725004080c071740d440d51400070940c0401040004107020140c0081d03810004240001e00031448608900b4020b40b110314a01d0903500c1d140c444208035419560700580010340586a41c2014803060031210341110340646041012012943c3c0300c04500008000740d000d40402c50911013401002c2403135008081040c0442d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 623298938 1250 623297688 623297729
    0x170708030a020d05070302041d0c040803030f04060c08060f0d02011e05310501200105070305060f0d0c05010f0e0319141b04050c07021003150b030c040605030709 71
    0x962150300f040011510740008110340610900071241200c0c039800f45101c40f0f11000134003d0100001070040e501c089020003000804100a0000e94440c40e84004180281d14050401109860b08102c01034100110303902085400d03600e14802c03415041d0241e40d00d040c00c55a910059030480704002c00764402007660400726210b1940203008010303014030301d0300c9a213001d22183c01e584100c0503c600d21600400c1500014041c0d03500c0707120000e4007450001d05e0052005000e80c061800c40e2401d848480000b03031101e0402050f828030100350740100f441a11140d038100c0711500c0303040e01c0c1d45140c01014108503810094061081c440c104200c040c000c000c05a5088500001e804169610003807002c55a000241d460502914000700700701c101c0700c3e0103580c200300c9a580d24003003000801d0000e00d81c00f559403040c007134030300561256010784441c1007080c1c030009940415010742d116001c6403540549003c2d04200100032244540703070296030445040d42410754894581c0c041c1075404010b546c1000c1d00c030904401c21a0301c07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 623300188 1250 623298938 623298941
    0x1401090b070207061d0d02010c06050103060605040605030c0a150203040e0108150108070b03070315030812040b06040605010c1b080d17060f060702130f090c0e06040203090a170708030a 81
    0x4036401d808a0f03020680d6460b050b20411039100c280c4104810300d50500e02c0b40d00742800c07246c00d481d10516001e091112207543e1a000c48201380c0084e10700c03999988043c0410b003007510814000c0c08088000f401054030802c00100d2405c0b80380941c6840380c2e03948058186090007042a03c01034000c0b2717440380002e50b1f110b101942d50348004150021444082200003c0c24800c0031400b802910800e0722154550350b00c030b10095014003d081c20350500c1c0201010000003103102c5001511444509910195507400e1604020304881c0e8040c10341e501c181d19003001080280e800a010a0205911500c80084145048a148031300c1c0d02c507601910340c80c01801c0040302290384c000c0b039001d101754020703c426455860341000e20002c4408102d189800072810813a031005403404002084482040880104d00c400c2c6030309900e01600c800000880b0b80384070480c014080f40782d084032140d900100c152421400e51405240c0b5960351211200c2c00740c608590480464003503032449003210145c9401c071300199035030b0504c0c440c42c00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 623301438 1250 623300188 623300191
    0x60b1203180f0603090613020109030c060f120e03070f1509030f030614090109020c01061a0a09140a154506050f1803160806070503040b010b03041401090b 68
    0xe205200d20304a80d01c840ca071003c182d901a510110007008542d5030f0300b0a105100304000700603418000d6003900080065044060b04001d44074581c0e640c0848642a40d000c2c00e000482108041b400b070411050408004001040c1d403081a00074030031001034003540c10105209010310303480380e190a0514540c9028103410025000e548402554100034180ea210340000c040e031200580790703600540220040005001c143c002c0d12101d031364000005481551102e2042130b25082410790410445c02042c150b0046400400b50401080d02ca4402030104550b040010544101406202104071030300300e000d203050b0300c100410b180c0703600740c003100c1c00c180c0c809052108101c0f0410201d40005185140506103009102d044803001c60f8010f48400d82058008042e051046e00060415424408100900b01c0107607010400648100903000119060504265805091100c02402c54092200c2042400000ba114801c21811103030040506a10b03a119440c0c031244082844540d0503ca6082c02e581005111007071008a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 623302688 1250 623301438 623301487
    0x60e06180109080d05070215090c0a090203100b1303080409061809170c0c18010608090a0f0f03120e1006081906050612060405010501140616060b1203 66
    0x800482411550407402e031044244000e100c00c40600884419000b250442c5811003e0340c0142c03803c030f136004a40107030030342000c03034080d0420b5221580d012001d00b0541610b01c00342c02005025841c5280c072040071440b08400380319450f455140010500922500c0300b0b40380014560000070542c0c0ca40e500c0440b03c02a010038000c0060000c4e09400145042d403140c0b00e270800066004292008800c01801b07002ca1035041240d8000d82801003900c401c10325544c0002000164802c19142c00203541080c10041c90b0fa04010404002ca6005150680c00305d541d418040030610741c00104145201c40a01c3d045130201c0c10680e82c10340340c5042c00c0741da00b10060040781c458071004440004024056031441102e564046007902e600c0b010009219413000f00310b064010341d038095005403940d003540c003400c3e1800b40307003c90031a0155881c0c1d55801c01807011001c090300044041c00102e40042c2400588009881282d001a000402c180c0d502c14600c0400c0d00c03400760345507644e20302c03509a0342c4401d00207a800c140c0c0d90321078210 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 623303938 1250 623302688 623302711
    0x3100e01080d180815091e100b01141e09060a02010b10020105010f05040504060209060c032106130e12040b040306061d070f0302190c12020a0b070c020d060e06 70
    0x10740f0340b801446801d8004507805040217014a01d5070700d4a018a0b008040e00c95403039070007001d11000d1103c0c2505880d20710401c2190041c074200151500880031540341d81032490410a111000514250441050700c507010a603940e5100310042c00300ad00100b134810360035519040b40e000f00303d8100d0750381c06500030400a9015628016134400341d1000f282255800d0103040d10a00740540d0904c80317070a1075070000b54040c0c0300d044010f282c01c043c00700040300c64001c401d0040040d030001039a29400304070f600c5040b64610000708081c03d80d003407810028860740d1100140c003807156541d1140c2400c10404024583c0d8403240201c00a94a6440d446801c2c2694030500066032158102000010305031003240a01c0c0094031082000c01740303a02c8900c4215085034428510400b056020b0051042500103130400005031207140d280e184030642c0520308070003071521083e90360341550440842c01020801403804182d000a0074500380b108140548001210a00d030b0a00180c041c0c0d1910f0150a503009001607002d0266215560 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 623305188 1250 623303938 623303957
    0x10110a06052e050105040909030c0606030605190203011a030603150103060e0d0212070b06280e060d020f12031b07080c031609020f0c0f1c05041a03100e01080d 70
    0x2c1510348000b038814180007030310402c01000f0100b100d501030b00201c0d100b0300d40702e40c01940580701c1405941040d0410340c0c510340e80b00c1c144040d419401e0701003446081044415802c540c5410b2009440702e2908070030740c55410b400000a081d9503000d0044c00c142190402d540d80c80c9584034241403000346004480b10040f441100441c0724850300000f1451003160403540c1c4145448000c0d9210b0301404402b9000f41d03044030007058000c0485480503d094101903203900320a804916005d00b80124101c040d0101c0d000394031401e007035000b41c1c440c107507829100d14041c2d07403001c0c0009910b540c2031702c0c41c810084116489455a41c140d04111404507010701103a4402040301c0e110900c1004240e29070300c00030400708002e03494880070003204501c5e4001e4001c06000070341e2a8101070400c243d15041600b00003207000560002d40b0704101c4c40c2d01852160060f50018a48070b8185801d020780d41c0e40102e1078103046c0701c20410120004400c14114420700f406000c00407190305a07540e41d0605030380d50340c85000018010958410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 623306438 1250 623305188 623305261
    0x120b150a0510030e190b0103170c06150f0a0506071202190501061d06010203190306050d03080906010b0c0a0605090102070f030918110d0519050c090a1410110a0605 72
    0x2511754030429007010054440e6443d5549004951500071100b1600f100d061283c031446000501000340310750101c4c490011910754041c200426481c03884545849404048003e210f1912110b05480d200395205880180280701050168540445d143c001080384081c061030741c082090640044044810b1619002d02440b081c9884141018080f90914016441481203140249040100d40d888882500740000c001d83c545c0c000c01d0b40044030309001e07000324504005125010700d0030001030f4018050003200a041460450b034054460f80241809000c00d5103400104001c02d00a60468440a511140c0000440d0441c9005885041706104642c5c21940d940c3d44500100c0baa806081012210791400c2450170f003038001250300404003e00104c561029030310a07070468a490b8401c140c0070b1051046455110b40c601001c100c1c013440d40360000c2038242503000d008615501c80f0101000340800300e003005030340380b000055540d2400d14100809810030b070400d4184401071034400401ca1005041407914440c868081 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 623307688 1250 623306438 623306473
    0x10b07051204050f09070c320a052e0e1c0f020309040c050d05010603021b0a0b060603220b07030507110a03050f0d020d02030a06120b150a0510030e 65
    0x1445000d4002040782c44110861501411486d40003c0600f84081080703010b4541c421051104c0c0c001c58640e5422140d50b200c008804220340100344400c0005140e1300100f81d90b0252200c20340700c19841100c07000c110501200d0103c02e20300d61070801030f0f041084811200a806a90f561480c140415154201c0102c500c2540c071404a81c0902203158008502d080c4c03200080c44000c1284a00340c0041010030301031782002031070901881c1e0003010b5a0754056218144907100c030388251802d80208165500c610500400604894441544102c1c11180c4075181e65444210b440201075421000b4005154440d407a010080d10300001c500845a03a41c00300100d641d45082176424101911a68003142d01207c1c1010000e13204000410108038440289401c1c10f40e03501c1030100703980121801410a9401004004140d10300d0f200d000c00401031345018850400d0551194115480054840c11250180200c008101e4441e0035520b0018640030300010140d10075040d0080c01001524061122806202d506201c0120007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 623308938 1250 623307688 623307697
    0x40e1b0612040818040203100906080a020a0312090302030a060603050613230c0301060f0314010c1205220f0c140109090209120708030a0908120f0a0215010b070512 72
    0x81100c250703507680780d03502e0348240340d00701c004000074043c45803041c40a00c0c0c40b01d0010b140101c10010b14800c1803802d2450b40c0c0185c1e0780341d80082c0302e10b502c003443e81c0300540d403200d0000040300c2d0402c401e080c4001c61030100f145c00c01e07a1500065050f200394090310040000591001c002c890180c003e844182d21002d900b041000d0b1255005003d02c41000c00d41090407a1380c2220100b100030071822121b104146c2c4002c00c0c25140154000d10240070140b6007042408030008401d9421001d510003049007101442c0701070125590221010a42075448000450180541401d80d022030b0b01c184183c9031700001d0740f0b020064920354102c03c0351308030381c80c00e400584003078901500c60700508140c4462214038140340c41c80000b90040d00343d4030f9000c843d00d006050031110500c03c0e0005807a094000c1d41c1c4d20038481d034020308512204d0340182100da10804412510449040941d8407005401402a549540c00c0c00100c1c94903900404091078045100000248910030300002c1808038410002e0300c0f201d9104ea004c0c564103004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 623310188 1250 623308938 623308957
    0x100801020a052b0501090911030312010e0403050405030a060c1b26040b0301060519050901090303050c01140f10140307060e060d020a050d0501090905101505040e1b06 73
    0x3408068000c2e84900d0b01c0d45541020a540e60102c07000e110400420741d613082c0d2000c1c2e509940c96040d00c003406601010111220410307402075141c17512010300105100414496140046032407004202007510540c1220020310000381144d00d035048030b0402600401d250fa82290200d2201c60310011441840c4089100e242e8000180f9070b20300310038004401030414640c6804076074075800c003c04541c4000b5440074501030030441c0c0d2400d44603c155100810411004207509040c081c06118010706c40c1ea00c524500d050340d0307040c0f42c280d4a5411480c1280c0c05080402c04942181050004100600c8211340e2514800e9000e903001d0300049548102094101203128003203501604001401d114a0380200f100300e045010107052036140040004c042c030100c1c4c025140c6d1a00103000012401d846040c00e020b014050f0031052003c00a1030a190f4460b541c491860861040058551088114504090440b54014840900709004110402c0c144507164200c681546001c5840d0454014140c106082950340c080f4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 623311438 1250 623310188 623310197
    0xd110d0c080903010207080d060e010b04140d0f12030b10090602120a020703051c180e040221010e0705031c051611060a0509040501081b01080411060c06100801020a 72
    0x1541915a101c942c0e106001068156400300841d800103060b0314020030b80f13016010310000d0054203040c1c4500c5511010b902060814405003c14004040b0800b4801201e100843e251b4000350b0941c40c09040b010030b50807000c0c0003c41400d102140c01034068001c81c0461208803428140640c00b80019540d20800780140c03801640a5111942c001c503081d0000c1c10000081e0040701e2503241e4036900c080c0b070b100f92811010700014075030001e40391403a0003035144407582c00030400f000c00c00c2e070030000d520f4041c0000400191107580c20f968040f01800d9600841024058008000c0c81501ca002c082c030b0b0b941d00546e100d428002e01c1210a0a803001c1c403c0401c0804c1c24070983c1c0d40384d290401da040e2030311007482c0201003551341502d080301c3c289540d501c80700206482d0441791100d54a941521003000225030050740704011070341024007941c28980b00ca402004d50f840c02402d089c0d0f615156810032088502d240700c0c80341d810181c001101c003c64500043c40c0c40c420f10044c04400303041c9840d1a9418240d0081610110214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 623312688 1250 623311438 623311457
    0xf0207050709150620060403050d050603151311030105340807080c19080103021201060303020d110a02040e030304140f0303193b03040302091b0c010903020d110d 71
    0x1901c50305c21080e0b500d034140401e90040026402c2c1ca41000c03c103483c00c03008600000303035003054140140611580840c003180a010b926041c1c0a00200800c40141070031030030750360b0a0707003e4208081030f0400c2d01d03201d0000c0d000300094504480d401440c414011810354443d007500b0646440d545105846e001c80002d0f41e924442162102c1c030042d81c040300040c00c0c4007901c003002e01116000492482c0b00d03400c01c21a030f554246d20395145005020f0300440c0301410040071790401e4000d001094000075080000d0a9034a031501d0780401043c00c603800c080070010000c1d44107090012122554000201460145018046040c007019090110030b554000204900055800c1400020500308000c408201d40052509001c603968400080b1041e000385442c031441a0003600b4401c03441c3c588407860b6658400e5007000c00942c03601d0300b0350300015080366005000039840340721041a80b0078881c00000b95582c01290301c00030f0044036580d16001e5165010a06a8800110110015450107100190000e50380c4503645895041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 623313938 1250 623312688 623312699
    0x3010f021c1805190c0e150105090303040509010806012c01030b06040b100f020d030b0a12140607050c06060406180f18030306091107150f06090f020705070915 70
    0x6400102c00c90900320302107145000100e2000e03c440c02d500f00249249140d40c1e07155243c002100d1560382c10082030f804102c010009004240c804040c90751000342403040d110310300100000e146205503040307507400c03140604c000101040000b444d141078500d0312a66025990000c001480c1c00c1072468415a40f540c0c1350300040000c10b00b040036071608658040d0002c1a10071240b00400c07145940c50703c0403070000d10a0305012107107070f41c14400d401004285180600410b60607100181d180060390160300d44a40040c004002003046900204204401c1d050650b601c9103400f00c00034005800010380d401c107074083e92002541c00d20303141c403c40c5d040c1c80071800c5401d17136103044a10b00e4000f000f41001024066643c1c4450440e51301a50a007284114425a000704e415400d01012078203940c10fa8a8404c41e94030144140303800900c0d1050f002d01030343c1e0358290003e1180c1c17001308104054035560b4880c1000e01d00d0003110f40b91000880d00103002d0503000b41d003200c1c00d403562100c840342240c0c00040d040340039442c840400d100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 623315188 1250 623313938 623313941
    0xe031e1006090b01120b0d1a040b15031f02070b070c0c0e04122318030f01060608040206180409151404080f072301050402150327010f0c090503010f021c 67
    0xb8011b0011300350101d207110942c0c6440307100e0903c600d400044140002004200540e28184550042001c140d4150b0034224901084d901e41000340c0603c24400c1c058025075031007240343e054641043d0400d410880505041e03001409282604100b681c588003041800f040802c0c070451050b0046511840300700341030140d44001c94274000c035161080841c40d85d04080c0d8840d4403100c03003d010061070200d12204c40d54aa01c4c00c140c501100c131403a0900c140d041c2401000102d820035400c07640207406581060381e034201240341c00659144184160351180c0380c02281c07000c0c01003c60480490030500c8004205088440211141d08141150014800c0b0780401401d01440316203805001ca481c0b00709002c0d807002500b8a0300300c210384404c04100350b542c0e660ba0300b0081945085281c031092100c5094482e480c40c10804800714112501c20182500e02110311103895000d0001d43c0091111140d0020030004011905001406a1414880c05201e50300300b10400c08100075034422920041031001c00c000c10541114005030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 623316438 1250 623315188 623315201
    0x80f0a0809040b060c0d030f1a030c010302071401110a0306171b010201140a0e01050615030705070c0302030d12050a020a1d030313080a0209070c02060a0e031e1006090b0112 76
    0x2c2d00441c4c1400300041c1240d00b0003207880c45041940380860b490a07c1c80500080702c14003801d4000300c09170b00448039880d440c00700e40d0010507002841c015030341d10002e09182e0b9813007200603681d01e11980383c0407024007852903010282c440b2801540e4207000c015540c202c09403003c00214075681e101d41040704030183c0b03c40703e40900140b828041c000800e021000c41294242c542c801c440d02d664068070b40440206a520a2107981d510440c2182d2001190800b444050703118000240343c00184280000d000b001c1c08240841c010080d503000f41110b00107400d5480042021031402c0d04a01001d0900340403c4208610f8003e980320507146584100020940307001c0c490414201e008002c2e0540000c1008214040e40a0200070240401074001d103103066a910600c50b9030079000745004200302a040d00c0c1c2c0b0069840c1000c0f140001030900d840c101c03000d0284002030a140f092041090011070744442c6035400c0f0b00119011004018030b010801c0405e5490b0b07240300541d0700c220000d5001079040c03048501c0a0606170b0080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 623317688 1250 623316438 623316461
    0xa030f15080616032d2007030503040c230f04061a340b060a050a1701110a260603060f13020310020d0c03060b0a03020702030f0307060501080f0a080904 67
    0x3080c48502e24160300040f200816001c01009080c0d0100321010f17905005013950110f0a172001000300d1607404054100b40920440141080000004941841500030303080c070140a8000f910502003000c01280c510080c1100c8505000b0b0255a0707080c503243c44e103407140d0001c803190040361141d03919021030b030b0055070b0f40510002c3c03118001c400c61240e007201d05c1401d0031100c4c444030a019102c800745418842041c100003081c60b482081c00b0308003441640c9440703654100b00d80c000520020725400140798213024100030305c410214144007090019501d94001000310701242b00180ba0fa036107484403111100390003c2102e000f81c0541c40480031030b64400031249019400040122010f461600a80c000fa060401e051807000c1103580220706162041030500c55000004124241084450b1070a20001a20b005001910041c56030114503c1705546040c82507444021188003a650384041c1c41c5403160041c1000c1c0640e1190f40b081c4c403040c2450100c000362512440b074000203810300345400d05081002401c41440da5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 623318938 1250 623317688 623317691
    0xb0306060f0d0f0b040b010e090727020706050a051f120b04050a0b0703061d070e09070306050603040501050a110a0e19030f0506071b0f061505060a030f1508061603 72
    0xf5101013130f0000d035102d000b00c2c890482c0c0c0c1061b526080390300080c1c0c07401900c4426580c110310010810a1449840b08000121142c0d10703411008228080f10000d01800e85d0103030400d0f00b400c0030059000041c4c1d1000b841840f0003c041445440f03090760a606030300140c06074500c1d496a106c0d100010030f0b0300c0d003d03407540907201e6422190501c3d02a03545602c000010b450880100792a20400d01076000b50151880c422040c1185291162501c503100502c50342440a03075600641032940400d0680e4402d40100000d0301000e081e250342c0c1c1c10030b807a1203402807038116103100031240352044110000c07041008032000c1054654404008240031001c20242482050140410114a0000200148003484844609801074020700705500e080c41d4080d180300301e0041810240d00d0100380b0100010320304240308049a800042c001010f403400c111140e080c9a10360130103075001304007051114603260300d1307004140c1c1410294018054140d00f05d503003003041001c0b40207400c8140c0095001819003401c00c1a00e0441000e580340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 623320188 1250 623318938 623318963
    0x221040506040305060601081e060d0c0816090510050a0b0310120305070209010f060909020903030d020f042d060507052b020f0a0b06012006070507060b0306060f0d 72
    0x303075540d02c507920885850300301c07500300001581c20800c100e40c00302c0364900160400303000500c2d40640c1c40008201d0b43c801c0c103000c00444148655090450b000d4550741089910301c04a0000201314000b8600c5190381c4a400c060028801d084400511000c69a0141000b00420b0400c621044141c20041c01c1e030403084150240040c00e001c100c0780414443e4041d0311141e603030707001c80e005200c400b6105070080540c44030f0400d070070030240c3d502000000854000e5180182c8403180c210010b81144540a114a80140003103504000d00e60301d64002c2c800c680400c010241190444004164400381040c40b180c0c1c3c00e0001c140400c85140590001c1c50b0403882002030700e14142c55418040b08207201d010302290649069424658500d40411404009214820092025a44660b652041d05000620b103e04000944014196a40602d8a400b540044030310948606203000c0c03000038115081284255612402d00d280d03000c00c0c0c1000304a00c0e0080d03401030b200c3c82d1513031011410b12100400301001202d40915191 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 623321438 1250 623320188 623320199
    0x703150e030d020d0c08040b16032a0807020609150601020309120d030f0203040f0f0305040b040b250b01090c110a080901031d0601050d0212061302150a022104 70
    0x100910b0b04aa10600060b10341ca18141014100d54000c039040d001d00002c2c1c0180804a0303001c3c003045502c05e20804a00a005404480407800380c1140f0307000d01760b488080d030303c1032004118101c0c0c180ea0380a083d035152002aa641802282d03590401d4485c00a903070080b0800c9811850040302c40c0764000c0060044901e001e40d586c02080c20840d244800d1006078002405030301c10181c0c980540550381d8081002541141003a0711601d12841c5051002409440e464205100b094007940546000b00316000076a81c613241d6a444060b460b51002050054004e00c50000741e01d1140c110f03140d948940d802a09091140e1f08001d000b40050800358084800d02502d0709031400c04560421405112622a8041907141d100c07034030024003a0b1b4500600c0c400360300751041e2003100040c4001421811500219040b5030034110070300208112032506000300c000303030161030200f00c026030b4030700c10314110248240da4800b1b075100d2421011081c0e0282c40d01e84401a0414103a900c1c0d8030b11503054910490000d0100e06241c90b6844 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 623322688 1250 623321438 623321443
    0x3080c1c0603030e0109051804020301090b0c0919120b0a29090109090231020c151602030409020f040b130905010b07020f06070f050106270605030703150e 68
    0x5049160a03591201d00500030154411081e032500d0000b0300b00100d41c02e04100004403603030780b5680c80284e9115550005019035600f50068241540c004a248040d13040202100c00c01b40e000000203801054007040940c01c00420681c40000c440b225051001041510b070380d810300b140b401a11813805651102c50303a030b20503080d00d1109940714003008000344101c080745040c009020703c142d00611545240100101c0540c88440210b80200c000f820029040202c100d180740b1003105442e034410b0320078030201d034004412500044441c201c00029102c201c0a0342d0341400300c041d011480541c1c03001600240030070454034655802070145420702c62041f908050300c0e24111202c2d500800103915414510700c0d000c021104003403080764090042442640c2c13505601d0b8012442c601d40400045000c5c03040001e54200b800407210700d108c40594020020300c600740c2d98004443c00d0040c8a044814030f24034072140ca20310480a441800c003151700c09400b0344a0305181d5103c482801d00c0780344200700b84a440d000750000c1a54107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 623323938 1250 623322688 623322727
    0x605030601090c02063601090f060b0f1f1b02030604060b1903030f0825050408190c1502031b0105040606080c01140d09021804030206091903080c 64
    0x7030700b42c0007880c410803181c020319100e00603080d211416180c0f0000ca907803101c102c050841d401003040d400300c1e00113a401a114018000c00c40003611006140d036460701003114a402c00d0402c95000c4030140b8524a084003041200400f009150002106080602111600078600304900d140d9034131004110f001c032900880d040041c2127400b02c88196488224010915010303107240b8055542001c0381d0285401c41d0b80c0501b004200744041c0c824050120001070002c0d11201060880b4034510028110149050380083c1c1140c000c2c2c0100d4240c1e02880c0005510440e10301d5085070907540001c4a04121441c2851440711a030f01c41c1104021808100641c0c02c2416044040320b0701c48210f00c0001803149411300b00001152190382101e49650080403031307558640c0e80101101100107801036020b60321013034401000020158968001c0d0080c092501001244102070b0781207100d070b0b00a40035107080d0758843d80e04a4031a441d262174140b804880c80d0300140800d2040b11181e84c0010310100c018a0000c1c1d4a1480382425003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 623325188 1250 623323938 623323949
    0x9050906070201050702030a0507060506040b030a0b24220e0d0e090115021e0721170313030c0303150e0405070e06030316020d240e0309090601120605030601 69
    0x1805101d0000ea0922a6940c0422144041d40c203115250000500601c103001010745490780300e20200d1566030f5079034420a01140010111600c6c90918501030b402c803502103c4c17501d011140c2082840040002e1403c80d0342c42c0b00000c0082810142d802c102c0440420780c0784602c05002d54640c200b1950300010000e91514194607203a080d034495452080040c04001600105d4461840d0503821a54075000100002d9900d15444186108445026128641740e11a441031845c1c02c40c3d80c0b000385c1d1107501e01034194181c501401340c221810310001c620040c688000e50f45c6005e028900340c0d02078046480b03003100018852107441c0100d03007070f001034014070305041e0550801c0110b030b0b1075101404200101009040010800b103d902419450050700003616030095021602d07120a07412000d204540d00e81410b405102d0b8403510305140089080ca2406d0100c404009030245c2918010315486c03501000001e50b50080300007840e075185a5a040300449416a800d1104074000d0385603400800c80e0343d41030065601911 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 623326438 1250 623325188 623325193
    0xa0305060f0a0c0503040f051f0f0e03040f03200441070f030e03040806041e0c030206070503070b071d04060f0303082205150115081906090509 63
    0x1014001d412481902610b2a103426142403040c8107a190040260303544035410801e140c003425083d041090400c2c41c1205096000c100d0310f00c40c040010000d60090346441d41e400010400ba0030865100b030707940d10a80c02140f01c0d044030007104200061558600c1c03280c0f6941c80d08802e40d08008000400d0039500c40d0f0303040c0c104c80c413500300102d20304180b940042c003401c100040402000c0b44000c011400d0804015140e4001c20045240002d1058000d80003012140910011603507120350318172f18a83c50b06010358085541040708550f00d191451021114202260042e00c0103429529660800c403140d40006000c81d5640030502c00b10001c14103984169200e00c2540e2941e01010381d800201d409001c080c0301503107104501d020818441044d0604100081e2640740c00c1c0602d5a40314140404c0da01b4045d01d00d9240c85481401d54642009000314503100030204400981c9e4103a600d49020901c0c2c6130086098000003101d450000b0100960341c0740b0f08481403110600080c0c00c03900ca4480f1003e4410807107540040b075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 623327688 1250 623326438 623326441
    0x601052106012d110c0319050c060c06010b0d141311060c0c09060f090103080d050a020a020c040f180b091203040b0a05070201330905072007050a030506 67
    0x558004880c4100540000440c880e00c60003103285030f02410b100c10000b4100400780b096214002020002c0c1d00b000788004040b02d6814143d80358410400300c0302d400460303860060880842541c14500291801010b100010749201e031f0030420b101301c058100140c0a070710551290800300c2c601d01d8001340f4901408840110170400d20036420110303c0140c010b400140502c10420004010850200302c40940c2c0d0411105180b850310381d0301c0020f401100074200d4580c0440300d00000410400d00d0b8008100703040035404144510764684079644200c0c0a80101c04001d40c004d0148002c42c4e14056204034006400da5000080380c2072005444030084000e8042154181c4070141403141c450004c2103099888180210028914600f540e40e114409601400490640ea118030200307104c90700079004020003a080780d0882781c101041c910301c1041c0001d0140f031901441030f5004041140070541c09164400e540c20344585406208410f02e052945000d2000741200303000318100814160340d60b13140200214010002400302e03 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 623328938 1250 623327688 623327701
    0x19090303050a0c020c0a060518040c0f0228110d05030a020102040317030705040b180303030403080406181e17040b0403020109060e0a05060903030c1006080c0609090f06010521 77
    0xc448480f4596419035000052032601c80d41c54001240c1941c42d145046a101c0103412240c1c203811800824203030340507051000c0390850607030110303002080c4902c6030300321240c850300140b0141c1d000d0705007014400d894100c3e1411401140c500c80900041c20030140c513400f8903140c0b507280d843c110b0300080c0c01000140d40020f010018050a460848041421582000e2035424100f201a10300c0c401c81c46111740080c404520110040c40b84911903d14110280580c0d960380307050f1800804140049030110b41c401d2518000301010012042d410124591010407040726404101d50b15413034492403a000c650460b42181c40155448441001e00f0081024426854455007180300241903140f141e000701040108d03407290715100d9615503601600300d0b00e085c0e856507500c1d8501d101090941c03099040301022841200142845503000c0e42c0040c040390241c60a9030071180138178082003010721803140034075440710340c03000442c0c1c55126042616810000504005141c8001d050309041c400746800c44241361403030b40c04100000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 623330188 1250 623328938 623328941
    0x3130f11030f1b1c0f050d080a0203040c05061c0e0f0d020d02030301030f1e1103070501140d02090a15050a09270e07260106050108071719090303050a 66
    0x118003124070050720a01141400c0030241079900301c40648101842d5100ca01d8008400101415190304500e07004414000c1b41032031a96044886003441c0011460f90020300c0143e0386100f0b0364010ba40c82640b45605500c2c09041005680000b03807030700780701c0794070035241ca0302c0322254403031404118200c0b405005e800b405603e2040c18017078904040c000b52342014203014012580401105c1c1903e41c81001468101c0c00ca042c5415000486541841584e802860704070601040e200c4201100c04100d003100d144079110001159400e00754400046180024802908500c07165009041c0003440a44005450b583d10700c030000303000031701e90380b090003040000500c0100d09902c100400c0103440110480c2c090185402046201ca181598110704070710350300c1e001c69202200030300028004101e0700005050016014001d0010030b017604560440d65842c040c000034480d401007060f64840c100c15105d0280c000d410050310410800018480c440304002030646c154210640d00c10460320501030b6800040c140b4050310000d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 623331438 1250 623330188 623330203
    0x708010614041b08100e0a09050d03060506041a09061c05060a060903060203090705060c010b030f06101505040b0a050d0b0d0203030d0c030b04020d0c080c0412020603130f1103 77
    0x1806a418440c510407501e000e00c00c51142d860013844e202c84607070fa81071410240d0320f0301034206403104601a8140b041100b1980c100750310817801041598803c030041a41581141c0d090312900e41c00110a0204010300314140d400c40341058a041401840c0c0030303c0500040b02603000f500c00a01400517520140703a00c402a00c02c0e2540a081641e02d2200785007020405044e142c040d1100503c1c003500000040c103179503004d0012900400000d0921a100d2100911050103022200900d500a102c0c2d698014000c2d600050b519024903001c4104042041c01c01c80c2d0220814010a40901880001c110005070490000002c00c40c0342126034480307840302d458510f0030059443c01c0302c5c0940300b107600b01d1111003d0303070700401128910005050000b4600c0b940e000250080c00c503000178254803510105901c22258080d81260501e0810f581d0f4100181d541c061100c16140214000e0034031020b1032504280c01410814000c5800920f000c1d604881244140c1e00d0481034024440d0488910800150400f0503080820801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 623332688 1250 623331438 623331479
    0x20903102903030301090509030d11090112110a0c03020f0709090b0609070e091b040305060a0c050304030203040b0f04030f0c0e070203070b130305040e0c030f01060309150b01050c07080106 83
    0x1039410441d010000790f40d078001801911070b0240c2c0e074404640109020400c490b20a001c484040c00034031500003100955401001c020b9004c100c04101139144044544071b820340115a24214900b04601c0c010f0032203248020301c6d070071019072181c450420130b01801000410014070f409232000c91046c0c440c3c40c02c000340440181a407400381c065001440399841e004048098000e0303007940e810b6000c1d52500f0407500c0c0e600b18001c008403400c000240100138020042481c9200c0d0031895001d0200c0300c401e000841c0c1610013203802500580051000340802941030000b480340c004084007807030800d41c44c0d0300d600d00001d031507120864059011010800c4211003043c10b85900a40c940003071810300300d2a4440441c802d0005000e80c1c0d03d601c0790700c3c408017094011015035000e0724ac01825100145001c3c0580080303948240d03082041c0c1c8a401000041851090240c4529075500c070500015040003000351390094691035030b80701d0501205100e10488070000300300b65030051002c040045a09450048409100080c4210740b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 623333938 1250 623332688 623332751
    0x1030302280224070b100e040c1217040603150e1506092b03031a01050d050907091e0f0e0a02120a05010c110d09061d030102090310 58
    0x4042000076407034001c0140d01624a40b00c0924200c04010816082400340340d8860320200d415428800101c1102d8400c0b41c0c50340b915a0a26183d0070441c07034a07001160010030800c032042c010b000126038084007100484c80742402001ca000260030300c44440d0020780008002036650322242003100c04500c83e030310041035502540107850400001c0203184104006014cc000c403c00a003404641d22100485a06003024000c443c2140443c0050440810301168003030340080e0601c00c90a4044100d030f85848888030058490914110074a030156019100c02003c43c1164050500005221040c40c06400b00c031620f0350690440c0b031800c0800e0301003152342080b1400012890012003412141c0c4c00112221910340446070200d055404400369460084040e60040155083c210141038041c0c00059a044024030103083d40d1200d00c1d14a81200e1401242c424907001440e00e41040e41d408130101e4582d040c141c000780003d4601070000340400c1c81c00700100161401a45c0d1013000748914041e00c0c0206c0d9080480360078 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 623335188 1250 623333938 623333983
    0x60921031a0d020f0604090519020306030a14010e0610061d060a081f09020403031106060102060403180b031f06050c030f090402040302131a01050903070b0a03111201030302 76
    0x480c00941c00d244040c1c140550448042c0b02c0955a07044440780118030300806155803261148040e001500e000c0e5104190411411080700f0041c0440c000d803072081c0300203070041074489080d4403241c11b40c44044150705429541c85c10700022007001400781d18815451442034014151510300b0050002040b44020142000d80e00c2101d03142da42c501044501c207180c070b031a01801680303a492065a469001a202c224940446940092601c40c41e4000e84200d078025210219040040080c0c1034448804071451401a000040064006070042420072002540000d890b81d1150721211070424990068555803c20901c4403403800c100c03001e50700000040c080078500242049010008195a4020002c001c1441800418014969100c5905860046800900c1c81150100448420004001220401c0b07003c881c0c840000e40700d075000b4001c84002c010b0160040800502e05181290640c0004407910201625003244010704518a00035010391652019452000d5256290192400100c40000701c000b985003039 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 623336438 1250 623335188 623335211
    0x4030810240216120f030e21010f11090d0c1502030904060f03050714011803060203090c04150509040f053703080117070305070b07150603081b03040306092103 70
    0x225149880740d80052120340d156103d20702550b0341044102e02c603401468400c02802e501040c8123250750b210758480002c1009441c5590040180c0300d482c40c04041c450390400440043d410410071070b4006a0040400ea03002940f11025409a1411303d40e4801c0180c1c0007007540cac00185003601c1104004d04038488080007191440d86e4640c1c581d200d034860301c91004c1c0c0325007074034034036034004d0424410080c0c40480d110303a40f41d00e0b807605000a405c01c1c0c410440e24418402005581e0030107204201c1511006209100702501c0c040c100b0000042c0144201c1c2c915802c181c40d0340c00107004100440c8100c030301c40c07918060040c217550303510b0085002c2c043d02c4110f140c000b59100c01007034002d035503541942d060704480d91038401700700e100d1071924020703500040c0700e8401c07004005841c41c130b03d00c09492003620652400036040c0d250100b020940b03800c0e0001801c052400c0040c003c026201c004810710130703990101030768241556a11104111140340d035042c5d07004510300c40c3d52542c2c01130260302a81d411620b4102044401c1d900c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 623337688 1250 623336438 623336459
    0x216081326060c07020d0b070216030309090c0905010e060702031f0e12160b13051c1143060305060411070302060106050309011e02130b1204030810240216 68
    0x20003016050f400d100010483d00ca1003800b0192b8440c1c1032005152a940e92813400810b410120302c2519a95031415030450700003031040d1088812200140e4070181d0f4a4208001c0040c0e907444010300b268140b02c0e00000c08201d0109401007541c80c1c60549000a0352000a00700c5810301d41203103a60036008100b044104610304051024140664001d0032003c05650303820b01c031032068000c07600050054440c030810075210031014103890302212aa591500c4001452078840c80c0d840c5074501c20444854544074200c0b540700b001451003003903584100c0c0d204144610220000c03501808075005400080d440300d08101c0b490030075000c1c007e8520030910b60a4a006103c0e18005d44a51f01030117810100000040490043c100940051708402103181e03021f0307a1080c9000c00c030030003503002c40b044615a0b51b440c070340051442130f0501564200c05408070400c0039a669990100c2c0c1c1100010072124110380409804242035003180742500b20504002c51030070410900c8803001c0d18000340d16140c440d01c950391003800d0203c15000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 623338938 1250 623337688 623337709
    0x12901230d0e0f0d030c0e06220f06030905011508030d05040819021501050604080d0804020a0e090a0212070f0303110109050d0207031202010216081326060c0702 71
    0x140a03010744441070303946010080d19901040301c50500c90310310580381104010400602c5440141c5040040600b2881705840c910003482d0500c2c0e00c000c0030300c14911007001d480d200d07000010030003000340b05c40c64484101c0440d10502d50002e800080e13aa90300311701008000d1186c03080c41481290345507805450f0194541c2d80b4800c0c4284c802c130071030300d500100d000c0065010a40703445c0c1e41d61044500203440c4400001f5514a2540d91800340b0301751503c000101c9007400f0382120150349040002c0e04c900c60f1984015184804060422a0440e000e000001102e500d402c000c0c81c09160510003808450400d40100320388845503030501919a00404410000c42d0400e02a0b0011280d16090041075004d0711488c0e13078010070401f54058040e0181000d1041d0351a400702d4a0015203200c0e80089900649000049080f401013521142015244651001c00700705402c0240003d5107409200410032500c80061008541c01e880c4455001c1c070400480c02c054900c00e012080d4892020754040d03040010a40005081480303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 623340188 1250 623338938 623338997
    0x30806030c0d1506030804080d090905070e0111030c01020708030613060b031603060e0109140a14060906190e06130b3a050a0c0e0f01150e03012901 65
    0x2c1804031283c2d80150b54026000031a040000261100e6950301043c0e01c3d06848900382c0c00040c040c038400301c4c8895180c0308450082484e55200581a01b225006680c510b11160145d403d501c0148181c00f07040400340014510360b489a00035580b04c1c00c000f01071009051180f06407810f0681004000c0c440070300950b00b625403080350020b88414000c4413801c20b90080000750071020240c1d06502c0045800e0145800241c80014100780003a115035035403000e402121050001c04006e400904046102e529101e003155820500040081d0240c1205e94491791401150b42d0014003082c82c007504002c40b900d0300001a001000b00c0c400280b1205503000c002625000031140c043e2005c0701c08400400914609104004800740c0507054110080f449062035940c0d5102041c080383c01000e01500801d40406010506001e4003554107104040d9003806d4103031b6480440c8a40c2c0c00108903030801080c80300e40c0c00b40220500e00c003c0d030313030484803a101c03841c10b031a90345003580f5a6906106404030408942015544490440310 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 623341438 1250 623340188 623340203
    0x605030c01080a2f0c15100303080403200c030d0207030c091107020d152a08040302030903070b04050907020303070207031b0302130f05060a14120c06120103030806030c0d 75
    0x30013001d01d074504820100503025400824590300e44c92050700041c13690101050807681409401d99100000d00011110500ca5080d600c40c1080080e0080c802103400500c03a00345941001100401401101c000310840000d5a10050314010706090078040e0365400c410606c0500007007070850301c604030f0b2072940d8410500c60340e03a61889189024808025039015a40c02084005400c40b00d00346002c9244d415202407058919151200f004540200c04282002090319294a401a480034082c2c3d42014000c009400f980020012600965814405003010748035040141c3d484904102c00d01c0070030304000344081c0c2954000c0042c440a0303500001c50f007003101d911240058a11801c003c148880c550f660b44003c1d00000048801000f400040e0000300801a003000e040005540c0d5808115600c406841070142e504100c4810074050304202591201c04102001120041110040070072043e0f800f003001e50305146001401802015440000c01d5040314003100103000e00440702c07000038030640c0146030050a44 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 623342688 1250 623341438 623341451
    0xc0503011a150c0105341b020103091506060e121c0207030b0705210402210102040305060a140a060509060105070302010e0106170114010e040b07020a05030a120605030c01080a 77
    0x207111210496401c0f030070900080c845c50904400525500349800742c80b02d003204100503240354201d00140c5690451701302d41d4540300d20300344030b1240840340e11040b141a170401d62901540c0000c00c80340c40c401b1940801d00b500028446183c084020203918640000502c62208a0382e820144c1d180044e81d40000f900f9820064610040c4400a0740b07400d40e181c0c401400580803004001040b038110b0081c1c1094904050b00e2003207007000448110162900f220000e5000260400d244030403c0503408581861006c500010328168498562a00c0c0a40803500320415a44a142480008081c059031235008060300d60309000ba2400c02000070315003100186003504126007c20b4180a05200350054000c0c005141c008001c070984440c000400401201c003002c006d9803d141c08081000081c6154504883d89140c8058042d1620781c2c42501c1c408020303104d107045200e400400c802089041c00207101000d142d40b60000300d85015484441540c08582c00b46100350002644854107036004089a94054006680006d41c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 623343938 1250 623342688 623342719
    0x504110909030d05010806040308010501021c030f0e1c1b0b1303170709051504050a0308130503060c04090f09021806031e031b0601081c0302040b070503070c0503011a 73
    0xd43c028030902008440c200b01c0001074014000c600305000341d00030b0b518000300d41e8903500166580c1071083c0e21111100c00b107c0b91500c000e8420340c803c08a00180c1c4001042e044110f1000e1803500744101038070341444070300e1210724500c0750308520510501c8583c0307042002c0d10310760b640b1408540e000040cc04480e010f02d4a0071002014482e1140c04206616041c560329181020340004103200d9140c0102801164103050445100c1064801c0e50100e4400400e81085503040d6960340411b600016020790760301950b4540441c842d5028403445100c2c4405581080d202d0f0701d002c8240e0152240304e0781410b500307450503d5110141c0c552181460300c488001402d034003951104000f0a1808440704051020b1a15050101c14911000320052001581030325090b41d24075001c04415403030b48400e1180c20010350000050820908003070703000803d102e805060040c1050b0340d405d1101070b150b00c14034044172660000909101080400c04001003d0101034001704408800650f03220030b0a212040c280d4031402d1205160601c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 623345188 1250 623343938 623343943
    0x1504093009331e0302091c02040e011b0f05030601120b0a05030304090207021912121809020702011209080f0912030a02011407051c1109120304180504110909 69
    0x1641c40c01240c81484100e01e500c00414560b00360300c03038000f01040c002c00e421074544079000352048940c00811195a100c0070b070504040030310b01c0000490b0065124144041c800100703210310145402c504620300ca541c1d0078280c004040801018124083c02028400c1c02503a03680062050040300c4968000070702100070714000386c005542a0301c000e0b4580700c0082c01003030f10700c03da4001c1e06c0d2251003a80d165666070f60b01c000c03008030480c00d030045c0445125040d071200d001c20000c088100304041c0300c1c148000d4071129100c4444d407880254205162494000410504550b8080b440317141200c0400c80400400c10f10359a0415544101d0031501c80d400303404a2910f94607614442c2c0046211a203600b00c96030f40d603407900c000c1d000c0e08103070040c40345041140c1d00268100c1c0c05a000c540c0e1051000e4211281d0841c0d045100c0700070400b050982c01c00702e4040c007198055480f450700c0400300d43c82c801c00a42d11b941c500900e0b041c034101c201c960446030605001c00e100c00903001c0d4108003003c441c00c9070f0303ca03c00da480c0c0f0340300392 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 623346438 1250 623345188 623345249
    0x10e1b01031811011403041205130806010b04050a060f120f0608011404110a060203070f0f0b1f080f030418180f02040c050c0c04051504093009 63
    0xc540c0c50282c0c403a010040c036607410141200c42030b2900e1308003c0200d04c600c50700d408200c80240044844900d4410b0007440b4400a142000c4507450080100381c0320074009107080d009820000a11000060501440c5499410200200424a07100307204c48416400101030f0590301c4000f0040540350b2821614134401c0c0e401c041c015050480c001c0044c0000c80d2050381509400782c6003510305d4070001c0d038614610b0800443c00350580740385800a51a00d000b540c2c80302c5c891000028103440000040c688480018031b01c1500a00070344500025003014802a003a90620b0116580450100e40c0000311180c0008004410b5034100c458800c51014030540140d104006400b06020014104120411403001c00c0600003100108030300a407001c1010003410201035509110301a0311070882e40c052021101c00e4503060304156800000c81c580c0302189010100810155a007a910448414a201d00d514034040f05c403480889140591940e41044500035200c00b0300b445403030b40a080c41c000b03000c07450010005044403902 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 623347688 1250 623346438 623346461
    0x604080d03091401090b0f0621030703120612020108100e01081c090501120c030e01020a022503080a0f182d031106160501051302010908010e1b0103 65
    0x458552004010040040001c010b00311415030a000c04180102014402d280c2c12503402400d1442940300c00116880194000309032a501502c01240c03590480100c0c4225120381484400643d2070b59154500a407022480b03030071a441292500d401000411a00d501c920728842c2c082c00c1c981943d8840196003121542c00380c00207103103108200e0001a01d6640000c7d8280550b1090000746000a0310240c01c07180c680e001e208290001e20b04881488510019a2110384003910600300041c0b04445c0c0040e03e030030381c0c1140000a01582203c1d8a4200090f4041420038002c81c1d011038081c60703242141d42d28003503402510342080400810031070100c803007401b480040a0070341801a600d1107481ea60404001440c11340414003040c40041641080c2d007601d009248410f89a01446844d4244010700910a24ac1c00504030041c2d40150320b94050082202031103154029604100d584100028500024003101c5155001507100d070716000784000707500c102244c0d003c1581c00700101130000e511130000480c068171440160 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 623348938 1250 623347688 623347693
    0x190e0d020a181b020304060f0203030105030715020a020a0f090e030309060c130e100f050405090c040e010f0608010902010e180103060504030c0501021206011206061b06020f070620190806060408 85
    0x20350043c150000090030449a0315510600d46000e170000403600d03400b080c80fa184d0558041f00f400d208584507903401c90410315441c41240d54807071498001658003001070740316110302505250305012030281030003041d0101640d00700640c95800d050301d889584a9000746508030034440400d81c4c40320300e4610003080008104000014103d8182040c80c46030ba120709104007420342d465540d0006050400380201842000010702402e0312055080c00e100244c039a1401c0c1d56100e55035003c603080862807902c030781c2000c4c2500000016410186100252010100c0c22070540b1400303a0f9284910410b2001a40b64103503980300d0390109017910740b031605607078000b00000014a154000300f20071000300001441306108000907600d003c1e1403104000c00c0c10481e00c050103a400000c0800403a1000d100c5007845010f0f5442c40354400528005905100715059000041e089400c20333200d0b008507035a100c2002e8040f803244819031030301e450180000c0d0043c40c4100002013160034410a80c0000e070b02d03681d90500f0350340101012001d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 623350188 1250 623348938 623348981
    0x50106030203031b01051303020a060f2408010b010e061c0b0616050105010609061202030c13080a060c05040f060c0f050303070201060626010608090f0102190e0d020a18 74
    0x803504c0307240303c0c3c25001900710f45c039000c0044c400002c0209071042d07540c0c264002c3d004e402140c0e2258000b07080c8d26480100d034641c8545007a4044603200d140b041c0c03203100c00150240e106080030b03070013070943d020b0600550400c256840d140e02c0560f01c52044444601e0341c0560000d510300c0868212019260b802403c550103d0046110010081d000c0035100066104400030803881ea280e103016a05c0a00c240511400170303c030341d0707180c684905031a40116080003403441c88a091915a4071000030302c60700394106120340e40003529104200801e6020b180c0c42c001c2c160402e10300b42806c28403403c00e071088a2081804210620b5581000d00904905181180b9001004d0700c0e03481c0740a14020303002c4c100170b1142c50700245d1210441a4500d0904909131070200d40ca04001c142039107042d0080b0ba520b0390140c201c182a004d031104d80c00600b0340c2480103020110100c00d014880640003800038103030034110a1201d009505c1004403000580e1029000e10179140d501c1381070420310007201c0e071403002410743e9040010f075000c1d10710 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 623351438 1250 623350188 623350207
    0x90d110312120f090d0c0f0209070c05101107030305130b01090213121214040b0403050c0a120c0504051b0c06040209060123030a1e0507180605070206030405010603020303 75
    0x18020054000b801c600c04456846415007051521800c030b41c1c4980b50f80010740399030980c1c3d1056804a04a5000d02c1d0381c804512001d0f00050075150003030311810042006aa0b0708010440140024081c50004030010411260303407900d8401144a440d0005040540e1800040d46490255124044d048c1d00001058510340c2c540100b50000c0d403000340c00184540c0d004600146182e201519400841d51242a0606011044600355940d059090744001100d005100100703490040e070300500300940c003800040c0b10141340d00c2d06100d440c984036081f04003000324505464001c0f070310080e0008200c0f10160f0f0000348030784d14640482b8150000b803481c1407910000040d6071110200005a060103580200c8160f0341c903446107001550000c0f15440c046c114404c04400010b01c038a26a009554405070a035408900340c040682080000b1030000f40c0c600780030780d6030001e1003c0c040e4800388144104030118020106281403039005410b41c000c5000003403140c1000000182000404e401c4800110b034050100d0f0307100d05800 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 623352688 1250 623351438 623351473
    0x50a06030201030b06130b0304020607080304060b040b09091b010e030703060902090c070203061501030213240305151207080613060506030318060a02012c10020a05090d1103 76
    0x1848264000f030308112543d100c41c0b41c0304003210707110583c1d00000c0c40d20924184502c00d003500000c2007030360302c81e01c11700850b404201c40c00015031041c3d00c6440009903410035a010401140d40342e5071401d00406040c000c0000d88500000c2c00d03040410035885e441490051032004803a40b0304500c0c0c1319909405020400002c001087d000303240c0c054400c9546400b2030782c45162142250241610181d410741c4003102194002c440d40c1060301500a0601d40980b13424260700302d0000c0301103581d0040a00401e82c84032104442d4245003280d0385500d441c80c05018904000d403242207095010700346070f4815414502c0b030f0400d01200300000710003010030360f007540c4080c03903c0481003445c2c0c20b035070307806035020390403c0c00240c0340303181c044111500e01c040c82010049039204142400107982005440400f59962103100c14400c0d90100100c01d291880d40d245152180198600b81d0304007055684102c15080c010b000c050506a0460140c0c0c005117000e0303603004450051030400c11580d11003d4101601400b401c419620f416054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 623353938 1250 623352688 623352701
    0x6051207081902010c03080403090902030f0a050f07020601050f0a0806010303110f0309010203030c0304061d0c010e06160803062403220203060105062d0a0e01020a0519060e01050a 79
    0x1640c00750350910440c0c169004250350200c00084c00120030a6411002038040d1300415005806880c0c01c41301e01c1d4950308000200d0f8802d541c04640501c2d0b040800130503400f980140755000700c101e00039810a04200340069624241800344501c10000b07411070380003139220001c0300e400910348401150410750350303810080c049a002403c64682d50162040782c205603000001125007100c0103030b004520b1030f170781c0e15103005136500090400c54001e82c070fa1418607001000448242c0440d513290014040c202501070001d0a0903040002c3c0f18000c3c442800b45c803641072200001d035541d40741c02982d815940d40d5502d001031480281c01c000750071032807070f01d400c1c01d00101025405103204540903440c0c0c1030a01384c00c00d8000c20390114800000e51551004005000ba400c00602911940e401d41d0040d8441a4070140b0110442040800511620102150314503805502980400c09140c0c01c1c00603141c50002629940c0d03c42d80740e000d4181502014015407000c0000d41d900400240040c10700810490030081203040c0034104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 623355188 1250 623353938 623353949
    0xe090307050619050f130312090516060306050d0c0b180a14010f0503090613020a0f0909020a120206031b1e030f0a05070f20030a11010606030c050d0b030106051207 72
    0x18160016000500704405140200044c0140c0c604040301564211000000e403055088c00b5605d81c040500020030420020301c07401d0420010b144154140003000707007140c070294021441001518150b00108001d11260030649440e884010350303400160030081c4c2d03000e600160003a04200700000002e404140041c02000000c8240d035902000d40701c00d201280c0501003aa0800c403290401030204103042003941c91144858406880400c405644003607100310602c0c2c950007100000c3e1550701c0e01c401c610b803014020002c0e0600c00014030300c2e80000d0b00072420300d000003006d0154180580465050b188000030036624070b07508408680c0c05078545200d12020581040e00e881c0000304010012514022a42c00707090302c00c80c42c0d0b59407540d1401903e40102c50710f400307541c125281955082d100c0da065000c140000c2684026948034500f5034488103000c54210742042d4085130401d40390251040990750301c4070486104551116020030700d900141c000a0041c84154443c940c0141c0b102c808102215000c20310038110740 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 623356438 1250 623355188 623355191
    0x12090f1b06020c0f060405041d0f1b04110304080a2109020103051e16360801020c03040e0a0f0f0b040605010905060a050f0d11310e090307050619 64
    0x2c01030003032080b6060f20041d01030b880001403100f4441414030754404401d015402e07096204d191800d01080e801c00d482414000d405401240c40038102f41c3c0d858140c224040c400b82c0d42044003500c0e8008a101e9400050002003e007040061000fa00910503800600c3c2640400c15802c9048003245003140144150501240420b040c000052140c01d100201120a03480e400710f0b9a00f1a5070b4103003203e448c0903200c00c400081c03010040c80340460142c0040070942161441d10407110070115008500a014400d83c03000800368010080300c10b130350b400801510120b0b240508028100d85840031a64060302181000c003444600d00380841400021940100f46054403e070b41c10081e6940b40c0d40110741105aa0095a41204081150400e028400d400030301510600c41069410404000c00c03d42c1610701c00c0d800c0c0000e8901c08140c0e6030302c0000c0100c1440304840b0902d00c0181c00c042480a18000f06c02c0b52080441083d9440002215030a080c01111a031a0b40070080c0c0d0104e1a100a0081c080e0425866055410b03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 623357688 1250 623356438 623356453
    0x41401050c0a1e060504060b2e2a05060609012c040201090e09030a0f03020c0606040903030e070e090606030303220501061a07140d12090f1b0602 64
    0x650048085400020581020742111016601c4802110592030f41d1903041d40c1000c1d040c2c1010a42c01e22a09010382d110f50004900c8203941c0c1d080000d00401d407040c44c40800992110440070550440031700206070214103002040c410b0b260401417082c00d514140189201d850b1004d4400c014010941d0303845031030101c0320450140d8a42c0e803160824a4207a043c55222903010b11150102c4490100c83d5a000e44140350800c882900c03114010020b420585004140b9400820502001c54201030141900c038990301d030031400c101640e01a82d590703102c09003807180a07a87e5440e40d4000e151294100042c107550b034000300d440d0780c1d594107040002a030003111150070074041d07500030035614900802224069028070224030b4601103200c51707508a002000170229110740d40c40c02c0002d2061140051494116541c5854541b90101800c00c0d100041c4600121505504065190400706810243ca4084030844500001b18500e00d442c00469000b4075000151130701c00c00b840010060080003620800b661039070750a0703a504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 623358938 1250 623357688 623357729
    0xf040608072a03080a090f03050403031202090a170109050d02030d0f0912110a02180f060406080d0c05010f060324020406120b0402220611060103050a0605070908010e0304 75
    0x2c180c1e42100780042e20002e48041c5000c01c1c8280b07001504003004020014480301140d580c240c4a081421b82240424030102c1c0810a260708801017403401d01d180007040d4544485400018103015503802070444940c4038060649410200b54451142ca031ba10400710780188036540800380d92600007119410003542000c44040b0304110390b0145c402160f074091101c07942c1e0715410303105544c1180a102c2113100352141e034a602015a0b1038154500311164906116162403c010b0359503410208018035050056007820700030480c6110010300000c8440040c0b0740103008141a00d01b85e07015014000101d00040e04004000c030520201030240d10594023803107428429000d01400e014143c1c001c1c0c0c8102d0021078881102c1c0504801144c02c00503110000400040c5000c9890141106100e480c01c0c4001007601524414402c0d80d4110403444103e40344c0500034581d80d851990307010b5a500c280701d00108020340792400f0a01181c05144400c02402c2084020b1088200c0c0c1e0080390743d0794010340300c0c0301407a8220004901a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 623360188 1250 623358938 623358977
    0xf050d09061d12090121050c070b09030703080711030403020d0c05030706110322121b0b0f16020a031509110909150619240206070c03080c0f04060807 66
    0x1258080d403121900706929040191034112007040c041d00c83d02d8418a056201a046c1e20031f051013440001001900d034180b9007450503900e04010400609580304100700400300740c0101c0342a13842a540e00e4446a88028200303402d04500840d40025000280412030104000a4820311020380c1c00603012078510550351380085480c00342c00302e9180150307041000060345140502101081c140f2840101d030038500c2d592740e103101c03032a24811403e480281c2c90205120045c0711548010f002800c40c4840d10f03041241d02610100b0603c41c1301c40081c2d0f640c2d064040725046403914086e403001541c2050844682c0c070240918400901201002191000301181041c0c0262910011140c020502d0000a0405000032902c48aa2940c003505996100000101d03280120403400314140151884000e01d080001140c5190704900140c40d81342d00c2507411013810440d029500c1008901d2302d90301480d04011035203a8410183c0c503807081041c107080c060030004011a0481e004100b40c0e0207584142c0d035504410141c02d80582 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 623361438 1250 623360188 623360203
    0x61b06180d08040f0f1406150f0105160c08010c02240106080f0a1d0c04060b03041e1a07030c27060f02030d1a01021207050d0f050d09061d 61
    0x20202d4140000300f00850801d000d0b00340c020b803003080c0c00510300076a602c600b034442d40c1c4910500d035654812410016406490b6034040c500c0d0300181c1318000803040c0d01c2e00282c0740d40603c8041e0b0200040c08152030b428800900b130024000e0110760020003d002000e00f0003501d607058140f401c098000b880021481a00d068450a812130740b0f2079841d1811925804a84240610082e01480465807110000310f4940340801c2010500300c003000c010881000b80909000c140c1c1d180364480321380000144100000b003041340302c1144207040741c5100c145c11070070240380c20713000f510070034008500c2e502c000d00800c0310090701540409410380d1180c54003242c070810302c0f00403003c1e00409481ca01038200c0c103c1080141c0e40c020460f0780d614100900669003010710090102c403ca56062040b402c01c800b11032181e85440d46c05016201400d1206c00744a0728007103c54030303190b0350307000c0141c0032608103c241c404240303401c0c0c8142c003501d03041d1014100510004210f42400005404c4422049031901407004071480355440028906 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 623362688 1250 623361438 623361463
    0x180601050604051011070e0106030e061504110d02040e04060e01021623030d150b040b040b03070c0204050a091103010902033307090614040308090906061b0618 70
    0xa0b4545410103051002c0c0c800c00b03000400c00c1c08090008600c508109008440c0513080740d003586813481d071620000900ba0b030b000c00750410f1690042030502940400440f075805234540217803004215181c0c0d4442100192181c81c0c6045600e510108011132260049405503002e14061903003030001a400c461894202d1244805103113032590880510300c0041c501e0081a8001c0c2e120b18481d0180000038105076003160b000451000426642c1c0540b803003a00008907858000c1d1964a1142d81001d080241043c0c0610850041450800001c0f0019603083d2041014111013031b4090310034411414a424214003418140c102240c00e04618200c2d10350508051007444003090300100140010081c581001c0b550400104038004000c915020703502400c0c1e00346010a01a036050ba4481400780e2034aa401880314010450b6038030b411100300030400101e5070071002da990880c42260200040d1720b5010001e01ba910505d2071422000100c0c0101c0070560001140740743c41507001c100450003407284044c541e529015564000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 623363938 1250 623362688 623362699
    0xe04030201110c0a02090a0b04020c010b04061a030a09050304051309061109010c060e0106080d02071a03010b1210050a0b09151201030f2a0510030908030a18020a0b0318060105 77
    0x41304054500903203c0c5401c03c0001400246182441c0b01280a03070b88000c0140d05140c0d15203c08815900342032107007100821f9060350000000c220444007420310301c0050180c82d500c544900408050010610485000f454010403540c02c001074525594003030400b00e0301c25107002d49030880c000c0c0b6070402c1c0c0d0708640c00070b10140d60b0008103d4007565040e0003441040361036103007590381e01c0d40403c0400c0704000411121095400a040d46031409071110f441c129404900042400d0910040002294500c141d0b206000c0c0c540300d040543c0e440854103480e412080e481254011008a000134007400c03404001c021482058405040d08810782c0410300041c030420b40040b0700351500600410201e172000a520301002d208401807000710704020040e00301d203a0507103809114644641400c015510340f078070360008044442e080501c20880542c82d1100c2074040101420a040c1e03e40f40401c50320403074074804500c030039402028040714a4a40c0a441d8203500200c0d103040140a56844c014506140020028100c41e401000b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 623365188 1250 623363938 623363953
    0x120b1e03060709180e07080d0c0c150503130f020a06080115050403150203040312050c21070c1e060203090c0126011806090c0c170918070c0b010e04030201110c 70
    0xa990001d1640280f400010f000300e480c00300300354409100e0230650807840c2d6200800d0203643c0c1880d4628070300687c042c12215500c402800d0102e60010192940300a003151204030100850804045c41040107000035408092000b0100d04c4a42050485050300e00c83d081d480780250840d02d080c2d4440c4540d01000d0220014860b107101c8100d9150029540140f01385440c1d00000442c20f07032441900c400347da482040250210358154102c224070b420942c1c1c00303104043c4850718101a8009004208400e001500900000044031000c00103c05000c4055074016400c40d600d10700316003143e40b40c0d40d41580f500e0008180030410310110030310102031645005411840860f6900c4e10768084014001c80c1240070043d80c81c0d14000401c1c000e544144007101e82c6039214407602c40154900400210400702d820130304c1c3d44082c0070056003502c070495031001003414014403803043d89426034181e45852a0070402010400100c00100728008406181c1e8000c600c603400034401004150300a8905009004034070305151301410 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 623366438 1250 623365188 623365229
    0x20102030d050c09090103030507050c040c051204020a27050906060a06051e0703030509060f0c04090905030c0f160608151e0301290406050f01120b1e03060709 70
    0x81c842d581003101c29549a14003480d40010a1034078a00340d00903000b048010076080148031090102e15800d1404407010002c01075055009840d90003900c3c0941040b918480001c1c04544501030708601509001c00d500134419003134182c1e03800038041d000003500c845003810042102e8010010362603005210003044010040d080c080215a41c1d0840c03200e11040d840380d0450302e00d0402612004003102402a0780c0800c1500d403182d00c0b245444005040c0075400d9410302c0c10001c441303006500781c0342500e11140380800d8403080350400a285005074400f9000500503407001c04080180010b0001040c0d280140610031107984400903035017410b00311000b100c1ea080c803104854046c586030088012040c4a0010600c807030700030f10042400c54410f145061208403082d6051101a500d14900c0c1d00300c804100c0c6d041c01202e04141c045030b280c3c2e001000c0c0c0c034103200100105541c892025040342801100181196040303408a00c0010442c20350002228040e0040c0400b0980301c512580d14241522040c454950091380001c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 623367688 1250 623366438 623366441
    0xc0c0f010903050f070f0b0112030305250507020303043506060d1e05120a030b040e031204030c050d0824150f04030813030c051c061a1002010509060112020102030d 72
    0xc5c00031580c4800e03c4070a0350006140311a0b1074003070050114004420745c1980341c050304640e0050074201c0d001085055501c1e82a500ea4a5a1181105407824948071052440424514011a006a000503c0c0f108065003c00300c41c0c41000c0c400c20701d10307824408804035000d240d5101c210585840b6041045849020f02042510306c5020140d07902e840103100000c0c2c2e0f92902420006211070343e0610f1000000c1088003960b06005100d0050001c48081040c40c840650141e524442d5a01000751480988001001d1501038006001c0a03900141518602600c014004100710001c0b03a9010012814602e07640c100440341038007180541011b0840c0c074048079076222040c0d66400c8412172804941c010400030001411180281c058042c400081403c1582503242614400755503800c0640541032180320700a440036000000903070541c0104000480c074044005e582a58500b001d06a6004090b050390181e0007903055102c0d07485000c00700c00b40c466690b20707402400c803400342c4210068010383c401d0020300400b2019 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 623368938 1250 623367688 623367697
    0x10503010e0c1c0c1101060609120605060d05030414090708010302180405121201080712050d0c020102150106050306120c030c1309050a08130e10090b0111060c0c0f010903050f 77
    0x1100020f04009140242d04058402c0c40300d4820000f500e0000b032007401d1009026034400b80400d414040802400c141d03946941600038000900141e4407040802d41c10b03101c040703014604c0b680120640396030740e0301d41d070a100045010240c1c50b0300440d559400102480c1c403a151150503a5030080c51741154016a80401c0321005025205403024029440c3c99410054800d00602c00300c0b440001c52905036140200060401046501400e902c001c503030328010004601080c520140402401c0010300c941d60340c00105d10b42440c403400b011110b4a040d0002c603169030403001840c171800c4100c4207004160301d138000054590100b201e2554040d4000c2014107a145400032906884090600340015501041c2c1c035220f1500b04500d1003510494800904044002c6964030001c0207040006141d40c41820182d5403a140c0c0708072403280e0303250315542c0d0420750745907071040f1840c020a40409040321f04e40d04080b00b000840368481c0607002c0452203108840303086918103009400c01141c050301c0f0340c3c1c20040d00c17400901550b0320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 623370188 1250 623368938 623368957
    0x30f02010e0604081e06040c0303200114090613260d0f020a08090601050a0311010c06060801151d01174b0705061b060c0703030506010503010e0c 64
    0x140c0d5000d01c5a25064064001840743e04010078100186070b120141c0e80c8407404051a03250020300400002c1913540030380d03008907035145c40d2841c2083d0418844822000c1c0300c400181145d420291190003202c44210600d0050b6210030585185480300c00350720f80c4011001c1c00041100e4148041100c070070343c120340c01c00b0030110264029403500c241c0d1440142141c1c0e0031051a980245d000ca10100c60300e5021459a9100c40b4002c001c1905504050000d603c010461000801401c0c032042440c00071391296460320340c1d10350f0216040c08142c1e2a00d803420f0203030001042d04030003850551800150524840801240d401c0d07058540b810507401d2820b0340060312454070780210a8480d850140c0d004903070b2a080c06a210002036808076590765840807074042c2c4030f149400c3c4207003034a0304000415882004076106080f03c2c1c04a4030349039550004200c10700038203038070301c206d92040c0100d004100c0c150b41100e0007005e0b1544a55400c01c8259203584c01912180002c0c0a030012601d00000092005603085000740b40d20030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 623371438 1250 623370188 623370197
    0xa12031121070905190602070e040803012112210207030e04050a09050708070501140414041508120415030519090204021e120108010b0f060d06030b090a0c0915030f0201 74
    0x31388880215019626040d0b0108480d03190200801c080c07541489400081d0213516501c1c80c103070415440c2c2d110607000600549900b0038001211a007000300b9490300d403640e40d9004050900810360070802400740c00d4100c1c075031144905c00d4841d40301c012440784212504c0c5545510303644c1010828030107103c0101801003218000c69a5813000c0d00c00300d5000c00c00307080100310100080204500309000142865541c0c824a07000d04802c1c0700c01e0140c458400000144000107132000141c180900319000e10107071195118214074040c008118403405e40f9a40104150382100d4682401503000d03071780032801c55000b210311005038104029601c5035802540c02c08401c00380024805802c0030401e4118030541104c000b05032204540c0000c11042c41b0942d0300c280c0740100303290f2001300440d01c05d80780404c4111070000c0000e031040e2000142402c4030203480e4800030246800c0205040e16181041c016503861040c25415240302034074144c00207040f0060700900026a502d0748000118600d50342e40c0449400c9050000c03414071 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 623372688 1250 623371438 623371457
    0x90d0c0c09052401020d0504090209130f140907030b0105190e10081e0303010620101515050906030403020f0a0813090b06031f03050a1203112107 64
    0x30001c60141a006082c4080404180040a849114040c0400f0320581c1990006c030b4111724403030340090595003110400400540d4a6000d00002043c855080c007640404a21b07040c01450050288d9110000d01106201d40204c2e5031030f005034082c0c4d10845440006c21480b084c0d401800203081c00c00c107a94007070100582c100801034961102c050000400c0383d11140c3d088404208104240f400c00121602410014081d00a031802c1c62025442e48414040d5105000c3d5442e40c81d84400b0034068454003101e0008152540042c41000c2c000c0900700b04112603440c1e240007000880c03520406142e07458105401c0c0c881ca40b42101c4c10081c0029504010700c180d09500602c401c2c084800802d01c035017030380103218150540d1755510745202a01c0201c06500910041c51400c0041c9400d82c030f660040300d0300011401101400540100002c10984130300d5080140617002d02e909801c00c11504020520400ca5103440900400205a08041441c050160b4540d40c014103000d507002c5440b501505140c01c02c00038176154000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 623373938 1250 623372688 623372699
    0x120903100c020a0b06010315061d06030f010306061a0415110604030f020106090608100b03010b130b0a0b0909150312070507080c040209180a0914010b010215090d0c0c 73
    0x201d070a03810035000036030444034980c1c2c200200b890500e540304100b42070420041c441710200c5040b8211030b000e0307901801030640200c0d80c11003c0030202c895081008001550ba85800203050900c0c000c2132008071a59801d10b0710100c2d4104001580f500c001c680c1550f800e0070649070060000d1800d01d0300d03106d00e091081e0000481c0d01048180486407141380261560038000c83c143c00000d00b15003890f808409038038076151040c492410041f038488120f0365042004940c20030703001d00090041601d010402e611420180c4a004042600c0e045442400c10840340780340b0380d999541d0754105500c00c0c0c40304594401d018500245503080d40d40340d440c190800c003608a030a8100106c2009085500c0041d01f542d55500c01001000004010005403450900075030b815030a00c0c0c1080d0221356003400f40c141c3c00c4803103051030300020440b410561140401d26003100c01c5c1810348589002d031500900a04149034010301551b40314820401900e40000d004d074146000034042c9841c03180f8200c44d02c003e0440105c41403072900000007603 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 623375188 1250 623373938 623373941
    0x9042004050405030c0f070501021f0f0606090f0501080103080307030f1104060e030705030a0206090907021609060509100303050f09060904050903031006090b0a11030706151a030912090310 83
    0x202d103200d50021035907025450302d102d00e00f0086061540555020703400611943c2da01040c284801c0955141500081c024040d21902034500d80720520b00d22451302c1c00006209502c107505800712000f004141c40304540f03c13401116602000d01020b090785a040000c2030145100790701c081c44c008814580003d01d101a00c1da824036130741c0a903100e000084da8100580e40c0c0c0e441c050000748000c04081b0020703d0018001d6002c10130794060324520511840d014400503400704d0081c05494001d5101e003910f03401c807544841020006000700d0181c1801000a4000641281a000c03030f01025660581c2f0b545041c000051042045075114265150b0401000d1007103c0c10398980b400307418043e10514000e0341c0c89141950084030032030a958007000c10000801d004001c1154410122124511a880c091a640f004c0c0c0c01c089141d4851803038001d00b00d0f071402c03c4d189800c801084035201650030208016042d500442c0c2a00e04600054170211000e400c100e21071600d803400000140745480c0c018050703640440084040c0c80 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 623376438 1250 623375188 623375191
    0x603031303050c0a09020313020409031b03081803181c0f060b090c0724090519030e010c020105040e13021503060906010c0f03030b03100603080c06150904200405 71
    0x5807190701c0141060402c1c13400400d0300c405044680001c40c19440c02044c4041e14010b40c51010780102d42d2918801d06240c4541d0104002e4001443c0c482e0762110645030041c000074045a85c0d0380c0c004060824035003240c1c00801101e6400800c2104c0f4607010b07055004010b4000950b4104a0140344000c409400092500c50080b040d50b01602c40000e50034030100503c10101401032008180c1c1004000400014610903a60302c4421000080c0c1d5000c018107403c82401080c240c00302a10074811108807640c210100b004c0c640c00d661080d0707121040da4076524010741d6000e424200086c0420030901082c840036048810f96035010144802e0301742000c810b80c0201d84ca80c0d05070210900400c600004010141c14a981400e41148080c60701001500060326000500e4404120081c101502d0700080d0b80396940800024100c0c1c0700140c0c0030800c15940380380002c49a44002c07901942d9004510006103001c01068402d004c0c05000780c0115240e55985c1d44840710200c8a0500d03070b03950600c2c0d2440010640ba03510455 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 623377688 1250 623376438 623376443
    0x1202012f030c010c020f030a0804020d060216020301060501021612051c0c11010806060714100515040605090402240c03040e06090f09070510050909161101020316080603031303 77
    0x110b03030361041410303254251400c090180040d50310038030840c0c2c00300800104442d13441c90079181000c029205c40c400203000760703800a800b070324050002c14454103001c281020142028030072002001410340d180700581e11580e000100742c88241c2050780402603105410703502c24030188039806540403c840c800406001091000111002904a41c0e03604204219141c0001c2801c0013402c00b203c152412000041c81446481c400400c040100807000b000b230341c0c04000a11035803020140a020030f2510011001d502941d02c22510f20540c00d04000188608102e00f07030602994001d01590708003600b00d001404004040207001118010410180403800304c28405070000c0c0c000d0342d02c1c0d000e0701c1c1080f000304040341502800c1d41441034010001e1014140780055000105c89043d12500c50010055809030380300e0280d03000e500d030002c00c00010050302c005542c04d100c1040030079843c3c140c2ea840d208450700d4200d01046612a0349141c00f104444002409124580d034400c0006040300d241030321107100d2081c1d92000740d108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 623378938 1250 623377688 623377693
    0x42304090b0f0a0e03190e0a0303110c09010b03060616120c03120b100f0201020417060a0e0d020607140f070606050a05040b0105071704030506010f0303030c08011202012f 75
    0x30302c00b102e4070b00ea5581d50881000300043c48a05400201140c6074826588505911482145241c0c615030044010210004004000c0c162065490801070011a032095080c0107501441a5002c1c1c14900600c00b44d060700c0c54040c009003141c0e1458140b107159440318906954000001d06040b0005003803079080704c0090b0b03581d5140da4040090f0718014020071908001c64000c10300b441e42c0401c41d03459040070f900001c2d2003403418840e032a010340010380c0203100d1504800841d110380104a01c40c0d800003d941400f031100310204111114006101c1c60b120766151002d440180c006001003031005200c2e660301e590000103600060300d0000104501805036000040441e4107548650f0108072902d4042d4021000f071006481c1408500c1d4206c00003052445080001002a0168942200200c0320301094601460b8000103d9490356102c100c0181500d04510080700080c0c0ce105007e24640d10602c0030904070345901c600610200304039801558070301c01030308500800605023009009021840d15450111385c0a4601 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 623380188 1250 623378938 623378941
    0x9030318011209110108070516031e02031612090909120e03160b030a09020d0503031f05060a0e031218010210050708060607060603020a0303030605040b04050408042304090b 76
    0x5040100340d2035070240010703d40354444000c207444101c2112001801d2078541c9503540c1d1401c0c00d5580c0c1c010203d0206443c0d00d055600e004140d00100d030142d04100081e220005c5802990089945e4480c840800c02801d10301038201e40004e50364030701100c460303026007448503070103454510300c1046400c480000c1d580c10640e0410307106582c3d0403413032189020341c040d40603200182180314a140740b02d001d8421114898000030008075407840c1540043c5941c0d9004041403154640c50400b40d950347c100b84c601e4030103c003881541004003c07040d5142c004031500138120701d09108947d1010749040310300c42c1d1055058018440c0c0da0f50114400c600074041c10a00310000030001c0d000c0030009107040e51551700004002e21b440284160b80b60468038503548030f80c0403155256100c407503241141c090405944000c1d000a6030401c08010541c260f0065429982d00b61b408004610404c010041501e000ba1800360100034100300505c1040603a00040350860352400f000c065503d60b0801042c101c40f15090250781c84040c020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 623381294 1106 623380188 623380237
    0x10e15010207210c1e03020d030c0609080a020d02030306091609080307060b09090c010c0305030703090c090501090c080103120804140f010608070b070b04020f06090303 74
    0x10825080045848403c051448080b40110307a20340505030003044c0318040d00d0341c409000d42400c4c1e40c2c803926841c5400744135007807200d500107604020075400c80401281d902c5c0164000644188500341e5281200d00d4000e040400d4102ca410440d0002c1042c44841c3c3e41d12611941c014401500381d500c62280312400b501d04038456404508240400b055030b000b846001ea2100000c03040540e8480d283e51b03201007200380c892002d81c80d242d001c1921200f402c40803d02c01c5000c2e5900104600b00000d150541e074584050701d02c80c0d5400410882c3d100c400511880340d45010301200c4100e9800d22038003950556468148840d41120204100322201d40042c0a00c0144800849080d2020094802c0f550030010500e010305101e008800c040d1003507020004001540f00b04071241c41e80c0140700411191210b82c00c00554004c6403000540c41042030101805682c1d0178002460840c144806501c1c160385800e = true := by decide +kernel

theorem cover : BRFrame.Cov 623201438 623381294 := by
  have h0 := BRFrame.cov_init 623201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 623201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 623201438 ≤ n) (h2 : n < 623381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
