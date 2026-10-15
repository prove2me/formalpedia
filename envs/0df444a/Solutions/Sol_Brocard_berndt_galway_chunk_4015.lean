-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:19:40.744798+00:00
-- url     : https://prove2.me/submissions/e1a5d3a8-0e2b-401d-8766-ccb991fb7d16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 721942446 ≤ n < 722122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 721943696 1250 721942446 721942453
    0x60b030f06190b0a0509272205100e0109020d0f0219080c010f120e06240102030f0a0201060302040c020d14090604030615090203040b1803030c0a03020a030603020909 73
    0x14a02d40355200721040d100c0100c52640403498010b2984250081c0c41c5000300b448404600d804040c0c07681415000640d4044038140780844020000001c000401d84480c5020505520060500d445072074142c08101d500800414280c00b03243c1043c00282860300103030785595200c040f60405a92101030800710540110f09000e900500d500c10021031480300d60805a2280e00ca80c02003002900100c0e40c0542c0140a0802580407412008101c3e000d41030104c10b214960700d00b045c40302c1000c030300181c0584580f04496031040069504204c1140e84040c484070700e40164001c00ca810740d080c9031200500032070007440c000810b006840781c6c0082e003511443c0691000590020101c40b203402d0703002c04200210031000009900e001039182c0400c4c2c0b18807840c000502a551600c41d107844480d80c0d03905260003440d00380c60454072401c180c030301b180708484103507114034a00400400d09008042d000c0b0481e80200700305102c0600d0201c11070740640103500101c0401c2c06241c4e440c000000981c49244c1b541307206414004c040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721944946 1250 721943696 721943701
    0x9080403050d0306060c0809190801060f0e0c09150703090e010b0702010e0a050108010b07050f010203090d1218061d070311101b022e03061404020a0806040e01060b030f 74
    0x50880340e02c1d80c03207102044014180900422049400c48e80c2c914000c2c1c990444918089002c4440140140e219040c1503103010030029940c00f004104078141d42c0d002e60030b02841d480d91004c00e05c660062070b10050b806940075074500c0c1c100101c0801010114070034101130000c1c40d614560002030340c90982c0103105660001030403000319a03200a8280c680d1408a41d09400303642000c0000740081414044d40c0c005080c0051414240202041401380c5125250001c1d035591511412080d1203c0e032030200700c004107803960713010307580c0343c0560003042000b84d030803c0d40440d516665256403002d04000c128245c0406c05140c0d080d264101d05100c8400618010101c0b0f03030500b540d9105005400c4032003400001009150b94616005080001221010b1034048078080030310f101251481d00b4104a0b6800030f0200d585443c1258035280d0141c000c80c0071a100b0f40d504129410500c0248000c0c1d129100c0d20000183c0014001426842c099000001c1d9581041c000109503880ea902c03c495940207458694030038018504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 721946196 1250 721944946 721944973
    0x310080d09050a090e1509032206020c0105030f0a0504060204241409091b040e1f090506030613030908010c051c0603051f1104030f05100b060406120908040305 70
    0x80000414810b002004548a0600e10b140c59001710081a98480d041b0380105003001010000e0310210301081c800c400340358000e0000c403120600c2c51310414000d0300580d0040d0301e640d0302910540b403041c0d0303840352170348020760720283d01c10020070008000300c0c2c615900740300100304d444042001014121100700010820b1040300806000c0a1000172840802c520401c07603c640c5888400c00f55403c03c00328001001c0e003000c880a41c1d800d500840d0400c104840001d401c00100c00d000031302d1000c10384012b070280c1c0c5046440f01c0c0b4400a13a0400c8030780641550104001c1450b0b420400c0622500e0b07802482c000a82544500800b401d40d910a00c40e20002800880c040030b20000c00d8290a10740d581c548010412039103156140f686540011100c1c078105040c25291030110109a00300364400d40c8259078039a503594403072130880081e004102042c4c5952141020a00c24241303503105040108070001c10341824503152000403101d03030042c030f2420458552120f9050000a498030041e1001e14403500103000600d12502 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 721947446 1250 721946196 721946209
    0x6060b0901021c0e01031109090907150504030f120201110f070c0806010311060d0b040216060c080402010e2101050403090e101a160f03050d06290310080d0905 70
    0x21001c00100304070503c0c3c0030055041628001101c07000e0070045020f04040401018500900000603003000b036800400c8a4801c1c081181420b407201e1945110014240280485060007507010007000e810580d450038002c91150003894030400030500c000304c2da0b00446050140075421100302418211008aa03050400c24003549207009440c042005040640c55600c41940203250146500e0260800040d0b488240b60700750014603480d4005003056544005c5503030b07040324062624605807034240c43e041030b01022510800301d03e805580c0503511406645000d030f00f00500700265001d80f00c2060296082c0464400c8203004061059000303489500f8250310700414044036442c01001406044010001400404403240c0b0143c2c2c0704007607060642d01e0b501c100926415100e0074100141c003400707100f4503040416601400600d50008060000d0249541c1e03198400b0343c101e07104115a0281e008a86030101c80c210b09000355910406500506820f2340d0794803c55414008482107440015240250511182c10401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 721948696 1250 721947446 721947463
    0x70b090607050f2d10020304020d051f06120c0e07020709240602030418021809040606091a090a0b010315060201091b1d040827040506060c070905040f06060b090102 72
    0x140c21130b440000341c558a0310384512500600008442c5d0210200d002e41d2100d1429540f400c0d8000100c80b50a84026814005511203100100e0780c60300388080440e4a03000b11541091440d40400b4a003039071800d084041000e00d400030718220843c807642c500003511560501074060240d1440112200141c0c001240d0200801182c01c10015540104820403940380d01181a03021240c15981c0142c032079034610740c41c00303c140280c42090f0303000104005200c140b04041e8010f00c1290450748040001d45100b2162103014251007100b950f04c5001c1e0307400600d55420700c0d00004130481c0140350014103042c0c00013820300d054041d0b4209100603956805030b84100315104400d01400c59140080f200ca1602d8416480c0e000b9401d071400402c4120309502190402944009071000e50350030b002c078803e07482401d03025004400e405001031407080e810217001c40c85505103401103440c2c06543c07401810400d403c02d0704100191501170030840d0135500b00340c100c0c0045880740c0305000203002c401100990301c8402c500024500000d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 721949946 1250 721948696 721948753
    0x1a0d14120d0506060a020a380907050f1309050304090c080a0c021c300c09140f1203040e0c21091b010c050d02010c17010503070b090607050f 62
    0xf0172140d1801900080d039283c1d000d5201000c940c102c41b0100e000c664410701464005c0e000703a0f206140d22444902c82c80c0c028403d120602c1221001940d800400c60890510700e079040c1c1107142d1284c0302d074210a0a42118040c180078030700300c9250540c0e48598008548007070340081c000900e284180301c140e0006008007100b41e0201c0c03008141d550500d8550400030ba464462030814031083c10035495a41110003640001c03021403079050341c01903900c000005c01401540b0113120020b1901100425172581e00d00901c4480340300036184020301003611061103a2034120320726840302da00c81808001075150802035071138440d549107414141c9804000f05c400568403090510340400d02000820411917900014804860809a512103640c4c1602038005031842c904641026209004511100c202640c054001d86541c1c40103980e60005512048079981d0b07080400c1c081c00703505410021003000030b898154068558401c00402c402d2400d143e0382d0b10303a860a005c100d010300ca9504041c6900c102114640407400310640c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 721951196 1250 721949946 721949959
    0x111603170c12010b07020d02040603080915030c040512030d02070609120c150f1508010e0c030d02151504020304140c01110c24120610031a0d14120d0506 67
    0x1100402d4001c00e05004901d0000c801040316000e40d0707180c503c40100303950050002c00909460382450081980102c1c0a10300403186514411042507400c012a031240c0701f0301401c60305142c2020200017214801d0094010365100501181410400c3ca200600a00b440394000041039806071500303901014007054280140140d561002000c61407200550f030b11007029110001c0d103501c101c490f04008242c45a092101049a041c002c9522101503000b01c950560355021078813020359000406654010f80381d54100143c001c00008002030702c0c4034007801e4001c0d49034042400303d1108040842c00b00d80040780c040d203240030721404512210030103011814403603000b880c20b00500320384603540a5449060301390190180c0c10010560a0044151a0040d12141c051003015a24901c0e01c17035607945600181c3d2407038456a00c045a02509900921400a84031200145020300c505030000700f212640c443c01d01590003051031000c0981c110024040810313003910480200b0b44031108040341201725400100b0b803501405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 721952446 1250 721951196 721951207
    0x605040b060a1202040f031a160c0f06060b0a0320160b040f1b060f02030313030809012d140105031203090a0804060e0306090a03050d111603170c 64
    0x1100d020454035620b00074101407103240590100d4070002c0c0f0a640c8114a20804100080108003240c44c0030f0240d443c1907580d400450b01c0b0340c48407000118181c0070030004075041d034501d180003555110320824601e00441000644d26521040ca8010781d00400c00c2c0c8000a5a416869810422107043d054003c6a4245080c0c20064040da15500c08840b249024040c142d01400140810002d005803000107644000f0440e00c411814101c00030b902001d00801c03000c104158141b0302e420744008240d920441100d440019041c01a44094816401c041d14010155480760040d0301946841d00c4c00d143d40016103201d09a191908110440454070f2100c21000821030318001005950740010740c810f250324480300b0f11903a07611075250f1240b5040c040c2000a01c19000481c00013401c1d500000703260a403a0095082da8880d5440d14006c580301c096010b0b00502249080c0030f89401ca03d91a486610700040004040c1c0c60001640c55644410b00c080b001180010820000c131140920320056054000303220100d02d90810f0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 721953696 1250 721952446 721952449
    0x15020c09061201090804090e060903122202030a0302160503060c0901180e010810060b030717130203100c1e020c0d0606030b090601080f070821071e060605040b 70
    0x619024180501c10444800c5a1501400079440013021035800010340796107035900c5582d0006801e41c3c6003c404c05000b00400185111404402c6541c0886c40060b00400380e9500210240c1031503041e4142c0c20560112b002200c01610100040082140660010705a1a1070040c1c2c6141d0000340d5000540130340c2050050164404884003641c50489003400c01c10030007000c00c0017103c2c82101647c0000c40d01540e4100028024102023421041e20054030300610843c3d88494405001b0322040e0341420000740c41c20820350050b69001300003a0080d401c00701114200315a600060301d4410038107003c0181690b00e000c0345450300d40245000700ca040e0542c0c03000c9000c0c45201c0000c0e44851350441c1143c0107500012040c410424140e00c8040515800100c004040c1407041500e239a4480c00d000c1c1c44403c2c401c000680c00035407030004070036003180d811600620341c88090f4040101020b0030310b031046282d08010f228100015039181140380340d00710720001c002005801c40c00d02205403002c5a01040c040d514083c40c03030003103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 721954946 1250 721953696 721953709
    0x60a080601210c08220807060e0c061305042009190909060f0b0f030303041104061805060a140f01121d0609060a0c080106050307020708070b0418060509010512030d0c080115020c 78
    0x8160088e03400180e4500700d00c40a81001840300407654810320025281100c0b4460340c60031001e4a8080c1c600300f20210000030249404540b079010f9060520042c00000790038034000d03001c02032850000d5401d005180d0b80e031408000b03548000c81c048411b103484003e141100442c51040d2040c680e403c0711a18484e02e10303040402d07102d00c0050409040c443c80e0312070050301034503241c000d20005c0c0704a100c0071031600150307499400281810f4030440c3c81a19071100008600c011500703000740c5441c0061401039442c0409005440284481d21140f0145455420030f0704c40890ba00001841c2c0300ca2000906264a0700003015818803400900340180145010340310001c0e0743d030155215042d5003076414031503036a44565100381e00c0c2c02d04d40d6204c0055446003140104800341ea0102900848100043d4058100708200383c420554110707025a641080c0b070740c0010803141c0340040e4ac0015225109003aa483d011400c00740e00c0680c0c500e0b000c900701051411780108412a20040048070303c000da4405000210000c5000410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 721956196 1250 721954946 721954957
    0x4031103070303082d041a0901050c0a0318080d09120215012d0303120c05090f1005040306060b030618061810091a0f060a080601210c082208 62
    0xa2629203400c1441e80380c0200c52480c0e51003480c00141e06100d20341885d00300c247e00c0f2285980581d80d5100701c080f039014203050140b28000c05041205d58100020414100c0040018409240d0a40c5030036035198081103440e401018000503452000c0b810030318a081500c007012b0782c0b580800071540400301d91a0020382d0b03104041d0649034201032007548410100258410440c05aa52001c0a135801c5030000401d6000000c02c0004032125400f4081d140203188240ca25010341c40c103880d003204c0f0400a0303070342d0b0380740229a04070324803064202982842d450752905001ca55032a005107921220000c24080640b07010b144030b00280d800c10b46407c5c207a02c0d2041c007044207650a51a221001031601000c00c1c0346504041c60380d07014100d0f901003040440c1d4a482c100c4407801e0304a0000f40210039a0951198908004040f2009803407503444102c116210140111200060551040c188641d64410038662082d43e000b4580b01000a603211866420110101d480ca540f8001c41c1c4000f8000380317a00360001408040903142d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 721957446 1250 721956196 721956211
    0x103080d0207020609040507020d020708030a0503150301150305030703080a2a0516111302250c12080d0b04020913090c03050f0d12060609090b0a0b0f0403110307030308 74
    0x1a00d0360503910114070580174091710b29034030904000801540750b50010302c0c0003041d06540d0842d0741083c3d80f2480c10b40ca9100703140603500010340c2080081c5240d0a04e00d42190704c004068000075078000e42200c0d964807800c00d50000c0325103030000100300b814198000c120356000207840070304110701010711480c2a5100218a10500c084180c082c5100000d4010790a54140004848500e040c101d203602c1d0101d001d64132076140a200303881c6642c59604150302072091340d9410303c110035800d4441e402441c0c500141080c01d01d003101d9108070b6100124050742c031a03005001a510031100a61150601c407140c0d02910300086065000fa403050210280c5643d0f0007000c518110020a40015810070340e00b0030452901c0d20b03030005481c0f8400c0018500da080d100003051441c0b501c40b13a076510b041101000c03580056680314440c2a0000d4501d450a02400c1c0069110030080c40c4018010018260343c2d541c041701942082e803012044c6a8045020010300619a80b02030880310110050901d09040d90380c0a03141c0d920180c20700 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 721958696 1250 721957446 721957451
    0xf010e010f0c0803130506090d0804200402120601020c011823100206071205090a030e04020d0e060601030b032d0a0f1b14031e07120c090605090103080d 67
    0x800d0042c040d0418810007034201d0001c69580c941440c003034203074030b000090854051003210001000302001041702508504030703517981529901c1d603131140c035503401c1d540c448000303008560001d40600c4c0d62540b00600320706000e144201c26503e8144006410046050042c90600010514413410107402c01e07c084140d407045100302c0c50058403021010398450814040c02d070006c3c5e140e49141d020f15000241c180c0b04007202c1c0d03194045c0001014076082990000d980d1641581c0c0020002d00000c0d000e038958074007507400900018244424900c2c0c900c01d8801201c00c0f0070b50380c0c0000d0207100c82540e241c000c0a000c81b40503030007002c211a003243c485409048601e144111218440c851510207101803005164840e0417403003498039110507003011003403c8046c3c8646005085850320010b54050b0700c1586108800000b00640200003041084d031480700400382815004d8041d82c800428202c848036440c40016002e06529183d9070700300000d4004540780c0ba0029889091004010000034a001e400c50301d8400040402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 721959946 1250 721958696 721958717
    0xc0c02090a0e030c10060906050d050c01030f0e03030a0501050a050315010e04050111180a050406060f1d120a02040e030f0f07031209061406040c021213320f010e01 72
    0x10542140513400749000075001d0f412403a4900c2117290080001d907807898904019131039442003000f50003500342c18000c10580108242e05165070280d0b0001c040c0920b100d80128022146409950465008641c504145550f0348010b106505202c032010000c0d000580c000c1140c060602d020f61759150051050484507aa5140080e041000a412050242c24000b040a46031700348200d08403040c0030000300460003528409800141840c5c0f500408044500a80340c0182c80e18110404030740b5002c00400e15020b4504204902c0c2ca00d459500c0d50303560101c8000c0207407101c8000b51040000383c80341500031950340e510902030b025108140c04201c600483c2c400071916610103040c81c045c0d44c40800c031690300451a203480013540030b1103056000b00312072b00b4078030682440e0f0f9501d0f00100012914040a2480180d10403216545035038140c0c001059802010700a01d40c20310380d43c0c1c1d0700d44500b940c4c880000c80f00168441002c00b40d0076103980103031000b46089404500070300d02040001c0c04030318070580550400084800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 721961196 1250 721959946 721959971
    0x504030f08040e010815130b04030f0309050303100602100504120f0c15020c0d030c05040513090210050a1106160f051e0418020f0d05061815040c0c02090a 68
    0x80b90001c00c0056048112980d4480501d43c0314003209440a43c20402500003402d401c0109610303640041d0300080c6040184c450340c8003103078822081405c29040c10380e01d0b02c0140216030208050340c450b81c03d03002007003446810b20343d0084c24800302000d00403640781000203000014000f0700444040004e546880c13402d1402c0b038581251030310b080c1503001c2d00031042411000c400c0d40c4590024208454038008a03402004151011012101d000201d071000903018031040c0a2451f240403942d00300b04c00110041005072458000801c0d0000f003035583c40202d80005800e01c9001d822081b201200303805a00036100500d0003080c4260300072818800703001000040100003981c9400781054a540c17130541044824120358048003580c0b5940540500c451000010481d80c0b8203098a00865092103014021181444101e1640c00080c3c07101401c00e0707501080000b00c048500f1084900c55100c0d004c080140c800e8170400c0c0b81808111130040780c101c0d00b0064451704110158940401d03460b0094031015000400312046c02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 721962446 1250 721961196 721961213
    0x412031205070305100519060e240301090b1507020d020418050a06050a06080316051c030506040c0f08041104110f12070e1005090a0b040e1e070504030f 67
    0x45050240d03441c00081c0900d1a9040d88050f2080705200a06001203450304100500e0b180c640400500200c50071f44e0901c9003c0c8a051070904c00342000c0c0c94012845a0460100b1214403000c90300c1308201c5000c00100220b403802d0180302107007401030714171044d141d409401c200a94071442c0c0020380108802e19000c011034070740341d11402c1605070007140c110094400f80303040c54507036104440c15208142000c002c12014001840390300c1c100d81c0030000840c5441c1c0d12a08025107908208001e8419004c2d400d40e403001d15840b051602e92544183c0d40001f40751a02804000c210350801042c18100240a030310800069080000c0035045600101000007501000e00000c0160680c0007072100c03400c0000c070300d080480035818050f100c414204c3d522030f102070b03071049000c0711070764800b2aa165000a80035034a0303400d01d004da00140010302c1c0c040c0141030601c0e152410081180d000b6800300340030603894010400d4002460a00c44450303440e0713000d08059410144da00420a008600003c0e001851004100c0104200203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 721963696 1250 721962446 721962467
    0x40204081b0402041a0703051c021b03090d020d050f01020406200a0f1b091805060105091e090c1e13060f14030a12030506010228060b030c04110d0c0504050303041203 73
    0x80d5150280b0749c403914500d400383d00b051029888410140e0b6143d82c83c00380102c143d41082c080901170258000c0302d2340030024a403070035800580f114000c8640440034013900380000e1003d08a140c64800c0b420146454002481c074001c0d94000310ae030812200500014855880c2e007025a8006004501c0035020714501004040107901c60b5407402d15080d12030340d881420710240c0c5503190160094400036a621000d0064484003103902c50804511070340402c0d108082c08500b140c0040c400c20032a10000c8080c00480e0903201c0c8140002c1108007204070000e5589410480103403402c102c0e240900c2214940795051948520b00d0080040005210800e03040640742008800d80c11a04040b200e00a800c0e0180054014002902d44500502410743e80f909000985d80b484056440c094000e041da110060311018000c0011905442e0b141c06101d55a05090303803103010760f1992603d8195403640d01c2505900300340485568160b140c081c0030042c0001c00007594048141d800f110a4100c00751441a03c40ca42240c003805d41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 721964946 1250 721963696 721963717
    0xc030512120f220c05120a0506011e0f030b04201f180b0306181b090a030503071b060e06041406130306090312050402030303061e040204081b0402041a070305 69
    0xc0c031145030902a101c110138040750426940200a00108800c0913210f03242008040e16561001004001a60304818203207000d4001500c84a0000d880e4907078580c0ba014540d00589000850105000c00c1c04184810b0400b0140c5c100b03d26804101e410000ca04d0178030301e180000710400165041802c05c60f0284504c1c1449511520300d1031342d003580744d0030a040d403600292002d500403500040d0081d8440485200580540440490003003202c0408000e90391503845640da6581145e040040040069404c2002d4150f203440ba0070101195480020305c074200000d00e0f03100d241040291282e09200303403600421034040c0c840e81d00112940010385008240740d172240500141c01900c013104008140500f0342c2c0300c404814400da48068401413180c42c1502a00c40548019505820800100d1b08134a003801d002500c02c0403106981d41c0f0303840c0400c00034003280c00c20390200d5500c0c0c01807001c180c0440e15000384008840000c6804504060030a102c420010030b80f0380380070344402c00000e103003024140030780c017660780c003040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 721966196 1250 721964946 721965001
    0x515130e01020f043006150f030b0906100620010b0a03050d020606100914010309080d0605040506030f0604080f0403060c1713020f0609040f090c030512120f 69
    0x2038440f00310300c0683c098032504558003010b641349070004242c0103007802c01007007010030460b5000e4140ca60384000d00c5051000350b80c07160200000111950325291a000450141c03801c0f00e038a04d081d0390700324101301008082a030001d51f0310009010703050304003410060b010b42c1c02103a4040028071500080c0100401c908541c0c0c00f0720550320020801800040c01121044680c1c00d8403030300e07241c0704103001c525074110b00c4035000f040b00e030b44c400c1c8901c2c00020700780745445a0500d00800c0805054452604a92041e000881855140c02061001e0300b401e005440e08031030160024050201d007009000d0b21114003402c002c10390800020070a0081d900c01090b2000785812010401c0188a8034501074892246046403032140841d4100143c2c20784103005241203c990042c00c00401a42c019040006650191030710507440f41e5205801d40169001e449000c0710750f44200030400c452030950801c103141c241d180700b5006041d50304114540000c042840600d41003220b43c0c94961031502c40001d0340030100c406030b51201c1b000c103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 721967446 1250 721966196 721966207
    0x100f020d05090304060f03060501020d05070302032b0b0105030f04080c0a050613170a1d04021c0905120c0a021009030204050a29061c091a0601020d030515130e0102 72
    0x350100c01001151001c5e01c6406d480e40e09000264142c0380c03980328181c090380140c560004154090401002d038148203205682c50000702c0d02d44012889038616000c62103401c81502c0c0001d085291041141064003420480c1c2980741c00c0d240e40d03140231070040c4000d05000000c1001c080d640420444010300302d80c01420740d0350601d0f01d0020030301990111802034801000f500d034540c00d01d8406038200c512140c669911340e048d010008021041c01404442201c1c3c00c00c0d8200310000c3d501c1c11300350414141140e06803020440d0b0b005414103919052031003900c40000c80007002039100e522400215282d07140c0d0b05881030541e103030a280701920110040c2c0c0c0060340041c2001c041100c0703881d440d40301e12480841e406000211400b80122481e44007000100260403c104006060944c940c64640d25110404803802013407203140e540d1040070340f00a80e0300b0f1a0f03580e14401c09110b503540e014070850312214a00e240c20410351811203070050725100145d1038107018912501007804680202c0e04480040c2920340000d550781c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 721968696 1250 721967446 721967461
    0x308030f07020c013615050903070905010e01120305041703120f06031f020c010c0909111306080402010c140a0c08010903230c0a06091a09100f020d05 66
    0x40388119400c40c0180520f0250080a42c021022032420400c166002812103052510708020503444603042c0c041140344100004000c3c50035119199860015500c1c607884e0f1207003805262030102d082d0045a095402c0c000103202d5101c26500c80c07030445940c54071965011015040a03038052040d50003408010400004d030054841c8000020a100d03040c04a024030785950f07014150050913810f0351641ea040d040170983d800340008241c003100d00c400241d4401890000343c11b03801800c40742600c8a80010640d010300c10004440207210348a00f082041c4211850940590700e021340303d1940780118000c0c4601c81e004107082d6441031542d118090391142c2036811300390454124607510206080d048900e01104040070403000e80c11b01481000360b5054444100105004001c0c81c003080b28110365058506c028001483c8460382040000c1509014039000100d2400030704244100c00c0b101c00ca003c041e1100b80007800440800041c0c5000c04081c803000001c0c040411404940c00b0744a8000004601ca06003800d103e580e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 721969946 1250 721968696 721968721
    0xc0309030f0309180b131508150f0c13030204050901150905160203090a030b25030606030509030a12150b040b0c0606010c03020c0d0f0b1305101103061504030803 71
    0x3601e0408400762903000781541c500041d143c02c5d4480743e41000d02040280c041c42c140e600021490500c442081e2042a151f801075450540034083ca07036050300d003d45c1400316480303a221020350041c0030044900e1502a03001c00c4a500600d85200003401190355900250903150294003500c46001e40000b0800955562181d82000e0a000d071802042109404645075616000200b103d0b420a4050180d00c8031381e140d5151041c010304018401001028503a0010103100c80c00590310300c0d00100ca40b000206a809d2000040445034020410300a41d40100003a0701c0b0386802c03500a0710704130340448001c03072000b00c880000c40102c0304551040d000407401090118011088601802c60244140c04070b400d1640c50f46c0044030a04071440002e000341c1c2001c41c4212150401500c0020481c0c0030300001500c80701160343e6200c080008031000304038802c0551001d070070070a00703003e081d158007a0030609020a684051011241c0d11028043c20300c00d1000c001206100302d1442c05440c021071b00103281a80324600081c8080c40c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 721971196 1250 721969946 721969949
    0x60e131e09060c09060e13020702100815060c1b060405040f2702060301120503070804060f0f02030c031803070302090405060a0e19060c11011803020115050102030304030c0309030f0309 81
    0x72000d042055506943d0311503181d400403505195903881030040c00b2824000207100110b8141100c94080001001503100d001606d241c0802d6075a40801c546840d40c20b4156030114000014031400c4100710400f4404000aa613a4032001070081202d6409404400200c06200b00d40c001078003c0c1c1001c144a4000303210340d00548480c2005202504255980e00c0140069100c0e01d034001d51112040c401882022202d070f241968961041c0d080703d01c0c0101715103c0c510540c00586c420303030020719454945240c01e0740c07154024031900303280d00066040c100c10545c42c58490140442100e80d45411000d00001035500700900001560041e140d0078842c2018107280e078407420201c50195246003010000550f80400060210b4101941d064020313030341441d952218080d20b40301d5484c030100501403101c440e41810030b03c60003503c024600100c0150000034a40039080d02c41100e0100c141c0503050008102c0c590700441180e03441541407810032a071300d289103400d45905105800140000e10050050820590054140c10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 721972446 1250 721971196 721971203
    0x1031401090308065103062206090204030c030311010b01081f0f0b04050307061106073002041d0402180c070510060918050d0503130519030315060e131e09 68
    0x40d00030011401c0d000b6a4803042d201f4030b8200380c0c000030fa13400c81e251045c070742c5102090f440c0000c64140d55400109040c2d8106401c2524100c0305080204105604074400d45e4000914800900c0420354500000e824100c00904c10001075000b83e0700c0f0810000d810984101078003010802044a980320300c034000799900300f80a0300d0700910032250003060440c024942d00788031904000091043d0765500e00301315903c440f5049005400c03c3c04101c1311014502802c4010703070020304a0f40c0140c80340d2070f105c020080c1e00400d1460b20020400b400900016072291001d4201945618800411540320402d0b41c20407031064003130281c01c0d400b0301040c40700c2340066500b100c81213035130a8606101d4160071450000708611340150040150f440905a41c61240c0200080c6501c4100c0c160120090181a1155420f0900018000d02c0010b8032030204410940c15209040390200ca0b480745250050400304090218200c501416200302e070f55041422500000da0401030201c00c503a40c1e07880034840c81d5405a0040c280304041103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 721973696 1250 721972446 721972579
    0x30f070510020619020a0c08071101020c060f0d0515060a0c0b0c0406021c031d031216080a020f091f03240512010204050301090b0103140109030806 65
    0x1c40602c0081d45502410031001400b404411118100000750311000c0c855092011645105c0c0103e840d030b07005401e410f40100e60300d2480f203851000090030801241c0b440352282c241070080e0251340b8410000c0e00c41c4409084c0e4000f0709a00d9090040450040e010f207140d03400741000a110f81c003240d0020403101070034403c050fa9580d40d05c6d0346841c48494001c3d030042d0b00c0103070f0096624120052042c165128184a141000510010402c0b03120941d178440c2d0800c9609035000107401100401000d00d01d66004409007045030340c001d03125170b0040c2010805030050705d4a40d0081a11407400c88403400302c3e60f4594006280018a40a00c221217418000348030820001c24600036240300c84920484010840c924101c10700c085440c2003e0070440e400070464200c1c0899036080c480460a07440921944440300c0c01906645010740c5103103828985440200d02102c281e0b41401d802c480040d4200e0720498004008548040000b810f0001c008040805407114651413914101522404205003040d00c0040040e030246 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 721974946 1250 721973696 721973719
    0x9122904051027020907110d0e01110106050f0112020405032b02070806160c0c0f0510020d080c16021f03180c0e0403020f010e0304171506040b03070302030f0705 71
    0xf41101d0318612032036641858108448440146040c0408941c03141c1c59040688101940903102d516000499100700b01013020f84034201025a008008056408408030013803040074201008a1b100040140e138441c1800007500703c0c118040003d40559015181c003400315403c4040746810b06044085002c0100c0040c0e014406c0e00c40707140d10114620f02552181c000920b49529003540f20111800700d41405410020341140c440c0000e1301c00e500101c014942181e000351000c1c241010070210a888099034829913001c02c0c030580c0c10a8009011703503442030200c41180d0b00c800640300b80c80d1041569000c000d43c000d9580180d20b04c041103141d01000040080d5900304010080e84600c0003041c84004400342614142410801c100300d20180741c2641b00e0b101384166952030840c50855801d44141200c0c1000716000440c0034005103c1030085110501c4201005000ea981031a8800031207000c0640030780d000d01d03162020300d01542c41c2004042d0003541d002e8101c545d401d9400c00e1258031346906020f903d201d803a0038042c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 721976196 1250 721974946 721974971
    0x308120c0c1522052109130b01110f0705130b12010c08010b130b0a090e0705070510140a0b0a050616050c0901180213050d120f091229040510 62
    0x160025141c3c0700004007001c029030410424018411040e11505c11000c102d00c400c140c6803046c0704407103041903042c00300d080b08149001400042c1c00c0400501e15900000c45079043d0f101c00100710003294010ba0f11824071165912520003d0404250303929088000d84000c21800007055021030003001c00e580e82c41d40181d80701c00b006490362081c203429101e2101803110030701551003030700024507900384241800300140d603803a0300b8042101c40031540d00010900118501c07050040a005d0036002000b40201044500c803d024110109140904010080c0b5034401c001d00150721600b80d40300107004014081c42d00d07540d859000008206029000701d40324040c200c5018204c0c280500c40034103803105d20300445004c410f88120340c40250001803e15544c0d0340c0701800020107899001c01e00310f006000e0403c5c20030b500070402014040e80d105880003410840c010000700304800981c501c002d411584010880b000ca403903170baa6500c2001c041d119451801e41d8850510003040400691041c5d0654400d4080c003140c2240c41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 721977446 1250 721976196 721976251
    0x807020d050f04091a090106091802090901120203070e0901091e03090b0d06031208071707021e0102090a08031b03070b0a0209030102070b070302031f0308120c0c15 72
    0x26064940c000602c03040c0000e070242d40185e40c1300c4007000019034900c48650001620035000303078001c50102c1c0c00f44c0024071040c11000e01e0aa000351203031500398517019000000c121102414071070100c0341190564000c0840d42c007030258900510003c0c008100314148001168003d00e51341c0e4084a03140440b20b55402e100f4420540d62003140e8160315070803030261400554003a00d80c0030383c0030001119594400800000c03244412450000c440d03944d035072918900707808043c1804104c0e1030b9400a205481040004403030340011016401c11a4409043c0403101450ba002c0c0a03001c0c2d8a12a5800420030101003203001c0000068061281640048211101d04041407a100d10641ca0042d040c10707245000034204001c1030b0018901d01c81c0c054001451701c0d103d9262004e46a02c10390314000040d0b00003040c0b205804040e41400d500c0840031260040083c650340d1542214460703144c040f03d440d20141c0c005104c041500082e517003140c52035000d0b0340329801c1140c13003404000d40444000608414042d1601840c03503084 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 721978696 1250 721977446 721977457
    0xa021b01050601020d02211c060815010b0315040b0a0e0f0406060f0602070605070311150402030c010e0d1506030f081e090607020409020609130509060a020a0c111305070807020d05 79
    0x409080403010905414070707071140e20044040d00c0703910640307088c0001070b081441104000c0c2642d00290080721503000c3c1c444a81c420690050784410b10034018410a00b6000720301840d0000d0840740084c82c104400301181482881358031800c00513851504121000382541e207424420392145c001044101e0315401e24000300c504a003d00070060313000780414411079025000901d80315001c1c1c1880344841c0907001c0040e00e0021168180c60100c0000310601003141410442c0c119208000d0a095658034526000b0030505004e21002520440115003540b540708203070380c808006540c2040503d0204407180c1891800c0d0350111840e040443c042e031403026800744000b010b031407000c0c4000702076a140c140c26800708005007070924000d9034015820000c1840c46e0350303168054094080c2c04400072501d880c0210060b42400001000e0030a200e0041049008090f400b9612034181da502c804010882c4811402140702213042100b2050340c40d02e0f1405200782140c20900842c8640726a1b4219206c8182d50403080301d150040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 721979946 1250 721978696 721978723
    0x2a0c0c0d0b130303110412030906050a0e06130f0611060a050402060901180509090703030e0a05010509060c100911100c0314090d020406091401060306031a0a021b01050601020d02 78
    0x610045440d0800d20301d100c0316803d02924000c6910318110661200680c0030340e010f820078800c0c1c2c0c0c14107410150001860b00040c050345c104141024a50b0f0805070038020040304491040e00001006041c0c01211840100901501102c2c014215112103001d489030091010844e03151103808006010b401c080c2c081c80784142e41c050081400c00d40e1090054551601103040c00b1340301900e000b4007080588564446a00c905c6450008021a0f880e60801400126101001307a000e25580c0d48e040c042030340c002007118400f000030f4910030381d10f191200c980f500b01480809400103043c01d10384604203100200460b60700c09502110160001c0c0b410702c01c240c0324030507101c400801048009006503c2030510001806000d000070701407030032060700c3c2e6000604448480d0854001c541d17403080d68607208010200342e24007405890404100b15800d5884408121001c00030748a1341b040307203100062a011264040d140c41a11141001c0050000303803815a000c0c00040b00ca00740103114010001640c58400500c2c3ca050114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 721981196 1250 721979946 721979963
    0x51806100302121c02031c1808090105070b0a092015090d0803040507030501050105031b0411040e040b041202010b0d0b060303041d010f05010519082a0c0c0d 69
    0x10310b40c20b010410141000800e100e0140d9041c0042460380c480302001c4001c110740c044e50780c0d00c0700032039000144500000d186103030b0b500e400c0703007072050210000c82420501d400c014110344a01c00900101c44074441c0e03180081c14a02000148108400590001c40724107100310306111800706580074000c1c0e10303002d8800d5a0351081500303000c0701400501d0301c000c0c48044805000241103201e5520364134021740c030581e41154180d000c11010418800e00303100b21400342c03d00310054000a2030101d10040c0024600d00b0444c490b81c0c0c2c0702c55820590125804507401000c0ac00385020f480d00e45801c0c210102442201c080c0c45820715072100780507407441072062913003d400003000c201403022243c44529119500903c00768052004110124542e28401d040004c3c000d00800d800e0300543c140543c5020700300940d444241807040510a54001d200191401c411070b116902d840342c07040c4d41c2c10701051144030444460405100036402c000d12407000c548000c10900080104a41915207848107202158501810250440e174 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 721982446 1250 721981196 721981199
    0x602041701200a080402123a02070e18010f110901020c0a0b04090f02040b160317010e01330e0405150f0d060b18010312020105040c06031509060905180610 68
    0x282c047c4c44c0080401d05001111a8110a50f02c8042c081414070410540c0e03031400104040d4010004444206030700051018008440ca0082c8214203410081c01c0055442010341840c3d0900e0802d5018102c43d440c0300c40c05221628070301c2580002c0350300901e860350040c011210003007000d0818034050011101401581c030715141c50f201c0b1540007000c0501c00391401d00e4081100103010b00304c00c4007500114000c1019042154001c1c58081e01c9410402141541305c80c03050010064440004030f000d0440b101a205109800c204401c000a1000051015074608014001180c205a4002c41c02d5400071000e440802c195101d40d505840b05010140c2101c0c3c1c4510019404681070800d40100100300e4442d90307012078843c5000d030006801d840745a80100b038100d1148010000d201d12050802107400c0c041c00208541d0419407a80c11180e03102c1e001c0c4805164070303160010b480e9401100c2c55802484890005c100c06615400c5840117048251880618006002c101c03044c007660205440d4003e103a51032000d1141c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 721983696 1250 721982446 721982449
    0x3070303091d0f13062306090f0f040b0a0b0a15030c140702060705190506060f01050703170c070204060305030301080f0d0c03032019120b0307030f0602041701200a080402 75
    0x55101e03104031007441c2c480201c101006e610f4186955124411180b565240c50004103000c0049002030404c07420b040660103008581d20120070107034209400ca110424540d80d4041c44801400c2d4080f0040e411201d2060001180f00c00000059200159958203000e1728110700341c00c0f075145000f00b000c08040c00080002900524100c0c0c0203020361841242034a50010310400d1203032440100d0141a07445400101c208101c0340b41460010a0b00c5000b42020b60800308140c50082500f20140140d96a00b07070a40003041d10996400c054814055000707000b440855228038005440382c00a204140c06841005084190f184020440303542c03507206950342414000c0a03440480c040c00b0f652070700b07184034403202a0f48100c00c0343c62030080c90706a0044008052410b2650402020034441c400040110b0b8644401c14281c1d90340412840b049907004016959a90b0550602e4402840395600045487d030300c0403c5101d191302c0641019401c068016040c01c02d0107408404242d8074440c043c0c01d900022079900001c0c006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 721984946 1250 721983696 721983721
    0x22051c031215050d0c170703030215010b030414010e1b1c051b040b040603080c06060f100305060609100807090b03041e111003090b060f012c03070303091d0f 69
    0x980175644600040b0f0740c03180402000740044896030844e8106000c14014540c04200412034030400101e25810707581750041c44001800013a2008004621070340d282003441d4001d400006c518200c0d44103031140105065108000e05429042e414010a454015030311018104003103805041d801c41c014000c40710980f41c1c41031000619244555100c3d60703444500170540c80364441c001c0a180710329902a500d0000c07440c0103107409130003060244215143c1650242c540c4600c0b00303e240840300c5060201705030302c5030703400149a03001301c11a0682240c0319408003507401d64411400780c0500701ca6200c1000180c2ca03008422403a11003110060101c0c6402410841c0e407e9036225400c05040c06480404502686807000910901e00403100c000001e4480866509002c030704040f064208200704c3c0c0c41c05100c09000006083c00442100d10b0164800b0103440199000e1108202c00e0902c0004043d22030190301c0303140203030052406014045944400d580c1c8880700c8100040c1c1e4a00500000613900d1140d070390700303840200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 721986196 1250 721984946 721984969
    0x9010806070f140310081005040203070603090c03081206130209181503010c02161205191e0b01031110021e03130e01081c0522051c03121505 62
    0x204090801c0f080a009040d070051402120400c200a29480c605a0740034540421031840d40302c40791420092000607940096400111180350801042d64420360919103224842c562020341210400101c2c0032007180e8030300b00107128000c120743d41d4101e0f60341d4134044001ca0103502d090301d420640544003501300c40c441e0700d01b43d80d00c01030b910180d030003054010022078295104c608904000d0b910422062042e040320b02d2407040900315940d2041010003454035102d9464450a848000703001140c01d00b9410310404001e040d840645403030001040918a141501c0740301824402541e03035840e80050100640740113038032810300384101d40c020106a41400b00081e1560142806464244010841e415649044e944210000d04054804907042e61600c03280a0030001c2c4208444c4020841403960704c00ca640103000d91310310254420341089401c104003403540c050f007243d070410b41d84800195400c00c0120606008003541c030b40300341d0b2000c040400c1e0456030302c143c3d0805042d000c11205001d605100b9070620b0000c3c01c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 721987446 1250 721986196 721986227
    0x3130b1f12140312040303060518040618080f04093e0c0f010b0f031f020c100f050402040e0106140d0602070c030308101e0611010f02040902090f0901080607 69
    0x890b15205802c07100d15551209035030342d412014550400041c99014400d40008000545446101440040300c80c58901001000108850b41d6113149a007040d0304182003100440d4000c0d0015036a2603a05404407003070300544a8400c20034103010440300741d03800b000401c40c602150501e4801d072007911464600c1d550300c502e02401410580501050400400030805250011650000001c4015200c4180602c48482d9101e5a01a42c001d20004103040950079076010384800c2542c005880d08528a0054108407070300004038010b81c200030301034003541c0c252761069009a200302c600300080e4444824007800c0c7c40940c4100c10b00d19594032144051030501c10380c2c10060b240b0606005180c8145981c418030560fa142c2c105400181c041020009500d03100380f500d0024166000720360100c0b040e036810594003403040f402401c0c100303c02030440d00c02c511025004010702100e0041d06546403030f00d8007030140080d003040c5d0313106108215001440c09281040007519060701d00b5000945580c3e030783e81c4000c3d00c08840400366030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 721988696 1250 721987446 721987463
    0xe040902090a0c030e0c0901051002150a05070305070e0906010f0c0f060b090c03040210120207050d0e0f0103051e04140f011b032c03090603130b1f12 66
    0x100140d9800644074402c0c02e003080005141040d09400808a41c02d103000c26200b42d21a800700125695041119411200221501c0e00d00c84021513081703041c041400c100303006286910080c0100305041b50401031180840c0c0d03404102079070b00e511702125071400705055690050904070120f44c155103d15130508072030205041c035943c0c0c01c2c002d0f0354055420800354026140c0c1d42c3e541d1000e0545141c0103000a0700141d00b2100103042d0f04042c0c00041c0e54110b03403502c50090040b440700084c24800203030140e400c2c00e40c1205c256220140369180180650001c8943d0a20500d1240e00164056029105040c010b680b4813122050302043d00340c140060180190042d1011000007040a000740c1080080c0004c0074551070000c1000081008100b03500c03050700240005050504210201030104545c403101c0d4400b600d40d44c0094880000341c2141103216040e6550b410036000420002c030403500c160002c402900c1003030f4004203503990604160651004a0500091000104c02000b200d0b021840001c411405500c64 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 721989946 1250 721988696 721988711
    0x6100e011e11032107210c0c120e0f0a180504050109020d12080c0a0516150e0c15040f1a0f0d05150907121d0a031814100e04 55
    0x100c2c5140c210301e00c13140c620001021080718901400c56120741000f4035040c545449816540028201c08258141810455480450f0481d240c406c24209803155000444040384113000c0d00028090310b400d05203a0301900b030b010038031800717800c1071081d110460f8804809012420007020659010700000f0b8000c1e20550348940907030015130f58042d0350300c200c940b141da0a85602e03a443c18010708143c400600c00010b07503e080c04401001170b0000121511110b20003110a50150540360544511266070302c10350085180500101c01e002001034920201d000c1256268880c0c00b84814060140c07050340589151508400410050665026084620000d03114080c43c1801210307000000c0325000250400c05543d2918240502c040d07984901080d80f0800b82d801c00c4485c5401c000251072020659800c00b52190703504050303035030b9202d020b48500c2a41541010b4640540150a004000d07003d0007406d8129087c003040005001441d007440e410029501911301031a101c16100140d440e1901d02d100e060300180c44009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 721991196 1250 721989946 721989977
    0x30606080c31180c0f0f2615090c0a1e0c0503300103020f130b06120f0106080103030e01050a020c0a06020d0f030605060405040213030b07030506100e011e 68
    0x7404405070480020490743c08070b00c008035a0a4440c0c0c501044140b100301c001c0c6060765035000000ca00c3d000c20710f00307086000c178010002d51100c00b04e5010ba201d034001c81420a0085110040e6001b00e02c42404450b95110f9465402c21460341d44140c42121002c50241d413100080c11001010b6403d10b03101d64200340013594056101c0c40e04682c448941d1030110746200c40070100c4005004500b00d1050002100c500b100d60540d408500c1380714803412007a01c550500c034591865a0420303007140b20440340c058615078841211510492429901340c40043c8030400c2d800001c079038140300c0c10025040b650165600c05038a20028019281035002d42c42850460007101240d1032192504402400285802d50080407060001e0400820300114804020101410f00d0420440341ea20035065800b60b0b5030449005075505406007400000d510103900c000e0880701c0d04020081c2d401e825601052249034141d460300712214081c5404c075004c1402c40411404198134030220001019850203510703040c034960419291420300c250 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 721992446 1250 721991196 721991287
    0x1e05060a14070f0b180102070b0a0509011808070b0117060a1d1606120b011d0d020910030b070905061b070b04030503040311060c03040608070c0b01080a03030606080c 73
    0x80050700c01e81420000d104445d0a00b01100c407622551800843c1019100d5550081c0548040e10300c1c074005440e240401d101040a52014650524417200c0c1ca41158481c5407180694111010a545c00d4400f840002a103c019a05005141d104907018081c141d5501d10141c0003000485544084a03c0c2290503003484c400030003480350500d41c200da2880e0340ea407416000401c2220709a0140c0c803001d0414022482e5a41c105500000e0040084e2030400190982e901081c07400c0c40c04240698001000070600c01c0040c1460000c40950740034041c03a80c0d41d07690720035068444d9000c074410f1541240d010003011410b00d00e40e2000801e801803d0b0b060321101d0381c3d0388990b800360f600030703070010341700390b04009030400c00c2207582e00b0100418201034550070308003011220842d0300c900441c801c40050140040000f040103106140003110103902109050716541c50f14a05640c2e04012807089010924000003c80c80714001c41d0030500c41d68040790301e03505d01076400c0d40c1e02c140f00224000350307004968030440118540d171001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 721993696 1250 721992446 721992473
    0xf021509030c01020c0a03030e0d0506070809070509060105030f06120102030711100501120210090e010b04060221160609200a0e0103020a0e13021201061e05060a1407 73
    0x412410303458900040400d41010460a0490b066521010380642c40d40c90b00900c4404594060520f90109444070f0042813000c000054001d160340034000c100501c00ea0031110180c0201001000c841445031101c0c00d10106400c140c0f1030502042c0140001519510040004c0d90700c1000507141c2e24107081d03900200e60980e0015039204000c1035520036038802000e400c01040010034070200041c01254900700e07620b6180c5808400181c0191004150402601d00500c8041d0042c445044030355070541e541e00c0c0c0a242e90f0401e009004c018015625102060031070462a1030350020f501e00644e26260410718520003c8200000c01c4403410341f100c0504010801c000c8040301c0404015a445a00f0704030541003080e4240d003034215000402108005201584400151a0035240c0c544030b001c80ea601d55070b54290201c046601c000354442228018078400000c103411020842d0500960000400c40035418074020703003a41d0203100d401050601200241621840501101400d4155440d16012032a180d0707803503400b86d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 721994946 1250 721993696 721993729
    0x10b0a060306090f021608030717040b01061d1020190b01080703030e06070f1202010914010209060d0f09170a02070501050a0c060509030c0d02060f060a0b030a02070f02 74
    0x1030b120304110b801e070700380180100c2c00d1a9082c11464009100e80c1d060040f441c86001a04030072000c400681c0145c0140c081c0030030751140241504c8a86810314011002d40424000c1c8030000e940303d590114007624500103100e000703000800032803075400c401400701c44911032101c075011000310190503841000000d000e00303210060516040d139484145801e201040d14010303031100009521160f0200046030f480141c0c50b00c15001107428980d6102f01c0d0500d858141c15a010103803e0706030109041503160303015440500078520903803c0002c450740c1c642c2c00508034082c0841c25a001101040944090130156000d400030340d40a940003d901816030302d40114610302c3c450303a0512a038001450100d09901080114000c040c00d04e1301d1890055802c0006003e418030980003031480c2d4031400440e8400c0c0c014001d58a440c00094101e03080383e4400c0c030000b50b4400d02940c00354a0481402c000ca03469050140c2c0303e40a4031038521155103035840d5200903200035800094103680d03003140c481d8808010b980f003503180c81d00d0840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 721996196 1250 721994946 721994951
    0x415020a0801050f060405060a03150b03070509040501090e0d0c060f06150e0901050105070807030e12070611060f010314010e010c050306101e120f0204080d020709050c030c030702010b0a0603 84
    0x1000113112080c0c152410082c0302d60f0092000304078035a9081c08070740c0300c410b4130b1801089005c81c15495079022801e50f001100b40d00808820068015840307005040110341c01c803402e00499984860344812641108501d201ca44c00c000e0004102038020494083d0051040c4400602118800c00703035802c4075240c0e0032402c014619a260410501c1c0c0c41140c054004034100d07450710b090352500d00060001e201307072400202141000b05800003854090104056410742c050304110030700700740c00065902c90700a4011031001c10000d20548030950000034000d44034554140215080c8c0e400c503142d40102d00c4000700319117a40d40d01d030001c40940c00c800b030040d0030300c00d810382d00e82540381d003031201c10028160740e00501482041205c1000e00100328100081ca80045454200700060b5152081840003501d50041e007000542c2c000200040e50340340000780300c0380c0c02d240c680c29100c0003511035041e0401d0311070a40d1042080082403001c00c030014069001507410001c00d00001039440030a101152440406620010101e42e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 721997446 1250 721996196 721996199
    0xe0114010206072118170912030403120e36010816090b0d060501080a06050f130b06010e0414071209030519030e0a05060402100507020d02090415020a0801 68
    0x580410406801c049141061030342c000301950315404c44071040c0c00d0303044501d4075070220414180540d2045002c075500860808800c241001c0409481d0f800a100c007401000c41410480ca6244044262400c3d81d43c4451048060095410111201d41e9224603031684004071203c90380d08080c0c403400c0c07000380e4691184900c01c1e00d4034103d9401e041d03050584c894000e68104d15141040e1302c100f2032050081e02c032010800074080f00d80001281000700511402407180707251000100c3c88030000102c5140e098490708040c80507942d4005134244217039080e584512801305400d140340001e030725905c0c40daa2110040c9000452804600005030907030f05c0d071403110840350f00c43d80144442c3d541d00402d07030000d10045050500110a007681c00405034070031005c1c40320810b032460700b240c840706100390001c1050b900c3c03001c100d40e05c0b40389508009440d84000e45040344110800b101c158910380c0904196071003a900245109528804c98013440301c40100140701325500e500c01025030003450458400780c2102a2241c3d2034403501d6 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 721998696 1250 721997446 721997449
    0x15010311090709061211130305151f0e25030e07050312070602090a080d021605010804150e0a080a1106010f0e0612030f0f180d05250e0114 61
    0xc090680d0b0b0070080c9280e002c1c403189400075036186840c0f101001c000f90500c000c0b0350b502c540c0e001c1c1340d000b401c000410060000a20400195140b0003034000d41d0702c3c1100d52200142c000594802c0103010420803028641006800965020341d548405002e00500101c464180c162598805440c1c4003000b00f542c6052259401ca0308000c424041d0074150028030b0f00180f440d1900950340901c0200030101ca40010782002e5544406240400030007200c8102c440b100320300030000c0c0d01d84840744e442c10078940d0218000200c541c4109840c03030069422030b24049014000c417254030003400024040040521a618810000800c0f000040144840e02e0b5a424620084149017608105040e0722000c644411001c1c140311424240359901c0c0c0000c0f0496207000c0095840c0a09415801032480202d560741c1e0101e2074070304040c03141008011405c400083c084c0303141020410400154043c800240003944140180d85d100d0a14860f802e00910640b20259509561942d50401a030401d800c04d1700111194440080f8a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 721999946 1250 721998696 721998709
    0x3030406030e0c0a080606040b041103040302061b0f0406050304030c0b04080301060905060705100c2304050a0603142206021308010c0903030f0e040905060a05060a09090215030915010311 82
    0x4000840d0745054180c5445c04540d80c581002d07101500c142d5440b00002883d075030701c0c0d002031a03d20010b00303000e48910701420065114103040300e01032266204104040e840d51405021207144403a41c40e295401c00782070440844454000400071002e1242c074407904400f080c03d0880a80c0308034450100d00b6581e604201c0001c240c0000340d88214040d0805111803000910042655a4501000000060a28034585080300c0121410100d5800d8801c022428007403081d01c00020310a0f504191000454503517100011011269255154000d01c4400808038090a2600b12001503076100405a0111031029845181c1207130b2101003001d0040c1440704003046008c0003130041710103840c50f40c1054603a161441e1005890b07141c0720041c5404100c0c00300c20520040d540c40c0c1c40150131540020440748070749420400030004002c281e6180d440307018444800a40032030b80e07000e1340ca50310b903001c0c0c41001043e48844006403150009000360240340a56160841d501540c100c1d40c5000314002c4050b000302c2208038050004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 722001196 1250 721999946 721999963
    0x1b10090606080307080f250503030f060904151e0c02030705010617030403060e1e0a0b01170304060e03031e1809060f0108070207030c0f0608012102061803030406030e 73
    0x2d00d50001e2005401145922040e034030f0340054022919641c00000c0e51031031007000c5980d2045202a0104c13221802d000f4000080c51258192002d902115110301c0100424407400b19001800d6081031a00ba03104441980c021249007281c0c2d02c0310340e00c40c02403451040140c540c0c00594100580c0302040d5407003407007801d000384c2c00201010700964840c02d900c0d0103150f4032407081e80009495039071147c2d00d605aa48003085900411143c56489111040d0300c030031110307140e101c3c0741800e6824000280010035014540d201d10700b901d011100066243c140b60810643e12030380a20800c40e4540818498001c0d145400c5040100c823031200b03501e03140e6078658030000301095103508801074041c0d102d050800c0f0b00343c0c44004500070200e1090178840515903400008914103055600300030042c006100002901007036a5441c2d0302a90025140c0117023a03a2240c02800342d6000c21900403100716418440c24000d800c0541c000d100d2141c5540d07094000001c09408607145921550203180041d6482e081040007071001d06c400d10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 722002446 1250 722001196 722001209
    0x20d0c180e01051510050304030216090c020c10021b030a02031b0306070507053a0801170f300f0a03060b1305010806030c030604350706021b10090606 66
    0x68080c001000702d8045c01c4026000002e00c03c00102007014180200058258990b046000364407082d15504400d018210000914000d40306114001d8040d140140108039280555402442203840001410166221000420b901400b0f60003402d40583c40902c03582c07038049040d102d20760b500e80c030a00600d8a0210000c048408103c018044c0f1000a00c010450348070144d404e0f858108141c4854181c201c0d90040c41c000d04034500c1c8560040a41c06410140c060304840c5001401c4801c40342c1501c255449807030142c2d00c0700d09508814188950f0319039030401c1d07428051003040080e1103580121012020390384050340041040f0070203d40a80c089925014034000780109100d0103061000b214800d1031004041d000b050305000c1500c1c0051482d40301000002c0020700020b04a8896007400c0c10031448800c00c188402404404420482807410000c145540e401807040054a180c01e80c180ca07040f0094200c1c211202c1803052034168031901003000c00c15003405510124000490303040c1491304804031600e41c0d01c0078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 722003696 1250 722002446 722002471
    0x2120f0103030c030f140a030b1c02090a0203130b3103080a051504020a08010e0a0207171305040501080c0901060f051c0609060f030605060607020d020d0c180e0105 72
    0x52001960041040d200b403645824200e175003041c140001e648414001402c195140c40110381c01c406541e05803c42c800c08041030f9444180d90340700c0c03207540b40719020380103029401440550100311001401c1d03008590050115810010b800800d60320713071441c0300f019100300701c0c40d0000c07000a810000305840c640c1c1c9045510300e803d4818030308a0740c000c0d01c0d81c44003e001e640c500b0f540e100000c1074650a18403840d218480280115500e0200700800342980c4400e018104990700032100040d1460424400c076441c054000d6004058030300704107502c529650001c812030848407042e10000800741c03140c4c0222800b0703101c884060010060010240100c05805178007581c1000710385a110b42125402004840c4d41e40c1c00c4000c02d000100e92040200090902e41c0d216910441c42d0071400140540010461701c1500d108940a01075501d9180400c0f89500500318040d40c4640d18681020043c6400240301099034481c911600f20301c0d94504103810400302e504064030389a80c440c800b18134183d00038400c49a0001000916 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 722004946 1250 722003696 722003699
    0x80c07140d0201230c1f0e0303063a03030c0f080105060706061a090a081c0302090d0b0a020c0f01150e0408040f080a0c09020a080f13080d02120f01 65
    0x1d040c481d600000603042c000c1c902941c2c1d98400d1481305502010b60445001552040c442d0b000c00e540d11126540d0903801000038400722941d004901400001c1e1000304011400c0d5189e40f400c100c040303101c114400b0b1110781c55114141240b920003440b5003400c050f0440e802c420303003094140030341070314002c259600400c22641c1038921465000044281515010340b00907444014901d0050001c100540003a10301c042d0254501030780c202881c1c01006002c109407111861380ba9121070b034a564480c40080703190207020001c0440f400c1c6102e0b9000d0100b00308000c000c80710820060f185c0b050034000c00c0d42e680440e142c000400b0300450404206000800c004c58008002510369640207190f0b5148034040c0540610325400810184407501042e5006009003000242d00d46954000c4946c0e039583c0510202c1c0c0c0c2d40d915204c001018405c41c030a58103095500c0d05c4850080e035402500341ea510b24010880017801500c85200303400728819001074600340101d4400180d0340d52034514a2229a80b00814211020110400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 722006196 1250 722004946 722004949
    0x90b0f03060114040b0301050906390a140a0c020108090c01020601090510080d08091b030a020d050f100902030106090506060d0c0e15030f090d0c030c060b060304080c0714 75
    0x40701ca0468204000f009082c41803040060301038070000795195455070138502480112900420041d000302c050028440705207104000105043e2400340d000c030f500c444d10041d984010701103000140b0f04c5195030b01c0c102d402039441d148103000d5500312504450004210501050855030402c0f0f07019005040d00000b84001c036500c00000395540c0c0c0500030340028a88400210b000c0002c600e80700c202034400d4100351a408805143c000300310100454281d0750900ca104840031031502821a2100d52003070140c06821250700036024010294203001c0b00310fa480c818404100140354061048511480000101044402c0e15004140c29030b90307250407840c4043e260070140007048e03680a04940d40d050300400301045c5904459010340f00032441604d00d58006003a001600050010b07400250721801c45a251030031592a098022581d4140040f0101c0214200c80361040100740207030340820803582305000200749181c85001068650f04192000c0301c0341500072481740c0b06040c00784014130162000310720803000c6035080300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 722007446 1250 722006196 722006203
    0xe0d050405030c130b10080a140402010813050a0b0702030a0e03030c031e0702060a050904150b04091d0304080705030d0e061b1905030a11070b0703051b0115090b0f03 73
    0x4030543d1003025048800f44c40310f0150342000e1000a402041c3d03a0003001c02d424043d00c800c00840760b14600c00c0c50154001a803a000d0101d6030b00541d0181d41c0c91900366104004100900031018080c0c6103031161840c040e00003a4031401c03552040c03040f0307406592141256000607120344a0280308c14480d0700705100301500c1ca6400425500000344100944d84050014102850f09100d82d241c00b070341050000a07a4048203400000400c4140d0301654200300500b410180b403840145c480c014581840320402007040050350b0364112264101501c500042c021804004480c0707036034465442a0890f030801481008145014011942c0c10300e15400c02020040c02180050000d01c80d43d81d03100000004007002a001441c100112000c00681c0b50181c410791003541040381c0d50b50031100c1c49000040b210813140315a40300c0400e41a04950001312010b003010510703030703040e03406400c040c51402e500024003642d07180a070024041d2102c800e0710258640c6e403003802c0140d243c0903500704001941c011040320304418440d4a001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 722008696 1250 722007446 722007463
    0x1515031504021b0f0307020112021903021b0a0b07080c0a080103060c09030501050f01140d050c240d0e10020906120603100609021306021207030305070207030b0a0e0d05040503 77
    0x3110010707030f505043c0181c241600000448100184a010001c1418020000082c032031b150003600c41e00021404282c0311026031086000c10b600c0fa8a0b20b07231015060303a010f90003803d00b0720003883e1a043c100000a004a24003814000155080720440d4103001d82c454020000e1904506100c5099292420030344028162048c18800200714a0341d03444001520b0784203281581c041e540c460003c0c001401c1c848015014242d080c050940601514903580c2c03141c0c602000c1c080b41d07007a0711402070f0611100b070f0810064490304c2d40c0440108005182d10308112408014010105074491b442c0000c0e040d014a04521701d070060440c003003940745204001c1c181c0b20b81e9416081d20004d154024003500b05a4030840403908192440003081c0d0003500704200032404008580242030f07821040c00460704201da030740b42c1c12a583e0b6408030701981e44103810800500031901c42c0d0030041d8018198011180e010707030369944a440c0160125541c0748443c0c0d9a0743c0140300d5020502040040305150300d030150405003403000080d00e90526 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 722009946 1250 722008696 722008699
    0x20f0405061e0102010906180c09062d090903020d1b1a0a27021302030f1b09360f011e0503010912080109090c0303081e15150315 57
    0x3030b95078424681c03007508144216544500c0c144400b850310500e05924503204141124a0b44418002141d00b140600c00d002c00c488008594403040794420785004400407984440740310030003110002280c45005400f65000759840b80d0300510300d40710a00703402008410702065540403c1049904000400e013421028050300c0c201d4400c98203151600500b0100a140c00a01c0020800000b14044144060381000d08030007802070340e8603001460120003900c100c0c40216824190031500c13a000c80e824000700e105010304800c4d40c0340c5582c07800d16114001150000f6140c911b00c44c51034544d84003000350304186401c000e9905081c0000d49a810200b074011500c0d2014010032591080b80350040840103481c40c4200c00502c00507001b000142040d041040450450004140116004900004cad0b901744034801c40050030f401008641c0006c2c1555021102c41002614900e042c905051030740c0039243d040c0e42c50600841c00383c01e04003030340492001402202c080318541844401c20501c1000341414400daa2942031160 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 722011196 1250 722009946 722009989
    0x3201020a080a020c221409071505124308090a0c0e04210e04051504020319200d0903090305060f0108070b04150309150e030403020f040506 61
    0xa101000ca03e002c200c4d034a0598071070513103041c44a0b050301c0706185840502c44520203100c8003800d00080380030070748181d40040b050741c02401c08011040644441d66078240440c0303440d9150485120021414410684e1b1200400415030f10045010707002d2501d00e035108401541d0f40e6025580c5160078081c101d900080101445034040c0000c00380c800c144030208071381d43e110400800302925107507083c400c00c1040f60102ca0501556030301e9500303104c003003039000e82c40c0003103907a07041244d40321201340005881c020b0006030308803000200714405585c0701c3c00514403c1080d0142103800214990f01c080c00c0ea080240424903000d403000700d0b204800e040e038089581e0f06000490200b05020381c2c1c40e0450712640380e54005001400781005100000070502e080031304a405180441c0c054940303880b00f4010314031842c400c942031076034040d240d8030301c0c940641c05c00041107004a003100c400541025041c0107550504140b48965000007a043c021032503e85088404201c05644c10000da107003910204290310b85110071a5105c00c0c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 722012446 1250 722011196 722011207
    0x1e0f03051009230102030f07080609040f03030b040f0b03122a0a0602070c03060c18060e010e041a04150b03060607210e10031406010e193201020a08 65
    0x5002c3c55641410100c001c8410021002003000c50003034005071060001100300f078022903d078030b03c110007841c014400203181c144c05494698031060940b01c4c030301d411018551a903503d294650344600c85c900d00c8410700c00d0302040e10380600d800c05082c48044504205c100341c0c00d00c0300b4444101041c49018200c500d56404c609208900c0c00b440d85010980d6100604079400090458100711100000c501103922a0720203000700d0308500300c190b8040420120107582005226002c11803503110b181c035402114018146407405040e41c0c4046415a50110540d0b00b071041c40410400d1b00e42018480ca1500502404015060504040301400240702c05440284070360000302d00c0c80705002c40354040b048841601450000740e1507064001920b08001e0000551141d9464034104d0952400383c040c0540080c540381100c80716641314401034402161100c413098000b031440d00c9100c4450144c0c80400094008421005041c1e840194101c0d8140040e1815041030300081d6074005480e600020f43c40c54459001e407001d9140c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 722013696 1250 722012446 722012453
    0x10c05180102161d101203050901110d0801060e0609060a0c0816060b040b190306110405040207080408010b030d170703140f06031b0306150a030b011e0f03051009 71
    0x16202e81c0380c42000f100c0200050318040c1c0311040c00d503856000d1408074803951a500c1c20110300c0301038491a1030f406168a1000c001a00c11801400509014100228149152034119241820090f0340c000802c03082001401a80d0300307c0501280305c02c048030100d00c1c240800c40462460f0007181d10910920600146e16000c00c000c00b800d6841d040c4c0a0000d4080000542c180032010300451186c040c05149081d03074410060419250710201c1c045280807400070581b030344c0d980780014401080c00b0100707007030144008a5959218001040c1c0755000e10109900e450401e111070782106c071044841480703940991102034485410510302c80c044072180e4018000b990324a80c081d40034004440000244040e01c104200c0d00e0342009000c1d9005800035000c48001d4541d0f403180c5418008000c0880d0703403581c00500069124100509103081c4c828024000741e6440d0f42c0c903135a41000c4038007a0040041d40380c0c28002200f480300841c0c880c10082442016a151080c83e58403540e840b01e281c0e0710014000381d101c2c140102030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 722014946 1250 722013696 722013703
    0x12090708010e210c0d09030b0a06050105071b080102070c031a0103170c0c0a060302030f15030a0f02040b031917040e0105040b010309170a140304240e01110706050702010c05180102 79
    0x3018004019120314640c03020740240301006d940030464050400310702050302d60400e403140c00d0541e40c041e110540b6100c41500c414543c004841c4000d003501c004600c000c6020074007070000c0d1803078620482600070014210310f00001d1580b090a4000b0004c5c00950041000c150329092500000c0e104903178840e620200002a103040401d5090b5a60f086000844001009030b070590081d0700c80c90020747c0725001a00c6143c02c40403460700382e8500550541c400568800414a200c000c044402d20043c00000c00303a0070440807902302000000300c08030845030468408240300a040e0484410300c42c410545103001d0070019201c0208406000e0300f8001d0b541c406151a03e41d000381c2c0030081254004040b07112103080603159215540c0400c080720b0004101081d02c401d5110400b040e24021640130101d03980c2614034600c84206c40301200c1000d00c034140c580c5c0c0c06038240002881050070500005643c0f0b40e5810b038504041081c5c51002c0c0907035045a15082026070b80c2ea1f4001c2c140c0702c0c070203c00e5850303032250302c02880100c0c40d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 722016196 1250 722014946 722014957
    0x304030c020d080703081303022104051207030c0b09090a05150a0f050f060702090402090c040314010f05090303090705100504180203010821070602090406030812090708010e21 77
    0x1041039070b050200080c428088090304000d84207a482070800c0e61241c2c51141c0459260354003c0140c1c1c018041c01c0360364119108500415106101002d050a0b0b03039800040082a9404441c14660885036050080c002d01340e83d5040600b4020f00c01d9803600695202040e80c40320300908440f0050355610108810b0340601a180c0100c000040010301c00ca038854603000d485210900c45c041c0721326408540b4000601303041d800d0300c1d0302940003410315131140d0340d0f602400400103000304011031015040002000040d1400064050208481c00005440c004d40300700c0800c035080078200c070b002984144100010004005906016030b503064454101101181c90300759214005e54020341a0602129980c415070341c9c2c070358080d5048616100448207202c81c0f5a580c00c05200400c1035001000500300014404074102c0d4005206514000d0400030700c3c50781d01d0716020b415030011884098016802c406120403000c0030091b410241c61280003c22514002000c66a5070710101d80e0100c8409516071204148221550b00b5904c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 722017446 1250 722016196 722016199
    0x50703020405040207212d0507080f0306040605150a030902150a180515030f10180b040608010e030a080402040e190b01081f0f15120b010b120c0304030c02 68
    0x6484480c94540118900d143c540c6d1140551200c80750301076080d04c58060745244902d442d40f8922580e42950001d030800c614600c0031001d201003040604009219000203002c1100d03250b400e00e490303090400400055408585c0310500c82c0203428904603242c00c40070210345214a0038140000c1919a40c4085200e10320b1900042c5020f04021442d0000603821140f200203d4003818900c111541d102d0082000c010940402804c1000c2c0606c00a03607003034036400c1c00c01e400001071480320451560b141d01011150701c107002e858800d00d880b5440e003030709410540242006011032000030f0050b03e080e48031450781ea000c0e21005400b0000e03801c0c00b003130654540d5400602d0f00c410710029500000115028420004011034084614105d02400016030000c0422041e03154004d29103030001405010071100007505040c1c40e40d44940e5030720684407103220011513141000f0040c0000400c5000c00307074200000103100591240b20081c1003000100c03940140100820f81c4041a81c00d032945035141ca08003220000e0b0fa000f8001d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 722018696 1250 722017446 722017451
    0x140d060b1614030708071e0501110a0e0d17090a08010507020f0d091202010c23060105031912201902100f0e0402030a0e1b01020c091905070302040504 66
    0x550404901441c01c480d1402020b4420b400920009181d07560f201c3d05030054001c0d5800d101c1400000c510303103071200b40045440341c0302c100c10015031181e5084442141a1800e004ca0005d500c0781e00e0b40c0c0000418a03104004c50380e40d032512025840300e64005c9011740c0c000c9400a400100134030030356a40001c1305d000d440110000c00103841c21280181d59480b20100c514a54400d201c2c40300c440c1803045a410007a50400324800d0840d1400d0303401076649601c18107046505a007142ca54945150007120190140c0c142c00d8014000e95141c03409050400c040d21003106d206003644040000460888880d100640f40c0501e01800da845016100b0300c41c10300ca003070031200e0b240600141c2404081304080303c0c01040380200c1e080d400b800c06000c019030303054504240c8a008500396000c101c0b414600381c0c1c00f442c0c0c4a038002e440401e048415810304c6042c0700b040144c14135030500300d5101c0000355a04000018404100760703181c041500f40000000c1c0b01020031000300400681b2280095081e520a405550040202400c11b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 722019946 1250 722018696 722018707
    0x8130b0a111c0b09040c051e0d03200703030e09070e0901060c061401080a2301063215180409060506040e06070522051903050c040c140d060b 62
    0x5004000c4010031030180780c0c01c0494010107841c00303000e413a0103107074401d00580c4003500d04402d21244017800000710b420080c0d0325002c405661111407820709401e200c0e543e011000d0b10030032086900b807000c261180350160301980c0e05000280d00700184048a0f0030854240045a070341c481d00b01c0c0d01494000f07905410110720b43c0005403481d000011055558440d110030b1002c40c1542006250b1080d091050f00510b0b803201d0b01e0030010800b400d866607518902000540701c80c1103542052825030b00154402440100361020455840046901e14550303039086260302c0b01d860125000180080804000040400c800001d64003501c20207492455140706010700180050081410148000c1c070080b2801d5000d58148103010b0b024440101c0d2281c4500041d8036045d0818101c4c20301c852090713000220300035040d0036102010865a0740d80d0803203105403c001246103c62402c5140c00d6041c0b01140100034040d030f083c048207440c1c048d00075820f90114905a40229262034102c1f4081c405030045030700c07207980c10500044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 722021196 1250 722019946 722019967
    0x40e0402060702041517030a050307270b04030510020c0606090c0c01060f0603150f06052b2408060601030e100c02010e070f0e01030b091e0c1008130b0a11 68
    0x5043c0c5c1210302c01000c0710080480914101d440e403007044071500024900b00300007400b003070040c1e40e8110000c9503000d41800007048100c0c100f5a40d0310039085545101d0b004a01081001310400c610074200da000d00c400e5040400c0240940c1e642c2001406151042a04c100014076a00901055950540300c10000b44269603880c21b00c007509508034060100081e0410042c120303030f9a802c0342104102c074400d03590701c1c007a03030700d000c008507901d07041004520303c034100281d0b0380d101e800c048640003550f40242883c001601c04007a1441c40240c002c40c100c000302108203d00400c01c5034070204490758400402e0a010582680890f011400c251070045091203281c94a2810308000351705520204040010000310740711242c40c5c0d801c50300000352070311a61460100c40030040c0700090301042c180740c10803000000c80b404031011030700004c040d00500c0c03021740702c903403021144140504c2c1100c0550810072807030a0003452407e00c1224a84902d090344006804516a000403c540100d42d40c001c6601580102d042a251a01f80c40c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 722022446 1250 722021196 722021231
    0xc010603030c17120c0d0204090e0601062d081e281505130204031a04150507020a0f03020c030a080c060a15030f020109030b0a02030402010809030f040e040206070204 73
    0x4803d6070b8842071000c101e400f20a00c00120350850120101e00041c968855042c64280d6118034162a80c66030284030015030745000e0701030701c03d1008004014110642c1480030050104500780082c8407036086004c007039801000c50200501b00360302c0c1ca241002240e521031030324100c0c000104d8881c00300b11860500b081b5441c014440b9800d4082180200c82d18107060135100343d0140e490880c180304c80034402120811291800c029101010b030403d400c054205581d0b41c56015900b0019071035070701220b040c2400c10081002e900000d0211480c1c80340200310508200000954500702e1180041207411003000c90b206042c000c0080c105001401401c84024800526060a0503000304070b00c860b440c49500302154041d80b46000d8101d20255940c0e13144441445c40d00d400b82c10b0140707120f040e0b051102c03a25000c80031690b0760300e000d03203e440009070160342d034141440010310810b0000d1070010142c04c280962070b00c0f480144126422180c0b800380c18001c03030f01c403400065154854903100039030052609600700e4044c1e0320702 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 722023696 1250 722022446 722022467
    0x30206190309120c1403130620030316020d020604080a0e04060f140315151302130b071e0b06061e160515010620011503060f110c070311060c01060303 66
    0x300c02080140307a125031707a1644c80c0a02c00d1605280040d10105020281c41440d05a0341312016a4171001d851101409090540c3d1055901d08921604541444180d076010000c6410800e403e2004101e43d1810751910b268501036640741000300a03420109040e142c3d2a500300c10041d0082014111450365140e40d00f80144210300011030280c003030b42552401c812012507030300380704202d40490400c80310030120400800e115402c031501c900e95030901a903404a13000d80b05800c06402006180c559461142c00c10500f45000e107103659916643c0800c00340d002441c25000690054402c2d540f5076124030240709000405c0e014800b01500684d07010640d8241241a411303850045805001600d00080c40d039442d401d4046001d00038000070a0000407650383c40360350b808100c40c919421710000030301c0b0040744422003043c1c05107030701c142d6000e6283c5504220f004030701c1c410124100e9144504500c0c0c1030040a40c95211001440080c2007000b4031983c10701c00e511040102c5119008540082000d90344910b406043c02296 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 722024946 1250 722023696 722023703
    0xd140d02011d011a09060a0f0b0d06090203190f1107110906011d0609121f1506120c0504170d09050915041104051306080105090304030206190309120c 66
    0x1403109908078030040c81080b050713800e42c00c42c111040d408203007840a8450060001d903000f607000070001aa151020342001c01911210026640d65070040304c400040d0360f40b54014004e041c3c410018803490311401802d00060319940d0b40080743c00b0140142020083c44d10b40c9108005000001e0454100303c0c5026100300c80ac01c0032a1400c51544401c0011114004018401038103000c2032038032400540f0308203010b02006075008118400f41608000a90300700300070640542028142c425000418400e20b0050021034071024a60401745841c2c000001c05807011050b940c60301d1035840020044c0e052245007210041d098403c00381c1030082c980509a40d5480340d051400c00000d90a140c08680e03460044000b60080446084006002107038030200f200400e0043c0d40322101c4082040000354584450082100701003515500240f81f51500300400c0c00d503500100942d9080e04208030500043c0e56150035580d04000d0341c9146882c9491001003a801000c8465001d042c18000303408984d000e81d0711a035003000e03c1d0310 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 722026196 1250 722024946 722024981
    0x708060105040608010606020703030e030c1507030f08070c0308090304090c0c061505090609060d05010c020c0a05100212030a09170301140d17070302100f0c0915020c0d140d0201 78
    0x561344045400c031406809440c0050304500802c00100340306107800d0030070150080a4400c40743d1528009a1490244001212140b601050000506800c1814402c41805a0520750100d280002c4001c040d5008040003c052103401c01c0030a01c6d0030410804e8402a01184100f080380c400c800034060080c0c03100603000c840c01801c1c003031928080005542a00112400600300c07080680b40c0a04004203030100a000325003240b40d10201c40003140e4240103200501543e07401030040c1c0900d190504c1000140e50b0000d0f03005104103020005d841d0740c001043d4800b000102d00c0b894883d15001c2480028200c9000017034481501070140c000d660b14030000a6040321071070003c80c0300ba504076005015501d25400c0380035024801d03442d10010700340c0480d0020070449100f4415102006903803d091401c0310483d414282503199920f4a1610407508150340f01c002d042ca120800609004c4101d001795030b0034045440d14050b10003080d01c2c1082004544804030305402a8040d00c0e00c440202d14000d000740304180080c0c25844 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 722027446 1250 722026196 722026199
    0x3020d050a2609040f141510080912090a0f030b15010f020d0509010c0f060f2702011805030609010c180612020307050702090103080d051e040b0402060c07080601050406 74
    0x1d1102d1044060380003020b641040d9003001004014214800708a0f101c948600e00d42c090380c20f004802900c1009100b601c680d40000110921181c5021403800005200b199001c1c0400050001115088010f07812000340d594030420010598145a82d400301e40f00c800d4488002c4100202c003440b0504c2201d85002c03421110302c518004603100a494110040960003409007402e06034464001050505018101201082e9803a51400300c000f2003648181c0300d0551310702252110320b405004544010310380d109541d900b00d804206801541401002c02414054020141e80e40240850720380030003000001c05440b610b28108011030f020340b029400c1c0f2000108001c000c0040110101c0c01c00003030701d034035942d014895011070100328000c0d440608007000340311080c0b1400300160b4400d600d8601851141c403110307440306028200c540694001415104240e0f21a950044040031100403240c1d000303410055070300d1941c0303540c008100b0f640700b4040c810505004909001c6100940000c00f981200c40c180d400704200c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 722028696 1250 722027446 722027483
    0x423090a090201050a0c050c030304030501021b0c090c0304031709030c0106050907090e25090e0604020412021c06151a04080c010f02030f040e0117120417010603020d050a 75
    0x80c0d4420704000d001c10001c0c0041214288158010701c031080c0301c0c200700c035584144900000d156030015401141c00380c1d00001d11501410101500c40c2c4417141030380042940000d0300b0001400080d009044001c564000300004003072510595035150f041c23409040500c0141451000705440ea44403c0500e4403941c00c3c4a4002034500340256041d20400b22a6202e0604509202c1115583c5c1c9c0013500300c0505010040f50500700001d20720328440010b407280c446880c80c40ca4041e41003214400104118415481030008000705c40317240e0f08150035180d04448220f0501004481c48401200c0c00c14007030410783ca084007002c0c004a03200351130400e41d42d0003101c134a05032a80405422180c41a800340c081c0f550001546044554040c0d40004581c03010741c0162400d0840918041030b154000341e10910003150013070010803404488083c4044125155006400841440000c0100610441c4220f07454085440d41c2011a03020a60080c400b45600808640c41c1c2c200a044c46592488403010588a00e10381680040a0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 722029946 1250 722028696 722028701
    0x110405031b010516170a050705060106020609190302031608030108100b180c040e0a021b010903021b0607050a050726060601200303070908011b02030d0902060423090a 73
    0x21004140e42d00da2610b0b1049446400018075100c08440c20302d4000e4442d0174940d000006407104866031341d502511807a440c20264500076041e48803c0654200c0000d000b00c0b02804608030758010a4010300580854161404a286100d14001c8204820001d070f045c1042000c2c02d0000c6040302d03034080443d445500907031000c004490180035619408620103d110001c0a0b180b010158014041e24030b540c14140d6420a404100342e08680120016500184100400100049500990407040d00821034010b0039a0040e55503803840e480d000d1004000400c05039280d4030b40e0300f1200196800700c00d40d202072800b803034515664031280c01220418110700904148454031403070b04440001c80f8000501e10354035140015201c4c2034002c407a15074503907200c041c12880c0c190b0070001036000d903001da501c414810346000c88040c212210070007030b00381415a0925144841e6400130550700c140024810020704510345200241041c4201c3c0d001034080803040311468140d800c0300d030000c1c20241c02515240d40559910004004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 722031196 1250 722029946 722029993
    0xd2f0f12070306080c1503130602120907030218090318060f2b020c0d030c050f030106020c010e150427140406060f0f030f0201020f120904060b030603070605071511040503 75
    0x2114040c000500d28450280550b043c08e409203100514101c0024810212030b507044a0300521980041c50410450503c19a43c05090722180c0d0289440d00b4030360f5982e9100d204003070441e0240c41e05c020303405019544a0040b101200c1d01c41c0b00c05507a450108465455400c1c008189002c016410081404110618000c40e04941e00d044054550f0300c1c04160154010f14000310040c04104007403103010341260411000b0b5020385a96002403090700c22000005140c2d07440b94000c039006001c5a00c0900d448049101035034103407880041c851400000c2c0c8d44c800c50003980f103200c1034404030341085110540c101d80c20303e190340110f00528040c4100c0b0b072648000c5519040c648188000402c00103002c0011554695400c42454414410317141351a40b6060304d02c0c030784444840c03001c05410001406984516040c0305050080c40030760892421407074180300103915202a4807890040c4100080c0c01810000303401e111200d2004094020050348201ca040900550058010303107001e03101c2c60302c0800d0b4000c0b2125200c43d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 722032446 1250 722031196 722031229
    0x50604170715020316032102121e06120c031e070b090603150d061d19020315131205070c0b120a1109030a06020d2f0f12070306080c 58
    0x1817800111200900c1c400d032592000b07400b0007513800f804004005200800c0e144d02500030101603200c0440300801940c110001d031940e155603034800a403541d03000c0c80541c0703175900000c00c031007178590a0002c843c00e43c18006c112141980c503004440b140049400e0000d070b0b40400300c01800c1110030141c4c0310100200030380b20b8042c80c0e941c010420f200080103408181e0035041d04001c05010707420910015030341d0906980c44808280e40500d020f4450070135842c001c0006000d204601c44009111001c16000701c0e41b102e0401c08401204101c000004900c03095005022080d103900a011000090070b00400030b14542000c2c60454480c4001100065180c00180a0b140300701e00342030b191003064495800c0100140303504800d500400006111185c2207613800e004404801340180409660f46480e0f0703e0110440303e1a070509015001d034010203402d080300d1103100c0009a800001ca0036541e800d1901407540da8040c03c1c05c2941c1500003042002055540340c1c01c0003040714031001c12140300740460820000312940000404 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 722033696 1250 722032446 722032453
    0xc031b0f06070207140607050a060b01080a02070c030f030e1e011205160305040221101b05070609020420070506160e0f181f060f05090d02030705060417071502 70
    0x303111004601440841540d00242520307d030440590343c0a080c84551101a1940c035520a04400d15507000240c480d8001e601d000c0c21440c19660fa519620021003d001c0a010096480c181c042058010307282e070504d40b4002801d900c44060480c0b100e841e0410841741060014446212143c19140030b40102c46c00389251120040f41501040c100b02c1c010a4010300070780e480b0000d4800c0550801201803000715141d24040079281c913603c1d40300404c2c01c0d00d204404100c100d85941c1d4142016541c05019030390800e51020010856a0345800000e0140c900150307144402400144094060041c1c10000d0200302c0c82001900c40d036030b845800421a0070795221020010402c61254102a40b610300f0700e00901d84c000a20039402414000c020030b1621001300c444a80c1c19160202d07842d01858100c2000c0c0c001e0401d80340c211410515510010183d00034440554043c081003580102159410300c61003020b0305002d80740d113884039584c410074083c00399458180c2030b10740107006001c9510f040e0724003c982070150b1034009 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 722034946 1250 722033696 722033699
    0x40e100c1409100e0402040914090a24020403121e11280b07050403170c030403060504050c0904240b09010b0a090911070618110609060c031b0f06070207 67
    0x18400c07020954000f0204000400c100d4030f155585038400382001d0400c0340c90000c0d42d400ca07002d9842c44c811014060b0300803a40030100b124009204410303260005180c030580340781c25100c030340600c030044c1c011900000c041c0465400090b60b41b65008401541404040c00d15000e0810001c3d01504c1c55200d15a03400410b80004001002c600300d1104210380d05907440d070301c0348600462034071800410300c0255541800284001402c205200c900303584540300f291202c80061600d0443d0164030755a21962100819032501e8000190a000040c45441c46180300a84001134030702e4285802c002d032820085a40410345484201c40e551290365114000c68400b0240200f40c1c0e60342400c2d01d003c03003908061403400c104041d003480403602c0d074a01e019803001c00710002142520313500079207440001c0d5042c0d0784051403c03803402c590040106600d940d40c00c40c807241c10b40d5940d41e10403600010031024803514940071300034400082d9481a55071030101649005122106440101da00010801e4489406482d40e000590040b0300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 722036196 1250 722034946 722034949
    0x4110402031e01030605010503070614120c0706020c01150b04050604030f1e030806090711030702040c05040b070309030c050a1a030a0603210e030d120b040b040e100c1409 75
    0x2540c000000c00e94029404855009100c2c070110260000c032049034a8600400803420100701031340250541e4240240c40d044e80038041003039405114aa0000458403802241030405034004490b6001e0b08841c056603507101032907200d030103803601d01c002200303680c04c2c000002007004401c03080d64142e40d8000e10700c0303250618540f2000c0c2030360303034242003655400559405219503650054030f040c030301c5100b519510402d2a04804001002800a0041051040711180340b80c081d0404001c640700240d0451340010100e68803502103540f400781e9080b004500400041c800180368100c1c8076a0b040300d20a0303c01c1084c4580f01c00a00841010900c00d03030300d481c0300c2c4007410149150302c503001e5075000104a900040f200da482c3ca80014104001d001105c895440d52a407210302c561201c6c50a501c1c260640052074028070324800140440350200c1c83c51407160b42c40c009001155200e420206500d84000c00c24050b4603500d0b403800c0e840729a22030116020910380340a416001e40500405541096104241c5041450060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 722037446 1250 722036196 722036201
    0x220306111e130e060418030c11090f0705030702151005241e0906040b0a030b09040804090903091503020903100903050304112d010e06042409150e0109060305041104 72
    0x9201c4d50b403094854902182030a400e603107404807a402503843d8800d00c0c1c028240b01382c6244003200307900d0044161404100b00b50729003000150b040303c00c5103407650380d2b583d603010700724103140c0c0c060042265030581c50300744980031000383e03d560700342e60040b02c1c0503a01c500f5080c3c00c40020a526003c0e0401040305000c0c590603000788800221203001d8070003d0358078001151001030210b500603000720b446588045458020755615100b906100c020580303894486080545903070686000780d115030038605403a810840205482088150001d00040000c00c0d418102c0d4080034000c5d40103044103900078440c1c2400c04001c03a12034000c11501c241c15486803480c7d40c48070b44a0351a030b0351a81010326007000034050f89a26800e4039400603251217038240104411a100980010210354140100601c601804e201c18002c0310703100036007001c88180c0750000d4815225400c0e0190342072421688540300201c1540981c50196401080b20303a03002400340da51014003a107840094003240d0040d240548a0495280c1c1c0c0c11090801d503 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 722038696 1250 722037446 722037451
    0x5150f121203190f05041502070b0a0b030312090303041406010609090b040e03070c0503010e030c0c120106051003020c0c04020a020a0308060105300a02070503220306111e130e 77
    0x3c07121030001c4103072980308070305950286800e0003401d40e488080005104048000030600d12410782c056241040355100d0071048000900300b0f083c03942d40d904100c0c074165002c20446a1004140359241528584040c0c0b181d00c0c1c0c2c004503016250103450180034401040085840d41c16125141c0f1680741c05070500e019240240845a0065005941c0700c10030b9100f200e0410207440c0b840e11070280040d0081c00c0c40d003818256a039143c0c00704203e50040c800400e0a45021458a940300710a446050388088000c4c401c0d409040b1951000750810f00702c8011152441c0d150300200200f60f07117401140c0e81c10683c1014070003284201d21240340181c00c40c21003180006e12610107203030064014585142411015100d03d542c03400c41003400036816442c2c850304d0542e6000780c1c900030380c42401450114200304007510f0b459124454041602100d4640840ea8028602220308410103981c02c50010080b00000011001055024141c06011081840c1ea001079a480c1c0c1011140114405001c0149240c64104c5400c44031401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 722039946 1250 722038696 722038711
    0xc160311070902030109020705071a090111010f29090c0703110c130b0307080a170318031c0b0a0602100c0504050613030309240809010f05150f121203 66
    0x80300703000100040c641c00070303602901048000580d16400b925140380341c4899a4040c00c040400085d000c109400800c043e074562420a091080b100118032401c2401040e6150403440903500c1c080340690703411505410842c1201d0100712140b4200da000701086148402140d5060781484c04118601c0000e124003601d01c40110b561084601540c00c6100140303900003021038039039010350395540583e0b00b1b00d4200440c20003032601c0005060a04030342c0d110101403260990001c0c0c4000c9000011500b42c10b200c01351030502d0404001502d4903102d0000346501d41580514526681900b0125145124504880020206c90154006214045032083d40001809017113030074a092080500c030004080d11946c00414070500c007100708480c82c40c258503018141700425007028400704644090406c51184105502036080641e003001d1000f0344d6191131003070140142e60810340002d41000705201079403040021040007503204489104141040c8810300c21000361228100019a0210340c058110000110066800580 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 722041196 1250 722039946 722039953
    0x12070602210106050c011409070b0703020f03220b12161103030f071407030e0f040204050415030605180304090b01020a1a070e06121f050a030b0402090c160311 70
    0x341140c4040e01440709900c0580070401c0080c012142c03590078810701c548568a01185005801c012000380c1d07583d1228020030140c3c010005000d0b040c1030003000712001540103c0d003107070391710800a40c40d410200030800305143d0030805104007080c00d800c01c034140c80020f40006070040d902c1d9142222a55001c0c920140d0206100d41d80903100c00d010014801948213102e84910003501c0e081c41e1a0080c1034030000a03883c117203c2000e00c08640004c0d40000610341c0c00e802117800c2c0243c8616040001d00034490b65121279801854404a8400c07800030042c000210b9004070020891641e40031864614038144640e4005c0b690007c02052005200542c001680648103104032050b5050a90343d41014035442c070b01c01d41000103030a080000072a4010b4a8100701d14046d0b424600382220003014030071b141000b4041008844040342c000ea042ca940090510040c1401410b0311301403a5241050411190190360680c0110303021f400059031441d2090448501024032000145071003440c0d102200c0b13690700a441d4520500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 722042446 1250 722041196 722041237
    0x50310110f041212110a06090c090204090b0406060905060d09050f030a0903050d17040308072a0b0a09020a05061e130e07030501351603021212070602 66
    0x140c110003810103010001005002c1003020f0900207950102c520344c2c1420480a004035000360300303006c544000e01d90392058012441c03001c3c0e441d16140d011034a07048810301ea403000c2400214120707950400414003609442c204019900c5880423507041000e4003030150040401c10a01c25280016405104410300890566004c01e070781c0304c00d42c0d0030355201700c499100040140009005104042c0a4a0f1000300c281c10100340c00c017608901d00101c10002003024081c00314000000e803200c0d0041513140f0460008a00c800d110240d0501058071044031200180c6000d56400d0008901c11040d01c82c174201142c009010182c0d040c500b504000341c42d4071121a0341c0501d180110311448001c00306010300b122110007a036280030942040d50320f07840414028103400405080ca0010803031500c0c084160300408504400c3e2445c0c0f4001c0c61440c0440c1480104d8502140c807a040034000c501440c0d009100540744215240c503060812070031040d41d1740030080940b04411070200001000070f400d41d4000c000300100f01c40d0444003803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 722043696 1250 722042446 722042467
    0x3030318030f0403081309021903180b090129060d020a02030f0c150604050f070e010c0b01030c1a07050606091305100b03010b04150e1e011205011505031011 69
    0x1600f0591040352600000320b80314020301c1c0d05000305405042030100450034541009662100c0c28500740e0b8004c01c0c141d4031070605009254400508810341c0d000000c454a81c140110024020700c5a40300141d5545140b0110a0351611408805c1e03031106d0780107040c0b0707041609990304a4025400700b400340c0706600c400c1081507011440d440c0541088036100e001b40c050003d0010754403a070850000c00301c074412842d04c0d041241100100c000c140d0004103e26151000010100c016108004120310140010314568000801c0200d54118001520a0580c041c00034860b0203103514036600070908002d0490700803c00080c447e0600360001640034400d034414444103545912490704110540b15880030107600d581d20000d042c28240190101084c3c240c0e402c00c010089440104100300c8140644100780c00c0341000b0682494090300001490b0300050345101007542d64445180e42010407001c101e51039401d101c41e082c54410b5400010048071406000342850715001526503000380340611280c1d0381c0b41c10520100b0f002c03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 722044946 1250 722043696 722043727
    0x6051009090213120f0507060f05220b0f0405031c050406030f02041703030601080c0c0d120f2405030706050301050402070c030c0f061205130803190504030e040f0b0303031803 77
    0x400d1701a408810f02c1d00e0460502c3c2d0304108840d00b0000500030303480c0c03021801d994004102da4100d0344880c480481d640026104850248056000803e02cbc074000c605002c080265a00a20445000310102c07008400c3d11090b0f9914261511400000b060302400100a02806a000a149201950380051600b43c54117440088540301e01a1a0310582c03021003005500d58200c2000d80d0013030405034003942048004c00f40d0566038910341c04480100078500074054100c2c9510b402035043c40100c0d510070b211a8840d5a20912030380b44002c3c0380001501da900c00001c1505000c1404400e50741a560740c031340746a00301428031000e54020350040307d00c00d805060010214240c03070704180240074a030000e81e042c240703802c100900c00402182d02208a43c508018020028560b80c3c03d43c0210383c0c007031203c50704ca66034012850204907682500303a45103400c0078108010107038408005201003c003110100209030000344c868003160f055120152301f65100b0400b040a01514410a08500b0155000c8034031b450300c000b0102e01e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 722046196 1250 722044946 722044979
    0xc0b0a0b0303040f08010c030b22060905280b010c0f02180906150a120f0f0c0801020d230402370501140313030c11060a020c0406051009090213 63
    0xc083e00c14a402e1185c945d00b0f00881014031902d01d0107021080070b00300000e148403680c1005151050014240c0c40b0300000640004004040e451410481444d0a403a00c01550010200b210700c4041104082c210201661045854080040e0340d01c1e50300103482e82e100c1000034520402640c1c000c08100261007101d0f940c402e1503108081d801c01030700070b50401074610402c010005504500c20a2400c1c0c00303000c105035501650003440e802425100c0c4012141c01c10a0405510b500f01824403000d0080104c0d44880540041854804c80c10381006100314201c1040c060901c080c0148a0044031040442c02501d4440100c0500b0302d0884081f500030a0040400c1d80140300d0a8627000c10b140705c04a0030005d42d03821001c081d18646000c88924038620300501800c441154140c00101803000030403821050042e04480104c03081d1000d00b11030394881210f00060b40e00c0c1940c4500c00c0c8500e051a00c08941804c1c507486160a620080d00d400b0400b070300700385602010b90060615000900510400010b840c06009544030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 722047446 1250 722046196 722046209
    0x50102070f0e042f10020f21040515030402010207122102011805010e07061806050c0307060c081510020a0311030c0a2103050f010311041401061d09070c0b0a0b030304 73
    0x901d114420140580d03d115985c0070410364214444680b86d945000c42d03100300300240c2c003600c1030109102d4400c00b0040d005a82155421a0460768034041514114000350b016500076001c07200041c3d9910302c0c140c868076440d0802080d50404010204803580341140217807405140340008510180089070b040804100c034242075030030780e440d0724000c035180d1014868040640020f19256000304005840484a1500351141e5000c000d00041c064603201418825030b26807583c02107050198200d80d90004001c0d603400e60740a0360b449142d81c02a940c5140c48680800d15120a03000350044a1080d00c05841496850398145500d0004001100d01d080d030a02c0309010240c070070f182c51030090078500051082d102c036180c07850091502c0c14090100400740d480741941101d80c8041d075140000280c20208000d49811300e8080c89042076140003090300ca420072000c01642c1d51894a05002034460810045a160305544003000304000003600400309018946850340000c1340b03030b00824480c0c04440401e145920039480f01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 722048696 1250 722047446 722047523
    0x14030901151a030112080c030706060501120902091302130c0503040b090c010e0603040311010507020d0212190c1403161406100501031d1204050406050102070f0e04 72
    0x1814015040c1a81c0000b802482c20403854880b40c0c40b550352610311042c0030700307112140ea410480c0d040003014006c40c0c402528100591b42c039840d1070701e01000504003074040c49021032040000002c1e06c00c0c4901c50000c1003600109040842d490313070700303415800c8080c400060707030000c00601c0ca400340c1d5130b168080c0d10406046640e820342e40b45041d04104224031400340c013404841e004400580d50513a444039034812174844c1100c407903036607407035514054907500109002c1e48000c1d400c1000704070f020340d008074140450b00a07a400b603505825640150300c005101d0b41c0001803414005280f60b0810030300c03422130400040d20038100f8070328021500010038075507000030089140c600c8110400398100248200760101c0c0075042001400641000c03c4007515440c80d074011281091369440004010500307401d51100030103012005c0c1e4495400d024480c80c1241c1c000d0042c039006031305009002529510025140703084914015401c0f10b110308002e04005100d801600a94040e40c44181c900c1c002c1c039409207203150168030401c18 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 722049946 1250 722048696 722048711
    0x1090f03030b120312061809070812120109051b12070e0a050d173c03010515090303070c0b0c5104050d1103071707020114030901 57
    0x40c01d642ca840c0c203540c000c502c522980510f0b14000401c0c2d480d84200b101721004165500c0d008111145c0c809080103108030211400e0012100d4007140c91000d031601081a00c0460000c0801ca21030392042c0540d185065403504010810b65990751700c0b00da003081c401c8135418a10341030401c1244a94004403060040e21040005000d443c80d04031424407a049004d03550941010700c0c200008240091104018013a44074103007000c1c0f9000340e48011202d2200f81d40f0340d4040e4144646490b26202d03002e402c56011815003035602c04441d41540703000d41c1c0c106ca00c010300e01c11281e2003072119441243c00c0140e03842c0d0944010b100680c0001c5800c0c58003009001006ca445031074a03140d10b40c061604590040d0798207003042d0b0842d402441d52141d108045034450405081d015040c0c000100c052204601100240024500040c0010068049032003040b003071069036501c11070200080400d440380b01d03009c07000340164003c44c0190380c1d4881c0e407000380c416140141000300c0414a0102c070100198021a01c184107a5034036500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 722051196 1250 722049946 722049953
    0xd020f060c10150e07030911041a01030509071a220b0c1603030207050105090d051504021807020d0c080c0607050c0d1412180109060b1e031b040e01090f 67
    0x60300b0007403c0751115000990346440000480400090f091108043d150003844003440211840080201030203403080008880b007214103440700031355140960000b81010003092150f031000503404c0550701c5040c1d0385c00c42c0000090516000d6400403c6031081c08050120454a081800140800030300500f006155602240181907007024036a05403280d0407840765078107202099001688100307450080c00d140d5a15260035000401c40c00942c41d008246103c1d05030084030000603410003a005c0c51007030310708841481d1245401d522a080407500e420060707000c0c00c0c80001c1c95201c2c030383c0525602e020782c540f90700d00140b6202003410038030222291004030b100007842200780c68040101032500600c900c0c2090106586845428840c881d01c0300682c0320041000210f000c0100401200c3d0310b2500c241e00030840501c0c0340c03030800d0141c4100d00d8058458080f030a082007401d00c10030020b44520320002d019200b0090241c1c0c0e5180a030742c0d92200543c01c50380c2d411030030350803200921608001e1802111805580b11203880e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 722052446 1250 722051196 722051201
    0xa06090b01060c0b06011b050105041a010f15031104030506090a030207080c01020307020d0606120c050f0a0b0a0c051905160f0501120c0302120c031b03060a03020d020f060c10 77
    0x34440010440e0f0744000001141070542d00b141c00200910b014020024219104003072019501030152043d4070300030034002040400615800d030006900d00d03c0d440c5a980707507084e015050b1f07280300d001d2080030100040c1e14554480c0c0d10044030740a010000a08050b240c0d2501c0c0c0c80c0500480d000c0103982d02600200c024140c0400400c801000c4082c01012070446100000351680151300340240603521662405041001740c0c0c014101074005c5248020020384141080c02030441c491140e40e009000507c08a0b205003400880e82050720540165a07250812484003250441d03051700302502d1a0059260402801d10301d0b2024660b014081c030300802c40c1c01d000314004e10345004a680001d151a40650301003006903002041c2601300c880f900400608051125020340280c0705400d12050b00310042010808800100800745000e20032070100c91000c2c10f03268103240c1c9203110940d001030f40551240410001803030001900380350795101500c940c5a030310480740410501d8000a40c110401c0e00300313820309400e010715403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 722053696 1250 722052446 722052449
    0x70e090a0501080705062a060a0b010806150711030102041403010e0d1b1b0b04030302060604090b19021e07031403060a1505091002030a170915060d050a06090b01 71
    0xc4000c0209515003200d007566240c440c031990f07000c2d03e00411842080c0b400c104002d110901c103039505001e503101102143e52101e50031500094a41e142142140965101c2c00407180704d10000340034120440c204284002d915000044200e9031510200500410742d10280094401040040b441c00e42809419041509561238030641c1011640702c0213520700380f2944241c032004000504680e4803e101d6a82c20700c02c4030001100010580c0d51509c0c6000a05540b1440080040301e00035401c1e0740c0c00e5110641040190341900c030003e8180340c0d012012402c01c1000100c01806d001d000c610061601000d000c03200030000e811090350b0710785940420a001031541084000030f1030329020028501d1840d28000045080141b801014512120086100d201c1c90050003245c00b07802009140c400c02c6e06040c84000d6603644410303105000220390010950071404244600c03806030740d004020340f90927883c0c007507840d28606004040301ea20a0350140d010000c00c400340841980d141c05100301003001441c5080c88040e40406 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 722054946 1250 722053696 722053711
    0x40c0206010f21080c070911070b070f02070501050a050418140f040327032a050114070204050c12010305330a0b0a150203030603060711120a0306090203070e09 70
    0xc458203c54001034610b0300c45402d40c0c040e40c55030f110300a070190145007114940288030200c2c03600c5080b0714a091110003604620b84205070b202d0082d0748421046a40c40302241d00030025a00014081c4030a40c0548081d000359000361a201d410695503107554a485852000085229030b628582d4040b0f4a000320306a551102918810807040d05159a006201e507401107880e07061a4810020301d003108140700000402507400c24040d07401e036504030805009039480f9000b64004200e103260b000485501030a02d42c408a1040d0400c81c0c1002e046800303101c0a440d00608005e4419030810003401c0100d07009004902030350240c0010440348018070400c003141c20f0b010785540354488413061660f01501a100c4c42c00d07071000543c8408030340740e65600c010400818041d0070081b08122414010008568004044c41c03280c9001c0f070460340c164450b82c005131505200d4071134403522030700882d94bda1410b009000041440c1c229a140020301039940700b50f00703400c0f604141e4003200081c0186080109500d004050160007014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 722056196 1250 722054946 722054969
    0x190203012316081303030f02040504050f07021b10080a06080706050409050604050c070f0609080d0b0a1202010522030f0b0105040f05010f29030708040c06080103120c050309040c0206010f 82
    0x207004689080500c41c0540060425489101c41400070820790107480c0108ad01500901c49402d06084078244040119003040062086950810752041004d003180302c0c02c0e00250204441501c0c1e50021203a883d00100302c0994152581c0c1c00045c445410040070300200601d5071030030740300c905140307915090314009041d1a108a00782001c0c0304c1c180508000301c900441e03001d00b400700f48200034603142014181358400a810200302061418400d2042d41003030400d40000c0702c040d8101e1f515944080c2d000072500c400640014000d003c0110034005404240008203014040003204030741e280d980302002e1044d0703c0101d0b00d44030035400400c03160600d40038000701154141e1003440250306207160854085010311a10440d044081d24000440401c0d0301c1764141200450034040d81d80c9030a08029048400548044a092051050000b5110f20520b1450305036540b0513060101c4140d071000c100c50300c05c0904015a07580c0010801021144d60ba4407807898030304010b4025008641c580b45525a42103080e41c0010000030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 722057446 1250 722056196 722056201
    0x2b0318090e060703020912010f0b1c0b150307080a05010c03110c0c0613090f050603071e0621020a020d030c02010903050d0c030b06040b180109030519020301231608 72
    0x141c041205980040c0600d4010380303d400320300004000b448030004c20300320b039481c14440c2c0034a1032640d004070840d44025100744036040f819411402c081d1880d03d5018094541c55008181318000884c099649c0100050850381002c1d01d4400031810040140c4088440b81e64a800c050b1190f0f0309802080d01c544141c065507400d0003110382d5501c0e1648a00616030748900c20028214040c228013010300760150582c02010400ca14403881c0f01e0005140984403180720f440b1f500390004a5095030b0b103182020520b40c0d002400710340d1604000361003181c18600b0b0344000c001d480045c02900c1003c2d2001d0002500507900030221080c450f04c003c1c0880c3c98160a0000316410650b40b580400e4005c0f007120114007081c0800910051000821802030042c242650f42c00740f80000c00042001811020300a070440402c1060306840e0302c4d800540380710711948001480e0740c00070002203070800e00581c0209074260019001007074103140998a40a101a240341c1c0e9800c041244090144240180341c90100c010090305140e402030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 722058696 1250 722057446 722057471
    0x304120506220b0916121401020f19020106120f0b060111032205120607030f0b0d020405091509071404021e1608040e041b0605092b031809 61
    0x10b407054401404181440000c90681001001088100ca810454400c001e58540031a250100306842d02600d1025646400c1c2c10b8200061003212a404070030780e503103498800100c5100c44a0712a075010302e41036559480e00000c10010840b01e00c15064070038842c0410861403464a265414000b031b0405041000c908100c00e142070000040300c51040648004010a6903100461000c1c1c00868100030f0300706110049018206500151050003410706031800d00051040521400445805491280d48926071040c00400f41c01c00307500140c4c0290303072401680d188180030b040345841d060064442c41c84a6103d01d208004154030703400d544407401030031a000d40c6021210800081958805005940c100f00002441096640416100c810450340580c00c00d88036566440c046a141600b1142039652903034411100d980c075000f81c0100800d039041070b2035103402c00d42031700244501280c247c1e05594400c1c446c0304c13248850162032440c4140c054825668007080024040c100252880d036a40940e500b181041801a4803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 722059946 1250 722058696 722058751
    0xc240603120311091903150207050f1f090302010b1e010f020c3006090312090c0a0603020a030209060d0c0f020f060417070b0703060311191e080304120506 68
    0x14070070115149481101c2c402102c0005c2078056000070202002500a120490350540184c000c41d4010001e444421202e03c482580324031918848824000c82c640000a158865500800c2d800d8028800040c0d01102013002c59414040d0420ba400b01a01000060025690110203200000440c0c800f41c401050400041a140b80240011070903100f2071004150401106003490425448580100c038211709008001300d440c0d6000c3d1b4600805009281d0014a00540014403064800005440c1d4000c00c1c1c51b01c0e03811402034104000000406408001ca260107584250240c5004070a40700001003501201070081e142c4191004a101550803104043c0c480707190200b145548550000a00d10880c0f003101c0218207a44610b01380108a80f00d410180550a641039200c0b40c1540c0c41480c0c2c0800180c803071001c12040d00c1001407111224400c1c11010b00514111010140c92264000400350500e61512000390840e00a42c1182c543c02d0000108401404000c11102e6000102203c8042044110000e201030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 722061196 1250 722059946 722059957
    0xe06060121050c0c060a06090501050607050307061a04020705011b0309170a0c0b040f0b0c0310050409020a0e131b06050d0903090329090303010608070c240603120311 73
    0x382150390b400001c103c08081c0303007201c184980380c0040e04c100b440c0c0351740c2c0d80008017007900802040e6442c03c07001141c542000302c200e80c205904030009505184c0e03d541c0f420b014003145080b502c0100850a00c408450302c59001030b04207039101d0030003c143c000c41440813954a60f4031700f1503030040500302200c610205a042094410400100301500e540f8280c20300240c03078144c0c00010003014142004200720a10298004d40e0030700c544215504003103619601040c5109010945111640642c00b0104003c0c1e0310f01f41d4020410640301511600303840d6a10611b40c407001908450084239103400c0404a020055095085002804201c0c1c0160029052000003800d5018100c81c00c2c41c8039950701d507400c041c54050107112000791790203802c0384801415006404c104405035a000101080b00d070700030450b405804025a03040e980c01d541c60305200d54a10130105d443e2106a0340c25079116104206090320961a01a0110141d140900224005c0c0c0781d4075000320b103c21450711b420300301850000c503010502c0c0c1d124100da1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 722062446 1250 722061196 722061257
    0x6090509090c130603050c031c030c140304032312040b0711010921090e040b1003140604020f0108040b011703160501050601030c180e19020d0e060601 66
    0x195603107005900349002c0c0c050314142c0d4849980807440d040c5050f55040301c015a031141050f100140c1218060507510403014110340c10320901500d92000c4a8880c4d07202e03a090b102c0030700d0b0221001c04002a8840d0f954003d41d01600050034030480000c0111401003e910f075901d2410919203407055180a4810703015024000a06000203a00414502403048074142001c1c00c41c48003c10802c0d1803440c09451403031586451910300001500b0350000b180c0294030a00032581c18810102240d41d640c0d032180203400c002020050049050000800440d0b0300124607955090000300601079030030540100146050b040c0340742c41c100071b0741c4000c001c00240070b00120f83c1120340c201c90400600d40030203050b50a40c0200c407622038230314480380494410301205402040c000c40013030701d0401134006a00d100722100c0c881d01140b400036503113440382086010010003c060348020075101d480c03128000300c092101a0381c0511a00c461b1103480d0310b04840c1c0303220240f10031038000d4002d00f8000c214020100070002241a0040c244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 722063696 1250 722062446 722062459
    0x1060809060a050c250b0a020403410a05060105060415030905011116020a122001171e0108071a0c0f06010e010e07021b040b0d020a1206050f01060905 66
    0x44c130b0402d000c006840d2064003106024006101710300c0c9901100c0701a0380280c40340d00940001c1a08903200c1c1c42200d069907000a070803040e034801341c00b0b0207240700607542510309500b1058000d014182c0e0001c2d100d1501d04c104074003800c1c001c440c40c100f039480d240e01a000b141c46898100020440c2087c1107092030801ca4241c240411842c1c09800c2031030040c007e881b08200000c0000031000600140c05a981c0102c51013268401402c507260b00e600c081010030082d0091404a16040e040349030000e082030340c00e039408140340001d60102113003444040c04000341e074030622500704c220760005600c25000045000d818400000d00b002440d140440f030302c01000e081d500c0f824090000e02024014818891030703d10031920021143d441d42e441c000c52189030800d01c070740c3c1c0302c0401110125103681d04c00b042c01c0346548100051001c1e0b040c0140c0811004100e4111540c0d07002942d0b10340040161180c6000b140200140001140380c8035250400b4419a10300800d03c010006c032080046c840b1540200c4410203540007a6241c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 722064946 1250 722063696 722063701
    0x908010b0f040e0f010e0c03100c080105060f0c030f0d050f071409061e04051c030531030b06040e0105010308070615090e1c0309020f0405100b13090501060809060a05 73
    0x1450510755100c12100c04c550a0a03803060110710300040100500d4000e4049030100c516000c8543c0454a070003c000c40080c0310340c001000b107841e00074080c05201c3e8284204524043c1e81a1540d03155a02c00c1d4100039010720049100713600b82d4440d06c9540c0e406000d59003002d000b0300d014000107004c4d061441e03541003140c41c045480d800c507440d09010313074004d843c14600c4c204960306181400d41c00c0b90400d2041510076805000c1c8112100104a101014190f240e10b0307990502a0f000b0807003090340c8030744101c0000c192000045004144040912400a40c0511044062030130900e0601040d40e2900b8001e11003603060200400000760310a0840b24007a410080004846c4000072040704800d07890b60007105200c1c20003000d0080c10001180c200e41da0205042e07144842c1e1b21501040e010b407061042c2c0654000100118200c190034070340c003c02c0e4003614600107860000c3d00c8c0c030000034054101900740807040030b50f10010b000d90038040c410700f40903041e142040c20326460280f1103a0f85e9020000c08201402c0d4440c0007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 722066196 1250 722064946 722064971
    0xe07030c0e090c0d020c1b15360402070605151804080705010905120a17012306090a090203060a0b03041e0507030210050705010c030b010c06020c030d02030103080a0908010b0f04 78
    0x40d0341039807801c84c099600040b00e17903036400e4250307204483e00c031311a5001e078144900e41d0f681402126007022002c96492007148503481070850049c3c42400b806114000d41070500c02e15a214801440c6a52007030000142c2070a240103100100a092400c00740104a15140c4035002031011120b0390303001d40d200500581e22900c524203203024005903600180f09101d461680010300040401404040d940d90340c07070540d4403c4016802108010a100302e4861101c86850700700100510700c00e031010004050100d07442c19070f8040102c1c60b04c0030184c0c84030041940c040180402880e01c480c1c000000d01e8920082410b50425844107201008100040700031b9801954030002044030a001d20001036800400403100065030040c0603100fa4051072080f41c840d40303083e50129440707000c4e21030603981a9069407501d410808030307516030b002036020580d10b08547c4003e10130010b0318800350000314040d40c0f183c0e0300c80c2d4803070720410005003a4100a4024849030b034100310b0711300c0840d00e40313041c9800407100c11030f004500f4600d80d85 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 722067446 1250 722066196 722066201
    0xf06050f0d170f03040605060604031a1b0d0c200607050d0605100305090c040e0c0d0302010209100207170a151109100f020f06190506030f070e07030c0e090c0d 70
    0x3042eaa1205400700b9034880740f20b1100c0c0a5403045005020a01855945804010301882103001c010058412280104070740320b82a110b0350f41c449060305103803104580100000c00a504001405110a17442c0d81141ca000da901050380d00d002070750100c01c80d900d900800c211944442e001441da008100000c00c1240401080b0381048d001080b020f0005441b00402000050280500315220420707403080944514107800c06e07104480010741d01602600903d1200030420886400281046e01159024044480681c2c0e80d51214840c1213010340007410040e1800400da02c1c200607080015407075810140c4c5410216801f032040e006001402400010440c900c000c2c0c18189010384c0c003250760083d240c2c44400b455540c100c51101c0080d66a41c00300d580b40341c82003c2503940c848084402c1404017507107003950550311300b49400c503039080384000b400c1d5000c1900303800d40d0910703150840d4015055181f0b00740a201441c0d030144103641e03052015103060f1800005250115030b484401401d41c1c010007c1c00502c101c200d200c5503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 722068696 1250 722067446 722067473
    0x12090d06050c040302120307030c06020904060e0f010e090f0c0f01030204080109030305040c0504021c050612030d051e06060a1d150d140712091502040312030f06050f0d 74
    0xc1810801d90614400c03500194125020403401400fa48802d200e405000200781c03850785525a4a2681c25006940c880c4040d401c070341406900a915120041901040180610301c10302090303524101540c035006002d646400302034102e1000350000e816801c002c038000320300900d007a0800c0e00c000c14180705c880e00413070092090b17034040145546000f206004059260300118007a81c0941c01011a5540300c0301003104a200e500003540b8402009070b0100c2c0b082c49142c11031988268002c280b5940c003e0588a207c0c20b6600003103003a041c484d51075013088a031405403094111180703540e03000c03d80103280180108065100d0710603088140700b20400358500c9900842c0d0904c200700c1c00600700b80016110f68403585615040700140c501c039030b8181169550140e4070030180314840c0d0420b654490f001c0364091880002400c44641c1034038680c401c000025040c07110b5000610080d481102c0d002009405c5040060407105070001205c42d050901d1020480c03981c55040c181e0300741504881c1c05018000520380300303107102c1c0b0a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 722069946 1250 722068696 722068703
    0xd170c090d140c010215150f0402040f030f03030c0c020d021329011106150616230c190b090105090301090309050a090509060a0c020c0910080d02010e12090d 69
    0x1e0b000d246601d0207011918420703a4500780c080300c040d04041c5c61a02c28000741143c0d604801ca8015014440340e11b003010284040c80800b500051406840b00010b500704200d41d00150b0312107540e40011800c00d42d061103042400d401074a85414103503819400229141c61a40300030780326401807048904031080a0740b1140b0b501090600e6070a8003103112052080d000e1041039203034089040f0300780c0c01001c40c07000314500388101480403540c0c5825000c542040703910303000310510007000700034004038a002501000540c4003100703202944d0001c484031401103604e0600450f202600403002081c42c1c982c0c070100c4824507025280009006038440d0748540040352a8091685850743c1907003802000000d05400542c2d500a45e24261a4400c02c40e80343c0a002c0242c41c0281c1e480c0107107512034000070b049071803154001050204c451040d00c0f100340302c103c0051b00b912015a503440581c1ca0070601004207090811030503070120b480b800240f00308284c0c0c2c42420745411420b0010a8402c8000034440301a5a4100402d80129030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 722071196 1250 722069946 722069963
    0x1401030609030e3006150607030c0b150f04091a06190e041106130306020d09020909010c1b0201120b0105120f01080c010908100b0a050604090e0d170c090d 68
    0x140303002c01307606100d0540030421074014882056007100408640c0c0f40c03240189044150132048014140022580144415010803050101c00d10002e289007418074040c5000d0320034001040c0c034410401c0900e4909161241c400c81c6007800c01c030000b0301840346000c0d007a05854101d030300316234800000c101990884020700da0b45a1441c02c002c07074815100c0302054055400703220b00d01c007403200f044180502071042204c1842000300d2340204000107800b5400400105242d08004141d403115640420626001602c100000365190b51990201641c8a846001e030301414428031520180e10750000707042140c2607514802103a880d010840502d90203402141c1d00c02904501b141000e1411255104800d4001e00592800380210102d69010b90310995516080e240e10001512031001284030507001882d140c525950813400f01000004d850b0380d40c20240008085804010400b04402d2450908000340c41c004c5400b8081490001340315503041c56065980103000c0c1c00050750b981c45c40d00000c0e4402d41940c030010982032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 722072446 1250 722071196 722071219
    0x705060f060604091d010c0906080a020d0f06060c050c1c06050c040b0f0304030905010905130209030a052505090405150a09080343260108060414011401030609030e 72
    0x85c60002510724421a4100802103410031140c11600c41209204640008205202242ca07000466000b0801d511028000040d400b1a450205003900d0b925803207503000c03034100001070f030910505018044c004007049500390340c01c20220092508217a240e03000a400301f5134600c00180d080d040102150003600c05045840c0d04c031040100100b103954800c4408a0020740c510b1000180d650043d40814140c6100500c01c9149400304c84100c0002c1d00300c04441507040c03064940c0180071801c1409401d0298100110000410421041c2c0901d00c042541c0601e00580e141404c0001140d4080303a04140780c2500050304119894050803038000d44842880035000250000c00e0002c40000c012200d080882d075840300340700d14240f03a818080c1d90000d22350054001003400c50003950140c4224600e1f00300e0350391039402c0501c070142804510500c5109800c020201e0b440705003804203100e4545620a01c2414910090110303508207546400d07440c4c01880024801911021890105402103444103144038010b040440903c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 722073696 1250 722072446 722072471
    0x803010311100504051804020409140610060c050a061806020d0b0f030d12150923090a050c010f1403100303031a0a260d0c05120705060f06060409 64
    0x302007500420b1042c0d407007200c0d102d0360500401c191001c44030000c004c914040100b202c0603007a181d004000300d0303119035509802d40020b100304035640c610b295900e00510103881c24003406095a003882d00b0010510410705000c0c400070324009807200700b10b071388203101155202c6842140c8051040d0004005e2110b800401d201d40b41841942c0407080700c003c111901100c10701c2e890305041d140c12044003080c00042000500c00c0d07101416030851074000b944111000c40b4250b07101550011140700c4c1c80d0000c400001e0380100154240c40001d181e4000d18003c0c05040c0003a143d0355095583c95500000b0390501c0011491709682c140908401d110704041c1c8003010303640c3c1c41c1995400d64000550702084000c83c0c0781c160b40c11100c004d5500c10664400703000c1d1006031400e0416040040901c40320003544110310002d01503000760442408441c0866280b42c441802c070502a203071090601042d03108510303c03420184411004504002542034102000d10b806007041e031034850100d2020710898000c1606a401e080001070b1300e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 722074946 1250 722073696 722073713
    0x1e062404060e0114160209061c0503130509190507020705040c02060703050f01140409020607050304080d2304272408060c091002010902190510030605090a0f0908030103 74
    0xc01400340c1e034402081c44122802d0300c142c011800a0b6007034074017021003a001800c0c109919504014001c117040441c2c51200304c1c08254010700e0004031440c0d000801d40385c015240042504010f0241298560080e181400c03440b04551540d02960040c00c0d110303000302d41c40c0c44c020b0100401601002e0018406050070a0000c0c0d928581a00c04030001f910b4100014140c150503c880350503584100c41180f01c1e14280e400b0003010389148001aa0702c080204800d200080003000140028403104000c1e1640015140d805080c803100002d8840a031602039100301654060308048405550000403000d00841c84455508400d010070001502498603041300038048890f0080c640000c0e4805100b80c0c60085d84400800781c9541b0140ca50303061413181440700c02c3e031a1030244c10102c06529248000030b40340300d0b5900040e8010700c114008068800131500c09002504248400e00080819810705020b1580b41c180403448503040240090030300c3e07070340e04641100400c0704d410046000760880006a165616400e28540 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 722076196 1250 722074946 722074967
    0x1110a17281d0a0309060e061606060602120304030f0305041a1f0501090b041a071a0103110f0a17010e060108060115180b030c0912010f051e06240406 66
    0x800c106014041c4402d88002401003011903241d03541c601214a070810a03660b0f80d5030210041d030711400074030640f1004058120707245c414500a640c0071445a00c0c048010703003046405824081a942c0410030030008c81d0308030242d103800380c1c032614000a250b0f8650074a8802180c082c44100340041c80d04090040f500040800c13280c80c01031100700c961006503244010b403200d045900c5012174111080c04204200c2c0c0f000d444915402c494455080d2500301e6070780da0140c0624000d507001f4002d0020600600600c1910b0140030521902650001c04004030710300020442c10303c0e4880d00e00d1900c4091480c0034400020f400800300e401039541100e04c02d5848826254848009001c0e601d00018000c07081000c445c8100100c007141320b12280003201d40d41c1092201825640300501d40c8503041801c20030004140c440b808024030300c0c01d41c20000104912000241010b541c2c02604003003011926141c5541e842040740301241e0040000c60751203503a944000e0012001c4030a04080410b002400700e40001da02750081007100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 722077446 1250 722076196 722076221
    0x13051e1003140705090d12020f07120b07050c101a10020a020312030f010b07020102010216030c170c07050613091103091212040206070512041701110a1728 68
    0x6480f941d46603000c6856002d03504841c1d900c418030109a0300071907100400e01540b4102441074500410301a000c0c01c2c40c1c907080da4020044508101d6514003030000006d2034640101251070703c2c43c900180c80182540c0c641c05074400c0002640d50f0000410102090341d0400000c80f40901025007145401c08040d41701c000c0d0b50010390190081d240b100d28001a44000ca91003004917902c980145d90906030303040640d40141d1030490640d94200010b546800404034459600d52081d614400e041c061840c082421030345860000116950521402c5001703000032a041050351000d544c0251600d68010502c4404007255012001070380c86c201d030992a107508680114030030f6040a08882061404142c0d00c1c1e050b101c0d001c051108004048003060051030840014200c4500640c01c0b900d00741c4004059101c194071640c81995040d902c0160550102e1080c003d03139203031a0802501500304844d24401600800e6035441d00700b6085035150008124803101c2d00c40442070441d01c1d01c0119066529415040103004800c10310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 722078696 1250 722077446 722077481
    0x30c14010903152304022808010911100306061d0f040603120f020f0705011b051608280201080915040602030601030506091302040e01020c1c031113051e1003 69
    0x448403072241350400f405544d0280060840b583c07011156038107034001c0036004c10003002243c2c0006016609001c1c00031041d01030391512001000400800014100001a5609250400000700265a0048902020220140460707558443d66000145000d0303030f85560103500514011700030090100c040d47e603040c10740640d1600ca0360380c41425000c4e41d03274101181d26030095134806041401a07511801c9018101c407203248140922085c2583d42d1402d000d10009140020002d17208100104641000210800c0300401024980d080e2803c130314484034041000003034184216080801c0c0908002c2103062100e540d0003145c40c9003070800d8980301d406940180e82d800d00290030f03c070100e1b41d90301e4640f6071103001d05044d42c401064511a80d0a000140c1901489140d665509101e04426690103111b4461920945854165401d005c048083c044840880c1c0b01c9900c0030050000840000c004082c403803d4950845844845100444141040154107108035030484001c000d91030055170950041c0b1020341412105 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 722079946 1250 722078696 722078741
    0x706150f03080405010c0609080a0c0326010e0402010203070f0b07030506120309091f0f0305120405090a0e0102130b030907171f1401030b1b04030c1401090315 70
    0x2a040d568445001c05066503400700010000756004880d8161414420000800e03800a40e481c0c0c40b1140d049103900c4004191412802020140c0c42900c2c00320480203c0205480c0014140710010030070750500a41c440e0100742800b050541e802041619401c81d80512540d04400c1e0a00d00b030082080180c1d0850042410900840c1043c64400c200101c03190301c840003141807040400801201c1400076005514419200c1e40e03500c803103501c6001150240c0b0040c0103800c03d043c03545ca0718600c0c0c001f4240c2c4111906000303110a0010741d540081321600312505442c04540d0711020070704240240b00d01c0324003014440c139990b400940f00c1d0b004400fa51182c1080e20640b54680d545195842c8200905882052990010390f250611002584418041000c2000d00002c04103202007114295a0003030308280c440d8190401041112103070740342c0d014105c00400500504040ca10746d41c100740009980622007035800d00c6e800124069110303001e903c1c0103541251801c2c240c4001d05214200034801c0383da00c0020200324052 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 722081196 1250 722079946 722079959
    0x40b031e070314040b1005030102031503120c0616020f03041202030f0d0f0c06090c0e06031b01020607030507030b090a0e07050a03081803030408100b010905270a0908070615 76
    0x41c2c2032142402d6070f43c441c8980c0c0715a910006524010811100024440c0021070691400d201840c0f0405540e9030b65943c1103004010145486c001c51800792840004201d01404a400440d0154004000d4240c84000b1244140d044e400c00320304940070b684521000c2800915502d481c603a44078143d0013642030b01c038104a00c0c5100c0e525031429089050100354000e006918182c4034859010b01203025000000d1785060a60791003030411040c0e0300c1103030401c0b205402d000789454140428041c1401502c0501c203010710460011391142402030009050550724000a05c0460081d00004c904c181d00801c84151850318100c0c51005054410b09400f1521886c0c1d0301003900d0810f0360b0000192504103070344504210340801e25a90140286c03202c150180814040004d1a082c2000802070341c803003d00c00130548030240c1e000106600820341c0058461a054003207244c14610800c40c0d42c1c064484140340003c035595000e03610003e004a00740003030180130002501401c5c4000d0754058010904409188104a40e4070b11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 722082446 1250 722081196 722081201
    0xf010e010501211a09030d060920041d1801180309081203040f1712060f100534050a0b0f07140c010f02040b09040c050a09030f0206040b031e0703 64
    0x100018141303031100c0c1001c410101500313442d69210341d1480032203140c43c905c0c0106000352403035a40003001c203640b556480569212206515000515040010b0f410329280403200088841880c1e41e0071001000381000c0f0784c0961031081081c1c0001480002481100e24000b81c00c20380614803a000e80004050810200d031180b404140e8032482c41d1503603403039419a140d986560301c0041c0d07440d408403603c80c140d16043c41c21154070350107040e2070803c101503078402c0c0c81c00d80103010b241c1c18a14045445106c0e05001ca08010350084241ca115114840100e8202004031070b02c0185142c020f5401031860001e0000ca801b0048005580c0d0034083c03180e6007042e0f647d1540300700c030391b1210b00585500f004513107503c801303182d02d0300c4c0e1001404180425000102e03c10f0100d00e5203200301e900c20707004030605000000308000641002d0103440110b00192514603d00100c12030010308815807804024800241074443c00195901c810554000c1c00080c404c0f1036684c28104440540000501c002d400e02c4524800000d903402d000340b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 722083696 1250 722082446 722082509
    0x30e01050310180212090a0303061e18061809031b0b01051509190608060109030b060d0503190201091e0503120a09050a0c140405090309090601020f010e010501 70
    0x84070b000940c241001d01048000c403041d5010040d0b400e00c112604d13450703030301403250281c008000070706140c1e18030341002010313140113401c4a80019008407400c5028015030944200315146036100b070300303200040c00e20348018194650002d8041c450300000502c40c504103034444141035100317841d078440c40304110700c0c1c1440e081e0b80c5010103415004c092004012034241404502c13070948d41078460516104120740007480302001c51840205c00307600010184503180d001052941c0194003402c04504207461070303403031880507100140528001c0c00742c1d00598042200c02c2050b540d683c400c10b4080c20030b40390640030007402420b04d10816200f06c02c03810b03000e0200c0c04128400c1810030340c000028500e0442c1110352040d810340c004d412010030075a40c40058003c1241030160710886840381c003200401514004414550156203e056403080e494170050202c04a000400c030307001107800355a103040359660180180e041a291040480240d400c0c42400e0840c504103512140c182e82c07106078844405102801e07404000700c0301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 722084946 1250 722083696 722083711
    0xd0e060918183c1203072c15071709041103090d0818160602010509030a2019050c0102060f07120b0f06130e0a090f0f0219030f030e010503 61
    0x84010b880b8425032044600301e282440035030303c220895030209105140013a440e400301c450842c04420321058076404070051141c0705119450300c441d0580d40103000554134284800901c14100ba070440740c0d1400761704098501d00342d00401c5d00c104100070300f0b898000583c01120f440e40303d00d00c2c000d00e42010185070419640924080801483c0000e441d1205071003218000d0100b51440c0189580746d07110420403c00c6081851440103401840e61914038083c1c00c0d0b0b44090400344464005008200f00076901012050303546400c10300108488181a09442c207205013203840114000b0801600c000f80140060420100c010a07822100e40c0e03692401a00c0c103d00d02603401c000021031090040c03d0051a9412a01011000520402000c880c100000762540d004406107800030203c004204202d01500035103d85c0000c50705000c0c055515583c1d00c2391824410440010100002400e0800a5440c0c0e929a03001942c040c03104028003984904040340306140309a012000101c41c422a00303042d51003102687c0c0034012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 722086196 1250 722084946 722084983
    0x318030f06070305040f02090a0f0b0405060d2006072105030c031302131802030f030721030906113006040207050c04020316080115020d0e06091818 65
    0xd42d000201c01405000e40709482100b0200d48440250740d80110150046000010026907404000000c50030340d00d0741070b81c4030b2003140f0b0401008002d80782c10b411498411f51215443e1180219158145c08281210a0203504071802141310010002880c02d400c0d4000c41103044c3c01c110b0080890221041d200441e02c54050315010300c0805c0c3c40210084c0ca4101d07051000748006000821401d0400031030341e241da09011100043c42650041d801d0a010f81115070345400080c6142c00c50741d07210240d546100160700c03481c1c8043c44032008000d600ca68026003e16620003828030014208202e00d24007070300b1900481e900064044c0b5002c1c9250041d1340900c00c0d00042c468520225501c00d41080300a40008800340c9150041890031f0740c050340e17548011881007103400b075054603615920340300404002c8160012070014004400710400710790009210441241a450132103004000400402c07a60300500091035040b8286407101c9103251001e0166500c1000c21a00c1942c4591501d03480344e51b03801000390318005d0102c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 722087446 1250 722086196 722086201
    0x32606010f030c030b030a030306090c020303090a030c02150f0417010b010f030c050d110a08060907020c0913020d150f02090a0302090a15060809010f0204051f140c0318030f06 77
    0x9002e9000340c1a6a08103040000340700d031609011904246802400b02e00107590b07104180808030a910656030030b41c040d403005600754509440045d640c1e40c40c03588040c2c03e1100e0403007005c007155280c101e07028407000c40d4081c2907241c580720155819181c100d8001c042e0b81145030304a80310f404005200b41c4d41d030594165140003002107203010560091042d00075140c108042041551040b18150103940c0a5070f20440341e10f9540c0030780c0080207100d010b000d000988500314480034041c0c0550300054911b000b200496112031551113907a1141c000d803106100007904034484141903010b20919000c030100d070304503e0320b05001900c0740c0400c0ca03049103ea200c074541c1c801d00c2d4000c00c0c8058106000444e6002d080b1005c009060030304281c0c0009400d02c00c0d4800b030f001503520400c00100490030f000340303500014ac43d8410760a05080030300107507010703245461041e0044800807409221910444001250342e400303c2d07240396542c00c0c91a150783c8030352165000d8900100344482010045c20005070744840c0034840c10251a2a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 722088696 1250 722087446 722087477
    0xe0603060405150d150606090f140a090e2b0f1b1e030306061b140c060d0b0a080706090b0f0f0d0c0e0904020a06030c02010f050403260601 61
    0x900b07014240302d060b01510711041043d912000c0f082036521703010307081d15400c0702032824015041d01e455030030040800180f042c0030040e40c008040b01c00c00341c07281c40070003440f181321400228141c2c2100381d01100381d080c2090b0a28036240c0d00403400e42c41c098049201200310b081141011445031061864690001e84480c151840c01d130b12130308030341119011070340607201d00000340e1311100300004440c0ba407401d0580b0507122113001c142d00751180700003c00341801c1010114070184100c0440a4051401909000c03047e950110f40c00c0301401410640d1400402641e100c0788043c801400400942e14998007c00718114040340105000985404881c007559444074850b09010810540d50454001017000f40380c04c0c4028600150741c00040c042e0300c0702e002d40c00540c0c020650740062905c85072400780c40c000ca04e09801d00c4090303114000d82c102030382c1d02401c0c040384c4400342c1d840480c01042003002840b4440d00d8001448101684468000941803d040c0151402c080328041c1c130407143c60a480c080d01003031400c4c1d0095140d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 722089946 1250 722088696 722088701
    0x3070b0306040f06080a06062d0b030402040f050c03091209031b060705030c0c2d01180302030118020306220b0c07080a02011509140612070b04030302030306030c010e06030604 77
    0x41c400c3c0c03600085040d1382d9803d03106103850a411000c41705652524000d2041034a00204500e0400d1075480d8060000500741c08200b0507811406401c244800000009003592610b4002906510321f00404004500d01320065a0307060f08161000c207140d004110201050103030010548041a8000b0003030001e43d650078002c0c180c805800750b803103504040c040c00240003150090028045a003400c8025141da040001c00308015814003075080742070b0080310b103070b18007034141065081002c03c40c0a003031a0b89030000b600b254107420380040d44002d50540c01c08040d16034510750895915120380c420f9040301c1407919982a12200ea0b0740c81510700100e443e02c00800d80c041000c46461a0304000010350044c60b0060310b488034001d55201713025035030141c0e440c0c0e41088207050420032104000c10315031070308005800d1410045c4900d0714001c0c28681c8902851082001e81d1801880400d006088245815540300d40d01c1ca0080e480303400c01c6031010300c40d02070718180301c08950140301c0c01500410001c016926564500e07081000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 722091196 1250 722089946 722089961
    0x60a030c03061a03180715111504050a03112107020a05180c0304030c080703031d06100504050a060504020705210406090501080405070510020a05061f030818090c09040b03070b030604 80
    0x10f0a00c03906c840055030304807401316112002001d035108150b42c1e805d04441854525010b1007580d902100c8030421000c2400494a040c00720380c035280030412841c0640e94103150503104118100c03040c08045c81c1c6540491020010300358507200b601c9551409a44008004041c00d038211503204d1501c15800007440d0b83c62000085500900c40e0800e6600c1000d1502c8040103900700b07941c00c070b0209588ea0007003403081c00040c500d051a420000700400e000d1074294005940c0150038400c41c3d02694584c008120160f038950062070241034060070440d00c410007414040c0d507030181d042400650b4111100c4074002845418211000d07501c081d1210701440e880c0030011a11140014001e031201d0041ea80702140c1039440114681250130300782c0c002c0a0126441c18164146480034000c52820101180029400d060b03d412040803a500f00d2506600e485214010700e1004280c25681640510950304100c24210f502c070141c004a8400c0d035081221520700404d1660303445d01c50062605d05441440010243d14198100e502d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 722092446 1250 722091196 722091241
    0x70f05150a14030c03012108160320010203190c2307021f020c03010603050a030c08220312030e072d0308090907140f03070509060a030c03061a03 64
    0x79815020b48440c0b111900f00365a40f40c01144000010800c1c03201012111903071035030f2810380d1480c41030b069807640d015118151800c4595904144413000b858050314940c2108001b020b404a004110102c40078000c6d4030840c1c0e104030b4a8407020a159410a00b441408900807082d1100d980d07419000300b880818107140a15420b900000b0007442c0e0041e00e034901082d00060050908117059072100b00e000e4184901608054040e03072400c0380410114030300180714607006425042c40320742c0546a007451101c0748202e400401d05050b081032048411004085214126402400c08a010050524049055800c40c3c3c00f00015903102e160280040ea0200a003200c0c103280070380d1040f48140281002c8144d262450303100b034415200110390103403203003449116198403c04500d85100c00041c04541000513024003040030b40382800200004080600500845004610003815161102985a001030151a031203282c4400281070041c00030f0f1714880c80083c0d00040b0040d10b011070455a5548400821090039a0102d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 722093696 1250 722092446 722092457
    0x60507030503250210050705070f140a051501150f08070e0307051e040b060c1902011b150e03180f030c04140a0c021b040209040b0901060302040602070f05150a 70
    0x10f0a10f101c00c00407654141ca45500604040103042500b00c0c00c89000401041c20710508006040001391020400c441c0c0131b0b0700c001c01d4082c020b699a2441e10300207503404010110321451660644801640300d5403412150388203401e50342e204080c881140c02d41c0c64035201c6004980318038049004140694401206481d010341210300503a91350300002c2014179060020781050180e031060b4441410140a4004294000c2d94500d00d889a044051a0f0b5011800c21540543c654440d042086a12922100c0801d1740d0088002e850050039060803c1f410848200c50036240b40f9101031084080400300594019111101c00c1038009410b40d0248009035406100c41a4580144c01084115540307600c905d60041c1c440311f00c124080e241c60710711041141c200404580a540c0001c1c4030082141100d214144880000c0d1009a02c80204c5804030300903000000c43c0340c1e0f01c502100004220642d0650140c07044607119400c40c2c1056548100494003020240117143d0041c0c02180d034001170000850040a481c1d801e46400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 722094946 1250 722093696 722093731
    0x1103040b070c120918020a0e010804031101050106050408061003120e1906020d020f060f01180f0501081612120c05030c0f0a0312051504151d06010216060507030503 72
    0x10340c200c240405100f4030101c0e074481c0c0240800340c08800004107050800804602c0c154010101420102007e0a205d04100066000a0416200d00c04840b0790000150080c003480d41c55140181254019000c7c40310f1901c61040000c0761b20924600c07607802c403500107038001c400e000036020445852281c40381082c0c000d0307a80b524600c1802d0702500020000d00e03180e401740c24078840070381e4007c0c100082c03001c840001e68003c070f05000c0b2043c0542c071031504440c08546d1b001041010342d001c0700c000d8103c1c8140c100195180800024a0800105400c020843c1d51040c80c0e6003140c0311a24a4480b4440c00e00c0901501d08400707405101601903214003617258010001caa0030702c981c80a510b450030751102c910f01b805c0e0700500c0c808020103400001c07441c041e4907503d009102516001201c003204503c545000c5110301d032a03030400000b0b40c140a801001514200d0000180c0b050300da2004613284d4401d59016006110b85003085203800a44d5000c8800e64140d959018500240c2e034508a8480d08003500070880000010b00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 722096196 1250 722094946 722094953
    0x24051309140a02100f091809021009030c12051902060909090c040c0807051801050c24180d11011404140705190306110d02210a1103040b070c 62
    0x4002240c0d1800d0740c001d220a01c580d00c144415194100c8441e400d000101400040700b64018880700207480030f0101c40502c03100c00303c4c09000a0301d540c00c0041c0d08025402103454900b5444445007007500c1c041c4401d410a280c1d1a02c0307a0041c2ca280d00b0300540030340c0000c007144c941e021100d03019040b8a80000c2c94641404150f0000400c0a5001d60300680190b11510301c00401342814010100c81e00904c1c240b03803240c0d18210601900c1c2d0302c103204c20708410307910801d056405a03018000f5215408419030448c1c0a40100f00c10741c201a008500982d0b05800448001440d02c4d09051180031002440c00060700d00038805550540300a140d568500410755212001c121307920350311000720303481540a07405214442d4160a00c40741070090b9500420302640d20aa00208090070010420040ba43c0c000c0c00041c00c00039a010a4059005d1054103406035400000c079000081c0b1032001c100c0c541985111080300544450702d207102120903524010403035110030b200040104010031401640030803a4101034000c6c004076034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 722097446 1250 722096196 722096213
    0xe0d0c170d0c08181b06031b03130c0b0408211c090b090703030203091002120304050c1003020307120f0e010504140f030c15100f0306050a24051309 65
    0x905101c0050b44850030020040104c52141d04440300c900701400160505404030100420100010703070040300000082440b05140880c2030b00480720b010401c0d616401c01c0c009101da02c03145140182c0303140345264000304e000d021041c04c541c00c50b0785401c002c020028403100c040c0414000400355602907001032054440351100c1c08580047d20700e50400010343c500d61440c252903085401b84c10703641c441d84000400e00000b40c0000482d00c02c218200c0701483c09100324041246429050280343da503c1070080140001c0140010720390040c0e24080391440d0003549014412404c83c0001c581000001c3d00c841c1d00c03501d048855900140481d150003202040c1c41240044c40c600792802a9012160b480700c80c000c0c81c26422051103106085a905000356241484107040550b0340c0c5803000c0002102c24108004c40c40d507440c540c00c42c1c0b000344660804010f46a40d42e080031001444100c0c1c84040150905540b210114911840c1e80d2600385192071079502903007403005002c450348462607004920365840b054100440d242c034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 722098696 1250 722097446 722097461
    0x20708070e070f091a0912030306010210050c07140d020d080705071112060709090c0c0f06051e0702060106020c3c0418110414070c0503041205100e0d0c170d 69
    0x51078a19070320040c031b01c00e100703000c0904244401640c01c14014030280340e074003140d00418080888008186900c0e5810849554801e0080c020204440034802204000000c0b40041c42c8080c0f41c2c0980d02140410b40d01540c0c411407c8400d40002042040b041e00080d60b4000019031189010f080082c05811007008103103040e00c16280f50012406c4d80d28208603615250142e40f85600700791030714200403040c69aa00400002c1900020043d60f181c400007801c0300c0050500116501040c03a90800d54204540d0194450000303004020050007009a03000c1c3e54102a0381c1105405801741b4050919202c482d0003041035070002d5140d03030b80070f5036061041d4269070383e90040120a521000e02034003075022a1904115680094078807602490801b40e400c01c0d001c1c907507403c041c0e104045091a10802c0d065107003030f50071882180c00640e034003840c00d5420824840000340c010f84803015030504101c6041554485681c4407503400040000a10f42070001000071541c1c1c0300504c480c0070540800d4244ec03c010221820f41c2d510 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 722099946 1250 722098696 722098739
    0xc03120f0506031e070b0d0e0a150e0615010f02010b04060609050a05040c0c1b0e100501080f04050601153501060c08070b041104090b07020708070e070f09 68
    0x65a09100540c64103010900040010040681d64442e9034030006486034586d114000e075040000c2000400180c05030480c04034190060141d5145601d60701d05075000740700c5080280502c42c070742000d202250b070300090501c3c005c1a000f00181a150300704001181c40420421a01c81103540768110000c541d2218000e40c00602015240c90400c0d0b41801c05002031f45090b030b4011849141020b9950081540003203d003040590010a4240c96001101ca045041c241d42d5000c1038003400700c4030400c80c0f100b200c2030805054990980c0c0d4a03c0545074103100e4000c0321030076140604284c01074401044400b840381c604c0a4050b0365130515942c407803d01d81a50003e09403881c1985031814842158121411840c4e140c0342c050160360806005604c1c4139150140340e406115401400d485001d80450203000068a400c8100380380100207101040f1540390000380d11005071031890141c0304064000c03454050120300b620680342960b6000d1901d9640c2082101d884000040307074800d0000a10011450b060503603c0b004401c0c44 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 722101196 1250 722099946 722099951
    0x2010921021906020d081b0f0403050a03120509030306130e120708070c050607030509040b3f2b110708060121020f100509040c0210050a060f060c03120f 67
    0x1501c83e001c0e00f00401c0b45109010403a10070200035030402003100f050030130080c0817680354640c0d40e0141c00400c24400da030405000c9101d02e0304440201640084030b1a502c0e01da01c142401180c92b00400307a075890009541899100c00d00d9011481b0301d46807a401002ca2080e0030048071210807032464481102d80c019501a145a0000140030b4244814503248030000c21094805528155060b00d00038014051464030b00e00c01c0d91102640060f95680c100050700c0340701e403458241200c5284202072070740d40b07d41d02810044661038844810301c0b910013294440711982008480324030451284603589603041e0f480000403d10007510030850141d0b20421004e400b40c036040000700b8155040030385a1216403001d4283d07080804a038036880006886000892402c944240c54500c030214202500703503664091030380d120b50042c1c40e145620f05040c2d40050750000c0b91001220800082e02da20310035a054400f039016000c588210104200001481a8141c00d0300034001d1a000c01c00d140308840d43d5040e900303a5400c103145541c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 722102446 1250 722101196 722101199
    0x10219090323032506150308030f04030509100c03080708070c0803060d08160c1415030702010608010c1706090c090d03030e0105070c02010216180b030a020604030c1d04020109210219 80
    0x41b4440e04001055034041c3e510020b03e15525a1894840200030501011120010604050142003070f40c409005c01450a00c80d100d50110050403658009001e030009141e0300049884c071800744004a01411160791240521080b0782c60f203007070320b510180c10745810483c45c110f502c0101c1c40d00400340032080c00702484440c24400a050600720740ba0030742c1140b040100c040c0046030b4151741d5007100c005c0a40514003400d4032581c0e412000d90042c10140d0014000f0b5003007000d04403407180d1202c14612440740304403824400e6160326050060805084039601000481040082c010740741418001d001d492081c03401240001c400021a4251103050b140c40c0c0204030742d088242c1c00c568040c0510344094210500101c0280e14101c0a0002141d2114103041e030b0507500d50480846440601041c071206401400050b5170315920b1034040e07035444051141000301c0c5801c10074500c000d1600c0039018007507a016910400e01c54103166191420740e45143c2040c02c000c501580d00380c0140c84038800c507035030199440d91002125 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 722103696 1250 722102446 722102453
    0x301020a05040e0a020a0c120c02280602070b07020603130c080309040b0906030c010f020c031e07120f06020a03140a0b0405070306081b210102190903230325 69
    0x191400342c1034403044c0c1d005001700c00100d0751044165000e190040312860081c1f0104070251680381d26100083d42081c481500c8a851b000c04000800b0000c0e4031002c4c591321310341d580ba401c80c0c40c2c0100d07001e04402204100002005403410704040d54000e16102401000c00080342d440d031801e0325255200d00f03032542000c5841c0c82c0500e014416a403e01600360b884490301d15084c40083d48901080b1241410721a0704501c20300d5642c420455080203400c081c0c02c071000102a0455900c10b030440c0078181d032441c802d440000c501d20410911091205a025484007202409587e40c0c001a41000c00b0714810140c1cad5450b1a021006c0c41001607010314091240015051484c070b040c4411b41342c00410300c00503d8181802000701280000b06030000c10400c16150f001880200001805a640c003251022035400d02d04481c491000194010209140404128800c0090381c640540700d14508d440701034141090030440e40154031a101c1001c030b03165500b01c240c80c5030050340c104072800f09031001d85800d040c00c071120b40d03503042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 722104946 1250 722103696 722103719
    0x80f01060504020306131104090c02030301050a0510020318010c02540408071a07020c010c0b0c0d0e0d0c021e0907140409091118150118050301020a0504 67
    0x1400d0300307690a520714581100419031000c0041d40700207180f5540d4003a107d000503038400b03072006894101000d002e4034480a400a5481d0006c1c01400c0c82902008000919890300640ca1081820030360040d41c1824070f484034031130351801141519810b1000c12000d80b030060395042c1c106ca40f4510645000300d403440d03400c070904031406405103164a00d2080502c45a2a8205040b418440c42502d0040201d269a803440d011106001d0510000c2c401c64214041c85080460402c52078800c1503507034205d4403030140340c400440c0c8100c80c514026060150f0740c808584c00c50711520007032040d06007400b004210320021510451512111810003000102031009110451030f021444c029001260100d10003840e01200c0012480c140140201e0184489120700b0b045000f02c8009403030003040d02c4401000b200005041080707032100350b40070313030741c032424484040c42c14000c612015240949050241c141860034103400644048040144a00c8000380001002450307907801d0000740300c840003a6640c00d80b02c92409030203118 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 722106196 1250 722104946 722104949
    0x120103050c0a051e0102070b0705010b031212012c04080405010212091c0f08030106021c02030c0a0816060f06090b0a080c130e0a030f1e090b1b07080f0106 68
    0xc82d42040300b04101c2951940c40020302003c0010003480e00442060060f89005041c0e417041c1c2d805400810101c0900c803040d400000710010941c02d03200407404d00b40d542405c0788a580441d10180c0c80c218010701045060030154030038a034141081c03100030900c0b03c4e6080500c0340100c80403a50329034001414401c03540e040c09482c0c1070703e00c0b6113007103810320460000040602c51081c012826207025180150240807545650036481a0400c030300c030f41c1e00d5171504030013512800300c60718689041030010300104a043c400011140048004800307032400b1200755070350003000d502c00c03001082c01014101003040403451521a80c000f280000000040301880d20b0326020035a040b0442280c494110190200140000450360f00c0f40c034081151010f00c854041c440c184010541009130b0040d9102c2c0740466410036030401191594a007041c0c07100352001d42070062090a14000b0101040080c00410b030070000706120001404c42c1603000c000c01d6988a24001c9540e217050f1155101e94a658040c40601d00c0e00d007400e200300d00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 722107446 1250 722106196 722106199
    0x7050a0c0f0335120f0c07020f010e0102010e0304080f072702030402060f07060b1503090705010c050c0904030801150e060f0c0f24090106150f0e06120103050c 70
    0x81d0901c0c43d2240e02410202c1e41c0c03600150140c001e000c2d0400039080ba582004480030500164850000b00030441c0300d01411a82c2c04616911704000c14800040c080071342c4c040320790041a44442400400c01100c04880b10000541599294041c082d5191000d10190025103210401048031145500c007291400c5030340c4e8803207141d801c06007001034281c2810302c452716002150800e026988ea00c0c3d910201c1c3c26440380743c0c80c42100303200200d5210300304990380d004850820000c07204594001c503102882c02c81c40c4001e03150344820360b210880c100b000354000c0d06008045801003094071050541c0002040c12a1030403a401c4001441001c01849410004845016030041c0e6160080c060b0301c10101046240c4540062038000080206031440803c3c01003103802030a030180001d4603030500380078008904c141e0b010042e6603480c810b03a034001402d101d01486040d04030344030392805003080c00800c0c01c151140b0070301e07140702c004101d100b0002c900652a04402403400700b5a038880340c6025859810f145003040120380406 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 722108696 1250 722107446 722107469
    0xb13050c0d0b0d0f031b020301231501050406140708070804030b071701140d060e06180610170a060504080306010806011b170c0f010213270b12010207050a0c 69
    0x388081354550049000c1a681802c200f01840242903045116913000c040080d4191308200240000c402072604c42d0740a00030910820403240c807074180543c4010048140c003800104280403c002c807601c900818000c0c142150202440c00d04030b9100c18240340e0004400390765420000400704100230742d40240351b40c06000c502e0091004c460300303041748091030700c10311850142d14800024103d1075510141c4003048194000800c02805103148052900d03001e040b02d01c003981c0c0700c46001c114619100450307840c0c071179011700031040c0700c8074100344407100e0121117155549900e220380c110020000340d040c40740f1401103000b00b51090f22490312800040c000100102441c0c100300c40d418071300080344401448228416403260b4a0098905071058540f540c0c020741802200911400c0b0154040c40d60650050000780001241c181d04140c40d10300c0007030004440031802d004507038000d01140c20041c00f030b849210800f000400c0e038020780c0881d44079142a604148404d90b00e9800c0340d03040504204c01030b080d51008200c030a0f07e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 722109946 1250 722108696 722108719
    0xe0a110909101e02030901060f0b0f190507080a271d09010f0c12060f0f0317070210080a05061014031f030b010801060503031303060b13050c0d0b 64
    0x481d110b4900151509420380c46411034062140e800010f8400202c002c0720843d101d142c140b4105000e004148100c00d54035041d000c1c00704802ca003840031030300380421440c1194607100b940952407045201100c0900100101400940300081040004248140c4295a408900da803d100e0302c000400c04842d010a5056440d0001c0010f0269444120f1001d56060b01c80015540e88c0030313a440c090030b240302030050b01501c0e118081c1507158105424803442c06d00300a04001c25134841f1140101c154081c05210300240d45503404000280c5220041074032280031000c1c084c100003c0c0c0c4e0110b484006402c682d000400c0003c002c100401c1442d20402d40c1c04002120301c0205484c0c660f401a01e091480045804200000030016070410020381c040b240c01c060021105481655030304040d000d00d1400c0c0030740803035542490000281303450000700b41e560072112031500410b0039285550f03030b41c01071003041e846e650428480420302c4c4e00e424040c130031a44255081500c171562510060090300c101d458a0321072600c14217000c01c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 722111196 1250 722109946 722109961
    0x40807080a151815020c010b090411190e01260d0f0507021503091c0206282a1202250804030503031f0b0901080c09010309060e0a1109 59
    0x404075459aa40080022074880c1011080080c8060b850f0162140c601c0032071049410703009a0041c82c02c4080341c03000700300d024a080100100c49409450140c8003409000c050740c22890119414052074643c8140009a99038a00c1c00007440030090b805200c00902c800d00000c00580e0307070301c4a601901440c0d00580341101e50703004042c01d040e000c0c07000741040001c041008000c544440035034007032401000c000c10f5160310f025441d06581342c02c22800134400c02c85415242051600025541340500003c880c0003c0064480018a032020885007810200035111801c00241c070b908a01202440302c9200c5c030200f00860030010107000b19900740b102c0507407035204021407214580408644d659888007600400702c0d800582c28100c03c51300803038002030201d01001092042000031500c80a240c441290301018080e40d9444840b845406900d20160100b12840001808000000c0c000e006080c014100028080c0e140d855200c201c03840c00d511004250302c04440c08c030600001d03aa9100801c00201d56010003441c1614 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 722112446 1250 722111196 722111213
    0x50712050a090f03050a02041b020606090408161211150c0a0c050318030d08010b0d050603071806090b1c0b06030a06050c03040312020c03041a070c0605040807080a 72
    0x11516040040c082104604544101071400c000c0000d10140304189480e420160b132141c00554040f8072aa252004070352900342695070190803032465401030304440d520701040c07084014000308102c68800c020007000703000105c600380c29030000d40610b030034906582294102030448049404006500c0d8003088038010070804070005690b10802c500d11064682005080c203982c01100148002c02c140000705140c5102c2900c8242c0480c3c0d41c00c01c030304072031160070480301c2076030903540038001c0b0400e0742000c0107202c41851240c1c00698000c4c1340501241c3d00140d84004084030089071a4086080e00d0700c1c1c5104025800e50344c01801d4281004880c4034580340103800a0b6405104414402840302c908540007400b1a40c09101a01c1c1968025406004074a01003400184030f40c02110200e02003800c3c0c0d000c10031745640c20b100351400440114001c52602d4140020451010200400455440803c110b0100060703100c8002c1d00050449440d0151a142003c0305941400d1443c4c005800030390000144901084242 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 722113696 1250 722112446 722112473
    0x6070e040b1c140601080a11040507050f07020d02040c17090d0801030b070e04020a0f08100506030c1c0e0102040302010206090f061b190905150315010e13150608070507 74
    0x3000450764081d0718040400d003040340d0390f0011500951000142e2210003190946240e41700310b04552400621a0800c4100c0f2800d0f180e0a0014401340950900e00742c0c07a0000780305190004000010604080d800141658000c10010002a8030b2000a201c417915031050356030000c9601c00500b05248494a00904d0b40005100217032021805130007003402c4034090381d01103800d064090410741d80c031100030314083c013541d4002000b0340c0061414030024060500300c0c0001c1c3c0a5520040138545140c07201c000c100e12036000078a100c0d03040f6040c44905503400c0c1741845105681440d82c000541c650380344d030001909110005084030032a800045010541b184080340c1140c1c000711602803840096141d00265000d40503030700740c0c0c01c0702038a0621030b611410741050740c0204803501155601030103000030126070700601085d1111040742c181c090b20060703a5809120000c56801c009841d18003032200e45049202a42c0004c124140c0c2160071032018441654007040841d0312040c50b0510750314180c1155580030030400c56 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 722114946 1250 722113696 722113729
    0x50f09060105091305040c03232109090f010305010c08041101030510080f0106181802060717160302010c0c0201020312070905030a05010608070611030d021309090506070e040b 77
    0xd01c5040f650300e14008404808410204002c02c0c50280b80c10078038a8110b00040e130780c24103020b207065080150007000b840c0491901028110318000c0500e100141c0f410842e5814021009004030843d98542c014a14442d0070042d0202d0b03410f5245092042c21103070784600c40300c1007141d007500b0400407a107015803940c2035500030300c0c001031182e868542804a0314820f0300b004c081030040c8209901c500605420540980390f0314001050585005507481e0116081483c01c40c0010f1050030801001d0300d061030240c19400e0007100700b074000c01c10004400240d80d1155141c50f8845d04210203040038164240b058a82131072f81030520340008a203d0300080d40e24002d410381710410708801000940ca0700d225055040c02828050101c40c00080309240c01806400390340139204071407080110001c1d0b12440303048200398003101640039524040c8101c0404011b94000e00c1541c0c860341c810480081ea000403071040091040c02440a0401d60501101c01402400301202040c812130402e12650025a03e0429900c1038445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 722116196 1250 722114946 722114957
    0x18050a060b0f04180b1003140609061507080409111905070b043f030b1009150c020d03120f090803010b071e0f032003040b03060d170405010306050f090601 68
    0x15022520026017202d840c280e40252941c25151119a05500110003c00c0c84607110903c60f0b03241e13010302c03c000ca003c44000382e00c9031a404034000c0c01034030480184507046c0103081039444d0503140c0c546001a5840b1039005d00391074000194014210562079031010406c040c502d0b00519003055030311402111a4090800341200703918042d20744140c514810907948108204502c247d4000007480289482810344501e400401d0805422a03280d2a010703001342840f42c006e0702c2d080905c6040c00e10180486141038428070501481100810143c3e454440204070284280c0d24407007414081c1840b03030241c40307080700d012600c10f0404401c00005a05801a80d0668400c2c5082c02e48034005414080340c01e40e0b00b00c00042940c1c819003a20400d001254042c14041406a1280c80304011038841c00da42d80000e1010f1070f000c40c2c1060200780304001c0399000540d00104014240815802c1c940c4501303a8848269402151000e0001410007075940c01d8041c2c14000c1c8000c8a9523041c4031043e03004a4544000202a10304024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 722117446 1250 722116196 722116229
    0x6030c0909110706061806080c03060708060a210303060806241302030a020310051203041e0b0a090e0a1406040525020705180105030a030f030618050a060b0f04 70
    0x111020183d420403a0490f5013404500d568005001400d00303000ca20705a282c0c01c111011800200008100e9191180a0010101607981d00011181108054160780d40170040883c002111403032046003074001d4408071080090642a860041c0480384687c0c0052140e0700035a0401c01010400328010f02000d98040b4400c06e0003106c040000d810440b80d444021400d0720101c1480220940c82d80554861585000c1d016540c644803000c00840369030003000c004080d4000c200906c0310f6411154403400b00b2109072007003022a41c4410007450700d9004091400005000100c0130845442c822104540251484da0100700c43c25406041c00d101d50402032030b55002d1510340c03007c01c280710100ea0526421000c104021603200b0804cc07002034a8002034070a8a1085070701c1000f07081058960843e4504076030000740141150b055543c3d040ea4090103145202042c541d0310000081e000400c0d0070b140c6a9030519000008462a08452090860b20183c000151100080c44414000c500400071101590724040c0541c241c4d8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 722118696 1250 722117446 722117471
    0xd08072a0c0b0708040305060901111c110703030c02160b07170921010c0815040c170106020d1403090c1903060f0b13050403120207020402040905070206060a06030c0909 74
    0x3a0340e5030b0107811112000a0020180100f80c03011300280d0703101e001a180c040d1640d04042d400c0c0c0b209941e10001d0210204100c400c410044d140311640d452100d41d0219404a596030510141c2e00f08801c1940032a48a401c64600d10381e052102442c00c4100c1705240300407504080014030140038845009040c032401110007103105120b08103a508100c4000c1281d0031004140c40240c400d4182e05964605030b40c00d04ea07184000901451140384100840c1c480c4a800e1150700007040081d02049285006200303040d8015800c2e4180c4e0a1118060841c507001800c00d1450010b0041c110f41c240c51403812004002e1060020f003510115600320303071140440700d200100d106080b140d50135041542c0014141d038a8080e0100000780701e6080058a0301080300e8031420359a00e907110b0b40c1a128211001000031300010005140340394554083c001c180e001400c0103047c140c59410306803c075032080e21003801503070010040241c80d1070420803200140806180a010741002840050b107000140d0148170180c589800c5241d554 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 722119946 1250 722118696 722118713
    0x1110a0e03070819120c031b060207170a120e0703060507180906150216030204050a180501020c0f0a0f23031215030d05030604091a01080d08072a 64
    0x907042c003000781c136151162010b00910010140000701c50106003075182c003074400e00503030360116030f1901500c1c0c0c002c412060b1001c18105500c84041101c03150b40c03c0c8500004035890340421a1500d000141c095501d0b00c0040d001340444d25200c00702c1305800c0c04c207200c207000400c0c00319401d000ca079442140802c0b40d2311610303002d984c000304d400c00c420210700c8030980014040307401e0b4000c0300481c0d001036480a0300d10504501281c5803d620708804c00c40c29603903a0104014202984010340c46031811000050314030452141c1903203602552010364160f034012424211609050004072000241d460041500c0f00d02981d404280800c51040030300300c06e000441c0340d10218490661038003078460040c00d50380c0e66450f904d2038843c025015290400011101c5108500504001841051410442e20b074182569241802c12010b050b036090301706c0e001521040320010310102c000303d03180070b030011b14060f0003a074050050040010714003d10740301c100b10720340003003400107686492000d00c0445100b011100c45aa10f06003000c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 722121196 1250 722119946 722119949
    0xf06040324060e04030c030f0806010f0819060803040504050f060d03140d090b04030806033009061201030b0a020406200c090903040302040f0b0604060c140a030c1401110a0e0307 78
    0x11400000f20420042560201034010510700c20b80399000c601041c600d0032203600ca402c4803201c0c08181000c2e80011811301615902d070380b2900c00c0022444059a452105c03050f03420542c000c00032940701040034481742c5024060240c4c0011140e00399640b503c0c003280000d0000c0000c29010b0140100000440885412042154a421007429050081081c145080c1c00440340450701680001c04c17007800710701a840c020540c9548039140b180d40207a1036821403099a2940300141d800e0f0012201004241402e8481c60040c1c0f51a00503000e5100b5150b00d142403c155004000304a1ba06485c030422042c071600e5000802071482514900c815180001420754230352030f01c14421582e56001d400501081481900000100192032081c2c130144101c550304410781c0240d4008180d85540043c06110a00c2a10720468480380381c140141c4007408648880c9011504008801400340d00258058001a05120440d030b0042c045c104284000c00a101a1940031300c01c60161103403076000c0124806042403180d804105c00c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 722122302 1106 722121196 722121209
    0x10c0b071805120303010e01171c11010906020417070f0608092a15130306200f030603010608070e0c0703210b0f0604032406 55
    0x11001d010508444807840103001d80000c06603902e00d1034010a40502010310344c0e95061140320160b111050f001512046400c44524102c80000681e002c0308101401012109604a5500315280048210241900e600b03191050083c816298010702c00c43d0b440580d00014040e0318911a42c61b0005445400b401c49030341c1404000880c080d00e003040d44254040240d51031030104c010b403400809250f070305400210f401200d0001c0c0c3e84c14260541e440452a1030a04c42c241210300b00809402d1000340001401c0903246c540c0300b0044504024070015240340080380b2071b2502180d049138011038100301c9080740300c1e42c02c0045c00190707900c01098090940700030210004a03543d40102c0701c685030740b00b01c00480400c010382d114440500020702003080c0f61054500c000c1401c036605020006440c0480d000e081c8103103820401000062144d8143c010021004100d000c1208003001d00c3c440285026403114 = true := by decide +kernel

theorem cover : BRFrame.Cov 721942446 722122302 := by
  have h0 := BRFrame.cov_init 721942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 721942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 721942446 ≤ n) (h2 : n < 722122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
