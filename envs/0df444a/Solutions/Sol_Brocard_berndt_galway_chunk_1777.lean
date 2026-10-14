-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1777
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:38:15.540441+00:00
-- url     : https://prove2.me/submissions/e2f8f9b8-b520-4c74-adda-b2d0b5989b76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 319424460 ≤ n < 319604316 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 319425710 1250 319424460 319424467
    0x8030a090c29040308070609060f0228111b030a0c0815090304050105040e0a11040f03050c09070f0503130606060e040e0606031e032808070e031911091317 68
    0x1654803000b4810300e06c026000c2c80e582c03400441003000c250044203076000720600c203548440e1941c0d5071402703419000c5412a100e14621030036074090307070090490700d5101014401030300c0744039000b101d031441007440005129490b004821f21100040c1080d04400e0140a502000344040212070064201c1e5100c0a003c140c580d40c0244010442a03038010111410307284420703d01c1013203807030b0700c1580380c081c0c821038000500e69803002c5000301e040401d00310180c1c00c690080e400c071043c0e070316040c0a00c11800b10942d042c2d13002400490341c440d800340c003c0c40155009408011980d0415a003516440c08484041d002880007500302509003440f0314160103650040399040005e04200d003001e5001a035202051506112011a101701035030758503005000356440c8040c6101480e06c03401458210041d9829081c1450000c01d40e04004555490701c9010420382c1c1100140041c00803901a4900030007040304408100d6544001d4032070780c031345510b61046403805100c200401c140c00250030b01d0100700c00d080c40c0099900741001030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 319426960 1250 319425710 319425713
    0x20c10030f14040209270a0302060403080f01120212030702100305060a061e08070225050111010207050a080903070f030c0509091603080d0e06041a06030f060408030a090c290403 78
    0x7000d0b064004103410348000c000c1c0f90a00c6c189a0300f82e9031095948550003031000ca03000340b50b00404e08034801c5110391355881a5581351030003480d0b04d550a01032181c6000c12040360b0001030800d5014101c02082440403a401c211180d400248500d003d032143e8000079032100e007406450306000c25154094807150070107202404085200c02d1108c1c1c0340d24007090801c1491004a036041e8001e011400c00441468030070240c4100c41c8503402500d03841481150300040c00850a07181101040c03080d00d801c294002c0140082c40b80c680c0b503400a980000300b03000d9140c000c019000880089688001f8010361080010b203201a160208100c181c2d10024011301440d0424104001c211500c00ba034041565070005d001501c07009419003080c020b15160b4903d1a092044500380030910805000f141941c002d0846281d44a90b13030101810781720042c200d00380c040d40d0b20900c00308002485100c05181e100407031020000b0286482e0720380d00041c4c54103600103640400c10034224260685a522602c444440200c1c2003498286103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 319428210 1250 319426960 319426969
    0x10c0f0204020c07140f01020a020f0a050a080105150d03020615130e01050603010f18140703080d1a0f0604060c02061213120c0b18010605060301091e050124020c10030f140402 77
    0x841c08024815030081c3d60380d44bc5980d07040604070103003d024000181040d00c0c0c03d8501d009060540740031600300b119207411681450010111214951b169010300156207400340b40050701c1b0b41401e540f0f50b102c00003e0f03001d5145840e51041e020020b070040d002040f2414800c003818211044c1200407203a9a041020581c95500210040680e1907403101c074800d00781c05030300465418200381e50001003024100140c13001d42c01c0d020360440c00c1e42441c00100110b040300100204015000500a00351708002d040c8001c00440c0d008440880c01c090001c0d0072245851103401ea240d041440441c0c80540c0d0000c2000710500344081c04c030300c40c120311b490760801c3e46035041c0c0b9445c7c103180301c640101400c612074419952000a1030302034000000410003e001580c0b00e584851801c0060300c4c0f400c1e144082140350f1170841903480c8503405482d048440701c803400c00d520003030041c8508180c1000c400c610258804c2003a840c0c5562992001100c1c00d0815540002e0714040c810503203000e0362581d0b074110881046c02000d010140c4c1c0d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 319429460 1250 319428210 319428223
    0x908010e01092f010c05330f0103120c060204030501090b010e0a02041208031e04080c0d02120910111204030210030504050d03020a02070b0301080f060c03010b09010c0f0204020c07140f0102 83
    0x202400d04100c0e04401d851b041f4640700090910b0800c1030400300b000070b118141042c42d084121084c040c1c03030b1496511616840d601c01001d00c0050070464982041e80c00c8640079244602526024501c0580b0b800c1d202e44805081d504040c0d0222804503038040100031450314001c400e904103604000940c5020700d13100b4110144010b52602906011000010541040d614017085680d03c1c2c89030700440e100d14107810114025008002100d01c40d010307285104c48041c3c030100e0a500f090900c3c2d00072506105014003440521007082031204140910040c1401e014541001314100c4003040b4800700380d5890442c8180000010b90108460a00d41072206000000c1d00c0030035180c10701c01451030b00685813611840c0492034081940d00c050b110007800000418000c0001c1202c00002040781c1c00c45980d82c848080c0368000344000d200f054841841844440110340c40384050a8000d402407900c0681c03841941c0004007245e000300981d11a0707600c11002000480e25403803c0d03084120341160304400c452000c800213516080f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 319430710 1250 319429460 319429553
    0xf02041d0a0b071e120c0504170706020105150a12030c0510060303090b0a0f08090c150306030c030601060c0f1a070f08060609060d09020a0b030c0c1615030c0908010e0109 75
    0x240c840c6c0c3c40002c880d10507000c2d240100b0902e0038403244500e034641d1f981d44500c003900801006508203400640c042a841ca51081e00100142c280c2035032a280410600d00886405801c0f01044064070502001c100100030700d56564030081d000090052a514001d0b08c641c0e4507034001011280144040c1c405150050b22180100c4120308082040e07076a6401d076141040c680780d146581c45151420549076142030103000d584102c601381c00301da00408a01d81010f559000074403e1100190a00d58920f0014180f00a1030208500c9110390a06852500341500307806681111401d0000b0244100c4044a550104500ba0020000d81e20380b49001c24000100d6805e1003007001c03800860b504d840c070804c119100c00030b01034010701c0234040680e101c4c01d02c04103c0c80c0030340c00a82d400f16544034440c1502842c40d1741c80302e03480c00c81d9440c0d20b107500a0600a581039000d031a03201050414000d0114000850700e50a0040d04058101d00307000040c21800c038a401d00d001d40750346080784181048075081c2d00200050180640b4800e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 319431960 1250 319430710 319430747
    0xd0f1706010c02040e0f0c150405031f02090319050120041a0702030a03052a0c090a140702031b0102030603030d09050a081204060b06070f02041d0a0b071e 68
    0x20083c00030502034100c0ca441c21590f40f1801d80ea000760440040b50b08005200308640c07000400c6032054008866005902500c0d82c942c00421440400c40000a502e0303132001103401e0f0150800c461040000d05100141e40f03060185051308881c00300f00300d028030411140d450304802c511003c1c440411404014011400740c0703070011000d4201038410303400c401c0a4403103150b40101180c0c5005514900244140c20500303d0f078000350601103516401201184900c3d0900da402d800074150404224108141501c0140a001315107664134a000c401070035200c1c0d110301c203041d01c4c0c0007541e4030414492403100008403c490b0b040743c0d0748140f06100c0b480e13501008079040c41255030000b1607112501e06165040140d071220061000340d0008135445010000d042040c1b0035409510100182400c0e0810301c200c0e4420204010500d0300b4428a2000501e0300c0c1c0e101c002e0070440001204100343c2c405034068a850028401a119100c0e07070b000300a502e07030340009503007014007860418903850048002c001d401003845c0407080f0b020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 319433210 1250 319431960 319431977
    0x160302011b080409060501020d080f06060310050607050a1b060206010302130209060403050d0306150c020907021e0610050a1a0a18090207020f09013b090d0f170601 72
    0x101d00701440c0c103203035964110460320f5031242d60725000801400284221030150080a01c5404028041d41180d4802c9807400309001840d40e89808000c65075200400d20020000020000b10303081e1294030150180c6442000101030110103401c0c0700052104485013011400f03d080b400b8402c095001c1440c1b81102c0c2e05903107420034035180c003400c400a4011445140d80012002c02e0000510100040d52014210682c50421515886480d50504028110100700109000c0440d031001410110105270f803100d01841980e58400b0000d03042d09141e0007000a4401990083d800d108220300c040c41c202e401407104a50009030145401c07002c00c2e01c139503100032404960b00049164040355000e40b240400503c41880240d162a4480c04644005e40004034180d02440080307402145a0900100c0103060b00d0514000c40103a008103612055090a041c3c2d12402284044009000c2840d0200d440303402076900d5005044c03101c500b13820050010031403465840412806c4614400c3c0c40803169915900329000f840d15851 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 319434460 1250 319433210 319433237
    0x6150c030804080c0a030c0b072f0f060a02090a0f050f06071119080606030109211206080c090f04081602030a02030f1b180a05190f1d16030201 63
    0x6a074010040340c4c400394010f0154013010590f000c07015910080c4241e61078541c580314240d0403501103a248008080c0c4018481c104200d0701303019609040c0c2c40306603104030384800001c0d6112a062440c19143c916119802043c0f40c501e92600c0c03c0c6200c040c0030300c19042c2c9416450300c40003840031405a82042e008500c0029241c0a10119160036030040c0000b030404041752040880c10004010544a507032850701514012610b10324042c080c00b90015001960101c0c4140040c2d94150310300800d02230b1409000d4441001c040b01002e6000b00130040c001080a00710103200041846000e5000030115602e011840040100107881041540d10003504015154642d0115101080c503206480f03030f010350701d44201001c940c00c162000510300c254005015003140100b03004418006010440004244444001d400140011645502c01c07684446421301c10103001080d483c0c544129401880640007290300e0303078201001c2c14202c0000140380e1520500500103441500500b0241d00c1184c04001d0410103413891009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 319435710 1250 319434460 319434473
    0xc05010305180a1a130302060f150d082805031303030e0f010606180f0306200703090501090e01030b0f07020f0321010f0f0e0a2a0306150c030804 64
    0x2d00c000c4a410880d5003079250f81c18106540da040d1030030512000408400107130200c8118215201d0907600d900240038588420b4222264040001c1c690040d10b4040c03000350500f9964100d05507555409000415910302c20055036040b90516505014100b94010f140401c459501000316503203c2d00165202c0b072484528501140600440c0c003a0803090700c1303520308080c1111419884282202c49a440b5051003d040443c0c80d002100d80d44600c000400c0040000c1012864640101d0048040c0b140014565540e4603141c8405801848090700080c650f0ba02c103100035600840c410001c2c0011f40b0401006600d181e40d003010b050f0700203101d00b04d144480030220f03d80600030081064440920403d076500c0d6030310b03075031120f05003420316001d110340c070b1200e20002a8a0094010079020f5564401501c4881c03400e10309100380030103015154250300f69072041d28654880406040340c00032003d0301c01d015101400040300409a1301c10750410214010200480c40300c1c10b4216190307400440d898246401c151340e8508228 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 319436960 1250 319435710 319435741
    0xa0618030b0a020c010c1b0b090f120310120f1202160909060f0e0607180e0a06060305150f010e150403030f020d03051302090a0f06061112070c05010305 67
    0x52a011159050064007400350700603003041d580b882c4c000c0040c0d001002d001c840c010036000c00d082a09100545840201d042039100944c0b1402400440e0800c0c84049245890800c0c40295003010303900c080248080c0180b05034011008192416620460901c2a100c0034038000074440010b084034108542c1e00c1640d4001d10840300882c007107210040e03290355180b208001400c00180101c130203500d445405c2040740000d1007000c0710240814020003255450380c41c1a100c080c801c002c0011011000c20300018450b145d403911038490034040c200483c200b4508440a0240d90000c0c2c10f00045101c8103116100d907807150030310800500401d2808110f12481e40006c18046a007580701c1ca820280300180200906400200041c0115204d80c202d40c0c1d1400e0720030040381100c80a0350b12101034240e0b03000788800b502c0d0510455420107402c44000500740101031501044400030751080005c81d0b1400380f00161400d09001401039919031000092401341d4580c0c4090401001e401200d0501d551a4049241d0441d01d5480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 319438210 1250 319436960 319436963
    0x9120703021c0f02071a07021525140d021c0504050d0507050127181103040609020f0d03080f0c0c0a03050904050a0212070f05130e09060a0b0a061803 66
    0x100c05001410100003854161060703c0a009403150250005501c201400359141d0315400034440750504900d40e00300701009022040d0071480200902110028100034803010503600394804840c00780a00318a040251030401c410f0f03680d5140c20800748607094540205040b006003a1121122140108440303065440d8060341e0816030f0440782c1745201004010b00058080240c9500b40c9405103c421120603803400103c942c410401810720307902003001341ca02d0703000060140d4803070701c000440e88001c00c0900200680089800303980d07098944d104401981030020000044500655a800c02510103886c06801b8000240c004240701e0703a10400145811049401d80d030001884200769107001c031450070700614641101240c11321440ca40804036010ba1618801c4812410300b00b030300c110711981c0d82502074418600f152910f2090050070844c403900c0c80284840b62010b448401c000c50318074286443c5071490000000c1400344018540031600e040d030356031301205800326081d5203065000d00d4003100400003609000d500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 319439460 1250 319438210 319438243
    0x9030203070b10080a0b01092415030609051f05030105060325050910090b01030b0109090c0903060606050c0f1603020d0609080a1e0e0a0501030b0a050307030f0c0e0912070302 77
    0xc04010400318080d600c1c12123405c40001d000400c911200b0b00c0c1c140240b1002c4d07a02c1403040110800824207424940782d0382c40000c0c01d0020390603680784000e100343c510443c2e1004000c140d81d5100f810955510848002406c0258000c0105203803803004680c0c0c50301d0744a1329100c0800324424402000b1000084d101c0a801c0c00790880c41c5505247c00300c1c8018003141c0c000c60500d00c0c06d1200403e00755200c1e11451b68640016503503461182c0c030340306040004100b0070030b0220401c44a0003011000c80c0c0b0a0242e41d008140d19030f2855540e00c05880c45e1414404100034424041d04031485021f6400851410394043d00e404907429140d44281d450400000d060542c2c0007446141c003c55600c0906130049160140030824050080292a6520b82200d8510359140003603400340541e003052086502c83c0e40814044100a09031110541d1180001703442e04c0219842103074000c4460105004000002c071602d001800c2054101c8558100210155110b490300524644800c0003c198903060510801802c0300d0002c080c0c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 319440710 1250 319439460 319439473
    0x5250203010f0903080f060105040b0f070c031209120203030702010503090a060507030902090108010507020d03020901030207080304060207110d0c150e04050403090e0709121506051c1509030203070b1008 89
    0x2d40d400703000310368025008243c9481c0050780003580d050342548200f00c16076440d464541003072210201f0740c02c60318042c03601c3c0c0400d00c130000001d51102c402d0320245005518014075240c00650080603002c0d00d403c259207021800c050078005840000941d050540d0900302241c403940c50001da2807030f20503956000380040d8284800e21418907095408202e0701402504c040b1516a00d6a03405401e9407019100c3d400140e00c108020003000d40b090340903109134441450b001d8944000703520380b50019001690305880d0603a00140d503104020580c50303980065882030381d0200000200707403a0341107410058401c007401d000c0340e620f85c0b40e42d43c0d11508500303201002c001c10810007801c1a090003403c0d03500c1c90250700c495515070000308070082c0c01212880219806800701009048650390391202c2c49030b080642c644266210f0b880401d480c0e4400864800344d0032002c0501394402007a080070701c0190340300503d2558881c548402d00c07010035802f0080300c4415070081c810140d60740b2810150380003007025920810444c040d04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 319441960 1250 319440710 319440731
    0x110a32060313030801050411030a0903182402010b10031112040b0405060901150519091b030b010f08040206090f040204091d0705010c0212010b0a061710060525020301 73
    0x3290114001c2e400307a9584161682ca82040c04212a5242151710814a0500014502902c941c016a08040c444d1030400c0c00114000c005560780013294103c02c80c2000400b2401e50f140c41c2d0b00c00e9502041000303100920a1040030f1001c40c034a07185036101d0300101525030402401001031001140d407000c840d00c0c3c0c140d01c1c501c0d00b4181090605402d5404440a0107241c003c9007943c8014081e07403061001942e0a041d80344c0c030381000c2088500700055542e10381c062188000401c4042c62055140d0007090110b070003442d01001e0002400c490307143c07a4081c140601c441030301c1c480991020b40300d0381c842e40c10f40d0709660303d00c650302c006005401d00625040e0700900000e0701081005aa030400a040c81c4924640c004000c3c481010310b85500d0f040c02024002440500d9030000b51800845100c0d244034070100000f0581d007210b020880c40201a0442c0003c1011300440c0d640a803440707110581d00000c0030b18400480390404030014118494280c11490707401c0f000c8049910700a200a99106081d4020000c0100d204007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 319443210 1250 319441960 319441981
    0x1111206010f0809060c09040906180c0906080607030203040f06052d040803062206080303070f0302090d060c1101021303060c050403030507060c090806090a110a320603 74
    0x440e1894001003160741000000da0081070303254041e0820350003400d0990307914401064140c009505095025864100481c08100c00c3c0c42204c64030346041a0582d09000039003004004c000340ca6000d844042e140c45010003d907100414125009480ca1a001da900d4440e03040810a20303124041c080c0c02949400203100310b02c1a9410803c0704900c91020030000780b04210754a002d800002c803805880070400b040050b41d43c0c54681d11007940400382210404035412400803010445003223802c00c110641c00081030024190b08100d2043c0360403517030b00d8298130b0300051350086003128130401c10060007291240844040c1c41c0c0103247c1c4100200c0b00400131525022074038481007458106201c296500b07450300404190443c0301388102d50540c0e4050b1030f180d03e86602503640d00024000d00c0100c0d02084101c4101050903501400b106000d011004000c0c05400d02c541400030194082c0d1307007102d126221b800d800b002603805205c0c080352680404e0040c1f0310422030102609001402c0c0240b0154480000002c001203c101c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 319444460 1250 319443210 319443247
    0x90c070218010e01121505060d1703061305070f2d090302120109080403171303030201140609070c03080a15030c1404050402010e130b090c040e0c07120503090111 71
    0x4a030081c3d00c3e036038407120144101004e620181070800303444103066509040da0000d580000780034103602c800c4003e035102c3c1030700d64200c001301d1020f80800005000c03403881c040c007034007a42c0742c0ea4a804000c50308001d0000380083c0340360f101c40d5060082c06a071810a2504417004098041d0102c0c0e441e1400000c0c10000411702d40081c0000c0380b04610521589000d414144a0032a403079034455580d6181500315203d804021261a0181c6000f290802c0052100340d2035038003003c0158803a0700041089030001152a000324801040e15000b8040d060801030b440c1d5009448003c0c0d140c040c00c2c6803601d0780720101c40001801c1ca20300c040c10780c501403040000801840c4c0c00100211050b04018801400340c0e1010441520300a46010b8006429070f04071a0172860b140c00c0c0d188481c4090200056546c0701000131414040381102c501503483c102042c00c03c4101d00e41144c5c00d503c12800c800c2070340f5140c001da0f1028980241031148104011001c00000c01090f025842504020341980780d850301e0f9404000b00100504 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 319445710 1250 319444460 319444469
    0x110613050f0303040c0b160615091d03030112020117070816031406041109041104080c0307050d03031d07150e0d0f02010f0c14030a0e180105090c07021801 68
    0x1090500514038072401100362406143e110f500b03145075610740b0703200704c106410290150080300c0000809000140b000d22481c01c071654049402c80016207003610f0341d4212403550304529284030340131840540826011080300c1c10356120700881c8085041c540012105115003238040d0864501120500c4002340e0804c295502c80c040405040102d1381c1d040c13a0480039500c20141030f41007140b038030000c2a41890140c004400b40002c0c0c00c0001d00b00403d10000505951285110111041e40000c1c14170a008040c0320000c075500040d0004c1410314600004160000f0082c0f00240030074aea00c4011800c0f00800c807010528088001046620264aa21401d502c0c3c0744c2c40c030100d0700428403000c40c1b52030380d091100340f00007143c0d0001c490181c0074a8680040d81e58140c80c0c1803000c10401c60f01990030001e03100504000b0880b04410045803a1071206d00060894070707800b880349120b94442034005004640542907141500d0051740c9080c502d0300c030400725401500410100a50202c1c0069480c020814410701c2c1c2c2d41280c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 319446960 1250 319445710 319445713
    0x40506060316060c1509051b01030f020a0909090f02060c010b011b0b061002031614070504050c180a180c0e09010501051b0f1c0921110111061305 64
    0x507205005040188140c501042000d110030000c100c0d58800c0140705d120401001c601e02144da0b451609191502100340e030200c3c41200c0c0581c0c5940d1510441d0518107012604519040070380340090312030241481084600c070b88640c011020421040c030403103e002d80c0070f40007039121200d00e69028041d240030300c1c45600085501c40181c001428038964110010b400c400100103a8448000707104240b405040b5890a51104001c00b14030300c2d031240311148100c1d019031051000f412414000a04280d03640c0e0126100c1c904103024005010751030400c903902071000804142d00c600b107070004600084c900394800c000c2c10f007120070640040007141e00000d40704003c51703441d40c0b02c540b40c2804025450400303000300307400600207005024a204070081c5038109000c131903084515044811401a01c2c1c94580b07810001c0240714201203c0342244c000c62460040c118880040383c074920000840030039021001000f40080c020a20541140d0740903c5141409500c00006e5800030b1400c3c081090054005035003c8619 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 319448210 1250 319446960 319446973
    0x301060206011e1508040f020a1715150d0f061d0f0a0503090f15030702010615020a0203150c0706060f06090519120203071701060f15080402060a030b090405060603 72
    0x14040b1081064043e5102031030000c41104d00300704110740c1c05000400c01c507414540300d40110302698407a0082401040042c4080710200003030700502c0d081c4032103003041f01114050300c1c09004000c2c80304110014400815507003890002054103100c0315812030060050921407a052600d4222580c100b90412002c0c0500c080303c406046d81c0c0315655035083e01100252140e00144903100309442d0020042403100801407441e03078a0981042d24000e01e030b2007542c0385030160399200001c100c0203911303d01c80910700500303001406800340d4580219445000415058002144010004010406070015102060740043c020000a602d401c0e103142c40300e80e14010500442d1000030005180d20b4004500080815400042c0b8040c2e840c2003a40c000000780f0100072603150180501c0420406010040010b49509180c0045102858800c000052210507009102c42140380041e00000ba500415040e0700554191082da550382101c1004500070000c010006502480050070312080c8034001910318000c090440642d0720 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 319449460 1250 319448210 319448249
    0xd0c1211010e1011070801050a0b0102010b0114030106030917030a1d071208030402030319090e13080712020309270c070507030b1f0303020609121c050c0c0102030106020601 76
    0xa00341c450908069101d421103d403050b07001d04c036500003124071030070302d003211403040d2110034040c01d5170b801300c0341c00750f09591740d1203010038560b0b090242c844511020702f084100214981501e40107484140168000c1c1511080807004201003160f21803116207010943d240c032420000f101744040c1c10030304070b043d001c0c0784040d9592002d500c001c20050101c42c00f11045080040781a515108113802c0100180d0741404207000c00783ca02204042090120001656400e50f0503050a002e20341801001d01142d88042e0345501400004084804582c0c44a820601070312a050608104a10318032881120642155000d119101103802641c103103a0314003d505030f081c2c1c00d5524807148080a008000d8003900300c0d80110010404101c04946803500b055044e94030814040d46030461030303110b001030791046005a2042040140c0d056040c45042c603101d881001c894035142083c40316200e0740c00d4800950f064150f581c008600000307411411a070151111500a540780c1d81d4808010391154000d03c5031001c4003000069100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 319450710 1250 319449460 319449467
    0x906040620070f0503040b1308060f010e040b0402240d0b12070b13122f0109150509090c03180d0f0e06070b0c030a0e01020909010605090d0c121101 65
    0x1c29801c01c0301d01ca2420000d1503100c02541c076106030030a85041c041008040740e141c01e45002417110907038042d9a070319503a1034020681e181c40801420704a1550340000140304c001c1a20410540140d0028140103941d2250b00024608441600c40c8003030b554008030341c1c24400788402000e03100b03440881c3c10801c8414005400c0c0040c0c082c62401d4580241c01c41181842425641c401510004009061001359282c551110600100b00180300790b9001d01030b49080403003d103090903540b580301c481c001c400d1042c041800005c0c011040794003a400001c06160707070660000d88170304252161004018504005801d1100040005078416079062280d10341c2c000856207100ca0004800a01505a40d40e00e80c1e80c0020b000c044079080088803d85a000404100790030224072403990300b03401944400c0e07405e9500d080074a012012202c94200c080e41690061249ca00180d40b40ca4000d070445403c0e00700300340ea68008000041d019100c024000340b801c2031100d00861201d480c450948501482005551a18240f640055 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 319451960 1250 319450710 319450751
    0x1a18060d1d0c031b01050307120c0201023a02030a0b0402070b0a0b010203030403020721060c02010507020606012f0c1003060602070b2a07080109030e09160203040e040203030d0509060406 82
    0x1030204139072001c0c07425580d51240c4011035002c6020b03e1303e02e01c41e1345080d1a00041d200204500c070300503034000c1403181080b0a4000035061014029140741144c01d03000e00e4425004040081d60000c05074084000390450310542c00c20000c61100800440d6920704914100f4880d44e41a155181101d02c1c02014003140d5000008803070103560513030010b206c802d180c10381040319006036180703030340f8a0030303100d41180002080da00600c00749031400c2d0004034a600d4070341c0000786028402022641084a9000c0f48500e0300030249503030909c011b00cd240151174210728500146006440c0e8650364101d40a64444030b08160715034005016500039a082d00d800681d0364640702505d0060030310301c01d00001c40349440300e880700c005000c1c2c842a04074441a10030590391540f500b821900d0071070041c0c0204108080300c040500d0075403560303541301c3c540d0307184481404c80d500c1c1e00035a20302540c050307101980301e02c3d80418290f5a003003003941e003d80ca0604c2c0a000320301d0000611503e845065508036075507410664460095419207009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 319453210 1250 319451960 319451983
    0x60b040303081302041b0302120c21040c0b27010201050f0604200f0405010e0411070308040303090222050a09110f0d0c090e071a18060d1d0c03 63
    0x42d122980c41c0c0c85460f02e652855010100e9001e582c4030701071200c01010344161280407455480050729003c04403840ca690740b0b80184601089075040210254100070640c83c2c0c0e28440101b680b070079007a621031500c1c0c1d4000c1d09030f80220901500118002c8007100180e124003d000c046900303440180c038440c0e00164240c45e0709440060f00b5203001800580c0506140c0d02000c1c140f501848000c690303450f1002100e09640c80140007035121100042d040c04a540c01409c814291001514100040e48902112100d24094810b0081c20441d00402103824035120790080014160000c203140d2807055036100d8040d02003140154207100c24100000511003440900c21040c04540080107501440082c2c020020320070401d042059201550031040d01c040b4039515444070280441c1c1d00c0006e1103900307a416003490101594058040c408554044400c00c1103480151404914040d52003220814580001019401208084003d43c2d150484013074011350548000354002140c5010341c1c20561417003040c5920f50710320052 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 319454460 1250 319453210 319453217
    0x140408010e073002060d0504141501030209010303230d050105131b2a050f06090d140f04050d060b04060902040803040510050405150405030709020408100b03010605031906060b040303 80
    0x1003d1012040084096540620042240d03180521100c0e5078011290281c40c10307500c00b0102030034a1040d00d420046080340d807036000907900b02585107500190b000141404001c0810201ca162141d40d0f0791844042c12400380d00540b4030ba00d078140c00c0c040c134000304400d1080c01e2160540b0001c07072413690036521030302c10a450507104a0504040300d10064564a408016040b400818035541845a0320b8404456014034802c030003524500c0c9010141c0c9103061000343c003024058020400007000260003410701091011030000003030321034045981d0700781c19010b0742d40f010b504000014000c1c401c10445501c881109101210204061074440502c0001c0340034500500880364800c10040c0454502102c070a1540c1c052450325614182d29240441c0c000e5654040c01215035a020a0500061906010344005400864070441c14545482d81650741c400305441107540d040c1c0c0c1c681c081240c2e61020740000b0060710000c1d08458036049080801003120140400a6502520748580030620080c40000c47d01145d40503903 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 319455710 1250 319454460 319454519
    0xc02030d05060f130509011103060a06030c0e0d060f062102060f04030c0611010b03060f041b030501110c1e03030103300c03030b01020705090115140408010e07 70
    0x40080e0300500d006802103a0018921001c3c4049030766451904140d103603580b802148900304900e815083d10b440d5440134068440074400c025064540c0340d689811038074140f46c081100c40320316800751026501d104071b03290083d1540704a04e050003a40e4004c86090807030044208581541c816503132000003045405200784a000f011a00050b14007440985101c1020030303941c0d0b00c0c09079683e94050070444039910040c0460000e41c0142c54607a0b082c031581c10301c40b00542c0541941e00e05540c100c51000c40040009200d0078131007012220b0020b00c54041e00203564440b008005004095001d440180c000c45084c0c00f6910804070401401c0d505e01560380b4200742104004c506590940e95054520006001181c0300166203003103d81c0c08995100422016910030b4039920411036150400409842400001d241994000c01e000c1089403a503600381811600d4062070300702000440071044900d050b520b0300740c4583c4000400d010503004410350001c0302d84400c03041100c0c03401d9515a181c00d0381d000031b0308007010895240c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 319456960 1250 319455710 319455727
    0x109030210182c0c0f0307030e030702031501151d0d0305220527070509030106050a0b0a110706021b1c030e030601080a11130e0a03031e0c0203 63
    0x142d40c0b07048000400c41514030031644841d100c4100c40c240403803620940004048403010802d8a00b080c0341c0200d59500402e10b80074016050344144e11019044400701551400d410004400a00543d1030f0b0b242d000b000c0e90700b0502d0f2840034400e510020300901e0107800c40d54500941e11401802082104c0005001032159031215204100050078891019018480100940c0003481c03c0b07102c08000540d80056072080c0941030030284450f03521225142c05180c000e407120512080b000d50b660756446007503031030001d81c1c03030f0600c6000c0ba000d094076074003091300711641d0728010030300307032802c2c1c2c0a420314040980d16016075048142c001c070740e80c4946101d01c10140c0c211030000a080a500400450550710244c581d048440d4000741c00c0070403d41e200402c3d400610000400145480c09120043c01001d4400080121500907140d44904480014005105140740b0304c5500d50b0a4549e0410300740c42030300c1ea0139216859454140600a8041544c81079226840c500ca441c0305003915100309480c04556500540c14100701 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 319458210 1250 319456960 319456967
    0x60509011e03061104030503070506091603020102102a08041101030c090b07080f0d0b01030f05060f01120b090408030f01081b10030e010e1e0705010e130e0312060f0109030210 77
    0x1850030b0101d1390b8801c20000c00400c000300008e20010348148000c090902d000d141d25428628400c080043c0341c07848070b20803c00740c1e0340018006901c0a001100155a00100405021513804e003020300b0408036a03101104442600003a00603c504c2c0903400034000340c1c1400d4011421103809144140c04a4032280090000d450400c000d4079125110700385040c0351640181c401d41c00740e0031100c003542d5a662100302c0482c0c00c2d45d040c02950345521214a091096050038070001c1d01c42000daa1117503040003a070503c00001c1ca0307202e8000c0c0021510240030701e49903041078204900c00c1d5004450000407403041e030000082d8403400050382c0303841e001d09136142d09103580f070b00040092803040c0d0f1082908058443c1e5050656480a01c40c41c2042c1d6680002005030542d01e05003c500944c04a50494142d0007801c41000a641c000c40001c542001c100c2d2000356180101d143d0100401c0110514900c511011421a00d0203401c94090307402004100c801088420342c030801103841c0850f9000080d00701180d11000b03a0060b02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 319459460 1250 319458210 319458221
    0x203240609130b0415050103140f0f0316050c0405010305061b04140904020f040c0f2714030a050307030c170a021506120a061a1f080402130906060509011e0306 70
    0x852032172040f00c0e0041110007402d942d001c7c0c0044e10000380030007100b46c1d000410402115801e804070003410a049050603410f172a405120200800021016080c80c10080140904080803400074410000755840b0b05250341d99080c211540c000702808401800315000880e800e4030111858203235010f240c4000f0006000365191b01a01c100d03004008052550259a1140034000312540300eaa25444c000484010080034400903064220301e581604609400d0110303c4408001503c8814148803001c4031100042464a1100240a0128000814040d04241c1c1c40310452228030b0003aa03035002440e01c280d00682480c03003040790b40b8015910900703030ba00c402000e540d4203503485000102401e40e58103070603203100c1c1071484500c800c0381c00c0c5680e40d040303000444400c514100e034444c3c190340000d0402c2c003009940300c1c401c54242181040c40040c4002604541c0c031112007213841c21f40e555042c0440340f050704e04003024104c00d0041c14810103101002044594079400c407020084071115070140301629540301c00f0010711 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 319460710 1250 319459460 319459463
    0x1023060c250f0501140909040b0a110901020a02060703050f030a05070f030605210f010f021b0106052103250302060705160b09010605091311010e0105250203240609130b04 75
    0x1100f44110b0503aa50f515011f0341c0f0441c000e050131704071842c02c3d01d040c000302d43d0101c0004174560028811018280d070b000400d65001c65054844642c0c4400707600301074610f40280c66141c5040000002001071030340c510f802c601c2c0101c2c000e0701c2d900501c50300081c0942c20740b9014000d1640051801c204000340e40c84c605051020407081d44143e84c0c003410300e144047d09541b0304020484065800154441c01d00314240030002200d0071400c000c012003420b00c03001403105140e40f940c00c0e0004629079a00e0710004802d0048491811580500c148500d9030700e954080000c4413008281c02600503a00040c08490040301104c250301000d91005002140c55075514082800192940d460b5660b5004081001d1301d07115a0240180900800b180c841c900300d1501281c81c1750060610360400507241c0510708642d800c60285c507444001e030f00b002100140c0317105651204c0d40783e0480195051051201c641071040e43d0030100704455071b02102c081c031103646000900034a5907040ea0304443c200510501e24001c50019004140c026 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 319461960 1250 319460710 319460747
    0x60d080f071110031401080307030e13021201060c1a060306011206060911072003060a0c020a12050a0201060905101e09020304051c081023060c250f0501 67
    0x240640c08640d00e644240f1144002c00d580780c15400d11a00c2c005119030050421500440c036200d100c0d03034000d103404811803149025080d01c0740381001005140d015501410030420311508290394498004240341107002003512101210740111640410510b00741e480b515010f17000304250792034582d40900130fa1003220283c07a8140c1d1164046005c030100c0c011080108000c1e05140d80710100b6081c2010340c003207000c0b09003182e40401214038084d510701080640d0701c400d419000040d6131180d1107081e820318010083c000c00300c164030090b00c20803e800c0320291201080e142e000300f100b107032141014011504142d070b1602e000e40d007080c2c00300703c50081c0704180b0440c07110b81120002000c6da180000c01c144c1e00180e404665540000c1c6100060342c84011070000c80d18400d190624a50a1181e0301805503541402591502c0021001a09007c2ca07950058203654101601007940c07500d009500903142d01395207a101961005210503940a000d01050030b0081d0303070300000b01c3c030f00e01c40ca4400151000002d16001d0b04a1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 319463210 1250 319461960 319461983
    0xc0d14010905030c0d030e15060603190906050a0b0f010e0405090f030711090c04060c12021e0309031605130506030a0c03060902090a05012108070f1a060d080f07 71
    0x14003d00160201ca2240b000910200c280750030003a041d100d90510826070340d881034801c6c0503036043d03220b1120b80140d005d5030000d680c2c0d222109201c07458010080b9400d0795a040046138420081350340d00040c0300d0709814000f040100b006c032040042e020101d603180b0740000c001c605c82c501140303482d40c09075811035002c0c0125021a4601204c40b03095400c00c14050301e40c00c013584125a0a403e10042207079025011202042c0f80509060000d8803c0c4440c3d607001c2c29451021466180e480e008112040780c014519901c2e840301c007003105059a44c3d07809204410701030300039520a6022074594080314802d13260018041008038001201c008010039005000e1a410b2007065000e0000c51640198200954040c110200f10321103140144085080080c04074040c0341e10f403600401c140c0f6081c0e1100b0207d49140100f0031004046c9080481e10390007102c6004d40720424016400040100100008041c60350076441095a56a480100074940039280c5000e85400c0c5e0411101411200e020024190144079042140d43c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 319464460 1250 319463210 319463213
    0x10c020913020a0602071703030610050c1614040e01050402060906030702120f0301031407061409010507080c06190504050a030e180f0105030c150702011b0f03030219020c0d140109 79
    0x41c3c00705611080158102901c180014260030400444441071000110b2a60030072402051080170004001010403401244c0301d070002034148540c451100701d549480c80b42030f403500c103201c1c015681500b034140700d140352814648004206000780c92146800410ba141008080d00503c0b035558001001501180109005456010260b0010b40044840148036949940c15071415200242506160840302d50002e0b204003c100e6105050741e0300164044041e40d12180d071140140ca990042440080964002041c02c4e1685c0c980010140e20071120410001d07120310794001d090341210010f5402070515080302c0d840303e01080c018cd110f481d054401810b0b4003d4080380c1c419220740b100042c0d518040802004004004901e02004007c2421108680348c50603800f451600c43c00e10b100b0010002e06000300c02041e10300c92018019101415500580d4500d031a0146d440c00900030740c48a210358569100e000c0d24012082d10000764496032000283c200a4541c1031510340240c1c40d40210070600c02036488411721030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 319465710 1250 319464460 319464469
    0x2030c13080102030406140f04080d0b090915060d201c050a02031c080a0c111005040210031404033006050307060c030503072703080904060f05010c02091302 69
    0x8014070400c000182c507424140340120035a903a2441e03e070f01d65500c5400317208058001b5100c13650880d501ca103901d95a0a81c0c060904090301444810f283d00c1129003003081404e9101283c0b0403560044440d8808041c4c0e502820000401c24a0401500072a1500b8a52407043c1c040304004a9074800100b080c07103410001c510044000c00c24100403151b503008103208200b1030804001e450100340542060300d101488050000301682c6008090002d9141c5075000001c4031070051180600c50014071064403014001506107401410066504a00074181120480f048a20910031035441c2d181c5582c110855888640701190b88a60303101600714807034031b004c040026921160680c40702d180d18541e07000c140680fa040803d41411225031045050014600301000081d40c0b000440e540702e041414020b4150f8100c034000d1030000a2009180ca48941c03a01002c424401c1240241c68440001c460601c81c19032144400e124101e81407107114082a003c40744080149011140359501400404014109944540014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 319466960 1250 319465710 319465747
    0xc020d020402030c1c060602030a050912030c060106020c090606070b1b041401020715022a06040b0301080f070302131a03010f02040305060c030f070509060d06060e040f0510050402030c 81
    0x4c10141000180b001010702c80d03a203140c151041000400c1162078030b0000c001e500d03407042d042107400b044000130344500030343d40e045955060f03052a00c00b142d40b1071512000b61981c44d0400e00901000d441129841e907518940309404a1181401500d40c50a0001550b51000c4007000030b045052001030f80c00300410200c40090141c03004041328038411201894103000681000880d8011000c2009006607030320710f29400140c2107262020b030001850704075000d0020f040304400c1d022a25030780030100040c0001e18540020180d410f841039801940c002c0e840d2202c007103942e04064480290400d030500540001848960711000d400500c0b21501210302c034880000a00315030b0b8040884940d245d01107814414040300304074003176100310130030340c803501d5410440300114983e08020000e004100c400201600541c8580741600c40c0f801062600380b1415489010181c54594100b94140c0180d1600e04410407442880c052a4094a00b024844030442d0901003440080e500061420320a49070070001d0350070404904a03e03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 319468210 1250 319466960 319466971
    0x140f010507030f060e010b090613120302011b0f09060809160f0f060908120d111206011101090305030a0c0203040803030702150124030b030f120705101103070c020d02040203 76
    0x203820f1a0621810b0102c6085410015246040000521140540c6001c560142c3c0b807c4a0058840d07101070b502e500500340d44d41061841c0180c1c16036501c01c15405401260f420310034003403880752501d0301c0303a411240b00d10300d01c0c0d00c1340002e000b5120400c00b20380203103c4035070408911810380d540816100039035141c111096024107940111035104004001c018480c0c0d00107000c26207401c0e540c4c140761800d215075807000b880207465929070002c1c0c91040f0b075009034000e0583c090a9420142c440301000c44400c8401c004a0394140814090b90120040303640c188580c031007040d8151a80360850b1244200d800045c4440801e031002c7d1702c010080420140300c00c01c05136104800b40d500501c881103417020914040311041c0c1c0250340b100010003186034109810f90f50003101c0350640c5400203000307604000007131420000001500c0d0307078040d80140c8064008040001d0540e6401001100c9078002e500710010103c2d01c00035400700000c0c20038008210000e2140d200c8482060009000601d0301c0b9850300018100e80c4290fa6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 319469460 1250 319468210 319468217
    0x16110a0b190309111c0b010801090804061107030c0806070809010b0a03030309020d0b09030307090b040b04050910091a19051807030f0c0c060b0f15070503121e090c0d140f010507 78
    0x100101b220264103036001d44146070090002c0704003580c422100c0d0107a40a050280085902c2c0002c0c041810400b0100458006412286842d61810102e40310b02d4180c509600060764040020841c250501603002d4241019020741c054503e1074074114014500002c00f2a030210200200001003108000391502580024003e0741d40e80c2041030003e001d1070309550021851040030b11042001d01c0e4404151411201d0a1300c0d9200b03e5902c01c000351210b0503c0760071100703105180220119541c07040043c2c0a25007a810350301c14944100c031007540320403900c4a00c14242c2c01440040490410402c0c0011b103038200c0c0c15414041035400143c8081400c1d10080c207407100000380c440f08544148441400359042c42076043c0d071203c2c4e41c1340c0710340049460900117034541c0c8142c41d000036503001004410011114041d4640b00d4040b0030f070030403031703103d02c03c1000790036004072808068000318a2007030011564031200040188529004051075a0780d201400d980c9400c84454000c4004407408081c2c02e02039640310700c44d1a40e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 319470710 1250 319469460 319469509
    0xb010e0f0d0f05160e0c03010e0a02090301090305040f09060f210b07081608070206010e19050406060512070807090b0f031504030206161b060216110a0b19030911 71
    0x3600d07020300000301d0b44418a0707245418140900c6e13103440c1044034107403192004045201e584450540d400303031003241041074141d03282c5140d80c0c00f45540000503109480c6581e00909146954450359000e85100b80125840f6440205040260301a030307800c559441d100c0d00c41d802e22454215120050310304821541d0901040300b410401204030301e05100d044800c0070b182032003052403d004100940e6014140154218842d1440210b100c0e008141007030307580d40034146406d2129140a01e03000002d000184100c0380640c0081544035141c80d00400c0300030a40c2d910100400c2002d141841c0c0344041c0010204454221001d4801e200c91a202071144402c0d981805c2c0280d60541032616000380303003030b40040c0301031068046124400b03041c550100a40000480e91008450385600c241040d0b0004d1080441084500403071500d10b83c20086c440681012444c4200d4501000300d90344c4d00690040e12401c031500040e04035402d04108058020b911001515000d0f0940000c40400b480c0815528150681c18250000803070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 319471960 1250 319470710 319470733
    0x110906131d07020d03090b130c17010f060503211806030702011a01091a030c04080d02070f240503040c0503070b1305121c12020f0712030b010e0f0d0f05 67
    0x400241d01d902c2902c5c034003040381649544a003e040742d000f82100e0b0b03402d0303200b00b03810b4280180310140401400c200340382004d140302402c54881c000d0140c03003d90198941440700029080c60040782003031007500309810b180c03e88001c151301030440d507104208480e4421002e1a11a0864a0b01e8000e140f1642c816000062403040580035000111000702c40e140c10480e64241c10b1266410350803000085860454a0b40d40741d440380c0d10307600345501035500b00c3c007081e20032840039203101a070001d00072040361302c0310301d01a0f441a03c07034046003034001049006c2c0c40604842100c100707120b031013540215030190061900041040d2501e0009050030b000782d10890016401041c070003405110490410000c150484d001602d444008d1001e607200c180764035a00e204001c08407400100a80624504144000e45400455680e002443d141c01c5030b8005400a9510084807078071b4041c0c2c14024070410b0080d3f0816168482c60343c0c820020810341d101c541142c25001401a5134030000204d82d440e803192a80d02c107101400000c02f42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 319473210 1250 319471960 319471963
    0xf05150c19080904050f0402060904090807060c0f1103030906070e0f090901020d0e0a02030a02010c1a0702070f0b161b0815090c0904080703030902040603141609110906131d0702 78
    0x45e0000f1502c840c6c000c28400144c2c3d942e0207d500d085001e0300d01081d100c050b410030f03414600030620090403031420500c4984203150b102c1e441001c0f125098950a9600000c1c0213255541e0100700c803012040e600c10b50210368400c1c02940c08281240c4020040070041c2c41050109408501c183c800038000d80d004100c80313107039410754040da05200300040001c041003046900001d42d0f42004100107414046164049028070904040b200d031302c50381a0b408101c45060506000359602914841c00202494480700804c0c076030310260403100050040180c08604c40d4283e11240128005a10440a054104038000514041c20b0106008010344210400b074203107010a5900e0805250004823840340d421801000002000c0e0001d55040c04c4d01031400240c1d000561000c50010041900058042008900600004000002c001c50304c6619200700c0c4403541d030b0350071903002076800d00b41052962200178081e03540c0390306000d8003805200e019034100c0220503950300e1031090304d89807500025200d03010300c50811821540 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 319474460 1250 319473210 319473221
    0x231e090301020a121b02150a0209100504030209070c050604030e0303040807081b150d0b0f120a05010f05070212031905041b0e06150702180903130f05150c19080904 72
    0x680c250340183c1740c030340310303070300940740c511140100307841510840114082000c2981583e40342c080182107105452400b05018100e0b81140c44128400c1c142200020030340341c4100f07a078580e81c0380c0c4140208182e0b06c071603606403110f0001b0080b20b82c261105000006181004001d0280140308a0004e00a48040103841e882c4078910402541e000300701244401c00700540c007604481c503542140000144000ea100c0004605030303240403409922400c201c9444454001c04075002156a1084000300240484003411005407a002c48a000260f085110441e52010b1400010b42c3c1c04410415008070080101386444111001a038003517507081e030051503181c80c02d04058011006044240b550b90664989440020f940801c0218032410f100b01c00300c1c01c50215240e02c8042013000f000e60903018101e25115680d1170b82c80d00a000d420380ca80c141081c00041d440c0781e00030380c2000c0e1480503020014044088200c10b1240c0c0c81a0a400000d2284035100c04c41810940b8032040030174801d03002c450f83c0c1c071507020421040c0c58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 319475710 1250 319474460 319474481
    0x3020f0402040311090c04031a06011e020601140d170307020d02030f04121103010603080c070603020f0f070c1a27010c060b04060317040501231e090301020a12 70
    0x184100b1062012078001c800325004500101c541c00ca09070b940f80300340c010902883d031004050003809030100300c88116481c0050304c208002c0e43d41d0101461142826084c000b0071b6002c01e40540c110b5001406144200c884650b24841c010b44141e87c461801c0d034642c208480240602580ca81c004003d2061043d410301101031034645030300c002c41c01c0003501c9007050f001f40305038403941c0360100202c2070036010400420243d1481d008010700810410303a0700d0a02116942c400980105079009541002c107105001c2d00c2596420b6180414080c141040b0020030000d55010070816a05025007000000d80241400300e103200350800349400984814103000040c814402144803110038118480342b0500b44e99000505600b0260000004110b50740030002250080a41e03410140a1030900b242a0103c42c007160001c108544007070b80c50480c424161070103458113583d40c2103c0c1806800401510000c2e03c0d0340350b21070318950b201c03451052511b144c140000e0b08903404501c0f4580880c010300020f0742051401d105594054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 319476960 1250 319475710 319475719
    0xa09090b010302120901062c060d020409150f06080102040303050d090618030c03180305100504081903230112080903101a0f1f050c030f13031b141017070903020f 71
    0x41041108500b40c7d0207002744100d000b843c0d404003000a540d40c82d084211020307001031070062000801c4e0820130150183c90400c10710a424031000044042c014801c81d022260140e65190038804802558800351a81c0001514426220f0070f0203102440a9031010f11054400d0300c1e042c150164514010703045039891a80c00042e0000440104045070001c52103407081c00e50250005083c0d9168075081245004010240441142030100c010b48190503600500c019052400124002d549060100207015024003600611181055426000a02200241c02100001020389000b5112014100c003140c080800070a600c8406245804c0c0321304102c548440320070350594043d03201a008800c5a10106280480175040100003c3c44c03104000f018000d48400c1c403564503101303640e110500e1140407107020500094034102900012a0690108018150b0481d42c2c0b501c202c0405078403450402803400c402c400141e003880340303011420301d440b021040c407688119003548611101c1c07411130060084038004500914042c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 319478210 1250 319476960 319477019
    0x807050654390616031106091f060501020307030f050f0703120b030a02030c060702010c0b09030a02060106020309010f0e041e06081e071406190f140a09090b01030212090106 76
    0x40b0f49070b040440b400168550030b080c2d186280c0f464100c848500380085152079000301c0e018130180c0701022038030120319034159000502c00710070380c40403074220750fa54070404d40543e00c10885c0c180024000c800012035051203092140c2448810003403040c040d44610380440006000d030709218000b807028484e07290300f024140d009001c141c0103903010070341e14101501c00720710603100444c1c1e20003160700c100c2c6411960750b802940b1004c07504100d44840d94981080d0104c038058000c003000810140d20000076261001c4c1c05a6138040b40315110310058070303202808502e041d08640c44030840707043c18041d02c00c4a4034800303441c900010040e01e40346101d81421410300f14540c1c48007181c50b03000c0c0000000a003c42c15560b0300200411200b91140028480b0b2040b03103012100d869a141440305102e42103058684540c1d6103460b0525058061a140d003c144160311041c0040745181d1400c0c0140656a840101d080c0c1c0181001454100141510440e1410845800c01260b445640c1403048980300950228402d0315084003070744 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 319479460 1250 319478210 319478323
    0x3040f082a0d1103010f090803090114090309040207110405090d03060617040206090a08100c020d0f02030d051902040b18090c1b01090807050654 64
    0x381d103541d0b00005007407000c001c40d0b07001c1c0e83c0d07400b035200846c2d88101040c20400054585000c0d00380d07400488040025500c0c16104070f041000b050140d9200300b103890099031612024401f000000d4000100503907500c0441540c1c01d000361039074403d071030240400c01c00410102240700d43c0102525001d80000c0200b204240701c0c9088098200c0d092500139038110b0f1515110300056003c581640550340c895203485c415030514804102d05036121811141c2e066003502d183e4a800042a101c1651500107040107920400620202000d150f1081c2c1d001804a640c513150010042c200c0c900380d0f0015004aa100880000c1d00c12404481a48506451409603111402882c4c4486070010300d01460b82c06a964241c1d84072002c83e19113080d8003820f5169071180b4000e41342e24850030125541c401c00c84e21480c6d0401400e507084050030303c0d6551180d107140e41080000e0100c8895030303c0c4150010449240c84e5150183c4c186100040d810300c100302000301200c0003100c18038200b403150204c1100d100748181480200c21040355 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 319480710 1250 319479460 319479469
    0x1302030d03060b1b0c03030418050f0417160203070602011401091112070903170a0e040509061f030605040809030607091a0f09040c051b03090a03031103040f082a 71
    0x34002c07043c0c00e00c0030200d08884101c4c03d043c14809840103038507001c0040c0224510f89c0d110b6885488020310507080100e40e895012024044806a4010744014005655a44000c1060000b819003800311b41449a100d0b0703050b0302081c0323099015080440076075114440000f00082c0c0711030141c01002c003d28103000362100d440d901c801c680b15a50f000000d51384030b10000380a05000d4605c1d00c00a65120b0008009450304000c01c04082c0c2001c0d001d0360000388501840c02844c41c1078000c3e0303401840840094025501ca02c110010a81c04103041202200c090610010120380a071103030500c01d41c00381d01e019940d201680c0425042460052015052205030001403142c204c84620081aa10015014940d00c1040c100ca6500601412a1055010f410a00560031035988400604a841b00c0c201b804055215001803403601d9005442d02c55070489510700c001c001003803180c50181460011107090380d103030544801c04200000c85d56080074031280e01000e50240c0603140a8007000e040302d0303420094007207143d1003400074 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 319481960 1250 319480710 319480717
    0x100902060a050a211b02010218040f0f021911070308041a04180c0906091809020612010314070e16080402060903100b0f030102090d0b100e1302030d03060b 68
    0xc1c42000380118418804902502d80005401140c2e0103400d40040c0407019400074105280265481c80303000007000300c0359130050081d1103881c42a00e18000341380c460380c02400018407004101811182e00e91080e22200541ca100401b5182c2c51001d5442201900101c05440d122002120f10711310707448441c007000403078400016102a581504120b24000e076a034542c1583c0c40c056604865103c2003100100f03151124240e022040e1030407103440e0a01550b40e60b132030a550b50311084c401c500868190440c00390045d42564041041d880c4020081e90070f1100011820b8503424090300300320346040070001c440004400410100e00281103c002d400d55070b2030581d5055900a00380f840318800d03c61143c01003001c5640303a105031000041c026040781c0025940c00d10040140c6044108980070f02200d02d07120005040600840d10107107400b9206241e10840f03030b510507008440040c015607a140010202203034807040104800d02908182001252507045801014140b0b4601d101450a251a180040080c0194103080c4c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 319483210 1250 319481960 319481977
    0x915040f090204144c0309050c030c0609060c0a140708010b09040c06030b0a0e07022808070807060618020306010806030622030306031203020a090806042d060e06060310090206 77
    0xd174100c10000e0740c41e01c020304607071101d44610664141200b0003042e6050f0b20112413a80900119151010070f80b0900d13480700400304901c1d801a04c01c001e082d4060910b00000e081070300c1d620701260304030342c102d40720b045d12850032801da4100d80c0c0000500300300040d424010719a01c03001c100c4245026050a946500021416115481c141030b2119201d440700d03615a6080c5000b080550440d00a1b0f15184078020b4841c0031a903809840b1401d05000064000c02100140c009107500c54803451030185036484d4101544c201060031101540c44190118500310104850041c50006481c05a201d00b4540005003000b60014543c0d4000c1d4000401c001c1203810702c1d25200b05600700083c819a140c1102d0030200c025000c1500007400000300700311031a0301103034954000c040c80d4000c3d135651442c081e02d41c0c020a89a6a06039409030102d004103801440030017091000000c40c410807104a84210ba9031740d42c510580c1c400c856800f0654000e001040b5542c1405d10008114040502d410003000302070b6800a900c034090500c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 319484460 1250 319483210 319483279
    0x10031107060507110a0c1505070203120f0c010218040b0d020d0b070509040212090c030303010617071119211202090d0b01030506010810020f0915040f09020414 70
    0x3160005010342c8040c0c0420201c50300750b4805c6a0b040c1091014400d0718819400d0315200c2c000301c02603d6108078180c1c0c000560040151980044d02042c501c4180c10100071803818102c01c004d25000d08a01348000c4c07442e00520680c8515151401c400c0104443c4800f40c9170780100180207070031006036160741801402c0780d0310120703d0b905600c404d08201c50500500c1c5126802c035100244090100540e40c400320f00c80c1036402e040351142580e40e000d143e2030340020b10401000c01c1a13800f1307404600c00e40d80714030b0f60b00c00c10700e140884546042200c410726107010414040104103454a00d001130140140f140d44140600408280090240340402468290690b4200b40c0c000e501013221507241d9500d141518909400185a17511035850b82002622107a003131050310b15a00c01c5420010b21440c0340d0003075480b00307040c00c00c5460a0401417824480c4d01c080b074805a85a1040c10000442c2d090002c6440c640a844e611400684860401e441d140c0540c000d00340a502c241c8452030340d200309058202c5003010141c07215a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 319485710 1250 319484460 319484471
    0xf03030a0c110f1f03061a030613090506070e0f090408031006090b09060d020903060f09011404021f030f05180f01060302090408130302060406030b0414070801061125051003110706 79
    0x500305d0080c03001390484c0f90038003d070700c03440c658045101014501405007129800c0300c511413010560100c40d50048024010380200c800641c45500510381c0c4c04490790080c0810300000c0265000a8680e0b5003242c044481d41008424007140580f0303040020007400481c14402e0415041900c2206a0301130f4190081c4a142d00050004e070007542070301544d2100c3e00143c00c9502504000e0310402c2c0c251802c851104840d8a40312603072040e440300d46281c50044e6000b521110b01c805110a00c0541c80540c1c20905d4203241c4c66008e1b040c1071300400d10400380300b2101c20802e0720f0544115855513040c03802444451b046070381000414030241c0c0c2e03074030446034000764005842c45d42da0390951aa420214a60740c1302940c000004100001d40c65019003000461040c2201d0070030180407804502141c0200c16104071000918000061104900500004a0144902c2d040303446541c0d42441c500a0081840032112804400400410072403d265252206176600c60400313202c0c114061031400400c0c0560f04001d0f200c940c803139 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 319486960 1250 319485710 319485769
    0x807021c050d180812160e060703030c051315020c09041e03020712030201020d0506040c080a15030b010b09150a081f050405041109100503100b0f03030a0c110f 70
    0x2124480481030703100c1c080321780320503007114650030600c42180c00e20550b43c02e1180f203c0101d40305103495000d05400a00a0b410442544c030120002c03c03000000340c003423000400c40341c11110725203928503004107100c1000844c4901c0315880203091140d4041c80a00601c821030900000071407581d120040315229200040714000749050403442c2c0280c60b0700c140030700d2035803003500c50605506400508800e22402d806101c183c4800d0706200881d4441218013000403034040124038523810941041503d0b50b005031003410711076100c0d180c1da901c00300281e004602d00040018a0395080c280b80140c1c0a41561425009040601480003e007010100800d40c0d5800f46a18a80000c2421250b8482024140240c03003044986854a0951b004240071140d40b032040310020002065003022180040a03035101030060807551514210002c0581a1600a250f02c003041c003648050a0b10204041c1141440a9444102c9c50909061900404481d0406607001c0c1c0000001042640c803501050307001034103103510307141c11503015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 319488210 1250 319486960 319486991
    0x313110402120f040c0f08100605010c081c0b06120a0b01050301030c030b100f140f0a05100e06070218070e0f010503190605030f01090b060604030b0103080a020f0d0807021c050d 78
    0x1960003002e04000ba000300820380847c001140790444081c1a0308000039510b49005544084504000511102c001c0142980321442450120003913060b40c6000304148103941c4c006405504144102d01c0c01900b403104010340b00e10b2a00894101e00001c0c00e00701d245505649030211291050300010300640d5000020510030501c54507400c0040010f00305401034541c030b4010600540012006c000d1180c048224514045d1510102950440b440105032841d101001c00d000e54a01c02c81e1008554012004d02004000d40c80329104070900700c1900031504100d15100b0006400c500c4404030960041c00102080c1551780d80100c01c49401041040110240c0383c2e0800202c0003901042e0082c5406000701c0108404500054103d461440d128130310f419a9035a40c18240f0009000300d20004d424041420010008035216000034921200180b06480c1286045041286020311018000c0001400001004040790f4180081c21121710fa0189030100480c030358500074074078050403800b544829a200d0003420031422 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 319489460 1250 319488210 319488233
    0x2090c070602040e06030c0a0602060105040f09020904080a1101090f080c011503050601061101020c0c041119050d0608010507020616020a1a0f01120804061803080313110402120f04 79
    0x188071000355619500c880041d904154152040c90007441500807803030f01840e001c1c4015080c0c0c0e00c20f80c02090076a103071408010280803c003440002950392009418090303120000c090b072156002d45200b81e0340f46074412000304490310640e188030045c3d14004a25000030f81c00c011600130180c10600301c80e229035810500b21300400d002d0700422044400c5080000400c40702150041c1261780d15140c03240c2803c3c442c22a42d091744038080703c0062a8110b88409a201e2a0591002d0300c8401c4001d503140c104005405000d6020100130008404190702181400340111030707001d44409001068000d02903410180c0b0040c2d41e4060150021841c402100c041d0035155208102d10780d0040c3d005402e51074100700611404c54030842c1a90180078445540c000440e010f0381742c0d42035040b00369000b04007a1505143c444210b0341904c003022080080c0d03200c20b4000000c0341215010b10301a907003043c400c0c40d115445103807241c0d91407007201c0320034042c0d80107020115a081c055122140e2040c440190a2065526446c10402401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 319490710 1250 319489460 319489463
    0x30c0909090515060102031312062301090f020403050d030506120111070507050a0303020d111e0f0124051201060b070b0a0c08042a0305030406030b1c0c0302090c07 72
    0x600d001281401d000000600300180700fa0360003070070460b44515004907201c0c0b00380c095081001418400c00c10005810005501d4014000c5000040c1c6030300f48441280440c0c10010805440c54414005001141c0c19100e4901c2e5041d81e90070452605285907240c80d00e8a505441407010316a81d100014500d4a49c1400031450715200c4008004010308010455140d8001d2038003500c45200d145000300b02810200e80c104241c0e034054004105808515004440300c0004030b14059090260816401070086c0d103441810070310501d50b000d804c503211038081450840d44807030100c454005100d0841c0304031840c10360101091300c1e003d0b03030800045602c6500307041c090400e41e0700034004401c00203417242c24410b0800e0130701e00541c034a9000340481c08544e001216410b2090303134050b1800a075292001c5110503410600218400c0070502100780c16542d48a840c00c6070800d51140010035101c44103980e01b40ba001d141000015002c500c0c0703900305425912655010000c0c0e0100a003c0c020b00000716241d90f030300c0010b459409 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 319491960 1250 319490710 319490729
    0x90e1f0e01121511071b0e040c240905010e12031209120a02120903011410090b01021605090601021603050c04230a150b0f04080c06070302070501030c09 67
    0x3965548141c1c0c01c4081a990156800c15404116420281c0c0d640119101c403903481a150b810004141c03115204a82002003c101091b0403c8001412101e80f40c0c100d84160b010300110b840385483c1c0806401e00411410800c081d42140b801c422100c2c640214030380c8183d0f070003843c012041c110311001054100607030310300c500e001b44408035000603042c0c01400417611031086901034486003111010b83c00d81c00c3c09040140c0e005600b106690447c1608071102a25040c20003e001051901c82e4902c1e1f00381d520700030b0741e5095401d032200d81c045c081010103010b6451120b034207100030861300b02c418a4200901200d8024140b0602a12001c141c030303607200f00301607400b01001e46800d0036955580d01c0c140c1e56805240c11240d000c0e0b03045c60854044072110144034011100ba0444001c2182d0300c3c0d40712017001780304c0c00042e00036003040d13010007003490007106000d0200c1060350310040d5595070a04400318a00242a848a4461134040114000199021030140e04a802c01c0c240401c4d0068620001c5d104c2294581111005c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 319493210 1250 319491960 319491989
    0x90a09060e0709060c0312020f1605011a01020c01090b0304080909130203060c0304150c02030d09050c0906100c38270703150e0f0a1101090e1f 63
    0x1101c1200702400d02a2003140c9581446903a582c0c4255852068080f0280108040741c1401200c460b940d00140850303200ca20a40c0d180c0380000f480c03039a00054120060b941a07555014007030030030f0762025001c41403a0090000308488046500000d02c41d49403409101c81000000c00410100305080050703442d4400000c2c00201c20346410b058039941400f040e14180e12910460f4049512142a0b0040341d0040e41c00c14081c1e881203022048100c0507040c0c0a40d10002c505c810040003003800c541d4840d240c900c6106001030a039038040f840800c00c5d46c6138040c10a620034000e845203e0041500403124803046540325a0707031040095104c0507055424803624525040f03040c08a0501030050b802c1c40590303c5110329840000d100e0b0220003800c042e240d12140426100d6000d07440130b001064500002d001c0b078030850f02c404500e0440b04450141064002107540d00720b540000150340800114896210390700307000303182c842d03806494480903105c03802003d0061022107918001d041c074070050040d8030002500d20501003551 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 319494460 1250 319493210 319493219
    0x405060405040f0f3306090306020901021f1d0705030d180b0406050705010e015010060c03090909030c060507080a0c1b0201080c1204050d081602070b090a0906 70
    0x6071120354170005442c45c01780d100700041001100a082074070303201d42c0c90050079400c4d644c42c2c00c02580010903980c1940f0803e9081010020300c050340c80c00b4500da6190100349c90203a103140080d150400c0c0741818140d00040802d003c00d03140080c903101c042d642841c158511286446640fa0002c2c0319400480a80d000010040b550640020060000b107104000030003004814802d114222070317080c071218002800050300c03107400310070b00755002c503039000c100300301c3c0d01c400c000000c0c041070010007140340400089004040104103c2c001076100000c00c00380c2003500000d021035030020581e03031080c0100c10002c2c2d618052407052520840c02000c032940c1c0f000c0e0070007181c00c00800140c25650200c03030301c004190415035610851841010351813444101d0041d101a01030b26030f8019589160300a10391000e0010510080b8080c9959401e50b50040307000d10054290f521410200404031200103250440c031481080484100541c0050100111811592420707241d501c00d1002030301032543c1da4405503a19081040116 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 319495710 1250 319494460 319494491
    0x18010c0506130f0f11090906100e07020f010f0e0d05160b0c07080d0905010b100207031509020a030605040314040b1812010e070f0509040c0b030702031201030b0f0c0405060405040f0f 80
    0x5210328221802003086c1d59521f00c2a41d03a4108075144214114040c20402905600d0702030030b5001201c50041d102207591104c1e00908445051080c1903c054562090084160080c44110410701c002d280880c80c00c010010006400c0b005144000c103074030100000540f500c68401c0c140c8044a501803501e031360320510031001c1405404602c400755000d5182c101c01400a140104130150303600525005002002d02c1d51700c1d842441848213200290064031444800d005035649892140614494100003800307050609005242001c6255040f014003070801c0280306c3c1c400d030071040e41c00380d00031002039003400229180410050b000300819040950b09040e00c240d029030f4081120f00581c0ca05242c12130070b00f41e5940030031142c6801170b035014024602d19903081c0b0100800e10010342d4007035842d00450f4a044000940d0000300c0100b42e00a94115280f0014420302c000d00d080700d181c1025449202d03900b400d00703100c0042c22922541c89014407841da5407008900c604d04542252450071a6108100406001e40f0b000a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 319496960 1250 319495710 319495733
    0x16031701030311150105100804111c0b010e01032d02220e010203221106070803010e13080306100306030501020409050106180602060c07031806030218010c0506130f0f 73
    0x415500414004d500c0d095441e001440c12528010710703c464031203680109462422028005a0b52103541c3c401542070758a4540c418508045000d00c285181d07480e50038005034034007060300314a4459125000405c00b0640340700050007620201620301b03924a103519042c084600c0100c0000f0740203044400d0b07132542c00070250030604840d90150300a01a154130200703034600f00d110454002c0205001080c840075003000558411035201c0c440d42d403036005180300c540050840c0d04800d0048030300708000001130010311440c0b401103170804030007129021869140e9030780c0c60444c007000344410b015114901d0310700b41a034482d411580055402c84d000b11350f155101c1c46198081c0109005035008100960061b04000c48144050701c100c4116a016200036180e040c5507a00756032200d10254100b10068004580e00c0b050600c1c0b4900034030b00b42e200140d440074a003039194203002101d60344e01d051200c4207071040c0c041600401e800b41d11410560707030005000e505142a1400c8604080090916038981d4a450200400f90000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 319498210 1250 319496960 319496987
    0xe01050705041404020405060412030504080a08030103030e0303131a0d060b0d050c130e06040f05150a060302040602060109052814061518060d0e0a02190605160317010303 75
    0x1008543c5a65030030f101c1a80700301c0c46001c1d001541000300300f002290058040641078428640145040d0391480142e241000300c00341510a0040040108100f5400055034882c18500784c011714100359001e640440075801c14400c001c1c502c4801d1035244882c1035030a0031030346000d494185c10081c81351642c0f45640d0301d03044402c50714202031801011030304a8104106a98042d070442810541950401c0b81001a61030080c0c5040d800c143c95030300e64880e681c801e0050920404007001c00b4070a0541c1c12003040020000fa80c00102818810001448034039804541c2505591a520001ca0b1545662030044160001031407140b040203000c4524003c1000c040e006100c2d14000c00381c02a0f2191034041c10005c020450311000c0765140f030204400b50b07070040d00300d201041d2010002e0000d800d04242e4202142982d0200010101c25000220000300310320300000c000b44524490b068825006003080f00181103403050002d005801e042e204440702c10103202d024280042c0c4480030940c10196034038940a01740d4070701c5403007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 319499460 1250 319498210 319498229
    0x609090c03050c0703030c02070306051f2c0c0403141e031201091a10090503120c0d0c0606080d0f02010c02010c2304080307050313060c0b01060302030a0e0105070504 73
    0xc0a18140e0321900400707000b42d032180f00c2e0910f0f15800d80d6040d0014280b85000e00154098004000045403080c40754521807004410341d8104e003680c4030502100480c0030303009036401c02c10a00ca01c0c02450300031412a1025200e9488143d4181ca40ea0002581401254001002c03001882c0800300ca10700045552038000d400000c11000340308800410395181d001d565a5002400f48500042010302c103181c00c621902c1010710100317028510306802080d0843ea2017072440b80480c1d0b08010806c8141010042c960441c9200c45040e4140b1042807006a240c8404c01602030401c180e040071641400b400e0390180c00286100400c60703032100301200c00540b004070300400c41c0380513501c1c02d12407004a2340103000c0c0c4907040c0744a40d0307007542041902100e410039010641200384001424400416624004c1004082c030b0f5003d41c0c01103403680e603500146e00440d049900448100049449014000f0b4501140395040d0744403424091317100e540d03503902200103003e1401c80000710340c2084d040c0038034960480c000300240c520100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 319500710 1250 319499460 319499471
    0xf0e031312030f030b010c0611090117060907051b0303070215060d0b010e150402030108010b0a05030a1703072607081b03040f03050f0d0f1802130b01020f07060909 72
    0x100c440410040e50040680407560038480f2010203071003a84200d240b0201410000c1407200192111800c5600054441801c00c500095900715980c00110781c0f00078065941d603940305490500d0101d00c00c240c01419580920001140566400401c07603030340c9001c14001b9044988034035250200958503940d00c040c0d2014164030001190580c01e001c0761076010f00b6041082039141da441c0034003950f081c40c2c004214010328402c404000702990340d035000660080078a20004901c0b05403803000c200c2289543d078802407082e40981030b0358000410340e074544000840d4a04d18141c03250354252040d2141018524421002d015104458184078002d8111038007900c1e807951000303140c2d40e80d200c0c0100c1c501c1c0c862440e802072560070320000b0000381d003d600c03480c4054403c2c60301030b050001700761940c14941c0003146d0948035940c542d121064a14100e2048400380c140c008011105544c6a40105030866003512030300420644800490300664004c002074101e42c0740003800c4075807440e641c02004190281a0007200202420113 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 319501960 1250 319500710 319500719
    0x15170601030b0121020d020303090a091d033a060909120504080705120f01050123030a0305120a150b0a020c0f092802030709050306060907210f0e0313 66
    0xa61242c40c81c00c1c01d568544010134103503003c00031140c5025008991601c010000306280742c4074180c00030001d0104100100311303485010104034442490400c1c0e0f00c160362083c04580d1521025140c100b410819840c0c6086800d031401d0a41c0502c410701d2400070480908101c0000740322515a840700c00418000d42001e8140c5040920840d50342c410380c41550b12a0744072035002e11842c60402c00c8074a40b48401802c94442d9518102c8050a4403801d9202800716640300a1181d0080c3d4200c405501d0b480c401c40150558441c542e40241807130140000e60003a40c00c00d00c0c001101c083e01c69020301c10179455078031804607003a42d40000c0121540503990b0107005004404000149041808114040c0c4000800c2120560380c0c860340c003201102c0318150610f0182c0904903004e0040340f00d200460241036281d94100c016070804040c1442e00382e0107010030b4040c00512041001080d4030089007aa420700c04120b040c148000340602c0c4d030180070407800c0984141c0c030780050784184160000090480010082424560507641d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 319503210 1250 319501960 319501979
    0x10f1112060a0302030c10031b320d050601020a0203011a01090b09090705030727090c0203130308091914030105060105190c0c080a030906081006050d15170601030b01 73
    0x8500c0003e40603800f20701d41e0ba04919051f941a88413104a15000548074140b00d03011807046000c40b210004900803801440300d240b00056100014500e902d2203000341310400c6000940b5124001041c0c00f41131707580011803220381c0f081c400d404240d50001c009205540709046010b40560f814800e10380403070885100010b490362030809407000d10900401d100030f00e5591076010340309030784000d0000c0301f04180704884648060001c00060211445429440700442c2007040d100c040b24411021401954403d00622000e0300041e01c0c06d409490740407036203075100d0b41040e001c1a5078149030300011303402440c0c880021644080c0000b081a83d50310440081c4103944a12005481c544943c13418002808640540115624001d0006d1000030b44502105502542e441c181d05080030340d1080700301c0015242501c1008101d0340310403205d420100b01c44141001601d0300d00c0c00380c4544105040140c07425200c1c00098444000440102c0c002e04031107030baa240460040c2c40303568458009000440303040c3d2002e800400d110700c0c07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 319504460 1250 319503210 319503229
    0x1204032d1209060608060403020f010f0e0606360603070e0c071b03080304050115300804050402030103030903060f0b010926030a1d030309030a0b09010f111206 70
    0x1194440800301c003111030808015090309041030341c0031034030781c070000400354000c001c501e1281d806a03003d03006802c0d407141c00305e003034440404849220903304080903e101101152058224000301c41204001d00102088140c0504c0e041c003071710f05240e10808120a80000403010b91003000c088040c1c94171551a08002c00384010103440218082900340210000511084030303040076010b058030000c05050380c070b03a0f0300c0c203165208990464659449108080041c156407040c007000d809092140101c6102c03000f10a00c4500c22013072a074039850348407034200c001e000301e02c2d044074081e181c05441035543c0e68580c10007400940862004444062802c480c000d002d000030320071441c00250594078900c415280c01c0d40b038414034821007546084038040740c0759003001141c100010801040551140032540c1d002030034061134850203500323060280d04108002c103403d94010401982d071a03071050800d02c0c02d40319400003d00505404400d1307038480c0d141148800601c007041000e40011082c1d0010390361642d0f207040030f01c00c1514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 319505710 1250 319504460 319504547
    0xc090106030b210304061d040513030809281109010308040e0a0c0819230a0e12090d051513140f070302060315060f040302011b0b041205120403 63
    0x410031700013800a9403152021071108141c07064040064952400040c1c2224801d036684038540074450303506002c03d0380090503031340c0c8080b92001419000146500010398404107050f1185084244a40c607400c000c0b482c00d0701c40b02d26401078280052581c5a01c0e00c1e1105500c00e0046c8583c0041807000545030701c015016117000e2194540d101c00301078039a6128213050080e4605041e00e1944c4038040d080803420034041c20800c01007030503410482c0741010102d0804840702c0944211440c0c00c038808494004042d0412030b10b01e68426030303145640c40c40a0528500b8648012441541e120751841480381d96903880f000400054007501180501c1d00508035a5035441c0c4640e0352010041d00404020005494803030042c6074400c81c0e0140000450b40e14200051036036000d01641000b103940850140f05550340308080e2a44da40c2a00c803208039505030f41e111200000002000100340b264881010141d15100d038050361502010416004141c0c2498a006030003e5801032114011071507808918150007881e286110845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 319506960 1250 319505710 319505713
    0xb0405010b0907140307111005010501030c050c0718060806070c05280609140a031101050f041e03050409020d02070512090d0803090703050313090501090b0f120c090106030b21 77
    0x195910041080641000b011842405012803036031f03403e8031080c00882102c02c014440000c4540c1440c2c005011240382002e0720003000410310801031131030700000708501907030312040e01d00c1c1c01c50240070000e201419490b001307403106014100c244881290003907640b285443c45003080d551030181d80c044d503800006509001a034030402e4803d0b800c000c180a9444090b4090003844076801542103520f0786450a500c800044000a070148010900c26100703208040e003007910300341700d804681019120408801e95652451081e40080a010002c050184040305d00401081d8402c0d9141c0c6142400e05000390003040055986014950321080022204021a0010000100088078503491621520b60580000384000030900c256040030000c12810406082c4e020305403c2d07000009800c18880700d0035200113030b0090007264209031041d01284d840c21800809244140c1741c2d20103103681c10381d20f10b00e05224036040c10307000010380d00003240701985038000d4076101d0700580c1c100303a034041e02485e0406820b170031040368080ba = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 319508210 1250 319506960 319506977
    0x12090109120f0915051b0c0f13061d0118140c0a0c05120c07080705030c09060f040911031b0a0e250801150e03070504020a050c0304030b0405010b0907 66
    0x919000305810b002580462601440d0030381c0301c40c5650b40040c609107504000c03450115500c404210300d0054400002c4504015002c03501507030010400d020011540c262084c007260104410514440c0d000d8002031600840341001403059841040d01c0078428040c0c020240340307442e95402400000c0c0607100c01c14440f03101d02d114070f46c0c410b42c80e524140c1101c4150700c10415613421880210307800b00107414040721081607003917a0b0125404c1544c0f9043e500e80c030048085d0441e0381e0810440d0785c00300e0031380345600d0141d40c03041d1f059aa0b00005034451840d540d01c90351051814106e90140304541410f4000300c80113500b01c42c4a09510b102440403c510301c13041e41c1d40049240340512050301512000b40e0040540c0c002c2e43e501d80b03210000710700c04c0641c0e14566400104000010000404e9040101140030f21a0910205180031540884c4e1540c0590060074022a0000303841c00c0d0683c86a01229503880682042e00c1c0c6903034803032410f808150001c2d40c09858079800e105003030440c4c1c80c11034000d50240e07030580c0b220141c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 319509460 1250 319508210 319508243
    0x20607082406040e0601030e0703120c08190c020a06020c0901090f0209060a0201090317010312030e0c150d060e0f1816030f1203020f0f0d0902060403050312090109 72
    0x8a4101c52600d00c406422000d41c81d403815252600608064030700c075280f6040c5803803d40001001c42c0d16549a8814030760100c1c8003040444d82c0007104240384004c41c50900a5002d644c10096290b115084070b6085e100b41c40b4402401040c3e110100d030403446d108039060300b407c2c1e94a800803640c90b2080c0d46a05c0d1300406500c01000455241d41c48403c161203da5401741c180482000050f001c0d822031034040e00580d4484a110040550240700070b0714034610410005107950440d2166501c440184031004281540d070040c504407481c0410100500030300051032409034604040781d100e4a81c0040100e00b070b1413800c200703001c61030300d00103090107114200c00d480d000b244d90754030308070300e030714591718040010080c061001107410711403d02c900d2001a40c003402110034007205a1400a520040780714815041520500c0101155001d0000f1075005011444000e52079030351501c0380c0c40080050b543c0081d4002c0340003a0000c1082000b10140400c0c0410311020031843d0350304c2c55a0303400c0c1ca20901000b032006010010105 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 319510710 1250 319509460 319509481
    0x150507020c06250812091b0d0203070f081e01020414060d061d070e01031104060c0809060c0c090a02071104020a030f0e0337080c07051504030f02060708 67
    0x2a00340d8580d002044203400d43e261603141c010002c24291684200004c1e618040c0003c1c0385244d40186048008001101540a50240c005032103c10f051041e480c00d44c580040d550100459805017074072054001203503646040003517949041c2c2214103010402c00f881344600c51818400e8504807452034512400e01046c080420506512013140c10074403a68a0308042203002c00c3c640c51009005e85400c8a10711403c007540e01504810040100c1c82c1058140400075502c18040c006a030b044a40c10306103104001f00619002da843d00851182980218001c20654408a000034010304641c900f614108010780312505c582050380f15800d0041c03c05c107100b5907113640c60700309540281000400d5140000f0b51558150700501910702ca80e030382410a41c008561214807003503031000050580a001c484040c1c00c42100a4006a034510701108010f001c01c1c0d100160800e848482183d041a43c0301013070740c01c040040c144101540c40c060b02c065001071901c0d1007080d00140001043e5010b03098944420035103550300308801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 319511960 1250 319510710 319510717
    0x403050c07150c060501080102130b0a020a05150f090d0f051b1905010b010504120206030603121308062d0601030f0606031d030913021809070507150507020c06 70
    0x80d100340303030000030103016401014102c000680d8440c9603040150809600b90354040e00b2101d4039900c1048101c2c4c5a0350706075805011600e103409019145c8007002801da044c0071980c903001e0510700818400d0107421050841f41842020a103000c800d181e1104c4141070741d11808000a40b0204d074003485105041c9005002420468400b800c2c502e40d00101814482c1c1482d1710305000600c0440d410031007104114080c06000780e0792200b86041030a041c0f52803072030300b0f0701d20002c01d019000d11000000705000352000c2c000c8540c80101d07600e01c282d841d452200914050070346842200f8440c042d0700e0106501d2014150620000381c0d07080d817003804210814203624025030700601014145562250060601c0c8000c0c01008010b2102c0c0c0c071300203a502011040741004d4108400d0442040d0400c003c80140c90f0ba610702070142c80f02880c42c0c01611441d8595031000c4041c22007200980c408803540801c00150703403100003031918605c10004468050041200782040d2036098174100d004d80c200240150a50400b04080c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 319513210 1250 319511960 319511977
    0xa0e0103060801540c1203021005010b030c041406040504051015140d2d0c020106050a03050d0807140d05010501032a0c060213090203010303110703080d230a0203090c0301050f040305 80
    0x103445d9450354640c4010070106444000f00d016030002d51381e100520030144100f6005101140c1d0312440c528040302c4401c0b80707204030702885007034025100c0050440d80320301080d02c001d414040c0c020001400c003407000c0300021140d0300c10030040203402082d40c0240740c880c00e04410380f4800d80d826941410760054040020340000003a240040a83c002d04c0485010a43e40701e13002030769000c1001a01e0684c9440090075030b015034024500030007504108200207040060301c1c40d4543e403d1300d080d03c2a62101001142c40032200c01c02c02c0941e182c0880c4500200b04903500250403031740241c80821604040c141145030b00040078a013075000514501580c1c0c0010b0140030305100d25841007000610300515800038007802d01c03d43e0052242c03158048014000c00da00b10320200b81031304180c00141001440d60b500c0040c0c6100350b481035107805454402c03100707400c8200c51741c00c00310411002c1008486d1a140316520003c0d002152904003502c1840703a440080e05044c80388034051040030182588543d0340c2d890a5030075a0006c2603 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 319514460 1250 319513210 319513223
    0xa030503271b030c09040c0902160609084602030706020d06032307091a1003090611090d0b041a0403020c040609020c030a0e010306080154 61
    0x1c80803814080c0819000303921007003600400580700d007060501e86502d031100603010f200c100060102080082015100b142c0000c000580d80742c02410120a50004801300104600c2c01c00310301e8000c101200c0050f01141e030008031103442d1104c00b003c0b880c008040c0c04105000d0300d0040d06207500c21018a000f1081441d08a0045034a060b500c4d64450040b64404014000f006507101000d10801c40306d40c5801c800358408000b04038540351011040d035220030080c0b04070180c09980d240c441030345031a113032010142d86d403000342181c061103004040a80501001074040720840e28054411030864085010307100d044030064520b0302504200d50780d010b038000c0301400c03d40b442e604615001c40500b5141408a11441c4a5409001e0301ca21907005c1c8820f56445030000c4d54460b005002c1640d02c0c401c00801d8481c0800300e031416418480c4d0150058004001e1600219819400c05564846404a800303490b805102c05001001d903800080c29144c00400602081034102d05201c4020029001905e1032014018020705 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 319515710 1250 319514460 319514521
    0xc0321071710050a2c0c0d0b0a15120b03030f09040b04020c03031e0601080f040b0406060b03090c0316121b081b011209030212131a0c0706020a030503 66
    0x1a0001105a020030702500f50701103424085c1c4400042c5040141c00f500080c0a941001070a0810a0040ca440030045035a5040454a5691840b141000030117102d51407080d0340340000c000402204072000040c0a00f401e169070000617050000841c1c3c66402d84802407810503214500704006040c1c2c80e550a584030b40c090060104a550520045020310461040c031106100105003108140c1001803025050280c00f03010407142c50b00303607030500750f11550094914040c0c0d0360b1441d0102c02041150414402c0c007002008002901d480010511000c010417170803606c3c04410101e0301a1818824006da4200d80c0b501e40240c070002d903416007040340f2100300c0440d03c0c100030340340d03a03180c1d15001440150b10b4003007000c81c40111003560400ca15401e42e241d0b03034106022221040d10043d564219860380000c4007640095101201400809043c0191100c001d000359076206103480040075800030607d084150250303200004215000151070800250325461b41415943c808444980342444140d0101d803a04190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 319516960 1250 319515710 319515719
    0x90f04120f090b0f1314060a2006070e0a090213060c02030a080703050406170424021b03030a050c0c0a0602090607020301050a050a0501140d0f03140c0321071710 71
    0x1d80a00132205240c010251030303292080380711019101c41d034006c003008500c0c0b0400040d2034840c28211804840c06013810b0782a400b5010100e07004c035100c000b032441e060055005208480340d11007401d0031444411102600040d4640510300c0c224403039400c2c0f80e101c419040000300038840c01022010502d50004051310380c0d40c891354507118140e078072401c0c0c04c6000510004080c812103400000440c2d0b10f805a8440000c0e0b451326999080030f0410300d04d00c25001406a07481c0c24007299003601202c0b4002082d0010312aa044505c550907601d030810384409403103d08280c00208140c0c0518192024001e044004044c0b90045464900080d13008501c89600a2002c025000160b00c003401070500400c01d100e0002880d00c2e026440c80b04950741a005070400c20706e15054402181d4864100c03140315500074020048480040c0303410340d040019a6220044010085001e03414003101101801841202e03111080c28084420462001e2010413106103021030702c90104240308501c00c8074035950180040100f49104c9032207 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 319518210 1250 319516960 319516979
    0x30f01181b08120a0807090e1f05030106170c03030c121317030901030b100203090105090612011806080106050904080d0608060108010e0f030f1605190f02090f04120f09 74
    0x2404854280f58400260005541d5806050305d6403115840c43c05191050900104480c40da0001c1c00303050901d20f101001d0100c20042c2d9452800910f8000e0080011540c1c41b00e903400601d14100b10811680201c002c4242c1c1c07414003100b26480d02c404400900346014000c0d2114a80d500552281110801c1030440881c2820101c030040c00e4103400d100c000e6849040e248001030503261400d02c0d81d0700075190411603840090f000800e40f0800b45003401e0842e10b460940c0046410f070b0092482d0321070100041000001c030510b9030151250341d801c03102014407420781c07120040d9081e40d1061207201d0700541004005004150171801500c6070002640b008503400d65200e240d5840c1080c207820403011a55152032050522008000c03000c00b030b04061015504101c2c60310300031143c600810f50600c5807000108407450401030144000010b542c8800562003102071141001501e000d0f000c10200d000d0364401c000306020780c039683ca00b24840c9500c407802c0303580c1410003442144d07031410070907000c03040c08521040468003814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 319519460 1250 319518210 319518223
    0x627032a0609050c030d02030f07080d06060929030403030e0c041e0e01060b030a20031311041404080a0c140a050d0503041106160f050c030f01181b08 66
    0x60800441d01203200d003019404d105116101c0c030f10a500507211904415000300030f0307030700741c0c1111108541c8070f10041c01c007244644618001d44400d0381c41e294001c03a2980d0002c0c64107055814040d0f0141603618440400c50b44c0c0c06e1b403400d00c00d032000d604ac0300080000348030b0781104450488640985140507840c00104040d02c007035401e0400088840c1e10098803480c014031445801d005100300034403440d81703060482105e80c4000b4001081264562400150821104a500c2c08c04465051001d559240c0a0503003229034160600498105211940d0800b192409000f4141e00c00b90020f000000ca4861303941c1c92049a0144038000280318001172442c1c00303e0405a503040c209843c0c000581010f20140c5040340c04c3c100f1420b001da0905c0014014000410804490b9102c503080607103040e036441440554042190784400c800805d48002c1f210158100140444c074040c1c044016000c449900002103000707402d0322030b8030400f170286025034a83c0d440171640071241c1e100510302071082c80201c1c50700c034440b00c2e0a01d407 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 319520710 1250 319519460 319519463
    0xa06081903020d0309020d0b0a09050318040b060a1704051f0509060129070602130603090c06020118060207020a051503040c05030d140307031d0a0627032a 68
    0x54104108400c0c50b4043c0300100038140341d40703010046900310354000f4207035820f910001307002c60b640c076400a507020405900440d4003a0700a000ca07a29000c40d4540758a20440502d2041d02660030300341501c14070700342001030710540c10181e1113841c03007008140d82081c00d2640040061302c042c030882c003840d13014541054201d0f001260801c80403500b850440c1c0c8040ca0440c040e07104860866003e204010068000368604100c2e000112120ba030f5501c003407c2a4000c0d001d085082c10900c5854000082c0c0582c040d4040203038944038a10240f041540d0ba04e060b400c0b91409491700b06803a4a0300007540000e141c5034021702e0994801003110780d81d1911480820b81e5001c0c00e01c50744400e102d001081c0001e004144403c440141000ca00034901c00d203038507000900c10b0240b0389043c00b00403404800320341603d02030342007246001032055005442d4000c0300c50740c940d80e051061007601c04130f280c00d94415129074041e0000c111000c800181d0030f6214140d0782e0803544105641c280400d0502103201441c50700b042d6a41050a40b03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 319521960 1250 319520710 319520743
    0x60521041b1d250f0201060801050106210e03030a020a0314040803090f0c100c0f0f080301060306060903050d0c0c0e0405151f0302190302190e010f06090e0a0608 71
    0x2c500c46014a910074080c1000c0b107a42d0103109480d92401c0c408080c0e41c0b41184915084000410070103090b030150178160410364083d42040000706941d0703413002d0f0503070b000781584045100744401c003c40b0100700c03820403000c481e003901b003080021240041074005040403c840d00d000101e07400ca125400c8c800401c2601d04560714840003052003900c103000c10100445400c0714024003100c1d030002e0000358101090f1640c000c10f1150403115441407080089443c84126000050449021190b2501070440d600034051100407a141103c04500503100301108020380340e0000c0100010326812009481d010008034048407000c007002d002003450100b4140786030060b0702c00c100511030101011480500790400428200000410100c846006420a815602140e4054800001010020881c0ea01c04400d03500b020350485415000c0038003001d18980044110749480525444c3c59803154512806030b26103200d2080010580782003440240c2e81544196080002c0000028103d60749801c2e07142040400325070751684 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 319523210 1250 319521960 319521989
    0x1e030103050c0a0609051306091406031006120f1e0303020d0b010302031e09121305090c0c0709020d060306061d0106180306021c24060521041b 63
    0x4000e4100a0038001407411140c2e43c444505050004016030480d00c94103103d00c2d04020b51410340441a03108202801840303106220f100540058181c1500c0705480103802072081a0b10101480501d01c6902c0a4900b00000004110b0385911051034586598005030b0300140000e9134020948110b0203186900c45c4242c030301603101c0d8507020048003104e003101c4085042c94010400c02880f14485e05c8210b504c850752012048040d00c035002c0051134401014491510500005219101c48001c24000c40c2203400031502c1d8081c5507115180044680169807600c00950b00048040c400c460032078018151003111901c0000340d01d42d40740c0707429040e500c487c0c0c004920b42130a050740c4515000c616410358050701c211700304510b80e0900c88940b03e2194000381300141c407140e804074684814014040b0648110f080351a024007295035000007103240040c520032001c001c501690400258240280c09035285081e024108800c030303103490100311440c07000040c411903881c10b06c20158a05030300c1340d48046000e0b02ca580d004000c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 319524460 1250 319523210 319523213
    0x141006080121061805060c130b070b07050705010e030406050a03050a0c1b051603050c011e080106110a06090c08010b0a142e03050f0601050315151e030103 68
    0x901038103811007035602181d404140320500401844400d510ba21440004401d018442100c2984248410040c0f4a02400043c0170040c1010000750940c40c620600c42c8a4450350307081900b0461059840c010941c00c03c1c40000740e111070160015050305405000081480c0705da020155046500c541c03c07900124502003403421070682e02d4452941e100f00044810011440b200002400c1505c0c5480c0801601a00e40c0000d07040010921813244214451039001c13441c2c680b2490495243c4212812146c0042c1c0803044040040b07000c2083c011081c0e10944075640542d0034041c0c01c81d024010b0200d0384c10781d407040c2d04903c000107900f48640100d00340644080304140703041820309404d656400002c24072407018950240300c51282048000c015140441e08000980032508080c4142143c000c0001401d10b8000c0c0c5032044940c2642010340301d0b0480c40100c03060f60b584d14005603050300080c0c0300142010f681500303401960030312040520028000355405410701c428020003007c0d00341c2d2030b082c034403d14070003000400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 319525710 1250 319524460 319524467
    0x51005041b21020915150a080702120301050f04090803040506060f060705060c0306010c020a0902090f06041404050a0b0607031e02060106300e0a03120c0c030e04141006 74
    0x20140000c20000c08150310038030b5405805280024001c2e11a41c120004911800409407070984450f2018080e02052a48003420541607004180070b04007103500b40c40001d403014808105150905120740c0c005003140d08080910001c00c3d6070381440f40d0080c2d036691160000c5802c003c082d6101d64485c0004141c0c40c5400d0b824000c01c83c46048500b401203c09001120000e50301092280d48050326210264980d81d840c0300490319481c4240b4042c0d000006410049001c0710b02d0380081c035003440c0503182e00101245803014403a1902caa031082c81080c0ca0b0100c0c503d00d03107181540080ea0001041d2101040410100c0d0015038103030302001d4200d002c0f03000d1004900d01041070003404103203135407140041d003510762400c1806090404d14014041901c8403028260b0580c0d2402d014800729039480321802c000c00d0754102c800a6075501c030590260b0114111400060604100b80240512000d55903104852110565015252861401105035005844424154040600c3c941c0b8502c00c070b901c2103200352402d103003a4000c1d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 319526960 1250 319525710 319525763
    0xb0f1c0204092901540b04120f0204150b07020102070801141602070f062a03020709110d0c171003030c080a0507050f0318040603050703080705100504 66
    0x340f10384003030881075012030303030812601a00e028405521940e070b003401c1c1200c082c0d01c20745440343d5051994200c0f09004d480f14035480c0031030010003c0b00c140107000d0300c524850169006511038200c4800a510b4100001102d032131142010a101030000300700e240725120b405500512503000709548034030100d504000d41d81e04210900041240800811100454600180c010ba400808042013440741d0764903410303624030804c0680000d00350b6043c6180d446440b4040148a41541060b4a5401c0700c12154600820800b0084000c01645500280701d040d1070860050041e240c0c000c01240800400c0c00540a403106030f001c0c0c079000144640e141c00b0b44105200d0315a800b004050903507121002e9841c1d044c40001d070001e01d0412940d0300401d20503103903249288200c3d014411070100425500170303d080d0754242d4500101401d540101c101040300110030030414002151900d00c000350640e400340e807041010442e000c004141045c0200140c8000045084040b000c1e0381094800b203464080803c0040400791102007003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 319528210 1250 319526960 319527011
    0x1303050309180103230a051f0506010e091605040b07050102030405060f09060f130f1b08210d020f03070c061a010806010e0f0a030f12090b0f1c020409 66
    0x742c1c05154155100c288a03a260800c1c0d8001c6401e001003c070a111008100341084664440c040fa1a400780c40e10362036107040082007800001908100c0484c1c00f0303601429149504140c0500310000a5440e1b95401c1078059441c1d5204042c00020003001c640b1030050b800610340e031400b072000036980e41405d103489031800b24002c4c142880c1060241c1440010381010a500f0f0304242958000105a15591000c0342c08581c17105006106020040080301080114521844c1d141e08251407c0c8c1c440d0f5540a25a0b11a81c4c911018020400d00c80381881417a0400b501500e5081d0550000504020760159145829481600e0480200b11001146030070842240910280450340818242e407891300000041c014540160209050003074240701003043c0e80f141005125001401000d180401d65603041c0f0012041d04440155401492910301c44910350040c09080d0072a50b9500c41c0c2e0b4982642c540c0244003a420003426540d0000143c2112660403883d4000b8002030002100c0005086a1145184d466402e02020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 319529460 1250 319528210 319528249
    0x60f06020105010b0406030507260405010507050a02030d1d06010308030a0e0a0b060607240c11010b15030c040b0a0f030b0109050604051c080403030507230d0c06021303050309 77
    0x140013181c0400282d8044030500d080200b01510f0f410300075607150071344c0c1994190101403400e004040c644904400b60040d8010701c002c1290307403075900b0125018800c00b40c4200151303000300010040401282d024800d0103034614140905110103802042c2048070a9105a41010020003440218079841c0301c0c213041010500c00070025501c099440e481d60381001095148103040101c1c01c181807041d60705c81501001040190514603000e5a0001c800400801100b00001400240c0d000c042100c140703d44403070b10000070801c005014503c00400c107035900050080c82d0414088c000050200410030280511000c2c0c5e441702000d0350b082d03440c02000c6840740e0006c0d90402001c0c1800708030700c4e06c80d0b404580958070282d501301c42d540c0c6203500a0f83da480d0080c1d40103000c0e030b00000f4000249913100700641b0b000d921803196001907101421140c0d00b0026440c10465898110f0120003038500c1c0500d00c8150868030401026007803041c03c02102841c004139601c00e80b22600700040d00d40c1e0614013014074036406060308a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 319530710 1250 319529460 319529471
    0x903020610031211010213080318010903020d020909030f1912050411040b0109120602030a0e0703080a05091201231f050d020f0a03030e2d0907090f060201060f060201 73
    0x4403800d80700f200040c1c3d12000e2041c0008080e10070032083d01201d2a208541c010011003e9541d00ba0940c1c0e40d014502c074200340c000300010b80d58158400c54960003125001000c5610000494003000241c0002600c29001c0384010011b034020424480302400d6035181c50542c0d80b403039201040020b021025404401461030f803401040000040c040540c09801003020368000840059080050380c800c24241c000c02d0714054044038070b80c104011600194070410155105001800001000950390401e601000303021030300c02d01000c050244140301070103c1210007800c0c0c45c501d420804002c0c0c00c45a062540440e1104032042c03008068a00f1100d207a0820140c02c48440074407900f40c02d9602c0e080d514010a4442c9000c0448041555070303100001c541542c0007011101e03000d40d03900d005010801e0a6200358001c0c010100d1101045000e6668000c4190480c000035181e1a4a0001c11262a40003002c40060000070030010910b18404a004130107020183c00002e105410038682c40081c0d407a41d0300c20411603040c01c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 319531960 1250 319530710 319530713
    0x130e010f0e07050307030b4606050403030c02010507060e0a0b0708060d0321020c100e010209090411031c0f0206090607090b070305090d030c032c0f040b06070303090302061003 77
    0xb400c407503210100b4a00001c0c847c00c0c010000d1403842c0603076030481d80c59504030000300e4000700c2c8609000e40d81149940d4101454000c00844144a603207102d0800812000d003c104042401282e084032140d205240c81450600165940811121528121411503014981e100c080068928040d070b04a0300d9802c0c0900c1c2407510800103040b400318240c0003410000c02e00c40c21425111500c3c88600f0340308002c00c0079921005008441c41d503560003980c400642505004001004540c103200300c03514032030b014140f0540342d03660707454443d202c1c0e2502844a03010704c90208010484007006615860f1280741c1d03a210035024610910081c50604040d00080f45600480700b4482800e400104100848680802c000e4413001c15040550f402d010342c001d080e801449440030482003543c4132039030300c0c00544281c444165003112650040c2801040c1801c40c0c03404078000c2542e50207440c0406d02c60300e170407000500100f2041c2850340843e0058011036012804240c0303c440100805405005080d0310070110075804600c140345 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 319533210 1250 319531960 319531967
    0x709030b0105010509040e06040501050712090b0601050304150c030203011805061e1c05070501030c0f0e010e120a081305010815060315030d02060103050d02070b0f030705130e010f0e07 81
    0x180b060034140440098000190b40395908240c0c0c80305101400d03201d107458181041400b8007000c45400e0b00080c00307880c4a00e096102403054022160f00004690380d25039441c070041d505940040c01c00d40d02e13110a4a0f50800c0f2501900036807958003420759001da200c0d40b41045824040305c1e215000301d080390511302004454ac640d038010112818890345c034988010003060225482101c803420086034949041d608005000001500b50115071080ea402c00c0001203030740c011207400b000d450000c1d001410341a001240c66105c0e618007550140700810b40341d4000c9540011030700d0540e140310100c40460001c02c030488122010382600e0300804081c2020304551070a9440e0203d089034a40505100e41008004600200c00c01200510303010070182c11144011241030000e90ba5480901c03046a1501c1241e100c41c1d485440425185d007200d080107180b9082022030307114240d2a0b04010080130412009006400001810541441c0103041c841c00740f640315410305014101d80070741038204003100c0a04005200305180e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 319534460 1250 319533210 319533233
    0xc010c020105032e0e07081006170a150f0311010905090109020f1e03040b0901110d1a04020703050d0e011a04090311010f06080105091203011a040f030f020306070903 73
    0x5254490513030404041ea81c1d8052050a003000043c14140c0c2c00d0103c2c0351044903281d40d0040207039442d004e8079030f91100c40c0514050f000d030007100000b444401030f603454242030f000c0040d00090300e004045540e1642c6c05031450850384c10b03405500700ca04060800c0080c0700e500507269445180c203182c002c0e2041d040501140308818180f00301d552041e1700180000d0303400c1616040c0c803001003090b503480c4018007400704d403102d07070b03030400c0e0f80aa0700c411010010800804052095001c000480e0140d94203003460781d0080d6000f0309017400307041c408182c4020308a00c590354500c02084914800d80707501c0e480c2c01c501c50040702207070200002900d03980c1c50801c0b4010781416a0002c04080c000444010603800c0c01450116401026145040d42541c00c20410310381c850034030740008041d079040e00001c100ba40e0301e09080e6a41c90b890071400511000017040140401030303000071440e04404c501700c11580ba1654a215100c60522543e10079103030400c445001404614040c4607242d0017941c680380607061641561a81104002c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 319535710 1250 319534460 319534471
    0x6020705061308070303050301030209182a030a0c06080a0501120609210305011d010320030f10051605090a0501030e0c090907050a0e0c030a09030c0f0c080c010c02010503 75
    0x10450380b2107415290b608401901074001600c500702d5492402810a0708203000803072107014100300043c0f002e01c0441c6010401010b4030000e05641c10451403142d60341c4000b1681a072440d0003090742c82d0036a201086080d502a20444d40034120a241010040c50004042c0c92032040900348401080174140400b59072400b40c1d008000001c004007586002c00d1016490752401145112080e03601130700303981543c0440d048130381c8a01900c044006200a585c0048000d020041940300305a220702c03550314000d198030740c60aa015044840e402c0d5401007540c50443c82c1402c1d022625190020852401d10a80d0b600a8150312800e0803030410481c3c00000740504254043c1d14105562900c003000001c0c400c0085220821018008090718141041140d441350f84e1805600d0061700c2e40344000413a4846035400910464880c0349480c15515031036100340103040c016800390100000e0340c0c0c400c4c3c04540359240c0b01000a10031461840b43d41e18016206040402e01c503180c0c0e040c4240c0e0818540540d0300030049a5204 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 319536960 1250 319535710 319535719
    0x60f1506071a1905090109050c03030c120c0a0c03050a020f0a0806070c15020403060b09010e0c0d050c07021806011103161103100e1605090c0d0c140313020f090106020705 75
    0x1a914024014480039810b00340c3c8000c0307800d1006002a0000652110030040d000d801601c40185544041c142d5034480c1480d01111a44081d9000c1304540d0180040d0583e0ba1446042d02c1d000c035295240c0741002801c541044d2042c0e080440c0003011442d010390841c02c8443e0607070b90451803a242c40d4140303445000c01060b01c024014280452010448110390b1a00c004000c801c0c00c545494a03410403000402c19404d5650256a4600010460540c032280d000e101c3d001c941e14035440c0034008a039441c081e210103070640403c047c041c40088010390300d00e03004401803642204599014540400010205012414406820f07001082000ca07840c6d4202c080219440d00301d001c444040380c03079502091074001c48114407403801c2e140882c040620040030807060384008101860242d80c0e43c507001040302e0f46c801524805807a2004100141c00b00d101900301c0b140169050820045804e000002503080e944211a60803503a02101202c43c1103140142c40395810820540b0449040d6041c02c0b0040e43d100814084c0c036115 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 319538210 1250 319536960 319537013
    0x608040303020d090b070e12030f040b0c100c030b030606040902100c020f0306070305010828030806010e0d06020409060803070c0303081b0415090504090b1b0903060f150607 76
    0x85034520b800603441c0c1a840345c44122186070011009051301140200740d07201da805514403141290001060b81c4444186807540b40c81c1920302071440c3d2a070707800000464542e000305c80350b00301c500c4540e11174102075400d1034030045007500c44201058140100204541c0c42030345000b01b1280540ca5507440b449549070070b070900c0500081035000060a1640c1c4021a942c14841e0000304950164180c00050480c1c20303d0302221000c4041101040440004603c0e0607000c0034800503204c0440e105600f416045007060601c11a445800400325601801c00c003029121a600020104054665441844014912000510b0601a850750340c0c08142003a484080c0410007240c0100d80303003405200d690004114601108da540303d80c8c4520100c850308503e12201d010034120308001506040500910142561103405100c2c0d030764a1080581500c080c0c1400d40400c1201407000e1003e9403401c200c11805000802e1000c2220314181d900030580c0b1070440112070141d00c0a01020001a4402c900c0c2c00c040503020801003407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 319539460 1250 319538210 319538227
    0x2031801330302030f0a02030d0801061e03020c0313080f070302060304260c06070f08010b1b1216050d030908030f0712020a17060102030319020f0403080406021608010501060804030302 81
    0x610074100c1d0030203075040c0110400c00c0d81c0c240c000100300452510139801e6900c204500343c0d003550000024032504010510b0b06088078100c09980c103c1c0e0525a0140c10010706000810b40310a1441c0c00001448206840c8840309014a0104110039100510a1002000210704550108556000c00f4100a0000c2c0281100c40c45070314401403401030b0342410104654484001116a075a111070680e5000040341050083e0031441d03204850300d42c1039030302d0040f00c103181290301048000b072421070b06c00100f51406804444518450b018004208080c042000040e1415050401c10300f000030714500c40042c149003049610020344640c0649034401c0d003400d140041580c40d888152981c22814060003c110304c002986050140c10000b02c0c19a000c400e401088203982c5c1d04c0041e6501e00c000d545211051082c0c20440214040a80080001601c05d9681b1424540da035500c0200c1500a034100c0800351f0000340b0080314503011040c981d4010012680280035035454500040c2020001074805410180c00041d04007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 319540710 1250 319539460 319539551
    0x90303190209060702040504210c020d140a0b09030a11010605100503090114010e0103030f0e09150d06020d14071e08150d111203180f0d060c0302031801 67
    0x41300c03c0d80180090009240a00e4a0f010031a0b51503428940301307000701c1035a140684190554262981d02505461020141e612080100e0424020b1030000744030b0040d000c070002d804c200303005008018600080d0b40b42d03807250b400a40200e22500344645e4503854504200503540c2c2d01208000c040f96607080050b625100c42d44c080d40074008500006120301d0281e000010a00000c2000c40d0489000350f0300d80360002c030811300458404a00e210b040c4d0303104c060640440c00b482c100440d0840b030f4034402003001c5052900c5584d1801a83c21800f1070758021a074034000f1962442c550000345500480502d4808030748594000e402e42c282d03414a100c4000c010000d800220815070b880d0322211000030013011a1218070651030840081402100444c0c051078802800440203000001500c020a2940c0640601081a01d09003c021a18002c09940c010000d008003400f01e036641c814040034061035540503981e40381c0340300d2510500c0580102c4030300d40d80c585091000c0760700c0008241c9400c548a4419416445004807074030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 319541960 1250 319540710 319540717
    0xe061305032206030e03160813080f01050a060b0c0706030b0109050301022b0902060d0509251517060d03031508060a060f0506030a02030604020403120c0b09030319020906 75
    0x80340b0700648090600c0c1c2d500008800c000031a012940d061101d000c865040039183d018002c07200c6440141c03400900005225100608948191a406480700a83d61040e03a4503002c122400980165982c100344002a0301034000e41d8060464592100e150048189255941d0383e60362091404144c1e4456842c5842e038412a070380d90013004018029500c0f02005680c0414603030068040306044080842d80f001007181d00e0140000003074001b4480c90800861a1000c00545002000c0d0441d42c003404c4110540720384084031080c104040b80246203d424241030b110603009401000c0c0000f44600c0c0c00040e2001e000381c101d0b6951025050700c80280300501450300f6005021034140e21075040c500d42502080342d410020700203114414021040c04903503621401c040391001240201508043e04000184406406400554100e840600014601541c81d00c0e103010381100c081f80c2d1400101c00c560040c041c464a40000358100f80c1140c0030b140303103082c01c24628001d0751081d103c500c0c1c80380d000324110b00a9962802038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 319543210 1250 319541960 319541977
    0x30a09081207020c0114070605040825050c060f27060c030d06211b09090c03031706011b14030d0c02120403050d0e130c050310090e06130503 62
    0x2041c0c0c49000365049036401d0503045800c040140b08030661100d0541c070500900c06011444000649801040e403248000b510b801841903426450820034207214009039803200d07070010a079480e400000c1d491840c1c00b500f0083d09400c0288140d805118101000c200d0508031403450300400038945880c049a510720100780b40920a080d803000010500000048001c0028140c1402060080040540307410720780e4180300c80e8048408502400f480306000280c5100703400c01640c0180c4036060750f46030f9100c0c841000e4030304803101221401c1001004004154010092039503402c0c10303180c2800540341c000c00080860759950035007003465030740e0700a803028070101e904060400d14041003640e03130b180001c40200006d0510140060010b2161050031461032080e6000d4030252940100038210180321060102d84440740c00e454035501142c01c8414110882561183c0c2041c10b0b4180c85141e204d1a001c20344440300001684290b119504000c05003c403010085445907225100f504484d225010a003015407441c00741070b89 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 319544460 1250 319543210 319543223
    0x109080c062b09080415020303010305060435041422050c1c0603050606030d0834090e0a0e061308070210020c04051024050d2c031e030a09 61
    0xf401808400c100601c15a003503903024014401040d40e08980d070780310922000e0f115410480c085000a0704204006005200c4845500b00703016141910320b880c030000520700115880300003010800d55421424480340b080e0b080319082c10710000b000c90a0200580341d407040c184d141da10300004401c0c4040000750f170304242c515130346201a50403d500c41c40040c00640401d44039841600e0000e4101c0ca000225151f2007401c035543d686d10303030f150301402080c0e02c001405e0701c40c103c220048220010340390001e000303510820710740c1e9020070040ca40071000d058603070040c02c002001070500c1c0c1d48020361880010002c1e0420001c5941c0303a1a0106c1d414120954003407044e000390301c85c0c161112b43c0c000d00d9001600d122074110449007002a9250b0300301c0004849503510851341c181c44a009809503100e020702c2d070031001001030704005160880035840e060440341c0c005404030402d07103468070b1390042c9010755100000c4015140001c41c41c00582c0b100b040c3d03950b40103400c81d000d000300000001e54038110070f4001c80c540551180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 319545710 1250 319544460 319544471
    0x1f1206090e06090106090203160f050904090302030a1e0c0803040f0503030126010c0f050901090e07050d0b09010f0506071104020d050405160303080a09050c1c020109080c062b 77
    0x144510b44995007601d0035820b0758205940424005118821079004808400740c050162031040810703140c2800281c0c001040c840b0078072401032191220b001e03c082182c8682d01440c0d69602810002d040724111048501c14045850100d2808540200705003000e65001081079449075a42c0ca02000c12448211004110f404084000600c071304507003030200c3d500118411016112020050328600321414035940030001688002c0f1111080c0c011070080c08540d606240003903042e600c8101066002c2c1c000e0321014000b9200084445101c1c0782803180010350101260451044d514010240201c84407038098103120320400a001c000700510286e107480140000b400542d214045030900b00300803e4221015904c1b0300803040712203014940003042c3c4050340d915480301c00e00e546030211030070018200c1010444076449021018030059441404107000042000740d25122600341d440010001c6000e40d000d0341141d44600c1c54080d0b10f0340c0e5072003940c15040b540307009251082e2840c900e508000028a901c1500549040d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 319546960 1250 319545710 319545731
    0x621081b1002040b0c120c0c0111010923070605030c190903050106030b01030c1205061b0409060e06030d050319090602090904200607030c060e07030b01090501080105061f120609 78
    0x2400507040e0417440506461a0005642203007060703200743c0b60311603401c0d04400c020031034035130007030000e10020f18881000055100d619a1100000d8403091061328806091003200e640c107a108009150240105103465411401c000105904078010301d00d0704075108450313103411312205208810038401540c000340203100080d0f0b03a04221808134401e0100342d0b403d0401140100384640100c03a913080056001e070042c407032a610303003101039854690412150100ba5041200003452115806194040c0540302c18049032814410105071030118000349080c1840410310030489203c1842e41645c0a282d4407a0300840d075402c0750700c2d20030001d104403240705030b010b031010051109002c40081041c41904110901c812070540540800c401170007030810040006440102103000107070243c106a03000940042202d5401b0f88039500c24200381c0c030036041040d060359a42c004001c2d441c030074010030b41c21402c1aa401c105008481400340e10650001840d02d09010401c000c2200c0b0488650010004000c070303880c2000100e450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 319548210 1250 319546960 319546979
    0x70b040b06010216050906012313051011060c03090a060501090c02010e19031d09010b0711040603030504030602031e0709050f0307060e0904031b03030621081b100204 73
    0x90741c01c540140b040c203503c414402001601102a6180100060107503a03070500115408070036034000c102141e05140c01f2100c4402110083d001c01006003529808850400040c42501c4c51040000b000300100b800300b4005003a404500b043d0400e10352241656655500ca80d1380e40f40020905004100524110002440c1d40f419404a40012032680c02030020741641860b45640c2c140701c0b102040f101c0224241280000e010b130402500511200e541082d0403107610001500c98070b8240c0c00241002c10010b100b50030402c2584822840784d2049400b080344908603100180313280594040180860b0b4004081642c09046013203402425064000b0781c0041d03e8525070003403850b03046114880c001e2200e0400000c0901c1d002c1040020348080c1d50751010600800c0c0c04000040a014100b80c06120440c04000c440d4880007a5944030f01c1d000303407400310303406141c01d8102c3c40306040004802141001d0040403800900d404045541d03da502c0c0c03110780c0740481d91a001e80c1c140410000002e00040c03001400290480c103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 319549460 1250 319548210 319548233
    0xf010b0d320a090503160c03020d050303071421090307210207060305063a0309030209010902090904060e01060f090c030c02060106210b091f05030a02030c040c05070b04 74
    0x1c11054032890391070303001540c410b03100c2d1040000c220750401d1001a0b00000822000c50b401805050040d80c180e64035000306410291030441607800d81c2000007048140354201d107440c13131000000d620503450506903c603800483d6641c10341d90440c0000450104043c41410000e6914036604400c640d444070171000010400315624032002000b44c081e54000142c618080e00c9641d20620001c1c2110704040182d0003d1000d502d03c0c1d07616201c3c2c0d1140051881282d007580d00c00c080d40148651922104982107004221303001005a000810803401001a184661502011039411542c440c20104410901ca41c000b40500456040030020700706c08040024405c0046d009140c204074981c03810015500031840481e21a4803d004490200d0210803003410030780715610360300c0021440324030005142801400010100ca4080d103241c00d2040e611143ca42c2d0f86042d00281400a09003100245000303a42e985c08251160b0520309254801c42c0e5510a01c14843d018104654820381e10540801c5a840d240c03401d10f11140c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 319550710 1250 319549460 319549541
    0x80c0a05060711070302120f030c06101208070b09010e150a050106030b01320304060b01030605010201020a091214190302061506271e090c030f010b0d 66
    0xca100003148026010f6820307101d4060120024002070740c15034007404100d034104d080c052400c2c822241c3c09030200d00306101411880407400c025252600b0020741307001141034035402448000c40094880d000050b620800c0714529540200240070642d161401c4a004064222802019006605000d981880c2d40b60b1090700c01c0407105410442a6250041141240c001c6c3d00d100f40460101002509040703030344c000c0f10340941ba106010620440544918176110b40055904865142c0c40341011884c03507806005403405406c0a04c0214108010b0200007030241042d8031614030380301241d500c00c0c406e000c0c410040e1404102d00302e0031600d10740192030031202c0700001d61400750018001d4a0101d211098885007440c0c0b4054000d1840e400d0540c42e0700303d0102110b10340e541c802c150070441c54540306626000d0f110b03c00c1e5884041c8240c4176034122414440401c8004203c8826042c080041040c0080c03090b00e00e50560300690320443d1503001d00044007000300201d40c00c258480c804100000c1461030f40c19000b00c0040b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 319551960 1250 319550710 319550713
    0x2040f03020a240813060603030e01021c08060f030a0c030c080708010203070f0e0d0b0a0e1002030633030108031e161b0b070b16021b06090d080c0a05 66
    0x49a9842140c83c001c4207210b5580358070708140000c00c08442c421840c8503081040801c40703e501c0c40c060b648440c1141d81d542e02c101c0c041410341107815070303a41c0c0610401c0c1000c2580c015050000d4081c5400408a02d4010011480307004840901d070b40c4c0b1b813400c10403003681941c081800c0140e1603c0e03003801e0b400e44000b40305a821903c00c210000c241d403003060007960b000e610340e515584849420700c42c1c152141d44903940400e40200c0310101c4e810104680d440040d024041205001415000540c543c50801d0001d0000f801d007240100240300d01c6440d00600e514580d000c00c0c4505801d01d0f02c2145000803000845c07000c5504500200020030780d2100032006003141317004210140e00450410190788114001d0154807000d41290000f200045a15410300c4506001d8240b50910411780341c0c00da0403450382007080181c50440440040040100324a202d0000d0916940001c0c40d03580015121045a4015410628090300c4040f83d034011603114548080412a071001e9407e844a8800750340c50703960400000c0a9516 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 319553210 1250 319551960 319551979
    0xf180803040902031f0f140607021c050106080d05030a1505030a060209011205041e0204020405041806060e010806070f18140f12120708090a060f0e01020129010e030102040f0302 78
    0x390140c4401d40f00407201ea00002e02541450500304516160800402c40d030060b00400c52140144d52f22404200740e03084141422a09600e182061800c460b65900024440d60018818600454000080c6c2e580b000c1d0412022809250b900c154403206015644a541c00d807103440e049404120030394000d8031552500782c0e2141507411444100e8402e4401c1524003074180b107452080b800318580041c1c181e89010780081c00c05450555600040f0f000c450661b411581e01c041d40705821010000705005d4180200303450601d40f651941440c1d030075515100301038215020f211104200400b0700f8000c60710f103414103980c40b00702000b00341d5410180d03180031401e001c0c0c188200c80030112035842c0c0c036208101e07180519841c0004d02c0c41c0f45880c083c20169612112007560000300500284046544032030000c03015080c1552141074129805902500800d0f40450003815039042c0002d50380d41300440c3c02d21420b2908035243c1d07101428102001030b10b80d00c08a40c441600b5500000780800d02480051401049910a48030341d0345 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 319554460 1250 319553210 319553251
    0x9012c0609010605090a0c020703020316080606090106021c090503030f0307030c0c031b03021603061509050609060427030905030c040e03040e1906080604020909010b010f18080304090203 82
    0x200c40c43c034060280d10400c100007054620803180e00190482a040c01180c25a94898000038a040043e49540d600710f82507040500042c14140071294001005883c400d0311941000d1003e501c0f51210030140312054a508007107240c43c0e1003028108014034001d81681d6480307146103039010981d032048490f000401e00b00764011043c148642c0a4090719a09642d600181d00c007030b8042ca003812400c2c90000e070211710402c1d050783c10011201c42c04400551195000082d1151300d88031440c00400320394000c050041c641001c001e010344030140925031207d81102c002030014001070008040010100308071048102c0c50041c141059000440e100a07640110210380058107100200010303158441c0c0801e20b16001404100595000160300e183c004210300407a28214581d03100d10b80883c0c01690143e4016803000c0b0500c01542411403029801c0703415000240401c00080340003800144000c140b040410031741c040c1405002d8520401c44c1d002c0c01e02c080c00d0702c3e0707600c1d0b440301f0b132002070b400c25a2022003140348c40780c081a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 319555710 1250 319554460 319554463
    0x6020f06130206040e31240f020c01020405041440050c03120405061903020705030c060103030807080c07020f0f0d0b0103020f0405010806010e041104090b040318080309040509012c0609 81
    0xd01c00f0783c7c000549480014009500c006070340080c4541000715403500c2c8a0042c0440a0001d0465030418100040c0c40d01d2800003000141da045602e10341328800c180c0700b400703e0f01c19110b00050b400220b501140d80003014915122010131401d503801a4981203620001003000b81c00f007843c0046010840840d22010480020980c6e81d10552042c140c1c40368041084a5041a40038400a2500d60034100103041501b681c0301d0724190380c482038035001c95400c03080040c000c168204c41c2203070708850300e0314100d01c9520700300c024602070b40704611000e881031816100c1d03031120750745481010000900250502c00c2c0304070285888800c0c15000c1c04201c3c4034a188120518850900d88075450480303030002c00810340d5034070381800401f50600c080c20684080300041030a0910761640d02420100b03078454040c1602d1440c10b4100201040300c940e240403600b003141ca02c1049000000400d0320400134040b81e0015454a0349030000d401810303070300d4120301c2a04120800e041440501c8841d025404100d13020341d1f15a41c0c4601189 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 319556960 1250 319555710 319555801
    0xc12020d05090f270f330301061806030501061502030a0c030c080a05040e070c02030d200706030615020102160b091515030706020f06130206040e 64
    0x400a00c0701c82c840345000340f0120409980a0208456800c100d140300c013102d41c501c02c11080101c0c0d030340188480c03aa4400691940000316501d07100041c000300502006071044011580840d00710078a00902c01c2da03081d8070010003000c00c0d510308842c0011000907803010344018801070303405500e880303c0020101043c400250716541c1c9540910700d00320301000c0946400c103251900f82c00700444003140303400088211008041d03020a41e00d80d543c55628200540341e408034010030b06002c120007810284016107000a9204011103a0300340000b49854801c2a05a18480103d000307d06101d06c860001e00e03030380c01d5030005040d610007031001401603101c1402a0700343c0c4100d5080700300c9800000750300000300e694080d03c0c0390083c103800151902c1ca0480d1081581f40041034624541c000c0750480c0e02c0b0700e1454104680c9c0020000340c009007080701c03411040039840b1000240000503d600c0511001d045655910841d4081c00d00c00c070000c5803e0a105041c007030303503070481c00c2200c4001c5c8401450411840014601 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 319558210 1250 319556960 319556983
    0x313060b131505011704020603130b0a09110117151212031b13050f130903030c081308030c0313080c0102031e0105060910030209030a260901020706050708090a03030c1202 75
    0x11400c864403070b41d0902805500040052b410500210942d5000030b180c5080d480c040c5070008404540c45146061048012601e03110450501c0783c4203800000300d003006001c81e540b1114403803103c684000c84401090f1b400144102070140c0d401481d01000310420900091406020002c1015a84000c2540d201d045e5100d2140c02d44405002c04074108003a02d001d0441c61000c82c07016159102d50131100d10400f040d1a0080021030129031590022407034a6404030300706910200311116400c0078800d0751200016484054248006102d0000018104c040f0300c404507001181d00044003039490810a180a00075001910408240c420890032210307110210041141030300c6000340318924003400d40301080083c1503548507190506809100f5a041940c080c4203403c0502d000f81e0851044103011040340d0906214403003c1502c109060000d042541d034006a10800d88400f428140d0f668210b0707091544140c0a01e0411560110320304001104050344540d549442e28800d000f40041013002d4401640c0b030b0720710b2252 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 319559460 1250 319558210 319558247
    0x1e0f05010e03030d050a0b13050601030e01150306150e0f070e030705010f0e04110309070501020f0d0c08070c0b0d0902010e1e010302090604090507080613050105060313060b13150501 80
    0x1044004e083c060744850380000114500080705901c050118003c148142d000f000c05994400c100030701d9582501401003206400b800821a02110050720f15582501d40809070034142d403888118000c2d6950203041011f000341006240e200d181013020303000840001c883c40e00c000750301c040d1401c500d400c00140c83c00c10340300140c44203942a466404100e4119814240310b81e030140e12046840818042c2c80001c50041040a01500482d0300740400a458800c49510a01c4030f42c0c05503074605143d982c4569185d41e002c2e400110180d13100203030704044410111075000520340c01000145641d0501300e40c3d100381a81e610070703200c02e2155041e0000700060000040a18164481107000124580d0b100341d00504041c9401446542032948a0388840c2c04c861045070342c000801d08090500c002c6252503440640c0c081d845d591309014560500d0080b5000380009412810b18481c82c24001c0c080240c80d400c0000300800c003410183c0040301c5540302d10058400e051101c9a0b4440080380403c555201c0c004883c084412200f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 319560710 1250 319559460 319559467
    0x50a0e0907090e01090c2405070b060907180801140a020705061f0b030f011a040305100b0409320c031e0309060a09090506121905071e0f05010e0303 65
    0x40c01e01c02501032140c0626955603524545e0000941002c50702e0081e0050303d104840308500c03100c031030300701003548200402800720034003010001400302c101096001c00242e601a555407100d400541f0116403150440000280821003c1810413055010034811040200010381c1d40c3c8448030068120b11801c60050300c3c80d0461000a401120380303008455102c120105545965642e401c80c007005070300700b035920355404441c01c00100b10259003607031000705a0b404800c00307901e843e1541d550199240384446080d80c2c0b140c0c80340950040b03665950b00ca980c5090308002c1204021a9100345540001003032540140d070180402c094800407040041d00c0410103102600420b8040100320105200c41e421581c1d45000b40b00401c019000380d20340c1f00151402440d0b603100c0b000801c0c1094100000c3c0e5030000c04560085803803081c0c0388110980001e403240c0003006c580022902c5074080c1001c0782000300642100010140c054443d5055080e280300080844503920100c18600f610390f801140c50002c60180c5a40c103078002d0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 319561960 1250 319560710 319560719
    0x1101031407171f09020c0705040606020607140d09080306120c0307051909021216050307120b04150816080a02010503060622091409300c060c04050a0e0907 68
    0x30702c1d02d81d0050f1944085010408904070300c20508003480d00f00201c15a0007180042604504005800103441c0c01c88042c082503050040081d604c11004200304100540c0d031101e06442c3c101c1030308484071081554028030100c54070382003658651b84180e5410b40203181c000d0480b040c1490102303420901000c0103014002e0a403600c810818030300016a82140c0800f0558800585084184020082104460360100d01850322000b4010b8064144019400784102001000314450b44512000c490044ca41d400017083c4501c600840e000300200841c0c40c54806001101280c400f078001101070204508042c80e034032507912001255195400ba64000780801c0050001c05c810345044c1c0058981c9001c261079901c40220450036a241100300ca44c4000651544c0d0250034000160307001c8480c0d402000b000041c282c120b100d0380700800e00c09084c80e00540c108030184031910a446c1c4801182e120440c1f64049801a0402e84066122030f40288901445210000400070b03681803e01ea9440c802c080c00405003001c0e6103003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 319563210 1250 319561960 319561997
    0x5030706050c0c1c0311120f0322030e0406080309060702042f09150c0618030708040b030f0105090114040f1b0237020f010e09041101031407 62
    0x2c5850700d0014010400360f40ca55882d1107800030b01300c00c50104043c02008130350038013510440d9003001c03000303031900700003500031a80c040c00c1c0c22900d01060403001c056a036520031070718184244009140c4041e28451541c4070082c10740c44403e8100c000003c0b101005055500c2c0540d030740d0307445040e0381a45c01103420f01c0117201610b0964810528500c1081e514005284c0b030040852810f0146048076541410105d08100b060074060149042c4248001490381b41644040b4520b43e1054010580c04d895aa1105080405142072042c0d0b407955030b12000389034856440340c15806c0c064208449ca11403c0c0d404200003d150701d08030103240d04a40f00c0e240402c800705e01351340600024005041c0c2600d800c0f030319000103580442e11704280c06036804465000d08103044241c0c80794482039240904c0c0a00d0f11184020040c04035011001d84c0202560440f609000004140c0050303c030200c452060b60342c00a20a401c01081c0b0004107180b0a240600341e800300302210300440b409481c0482540d52000080041c03036003021349646d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 319564460 1250 319563210 319563217
    0xe010302100e090109020a1805011e09170a14010204030f0b0603010b090f070306230d30020607031a101101151e0b070b1b0414090708010503070605 65
    0xc0b480c1c60410902d82a0116503040d10a034001241c0707960008501c105180e002c0702c00200c0060b100720720b1041c1850500000d040701001c00e40c0c5913428020b1a00f00042c240181c811800800c400c14460bc4c2c1110440101512282c3c466000d07144510406400704880c0307010304c00c07102a40d90007440c1c02c00c24002500c0303030310140000070602034041d943c03215200c00d96a92031310306c0c2d032181510580c2841c0038070700110300a054401507841451100e2448000210751111800c181c56883e0059582c4030f424585424500640000711115142c8600030203030000c1c00340050360a0240c4130026400b100c046841d0361108600b1100e68811001030303030144410319281840c0c121041c41603100c0d2850180c6041070400300150071200018a185c0002c40c640c02c00308030280241d0402211a0840341c0301c1342c032803480c100300040c052060380402410155054002800700d034003410008140346000200a4583d512550b0000100b00d1550b5454030592408001408480c418200d50341654000750141a203e80b41c030784142c40310340 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 319565710 1250 319564460 319564489
    0xb01140712111005010324090203031602040204050a0f150207050306041707062a090b09090709080d080f01050f10050901050702131b1106060f0d051e01150e010302 72
    0x111941c0541d1030065028185c00f070360294510800d1000503c114a00071241d00301160406401c056201016030340100c10f5400c0341c440e030209440c1664003840000c0c02403080742c100540c0050307035803004a1164002d40803481170b1155640c1030403100003a030506980d0f0f4489441200e915510282c00903000551444440041c2040110f6050030881c1551703422085e9061140603240d20038100000101c1010858179190000c031007809e000d41581c0c00c0086640312b178401d084003079000d10301520216011170700c960f50100040c0300180640d19002d12140e00103007040c1c02500c011980c4244000046503518001034205000e01000b030030b00d1020010b1141c00d0b54144c21044401d41404002e000400c0035031141c44a41c03a030548441c0e40003501000941d46481c02500540b00001008140d140001c0c06032800500103070058012112071410441040000f00c0f1038200f104018094002e50b00e40b00384860f5120005441c0c0714960740288040d10b00c1d070303892a11200b118401c400c40c03c617400c0c0041004d03040c05683d480b02c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 319566960 1250 319565710 319565713
    0x110112020f0309100606030c0207030807020315180705150304020d0602042c0702120409020c07050d06021e0c100e01020c070e04030914060304061805010e010b0114071211 75
    0x18000203000040c9410440300003c45400c516559001c280c054400d005c00303040d060404000c02d44417000001c4d5130b104d03240001403001000080c01019980d040000d11154002100f1842d400d180c40c43c0250030850303011081e100c161080e84030200d803c2c90011507590b150410040f65a082d6540c91b000c000084024420944a0560810001c240c0c203c20f0f042031000c1f204102409899a403960000307503010300c00144850308540006050b400900e04140c229000c0b2200754a0150302c62100210344d504080642d13000b9176001c03103905150003c104054003e0004400d2000340e5000c0048401030302c0d40181f080c4601c3c00745681001c0c4c155201242c0c140d104007294040100010704051100b10510701d008600e0700032442e1202400c04100030150700c2050500a803510786075520241002c04007041076400050301c020102c989420a48170456400141c2c0303450150003600a111038200800e646008080905a0a000405000000e4400d1400d00219200a58441d00006111261030300888240100d00360002c0c0302d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 319568210 1250 319566960 319566967
    0x6060307090f080a0311060c040506070c050a090501031509020603180c120622030507120e150913020723030d0507090905090a030807080c0d090b07140711011202 71
    0x907851041102000307020fa2200504544245082c0600725444040a900302036110400308003503a440748041d142240c00a031103550701e40605140c071441c2400b81c0e030003c54005400a100007481312407500070f94100c0c0e01410032031030070002101000040d104008800b940150f0100003007201c0404075000121080000d0303094820419150300029100c1c0002104102c4580c05001070040e01d207101c041450314120001c00301206141e080c0c1d0058003070701a549000d0a4580c58004640e070b0355000c0c00144403058401010304030503d03038560f02c0324000d800074800180181c0ca0201c402d50180081d2080312a495040f101106030085401d16098203004504104103550005014020f00702d10f007802210b014248585580b0300d010709000811007142c80007482181c0b281d22600c21400465003150070103400280c0c0740352203006035960104c1d549081c42000110401c072850500307001c1c1880302e0031000314041c03e42070395140c60b040b0007484548003a00902e28090030740c80c0c1240282d01a507000704000d6040e00c800450140c01e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 319569460 1250 319568210 319568219
    0xb030106030809041b0207060513090e010603110604060e0625030e041a01050304150204080d081005180a09020310020307170105060a12090501090203060702240606030606030709 78
    0xa45603668021509818007041d080c3c0300b440e0a01a041c4040d03000009030741c800980c414029900d00e00f51150710180000014031407489607002e44814054403e0a1f818080d098240c2200c900a04252200351080005a00e02c2521840c10600f21400c5506540d25400c0c00346481080109a9012404800c03000d018400001d04400c0d00240c140403c40c00b82c1c46143e040d510000600003a919031030085e0711005841c1c05916410782e0400c06403600160401150018a02900034010007440307640c0124032248581840101c41641c000e2206101780d0040070b05000c400e40c0c42003800306400c091010f843c0c1039029400000c0c0304652590091600d58001001c03901101c8140240c04201e900c1030722410005040e01385400c1071040c04613550350040809840d6540340485400c00201072501c83e540310b401607500c90070200c05101094100617003440e00201a6441e038102043c02a40d00c131031062007030700c0002000700302c000d90302048158103124480c09001c00c0e00d19681c850410150340e01c0185000e00340003c01e8400318 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 319570710 1250 319569460 319569463
    0x5040b1c0b0405100203010308070605090106080f0703030e03030a0203041a0921010c08040209072001050c1c0c0f031d0109080a0215060a0605070201200115090b100e040b03 76
    0x314894000e81602040e82010b041990818a00d407240c0c1d50b4042c010001003001480810440e000d1b240c2140000070192a49503078680942541d40c08107049126244194400400220344035044a120740c841e41407241c4a60241500c07405030046400158009100406c910780c412602c040803000405d401034038061003080002c100603980200d04000001302d0f50680f0058400741b18030308112105007400240ba00c0d00794000365203000c0c020182003c01036004400d1a040c0041c0c045620301d006064000e2103645804d085554154009000c003d844c51500341a8220300798451041000a0f40b1560704d4540520f242d650550280c52040c040f1115044411080c00050b9000e100703000da82e9209460b5070340d407000e007a90028504000310503600103d224a030b050081a0fa12520954200c0b44036003017454a5480500042c0d8100c0c03441070030078580c80d0581d100814a0241988042080240503004591081e11200494100c4001980840c0c00080700c401c0e1a00c014050140701d01c410340018004640380c600d40700403d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 319571960 1250 319570710 319570759
    0x10605150405040c110f2a1e03010f020316020732010903021003050123060405040f09020604030308160815010311040f0801050103140c0d1709092703040f05040b 71
    0x86d0b85134000c031044040700c500074852900e00000f0521041e0720f01005200150300f821a030114182003040c4d41500c50880d89082d040180c1948010700110340b01d2800e444140c1c035100c0c240110354010f010b06440807410380265072503040c01085170340400000f0600303a2801d00b1883d0309640401e040c0940740d0030000042e80d4145100b01c40345070356503011905514110004e09001c010070f0801c514544010301e507400c40d88468055a0480d18110b50200e0181c2503085c0880040002241c060f40001001901200f0b0541214229008148011400f40001d86900c000c448181040c3c2d43c14440c0b15481d852b000701c80d0300c00d4101c0008991420056032a06944580700030b1344083c40d074443c10300c1e81d441e50010010700026411844e001086400948120b01000b80020143d10b42c1103001490b840140044200a800300810b403048504007400e045003e080c100d00a85111614030020544417004a154511070000402030f5070844000c0b15580009a00f02020840605496040113800c02111030381c3d03c00f658080c8081 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 319573210 1250 319571960 319571983
    0x10240201090b0c120114220906060305030a0212030c040e040201020c03011d0c0f06070201260709080610150f0512130c08010b090408030a090507060809010605150405040c11 76
    0x8466859421306101c00039988168081c1d6007003125103100440c2615810040702404e400042c250900840e05a0350b80000c00e1116400f414143c0ba00c4404420080000014842c41600b41c08861000c100c009441d00588811070381c140c690b000a00c820400a5564195290040d205005451041504001007800c440008444071a4591803600c0ca000c1094240a885004081503415040c3d813008840803031454495458020b04004059440c400c205c80200b002c081c40342a03803c03002c2c1c605d04002000070200702590084101c40d0003201d000c40c100d9910500c03090f0444014100060391494009010384890011500910070702102300802d0708114011030341944101b05042c1031801e461014105640c1d04415500410441ea150040c003000c199110f580b85e640c0260f20141056880e0f5401c0007060180c41c0c01e05000301350703108940c40030071800e40080345144240c0360500200f000503566400c02c03210015081c401088050f04120502c12400c141d00014101c04680c02c100c40580c00d0b02200301d141ca1701c0b200c031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 319574460 1250 319573210 319573231
    0x91a12090d09050d1a0601050c0f06060a05010804120f0c020d0f0302210d0b010504050303030a0605010311070201050f0f0405030a0b01030203120a0509040911060409060e10240201090b 81
    0x7100294104801c01c2c09070200383c0b848a046955643d0725001c1c0c0840700d03210781e03034151100005915607101e0070807502907c0318003064404495656914036030f80e40054818600c1035090704000b08540d4842d101492040e40c10190321990170b45410390a503009661141070108001490840300096110a004a00c2007031041540e017600d04d2050400905080114030442800d041d2080383c1c0c0c0800c01c41c5c2c0207454035884022000140c000602005917290b1003541d00c0903406000100401c11401c25503840b0f0f108651003a24280503c16112175200c1e9103104040f0004d010030b101b40a049000003031007014040e0345081c03901301c81c0341036101d01c0000d107400111142154504c110100500c210308040c0301c802c1120b69842106810440b81480c0a80103000710f05000d8040c0f81e440c0480710030f2001c0f00c0740c02d009c4054040c041a82e51a1621225006072185005aa45039600040415019100c410f560b8044542c108503498281c00310002e07100c0b0f101c05004040007199200c0b40140b0204a490003081c0c01501102c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 319575710 1250 319574460 319574473
    0x60b0705060c0c1b13090b160f02030a120f020c1b01030504110f0103090b010807061b08120910112208100c02280c0f0303091a1209 58
    0x2902500e08000200b110145030801d01441103070200008492444003030046a00350390284103000f0600b0315080d03030313658110b5500302800343d01881030401085000e4406541c52101412000c90b05442c1000403c1e880c4006074010440c0590a0f8807074080b20b0085508620041803401d0060b03041c50513604200700c45043c0390002146000c021580c82d070b00c41003111080c241440580340c0360302d0b69694500303640b00e0280a02520340c4c00004aa00c6981300800d05903000e03800710440d5859a200036950402402400003080c0300001102845041c1c811b000d03c0d00e5407141c4000d00c3c010031000082015032015080c41424452080e1015501d0054010704110001312420360f40c85444281e840c0a0009020090012070440142c0500c11888041030700040103a039400007042d401440602280740440c2c400800c8500680c85031844040f013414500800814047d010700700c0401d0700d441841030703800000c2c0b0006022074420907042140d5074503e4043d410180440040c1420400190100e80b01074008841401007600013a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 319576960 1250 319575710 319575713
    0x50903160602241014010e0315071b0b06060903070801020409150b030403080703051305060408030a05160f1b020607140706090308030f09010e0313080d1e0e03010609060b07 76
    0x1d5458440c403040002405080b41000010910045080e010301110200810003981c1176034000d0b00280d62182002e0101c4000c070300d241d90b24414038101030390707560000b40b4100c204009a03901616114113a68021a01952035100c00701000545e62100c5a020342500a811001070782d00d8081c4091f200402c807064010a580084070001810f60000c2d40082c010348409205010100303600c401c55a034020b1460400090503261500071011883c44050003c00f644616030030401080350b414003850140e0112101070100362562914140320000502041e40064102d49202c48014441d07560890b42c543c103c8421442c80440350007080d056400003c068901c200c1c0200300802803c0b04101040042a10380b409030015410359641da025884040d222105200d1a80d0224803007110a501c070184041d4000101c079a01c003d00246901a120b4511665043c0d0107201d0801c5040c81c02240107540d5900341c107079050841300e00747c8019101c190a041c0c03815050366945c00701082d21413076403040e03c0c0031b02049940241c4030b000f203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 319578210 1250 319576960 319576993
    0x70b0a0305060103060608130c05040609090b09010b0d032111070c170a06020c011803181415031008060712200f0f070f061a010e060a050903160602 65
    0x1800b4141014a055010428140e110020941210192000c01050b524604007a14a00f00315000030398042c2c60080d00203100340d080da01034040c4500c982e081221541d1140b022030f081700d4100340d086030000800c10310b0100191084d5811110314140211604580c903818075070100701c0c6c03000d44c0804a100000500c1d0402d0214000c1550300400980350820030307520701c00d0b881c1744d00c9174000c90b00100b8090f000b01e1a01d8950000b90401c05002d000c881454104120504004040301c01c0d9149188482480c1d80307010503002c0d00761390748111410014013030340f0740c030184040b00440a6200404061140380f0a607070105850710300f031101c82d00a44980c0e50f81e08029202c400031408441040d07102e104d9800305182c008150500074019510595004400161648a180e50540280c401d80381c0045c2680600361140c0204000f070b5002406d1541d155003070040d1118000019168030440d9407250358400303010b001103a001c2c0d00c41e400a150513071000c4c00741d9208942900d24114460455003080d0b0158003da0700503540c0d48030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 319579460 1250 319578210 319578221
    0x30040905011d04050c060c03070b090105010317030609010312031b0807020d020f0703030e03070801050c190e030c06210f16050304120305130b100e090a021305060111070b0a03 77
    0x1a160001d1603900f05642e64070790300c1c0c50740340c0d41030301a01001c108500e0480b000c2c0b050fa07280940180c0600c100b4505248018000d02c002d010856031140403150220703200800c0b5050b01d22405002c1c08495090342145c81c2c8481c1c011010440c00d0416440d042d649544034500c030a42c1d5280120b0352a540003c1c1450300f0041e040c032050140740400c540c000543e4040c94040054850220b0360581000b200740040c0201090400c1d48681044100390300f0300c020300207854201002081820001e0b400b20542010030081190302c54141c020055055000d5000b160131031900c81c000303100242c0d1180e00490304c002da48010815800044800c082c50140403c00c001441d62541641c64a100750391404d20300d54500b981da06103100700c01e039010724100360307560b03000623541302c28041c140500c1c035007010b8440c20914064252180c41c032520700960300c40240040125841c0d4000040b0f07000c1d01940204030a4001c0d042401060042030000c02c1141041001d51012110390350520559000c2c1c4009207485a40d20b98661019050b9070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 319580710 1250 319579460 319579499
    0x29040201082211030f030406020c03011401030f0201030f0e070905100f060915051c0e0111030c070605090309092d01030201270504020d060303030605040e3004090501 73
    0x8220720107400c0c5102c42c1101c80d6200d581c001e20003141c035004040420b16000c82c1e0035520045200024011802c03e400281d42850040118028042800302c098500ca0800c428400108446010a0383c40c00541c0260407007009000394400000b0b0741c03041d80301458600710890340004246030b542c0050041c240c2520a008000c1d040070002c041125260050082c0701421901c507a089491496858825a903c600201c5002540c00340c0300c164001011072070b5000410160b071400b19250300c0d08003910a00c18400301581e2042620241311030401601d0748070800544401030400145000402c540b40303455496903800c134041c001c0380320000c840d07800c600c421a4a45440307082e0790042035054001000182ea0200748201d95070302092a1540142e6041c480c1010030929411a0f64410f00224040c0389202c50359104404580c0a641c00f0f00543c3e503035100340001c407103550254000681040c501c55821082000900a1541c0703000170030348100c103030071070a28026085038105621064071040108540c9040070748448419 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 319581960 1250 319580710 319580731
    0x301050105011e0e030a0809040f0b030309010c0503040504232530020a02070b0408250b0301092901021510031406100803070807060203042904020108 66
    0x5504160010340301080c42c0c10b0003c00301008140f0520081d1184600c2c0c0c1c641a005021104140c0c528130389201a50040c03201607010701d03d030000910030404039000790760105401601441c5008000c500459280556a0050311940b00c104070003c0d0945444c40b4011840c410008404146d01c411a1003401c48030010700017070081c60403890144600c130f80c000c1c101c084400e442c2c208088001145107a038007002c4005418031000d42441e484107420780990741c00410068113240c0c2910411600d5208924035130055000d442d40580c40140c100050000b403050031307580402c41351400c18074140d07511544c0360164400d8008a2499803540f100c034000088541c00c5c001043c080008141107081c5400c0001d55805c4565808200c1410340400b00b500c032300c49403c2800186411600c80483c00c0c40d00400da61f81c4600c00d544243c9152041d110002d055600842940c40855002d030702a8036001290b104c03c00a504003400607101064241d035140310005032203550405000080d144402c0301e1034140001b4000c2c560050001e201c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 319583210 1250 319581960 319581971
    0xc01050f0f090a08030c0a0c060c0302060105040207060e030c030405150a0e0d1502281e11100c0c030e040216020d060b03010e0f10060609180908040609030209060301 73
    0x8030524040d68112084071141c42c0d01c0d141d00380001566050b0030f500044190000288440d031008011488030b030040e0040700c01c5c0508950300c03002100d203203400310070103001038000400504c05450f0540061660f1402400041aa003204004883c115400380105420030341c0000b8041259082040644504d00035004180c0e091140b084000b404050766a003080e84a401c10708109400c00243d81400d91048a103c64119110503040131010414100343d00c80491511070807042590542c840c0b404901c20501007414801c16802800e400d580000c82001002d585000c0d4062034696111540f141c860010195900d041040c446424094140300c203041685005600421400d1600b1540702a07006101d64151958803808145060000c01040b0700c80c0403a81c9542003104043e07032008001040c14003400072509445014800c24401c02c01c4070500d100324400300c2c600040030014003403040d484c0f5a4542d0107031703004103000c41e031540c40b01d0091f481900306502191200c00c080c019400c0801c211540309070260000c215 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 319584460 1250 319583210 319583227
    0x20105010e060a1202040e0709231509090138030c030d0e010201020714070503060a090209041101021603030206071112040e04020d0f031709010504030f1b0b10080c0105 74
    0xf0188840c1c0500e404c03002c2d2100340c42c0c00719240d81c1d101d9000280c1030b2040d1a0071076220020080034004603150406e0320300c0101807140d08001c07041c0f101d5010741c00d84408424502501018002c51210041c5980311b255a00c46144c81010004258035000141040050000c06d181070044025483c02107090b5000b644112002409502c0005855180c24003601308001c4015204004034064400c03140018008400c1c43d903418900b020024003041603da04400740d44150b6505c10308203040310f002d028040c0d40030a400f404100032030086c202d2404891070601c145c0303944991081129500044651007100181d21180400003c00e40c000034025041c0b5013100980040d031944100270344140a1030140104d03440c0e0742d501090455031802400070803550b0150001850643ca410040c003141540000b140c640706451000900c3d844041c03003803511490b415100c1030881d80108904031104d45020b44018089000c44001e10003040c4913a0445120700180340003206140c3c1004032980c04c2413468007034541441f409001801 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 319585710 1250 319584460 319584469
    0x307030c2f12010e0102181008040b061009030204091104050903040e0c0a0504051c0308252f3406050d1103010303030209011404060c0f050724020105010e06 69
    0x141e90000440d907991a812031051280d00500e0080742c0000b09600c0001c1d010758414807841c408400e160112400c0403c0c1c41005400d80e0604070440d002054400164001040c0f032030600001d035001c1e003581c584036020507100d5010804450300200b05403203140000d100c441c2e292805000d400e42c460f420b000a1030806142452011002e0409080b44111101c0400c04440990ac02c83c141c80040c00004c100c048548001c4d003d000385030104000960001c2d184400003124580c140d2113030045d49003030380810350546903d01d8044074803011205204000c1c50030101003250100e10075100480d014a4a80580080c469108940680c00f801102120b90805210400300d4100b032203613804000c8401c04d003444c0340c1e105100c24000000b04120304e1140da1001c40407001009041e49680900700140e400c1e01d0f143c2840c5880b854558050141d80304a40004035071581c1d0070009008400380054651140084510827925296a1014000024102074003908058081070b47c103503090140500401421541c00f04508200c070116 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 319586960 1250 319585710 319585793
    0x7020f0d050306040b090c34061e050c0c10050601020a120504080615042906181201050912090315040311010614030709050c03130c080307030c 63
    0xc01d10101100003a0b103600c40342c11500ca0050020440c13000c529000007a0b1600350070014244210001e0080400383d280300111038607076801012000a0aa03a24a580b81405400481c12101c0d1101d510443d805100c071050040c580280300c800c0316580c880b16891100c42c034004001580291850070300301031042a980204148508a810100f000862a5000c100360780c1d921a03580702c0205031094804000c1c4218902444074840c0c00102e4084c0702010461070303101ca00c4142d00004400342d9102088800c039518101000f030440300040b100c5816103204c0307000060401034022141c0e8209944a400300400808144191815001100461070034064002d02003a910440500300002d1008810082001e00d8082d0600444520300c810080c090240c0311034075803078181210740c1481c3c005e1241110202d0042c4190080502c20400440300d94115501d40107480118521400c058504080c1c0d80f2000c641e10105000030880b40d400390b1580c182c00c85051074120b50003890202c841c40400b00c07000b1001281206007481 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 319588210 1250 319586960 319586983
    0x200301111603050f0313020909160e070c020a0e0603011409030703030b060f070615060c051209010e060f18040203040206070201031d0a03230c0303010308070809150705010507020f 79
    0xd078891152600307070f0700780c410100f003034048030f40c0401000f4045407404c442102c2c00e40300703540f80803030303a16200c0c81c990740e44160310307402c1940c041c00200c140122410260300d198000c0c101d1601d02440004e039004250b44000642207950340d00c0010f802c00c200c5090901035140d000c0c114141410503468015412904da00031014002c04043c2c80700303d1030300340b81d48684c203131128000070000c0260740324003502c2c2850003000c440e800da407020030070010006141c50141c020076008981100203811013541e80304507405143d100507441d03418012812106082d540b26074000e8600500341c4034000703a455040f400703500d00c0f50440030161031041c0c2c0104204401602c54a007038a408650a00740414480000d400f031111a20030000c0c41c41313542c415400006e05140e4800c4c81300001e0400c0c098000a004908061200144a410040101a4020030041001449031002031110038003d03601c0314100640c41d070004012058506885c139200c2000320b81c000034004207120f000d820111500092010031192480140c603004050074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 319589460 1250 319588210 319588237
    0xb060307050d021e04420c050a0503040e0106030b030c1309060b150a030b04020901090605070501021c05011d0609071103040b0304230601120605070509030a20030111 73
    0x515216881e426442089162110407610352a192165070503600846c00303e1410000140b2004400c070420380280091030001000c0b80c0e548069403074440309444944109504680a105e1408400c0200c1c80600c0a0809401440740004141d4500b200042c10754141c0c2844c58408c0c0c0203083c9044181c2d9804008000c101410013021402c80018100340c401090b004e5000c83d042824114241c003810894801801440c8075602c0421000006000340400c034001c0c5031036580800c41681c02404203900407405842e050348180000751401c2102c1d90540b0356424810407101d00e1a803100c00503c44078a1400c03540742e21244207107080c0d003940382410009502500191100040c401c2c2601d12800705038092045402520140c9600359a0342014500784000442000d0074018541c10107048140d000e01c00b081aa0480f03088010a41c8d82c8003194945000a25015083c0b00600500f00807001540d1810300103614031600500c00794600040004820040c0c42c40c54507880d1113649804000500c0b40d200100b600d0000a903d030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 319590710 1250 319589460 319589467
    0x8030304060506011115191422081305091602060a050a090602040803040e060d17130e100906140901090c020321010513050103020306060d02150a02030d0b060307050d02 74
    0x2001031750000d001c05180c00143c0103a9450703030341d025000e0396000d003d2010305481c80004980c400c03940044a804004d07000c490456640855a02d040800c2e0104441d00c1c0d40c40201070780010307982c07807001a62007000c001c040308403c06e41c00c03c981d01d060840554007140000322504404002900251140740040800a1066903400410b846607450b6015807200c0358030500440d5230340e845101c815520b81280c4900c0d0764114019001910300d04200c40305500321580100c0803020082c0b000c040032140c0d082614012004000d004000900541204890340181c19052503000c1c4a41800d540800b42c450030f40058a948031058090040f40c1c9070400003e044460300080040c8a810f5400701300d04621440700c0340d0f0310034010074205902000d00d17101200d04865044414a4a406248420b6001c1d28400d100c041d40c0b681021001641078105003040302c206600c0204800401ca01c0d0100d130314000d8001c4810746006034400319110030280000e10510008070320890f400c60a40c50004d00040841c030800000350407031034010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 319591960 1250 319590710 319590721
    0xa06090c051e03070611031611130c020c0405100b0705070f0f082b050c15130308090705092802030a0207051c140c0708030703020a0219080303040605 66
    0x2a840805000d000b4981c60180705290a20740d9140c224a0842d44070340038030900010001c3c000c21000812400030700145041618040c54000002050042a606032021b181004046c0c2d0f41d00d68016a0991402e100241c080c101002c001c1ca02448107112600951a10003071081601003400e0007421900c81071200c80d620142440c24900304015544800241030030101c01184034817100c03044406503501031040303501003030f0240c02022200b08545c1d013000c4074800c0c03920100260340c8500002e19105555000b11141742e488014050364210040710b11214a00f0319281c95000c00d40c1c400c2003241c00844040013010765504100014403c058050711094100484008031460b4072406118001c0f030f491246c00854581c600400c000d0041d6018500440d1280101c88800303480f528510014408282d9942e40c003150380580c282000001d61000200004c94451482c0004050108200030f10445109a02a00c5646e0b5184140310038404c01d801404640c031010301040c0010134001058a03446500104040b03255100d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 319593210 1250 319591960 319591973
    0xa05060a110601030b1b04030b010e0c09030d05032202210a1e0c0b0c1b060724060611030904092904140f2104120c081e0a0609 56
    0x40e681c10200e501400c4000018000580141c0344603c0c602250100501c0191075142c0c1030b8030690100401c0b400402c4010700140346020390050b481a282c03e0501e141402203000240341500001030100011800410406117007109014000ca030303016418500c540d004a0360019405110322614207c1d149c0b1f85603560694920704000c59080c03aa005210504030601c812415917480c00040e20907251001d09600000343c0381c030071008a0700da80c0302c440c01030401d000d0410f2409a46030b6100000c0381e44041c0030300603400401c01c0c00041019140c0500d00000035020903941c1c80099511940c0544c0131300c49100000000d6020200403504040301c100c0303000a800e60603103000c49001d50103144104074442d140800c5d8100c41280300755540241c0c01200c80d0107903000c1c807a8039075503148500500c8a10b81c5c0c10201c4c420341d1000c102c03036642e0913a07004222a1810240c9411b0680c94000d294801501c20b020b0480041048a00c203014100404002d008820a101c041c020107984da10308018009000d40c0e03690009400f8441c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 319594460 1250 319593210 319593227
    0x2007021c0c06050309010c0903050c09100906090203090d1701170a1505040b0a0605100809030f16030e09040305040b0d1d07080c060a081603060308040e07080f01050a05060a 76
    0xa220380c2040c0d1854490b603008010b07801c1191505907039864102c1105505020700c182e0003c03254800e000381582c14429090100d120300103480020000b1400c240864507028038011200070b84080c0c01d0050720f03460003114103032501003a1031101c0e0510038022418080da54501c01e034030381505e860240c012460114844183d00c0d0200621020307000401c0e80c54003d055038541c2d000307240100d000e940440d1590f10b4482600003119154854980d004d0380c607007100e0500c94000c000d5a54405c007404150303824400c5c0411a40341c07907440001041c0d0034500302582d1100b00740d00400d6000c2d03407280a5802e86442d15041e0780140c00c2d131080b0f00403180120310216600720310074140e07040f0410881d40e038541d500b1280210b001055503042c41d4050b40c000d034001c8507010507060600390300b0784201c14495540c00540703885940d540d40340181460048010507456000c0271001c102040700030401007144070100300552a0120009104581c080d00c1111030300c107a98010050381d9110000308041c6c0707001700c0c0d4059032540300c100c00391140c12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 319595710 1250 319594460 319594463
    0x302151e070f0809010e03093a050607020f1f0b1905040c0e10080709031704091a0d020f04020909090708011d060a0506010e09090d032007021c 63
    0x64030030001200d510150701c0a2085080d25458142d88a00700c9050982e405210130149903130092003000520304e040c1c106122507a00320445110010303216954540c8511000c02d000d80c141c1401501c80040000803c070706035004070284003a2266001e000c4015444080301040304030320081c3d0307038424030202443d076101061349080109980c8181e040c0038151a5058424842c0344d124524240c0c650170b8841c01020149030f8007500a10160501e18070800607900d075580501030800b0012444000f00c00217110707246208803801400d48054455180c43d84074400e5816150005c4603500c0c0c0d500d40c0405a44444081c0c08910307504549504684a1840110700280107410426900000101c14484041c90210b5880c0690714202e0007402041c2030340321454100d10514031a044540d20000c001a48100183d002c1a003003a41450300c8886180000c00059200c0380c1030b42ca4500c00d0304021030a000c0c454040c030403400c4800b11001c0c00810000c4003002001240600c40c00a070007203441840800001d08281412031905 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 319596960 1250 319595710 319595761
    0x100f0807080c0d140703061203080103080c070f060503060306060a03081204060e0106060c14010b0105160501020f070506160908030a11070f03150b0901030c0b09030a0503191b030215 80
    0x5507130350300000000b1042940d1141c0441d1038003202260003040030310301d200300c960143c648800c103074a107603607a10a5611801107420b07540035403e400304104a0b00701c3c86900400d030b5039440030b4403404c04204150509801407d031a200d403441c440204001070549050314251023610340d48010315541e44c10880058000c8107540304c40c1c2c0d440c040c0042140c1303800604002205000708002940e146000107001d003203a40c0403094502241c0f0510804e8840c1640b2400d68036140d208500260502840051100240c3c010b00c2045036180c00c05420054400313a0305240488152292074460449841c01d0311040c2c5a2140d95103032410040710b0811411445c00c00c000c1030004100c8490300a880d560360b810854503c0310401504050142803e486000500c0d00c030081905a940020720030004074902481000305610451100da0035005641c0c03100082034007070015194902181461261202e60100024003042030f0106400720150420744080110703500040d00300e040d4500360714141490f10340d540ca407806452810401d5130030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 319598210 1250 319596960 319596971
    0xb030402030f120a02010e0601060e06070807240c020607122705150a02030103110d11091528030209070c081305210d030f090803090606100f0807080c0d 67
    0x3c80e25a40002c150031035030340c1d0007005120f8803103500e680c0b610310138851000003801c1c000040500e8a4041c3c0201503ca200d0f000305454040160341d000100e070100a0000807a01190012038031440d1640100c142041142c405446686000040982551b14024070715003030b540d032030100000f0042c15200d541401d0300c01c044003418503551854002e6075040e41c00c086e500010066404900203102c18000d480c16070b43c1c001380b4118118191420300c03000340112201900ca0a140a400b014151150103202d801100c01c400c81c081c8a45400341070003440761041c862401101c08141c1c0000c1d401d5110000c4a09a9604441b01056030311600030454440030021030190030030b0030005841d0140c190140e808421644151109071143c101c8a1060040340f00480e250000303a0442d9208031031040c444d0380444055003609200088840c002e0710780801d43d81003240d030707000d1a900c94800c4c07100341c1c41d11103c0b0303004100307603403a20001484260100420070840501894244529580407640182c0300c00113031543c004102c4010480d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 319599460 1250 319598210 319598233
    0xe060114030721050c1f080c0d02030901060311180604020702030102090306090703060515030607030c020f0304030615090e030a26040b040c0b0421081201030f03140909010b030402030f 81
    0x4443c02189012a82407040703120445140c1049101c040c8903074142e2000700c825520340001a55040c40080401443c41010049404920346901c0914040c44081c8000100d080c1103240c2b4041e85213400c1c00c034510650102040345182d01a40200c0c1d81d01990599015850301060b02c0031a02a004101041e58540201800c1000c06100026480c085074014030081c8000c0d2600350b04440f0800d801410079405400601c009041503000b6000030180c0d03130244c41110b04404124842c0d81c119001604200c803e0383c1c07200f0b0340008004d01005428041d04e002d050400ca485001142143d43c1d2040030000014480c0b207810300f007180203603e1888680ba0443c071208440341e107003903d00380c01607071000c41d000c544280d200d0101041d0907a1900c252010f850301f003ca41812a25189a8410040f501c4402141c50f4001042440651952245254001c42c400d442c0141000101d00d805011100000441d411450040c0604c0320036a540030341e1a030456410b004002c0d0b9030303140d0b400824101044001c02d08400c1c429a403a40302c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 319600710 1250 319599460 319599509
    0x30602040303050705060f0106050d02090f060409020d2019020114010909020909010b012304031407050102100902060d1a0907080106020c010206060d0210020a1b060f030e0601140307 80
    0x4c00d0034801e00039200290350700400070080381030a02400c1d0004100307010380032807120f180d0300030100c103070009020b803483d000d0000c00500e10f6400354002d8040d194010400000000c018000c600c443c10079602c0460140d841043d481015004e01084040b0134168042da07100d01a00070f612120b118050a0041c00503580c51341a1800034068541040b402125840006441480c1c1846501d85161059490400f4801d0052140c1e02c0810150807111950100f0400000050b81030071000c0c001056403805007002500d8600060b0506082c08403e102143c206416100182c1d948001c44004840400c400a502034105840c155004088003405030015480400e206029402116050480301030b43d080710b5221545100480c0c0381c8100307640301500300348499418001440c041411540048891045803a00c044541310030300000b60b854181100001845c805100042c4d00088000511015040905c60400900e5100340d80e40750500c203142e16420541c504100503541840302c400102403c04414010b80c50a06801 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 319601960 1250 319600710 319600717
    0x17070305250b011508040803060609040515091b0406030228030e060705160f031106010e010302100306080d030b03012003060f0f1806041d0a0309091a1903060204030305 74
    0x42d11640382440002070b85140d2148580300041042d59200c103240c8a580c1c5d400c81030b4002510a6500407070034000300806448a11805202c1d01e5012000c40d242803031074060081c0c058025007c1c040c415aa0030000c240030028004580485500340780040c1d8400b40c8965403506000170b5124100d020956841e035041141d0b260708240c2c440804a02510805c0d00ca00c542034400c0c1c82850a501c2e012401c00c440c40d80840e03841d080222406000781070003084511110b01550801000340c1003240102c505000500550804004c02440e103c410b00f002c0041c6030030954000d6480b10203a600d0b2041585600c141b200c2500d00390858180c1c1c2e6809048240c0c60a42011640304a40046403640d00401269204148510300003c00000c210809086c0c8104840c0100ea80014898000d04840e00b15071a410b00507001c40c1801031000d4038000000140a0b22111460300034041c84082c0c1c01802c1090030003040c42c05181c80c1c142011920f0034100e84c4851802121100900d0901c3c69a1010b000c0302c0c130118000040c1078002c0000d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 319603210 1250 319601960 319601963
    0x10021c03090b131b08100b03120f04060807050a0e040e0f0615040b060f040302060d06120f0203010f0c09170109050d090312030e070506030a0b1f090e041707030525 72
    0x1a1310310001c0c103400c0c4200380340c90320a913070540d80300701c12154160b099031f8000c0440d000f0203030a8602007d2640e2210840781d010040001400d00001000c20032613500c140e18a410400038035103180ba06e140d55000522400c131050f06c0b58031a071350351018160501da080180c1e601400012082d00c0c1103107890159502d52101564486000e039080c103070840b8903442c01c5801c5822062441c60700c075042c1401c5409018103038022140b400340151345c030f50012480c08007052007208070034480d03140324105102c14070504d82556844040b40c09100d0820800070f045503008441402521080010055409040c0c00494054000c4000c068a81d000d107411080134950701560040c15030703000d41e1a40d0303541c0010705822012a026441c2d40306164121071410700c007502d0000f009680110581c400401d40c80004c00000f000d00200c0c400801c25905202c41d47e0320500d810030403641c002c2a03140b04011700c601d410f8a034450039440811010982000c000b5400e402c00d4004c40654903050010450307122400d181d000140703a00b45a1744c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 319604316 1106 319603210 319603223
    0x3030b060c07030602040f0b0702090f13020d060c020d17071803021305180c01020c13140c0903011103151002010b0301140103060b10021c03090b13 65
    0x308070050f50152400503a04c03441c0804007144141d9692001c1c4c2c0c00a1b090083d000503a03540fa030400e0f40102000c200c10350380c0e0384011104070380441d0315a00035413144030b2200c4441403117071951219040e080c0c0c2c1c2d000c640100c001070205640c141c0b401065800504403181c00251410b03c41e84a10b43c1c5500d0511072070308055217035800541c010301a05070b100900c90740c2c0c5041010000c04024103040800181016090030601d100c0002c2d00c0d1040348500c94000c41c1c1c2c09d004210007190551040703444c1550b50005400c241000c0e400b030000c50340070f01000340c465030800711031110b11803410b000c40c0e00614500302c400e842c0c5942e540c1440310524441c480d40302035550f0741c1100302c90fa0301d080c01303940c0441070f4039101071002c0d41c11490203030100d548040358a40a090030341c00111005400151030030070300101084c4180e10001081c03085014100048000b04505451818021072520503072140348111310404 = true := by decide +kernel

theorem cover : BRFrame.Cov 319424460 319604316 := by
  have h0 := BRFrame.cov_init 319424460
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 319424460 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 319424460 ≤ n) (h2 : n < 319604316) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
