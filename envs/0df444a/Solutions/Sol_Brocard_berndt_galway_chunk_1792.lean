-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1792
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:41:22.435765+00:00
-- url     : https://prove2.me/submissions/784f34ba-559b-408d-92ee-6531b95c41d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 322122302 ≤ n < 322302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 322123552 1250 322122302 322122347
    0x703060b150403150e1006060c0302060a051302040f02090904260702090408070212061801050f010602120a03020403021306090e0c06031302130c0807020d09150507030e0d1101020d 79
    0x40701003c064483c5509a0400703200381b00b104107024220344a1040100002d40720001201c41914004e82041801841200040e141c041040072103072100322400c0f40c0a40c100c40c0000c81486d480d1001c030090003a501490303081250b12040104001151081d45024140449040341c10740b0b0740d5181d5512803080140080d0000000e0380410001030040024010072403005040800d1074020f80d048502d0480c0403506030108088400310340020038001c0c4900c54025110070503c0f0740660400102a5440717241e00c00c46080f003076001a1141005209a040da00556402054032401c140034121795009032419010b820483c514218490700c80c4100050015002000600105d00f1592032134a030510480100b44103a03000220390150740d1240d1003510601900e4070094941c02110305082100a00d4030380c1040704c940600401d20400c2c01000c0d0440000824034003140b43c541e0b030318540c42c6400c41e10044515040c640041d20005040c081001c01d8205012612003a070072600040700d003e100b140e4215a1029504409a18 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 322124802 1250 322123552 322123583
    0xd09051b030706110c10032405030307020d0c080105010603020a09061b0803131509060b01050a020628180215090f060f0c150709050109240e030703060b150403 70
    0x20081c45080d288602d0581e14417860302c002141ca0303145040c0f81500040d50700c1c00350404000c1c0700c8041c50b52580240388180001800c000c080303a035a210314180179100c0d140c9041c0880401084003000400781c00100e009115650b901c10014029400070240304000c81c800b1600420f60314881e00e44900c40b50004529012038480c0e0b45c42d0040c42c0e510241015000c0385d80d05146401280b0020040c4c204c0c48405280099200302034104482200c0072a16007904010082003007010315035000503e503421100c4610041030790512040600040e0459160a804003414000c3d101110601c401041d44003500a4031901070201c1000c100381058445c640342c00d60710120702140ca071168280f200181100e0203040f00da1764a0040302041062030103d8444004015000d240200211154885d003046d0060a003070a00211840c104011124140007100703419a9803803d00682c01400c600c10b001e40340c1c42002c050191007101e40c881c01c00b14083c101400c00603008003888205880c1c611020002c4404072038000001489880c1c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 322126052 1250 322124802 322124807
    0x2100903030b220b0306070c06051315050a060504020f1b01020f040f08100911010e0a051203040602010e030c0c010516120801030b1303090501051c020d09051b030706 73
    0x14100826420940d44800c151919150540c584010014074a4a002d4a001c600c90304030a41d070600ea0814069000f00f02403152403604104035010059001c5408070300790381c1c0c140321200440380c181307000f40603803031440e01c14109034406511290040800709001d000c126110740c144402ea00c144010126182e1041209001054224185040b8120f01c40001341c502905507995030f034550420741207915407092000702040a80000c105080c00b460190700d00f4080041280c461545170100284228184070000419901668601146d0006400300030094203403050020a840d03948e82260041c00003562174134500d490201070000507503c00741200c41c003c1140580b9500111419003001c0d40b0250030704400305524002940300c0004507101c6090ba91034956961450034404903000000e0a04902592030360580c10109074404a000155031081c01c21503075810070043d4a40d00c4061218502d400d013440840ca149400f00e8540000c0c1e0024010402c075203400301d0f00c69010460700703940d14201d54942d008aa00b00540303030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 322127302 1250 322126052 322126061
    0x303070302071416060801140616030c02040e060709080703023a08130501050918060102160314070b0307051c090209070e15070201080a050a090c0303110706050306010210 75
    0xd2040210f203407461007800d980ea140030000745850032038441343c400500a0742c0d484011180182104628584222481e40201d4002c2c8501c0403190072943d00034068400789402641c103d45d10a5020f481040210b1040c2d1000d0b40740c01d000d841d4030f0001850a48006410400041c04400f9240c0003130101030315070542c1e031981480c01c2ca54200d1000d2407814010981409103c190758176640350141050b550b65240c503101c41201e103980e80d04045c0c140007061120071144d88a18290816900043c8502c5506445220060740b910002d096040304c542d10004021081124510400c180c0c07800341e90440d84102d4550101c031182d40800c40711103000403009c0c00345104a1600007031800c100300454100103003000d0160089522042c00311981004512101034a4960381460100d80340c0d00c1115420107030900800f42d0000f418a2005021090165125008504c94081c25441000119440180c40210030340e03900e4050b083c10680707408200719020f0130b40300150380c0340218200e91080c28140e014040f09401c2c07061040062 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 322128552 1250 322127302 322127317
    0x3090f0f0103110703020a030e09090a060e1f1b050705060714120702030c070f0602030f0304020a2402010c0503040201081303090b0a030b030c100906110a0812090114010302030303070302 82
    0x141c40f10854103899032460002d062050196000d00844151814003400c3d448262820602600d03c100401402c14804a42303d2400d6501c90000700d8101c80c86841c943c94241580b09444030031040c1180c4142000c0c1903405004101c6070440c248041110464090b100b5000d2031801422540020300040e402920840c0000041c0c1005008070303080c4803002c03581d100182802c89503000940d01c006084403801d8020440786d0018a00300005142c1e9604207030b0300130f4803805612080b00c031051002c0041000c40d5a07850848000d404203005100000e406030342045120345407030304003501651070003500080031840b5500701d0380301d180c041e118107206443d0300a100c005e01507160405e500700040c01d000400d42804141c003c0404400c540c2d008a84280c8913401c0508240d82016082c1c4240d55044048003c207400c222040c0440c0d100b42440101d01c11500f40072810414031000040c0028030004001d088072854646c424000c020b601d000f0040008921040da100550072301000c1d50551061001070395891003a001132815 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 322129802 1250 322128552 322128557
    0xe04140402100306080312150a05100e0604080d0309021011060402060f12150f0a0e0c070f060e010603140a031202090102070806150102012a051315080a060803090f0f01 74
    0x115900e401190854006a00a881507030381202030080c4940c20b235900c5c3c22583e40c1111000d01c46807504002840300788104091703500303205110790784082c5a5290815030b4001d2078100d0644800842025008004107504030080b44100881d50f040b10310244201c0076401412011401030440b902d541d0200403c58100a42c0d542d8000420004000b2001c02640b4450280c0040c403003030080540c11208020340d91402686450146225050400608407011501038100c4100d001d03c0b591070000d8145500b0820b030300940030300010705240000001142c158000012280034282d1201c9803040035044135142d408030031015000448400c61241c40030900d500a0003450014011074220329502e02c181c03400c1c010300315480440d0200610000c0c00c039580a0040d00200100d49400380118200c22220f404041341321030070314080280218070a4130400310000d0781c078040c0180317604d10080300d46020b0b001000c0701c100310350305c043c1c0900340b40c1e000490364000020b4a8070020000d28200c4111142030034030505c40201d1400b50b04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 322131052 1250 322129802 322129811
    0x30a14070204090c03031d031e0708060c03010905070903030e01030b06090a0602250e010314030706110714060606040306020c030906031807050a0f090504171602010e041404021003 79
    0x1a6110f00c02c10210b5882900c142c29681d1841c18058600c0c00c0303081d41441d218011201026071035802052032280030400b03880c40c15030f52a02e84486882e000e8550070001c0719210f450700340017046501c2e1018504840d00e50074144416a10384e60211480d078000c0c4030042c080340621024540d00e6000b82c0000009840180c00b050904540c580012030030b0a0070ba11a0001d60005040040380b40190805174400c50130440714402c4041c940b602d842103c0405200c0034005800401410403907480c10310480d8000c0d60400c1c818840c808800341d40342503607071060004440001c2181c0d68001810300120b1040d02c02c40d0000c06071814503242d41c855201035449030346420540d0104114003002d5954050285001381451580c40c540030000c004098035021141d00000d10a001c3e800c001c0011489d140707003004c25203032240c0012806031102e14010400e00403035981d50b03104440c01300d090440b00d59000f60302e40c1554001d17a18613498400c1c1d50309100031140d042241510500300318002902608195089194140040c0b80004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 322132302 1250 322131052 322131067
    0x90c0224151909050109110f030c070501060e071206060203090d020f030703030e33070501090b010308031902090901140a09050f0a061401021f1e0903020d02030c030a14 74
    0x40c0a0290303142c2c04010030681c0402031284510302e2080a024044e4403104111444029142d2803187c010403020300d02d1544004001380d0210751440540e10501d90050007808020744802c0094040300d4100e5a03440010f04408524412414501840c1c0c1154226000746140c0200c070402e000e011602913001383d0300120221400517564404010b100000c45c066602c40413130851030070812040b0520481c030761a03001c5901f502e244000f0070015180700d0050711002103a648100d00d103002800350a4020001d41420700040001041c04002401144540c2070300c4c801464691128040d1822800340070b88103504030648400600806100342101c01c0500001800e50a40c0c0e03039552199002e5540469001c45444d18120a01c0031044050060340003030920361110200c40c911080c0000e5481c0880b140c5010310142080003091110031a80c0310b10200e05040010661041902e403800018015801c42100107205400700c2200180c40402a950f45404107030180d450700e0420b070f00c00c58100c030203099a010985400c10140 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 322133552 1250 322132302 322132309
    0x30b0303040803130e16140328090203010c020106030c0b0c0f0708011b05090f040b04110a03091a0c03040f1b030f0507060f05040b03040507090e0304090c022415 71
    0x1072a01c090704400d01d5844500b0840d5010a482020b0121058030241c86c01c05000540c101206514a18440c0802922951061454689800c0300003030790712040640c246442020f00c02d80c0010454900a40003071221408040d404c07822141c4500c000340c10010880740502ca2022080024594200d905007140c103400c101d10307021420a002507000e603c003a0b640301d500c0d06203004008a555489461420042c1c1451a2440030601c0e00038500380c0709100710790311089417031300380e075980d0203040189031070f80c2c0050311030603240c10213402410302c81e1045c1c0e4000342050032040401d2203140000c6c0b28100d510b295500350303111030380c0d5a4410042c41400726130f00c000701c0e28124100c0c60302040320001940250250712030840103081050a0034895003003a8108188100c042a0554010048404588040b10000c0e039a5849062190500d1400d400caa5401402c200084d540031000102600c1600c04010301040490708181c2c040c0e0b0340b50060b2410501e1108180c3c030846240f105d80d80e0041d8400c89600c00e0243d01d10503500003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 322134802 1250 322133552 322133557
    0x60513031709091312030921111209090c030103030f0f02010e12041805090705011101061503090b01120201081501030e06040302071502011e051308040308090906060910030b0303040803 81
    0x5800d002c1410342620081c008420f8641703080d80d1090404200540e2a07842d450000c00d14214000410540c001c80f840c030891040f1008a40381c05040e0507244041601c3c084a9a030b54012a8040c0c400c0c1441c07008a100461031500300e078122a85a125000300d0384501006481c0b154a0103800802c3d55680c280a04041c401800540c0c61500344581c09595070b82000c0f0140194100041e0381c802c034501d814104540003100050000980300242415400351070080308181c00b41c8581d0700005c034001a90200800c03030b50b070140c0009030154494170f2140c0e910303a01c5001d40e5100803d00c01002c0d000035000c00c08039003004180520002814030601d00810074000c28440603141c82010b4070210010b074030000003082420b441c010111a082c4075480240030341c0781d041049204a0300303a403550082050303841000c201400b040818404410390b000d801244c889980f03041000ea90380200291500800e01340000506900d00281202c0b1142d200501c8640c8071407a0640803002006511815a010700c4100000305109004002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 322136052 1250 322134802 322134811
    0xa2417010e010302090a020a0206060910030c080105070e1021020403120c031b03090306150509090102040906051c1b050409080d1d03121018020a030606051303170909 73
    0x25600e040d0b51440c414441c2135007000b40101c0340c0b20b205204818001d036000c1741954001404558200040d1100794100680074100c2c2c5c4010f01c0100d4609002659050640210b0300c15585501c50101032001c0505102c0d07060343c184454030008081c2d5106854442440a50f04944503150b10b00604040c5c80e5039a9040044001112201240741400000101640600d01802300000d24091002c11840c5d541d000d040c41442d404014140e81e1520340c500700c3e069100c01410010301c001003088007241403003004c06e8000e520038059181e6050500401280301c1c1440d14103011403241000181d6880f00036038849500d1a409603160200318440c511002500b40d541c0d0007045821070040c03804594940c031021034441103e000c1c200040410700244007241c054080401550200c3d40c001001d400580d85007810300104400740d40100f205030780b00018101d41d00616070b001d010248030701d440c01c12003123840d240300381c034540242d055006112000c90002d000042c1c1c640f44034000080c8a00d507944c2070442d100300240c0d03219822113 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 322137302 1250 322136052 322136069
    0x120109090b010911120901180b04060509060c041e0b04090e0f010c050f0c15010603020c010b0a1404020a0c02060d0504210e0904140a12030b0a241701 66
    0x2000300090041c0341c2076031030051592540c00c00c010b1000110501550040c071507124028100c890028044607020f402502c07101e03003041035503598000b8620f030010048000350f85c10f56a42c0e28200004200c00400210540145030120549003842c1c941041091a041840c1c0ca441130840c02000024003031072084060f1000d04800040442d9198010991914111034500c10705c00b16170515442c000c91710b400c00101c80e0000003160541c0d81e03030118440000d00d084c0e491900341030f0088840e000005d8640d450fa0261113120000b000130704c800b02d5040104001c03c4e0b80c41c00742d00421002d1a501280c9444c155004104602484c00c000c000c2000c50f4002903400e0308014888000b03e61108200700402500744450f80c400010a194111201110310b4000c14100403040094003400101d03001c1800c1c0f2a8181e4030244511800044030000110b0380f80054030104001c0129000c41c0c101006d41c82c00e464601d50650646080410410184c2400e4031140c61100d00b80340210305000d0140901c08401100443e0503020300800c8 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 322138552 1250 322137302 322137311
    0xd0f0f02090102010b0f090103110d080c0109031d0f061b010905070510090b070f1103031602040509030f0322021203040815060907111c090f050d170c0102120109 71
    0x1c0300064251018410361511540d281c40c12504583e941802c62415681c020b02c10500a020400c0800e114000940014108040100707403004001015009000000e10072b0342c50110900c1e240c80c2c1c05101e0361035050382d01c0d8800a41c0c0da144060b410018054036818110174080c1318208070748081c482c00c48140740400d544541010009201509045115440d03580c1a40344c950011440c00018044601514000403d9840d8641a0100307200072402a803005201c000c0c1a0b03aa41c2c40b41020b80820181e402604a0003a420000001d41c1c118010055840c00760424040500d1907550b01c080050080005000c4103045209044c01805078550010045510580d00c00030b41d035803410a90413601e0202180c240800c02d503c8001046130b20f464800303020741c20a2481c2022001e180e090704886042c01484054000c0c0b81c0298180074001c5a8880b080703031308450780402071790041c58661050014544a80401411460071058011355400c000d4000b0041e030306041000508141d074908941c0a000000c2c3d001c4841c01d40c54 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 322139802 1250 322138552 322138567
    0x20105160308060925030b0109051e040e0304050102150619080a0615050d0312060b0c0106050913020604030f0c0803070b0f07090e07050901030209061201080d03150b0d0f0f02 77
    0x8403081501303c007035060300300c400c5070500d60030a640c410b030011003008151b12a030202c7c0169004002403405003074000d0009242e5011401000743c1d00e44820010392040d42030002400e03516038044110303000e991040c1d005c5c009064440c0e40a4150680141410350842c0c02c8141c0e1024481c00c0c40e160302c0c0a070003c00013805c000505401d154041e900101401c1c450601c08072070400c202d959000708a0f880a51605014207150b500005080003010340764032080302c84e6000030300f0103240c3c4410344c040800e640040310020f2880d00d036074a18015540303288100a403c001c0070402400819154000c00b0002c03841410b20f0044240c50300459419a0803100045078070603003aa0501c030381c0149070f80801e94010014038185034014540495051801005085601808000100c440403644682c0403151904809022155140b4082060b030802c61000d11800b44540210744004100b40d2290107200341c3e24000840036500d00c0d05054041c07a2580c059540e045c151943c40310491141788040c025020400301181e07006886502 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 322141052 1250 322139802 322139809
    0x611030c0a030806030f010b0604091109031605031b090109090c03080a1205010501080906010e06030f07030c0312231b0a0f05160320010201090807081c020301120f02010516030806 79
    0x1110301078106c0d90501c5032015070741e00d1784003c1da0100c48a800c400300f0701d10803210010035a8400c03004504c0d050b0140040c10303049111540c2c3c5031400c49100381d0442f15940c0011441c2d44848030700308403466000480000410003180f80c2d81005103132070701501b10001c540e82c0e01d40d00d2608641c44000740d6801729100341100588180c0c4d9200e0140142403e003080e0005141c460012605c4001c14011001c2c1074040c0c81c04a010380c2c600b04211180c5900c1c3e00708443e611034990400303070440103c41c030084409000340150000154450100c41d480341500003d0100341e0300c1e001d6985041d0360040c41c0300f1489410546100c10030410104600150140500302c001901d8016040090600e540c0550480d810001d9103010400a41d0304620181e4406c00102550039120a00004074007505401300b01500600c070124034401809840d8006101c030110510341820b8025602c80044141d0100348125402680888000f40216007400c24000c0110320515001d0316002040d408101486100d107000c5d80010049010402c1504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 322142302 1250 322141052 322141063
    0x71b090207020303071419050f06150a090b04140a0b010f03050601020d030e030403020904080c0106050f0d0305031e01080a020f03010501030b180106090606081504060803040611030c0a03080603 85
    0x28805518001c1d8680209aa07482030742d000515444640380000300c50b0405200558403418031700018400b140490074500c0d6074043c407800c41b075207900800011909140c18801d038000d108101030940b0350403600e0541044002c02d0301701c1c2400c1d0080d844032000e10301400d23003240e4240300b018681400140300ca44800018400304441c2800c2c0c081c9440c043c20b00c0f01580e00080c402c0c010302802c0ca00411031100c9100080c0c01c40c0266480250050050014001003088420240c0040300c0000001c1100d160344000f0018260f500004a80e0000192025803000c644035500450380003203003091491030030b8007400d10048219400d910040140d04004081c0c1d04500d03002024060f1044220b00a00c2b0702c1d4150707122501c3c0300741d028015200412110340c1e44001c1000039004a0000c1543c00010882039550324400342c00c0480031103207000880d030109550f62f05464144504030a4034800c0b0000c40c285410f00c0410381c1c5070301c03101002182034881070110102d060310400c114000140310f0340d0b0351001810b121040c5407400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 322143552 1250 322142302 322142309
    0x120d1d070501050316020a061b0206090312013302030309010c0305040b010501031e05090106030c06030c0207050f0d0804120c320f04050405150106050f0f070c0b071b 73
    0x15048800d003004280e92000a07290880c0b001e007984c039600800d01e2010b034644140910010302c3c480c1000508c4102c00b0a040d9000310551058080d034413103550302400c0c02d1f00c91007440007401d00c04800c0001800309540310b412604403031a00e450806219640d54910710138907210f00303241e071005910001c1000340403202805548002c0c4900d060500241c00c16613102c0240e1081401007604060359001164186175a00c1100c0c000e09921100410060074a000711501078003040c0403e0f10380b00d41c44140007842034031900c030b01c4040f0950750b03010745005801c0008006205640d004d44581c80034603140b040c0b011031604d400030b000412003c0e00e0005000910310f0091030010040c0e07c9001c0c8000402030381d00d0705010142034020501828044402c00c41e201d10001081070456050543d00075151100b00802c000d0300041880000c01da002c2502c02076030380c403034045482c1e1144825200c280ea4044c0040400003503680c01070702159100c1d11030489641d0315048400c001d60440c050646403682c4000b0200001c1f000c0440104c0507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 322144802 1250 322143552 322143611
    0x1031d06150132040b0f04060201061a09150c011a030c0103020a090e10031406040303050a02031b0d061a0301031703220203100f0c09050a03050a080c120d 68
    0x215103041c0d0030301590f119081d20041c0c00441c030103a000c94500200444002c0d2850568a81d1a5805890180780540142c06030f440590b00c1c1c40008608000103445030400380406c1442d1500c0c000c1003005002035090382c3c003000001550300f40034011801400380640010b10110124692007008075170100740c0b4120320226000d043c18410405000401d610806140c16182018008003003501d800d840050720742c41d143e10140450f40311902c90700c1ca440000c10a940030b1400b84e40c052205441c2d1104440c1248000c2d102c40d55080802e41c90f8840c550b90400c05084503604281000038190360700d0344440d82004291040040714107001005104010340032440060480b00c050f10b090545c0303440c0d043e41101ba4000d00ca4140d000704612000021541c0c200103d48140c80c21050038802000080e0b040d070058060324812002146000c2808039550801c0100142140e412000500c0c11030311640340d240f010382c020190351206008044122440c000b003000201048000704000190400100c69605031450301c40942c004e2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 322146052 1250 322144802 322144817
    0x150515090a17210f070b0f0f0f1914010e0601020607020f060c0d1506020634030c1206060f032a12090c03110901060f05071101031d061501 61
    0x4a080003540003441c01240010881218040c500c060f024081c3c04091255258001400003c01080e10b01c298020b11040b2040324154881021950701c02c8002c07108900f80300c08000010302c142603040000041c49200c0c034000100100c6012003400c60031000d07000880602090011f00c905943d041241d02e034421042d101525082098214071910f960016007010300c4040c001c10f0f90300030000c0030b5001d41e807a0181c08111581030b980c2c4c1d08001e0348980089900c0105000301c0542044121031303942113510006003507604d81c0018650b8030401c2d0002c2000105a1080007111620640250420301c03c410240019440d08264981c01c3c1c0320007004d0707643c079045003900c1c00d400e903c0c1c0e2451030601034000440c1d84c0060070940c41c0400d4500141d40109104500a4600e80284034000184641e60001c000d40a2003950300c540c95a89941080d0b90001c0160700080004004000540205402406070650b1680526020a80d0100802c1c0c81445103042c10705480240c0100742031041308822000400b5415000303090014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 322147302 1250 322146052 322146089
    0x10c09080a03091202010e0d0b0a050a1119050c0f0303041712070c02121e011104030b01060305040206070c0308120a2309010e0307030504061704080706150515090a 72
    0x2002503c961103248003d901200102d001c40e801303401d2000c80750001038460900c440d410304080ba4102e40070740c1c500700094035003c0811a003603883c0c0550407800340e01041c1c8c1031402103d12400386210f0320300d6517014200a0244201c4003903030b4081c80315040300e6011f00011510b0341050704212814034000ca1100111510030000808ac1012100d81103a200015040c1800611640e0001c6035040071405114600745c0201d000d11000004490b004640080d4540000c100310320224441e080c4078821404050100110040100a0517211750052076100d403024200c6410042650340304400c0f40309980003120301c0d403000f191103404d611600098039840718580c281444011158214010300860400b650000800c80d58001044504250004a410710003601200da4482e0103040060030394100b4015800085d20b1070b86100000c10300140311502464009020034a030101540c3e408006084103100c0070003248903445d0014080d51000d20300c3d5a03040e8503004035980c0e00014020009186459080100c2441402c1c6505c07 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 322148552 1250 322147302 322147307
    0x105010c0b01090b0d06020307180b0c06061c05060403031a091605070206040e010311010f051c0b3d08091e1c050403060501050108070f031509050405010c09080a03 72
    0x1d41100e0307040c0000103060700080081501c840800d00040c000381d00000c00d01024650001c9081034003241da0003112100c68075205200451310410b55440c03003036030005001c648245420940303990082124282070b42075500c0e5644032400c1886c1240d0950102c0d58601c620000305886c401c010031400021031398207000f0300e440140b60350140c506461074420042d01090003021912480c0480d0f01030122000040169070b9607107007140200b00c2070340358540040c11040b80075141d00d006400340c603080d04840c0c0300300c10812845c1000a00030003400d400325a000d00003c80200032405520111440f6001c46041445d500321400100d00000c0c0000d82d468040151300b0341009020400800c1c400d41043d101d08410300e40d030f9101c502480c9407140310701c801d1451005060790003504940110040040324810402481542e0341d4400544080000300c4240021401c101c0b501158684694480700080b5031319071201c10401e84840300d94044a404403004c403001d0395200c050001f02a0040403200090048000a005003221030703600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 322149802 1250 322148552 322148573
    0x1d03060114011e0905013507090515040305010c08010311090415020a080604060602070b070209060a030803010e100501030908120703110d02040315050c0f03090102070b04030806040b121b06070212060f0105010c 92
    0x1c00e03c411f0345a0f004200c0c09840390306040014032004041e4041c1c0a101c003006034465010b8401150740b5886c2050554001c1e0280c100c2a0480c0c1e0000804600b4505040c1030002d60300d8010421a0b18924000c2910400c801520292100b0f8806507951090b9107800d40c184803c4a030b040d0419415507000305410004428a04122040c0981c1543e11050b1030721044041401a00c01b500001c1207520080004202c0d00c095802d9980b245012841d490300d40350b941c44c01907040319000c41d00a0a082e5003045a00c03199001e6500c03058014150380f40010b08840c0c20030282c0525000043c01c8203100760001410024080002c1c8081445010b84200b0409411b00c140c41945500c0f03110310310921410080001904100300b941615076003500700940d00f81c20702d010b2500030450207048651911403440c201c4000c0c50f0b030601ca55825000e001c0c11300102201001c500c4809a01c841c0d982100c4c4d80882c08000303006c0141c544502c07100c2403d2691005082c42e00700710280000c041d005801407810030000c90040e9003c030750741c0d218 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 322151052 1250 322149802 322149887
    0x923040f060801091a250509030a02030105090a060f020910110a120507060c1403070e0d0c0303030203041a04030507021c02120309011d03060114011e090501 69
    0x4000481a803510a4440540942d51000281e5441d04644505002a800948038620103074000e102c41640c0f4500302c0704411030340d004c00c22030f05d1802005140d2100e014400610003020014110f035409455513000a0079200b0484043c00c0d5500001f000d10100310403402115850003104400350f040c98410720210b402d12081000710f41c01c100c961a8100c0d03001500f40b044c5403015070021040d0644c42d03042200501a039202c1e1108968491610b0b00c041c410503c01c0d00c421030184802e400c03080c51070301d8800c411a0940440705180ba4840d0440807500d0024422088100095121f40c030701584034542800c1480010000b0071190642e112100200000a0b07445800c440c0215411104400c0c0003005414080007116601d0000b90010440039288102c00700010141046d2002681c1c0d04860042d240356000700640c0a00c1c7c0c0c3c640691240c8018000c40d14690b00380c40a109040c90b000b1002c40704461400c0c01502003009580104900400500c01942c1c41540e01c1e105950f5999217031200001c42c82d1840c8a10800368 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 322152302 1250 322151052 322151059
    0xe0303091b011116050112140a0b060c030415020d090b09100e03030c0f12160b1b13050901060e0102031909050d05100605090f0103080702040f0f0902010923 69
    0x689480c1142c2c001c1409050f0304403000200c44d00c81d08a6010504642d006001e030710302040c5040070000e242e20090080c0c3c00b0544800000171303803035160910b40102410307503000101d91000c802d1160341315040003040a807000b880c0c135280c1750070380018840001c0d041001d1407880c0340030020614020311050255800701c96040c2c07403e490f074814509103400b084039180b48418245034180000101020900340000b40110004041700981e01090004a44d4403540c1c03003464035481031800007007408000304101c0924070b60301800840c5140138152002c2040041e0742e014803026401b040d0452414031140c14030140c2e00c1c0c0540b909003400c500c0792b00700000103036881c080c050840b040030300d20510308404a071040100c40b0041001514515400760a0b180071622003405100325a602032030401c00151501e090b0684174055404144130035510b03404c43d100c21300e0a6100c081c090b6002502c6802c0da80c5840035034442c41000c044048c100141210952000507d12505a800589450046902c0d40007008000c0540c010904085 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 322153552 1250 322152302 322152343
    0x50109020a1205072c010e1006020c220902061303050d080c1b010b09011d090d0903080d0908031501020c0f0307051e060c07170a331505040e030309 65
    0x7108171503031402c9a00344010390361040f9000143e0042e50001c1a4015001c2141d00000c03541c45d0201281d03102040310b405507001c2d00c6803045502140380c0c010042c0d5400300444010601c10300580105d005070b4405a40285400d102600400c14040144881a000d0400f403800d80482d04115403018501d001c0d041c0b004000041035040709103030742c400750700528405102070030001c182d603902c000070111410400c00101e000d0700a1000242908404070758078031481c805450f0300e58002d0540e15004299000000301c0969607540d41079a0000c900140040c511400b20401c1d012000b0940100090400b0484200c0c18001d25100d014202e00d541c0104d00d401c10745034242e400c1018113418004061060010303c50483d0001400170702d0301c03054080407409409860701200c00c110b81d04608000345a46411180b0082c02ca003101c90000607402040e5511102c0e03000c1e0b01c480700c22528203503066010880310040546011600110820081800e003800f44a002e009010095410352410303100e0b03952103801d005801d40444000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 322154802 1250 322153552 322153589
    0x4210c06110d0f050709080a0206040e09071a092d1516060e060606030f0403081503030d090605060a030807171201060c03080a09030215040c050d050109020a120507 72
    0x1001c00c2c0d9204103101d041c1808410034400300b4800078402514601d00080c41007801240c00907000440c07c00c10f927406071090f482d180c9449807440700b42c44003601180803405410800903030341c54088001c17881030700700391211651400790108000504070340c0a00300c1054603d2890070003c1807012054030804400541ea40b0b071110289030350a00c10b502c122101c0740b00d2480070401d51000d001c103e42c000420800b44904540c400e444140c10494240000c0314454040d000c000c0004002a02c100c1d0b203590025a00c2d034500c407211a903d800a8107640200b0306007031406541d000c020040c08074a0182d56040002540c0c600d440a0654031403c0300c1c0d200700807000e011034030b40100b6410103041c0380d02140c0c03200f130000f00220b4081d41c4408004251502d0120294001840300020481c5c0c4103443c822108502d51540003040581e040d00c0d080191000d0003801940c2d8120801000182a280d481c0c0e4090b41503c90340c00002e8000007841040340c415882d400c060031012100d1005d10000798000b800c171342900d455440c030f985420103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 322156052 1250 322154802 322154831
    0x20d181503091509031805043305060d0c092106020915040f06020c03151f03060c051b0a02030d05070c0510030903020d030b03120a1106070804210c06 66
    0x60780e00741000d0b6144c040e40c002459480903400443c40001010184220b989600704004e465002414440c0000100c5034030100c51515240c0d00c100b190702c1d1000802030303540c0c2e600046d2103804c0110f5003a2150348584141c14101da00c88001c80c06880c0050440d4003a491120110540a116440090103103500069410080d0380703070b02440500400e0114819034440e180e2100e143d060313070b95200f55000340c810081109071501d80800c4045107456501c00c01004c03651006599000007484010b000c5c04490b0040f408004103105014911000600d610742c240c0d81c1d140207005844441003549601c1450704242c03500d000681c2c3c04120040c0c1c01d038280c80c1280e01d4004504100380143c441c3e9001a81c0450b84030484101140c240e0400f15a25001e42c00f6601408a500740c01d42c1034a80d1407010b15403540098030440102c0720b81d8805808840d00b0752400849003100521690f1501d1025511800171950b000200302c10000310008a030411401c80300f15145030300444002401d10902c41c1401801d450315804c2032802c040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 322157302 1250 322156052 322156073
    0x14070f0804030f2f0f0d0207120206090409050d081005091902090a080115030209070e0a0b0f0f04031a01060203120c071a0703050414010b01080f100503060403020d18150309 76
    0x5410040b20701c4d038040c04d46100d03550780394101d4105a034091912480802c600219107002218407007164089510002e50070050264406002c2c0395002c1d80d070b035480380c020580800039400c12800a840c0e210290805058502401520341c0c000c9128074100e10401c800462110420f0711100ca10341800b41e1107641020005d44071681d00c0e0072444030343d840c0840504452210281650880b03009440c91601074856050899100c036115035080e07000501102d0400c6541c2d44800140281c042d50403c00b410072807942e07211049944294010b64050f6442061150500d00c0c00f2900c81c0101100d000039464181c0500044d004c0c41030040140b8406400403030301200380a1042d004042e04040000311081c01c4c900b03a4400b40045c081981c1c00e440345003c1d01c814441070001407040410480c4140c54840150f514400303904000d2030010109003601000020005691305d0400c07246008611a4000c4c00c0310340d112110040002e2496400203110043c442010007800c1006200b05c00b00c00918075010880c40c020707003081d4021a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 322158552 1250 322157302 322157357
    0xb010215091e0109030311090f010c170f03090705040203100e0c12010b0a02160f03021507081306080c030f2e0f061206030503090108091014070f0804030f 68
    0x400c1d910302c02008a0660003140d481d84280c13010801c1c900c0074400c01a050080850b80c0b60400b200080c00c88281d03025035102891684945c0c0712001824000024080030f800a2008041451020050091040041c00030402906040d02c0860442c503280303801c0150320030306d4030841094481c0300e004180240044000c03540d40300368072507a80318103581d2401d40248a40c0040080401409004240e100d010300d07082d400012a049000d10085190440d000c00802007844040f90170041410441440050303100d0001d0103a504883c0b000c072554516002010300610001003018100c40020020045909600d07002036030420300310224a02d002e0a0045000c00948003141d00b031134090755903000080d400c4a80d4000700280d8150365101096036843c0c0100000b40c0c2d529020080071900240b00d00441944a89030080d40301c50460102c034181c0450f140224111080001e80b640b00680381c0003000f01c100d030454480c8a00d00170b5403405031002c4c0760039200140b040c50301103404c0d400c0022070090742d041d901d405202c91440 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 322159802 1250 322158552 322158583
    0xc090d0609080711041a010801090e010b0d0b04171c0b13050103050706201b011e031d030705060a11120c03040b010e0114101413090509010b01021509 66
    0x86240034101101801c4c0d40d96074031403089003403510b42c6040a1090902c00901641a12500303016400c045110002d0000341505100941da140401601559002d50f00200b042c01403030f40d5090790a081c01d08156020710000e40d600f10b00d10400202c01a440490307100ea6202004060011300e035007420000850701d181c0341914450f510f00303003400071051000100701d0a080b2000c0e0346034541e150382c1e03003076014071a18500c20a46c0e81503040035805002245075540d02d4038820505140102101c90540c070b0200c0000f919a0b0400002a40c4103034252846201140c000051000b410003542040c8080e6242c1c2e54074140103014400042d12142d04002c04d00341e500641e0000c01c04800382c110f442c6460200a80d083e00f003100c00b91106242503000103456007100f03a03218180c840d401140d50584a40e00203000640078400c0200003004015940c004141c6003a030041e00d1070031113120710381100a1600c80b01c0429610042c094948992600100b00d00603a0000303040c06605d42c021034200c04030f99580750480e0500e80441e40300e000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 322161052 1250 322159802 322159807
    0x3040309090911040b010c03020705040e1501060f0305070e090621010f0225020117040305070816060b060a0203070308060d0f0b1e0403090501050325020c0906090c090d060908 77
    0x20441e603200030303695040c3d0030f0b542086141c180000440f10040741c0c84014000d40c01513581880035080c42d8129081d0441d07403a00700c4070250308541080d404000309034031400005a111715140c6e06540d150040c26004a0f86181950380e450714440051080b02c406000244290b08440c0382400d8181c4c81008000704480039802007140030351a00c481c802a600016480d011080b49898600c10300041c95034265911307406035100c8858038000c0480214001001e881903061000c1031000900049240000303120010070070740c1c401c4ea091442c1c03600768142d5420301d199500c1120b0a20400051507400815168016007503d0484415260200407418003801400003030302c002d03480900c950601524104050095031903000b03220360032074960340b00700442000307540040010b01c42d200c0411156124502942d004410341c002c8005004401007005e0611a07011480310151f0803900f44403040c0d180c44403140d1307031100c4241d60016845c5081c16040596108402446201c0c1440303034405001e108090b4080503800d5804917183c1e6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 322162302 1250 322161052 322161071
    0x209120304080109020112060b0a0c051204031112150a09020114130302011e05040302010c061503030207080d080609012702030f0a0e0a020904151e02030103050f0d0c080304030909 79
    0x10f018004088040e80400c150020202c51818944903510440e00c0692013903060103001a022511122004000e807441d00c07852403024165101e0301c00400c02944200e884000d68211001405020720411f04460308640045524040f02c1001c1d0414035840448007000007040e1220340b0041e50483c08241c4540d800b01070124540382859100703000f040030b481c001d07261400c610b0140c204e4643c0c482d0200c4001c50000b8824001000154041c2c6010b200c42d5104803070200300ca58210b0801040c842992f44140c0c0180e000c800100603100c4144104944516a443c00304143d1400341c0124001c2d100601c00c60003016070102c0c203031b240c20401800c0c45007000c1c180c4000303642e01e082180000e10380031001d035000403a680c580b01c01d070701c4840b90009611079550307400740c4070703804a03519900c9100c0512402d42001c401c254070f4013180220f40b00c00001010a1003003140300180c4a5055042c0140b914205c502d209081fa403201c03e00500b91034004010080700c0e03070702030406542ca584510341210b10300c10320350280105d0b1703080c1143d00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 322163552 1250 322162302 322162319
    0x13050106031401150f140d0b0a0c0e0d05060c2101060c060c0503070206131511070c0e041e03020c0616170f220e1f05030a150209120304 60
    0x41860007401d0000b4008070603864224040c0b860140704031410400c041301d003044504072550071b001c80c100000f01090045d1280d03403691701d00000101c3c0d03403000e080d40d1980b900121540212003100b00007010348080b00d44841d02c1d512242d5900001e42080503959020a10403060015010035040d0030400b01d03810f00d02543e40d04006031804076609004c50b156400c01c01540070740c0b0b208006480c46600d8a030b00815158451180c0e20000201d000402c0d95201c0065000900c2d20847c0e028046d04400705004080e914207450404c00704920898011102c2215500148008903c00380c0341c8040001d902200800e000ba201d203416072510810204090b04004003081050251400010240e0024040d4118054000f036402c5600c41c0d5100d0800807412a040500241c2c01844070340160080107007c004862510a49458021054060481e4042a40134159071040209503620b03582030001c01c419401404281c000e59209a12040c2d155280c100c0f41c2c0d0b02080004172942d0f49000d0024100304002525511504c60264 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 322164802 1250 322163552 322163573
    0x3030a02061e0c040501051317070e091b011103070c03080a1e020607030b220203091c050d0b0117010314011104080709050705130e0106081302030d081305010603 71
    0x10359842c11a0030005490305580c815807511450000303110500d40380c01c100c019202c0341c0003125803d208820b81c3c0e00c0480c2e100426405442c2c00c54494008046031450181842c0c40d03800004c04100490300302e50350302001c802202c840d400000409003003036207451150480d9103285018160f800380c160740e00c04000006211100d40240009040c503506c200d5015a80d0300490b0340320712050820030050344210001580c2910030340c08240c101c14000c000b0b0b00b8504d03042151418881c1801645040194000117110291308100281c1c1042120000c0c417408440081d1805407082c0980c1c441030000c503465004046a43e07214004074682c1c100507410000d0256140d003008086c6c0b01c0c12040c0d8803483c4d0310300851b41400010082c1500d003102c65900040140a0800340054050b18006e0044400c0c400248069100b41d1a280d401c4005402e00ba070002d420703585407070401003450784094a00d407030f000c0b013506900c000f41c2c9002c039100070401614282903156440d40c044050840042034000ba015500e0b0400103c10410000321 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 322166052 1250 322164802 322164811
    0x3072105011b111902100309050708030d15121b030203030c010506040e010e10020d02040506041203090509061c0503041e140306092e0903050702150f0406030b0f03030a0206 76
    0x5a4203508140360640c9950380083c00c440345804c04501040c10f0051816400c005000f51491402017000401c6070381e410302d800040e400141036a080030500b400c0003a45403007110070900907041200c40440c50700b1008084550402d5002c1c05014600390b241004032003a00540c0007c50380a41165961241d528250b4004d01007950314600c190309282c81084200c0d414000d981000c5156005000b0721082880d40f403000354000080b404e60340b0b03000c1c04002210f0780d50310b02500040c010154142482c3c41d4518008145c8849904000d201e65001c4051201e60740303034045007014203068401940c2448030141010784c03840c001c0c1d0348180da007161814410001741820f401c810b81110b03900004075600801450401d81ca6000c101d5040002d64052507603c526000c0c0358143c2e07107198001c4403000b05a100c507038074441c0549190450540100d0800503c00b811401c2c6041d62010714200b0b444040c0c184800f8090240151049108600c10592a10816545030361041e05140c03099900404480d80d4508911029403511000c48 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 322167302 1250 322166052 322166057
    0x1030204320a09050f1506090d05010f09080d06210807021206010906030203010e010b01080c0a0e1903050d020a02011b0503040906030f141605040c05071403041401050903072105011b 80
    0x2c0400c6c9030b058001750720200014001e00c0a4201040360062003040010050305440c0b6640b10114038a5a1100e07200d0b203404107014880c00c1b0f544461941151059502c0c60b40290b01c1c21940d601900001d85a040b6510702d219480f440d16a0341d44101e000050200c8650400c00301c40d4010b01000040114040d840002124400c6c4d00074805100d007240c4150032505803011040c0440d54550024a102058900514410149003858400d0203034000100e20021107085400f08410414903052042c0001080788075004003c40c40202805212940020b000c1054154084558441001c1c00400c0220a0003598041e200c4030a0412415a503820240304e030000f1102d044c0d403010701d401d03a91030f00c4440100c0c1414a02162a0845041d145444188002020504180803c00009100400028283c078244007940030003000190349603820511403450715800c018070241030100c10072100c18203480104a00044403110050340385000c1c40c4040d82d0105002e2410001c10f65480c1080700c242ca40d000c1b8101401094495 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 322168552 1250 322167302 322167331
    0x9060606021b031b061303051009030e120d032d0b090f0f130c12030804030306050d03080406020c01020c24010906080606150f0409060302030c01030204320a0905 71
    0x4041c151a40d03201034401030aa003401e0480131250401e030b002840c501e801030400300c16140daa230b21164100f1110b001c2d03454666403200280d0301890750000c01101c01210031141c0d2100a801010001c3d5120881c44c40041415111b00200c425502a581c10000303000301d1001403000c3c00800c4546400800356141075612030102034000c0340c8080c106a61141c4200183c0c962007089441b094400c0310415403244044804601c020310114141801c28080b04840d44a5151f0303449500705460040c00f5a003164100501503100f2481010119a0041500d904942c00c4540141d64030812000784d40640b08510452010b4450b0700e22036550003000c040d0300301c1003502c008a03002141e6207402c0303644190345a500c0740318102d500410202ea042d1815286100790701640750840c2d17241c0b0000b240c0c0551650010780c400701d00c00390b6407070f020402d6050520400001060900e0b04502d803904000010b4120000e40980340024102d14003084100c00b240d40b155905800010407148200c1d558031421800380c03600329282000d00c03220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 322169802 1250 322168552 322168603
    0x20d0615081f0204060206192702040b0108130206030901061a0c072c1003230c04090305030103141213081e2a0a060306060f02030307020606060a02010906060602 71
    0x240701380c609403051a4007400f6107859181d0340700404105a0440f00080c0d6031000400c3d20440d41040040303500c00301002645812069004020845100c66a06818446420b0070826460526640004d44503811a06103481c1c0c0c41d03042075a801401650090003103400b60f95200290403000300007615060600030216641152074080500322042038000c44904203810381c003c0540c80181441d0241d204940c2c51030480110360380d445a4184800603511895814650034040c2010718090208080d09a01a182802107115543d4001c0072840140700103044e0b40aa800c6180c1001c0081c00482490311110003144c3e100c5c0a0722144503015000c42c4a034a620b841414100b030210a0301c180d5008041304120702a0035002140500003100601543c0c1c101400d6100c890140380613903808500c8006070242d41e40004a560130704101070403a20894080d43c00f075600c00d008021003243c2c00180e440d844442600c0441d107500120700141c1c00f41180500c002e01d01400c0040102d002a8005140540d0350421882010710048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 322171052 1250 322169802 322169863
    0xc090103081c0c050702040504060e06040c080123180f03280f021f021b06060a0518061c08070f11181302031501090b0a170a020d061508 60
    0x3c480b04080086034050000750050300c1c0039804250311601038000810003142c6000080c1c10140d08070380484410060400c1444410400d114547d04070b85404241e00a0303040c801d00750161864014481030040500e180c030100d41103010b000e4005040c80039400c6a4035569074088a800341194044000e04110218030300e0961103100301d899003240601a00a010503001f1402c5c140907403c09082c03900c46181c0c00300030880c558a5408552020020f60b0000b904903030900c0010013800f000d442e031050b80305000c1082e0441c0c43d410121103031600312804844070449003c1c0c400100c11a01c500200c06418008042001c4040c08507221100908911071004a2441c0c2c15040c00c004038595800c901154004440d00020003401d080001c1c4841725000034111540d0014011410082500c260000c100b2591074a031810381d1802d0801c9900301400c4451803004d00c141c0e2605682da0340704c4080101a01c5031600d513615a045c0441030380318010300da0342c40101001c02c5427600b1071595a0102c074284201c0039070f45800305101c07019 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 322172302 1250 322171052 322171061
    0x6030d0806100809120a02060108060f040317092407030c020f100b03070f030507152105040609150b0916020a030f020f070609080c041406010c050c090103081c 70
    0x100401e8003285040146045603d860024034a050500c13a9000c280c085242581c040c00780907442d40d004000542c10a07007602e08010001d000e0900000045007070200098001d039019803290f4808103001c140303658244195181003c40300700c4030100b5528501950340c02c181407004034800c45e40c07038070244081504282c0c100da039004011140101d94018200840507134589400880103040e0050460320240e40f1109180e50400322580100c4066200c001c080101d905428440c062006190404620400c4190a803544048122462105070781e5180c000808110700340c0d21010581da08a1600d20008148840c0000180004121103200780004000a0100381d16400b060340400060342c064213030012240c1e41500c40d2501400810150f000b101590300d540001049107000a00d15941c51800451400309ca860419200a803403900031414400c04207031119008600702d40108080c40c10405101076814a0b41c140b81d100300c402c59101540c0000002030040b031401600d182c0c1401c2a43c40c01c00d152405049c001c98 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 322173552 1250 322172302 322172311
    0x302120c0a05060a030e01051003120c030804120302160b10091b0c1a10051201020a09230a0f0515030411040f0f090f0c21020f0103020f0f0306030d08 66
    0x41440d109105504052004d403003006404e007000320300031401e0540c030303400c3d110100c039800450500010104280920310911194605080c2411000700403113450003425204000c2010b400e904460500d030020300c1c420b0317044889104e8102c203082072000451400015000040e102c00c405840401c0020941001a10400401219108141514002070700c3c05840401d900d010948841a8040d42c0070301102c0c4104106110b080000c03040b4400506000c00c01046003203110700e80e031280e03205004030101107401c03903034170030075200a01c03031804807110846407202c038150242d0700d46034000400050010b84c07100410000c1054403412566518156000d880443c0d2501041b60080c214503041030500500e801e00398080e0b400200502008031310f00342c68980541c15682d1304c1008840c8022240c02d000d050100b24802d000141216440c00d507075541d14211440d81c841c14001e0040e00c00c1c54401d40710040b42c1c1c002d504030743e407174074040a2040c1c454141000000c903607002103a00c2400307401900426501544039a04080c0709 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 322174802 1250 322173552 322173559
    0x5430501240b1204080405090a020304051e1b0a0801090b09061e0103200904030e01080711070308030606040801050712061203050412230c1905100f0e0d06060302120c 73
    0x2003c90031503a00c0c151076400f070b00a581c0c404040002060680b100c0101e1031203074210710409030352400c3c0b5142042c0340121034941001c0510702035005000394140847d050f9841e10024181803040c07204040026210b1107540d02141e629882d0011070010421040c003101e01c11504107080e9041540c0703040011002e02900d5064124010000c0b00600c005036586c8000700c0402d030030002040c4842042d002080c13004609440c150081800030071200243d41c1c1c455080384d4002c41a00c0e00300d1019020104e12603071080075000040a0a0000c000196281c03a25400d44008022802c000d0002d4104000041c001805408103406554145003000c1000d2060300740700203880d40c0c950ba40500e01841c021900700e000d15641003c0300e14444206442c3c1c0d80c800010404686d140200f00a803000c00b02c030f2000c015500146403001c6250600384030040003a0317900c550f5141686183c0f400c04603943d8000450481c0d02e86034022420b5407103603804040500348a510303444601580d109861500003080d00c034940690303a04403462190790 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 322176052 1250 322174802 322174807
    0x8150105070b0703110406050409180b01140402070609030e010206010803041a0304020310140a06080a080414030a0c0602060402311104090204091401050105430501240b 74
    0x12038155845a000c078a510f000107481004001742413440d88181e03c550002800440e00f03100c10380d25803042400030f0000b03040c030083e28065a40d407444040c00504c61303280600c2c0b05034112035242d200c070380484071a84d6002c03008000365689450050007488a5050540c0188240f500105141c0e00c00821207080da20006540c0a103000c1e01c044060856100410803a0503004200c11002402c85d5800b41e039011940d801045200b03464410540d604071459076214517002e41c842440900400c07048812074041d00c00183c0d002c0c07822044000441e281c101c6064000f80040d8603004000742c1183d0204020340186d1007100c0807001d1807002060748150340d60b1503140c484541e9807452a0b11400c0c2140d07120340310340c00c51030185c80d081030781c1c0d56410070407a08550300c072084071070f210848600140c804110050142500b400c016040011003d40c050070030f5140e0008a10180c8440411817a5501c40200b404c43e0f2010034450440c4800c0c03614226000c0c7c91ba00c041c00d04290054072071944400c0840048000b500d806034007190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 322177302 1250 322176052 322176067
    0x10e0a03020c0f010c080705060a1b0507111809010204080d0f0f12110c07080c010305010803030a0e1203271c260103230d0905060a120f0c08150105 65
    0xc0010f02c24050f240c18003c1c414030780c5000581c0b84002c6d148203401070020b840103180c079a41400680b01030a40307244000400c2d031000310303100d900001580d9010790008006804036241e20081503070640380101c0c00e254001c0c240100305070b8940540003402558001801d0300e981d18185141510205813200700840843e15544441181da031240c40310302e090020f000400f240381c0b24921800d402c1580081c0883c01c15030050b01040c4039107001009140e644c44000c0c40c00b0001503142240305070303c81c08041c06519009440c1c0a60b150314140070803c0b00b03161260f502e2202c0d52070a100c1d96000800b141d00ba41e0402d81d51b000c0700405032a00380030440038041117800c00b05841e04600550121072202c11018280d5480500c11054400c1d2101816224040c601c950031030302c000ca80e00d0f22284118002c21105946561101242d5003065030300ca03140d6030448000f551140d8a41450347c1043d0368014044449039002440c140405984840a400403810b17400b403a1604012a29520318902c0400c0500400b00d000c50030400400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 322178552 1250 322177302 322177309
    0x7080d06330e1e01172e1a0a2109020f0415060509040207050706170a0225060f0f0f0b060301030503160c030c120c0803130501050c030f03010e0405010e0a03020c 71
    0x280b0980c205140051031800441007524101e442500d540080c00300802415140684c4850f400f00f00180176038280e28240d10b0708045c220132044203044c583c4081f8002c00c000c401203000701141020400300f06800032005103d40c0464006108140307007a442540001d0b150046401c0c2441070354a0500b640e140118002d06003041a103481e0f01401c881a04141c2c01c00c40b001c04104280800c80190003503507901007410002d1469021081c1000c1e20f074000c5188108074001e100da241c40d03110400f00b050100e81911000281c00c19500501c4030301e0840e2021818815856040101544032040714002140d04000c0c3c50321b86020310007180000d0000500c0c40c3c1c0100166003013800c0c0c44070400c0c01c4034442c41140e0741d201d84a40d202c0031050003540c00f90798015811216407041019603040350000c0e0a00d0001107080031141001d20700c2c440d0561180b241403040010300044103902c11302c121a00300016240301c65a81d40e44024001d2002e80403079040c0c81395480c114491308440c0c1c0102d50505600c3d050340c0184522100c65040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 322179802 1250 322178552 322178599
    0x1d03070302090c1e030108060601020304080705090a24030507060e1e061303030c02010905040c0c030f0302090301021803010b06070f11010e10050c0d0e0607080d06330e 74
    0x141620503428013820026104207098004400e440c607a18076204d502d07040c103e40c80d00c500a0105415500280320501c500d0100003000d0701120000ca4000c1000c0d2603050381c4000401043c0c0d0100700000d96001ca259120500d8600c0c201164820411034110699524046424203151100c03664130103807a805191826200d10350115a50318000c040c20729000020003c43c030450145da004402050284400e0005c3d9a0840048801050b05440902035030280c1180213042e500d17800750050510608450043c600d034031907419140d4400d0080c2c001c6680d80c4805e06000513000400129500c40c1d030074848850b02c1424854103654881364801401c1a0349103403a5100f8032228214942c1340d04000000c144814a0381d41e11200f400c814480d52110740c2d40d03600741d829407401c01d0030383c003482020f104494201d034800d80c40b00402c5502076900090070a48811034074001502410482d403084060f078000c3c000489000c0d1100d20142d242c0b6140c00d5402a140c41364800945540f1002200140e02800101c480720101209034007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322181052 1250 322179802 322179811
    0x203030c0a20011e05010504020a0e041d1b04150e010312031b0503011e150309020a15050c0706080603120306010c15021806091c210f1d0307030209 65
    0xd110b0010390b4034150003030840707060408281c2c03414560a050701d00e00100f403003054050441500e0940c03900e00090b01c05042500c9680b80709000c0c69840c410452280042c42da10a1006850400e58030b4030b0003501950079a03d0700d8102e15a10451500d00b250180c4c00d07c0303920f0b03d02120b000356850003a907847c50b20b90b1550741200c038040c401030644503c03062848a070a1417079005a09201e40f903464803541442c3c807000062201e0340b4641c0d500c0104072020b00c0341700d00d01040c900c101106458045407890081c40460380c0c400d910391000c841100340101c2c0c400744541210141502c050b0354002c845c0301355911182251516010745d0041d400d80c00c500324200b036415407500116403015040c100100c1a510135607480405400b2060803000150313001c41c0100d00c000d007944014445400842c0c880d41400100030000304007a0703a0203405010340f42a9113910f8100640144804003c4818114260350b880c0c1c040d402070725141c0c681490100061110200341c000303a0384980300030100240600180040c3e4115803e11000715001381 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322182302 1250 322181052 322181087
    0x1703060621100602010b090406020c0f19031106010303050a0f03020c03220b0405060f070c17010609060f0e070e130c031401090e03070b0a0f0c0206160203030c0a 71
    0x8040748110340c451031001e407400141c040d030075a0b1520714620342c400000c40d000f041c11641000c007400e000baa21a0b1403580c100390070840041e0f90303003a41c400c824540107000c100b80800d40a10042d440118040d80051039505000e51160600360303050105241d240c00c024003008000c141c00780040d400d03070b0b0300c103e03e4100704e01e8181c1801407078034403800d000c02d255400c50000b42c0c1c0040da5503202101c4030032040c1d440790010200200614140b85c1040c00107980d40c05442e00c5002e100101003a02000d22407180014801017a40c415500860020721064501808180c0070b2070200908008000a00c0d510241800003182c1c01c6640d01c031070300d80311101c2c01c49070340c20308045407540984000c848000b0310401d441060300120302c0340c03400564840c01c007203c07981c240c0c2d050303012030070007407504c030b107243d50280301000304c4080a611682c581d034107603603900400c1c0c01000c5c2002c1c00c1c411245070034005c485164000503118020350480010038003210950104036600d01c0100c07941d04201d402803014041e40c03400790a120f0082c00c44a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322183552 1250 322182302 322182307
    0x31501030f030207050d0f02150a140c1203010608040c0e04122319020606030303070207150c060510090f09080a0e01020307021203130f06020c0d0f02120c01020d080417030606 77
    0x1100000c1b0460f805a00548851901e1303040c0004502d0032003848480080250025400c09410708406009540703030042c40801da240015400c141c0d01001c0c0f100250040c0c94164440c1c4950710f400c4014a074100481d4200c0b146444c1280204120030808074040c401c540c801d046042c003c00506d4119943c3d10304a040400309034001002ca07810b104090040c0c40f0a0359808030110700d11040000081ca0103030041d10300e500a81042082c0540b165012404a00b40c407001e05040e50350800a500c02c8500d95058035000e0305192a01c0180045440080107600c201c6056034014040d101e5122401011246500030040005800300300350301c0054040d076080000000c050050303908159aa8000c02c80074205003030011025000025075084142c00d80c4506800340c50300d020b41c1c440050400340003039940d061070a103440c459044048108204403a030b4034a92001b550181400c0003c007004072080e1744c1d414008000354058007580c0040e01d0482c0c440c0304590f10454101581c40c02341c4004003103245942e84084c182c950001d904 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322184802 1250 322183552 322183559
    0xc1a100b1b0a05010b010e0a0b0a0c140a050d03050f15090a062411060106121a1f0806010c15050606071a090607050c0c0f03100606020714031501030f030207 69
    0x1c2c0140b0480c180110000710b528030280000500d202c60004c1103d1003400400001e002c4800154240c030052502c5040c01c001f014480d0405c181d0060f500380300001c2e544900c0e44a134080140206124928808a840078000c81e1102c10018260b6141192408202d0050010000b400e1500043e0a90000c440880c0090451388420802c011844c50380081102000300980c80e003401c580c81218551082c1c903441c05800603504040c0c3c02030004c0c0c01c07000071545098403140079124080103140044003c1c2e4004040c5203130024640140d1103a4248004514041814540000e641e5400b44a4584a45510410900f4a120310040440051501400c45908490144248400907100620228010607228418034491504804462614800524040402809112401c5070060000c2c0e00f031000c090455004072088410760200303141104014500000038240000025031680104180c1d040d1020020b100241440749400d2643d5a04250320030070012021000410104040e00351140d601d910900c16198075a54 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322186052 1250 322184802 322184857
    0x3090309210a0c05030606060405010804032303010e150301020f0904050901060e090601080f011b030504031e050c07050d02030606061e030a020d05100f050d050a050d0c1a100b 77
    0x3042e160440700a001d905081c0081d2070100406640004100d400a00d018140000240300030000380c00241844000300d0300703c00e42c891224003e4201e8400180c041e0300c03507940b40d071742c002c0042054030042201c42411001500d90b04040c001c076400c0b800d482c83c40c94903000c0344005020081c58024040440b1355a00c1d40081420000390541d640164400b0005012a50402d5100350504e204134840c0140e580c94202e0513020002c0030841d0f0340c44014607040c00500b65403541020340b049910341e49035981c50780445800f00805a000f201818006020700d0486034141d40305c900b4001190711005000e541a0f10600000b1002c2c03070410020300c2c605030402075010100d00300e860818051741054030292041600412159800481c51003581d5104080308a414469442c1003041680180307a0700469000e80b132524001014000304000c4115256400011a41c1040803000c000300300103803060080f2401200c4e940350301404102d440a5601451195000c0d200345407030410390000035132117404100c9000850110a10740c192 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322187302 1250 322186052 322186063
    0x40503031f0b0a0e09010803030106080a021810030f0b010503191508010906020a1b120e06090316030b010f0e010b03151e0a23060d020c0f1c03020309030921 69
    0x601d54442034003418050040165182d1705800c84c54269005200400107141c0c0040d8494000b005450010786d520140d800c5440c20742d00c03000032240c0000c101c170309401074654954440010801012400c00c1207601c0c503001119103100503950083c00c101042d070b4803103440a007503101386600407806040301c0d07527160b43d8560b140c2591200c040c190b03400c82c1d0104d0744000407a00400704180f000503d002003100c840140d940c041c10314070078040700c0d404c0126040c0b41c0c42c10768079120704981e947c40c0e0040480d42d14242e0a0302d074243c00c18050104a1342d04544030000104480000c04074015111401c81001d8a42c0c00e00f104100540c00041c42890245020354111000751907601803147c0f005070101120320700c03d01d010244000c3d00c3d010350041010088030507514544150000080104644c12541540d50310f840100c50406030095020714281402413101c10322082070700161402d201010440d44410606089005134100e0000301e914134200d8000308401000d620b8a1580a11407a0a010808074114030300782c089231504 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322188552 1250 322187302 322187317
    0x20120070302030f0322060c1203060f0f1d2e0e04050c0301050105060f07060504060e12030a0b060304030c020f15040f060e03030301030201020705090a0605030a080909060405040503031f0b 83
    0x15000050000002e103a80b06010005e5401d2000880c04107147c424000c0c2a4032a1440103045055100000307801584203810800089c203045401e11445a1220a01c4c8850081382c421070700ca00d40c078400004011403042c04000d22903980e000740d10640713084001f0183c0e03090200292001081806100c04640700898680e100c1c003460282000f49032010b44042810300b11401030700001d100d96020700000610034248001c64180c10b03030001e400729007915245007000181c201c0c106407001034013410078500c00d4032121901031403040c0718410701823210080003c18070441d0b03c020340e0007500141d00410307004050304005000c1051001d019100101030940c815078040645c01135080b940300400a00300c2048a41d40c0301c3d0074500c25160490195185514680c0040d45e650402c1c4242d900814499000501c9602182d0212005000150503a06a00c040b450071b04160307070002031240e21458000c4003140080c28903100725480340ea4003c3c021465610340644140e210007003070701c0c11002c0e80141d1030007241601801001d003070301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322189802 1250 322188552 322188583
    0x30c0d03060314060907091107290c03090a06090f060e061006140d0b03030f0d0507080108010e1203130203011e0c050a0f0e01050f180909030702012007030203 70
    0x1c1ca0b0071850316900007040914889025132200c000d000701c0d2034000c202482101c031038481c0000e009110a8100c0312134001c900c0040c0400810300080850402502900c01c860f4031200c0106410f941c50b10308600340c600056540d01d2040d0700150611000641303d13480b2a0902c0d00610340c1d518101d2081d81c0701011f50714103029102264101d1800d115040b03588220312405402e0324180f9103d03040307800074114000d00500f100f400c840c58440f010182c0d903880500c1140c40c190000401595644240c91560300a40401d940c48000100301c4400000c0c1514103104a040500910780600010349081d401400f60350000707000c1c40c1d200d481001c420801603809208a00c21220b4684000301100425018039080307030304006880f010722130100504194564407d103146031a00d86410019500560300300101e0f5140079000100c40c0ca828000340e9804003915600c0c8030300900c4021140703940c1c55a50300100a81768013460760024045072a00035412481f07903141850171100314000c0101d80e807680c1c1c0d90700041e141500351440401c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322191052 1250 322189802 322189811
    0xe0f161d040f09140c1342090209034305040b0d031709150c03060a060e0d02040e0102090d0b10080a02150c10050c040f0801050103030801050909030c0d03 68
    0x10401c5046403143d60400c2c0c0809040318800c0d10000c40d040344103441c04000884e03900c640219141c18240c04000c10000d203412034144144001070583e542c400b00c4088070981801f01000002d072100d550007150b048400280c040c1c0003d4110012094242d40400702003034604040030300c50b202000420750580358440340d21000d005403515000a020403a801000503030f010b2501000941c1c040b0744c2140c0b01342c00c00f034280c114814503547d40c3d111281c1040310820a0902c41d284240522603803804180281d4010702007219001c00c0c181d07480c0c5040e6209500c2481d6541c11080710f1403071101514050340844819100740c4000b61420300c42c0301c009844030300340800c1203c031004a070040c0029441c20300304070303c05001d10100410846040340c000559100000c1c283c5500140000780b10f165039a42404234002140c24110b0520040c00c4c41950746440707400c240200f9040242005002407030100501405048076015160310341540d0901c020304c00440f000502c1800113110030006680440420403107944215026540040e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322192302 1250 322191052 322191071
    0x507030e0f060f040620070512012c060a0c02071818290103110603151002030c150f0c07052a040f1b0513030c0f0e0f161d040f 56
    0x10f022038201c46c04551000b030000d403d10080500094041c0a9600031504145c2c411001d408203800b50a24815040011101d154a00f56030060301e011508060035410554485640b410304180454141a44403401071380100c900b00010041102d07030109440c41d01c440400d4001e1041191607419201f080c044910181c014541140c2c03440ca82c400020f120718100e1401d056500d1612804580c8034030403485407103000008042013003d039031460b0039a0150b030f025025041e44032510401039141d13003200c03040e041d040c002c143d0003000c0091a11304c00f5105a0940240d5082607c480400390300b140c11800085945129040d030580504c8124a01c00302184d05003110003141c1da001c0410320040c1c80103410301d80d291900345000060060039060200480e5503c0703243c0162036030000b01241014416581c000b4000e144031410100325a00c0e14440c6030180c0b90349600b080741903180c03507190001c0ca00c0121026081c10030004958501c442c82000800c03100c150964040b14081c55030800141200e0709006840310b89583c4100d480c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322193552 1250 322192302 322192307
    0xa080606270103021903141b012303060315012301030c080718050a0602030909070e010f05030a060e090a05390604030b070206010806160507030e0f060f0406 69
    0x24022038480c407860750019a040100031a410754107002c002e20400704a031102c0902d001482000d0019034000b202945584150082503032203608602412600c650035480058065014a0b401d1140c95203130042d8507511030440480c4211500090049585406010f0075840d02c101c1032510640a0411428030700a506103040410760015608002d480c18035003000c2c1a06102500042c1d415806405810024090b2407440c100d020124038542045521824203580401c4042e07002001e03045008007511203000d50384551201ba41e002d24040740c11400a40c40300c5c05002418411340145400c05040380010036016240c00c96441b40d51812180501349a0201e800c4c1c0041c8441040032007007810312045500644020088214845001580b915181c410030001040301d54607400c041380c00568000b80e0303202d800e040550f4025140c84081c4034161640c480d100c0400c421500d41d03a00c2040c40221034803010301c5c04c0c0b0241c0d02aa080c4a024036150703070041c601c0300b011055442e0b4a0040000d01201c0d050b49030385d6428040b01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322194802 1250 322193552 322193569
    0x2120303070801060f0815010804020109090f0903110102090609280b121e070c021801030c08060c0906030a0b030a0c03031e080402030304050d15020c0a0c061107030605090c0a080606 80
    0x1044200444001440787d030012000c5445404803007842c058440b690346000689140030a0b522800ea0186449006120b00426500c04034803188240d86108a2989065103d17080c0d026001500e40e204c40708200700c02c441e140054891442c1204c1240301d18000041880f0b0500390b889503408120107000014901e550041a0f0460030341c4071841007440c0c144c5040001c000314882e08014040c4085c081640101c1c0159540c0c90481900c07140081540c040725a124030b4500a00d003014480c4000c94426240401ca0610310a41900c4080801a1140d801c56544805410150210040d41901401200c01c1040810818517542d0042d41c02030b19001c400ea8a048102041040180e03003031010801140e041c000140d03000300c00c5a01b242c03403c8401e20341ea015030342403812030f021906280088007840043c0d50700854502080074441039000340c1031075109564820301075410204029161009412203c01030002a00651016402c05080403c85080c2d2010401141212989400c1000380750f101c64104142880c0a040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322196052 1250 322194802 322194827
    0x80f060105030708010b03070c050708030a1b05031c0605040f140a0902090408030403050c190302100501030b1b09150d110f07031103090d06020316080910090212030307080106 77
    0x20001c2c81e41c6409000209042018082e10300c0b031803400404510303080c1c4242c00318101e139500801600c4131196100001030350b0b9840014004003041408070f8001c0c1000310940019506900907015503d4214184203030301044402100b40402299941000714440d03e46210b089a2100810b10010700c0003548500c05501c41c100601e02411281008000d10058498110154000b43d01296031a180d480364130702901d50307015140407034101d40318041e2076901c2d82141080d01c803441c40c060380030303100422050115a03007500e03001d010140107040c0c0c0d6004520f0341c01e0a41148040314a2a2070a903042c4480000099100646030a00c5401e180c3d02082d2040060798501c100c0c1c40c1054a03003080cbe80351440c1d1600710b08960240d940d000e0140411950410113122050080b124070000c01842901403010620340080250001d4074118565000201c2c50405035000399806805016007500800c0707000c000c64050400791002030700498003ca000c045001000b042000510300aa1840d142d0f1100d0350706101c0000c280313440b03050 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322197302 1250 322196052 322196057
    0xf030a021201050901150c110418060f023415020903010b060316260109060303020d2a110d05030301080d0c0b0105120f0601091505030c0a090207020a08030a080f0601 73
    0x3c01001b22007810654030400300002c0c10902c0c0e00c2c0708541004050b1440543c4403c0d003040c2400500d1039007100c2004450900362040b50100202c0c0394052080d41203001d00d40142c0c0940d1400c2d40403080088903900601050388419903442d1000c60196108020002c0400e829100240c0211b0501d04d185400e00035514100c4040d030740c4c40c0c1135181c01c50b14560001c8943c10400c0a1201c242c0a10050008090800b5429140a003084a40d5650b42c001400180414401a0f0060041e988981000c910940980380700e49809412034900c90184400c0c001500c1c4416001c9038905950252399103191101580030150078007074006540c807036143c4980c003410030f000510300b102009103c007501d10002d09022642410744005032035456002503a031a40e280740c600341c0b203020b0340240316100000400081c20b8004e14002d2620020401c000b546d2013045c160b94040c07030410298003003d40d090071301095010703601810030940010000b41c8010f540342c4481382554001002e000002d48084100300881c80043c0403940c1000080c03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322198552 1250 322197302 322197319
    0x5030705010e0105190b030316140d0819150501120f0f0605010908070b0f030a02070b0a060f0b130e090c06040623160b0a0b060a0809062a0c030f030a02120105 70
    0x100000d41f644103000109401d00d0404949c41e00303100d4000c107282440501d440440c2c80c000d0309802d0251184c50220b5002d0402c0010b4804c000a00d0b0f460701a04585000c200fa103904903a041000656480121100030103000e981d40240c075480c20840d000318909a0f0810b5000203c180c24000010080744860300010159401480c04000142402c0100e50301c0d0b4001c1d200c440c2d1070303494002c542801382c4101c01c0080d01800500041c0401d0070055400f4070202c0c0c0104c05419160740d560302c41c0c81014080c3c1103c0c0e01d07400726040010014400040007160b401000b034001d0390300d5084070b00c000443c0c40e0001e822040008101072513500c20642100e19100841980409642c149a200b1032502c4403088034580007131441002a0102d02400b0f116048001c01c41801001c6988400c0d4410009001100885805a40d8461030303020072811801d24410000f81c0010300541452100c200642d4266a4441e4100d8150b9110030030002c8290704910001e10b0040c18a20720159a600d001400390040398010b80003240f10b030425 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322199802 1250 322198552 322198571
    0x509030d1107031511040308030a0506010807020a0308060d0206040b0a080708060a120f080d2c06040f14070f08010e0d09090c03020f030c0408060c0403020d030c05030705010e010519 80
    0x301c210840fa88065131041d200600e000c400040c01c01171078645070216000c9808010444244080c62080943d928100880e550381c000446544109945010142e04603003070980c0841e00c00c08856521480141404081c0250b95000c00c0f2140c2c020740c416002c10b000441d01e86051540f000d80250000e0140ca00301403542068000540400014495a03a81b0350f040411042004241034850205c0c41e0000b40c4c2d80e450700c3d4003c034500090900c001c4620341c9031181003090380302241e42864043c030141e000401011140d076560342c0d608208030079035815904c440d000c00d07400c050f2420800c0001d01074590007260040162030010041d081d26960303e241c0c80d1a8101c41c41c10085a43c1c080c00e40b00c111000b800e00030548250020003580244221150901402d00c00410400e20180d11802402141c030050126551981c0e814030040c01805a0b01009500c01850b8003506d0109129881b1006000e005205480c0f80084540c0d8540c2124010040c40900303035110340030058505d0b01c00380c0e070b4641c0403041c40d01488080c42c0b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322201052 1250 322199802 322199837
    0xa050d0b04022d0d03110604060e0705030601180c12050405370b1f0b0c070e010e04060b06090d03020a0201020c120601170c060c010902040b04020f2b0c0509030d 71
    0x550400f15019686400c1d0380000d0520802145469203004030a03034103941051f080c00d0025150b003141c040d4444c4a4000c00107074a0600040c6181251082c4825926150810480360040e200509080c0c08000c41c0b00840804030510344030700c9000d01c1c070600c02000142d5098180e5588104420315581d4a5288020003c041d5040c01c0000d8540b9940301241e201703150b80390601407503440382640518009611190f00442c00002540080080c0c841c0315044806003640c0304c00024031000240540c4c0400344000c00402c0010f1802e070064480c004009024a0820741d03200c022400314450814240c0c0180c1c0301c8415142503580500c854403a031311003031b01ca40210302e800d01d815564810042c803070f0840036982003600c2d808030501401a04260280207081d2903445c111298024060120b43e002648120700d420f0407100b040c13610b407003140c0340309090040b414240b110349152400400d2480c0b81c0c680380400060074803a210022031103084619460342c1c64081e1500040410b140c546203586a03540c0910402188201c030440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322202302 1250 322201052 322201129
    0x302150904050708061c02120307052b050d020706060308030a02070606240e0d050102030408040905060301151203090503030f0a02010f0b0d0b04030504080607030501032105180a050d0b0402 83
    0x4036502c01b00c06600300d0520104840c025180111401400b0108403c42000303c00708110614020410307964002418000004042c0c2c01c0410032000812000c200c2d800c2c4040d802e4000d841c503503005217400a121590313138075030140300d9100315008039070305078006400c1040040910440000e4450303034040082d03080326a031400134071903020311080c0c060100e803a00e04001e5070b4031044503099041e0300400130342d20390401c1e01e010000c0b41c00c14040c1d8890b050134080065001c2c18148074a00c1d01d11500703080303020110700c0d00d10301d010010220b000039010040006c0d13002ca40b9881c104010001f51030503d504540e81d0401500080c211503800c43c109441600b4011031040c04e0303a81200e000051500290b82d4042d0392114034050310382c1c0c03040c0e500c0b010241c05036504103c0a80d8241d030007541200c7c043c41101d01e20350800e205a610440c0c600403028003044092001d01e4507251828880f46c210f44002c0c041d4803029071640001022038580c1071040b640030558404000c00c508000141d00082e081e0800445003141d491000880b030342 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322203552 1250 322202302 322202329
    0x170403060f150e06150c0a0b040b130506220c170c0a080303010306020903190b180607080c0315180711030f040e06012f0f0d02060109020d06030215090405070806 71
    0x2a0300700e617000711115640c141143c840d400e00c002114004a4030b07140581d90759101b2507003641c9180c40c0c80d0008e446a04100884103140e6442800307080b407560744818850900c01001d1004003150301141a440025130703418072800c046d101945250040c11034014643d842c00d07410314520b80c002c83e0010000c0040d00c00000550707041d40d9120401603101c448441c0403a14145649c8055044444405500400e111a42d0040c80c020b188901c80700d5510b0b0a800d03000343e69814280c4403030000680701c0000402d400b8034003001c3c41c0c000600c152590405405080002c200d40100e90f0742c00c90040c155030600c1240d035000301d01c1003104034203840658200a10103140320720303601951142842c81040f84001900c541e12800b0251007482c40003818921088141180f156403104080d51219113101c1c3c52303148280382e50001421840000c0d41c0c0e00911113030382480384600194015208140786291181c01c0440143d45100a02c00c4425006040a03114000001044140c1d040500018240800e6400b070155907250011001d422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322204802 1250 322203552 322203559
    0x180f013309050c09060304061e020f07060506011b03021605030d1704030309021e01030e030423041d0d03140f010303050310171005060a05010813170403060f150e06 72
    0x2c9642d0704111200074412600000c0d40604000100000c01c0080c0c2d020007607a12889140654602070007081c00c1c204d1082c0001181c0c10007013030001c00d0004006402140e8031010616003140030710b12902c201d0a0207076841d001240581c0040381d01e0611001e031300140d0001451304030014001e8003a91200500350100340d054031542184517000041c1454026000f580c1a1a4040e0030400e03000c06011014541510802d081130009051a1030315808240020a039004d0701e407040040740900c8940b0a0760580355820034035040e041600d440345200c8500c0314828090541429001030500c00c2e00813000103003290200c4d0229581c16000e035041c03091034018405a10705599060404954130785801c034207031a1403130389030b80006441d000d035001e8104107803004241010b505054020500c03040d22941c0401014001501603640000d880800150344504889071994560b8000c1041c124a0406c4204945e5690700940041e0742aa4544040340300e201641e20403802c8504402030070454003410309146040804020386041e12 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322206052 1250 322204802 322204811
    0x20c1b0120010b060703090312140912010e0105010e160302070b06060c1c02031c06032d051903090608090a110102070e1f0e070512180f013309 63
    0xc078070096001c40103502c0000c104603201c04c110703e4014024500e9001c1202c048903c2411500110b0141780001202c110080c203103410292030354180020307050590301c802036642d220303407540394045020b01c1b50f079010301110110b100303080c50a048a607a50304500c0071200105881008400040348a594920f501b181048440b030b075641d0002c0600031314245001100091454140c9070b500983d64001008101e004941c0304003010b0740070604205011991548005030400c0c0c61551100f81015264420090020a9910300082550a500c6862429140d400c500214200c04425a801e1542007106500140400c1c038001c280e61814404c2c8586401c0b134480300805401d16075640e00300300c0e802449421302405011880405034a09448000380c05000c1300514401c2800220303001c1031428411022038416903540d15142d1600c5c0c0e180c0503118000e4001010010210040030860f880814240400c2000308514000402e40f107182c2c411810742d000350322070422000d800e40c03803690f2200c50745000144201d0716078000005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322207302 1250 322206052 322206107
    0x70b0c040510030b0a120b06040c17010602010203072a0210030f15050a140105070308090c0a17070f060e01050304061b020d02010b010302040f0b0306040b13020c1b01 73
    0x10180101e0700041d611441c800c2c40a1901c5034940d100301c140b0042201e2000103243e9407209600c3d01101c04030040c20f420b103200001407017400c040c0c0188505d544689003440c0c52480c0b121a00141c5603003030f0000300060350000144500203a00190071501c1c40542506d00c9001110b407603000050f00c682da00c0080c0580062070718101880d00940c02100180303c00392040c0044000c807854503ca80450703010b0f561003010485c0b408100d0081d045880d0701d4400741a100c4030b242608589060355085002400c0400354421520241c2e401c0d1259401c0e0002044440703034000070859007415444c1000440c2c0c028081f80e040454040007015480038102c9030000c1d00782030681d680e48903418488041c1203102a003000340424030424007203680d8000b610740c803490266030003009620040001102a441a0b1160b440c0369200d8139018032234201032400564211b60010000100c0280d1040450b80c59032800c4000b1183c0c80d0f0100b03104020440c240103002c000c0968074002510401e140f00041d00c500b5911100c0e8481d50024075400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322208552 1250 322207302 322207321
    0x41d0a060510111c0314091c0503040f20040e010507050406050c0c04090b04210c030e0102032a0c04050105090c070f1a011d090d08191103070e0d0503070b 68
    0x1050204140c1d0801c281301a05100180140c00c280120400070031090f0001141c600010a06940c48054040c0801e81d00046110488a0b600040c2007601c0ca0340916103d40e00180074010029002c225500021044000c0c1c2c204200840d12540c84c80d20441e41004d08002d1442d0b4444100d40039503882c5d06241e03071612928902075203014000d03e4065045890194000180310401d03034818800d91080046042c10a030361022092154218440007010a48a001b090b00180c0124865506850184120ba0500340765541c41c1d5a95140126102e421400895515502e41d03010700c201c5100300c906850038800380d494075000c9802c03e0350042104200400103c0c0300c900f0414907a500c07041503500860007114070100c403603000883c200207106400300f03a070318101d032a1000210700011502c9800c0c07000141c05021080d070380a071012071009080d441c140084c030203c55480c111611800061521050295440340781269001d001d030030a5100040c41000802c0640c00000c0b400421a401103500c004007000545500004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322209802 1250 322208552 322208563
    0xc090a020906040e0604110a020c100507080a090906060e09061504030209011d130b040f0305040f0b34110301140a051e2a070503041d0a06051011 64
    0xb6400b140028001403e41100380b80c032401101c0803035040100c41c05000d0841603e100d10f81101d000b40e08515100032480c81c192207186201142401c2c007500d011070b150343d6129680d000007805d4000c40c82a41701844421598804c5402610040c104506440c1110b4001022000c00600c1c081c0304403a4a24101135100340341d42510b00030744d8091b05010841d41c4440388031854008582d080d4060226207c0090a030b0501031810000309034010038181060b4482da2104002c00390205800e0301444010840007401000700c11102d4000d2450000e11601c0d540450b03500e00c40d1452016040080d034a80e000442c0c40480804e100003840c5501407540c01d854000c0e0310100c3c0c090096250714100011001c03080118101d590b801541c41015009004c3c0900c414040101b0309084d820ba070103840603889840308031041c88504440700403221000151724200743c4a56903031480c3d40d0240e0001e0414141c4140348000c0d00340102201a0006a8030310f090080b80c3c2001c2c04039400f44280c0c040c500c200b0001104004030301d0b005100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322211052 1250 322209802 322209817
    0x1a04080105010605070b090c09191d10050a0209010e060c01090614041110050a050702030703050d1e0503070509131503050c01092319180c080901020c0c090a02 70
    0x780080d43e552030002d00240c002c20000d90310303044e0180c00110400c0340801e021052540080c407490140c3c9078400314031046120400820140341c0e50300707200c480141416a05800d0b001c41c4a00400d010700d01142c0c0c4a05803800036288140300e87c014400e21007941c2c0c20680754039842105031034494031940e0407001e01d40902610480030b80120f20b080c08038405103105d0448035228601400420340504900130034004901105c04105000610621101903520700c01d10050a8003400202290410b40d2030f6182c96041000d680911000304401124a0714445614545025104d0850a03c01e0075450401c0000d021803142e80f00703080c86125410400c441070314041d484040d5107074901400c12205a224036000ea40c0b100003071040790108400100001d500c850402410246140ca0000f4802244000c014019035541d1100c5082031030007900130200d072444600c460403100d113424010101301007540070005400c2480c050089100c60340100800c411010b00014520480002500c416141d9518505450000c0c06002d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322212302 1250 322211052 322211069
    0xc030c0d0308041b140f01080f0703050604110c060610110304050d031205071206050a03081204020411130504050c03062d040914060a05060a0b0a120603061409010c091a04 75
    0x400100d00c1800040f41d00140340810740d1b101504042540064955071012108040c5030030703032200041d420501c17030f800203a00600c4c042d001203614200440468019004140c0203881ca40c8000e0400c00c191600c010115100d845500b070004803e58044081e0f84c580c412405440c2c02a6031a11800c0c04262003a000e03658034649080e01045a4101030744000c1014408181c4000b04a003080340210389031602200728021654858542480c015207000d48010784440240160380c85540c0300403101006006600404894a5007220b101d2801c0c142410081101e40207004940325080500030000f06403295443c4020303500021613092a400c19000000c60510800c01c48150018209040b003402c2092003010403220351600c8050322044e585204110084900844801c0da0100c2552401c001d102c10b11001403204000d00e28006500c01d40b20a09001503407001d40c81240c266a4805011003180380060b00ca98200b0003030300007030007142078140008240e4a824000c04070440d1180b00510912100714086800910034803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322213552 1250 322212302 322212353
    0x705070308102103090e13060b040e03120907120803070804050106050a06090801050105100c0318030c0b031501142704060905010e07020a030c031218080a020c030c0d030804 76
    0xc440c3c2501c0c0c015650000c81c04540c00e040003084201450452a00c0b88401841c49140050036480b0400a40060b034500390700280e803580000c00d80700050008000c140c20b8030820460504002c181c01c0d1504100b603020100301d101c00d0351200e001a17031f00c00889402c5500b525002c0740340d8a0b941806401444103500a0351302122003840007501075000b160182c12100c2d0031000700304680c1d0390010f00910b111000c2e000e40c0003c4e811b250807800640101d403000c20981d882d000b103080e8581c6a94440280710300030307000b0302e00226001c01017100988036071444c1c41000f6828a8100160b0150391890180c9003c4d40e42700443d5598403124890f07480600207107034041c1d101d0003072061200640c0c84060708003c0000f8003901c40f451141e00b0010380d0301c600025170841d0580d81951481481c00c0103440444d9041c4c1488140c034a1103448101d80703030341058007044482c02c0a01400c1c02c0e40d555800044042c0c40c1c1510a0002c5000b6040214070810b2070340c0c3d641c000b40d606501070901016a9a5900e024a00f18408040d00500040c14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322214802 1250 322213552 322213589
    0x3030c060b2e02011406040203040c170309041a0901050616021309020f2706060712020105090c0f1507060e060a23220201020c0612060a0e070507030810 67
    0x1001041d12a4031030040040b00815094049090b54081041c0b00217050b0350300d002c204542000d41c0150360080c064862021001e03120041e00c004540c01c1864010781c0d610210380900c4c545054411013010007950100c442015070004049204c50783d05200c1d462103240c0204102d03141003480510341c402e10f640201000020300386050440018070350030364164020102080301c01c41034102811803c03903a02901d0001c1c076500409880c940b2035010001c0c0b5254101209000020020f01b03101c1900c00200300ca60004a0189803801e002c0d4a40400d03180c109105a582190100c481c0c0c440421209a038020250419913802c81030510b10088d08408146081900c0b9030b000700400d03200c281e400128115944080c2d8503008039070f00002d042000040e20303100c03561070884039a600f42408903511801e0701d03803040c0140c82c51121a5400260325400c66421840580130400c10447c1a00c0d0010219014220000301c100b038034141580014803c0c081c1d243d00805122005012949065241100100601101c2600012043c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322216052 1250 322214802 322214839
    0x10608100212100317070f0f0317090c13090501092102010c180611150711191a190207080c0105090606090c070201030e0d21110403030c060b 62
    0x22a1001510070000001c150b00c044100245000c981d08400b864078174020f24080780c212a4002c001c121000080b605601002982c0300400b0034119000362201d802c4080d8040d40126421001884450280c0260301010030b19520718044014002e4607c8000614065524103140100101d00b4050700030a50b00f10011488034080c1458045031440380c0c02802504000350f000e031041006d510480c41c80980c02d11003400490701c10341111a400103003900701c54100514500600c82c902003501c4440000304075581030a00c0c0042046210800842c480b02500c0d000301940303944400040c407402c22860040c0000110394840342d803e0203020601d1542c2400c5607288507e10301300e0400d41c040b810011055007000e0014040203008200c0500c10030025003441c0541d91550b010540541c0000000c9042c145e5070884038034101000c1107086034081003074031008500c503e00c0160303603501021340e1300c40f0b825181400e01d0700a5100d100c01c10345003103d6041c10900b41c4040d07180b4100010f044200485504044040c0018040c400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322217302 1250 322216052 322216057
    0xe01060501090603050c07020f0f1005090f090417130b040803030604060501031a01051c02030f06011107030519111c060501050a080a080702062209060b0c0a12020106081002 76
    0x91090b01c441200303641e02c1c8819416150121040c00d600c1c54144070440240c01c02c0b130303100d00c1e0000700140030880384c2010900294a0405070145c1b080050008201e40341c1c90700b00b8594900c080401290524081c1c0740554451880241200288070780450100d89101160799502c10b280241240c0310080e52525101e884a40d0369030001c03070304940304038140344000849502a1203442c14504082d8a0ba115040040d0300545040d0300405c1c0813000940003401c14151529144059406140c1e080c40424607820201c000501104510f4804141600a8202000060780028003542c4000b0b00815000b81800c40d0f0411980d203600314229650484145040302c2d061191075540708880b00d101d001c0801544e41c070f80062080b10401d60080c2070440e4400309429000c240c0c40009072a07a240b008100c9403030b10410807a41b5949901010504c0b1300e02428001c18000d180d000e004003000740061130411410100c88040e425500d240300d00f00981445e00e04112039038001e02c01e4100030f002e400041d0459216190020841e402036 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322218552 1250 322217302 322217309
    0x20f1819060b0403021305060a0918060605031f0504050a020d0308090f030a0c08180a081c0c12110a060c0203130e1b0c010212040807110d050316060209040e0106 71
    0x26151280124006004109031804c1d2038018151000f440e02c0f0509441c000c0c100900001d0b03010503804d40c0010b441c6c41031301139081805407040c4800d036555041d240c542c05030f640603000680311303401003201e0103800e1460380d0013808107074104503002c03d864a42e82016410940300160107500490400030240c14181c00120260140c1070b40022a20000c9001e05c01039201e0248403030364030000b0303081000000800c405d5005808290041040f001d080808840003680103051030340990030540011440101941c28500070241400e5181440343c0340d02655900c00e0441030000b0000401e00602d418162440320003005070040103980301808020780d005541c0d02070b6980d0032001c070300d02080140e0080402d081d078101d403caa0040480740f10010088041200c3d03840c5503002010b00d0000381d90b092003a85044460280010b00540c0101145582c40c0450305219858000069900c1e02400c4803070807a4001400c0002251902140c911000a04000e01d00d483c1000e407050303002c184e6200e0f0403c00714080d980c1041d40484101c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322219802 1250 322218552 322218601
    0xf271b051908040804090b04020903030a020105011a04080a0b0a022a0d11190212060a050a1b0905040b040e1b030d021f090201030f0212040203011116020f18 69
    0xe407440c6060071244074804842c000c28140090004101514803504104020900240054100441480805c2c5150042d400c0540140e4403a00100016407042c40d2054558080c0b01015240074100a107085e656144844014201c2c1088000a5540303042d50307040d62480080c4491081703808a50b91403044440c940520000e9441c0520400c1e41c0070903025024100b0030911301400340c120284541420a01c0e181e40e02d6007a41c0100d081d400c000600402803080340e1041803070b02e000040c5410b0848030007080f9001d40460440720b00e403109412920301e40000c00001295400c5a02181d180080130208024007440c0d44025254454543c15003030040c10b581c254000d40400385c0032161415501c0c4412079a42c01005141c0d021481a90f4006102d83c3c9035800030f000c0140103040c0803880754003045480003260302201140122540540500085240a00901d506100c11a901c5414690542501500848039100091181c2070321194841d140d12034240b900a0308041007070024180c9443c405400d8800c0080901c0c100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322221052 1250 322219802 322219837
    0xa090501050a0c1b0503040b031030020f15070b04060c0503130b1e070201050a0e03040510030216081603020d031b0c060b03060901020706060f271b05 66
    0xc0100745210320010808541c0d02c1d075400c58000121944e0088400b0b605890034002080041510300c0c0c084021405803064100c41c0c062a460000790712201c0040b00506c0b80c10405100d84480441060060f00e0241c0e40c04440c3c03030000c101c0b090006007030466080d10010b00098041020f9080c004600d89151140303009090070710903903840d03110031a8513100449004000d181d04000c2000414076640f110b40c0c1c07190945583d8200d4000c8400c1040c0d1031802180d00c440141c1d142c8007001900b501d1402500030b8a0141030040d420a400c100000305480340c984010002c06034081038090440c000d4900e510300054105040c80daa0700075118150380204c44d240b00c01e03000340c8903421107102c0b0180b0134480d8802c0e407540e144190780300c603400da40c0440ba00c41c000e0000356505601c40c010210700c0c0e40c00340401c502510300240010b0791140300385011788c00e0314000c4d17000804185054004120700c05810a2140a4121b5140c03507185c03054081001c0001007201c454400310f04207070700414890b1325401000910540400100409 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322222302 1250 322221052 322221061
    0x60f130515270a03080703050c060406090212060c03060103020702040b0418030809150115050705060708160e06040308131a0306040b0607051506041d010c0e0108150f0a05090a09050105 81
    0x242c038209a411900c2c0c211031040c80030000314040e2070150520600c68a055032600300035410092402800741d5040d503415a0310400c190451501c10488602544000f01034515881d117841152900c0c0001811a0f050540010700e11045547d154002405818000e008100e00320309134088a4030740240d003000310003203004031022030401c0302e000500781350350480621001116800e00d04440140761403d4880030078454144110300028800b4022903200da00350f555604058681140203c201010700111034060000c01c14569a05442d00002c50301078a80059a40ba074541a550081d18061660340c0b2000d100a50002c00100c0c604130b100065010300703c101c6050095440000130400103204040340240140c2c051004030f4401303682e001066a00031001000001c0c4150f00f1482841410144000c01030640d5680480c4c45645030010711004040b10280390107241440e00c0071000e0560800d40500c81e20901a100c0311309a00e030b030350852110150a02500c8071a8900b007a16039a400f412040404a07180d509020005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322223552 1250 322222302 322222357
    0x501030c02032506060801140f0703060806131a0c0307022b030f0b0604090b121507080a0b060a0f0906050f0d090804030206070c14030309060f130515 66
    0x2200d003003d0f00d04001003103001080d100c2002c08504a0708071a01ea13220207000958034020310415482001c081380400300303441e162100d040442001441d0388181447c10b04c09002034500001c11540c0844d009034910340c445001e08119680c120905842038050310100300300a400c28240020f50300a8000340c080b14007407403171500341303240c202450103e0401c075040c1c7c215810020b038460303000451200e1640d00001440d03c0c0c03503404202c4a51142d00300a44064646038205010b09008042c10090211407001c0d00c5403010f50716a0070707035410019001d003040011560215490384a154014100c503000200b00d00d41d03a0b0a1b440016240c045d8150395080802c441c0c1000007040ca0140d8101d50072a565000107514001c6854540e4004011140341921580c00504c808801a100c09008288190217060b03110f000d140781c150540c901c8502681014000e400a02c86409036458841c1035030300b590031040718503449060680000c9005400c43e03000c3d90b400800c503901408618051001004125103d21280800c0c0d070440105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322224802 1250 322223552 322223557
    0x2e0b0306151b19030e09060406150207180204081f020c01091a07020d080c0a020f010c03020c070f05030c06090f090406060f06090f060503040503130e0109180f0204050603030903160501030c0203 85
    0x213000308055103480262071502d0b150069000500500000741142c4901d00d210701c0b068001078036030141e44008001c1c80751441001c0b1604801f41059015450325080005a41c0c4808140005490447c0c120014100881160b0141c1d440070803284020400f00e40c282c2009945008070f10444182564044e02252417144080bc42981000031902d507c680e5880340c1507a103644d68485d0450000718024200c081d13900c110280a010544401c85d900961039078450396225040c10529031010003020ba010104000705e4070301060307410740042d003294010348802c0c4400c049000a40e5a10b04d031540083c00c00200800c01c0aa5842542903d0034610a40c0030355440307500c19148440355004246460342000300410800c0c1c0700d10001c45d481841003080d00d041054003610380c140030481da0081d04280384140014010301c001d40c41580380752103407100514039400140c2c23981400c82010000107401103071900c001440b01e85080044840019024080301d008401c4610084078082c802c0c010580040d05184c03030032807250720000c103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322226052 1250 322224802 322224853
    0x30403081f0303050d02040b03100906050108040b07081905041a0604090812090102160f05010b0904080702040506060415080a05070c08030a0509242e0b0306151b 71
    0x1a240c1d07045403810344441d0082c141c00fa00e03032502004082018845030015602034501c001d501c002d01410200e01034161003c6400183c10410f10408200c049a503101c0d0040d04070070300d814591b41a071201d96481804403010100f455825041800b4003041040c1700349001c00d44e191030001c0804c0c680320441004156500160007402100c005c0c84120881c511000b00150046810400180b40103081e5407400c507607920580065411510303074a4140280007081c0181d80840c0070886120006103032542c0d9107402e40c041d040020707001c0c03aa03903000500704c0e4a4900c101d402800214900d5140041411001080d07440f0450780481e889040c60f0100d0083e5024115008245a004001c1d60035a510044032000512000300600a00d1080000e503407501d40704221102031010090b000d03044185090307038003650b14890388c2c0c1d15031f00c3d0f2403c1c44a00041034000241118240c414003062550350391a2403000603501c21500c0005400040c0004e6014200d02c1c10500280d009202c4200b50703540e200c400c1f1115407506c0040351 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322227302 1250 322226052 322226101
    0x8040e0420030a030513050306270c0d1203110d0218040b06070209070905060307030204031e0503040b131e0825090e15040605090708010209130b1c060203040308 71
    0xf906070000f40103d015006c0451010314914070665944006841d00b1800e0f9280750703441c500e070155050789507945210240880f000c20010168540a50007081800c40030714400b40400c1d0031905509503842c480e41044858090310140503450706d00c16003900009610041007034401c1c917810589011641024003845240c0c00c0000c04481c1825032503001e10002ea038000b402e0724104660048042031599550002c6e6000c1c11040d81e00507125815442c0070000341e0505248407401071010042000010000070460703042c1d44501600c16203450221540c00380319200c5400ca502c0707181500d556509080c0140705c1800071203814a0840d502c000c500c0008480c0c40740344081001c0e100c8a4204107109440b465042900c80190200865455920440c2000c4521106440c2113501948034000c1c07200c1c2e030b8010498403000c0c00504000b117180c07043d400002012901c5415a201c0203645842c0400c00c0c9a0311428800141b8007103c3c81d0200c00280d03468031200950044400f1404280c00b80b02203405a00040c0c0045a481c03c401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322228552 1250 322227302 322227313
    0x10c02100809031c2c07090e030408120d0605060a080103080a0c02100305071409061b011503110108010e0f13080f070309150807080f0c040308040e042003 68
    0x409048072100700060015099100411a803020103050384600030f00c0071000d076000a60018041e036203908205a1000610701d09411168119660340086900f0f01184e010340d00c0007490728011510b4508501850380808014000c4803c00002640008000e01070b1034403071142000019240c0d803c0040038001c0c1c1c089000040c11160040c03000901c0100144010340c0c150820b980300320074550024004034480000394001a89544c107000c992504184e154405844007a0440c0c00c4c080d440002c1041c0d8040ca0041810100c1c40b16181c2151260a40c80148281c080f20000c4007000c0e22420420108250844071900103401400001036207900050000e000d04200203410846899802020b940c07101e194800f66685141040f9000100d0a0710f40184181c504c40e13202c42403c285030203403000c23607140080c45000134000c07035200b0804410b90110144c1c1d4405074050340c03010252500311070500c10b8084c3c0c1c1c00080c040c030740004010401c1880003c0c0039108611405c400c10651602a000b0f01c08100e10042058050303005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322229802 1250 322228552 322228579
    0xd09170d0f030c0c06050118050106020105011505030a0b0918070506131202041d0703020406051c0b07090b07111908030f07080c19170c0c1201091211010b010c02 71
    0x43c2c1c110a40480b100d04e0192540541c5454610840b0004c1e800540c000701c40d00c40c101504c102d503001e003070300510f1540002c000f5989400b40c3c80c03000d01d8588800c03d080020000c009404854075510601d04120081e184007102c1c40e041c4a5460320300d0750505d0a900ca44a5031400185a01d810350403202d1000d114000c1c00c4109150401c1d29881d100e185004aa00039141c0c00002e51343c1d00300004075001c41201100400d075003440e500601c021075005800c114000e0341c18202d2022511072031054500295800b00c5c4052140d5201d0000312005030300d5420034041c041000070a2000d00c114038460b12001e45088030101d61140d0240100d5040f0755a501c0380f00d2054000307020759101400408080e0010718090741089107000c4070f00c21801e04104404c5407082c40240344010b010280074400400c80303a04840702008510302000100c046035524219142c41d4070640041c2d03003003060410207402c2141140d40c841d6140c0400300c0200005410803040c03403d440d01ea586851a90240340d84284d1504410940140c20020011107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322231052 1250 322229802 322229807
    0x606040501030f020c1f06060503040b06060319050a020301050a0b09031c0201060306060803070b100e0f06041404050604050f032b0207020a090b090a0507080a0911030d09170d0f 78
    0x1d003070721008000c0c0d81c24484403040c3d01081c0032440e201c1c15521b100100a04a11840c50100c5225030030480401c1400d004020003c0c8044d00c071030b500600100c55940e126540c5091090014407818040ba0f0300600300014010200815000346058036421100140c402d03071107090021440c010382140c10f61680c03041603030341c1017400c495081c000c0b00005480040340c1c2d162a500e0740c50903110251310035481079000180c018103000100c9a910342000098404074292440e041e10080d030910090101802051210301055055856902a1000041c418009005407405007000c5407900d41c2120262905e005000c0d1514500354040304840d8004110308181480051914840558031050b00c50700e400381c0c0d800c0081c400565515880100100340b042d40100c0c815241000380102c0f0030000e007800400500308070911160035008030995030721642c99000060191081c0c20300c00340c41d00f110310400c0e4141c0154940031400d15030114000b4151015108060100e4401402490765409000b24000000701e030745515450340d81c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322232302 1250 322231052 322231061
    0x82706070c0204110c030c07050a0f1503090618020f01030e0a03030b0310020f1e040302060d020d15180509070501020604080a12180210020604030206130c0f03050105090f06060604050103 82
    0x900141001603410400c192070f4110364400b0b8021805c1c1e50003c11802c44840d006c103c0d010286c0400c5e6521108685440d1440002d4055401384e50310401e120380100c000e0b1440303030348140e1030150040300c00e00200808480c0f06c1126524460280d000c0c1038243c0041c0202c1d40030380101659a00014028590034042d9207048000b4814030071034a90501a0309441d41400ca8140054204a28041c0640d50340c1c0720161668a200c18000100a0440a00f030100304003581c0e074141600c2030305000c2000236950300b4002000304d000301400c81800c3e0601034150340c0454803aa0b40c140300c1a40c00d103500400c0107162281084680d94038070314480c00740164451340000d00085c0c400005440030007104e0404900403550f800071a81515000c0d985034507001401c1c7d00800c00d610741b43c000100713120043c1c0064040d9060a80700291a408010301d440b0807140b2901c030800401005184240082500480c48020152a4a041e5020b8041aa407500f45803040d14a03508130002e0200e503450244400804051034a4500001940a003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322233552 1250 322232302 322232327
    0x308091513170a0215180d05030939040b15071a010603050f071d010e06121306060b03010f031502160c180204060518030c030d08270607 60
    0x41c0c040ba140d070400d9114000a000004601e40103070400040c03031001000003d80041c1b413124002000c84283d1010700300424401b440c0102c504c0c115a80342d40310b6a907d8500110303105a80c07496241c0f8000c4091034045401c40c0f41219040c42104a0780c04070780810071050314000c0760b0141d48141d00001c0a045c60112000502945110704280b40010200380700d00f4102000980c01080480d44581c10043ca903880c103582d040c0d10080798200300440c01c804000054540560040003814449c1078040fa418039903640054800203202e21a80d12043d2400002040c084211540202c41c1d4a04101010031200b40c0502602d06840c600541c2c480b1052454940300e07080020150005049a401c1105070106030040c0504403010f800382d54120210b502c0c0004000100d0128655411060f01c14401804000d42c09002c4504600e001030040070f0390543c9600090800101e01070701641881401540c0244542104145100d5a80c041003002e410001200300042c0174002405004a80c01680000791413600070010070070034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322234802 1250 322233552 322233563
    0xd020705010333030b0f060102071a0306011413180506241c090506070f050901091703040806130c0503010c050702010c050f01020a0201020702040e0c100c03021015030308091513 78
    0x1090350390310781060f038500c20f403001c09089001c0380c02c011f46545c04000000c01000c18422800690480034801809400068242810401c00c0314450000c00c44007020784122050303413001203007039603543c1954081c100304042840503134500b00b0000803420f10340001004440c2100083c20008001050130402e4258050161245100c02d246510214947c0314802c0140280c0302e42c00802c160b0500c0140500026440d46a04003041820403058000da41d0040080703040301d01c081c0075019148600c240311420f40c0140d0700884801d00c152800c1000070140480118202d60254080c2c01050344c0741d02c103150903100d8610040002c2102001740390300652140009203540c0b4081d40c00e50f0600001d00c0c170178a0070390307204071000300050b0340104811045d46807612413650300c00d1611005040d000350440c007040c1d800a50340645001d100104101206140c02031066921114050904200c1d074800b0000000c14003086000540008070010b002980000c00003c0490744100d0701403200d581980d561091041c40018444111b90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322236052 1250 322234802 322234901
    0x41d011508131505010501020c0405011809060f021602090a06030309050603090a12030203011e0312030908040806040305070b0a0509060103110f03010f0608060c0a0e060702040e0a050d0207050103 86
    0x441c3c1043c1c0c6078009260035110200701549000002454441460f0000784542e182200410001100d0144002c1500c0304840114504000d4107051004080d8034050f03001c0e507400001d403050150308902262940b180b00721000302468079400307441d00440b8480d02000300428400d150601580c9400030207140c0c010345240442d031400313440e0350760044595132820303088010940200050020601713000061101524032920740340c80303034590745a49820619001ca054185030751038003035100380400182201c1c00f901d45841106d0701402d0a01c8c00408981c000d003800e89107c041d40d0701254000364940a00b50080b07004600074002c076400c0d5110000a80c0c650a400c0354002d5a040303001c0710503142030103002d1408095800004560749088106030030008001c000804203c401c000102c0f40325001aa800c400c0300013560102d894255a101180c003c1c8040501803019101c2c01d41007208004e80065480e00c88005582503070101541d17507005405881c1408421381c817404880d407150702c600001075007400404d40c00b1a00040b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322237302 1250 322236052 322236091
    0x12070e1210060509011a0d0c050906162108071101020d0f0902030c09010f0306020c07050a15181d040614041203060e0f0c0c0a05010e03041d011508 65
    0x10301e00141e1403201449203440d0b0100b04800e141400c2c04500400500c0d0412000803607210a0b42100e2190032240c4404558410062014500c6041541d00720b60015100b541d0b074407001c0031801c1c03001c040a1001c40b102c4415501e0100481c0480c070503028480000e0b101e0011a486851043d0350300b0314071110b419810b650a202d51a82e0000b0360040705070134252031100092005030382c01414100104440b402c0d00412400004010011600100d0006c46ea0014401038440100c92005802c000705640300030744c440010302011504410030340c03a07410f0600141d00e4020950001501601072011a4480c4091900a0721903402d046481c0705226580940702d10303800150604aa0b0040f40c083c40b00b6101585e00d28820141302c0fa50780d42600c0751101501c80491198460b10f010f10b05140c1e07510f001880d00d02000408100c40503810000c001d62142c0590140c024000f00984048582d544e0f00548aa12918180200c44003203820b01c4a5034503040c3c2d13041c084411400780c05036409407111400035140191403514150b100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322238552 1250 322237302 322237339
    0x9090f0106140108010b0f04050613090903030b01180e0606210c07051b1003270813051206041412030106090f060503070f080901020906070c05040606020312070e 71
    0x29405400d0010b903180d2002054000100391030b0050308904d407009070800c515840c228643c015901156400c0360b0459032400e40042d2540e42d02019800080003604058120b4105030b0103400c0220204001e030f03148481500e8186036045691103a1007060305192100e804140a0305200b402050201000350b880c2503100c0c400042d4603207001d01294590351040b000b08103a42040f0082c00f41e83d400045c0e00902d25100320800000a812600110304403082c0f40c0c0e00c0000010700901d458038103030000e0304d40741d81035202095402d052449034081000425070120084000c41c291074061100307c030403c2503000600c11640c40d5582c884009002c480f80941921a00c08035100200c0c64400550180113140e5528211506d00f0109070621806508090140501442080a0194401c2041501c8001071034400c803a615812021802803140c00c040c29000300d0005003c1d403c1c0304010a107102262019036042010036038803a800ca840e030040002c6c110101d0061004214820f01c81d07084240c0499000f07100e83d0b1848450903a6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322239802 1250 322238552 322238561
    0x1709060f1b06090f07050d14010e010606020d09060923060f0c06070e061e0418020c0f060106050f0903070b03040b0609070e0a0b0d0209030d050408070605120609090f01 74
    0x3024001c48045103074030640c50051003010780004540f4004e002070003d5035420764407042e07039009140c02000902181402d0003420100b0742c1a0304d031030000800040d01f100302c80301e028144500481d00540305466030f4501c540d00c1400960200ca40c69611806041e0820f0102100300010203041480e151041c101c8100300d5850f0001808001c21041c013843d6a0900c4003241414003000038000f005001042c070000a054030356070708490a0325002c900510800800e12901901c1d03000765001040307000c446c2c4400b000d0703a10803603004066034134204007241c409402d10f42c04c441d41c41030240150f90000d07006002032503a007045000030381000b820003070950345015116120922242c004840684200515806100041c205140c000da0040c0c03640c50321144a4a03940701150009000380310f11398442c0d0001403881d50703641580c1d041c7c60550000038150742e0500c1ca048402415034105006e05542d5005000000804500a104a81315030080c070784c0001031692034000b00260076030010b00503131103030068034001007400720203104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322241052 1250 322239802 322239817
    0x1b0a0305061513060e090c22090507020703021e0a0b0f0403020603040b010e090105040803181501030303020a090f030203190303021608030a0606021b040b0d0f08041a071709060f 78
    0x1640c540c90450300a00d0716400082c494011006d0314240708140000200712401402e658848440c074040c14000880c0000c807a500040d900e42c0341c1010700c415141c0c04100d0b182168021260101606410618006016040c0640d2940206080403c200b5000d0b0900a08540180c0148690420342d0300e40100700e0542c011034040b01d46002c0403005002590000550303540082c007082c020816841c007955008007501c00030300705080300d801002c80814030082c10401d003981c41680185695481d41d4074a005000b94010084001c00304625200100b40d0400d075100031400c03640c000b0f00402103900c118090314000a00740c00103400701a020000a500ea90800007203011862240c1d107803070b81da0318103603000381c08852280d04400f0454201c00d45206c000ea8098403241c10064017100c00190845d4024000348804080d510300900b4031110100359001d000c40a0007410440e049504010b01c42c114403006040648682c15000b0000c2914410810b620103191001e40300414010f084a450200c0e4407000f50b186801801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322242302 1250 322241052 322241077
    0x10e0d060509011d01150303080a150816050111070b071401090c030309050406050609040c03091a01090c0504030210030f060f0905010317091011030921061b0a03050615 74
    0x21510b03029001030003500360920034113a0080006542d600b25401d280c0515120150400601340d0100d1a410715503400040c2403221117002402280c5e0765043c0e42c1c1c85160003113003208031011440c1c00180c40d5014103100d442400780d00c4054000d40d8245005108590030070402540d41861403815020070300350911428040328014200b00008516601e0024060105030300107501460800200300b1003502d55100751001c600c800c0341c0104800040480840090201107005010441042c2115140c1c12116004034180e48203140306100a00c2d860a0981300d6100c0e922000b90480c1d40c1e584040ca0061180d4002c20141c0151000030500030f66981302c1c84141c1c2c40a400010401e80c0d034030010020443ca100346040607003040c0c0340c124100799101e00020320b00d0601c090004244190046286d110700400e20841d903d151005010500f42d42d8006250f051821071055001098803502c00440d07003840aa050030302c648100402014500003c0b04801c401418003d480681c00106842d440001d00f4544400f5012402009 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322243552 1250 322242302 322242311
    0x6102c09102f0405010e150903072601060e0408070f140102120f09030a14090a09060510020c030319090f030b0f07030b010909090317150f01051206010e0d06050901 72
    0x451401c1d100507850070340780d819450300f0001003201d0b91b0015040100120103d800c58540305901d0601200d40c03103042001c6170b043c01418401f003160000c0a0124625000c1450141d1801c091075090600b240e545006800c880c0103101c0002c1c00240c980e00040810300e10a402c19400b910b400e03a82d880e945030b081b240c600e42694012604001415843c1c00b00740d409100100e5a012a00b004449184c0301d120b00002901048400b07c422a40c05c942101207071401403010308030b803a505540d411004c00a112600440c1d1040161081103160741d44000780300307480404000c0203580382c50010010030a80700303d4400c020061150700040020344840d0300d80c0300c000a40c00346280e100b4a18181a4a16016400504110a00d4503140c090318050742d00040520a591070810b000501c0480c2d41005d9a004041400014500e4141000c0240b240c0c010034225041400688081254805440054600c3d01072403440300c024103105400103207158802c1101c01c3c603100000e01a1240401540c45080c2a15812140128940e456 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322244802 1250 322243552 322243601
    0x4140c030d08150d15050c0c0a030e0f03060609220503030408070302010c080f01090b0a1e030201200a08160506160923010f120204030506102c0910 65
    0x3c203400d484100a04503011500d100036591030941d0b924440040c560326594600000c2e19100c11203046411490150b022a81038840519006100490102d00180500007040f0f14801a050000300349001c2c98004208220b07035070b5030911301c2400c1852018220182c030107030b07980340c008078100340300950085008280b410380d6841e482c1400f0382074407108180c1700100104441003001c14003071010740905560300c00d413001c55031701d010301c0004803a02e9071034200303000c034142490032620311038040d5102001302ca00c00e8880051501c0341c0c2004130701c1090b6000c1c00c00040d0300309154100c0040c409800401170100080055000710045813607551402c441110752a00d41020011003600440c0c00c00344d02c0d1300070300182c024054000601015042034240c808040c2d4140012130303181a00c894083d4240b268401e24201c011503c9a40c1c81c1025942d51405503044040d03c040c82c2ca010400200310301c00c81101c42c2c0f040205460510f43e20010040200d002020b109580c0120548031b5030400290103281c40300b107004061031550808 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322246052 1250 322244802 322244821
    0xe100c051201290c0c090a230105030c09061306031b05030111090d2f0f0a051005070305040503060106080403020f0601080d0f0504032a0602030f0304140c030d08 71
    0x1060b08160312000c004620960206200c0400d20100704283d4402d0b51110b85049a45141c40000d40e5841e80c000c2c0601c042122082603603100c0c2058911840725400058502c0c2901c003440102800b03079a8043d0084828052a03061280815401c0381d4090903940c03485030507550300021510710741c0040390700d41d00022200500c130400032407486c007400c81100200440e0031f82c89500c8149100f91502c140c0504910b140442c00c1c00403504168210901c3c80030101c1c00f01c00002400c0806400782e0220b80d01c030700300482c60200740e0b0030080804402c1d514040c081d45441080040155070a07080030740d044003000710800012890707880c107002c0c003802015242c440c1e1802d0705103454007909001242940036600c0e4800d50042002020020b000b82555a042c1004103080440c3d140445091140c3e41014000709200d03007550445a00190b00c0c040c4200064078140042510b503442245c0300c2c400c0041c1640001c109201040c08101d0f014140c4040390060710850710b90f04150350210342868480c0c140d620105098038200303c80520b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322247302 1250 322246052 322246087
    0x204050901140d06050711060a0e070f121b081c0f08040b04120e19061106010b0a050d06030b10050120071502150405060610140703030e100c05 63
    0x3600421100c216400d6002c121a08540e00001c0c00d06038445d408a8030880c094044840d004030b800007a10740038a4000008406015a50b00220143c0b10b0060300003043c00a00402c2d0041d1040704100070203050301034031000311a04074141400010708400100081680b001c0240100d0400c3e9070480d80a01c440b10800030b07008a074032080c0710042c4a5000704000004050503050365000c0d520914414010030b0342042160120469014540c20096a00842122408151000e41203401c2a6281481d030707507001c20318a46961083c0715061805001748011003543d40142c01401c1074030403281000560980d640c0700c0c290f00d01c100f0b80711705890b10f10480d07052206580c00003000041040d01c1d50508140c01c01840750782d503126010301c41d40064850704420710780e02c640709002400c003030b45035002c42c1c00c034a0a10341801038460605980e000e115041c80c06441c1c0c1c54500038480000800702c4110601e00b0300066031829405465034491b8500d96018a19142582c9001c034410751007020315075500c16813181018420301404c0c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322248552 1250 322247302 322247309
    0xe0906070f0e01050d1505040609050a0b06070b0414120d0203071416110409050f0708011505150705070f080a03140c0703080f0702040f0b040f06050a06030911030a060204050901 78
    0x625182c0c405030340c0100403a00e1290106500083e034480d4200103499104041d00304079805030030031200164200071500881e004001304041000803003890700402a151189040080c60803000c00b0004000c512a12448041a02808141c90880c002d008003400c0c29400010140750341c0b540441071010f030640c0082608408980750310454035003016102040e0a14005150080c8150003192071700816840340c0d042a4201603001c1c2c1102c5001e0004001261249040e01417601c40f5840c002410000c645e170040714030115a0040c00700707100c0c894002d1340803074071360701040382511079100c1c4900014101c0c08a4080c4d000616110003c0e01c80a0042d02d00209440c440b4104140c071168288904034205501080d441d044951248039540e8980e0341e0040c00c40280a001c2d00654010f19100c07141c40c18000c1a04111240c00c82200d0401c4442c04a01c01d079000c440b003d0185903044140c04209100043c0258040007840703008079060200442104006440e00700443c0080380c0864011808001d2401c040c2c2070103000d07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322249802 1250 322248552 322248557
    0x303090b130201120b0409140a02090705130501030f020c06072003070b071b050105010902030f1e041716050d2d0c03050403050d0903050c030307020607020f04060e0906070f 76
    0x784140794000030440300040c2c0740000c031683d44110804039035544d03030b00c1035042540c80215034003000384180995450704200c1c1d030164010555200020240380c42402159010700728034030000016414040110000c102c00000700d400340303600b00038460f0420010005030307200d10407542c2c440004101000c00700d5401c4030716001a0b40998014807461002504005030b150340328100b032424003402e20b50f011404038950420308004e4034552070302c40003290001042d0021480340e50300c1690f015507600c505001d598401e40d16581c10703065104240100d00040c01040f0b454803114190003040341040a50520201c1e41005c5c0e40c000c940c55803200342c8440c00142c101a00c0d007420590b24000b40800e20481c0e4039100c5850040480380c0421065200b40e0040501600540d03000d9500300c01100c0003a0202c0c0009415103820340016185403080900c1c0c68030354078000088651f001e50140c851814114a0f9003400500c020245056500c00d44a030340206281098510403881140000300809041c1050980582029980c05a5008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322251052 1250 322249802 322249831
    0x308030c160615092708040b0c060601020106060c110d02130e010e100902100c020102010f021206010e27060604030f080a1d0108040212160602030403151418010e06040303090b 77
    0x52501318100b450a25001c00e03040080f071024185006e100902c20f0b030300111003101021411481d00c0500240c400e1081c00b0a070000c0016588800c0700741c2c1c262680141c0100b984520b4262486542030154102c01c0a501c0905840e5042220750345200544015070018401603641c0c188441c800441000035040e48003225074208100d00054000c0380f1003903607400d00c03030b02030000c60440e441c21640301b50f0000b0380640c5031400845d01c414100d003152685a4042c0c81c8103002841c4640c02c60254070f8088100200300800720394901d407400d020280014440002003125a0040c800e02001012030302810000d112103204450f01540c5000d00d18028000301400000021100c16444660030b09036005028280c22030340483d00c1c0000d400701902054900425103480c18208038107408006020340d000400b0b00b00341d07071185903880c9880443c1d90841c01200c0d000d00f481d0040814440100c0e81c803440c0c030500501c11682c0c40b000480e854040b450300710328068051703d0850000f0740c0e44821509216000c440e0b40e420a0942d00400c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322252302 1250 322251052 322251071
    0x3030f180a080c0d1b032103060602100b0d08030a15090903020604111c0c06090e0613020915070c0e06030303061f1b0c080d020607090308030c16061509 67
    0x266500c035a0f00c422401003805404460034045801601d0300b10096058900030040d40381d29121144000c0981c0c0702c0b4481e88862910943d00e80280150801d4451a074010f140c1e00d1424030344e010207046880452500700180800d410003241e10100103500c6102a180085010641c1c1a941c07110580c0c66840501800d140c078000780c0010b43e02152154205402c0307a14041d04004100014500000c6148000500311800f9800c004104820080310111342c1d840d292022069580e031000700102904a82ca294820001100200808001d038003400010502501c40881d0500312070070520b55a0280d10243c8081c080410100300340b15032030b0700150303001e10709030017440c10f600302200031a01c40807000d85004140c2c03e0110b441c0c00410311818a0149180e0398410261694201c2d04210b06501003e020710320890081d880122101c03030000550500691309562500e5000349141c40d005016000500f01240c400d00411000541341102c14401045600a140008100d05003940381c00500c40980e00052040f414480d404 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322253552 1250 322252302 322252319
    0x12180e010303031d0a03020601050f0d05060f07021e0c03011a01020607081f0e0f0108010507020303160201060504050106030209031006141c02060a020601090b0105030115050d06030203030f180a 85
    0x9045030750508021034940c2ea456030104ca01c1141d000f03005024419084504c06040e030008000e4102c0b91309a50041c0d090301200c05100b80301c0012080500035500c9400800c0f01c0c00061240154441040c1c415542803030081307503400c0b454000001940c0001d9001001e0200070f0f24080c807a071003d2441003000c40c0407000b003a5002035211080140003001b48012540060003036149604040d00c8000c611017103240c488d4035001886411001920718030040310b816400491929414881c0c580102c060783c00441c01d59896444000c112407110b403410045540710000054191102e0040358081c0c002c6071800340c1c8810381d40084c185032481e81c2958407581400c15004200108145101504102007590350403c1002882c000c43d00200c1090b400035000b20001610031403080d40400c846040c1d892500041c08641d02550044415000a010342100d040c2c408843c0c0c80fa8500074002810380040301174021525550b04c6d00003074110b801c01c0103010410000058071591001d42595101e004003000c980d000280e9052400781d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322254802 1250 322253552 322253579
    0xb0a06021b030610050f0f060a0513141c050c090f09010507022d0a0203070603140a02030106051b0a0203070f17010509070603021630020105060d200901031218 70
    0x1114010031059210342a01d1311001c002201f0120f01805041c0d031400700800c0200365a00c40d9550b404200e000c201c0c00700d00c10745d044441d10605400200314181ca03c0c10262400c058041c00d84040b2001d2050701c4000105880e02d014161040e00c1c4a400c0040b50301c1c00f130101609450009001d14115003182140c0c550341c03801c1c0c0107000c104444145045260000c88244a80b40c001c0c00d5101941c140f01d420340000c1c07115416001300036204000001d28681ea2103481249060780401e0250601090f81070025442e907200b0003400c11007003010a4200c81c40340c80d554000c2410540b180e0000da1050700e09400501819020782e100500c842d1411008104514004c000e032921200b01d406148200b540004119510800b1a188000700c0741d0450491a010400341010303030240c5252582d4140040c00f4909100d03a800c0c018070a4610441002d840510201c8175590340c0c2c200904400812000000103949490003a01c03000720480c0658407a04801903400d014000140001005136840c1c42044151002441140f071030040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322256052 1250 322254802 322254809
    0xa0b090721090b090607020705060a0e0d061d151003051e07080304090c0207050405220201210906151a090310020705101d070b0c010b0a06021b030610 66
    0x22001e181941c014010020700000800680420903100c10321441d00c1c40441c5d0b25004001e20303002c0303076000c1c1d999006000442c068030301d843c0085a01e5507a0f900c02400d100e40c2d0302c0d41191044000184408258010000a210507c8280ca065010426081100400403030240d0004001000901007030b15581e05c075a902d048400017101000b40840310703101c0c8044208155009002c00000f0760b41c640e17455103d0302d0020000340b0024001071091550004460405201e0716000b80c1c008081c1c4005500d4505142202e81c40000040f41080440c0c012240c0c82c040040a5858100e90f524010907481c03d070317003001c03000e86983c8e0b005d1541b070320590b6004214060041e011502030790000e055039a141c440d520000b0341002001843d000041e030000038000304019000c5011030400300c0e444000c0040e0000c0e92040c0380382e040c401c031001d0541e602c540018460309040070054009114600c0002c1888015100803070270a40580e48000301591182072002012024216042c1903500164010031091400303665000d41c2d00074511 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322257302 1250 322256052 322256087
    0x405090609071403010219020d0807090501050906092206030c080d021c14070c03120c020a05040b030106030f05070617060a060c0201020a0204051f0f03050709020906160503030a0b0907 81
    0x4966668070348080d0161901f039000c6c0303940398112a6600001a44039003401010a0000340920f00103001c40e805400310105036401a5200c80c10203907601c0502c60180d022107001a4024002c1503c1700700c0c0d00740082c45c2d07140d055a81da00032503071701e00c0c61520040e43c01b0f21340c200c1100d0f074008846110100b5400190580322034800062140030b8810b0000594046801140141c3c982c080010076109001101056208607442075105a1080380d4441044642c1c0d400c0c610008d50181d40c2480401051801c4d41002215400040001698682d01d039900041640440030440d080e402694040188075088000712031200b8140403102c3c0c041c5480000264286042d0090205102a4061890959100304030a251007a1b001d03100b0800d500300601b1020381d4a290301030a04040240d10400301d0720321500c124920803241d0040c01440100d0a055552001e900804040341c0c100c101486203101d5101244000e5840600a0010b15a64207119400b00d007512450b80c0e2440c040c0c0301078010b0001243c0d014500401201920 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322258552 1250 322257302 322257329
    0xf14040b070605060a030b01090507080123091e040f120804030e15120703140115080f090f030a050d060506090603040b04140f010501330513030b0f06040509060907 72
    0x45c4d50a14207400143c003405900700040b0300f088640d40428021040c917103d584040c0e80e00c030107051101c009580a44002c0b2030190b201459802d0250120b07412085504041c03543c080d02a4a1612030001120107503482d040c000b5501e4140655615040c031400d801b0328000d9101d151648000e0501d0310385c0000140030705142d130483c07110a00c421081e200354039881554006141840324004019201e00100545443c0201000090082004444081070300181d11820107569940f0006841c1280003443d0174140e0040c81081c00403103005000074000c5416a0f2981502d400b0440221011034080b9005140183d508119224032603036642e003541c2c0c0c415800700c1103612954a51078030744807410000d060750059100b10782c1c0c41941201d064120070306a9007001c80100c00806142c5400c40107280583c81074640c100501d200d5409a8851001010030041e41030301142c1107507880c0d41d8103080841c1182c081d5511022172003032021034501400303040d400c1901c40b80204001e00b002e032039284d16411184550324410845 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322259802 1250 322258552 322258561
    0x31404080a03090b07081f180513021002060711060411041806050a1a100912030c021003061403011109010e010e12010c12050f04030507060f0c0f14040b070605 70
    0xa40c00c40400c0d0380d4003136800d81e050b051800740500102c0040d10304500007001e204075101c144415504060441d40300309200f0724019004c03c3c4120007407078040c04002c5488884c05140e405a00d41d0241c60303440006580c001d21b43c07443c0c0420014042800307103c00f500035800a034280000304169290024030210111000100c62611482d1110b011030001c800804c05400c1034200096840240c2c00304007040860340070840428a1b0204004070100d0800c00803010442d02c00c414040060710f0a00003403120301c42e040a520131a165000a00c04075001d0b1859000203445090910200f28001c8840e4001c803016802400a00d00400a080941c0500000c0310704015203402d508507107030301c00d120410351400060800d222070b4400c002d52a02a10309135030000003250720015405a00c03801d52080510800c4081c010707110a450381c1d0b07000c91f55a48898820360340d1540f1009680a06007051240703504100503611112000e11803007402811046002e50000c03441c60050004011055900b1704442c2c0c200d40c00b00c00040e2a03940c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322261052 1250 322259802 322259807
    0x2041e0f0e06060f13030c080d0801030c30230d02070e06040618060509130f0303020702041d071415030604090519030302040609090b0d1b051c12031404080a 69
    0x1e5005540b00d078215013000005001c82c7c2e00c01c1030305543d8124251a5940c0c11100305803143d0b0428440280201c45401d0104400e0707056a85012205200070040645000c100d002032500130700b090000c0d140c40c5062840780d109802e801c030b90301e0a0200e201000e8909020b030b91344040d440703a03644d205190100070b00d01d001910030f60ba1a17001c034015105d104899888090090700e001c008200a002e0030b0301550480d00460b603103d0160305285040c50740f02a40300f241c1001550704401035000260b0498001342c03203014283c141054888440b04000c0042c008000051030142000c000b0840d0f010114080c076503000704007904158581c101c0768030103000c2c0c50200704103030382c3d1601d146080c41c01d880c03084080d0644030310381c4101076058000b401103682941c3e60390700a9440f60b404074100c0303001c00c40c4154400c00c061054800500b01c205c0c03141d1303203548030310b040c04d03e540ea02c60105130081c5d181c00780390b49980c20400d809410130080b603100007000a0785290801520344c560f03203002c45004001d407025040d082d004c03882c82c50051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322262302 1250 322261052 322261057
    0x9050a0b06033105031c1503080f1c05060906040c0f110f0303070f02060601030c05070201080703410f0105092802030a140408030604020702030f0102041e0f0e06060f 73
    0x141c00c840944280d1070320b003049502c1b90803180880b0300d1003c1c2904461041c120078002da162840000c0c0b032482911781b41d5551140d0b144e002001c0c1e040c21003800e01c400c80d00540701542c00e070720079100d550000c18546861010090b8240b0011710b8a4820f42c5403e103c080701e0380d4480c5003000102d255007495009100000310b02071914402085a662a2000104110505503c959030031041c0e55603400301c602c140c940000540948201c02c00440010b03500b44189400f540c864421190400d1042c02c0020703120981d400074024040004003408000040483c1d0040c2281c000020041900f00400951945080c03540715180013040c10301c96140f04681c1c540120340411050189020644c0b0301e12500c00c1140c03180340c1100c010f074108031040e0146130324204890300c104401c0c40d5a580305a07405540507107150b654408000080d005088144e0b0544034004c5131741c114290910050014000325409140302e03842251552803a86900c2d0842c1104520400007080b425001c00e00d40c64100b9400c54085444400080f0881c4450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322263552 1250 322262302 322262371
    0x3051804110a020c01020f1f27080a0f050f0409050910020c0601241e0302090a03050a060501080307080304030509041b08010e091f0f02070b04080409050a0b0603 71
    0x1000001c0e80c2c8201038000529051481080c0c00b47e90f441508000c4464684840b48920341e0340328030710800500e0400c0141d01c03955040d15a181490059101880110480d0001d80001c5800714400a00c4040741500224109003e03036413032904615144140e80403206034000d40c03055a440030f480e0400700d444100140901c0d41e001d03902420840d1518041c040d03081d5505420320500c0d4018402d290b40e0003804188100100302030045848186003030844c00c3c24030ba0320038000604401015400c0c40f180c0c2d0701d5514000124000c6006000808411b001d600340b0100b10303030069212400307a5004000440004d0b10744800c3d2640035401d41005d5460780200400306000d000c00d10119000758404c402c3c283c000300d0308031924505840c001d00e000041079030768640980c0c3d10040e800041c42560141c00030703d910b00300d0f00e81204510400c079010150500441e40d88a2402010564007100c01c03030b00202c1c061118004d03e105440c0d0100302c0c0c150602480ca800404682c8501c80505880d0f6080c4054039103070070f1948600e07100e0528 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322264802 1250 322263552 322263581
    0x90703020d0602130605030c12180d1101050702010e100506060d0903020307050d0509030c150d1d0d0806010509061e1606060e0106020d120f0203070504060f080403051804 75
    0x1c85000d141c180700075448400e4010102c80304550108600d4828401c1c0ca02c18000560038508d8902c3c0710006d402c106100900c109190007447d00489828001032048036258041511210b01a01c4003200690035500010501000c6a00d0000c400c2c010590005002c903110400050018454a40c0341c0461240d206084411401e282030581311410190700000401016003e5803e0b10106c51101ea03088540d4420b4560b11a49584556058506468005101140b030f640785010702d0b143c51a5400c03460107940409004905140c41d017500103480110a01103162092a14603181210340307803940000e02036000312480306000c0e100100704d0b000c0d1009407244044440294803d00398442c5007060000c3c80950319042c040b038646044c07020025900600d078296031705944043d00030300250304c260b40c421544a000c2d09405050140c503050780c5419003070980700450081c00581d0b00c81e84d80d1400c080000c0c10500c0308800343d034100309841040002180c0d002d4103568520031071b08000c85031070300a030340028081c01d99034000343e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322266052 1250 322264802 322264819
    0xb0a020c0114010815040507140f0a090b0108010e091506040e060a06170f1903090e10030204061e0302011d0a0e0406060f030b06010c0f140105010f0515070b09070302 73
    0x2c2800d840540b80d4103d5086504450750b50004102000c40c1100a440c02080703503002c91020320001d00c00c808100380d9204090306410502e0300490010314255041c0d8840540c0340d9541e802d00006580c00f100c8503025002640f03100000d0704000c40190343c0c0d21019610710710f1103617101c004940d25a0b00c0750049a113605042080300c68904262094900420103842550700e09500c854034040305950102d483d0140004110250039040700115050740c20300c0495408508100300e100700400c0e460031100c21540a0076107074500030400d50442c4188002c5413081d03003201051001e4030705a104500c80a1482005aa5080c0b0300401d510b4030305140b03d0788030012003141691018181c603001c221083c00084c03840c481c0e070240b042070200640e240c080e9010401e15000181240c1080300001e0b490b540103c850f07019107441846821884940b5440f141004820b014403103800313035107030001082060740c2c0d1080c4101038842182e00402c8102a0321a03214103224600c001800e01201d1303800903884000c2485680015600900402e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322267302 1250 322266052 322266071
    0x929070801053606031905030f090a0503030a030c12060339170c10091e2601060918031d04020301180e0106050603060d050a12050c0105160c0b0a020c01 67
    0x440740071013152480c1c041d21031001d032940d001c44180907042c90150050302547c64007030903800c50705142d4040c211490700b1083c0c000000400e40c07020001803051002541c0c00080c0445210001480019403550b0311040b40d06255060010401d030000101405001001c0c00d1007000b5050344881400d004070340142002c0d09140800a24420780020079902000d00b90250741810002204124544006100b402c00185540030144040700105210844007020140302074506a0b5450b414130b20b11440c803000000f41810130501c01d4612600b4040c110240003000001e001d000401c408642d0074102c0c441c0c01a041140c00101c0b0354214030b02002038011100050000d5580f0f6071202684140043c801e403411950360714280740e4145004040c4600d1040d02c4000f4070461035a100c0720100038020010010680c0c9a00600031180700042c0c3c201c0c0e910440100b19126a41c4030402d0800182c01c4400080c100b1500f01c000013603d00100b9030002c2c0d000400780c1e04c402400465100c601201d0002d02425004c00465807078843d911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322268552 1250 322267302 322267399
    0x110111010b0613050102060c04140105030406020403050a12031b050919030209040c03120806030c0609030c0d03091401090b07060507020a05060708010e01080c0f060f0706092907080105 81
    0x60a665007a002c0342c1848d20f41820298092103035200302d444064155016001541c411401903801ca8041c0c20050b052585948802d403e062030a4412160450f0403005070b20103a405010704d4a0005e0107200c0c0440740001490007038072510562840714401c40a04260b402c070f900324520110b020b0b54000c3c01000c1c0900d002d00e0101d0f41a84580010fa611600c807404030b041643c0711b03550b002d1007080040c001c3c1070f00c10002c1d01480380c685c12a0b901c0d15031501500741c803404241c45108014600600035900d00300100c2c40e20401d2100c444001d1390003410000171030410700900c8101400ca0f0b2045600130b60009065031607040803420880941002001c0340a00740520650941c04101103041c0c2c1d40040d01d525442e680c649110780e40b4121040c1c20790304940c801e0074090541c07031f202e80600b00000d01c0e01c268615289865840303000300c405001e0202c8600c41a070490f01841d012520700300da040c824040d01b0704103d00748864041c0007240c051242d1880ba2554a003040c403d08516a00da004014190844002980200920 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322269802 1250 322268552 322268587
    0x1b07050102030c0a03110a0c020906220507030c030603020906121c03090c2114120a09031a04020913020a03060207030e0108091903110304051c050105070804110111010b06 75
    0x103940000b4144941102c0e4861b12404852407074080d80c41d0034450380c03010717401d1044d90b580080c099a03200e41c100280b000004c01040c101500b4002800000a0615040c0300c00340c22074034400c00c1d01e003c0514040341400140c442c2c481c01c0d80c008004507120110340f4410440149886a030000240100341000ca03211105501500004145413052010130199a2122507031031003608d4000b101000800030801070350101c0e5031210346481007182c0c50300b560b04079940e19901c0d10040d44041c0c128400202019000c00511080080035480b44401c03280301c1074a814690001b074504038000d880180c1495850031060f085645808039680115840744e801d40d212181801c1c05418515101c03c0c01d4040395500c1d000409001000c6001841121a048560741101050702e0468007520203030907004880c401000302240039500c01d40303042111003546010114051541c03919078207440703010304000c0c10310070b003581444006810103401c90020b15003880c2812440700f890780140e0241820408042e0000400143c0c3d5200100401c02c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322271052 1250 322269802 322269817
    0x70608090c220f02070b040204090614010b04090f1b2a06090b0703141303030b06030c0a09080d021507020a063e090d0f0501020d0501050915091b07050102030c 70
    0x410480d0000c1868100300741c0c4103107000207106d40d1984e00000c005150551220510038002c140006000c041941041c480060a0f00088400d49001c1003c00c46044c590050070a0450012010700004000e01c0c01d030810005800d002c0381c00e008041041d0f10038040354030b41c1c810704800c04110003414081c1c10b00f8030000605100070140c0307103d40c2500c00545414040d00458046d0881258001c08540d20180703041800c0e29a268201d08264440d00019002e6030b6039000b5602920034a20391a6892400e004090408c4401d64041419034100240d500c0c0c4041d0089101c0c0440d103070301019110382ea0b8511307404904216040000030704481c078180e40c0081180c409100d0002d54405000c80001800003102003030349041e07182040c60f0391100104403495440c00c2c0074056107020b9200e080314080c09081031b0b0341c903801d81e0001090002100e503039000400142c80e058030390a8101e2006099511464644030102c0d0794000f00a00140b102c0c1414114005002d800c401100d4901d60048000c5449003021100d07210150710009 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322272302 1250 322271052 322271119
    0x904080d062319091a12011a0a0e01060507061d0f0105010506070b0c0703111e0105070527060409110301080c040b0306010e060d0b010e1611070608090c 67
    0x1400c41c42c108074801d0718844200c0c529400394145800e00343c1d00600401417201410503008407014406485107003a0744100307500c2c0c0c0004070b101842d5000101c880c0d0700c1401054410100351808000c2400000d6011b41503550900e8001d071ba4070f41c1c81c02c1142c0645a10b0302c09800303480b00700b00001100c10000c070b03c00700e00c444000001e02181c2d03a150b0030000c15001d030300c4020b4160485000440d801340c6200005110f51807090500559a0401d45d64540c113220a04044485118071b00d00c0300701d002c40c03003032180310380c8211581001070a1484203214090420109003004840d401910014041c45e47ca9805540060042c04414800201042e50081c0590820311510429102d42401d00c050751409008400500345c1c0500100b815a1805090710040e040241500f80c100078484c800c44042140131254034041c1044000350070341414038540e42d00540c801e00401000700400702c4202c0142d03210104104049414038a804446911182802030518500000540d0721885403108a160348031148a0303c01903c920300e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322273552 1250 322272302 322272359
    0xf0a080a120206090706030f0e07060504030506060303030c09010c03090810021201050405150904030c02090103080703170f070e0f030a03170c0a0519030e07260f0c0904080d06 77
    0x7507000c0e070b070b254015503544003a6000018240401403080d40081c100e102c2401c4080b48441c0c0001503281402600d07000500060000603090040c0a4100840303038020400341c0003145107207000381440c1c405000715200745041054403040c000c00d15200c0c0740d000700030708542070a646525941d080007800a60000d084800030014035000010703a85010b1144500c41c54403043c010703007203070480c3c810869a144001c0c401c8040c000260802000b5032500007206020358882c000550381e0301c00c0741c00d026240000185000d6503401d04003040000c008540d50207141c100d0f080f801c01c0d900d00351b10305e000207012060180c41c1079007600c81c81308050b0525070301850820881c604d6201d0001c140c1c41d80d90b14580c80f441410070050205d0800c0003c0a5203503141802d0031101062490001a200340c40c526490070110b07664481c00c3d285410342d4650403400c0992406c4060103802d00000c201200c40300c10740702d03151122916081e202d40710940c0060188400302003220511276025004114440d160140010340e8510310640443c0100003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322274802 1250 322273552 322273583
    0x20c16080c03190c030210051209071d0403090e130212060a0e0f07060e01211b05180d020f0a060207150f1b1704080a020906040203041208060f0a080a 66
    0x402d40c6a0041c1e00301c0f841c044c03481d00b95000c0c010b40c0e8200307081310b008200040000c1c5107940e041000083c003c03c003034000350a6543c5094603006031040e80b141c0c000001600311342840006500540c0c1c0c4d00c100c50407202809125a42c000327003100520400400603411a070441a9829000c201145413440346001407001c100401103d0310107945c801d0b1084030740c0703801c1d40556000d102d214014454038040315414034210407220006c2069400440d5020300030110b4607148d0048001290000a02c07a881c850b0a1900f2814242005107069084018241751809070714415100c0c0e0030b6480b0082007040c0c6c50320107800b0368070060750307100d000f942d9020911503110001407a0541003900346c4520411030036114a41d480342403188000d02d40071100d00d6445004c44c0d035a0084c51404c1d02814030100900024032801c000f0386042c0c800c0d40140300e200e0070001d06081c17180f4810000c00c0005405440b180880011038940b400d6181e6504001c5500c54140c0d4a4003a030107140d01310006202000042c54421561040c1c4080d1259241c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322276052 1250 322274802 322274833
    0x10c0f03091503021c110a0c2102061501050c0c0906031002120108150601080f07020a29130302060112080409050c030402040f1b050c150f0414030702090a020c16080c03 74
    0x48500c60600f1b140000c000401000b4403a4880122513030084001040712940b81c541d203c103410b1071300c10b428050380060080180750380362503544160160007824228a0f0581071046e02d510b038214090490702c1801c10101040c50354404020ba170f118000070075411555920340d81c48412442300d00b481a13158070700c94042c42003e0001170fa01d10a00480f010785440f8480e840f42c10480e00110300084c82d9004622402e810a030104100320450341c034a441a07441942c5140c07100e012161200c2d8003d0140505c2e14404c540d810000340c3c0000c580d0704450310780415542402c0185040245031045522030101d140c100028019100c01c1030340114001c0b40308a03000c11070451902c482c030302a038912035032481c015480124207407000d501400013030108407600d105546c00c07031015040102c043d01080e50100410300c0984208410400340040410407401c03802c0065003018a15400240310a600528014a168011550550740d5500700190000c2a4060b9500c080c0341e038648840b15900d01c0c02251440c482d20911629109144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322277302 1250 322276052 322276061
    0x6010602010b0906090703020d05100f05030c030a121211030106030b01080f0114010309022d030a050c040c030b030f0c0f06090303040b0c0705091008060114010c0f03091503021c 78
    0x2410740f0026590b000c00b0400d036090010895414160204568504e001c01c2e441214421010103400c590450f0509510310f14690315a00490300941c0320124881c05d6a0b0000f1b410b2003040c1c1d02c107140029030100d03d01d044a401045003100444c081c2171441c0c0d842000c3c060070140d8160340c03c1d039904010403400c2100443c0c0039201601c1e20320100205034010302100c140e100c41c1340c0c0c403545d0604010650340410f40c00f0030000b550000c14584101c03000300b07499490200062200d0441d16048008000e215401c0d11368685078011000e10911132070f91b44440300140c6000c0c2d0080c080880c2d00505076030780c0010440166071201c9149031002d02c2007103812072807e41c4d450a5810380e241840080d00071400e09040481481480e480358220310f819205124000841d0790750044024440c01c02c1116610b40c0d145400c50301442c084047e000f500c0032560351246405943da2210345407160f1f03900118880d4000b6401c2c02c081e01c00340b050b90094484100050410703c51030350035400400b400480a03400c4002050100c0d100021103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322278552 1250 322277302 322277321
    0x40b070c12030b03120f28021b0a0f03080903010501050a1a0d0b03011d100903211e0b01020c060f16060e0a030c1a040206090607030207080a0c080601060201 69
    0x20155110014070991090f480b420034404040c0c00c030b0362020601411440260031040c4401c07102d800019014250342600c114000c2000d10480400d0000501d1601c065101c0210844140000006554455180d5507103c101d50040c40103007040400c1ca51203080002140d400a100c20f40a5030901000045c14103241c0781d054110741f00c00380300642b270031540c9140d0905680075070f41103404a40c6480468000e40d40a07c100081416480c801c0070842040101807400e0141d28218030000c149003460880c046500000601da91190030f285942e00da0740968048401400c05007401d1a060035111003042d90341041c1d0380080300d031034004d800300c6178404036260821805104644000707284920501503030040e641c400426107500b5218a601064006440e1002850314034800310680000710201e200702c0500080c2c071001c00709150112180c172290b1504c2c1d004100d00d8031501d2142e41c0074240008004044c140309000c0100a4111001942d1515a442c00d12380d81c0c50303240f4020b660960095000014001c0d00500c281d440300d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322279802 1250 322278552 322278563
    0x2061b030c0f27011805031002092106060f242b0b041109010801150e190504060f0806011406040905180f0312060d0c0b040905040b070c 60
    0x103680d0340c9600030240e0380000420101e032000500040d0280c01d550800e86408102141d60702e941c400c40f00000500d01c281e128507410020410050500c82510007091030340c4840b40d4802d0140c1d035202c0101c041050340510b42060320700d040198081114460000c41c015000e100103c6900d064008075104010442641c030404d008030394610803000101c3c4070040c0103000500307103c0c8818282e05001e804030703903400044407524001c2f55035940240d849031f19051140103c1a1852031041d400c0941c07410010781566418090500812524a80410703441c0c401d64203403140c968068000225032100b185009804103260141ca44928248080400d0800a2812200c11550308000a1130783e81d10300707042200d29000341809940c002c3d07820080421a04e1190003101e000b000401084480540c04486840c2031450846c8030100c0ba030410003602045c151041c00c0c0c150005c10031100241c2d4050b5a2400201e40281a03200307210800000c5030001d484000c560100748514001c210040300355035120f004503a907141e0520300400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 322281052 1250 322279802 322279807
    0x70807080d05090d08070f08041e14090c040815040611031018150602100c08060105040302040b040e060c0a091410032415020708011517010b060304030f02061b 70
    0x141881c0c10710b09510228045c800003440d1002c140c48204103001072240c1034030500000102044103910350481c4c0c01120155981e003e08a60400c90b040e0050b4030350b404600d224070b0030351b00800c442c3c21144080b80c00900c400c2c2c0880c1c075142c0c0160b41140c1041422030b016150701d45004007c00402808404176445061203580c01080581410f204041c402141602640e0342c59550310031a1a48800440c01c0024201c0307034009041f000070306030707109081c1c0b00d1071080002040035003000e0000d581d801105032030a507541190045101031492010030024041130303103c90b2591055200b40811700110350014a1546440e90340c4290450315148605100904007080c5600310301010300302007a40c0d1090b0700522280d100303408040c40c0c140601c135203c04d40403141e4000c60311240465908074245a0100040d8004000ca4002444402e004400410b1490b8092113811800750f41c182a0b5a000c0200394031168032954020201901c1c1e04240c24005c00300100d040c0c0b40d0000d440b50f40c011641030001c040a00d448543c000b4030203031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 322282302 1250 322281052 322281067
    0x91802060405060708070c0306050405210406030b01140f0a120c020c04090827041d06040f020d0c0b0301180e0a021905120f07060507080d050601120e070807080d05 72
    0x83d0b0303503000040948002005202410002d030301003003800021401210085170b9400e090038001c0c18420380541e0450701200d0a9401c0b1840c603409000c0d102124602d040000e041054075005840e00f01443c41c800510400000d0311405252146003c0e012144569480756041400407003940f0842d0510004440903921502769072441345010f40201d05558400c8115605001e091900c0c030400b2040441c1c1721413940d07d00803018025040038410010040e810700b1100b1045a00c040d042c07505c6000c0500090401070141e299601907403150b0400c0b8440e40e0340030620013000750707840c1180180b5401c00e010b40080e40c550300180d002520b1560040c00b001d41c000c1d80c013034071482550f5800c1040303811850900069001c400b03a40002e040d59250300e1a007802c0c001c88050b00a120145014a0508400d50402821b03c0024000d03c2c01154843c0e00751002c2c5042d804001070182c48400058840c009441c19001c3c4950404007144880e800104910003210706220848440d5515884181e072101039001c00400010390034004503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 322283552 1250 322282302 322282309
    0x7231f050a0612150c0f090302091003080315030d050f0a080421020105040c0e07020616020c04020406030e0105010911070b060609040c0c030f0219060506012106091802060405 77
    0x49401c40d0030380000103040c60351480c580d2804802154107a03140540d603020644005480c0c020160340000034034156035a1024008003801508650001a0254002100046418202c8024540a0354226111503201d1800c1c160030145d0360000d008603402402030424150400e030040041c0c6104010042c0f1040c01d18021060858412030020400d94540741c0d445040e1818019000051607890f081d42e00105461819042501001410b907004104544c501e800304140c0d03a9011a010350000340c1d015006402c105511402c0f89801210501c0035031240c40060000b41e40e6170035502a1000c00310050003844586c1c4d0342c050102c1180c03203c92151080a5080000100298ac4400700070751000b0001c0100c1d0400c4e03200341c0030500312030035046d8800104840c90011414141c000502c032441c48458401400d1580d2034050f0860801c1800c2c40003484940c031900440d40d26030240e55103441d104040c0160403030803c80f074030f1007401034000c40c0300d0303102080c1ca49010142c40c4454403c400241e0303500544020f185c0313840c0c83d052 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 322284802 1250 322283552 322283561
    0x91e0a080f03100b03070c022d122805060a0e06060d020105040f0b0301170303070e0409110939040e06010207031502040603061202030c1207030807231f 67
    0x20030f6514510160040785001c4000041d500400e9140e0300c1d40c200f1042841031080a103041704290500044c5d41105068120305001d8101074032a003a107400002c1240b01c00702070320700b0301d2000340c01030081c2c1683c0d6040e02c1c2642c984c5039050818082d600300c40d4907442d00311043c0203d690014081d120ba401000024500342003900e0340c8440c00784189800c0d494a5901d08808003a0031164110800c2c85100000420203840c1d041401c0c0b10480b102000b46156080c80785018050b030b9000c41c11035019580300c100d46828080c03040102c0c00803090141018480e403601da10001e18461040b1000500040f001c5240c980e03021407000d41650015070049001c0c54541400002000c030000104420304510940d000070001135015001c02724000c000305000b503129030038401c0244c255001a0400c201428007040c40c400980d0b00050b143c5921141039445500160303054080700d0400421b90000707001044006182420401d81c0070000e240d005000300301d0b01c500324010032003c1c0c07510303031940e40c01c81c0b0200303441305240c1c0c0f00e070880c1e02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 322286052 1250 322284802 322284811
    0x5040b040b09150108030301290703120f0f0b1f020a2a14010e0405040b04020904081e04151103070b190f020309010510150507061103091e0a080f03 65
    0x700d5102011803850070f44400c00980001e2116040031004001002c60001d50b501d03003101361a58000ba14010b181541903500584802034104a001d030a805500800c0742e00c4176844000143c028840a0380900303828024040302c1c0a0b080c01178004400c02040034034030301054200d4003900d50140c200c3c0302c099150410b407a4511a070400403d9007040c0f5003108100b850050740001d100980e940b920001c00d02002404510b41d0011842c010360407c0108000107058100241d405981201c21040b030343c54506200009001e035031910365600c221811010b8501e05800040c004554a400203890090b10f012802ca030b010f400c1c1008545950300c20f0280000203000413a516a1000b103d082060100d80b200720003100340c071404401c011046d54004288000f6050030701074164070030103486209544519003040588104600c40000782007000100b0901c1c10041250841d1a401b5815400030ba01ca05100c00c419445800c50080710402ca000110f03d09010304001c51401c902e070f500220440c0c1000510005450303c0d500040c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 322287302 1250 322286052 322286071
    0x20309010e0105010f030b010608060904030c0f05100e0c04020a0804030c060e031c0b040b0105090f0f12010c08011d2413020d06050315070309140a0302100b0405040b040b 75
    0x200307554540807003481014004c181d0707141c61010326031071418214079025040c0c00840400040300c04224407600c1d00d005a680082d410700d000f280003061801c0c030301020207031101c00a203030317010351501e1141540d003607003041d25511781650585026028150400080f44201c0704080c0c007040d011000035000c24003854950041d6809a640420480030031001e0f80e04582c04a024162189070032003002401d555507100d4004c0e2880151010010005100c0003c0d0040c000c80c0c5160744102130f8024048040d407100390105224490140c50328403070148a80304603020b0a8401e02c83c80000c1c0840c000002c060854000c01290280c03260140300c03068859102c0022403c0f804440c80755800048503d42d461a1600910380204c00b01036040140c480c503159912009071452940031301e03c00d0748984810300b0f0299040b01410381001040c203000804001d5454031580c1d400d061500745080d806030480c0c01d410700d600401e41c10700b4100c95040422109100100b00b008843d01550054090005000050005441c14140300d402c5089078 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 322288552 1250 322287302 322287311
    0x1c02070515060d0b04030f0e0301050402030a06050a0617071a030c0306040f021908010501020f0d120c020a21080612100e010e190b07051c0906020904090503120c03100902030901 78
    0x54540f003101303031810b60301200000c07103101503401642e600c0454450903183c01c82c0240001e0030244c0020383d8450340140080d0002d039440011400903221640b010008202c0d00e40c0c0c0c11003458000c1e15103034a945032032042c09071100500030b07505603200102c07080742e114044c1401d50505688076501404010b10701080350b80c0c0410703420020901d40f040200014612102d00e650b4881762503040070002824441824595001c1d58460303140218400c1e00010208040c440001000031360505c0000102d00e441540035014144a5400c450340d50b445407070707109442c030822130b03502d03070030469107404050215580ca60410400550404240303085912406c1e042505142d4480d400801d56108000c1d005041400055600004000c400e11034000c0140e680d0b0201e034021110b04240b030070141e13600807400c0c10904581801e014241e0b9004203504100d40780c1d05481000c000508108208120307450071542ea42d01032100d13003901005020000380d22622580850340320300c6c404c0840030340591030580040060340010b80b50b02c04c00d5495 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 322289802 1250 322288552 322288579
    0x181503020616060f0513022806020703030e010207030f08130e1602060c181507081809180d030207111201050f070504081216171c0207051506 62
    0x440c009410501c12002ca1803060b40840e10300081292800140040c4603410402045240358080041c68419a015640d072403641c440c1502140d203052141451007000c295452003c603090707600042c0d0318240e900c20340f550403405041000580ea00d5080344001070080500e46500380019100002070321029440442a001c2d403600ca003100c005540d0200e030b5504401104600340c2d0354003681001210340002c0c481d42d00d07916003044840304103c40301107a128580078000e101031640318115403c08440903182c1014405813a14a1408602c0f070480b1042880c40c03050f43c956021507050b19036844243c482d0031001d0010312201d0070140007a0043c0d0442d50068a02c0c6590b80d07000c0b0287d44410b2100170001c40710b40d00000d0316141055904803003800252000d001c0010902051002c58000105140c4150030808000e85641c000c5e81051149800300d003004009660000d010b01d0341c280300d60b01410161a00d103401500c8000681e0600040780a0380c0c2025200e0361203c15080d829641103103009410070800703408000c0100ca07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 322291052 1250 322289802 322289809
    0x5190212031311090414120f0301140117090705090601020c0102100c03020705030403060606030c1e03181e0302060a020a050d090201110601060503041e030c030806040e120c150118150302 82
    0x70484055481000090340020b010005010b0b504030130310a1000300d410001c14600d100302d180014052010a41c80f10f0200044336802404a0000100d03440b44200c054642402d045844408920881d806400d01201091f52980045950742c7d849406034001c0c8040004d41e08110702614080d0198000e151782001514003144052004201541c0942c0b404079550740f078004010200c4104150f00c500300021811301e00b505042c0241d0304406d40b040c41c900440c40e241c00c007455682c0310b060800b0040000b0526507518080340610108d035100d290094007a1074a966403034480c0b0381a03200719010200010b20801a03004070036540d82c081e051150043c5041c1004284a0807907501c1e0010a800900c0811000700070402001a001c103d0000c3d42d100b40c07010070030300e0160f40d00913080e041081d40050501240718005030483c3c0300e0ba0b100300e400e61205000c03118219800540f45003181d00000700c1400500414401c0300740c0940c50b146080c101c9100c070342c00c0031030300c01030b015801c00410745002c14100c5004805800009a036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 322292302 1250 322291052 322291069
    0xa0b1008030c0609060108161509050d1101020f03030601050702041e091b0f0b0f071b1511010606210e10050a0b030606101809060605190212031311 65
    0x180004000c04d061041403249010f4051f403007002e690340304900b812251090350000c0c1088840007440f020b003510320304c40240d031001c215412580d00b02c11110340c0b580a010341c00401d410b5011081c0c0030b943c404042510003607240d00c8101c80035404624100904c10060400ea44964200c0c1149080000c4441c0d00e2040d80040c1d44100d4000c1e00c2180c0c1780b1050400b003207042001c8900800365003c0c84028146024581800c0340200d0308100c0100001040c1081400340206146844001c541003124085448200f0242a801c0c8200410000b4180d01d41d48610305405100f841d003a9516a120000541500703d51050203c003281d444007170f515218108904140010131040907841204180402e281c03408194800495884410766840796000100380701035916541ca0940090105150480c11021201c0c900d80748640c4550103450000d28280c070000d00f10343d2260140404078000700107001c0f0f4180901080780d4034210405484a96142003010507504140140702040c0307248a80d8820003a45190b000003400c14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 322293552 1250 322292302 322292317
    0x62202060714010506090906010510030e160b0c010f02070c0512031207031a1008070503060d0c0f052706010f1101140103210c1412030112110d02030a0b100803 70
    0x90f03446200780042482c003040e1503a1f0000c0351000402c0c0c00e6245c400080c620005031140d810074103586000c4803006003018000f6034000c03034043c000020010307036074114280035900940c4000340c0f41d440d0400040b0042001e0003284d40740c5030070000096100303050204001050134259880322940c4020012104514006070032648600c1c603648000950050001050403070f8254500d9036882030a140200007101508400002e0b000821032814607101e41c0c9000124680f0300f4600c0c1c0c09003420008550003d86543c0480540041e103a087c1c1e40c0301480b03c0e051580d81e0400c520101080031162100780000e82ca944620785c9480203030740e58941201030404070000c0e5800c46400c0c82900708030100c5000103105000c0614444151008104060742201c2d9504200425098110400801d1000b00500400c001d0604000c64044200548026030f5039583d01c032259108000024412508003000050400f8246004184080302680140c003038604940d0301d0f03480d0f543c032070002402599031400300c260100e8070001c10409000305 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 322294802 1250 322293552 322293593
    0x3041701050702060604020304020904030c0305040b070b160912080310090509011a0a1d090127060c0c0201120e010f0f1e09020303120a0204050603070306170622020607 74
    0x42e040c03018000341040e00c001c03e4075000e07600410a000050303d890302c0440c0d2040d01450b000c130a6190600d0300b11064400c0d50f0018000c860085010070503c403801d50321358046d40000b1841c0b2040c4034000702c240d480307500b00d219000010541d04841da020904a40095a1186045001c0007115840c0c510380c01c21910242c448410b960754a0000d22907081000c50007130b844140480b2504407044c90a82d41c2c40020071100c3d410b0a03403903a104e0100c0d1031240250400011150b24125498040300c044d43d2032010080041d00640c1e51a04010030240203c1c002c4110071441034040c1d42d1128020305d0b4038450310107001e5094a8000665884080031400d03941c1d032044c1c0c4a6002002c0f0301058800c05a81d03c0c0307040500109584142900d00034180006940000803a040300802d00400e4410750364403d03e100003806103500003904500c00004010926506a100d081550140c00050ba03410707600440c21a80c2d2501150308001c0c03c590f00040928002e4440c22444500380b00904407490200d03542d803005203480b40f4a131ba1640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 322296052 1250 322294802 322294811
    0x40b180d03030b1905090c0a0201090203100506031e0606090612060916050603010518071803050d0f0e030d110f0102070b0a0b012313030b09060708010f03030905100203041701 77
    0x70324283d0a0b40c42030b140704604c0005118280000204605000b51401010041c0001c0c1101402d0003034100303050305500201500d154800c1c4003040006003d0845210b446801480c6141500c0c000c0401c00c0003072000d0314401081956540c0080c089401c03406420564001550b500d40880804208480703031095084902a2280b92032180c540c0c00328103440e4001c40c0c4034060a10040c00180c0350641d10701185400c0c4480140c80340c4440d0020745d940035000c44c41005002c0380108c04400d0010001d141e405155090b510405086c000e080c04076100b0500503066a4150054035032214560b01c118100700581d84190103995001403034401241c2264040803003251800e04000070052034030100d20501c0384150081c2820640011065000002061315a40c0840c01100110f4403a00028801e50414082c0d540b00c41c0c88000b42c24803004043d9076000440d00c01c00090000c4c000484d01207203200084007182d9154803128501801c00b01007101c50000700c030366842103110900c00007418900fa1907220341c09210748400001d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 322297302 1250 322296052 322296071
    0x100915030b090c040503060402060f0702030d0903150c0c0201271710020a0207060c0f06090302100b04060605120c0d0603030909050a020a080f07200304060215010b040b180d0303 78
    0x2010b6100244400b0b5002d200780303c2040039031000f050059020f80d0481da690354400c00c241002e5454007804001941504c1040311a50340d181c1c0080d10030303065070301502d803000340c80320541d03d414151a840018407001804043c0c040c1d0040d400742101040c950b45c803c10941d0340c0c2c0b00001c0c600000400c20ba0241e40c01c90703154610001c1014091000903000b801254040d8988146140080d65038042c40c884c0320b08015900c0700100600c0030614403108903aa000c00188031112260900a64640081c506104403d16120316941146428442c110480e101603e0342801e225005150b1440b5140c010401e040034403080080b0140f075020b611898001e1882a110000100c2c1009070031821034400030b103503020030303481044041403507034226044580c030141d108080b54080d601e070101160300080100c00020512a150112200030502001a009481c210307070031101343d910410441e070040e01084c4609140a00100400d02c03007200c010300101280e10100c1c8184048094031008a03031500b0b62003105400091ba14100d15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 322298552 1250 322297302 322297309
    0x21605030c0a0b10030323070206030109050411040614010c020a050907020303042609100e040504081b06010b0f091207090f050604020712081f030f020103050601110705100915030b 79
    0x1039007100380360310303148103417421a42d0107015104040d03d249255100e81070503080b0f5000d5241101e04451f4041e0411307881e56035902e4180c0c0940010b450840f00703c680c9015500c85c50a180c40707540304841150001d4040100004010f4400d034403035101c1070b60001d6900201141d1511801d040c40d0165005030b000390b980746014100803200311481c2c02d40c40328042c8815000c40c1500c4410045d500144e8bc100c0d035001c542c04c2148030541c0d00180d0800040e0300310f42080100800d00c2402005005d1001c490440c070140121011075603601c5d0704c000d0041100400042c0000c00d8180b181e40c0213420965405003800300a0451000c0c000c1c1f030710700f4a5002018082d110820355469540718014075802500c1540c0550a005c0035694500700b4400d039500c1e580c10050b18800083c00d082c001020004501c85142980c028a03899051110700c02c01035080030386c00b00f400c15000c1140c81d44141100c0a500e482813000c0d1200509180401c5841036a90303164070204180084042802c40070110003400c0c440582d100021100c1a41c82031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 322299802 1250 322298552 322298573
    0xb060a0e0c032706060906130e0a0203010b040b031207050a020d080307020709091e0c0b0d020904060e0712020304020105040e090f010b1021020d0603080319020913021605030c0a 78
    0x104940b458264091210f1030400142e0302d03401c01800c8030b045070150340d0381d00403038028141107041040c1e4500300740e254240340c0f1002c00c0b00d205090081d4002d100c101102d50a0105440d85207040c01e81550106846608402480300501180c5100f80140e6103440c281d900043c0392500d20020648505d4800010f100300c003601004844d00404070000248452090b507200e8014640c10301800f07802d26990804000c042004500101c1e02400c0074128071521503010f440444000e4000340c0d4000c1c0140c0ca803600103d185a8289001c610a4240303550300e1030814581c07200140650409007080341070200a00000c60507465810110b481100458001d10254030070000c81c1d400d445001030000e01401c4003000c00180c12b5400b203034049039141c2d5590150b211582c101880c1000703210f04001620307071524100d0048100241040118094901c01c80038100108503420410120707c64801c0756079002969841d140d2101490b034002d40010307000420000d4a5044a84480c2e0455101203075400c80ca0700000810750400c03101d0584c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 322301052 1250 322299802 322299841
    0xf060c1c11011e020a020c0a12060509150621031206040513080f0a27060809060114100225090e030906090f030304360c020a0b060a0e0c03 61
    0xd0112083c0c0b40070703544003455070340001000d403070b0000703141c0e52014003c00c14403240c50000341401c800305644040082d0341c1d00003800c00312202411724010503207000001a0401b0b0350302e40c83c3c809450365221007082003244500d02085010142c00d810154001007010700203041005280c4e103107003119141440400003140c40c0100980c805022205c80c140200c1d0130481940c50b07900b40b102405a90707107030b08002940c0199030700003010180059040e00d42040004030343c00400702c0da61a02e60741c0e0b050315490810350b2501c030240680700e00010400640704103807800d83d08031300f07041c2c007103005a40300420b40f15940840500444061141c1e110b44c4a005c00100c000e82c800c0d40c503004405000345003030a4904000500c5481103c01d0b4074400da4600d034401c2d9940da0140304a400a0945004068100958440000c1070b07800090f905240c0c400760a400e0141050300e0f00443d24000c1156004d8803840225507104c0c0701d140c0010b0f01d0641c02031608000411812408002980035100c00150603440345030140920b2810f0003810b6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 322302158 1106 322301052 322301087
    0x9030a050d03060f1206020a0509090a09140318150f07030c030216050d121e09050f01090506030f040609020612040b06030610050f060c1c 61
    0x400001c1c07480151014042150398860300f91041450788505807030101100506000076240d0b500600c3d180ca06414014185940c0e103002c1008004211006420b882c1e444d00a101400b10842000c420b2110410040d45005047e68100321944042240c42d80a076800381b03a940283c501c002c00b5202007240c840d100d01e4071206d00d42801440c0080c0c51b6403d13005400b80450700001400441030780d4042c0c440c00b8140c000e002901d950760b0000365a2604103282004036200b200132604400e9001c807502619180d907000b9000b4100f008201c103151900b07040a0520100e10b204001580f00c03442030742e0340010001b80c1c48656940310304080000d000402c1c5c0003544071200103000308031040812950f50040340502c81c201e0b000d64440040c1030b5915001d1382c109220000a0100b0046490b10a501d0140640c01034519801d10b61000462441c0031051740a410f8126081c0d40340100305603000d01c805a1079007461 = true := by decide +kernel

theorem cover : BRFrame.Cov 322122302 322302158 := by
  have h0 := BRFrame.cov_init 322122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 322122302 ≤ n) (h2 : n < 322302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
