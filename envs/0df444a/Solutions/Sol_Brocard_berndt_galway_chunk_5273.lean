-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5273
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:19:16.820052+00:00
-- url     : https://prove2.me/submissions/3a4b1489-e4b2-4c76-99a0-6876e66d2fa7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 948201438 ≤ n < 948381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 948202688 1250 948201438 948201493
    0x40c030b0f0616080c0102070f2a061e0e1c020f0307030525150c05010b092a07060e0708120703080f0402030c04050c04060f050c03090105071a0702 65
    0x2d03140c440030b004034200c1e5109500d0300805558001554540c0e0b60400d4050310520341d0031030451040c120722450142080720040210b10310800c001e01c641103101001c051594101c46994907044414130400104008442400320448103001100248040c140c4865811440083c0c40d40700b0111100004d00410081c0e07895904000d120307511040c010b2002400c0411030617900000f10503281886104020b480600d229a42c00200e00c90f0000781004800661104c14040c4e4180a20000c1280f03101d6003050004568007150a41005d0072010010b102c80c100080700d2641c00258103180c103052050315544c10054a21000041c82c25601000c001d000c0420144186140c1019020701617240c00309a40e0060500c0000078500010251000300040c1551014084407580070380c0184104100e01d0b03c450001c01c0c9401030300900380020020220640d205004400300e0316860024002075060000001c01116a42d012803401c03544108400540000b40310361030791240c09089160060940510300d01d01e00c0150a03542c90b5031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 948203938 1250 948202688 948202699
    0x901061d1003060e1f09020103140412050a0908030408010c110307031205070903050d02010c020f1203010306020c0a080a0801030201020c0f100f1107030c051206010e0a1a040c030b0f 80
    0x50000c4001c0152001c0116a03102c0c0780451503184001e21141484444d211400c20303240301603240c4120074003540c0005901071007600d040040d40512520040a0001202e00802d4800d0b200c80c2e40b5080b90240300580814030b00c80c0340a0251b9612846064155001984004001e81d11421400710190f04400c4d0007107000070300002541000d50a450041240d200d0204030790b516540c41c40420035041c860720b070050103942c010302180c1c1280c1052000a0090401000c0c0c18010b0151800245101c00003040300c60401840c824403908517402d5440b000020741c000d42c400f040c20310038020b04c080041c100c3e80282080c54200d40345c1c0541c81d07145000190500e090345081c00d100e5600c5544c9860907030345a091644108800380f40c4410b0311486480242c60b1983d401013901031501ca60900042080345c10791810701510303021b43d1310b00e08002c40b400c2d680b0380d1390000b80240c003107a00d10040003c245103203a074401d0b0142c0c05106040041043d40e007000c201100c40c100d02c00380010303485401203070301410a070701190111a000d540 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 948205188 1250 948203938 948203941
    0x15010e060102060a020705010b09250e2b0f0c03110f180a15090608010b09060901060f0c12120b0d08091504050604090608060f090c0120060901061d 65
    0xf91501c0c8001d015206485c0c2c00b050010500800354401721f01301c035010b012007140d810308c14110019050800b071f902c401d00c0410394840351581d2203903c4560480d0700103010032001c060380c003040f4000000313150613800c1c000403403455000119504a031a404e01c2400780c2503c0e06080e00b1414192880215000303a1801540340505902a54446491600d0080b06400030405151100c0250700054030380c24407200080c4804000c0800d61800c25030240d01220b12080081241c13803170080900c2a030003811503419601c0b8842d0b80040100e03a000b215034a410350710318075102c3c108050541e034490342c00c60f003000440c001507000c05d000740e014201881603020615048440303426100059640880521400030400c0c000c00d2009402c040401e0440250740141200410441d1990744600c21080101194821010a480740c9400b02c0c008008220115010303004500140c101503c004005480410302d10039100b448840b91600c8140400c0180701490180f0305000000c110a841e014094240c104501c0c0180601c031070000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 948206438 1250 948205188 948205201
    0x30412020d17180106030305040503160506070f08040e04030f144e041b231c060501061202121305150c030a1503020108240d0515010e 59
    0x1141d500e6168940144802c050f6180000100107203038580c14003903958244200801016080005803050398401d0b0300301da940ea42c00982c24800c0240074030800d6000f1200700302c0e500109540d0307012a00302c140105034451429996000107400c1c3d000c2210240d0016040201403040968882c0c104295a420260460b01b07080071890704030000403010004040c9500000303030b91920130540c501100c1c103041c03c004800c5802e0b0140c1d0204034070f050707040300c0403a9030520b00345141900c15004e0101e041910484c03072030741c20b450b807190400e00154a620f02c1450fa00000c14040d20040c45611243c081c0ea003485004003144551402c08041c100c42e40b2210016541401403002816808c0c40e0596541d200056000b9800300d00340c907040103420f0403842100000404c4444040002c40c108010045011b21550401040300000148200301c89540c980402400204c101c6c002c1042e81600100c035a0041240c850b4510281c081c02c000501111600c0340209c03a981c020045050000783c540c04040d00600980b07001402916201c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 948207688 1250 948206438 948206447
    0xb0a0e011505010e100e28050d031b030e1c0606090209310903080f06040207320601171608070509040807080a05190908070501031817030412020d 64
    0xa40700d50b02504d245040c5c00307070503441100700d5185860064401054054450b0601300c07540040030214135210b850020000326410002c24640030103406a860705409800c0350701d2074501c0c1004d49800d42c201b01100238400f0b0a640c400c0e103c0705c820281c0d4920800b48050314a8040c003a11000c3e8450b0f85c03081e10500034100b06454840c09000c1070001541591f200200e12600101c8040351a000108481d1500550b2000c0640000401380505030305008281c084d80c40d401004207070711811000524104ae541c03041200c8181d940651034081050005082440703220303001c0c3d9031030400d09a1040ca14602c0d40043c1030304081c3c0c1400801d0307044000703403c00c4901c2410040e1403aa506e01034851140a850342c400080d05100c0307008113880da59540082103d94036886000e005215403c5000c4007040c2030700c541140f110b524014441c1604491030038000d030948030704e0240190000c0c034a81c48182c0f82c800d40c00f02c4450001e0344c24000c1c1401000305989585e140d0800341012819048500c0c00d81c0306560052110707402c8140c22 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 948208938 1250 948207688 948207707
    0x10050f042102030c3312130212030a05040b0c0a021201061802030103081603020a050105090c0108250503100506040308070b1e01030f020406031407051003151505070b0a0e01150501 79
    0x4510b20003e0040d80400560610a403c10b00c00905208024402004142c203001c11f40607008580c0c1001a01406844a0704d0f8031500040c900404c8041008000341a80e100c00b070010748001c82c1c2500d010301950740109500003425184c5001995441e50144040212507148800348500340004604641c103564494aa03071141e03c980f214941c6451002000b0140b0800c51488078039488402445541801030042e070351850b094841c107012805020000b41a001c50014101200b90845040782049640f14020f540036030002e0703c1d48048a080c514081940c0d200d8600410045124030001303980d40485080c012080c60f0054840120229100d68103403042100c4400380d81965044010201100c00a01c009001403496074401001d0f003c0c0000010042503000c508401210400d4803612032011030607a00f101110b1003444200c240321400d4101744000c10107404103070040c08040c2006072400314152544801c412080b03810280103501d43d803000954103028042d0b21030040c0e407074000492050070031001038900d509 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 948210188 1250 948208938 948208999
    0x501091509150b0c06010527070c081e0306090a0b10080c1201080303180c03120904230403030e0303070c02040504060902060406020307020a1410050f042102030c 71
    0x40b00d1581c070890404a80c1884002c14a00c40201d5941c10340400c1540c83d42d000b4425103101e00642c0800001001c019140720000d03c404604c2070480d91f446140941d40360080f01703c2070b0703410350081c08203403800d4400d50086800001c400c403100c0d0326454584104880744030000c1161466508201c2c0300c08050f16200206404031000c1d00b0030003c01d0762401e0002895010b60f071510079440c50054000910702c5000303c01980a5800c0d80141e613210310780700c003610340c1c1d801440d0a03079a09036000d203800310788a8000c08080c0c032241c0401000030440b4010500b00c00790781880c110b80c2031180303910603090201701609446803070880c1800c07101440c154905200050f0041904050203030103561120005010001c0c150720031202c3c95401041981c442e9281c0800075920380000380100d02030b42d003089001c0764000c078a0701080c140000040c01c43c02034013a900d000700c465800546aa4610000600c0f0215481e10040301c0d240010085103441554040103004151074000424444c0380140201c0346000c040d25002401d06982c5079 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 948211438 1250 948210188 948210191
    0x201090606080c100f03150b0403050d0e0a0506251a011d010e18070b0406170105060d0b0607061103070306170607050906090d080c010e0d05030a0515060a0f030501091509 75
    0x5e0498402c2d00905940600740c100b1034114440415102d030441e0261090388e0040c0100c5007003201045055802c8c8000d52011a0f103c2d400810811051504200034a074010310540800380640d42480d186102d17885c2d002d002c903103800901c404d03121001e01e568090b900402e840c451100da20286000300d1080c0700b070103010b0f407580e500c0604002400880000542d176603605210b0b040320300160366200c1d21030003034020b07018100c00a0000c0301440030362246000424103a5500410703061614415400d002e0040940c01c0c600c540192040c40ba25002c43c02912440c801d45c8103103130b1016078a24250b100141220519001013800054042800c08404400520503a00c104507003825541c0315260b100007145401003401280e40440000c2c003500c02c03c82072001401200420000030b00089007060140c5460307101098210b000101c0c117000103203548003c4c2d040503820041100c80306401c401e103407000c6007040c1d1043e06008086282d56888110307803075242c4101801804130341c6003004405410494110440264802e002c2c515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 948212688 1250 948211438 948211457
    0xc021005070b100512061012082106040507030e1c03060b040807140a0e0601120609020c030403110102060c070f0c03122006131506081f0b040606080112210201090606080c10 76
    0x20030004903011044114000040b406645c101e1040031403040b01c0bc28010f40c2448041180e00b40a0300414550260391005052a8409620090001503005141008040d01e4560016424804000800c003400101001d4070759a800c00c02118010361345290035600034601300b4010030504407c07120703aa400400c00d2030403a11714848940c6030b0f0007810350307a00030030665440084d400707040c0c41c0004020012288640505040c1c1007800005907121142140c00304600700d403c0190740c0015031000c108044492041140e412010b840c0d48070303a4403044040d003034080420892841c00701e108000c0780640c200e288a200003440d10349072042490804a84103107009100c1c020075006160b0f4848241c02400141125800321f503104600c95003c000d85a00d0344042c402d520340350180e20200d0f424103000c0c0e030060750b940e522072011030791a02d0f144500919201b10150b5034055113001c0350030103414922240c0c80310300c810f0f40045410107441c1002804c503810b5621003420b40d40003018000d02a1144a1801400802c41c10401d540c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 948213938 1250 948212688 948212693
    0x30b0114092418130c050f0f040306021206120109050309011b020d50010b030601060e1e0f2701091e0902010c021005070b100512061012 60
    0x1e100d8000340030042c035011071801050060092074008010f411541440c400d068085801e0860315005d0592000031420400c004000e802800246018403104039107030315050356901c41100b280c2090451140404402c81486131601d06800741180700c88141000300191001640d03001c3d0ba92150690240c14824011004400040070181003030409401412440581036280f401e003962031040410407031000c8843c01c007801107194046803045d00b14202109142452000711a40d0245250901c10344201e41d2a11250700c02e17514180f0103140206a50746070898100307060410805030f5a001c400701540004511000c2e9443c0d51f4030041d141551100b038440c0d080d2400380c9203d03030000c85140d41d4040c41442c1e84000021300794203150321020a203481e200c2c0b041d003186404151a000c1c2c035030300d902c040d00280d85007480030090b1070280c81a1782416801e05101d0326220300e681d541030280c0710071a0103c00c10646444200000e082c001c024201c5941d000011380110711302140c5a1484609901507286042241c000d003404 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 948215188 1250 948213938 948213979
    0x2220b0a0f0f2006091504030801050d14010c0e0a060e030304050d02061e0a030b18061513031505010e040803010311061b0606030c091b0c030904060b0a030b011409 72
    0x1031414442551190700c400e0351043c02d96444040e81c40c014944100402c1c098603411000c1c10354000d0783d241d03841240503440e04040003004540500d003034800310307039030030030440d03070900c00d101e40c4558070710584454030400b6040c010441c001c0c00503480901480048114090f0642e804011603054410817a07010f0310018990021900e107006410001d4034030781141e4021050400d1040103403c246050b660280000c00d00c1c082801075081703200820003096056403000c1001803800c2400d08103190200c140d01c9003491582190200800710070b80c010344070b290303a8021580329a00c02c1d00070680540045265151346041c1542d03062914401440060128014074240f91003960341c00c800c5034880b400115120b980414003c80403512514240c507140d22034400d0810809250030a015440e02c90310341400c030b000c0001c20000e01581e8030751113000703185403030300040080046075500c51081902500380102c10949807211140050111071005c550b0364140031a00b5200310070403402804441a0755000d4504030251003085446d1003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 948216438 1250 948215188 948215207
    0x60a0e09031c090b09160906030b0f070c0606120212070605071704080a0b011701110a030b040e06090715052802030714010e07120b041103070902220b0a0f0f 69
    0xa098064004c01e02091210004101c40710b003449812100c5440e41ea003a01c6400c403529844020709080c5c40304c00040c40301001d0008207510100d141800c150820060303940d017040700c80710b030880303840080c6040c02a425420120008072501101c81c006120030b90034914050040d01403101c0007884800c0d00e14051900801c0303039050382c0040603424119011858140b034007074689402402642d03400c081c00c00400b450f0007014002c002c00b01c080a07107180e01d4560144000c901811480c4070300c41e04640c41e0403440495040400080d44100e075030380003a00c45541450f012100b182c070484140c5041040c1480701c8103c1d07003203480754011310504942c00c0d030000c5901c00030140d056000da440081d004038107a011200c503440064202c21621703901c25054035805500d440c4022840000d4a030050030b0010007a0003d80051604590750701800c0006080f01c5000e0359a1000302c080c2e80c000d0a200030800d040386545103440398944000c8010302801602c4901f400d000c501d00034042c52134003001c0f40411481d000d481e801203005a910b034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 948217688 1250 948216438 948216443
    0x40e0c0306030a2f03010b0a060e04140a0e01060602160b1c020a0e0319150504020402041a09030610080d080606090406090516090308040e1e0a05060a0e09031c09 71
    0x1502000340200301103410b8903028010019440c3d00a030703e400740389010300c500c80c7e404100070086140903051100c11100103c04030401908a65148030502d0900198010f4912070100f0401c046107003580000c40e1802d444003a4440e5042d9440300842004040c84903c21006a890281c0c4042d21003042c0c1160114885210501344141c500c0001d90300101d07070f400105024501c01c240d04444001016111480e050b5201405c040c210050403159620100f419400c42e80d002400100094205920349081000346288208182031307030100099140c549003010b02c1101e034032000c500c0010010034542400c4540311009a0800010805650005103103036456000717a540d82c881c050001c01210743c50b01003090003000d0a035a800241c400900c6c13140f203100c0c030619038038040e01e0340803240e01e0400f0f1505000b5604000302400e04000e610305803000b031041c0e94480301d103103208a9511101003001c1c01d00c08103121035511280c01030901d0b80380150800c1207541c0c00104840c48614080b054000302e203480c82c6c9445c000c04142d03d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 948218938 1250 948217688 948217703
    0x2030307060e16030f020307080606011b02150a110c03010506091503120a030f061a07080c030d11030a051609120201050c06041a090a020d080a05090d030302030a11040e0c0306030a 79
    0x44140100e45e0003a288003071007502290341c015220303114559554400c41d405400a9061101c004403414030712a01e8510f984094003041d80703d40c40252509140c0c200c000c0510000c0d400601510b401507081040142c8100160003c0040c0d007030000206030f14050061208251860060100010703441c01c00030103440807107511038140c403805441d2005020300400c0c500d03481c800b0b0a007040403c0c200f030f0301d010203452601c080003007030f290820039559001c05401c9450380e0071017400148004e0003502c43c05c1c010154159820711a02d55280340c406090411154050403c45020200d4102c10422a81101917070b0281d54103581003108000789480100ca4034480d10500700341b14040c0609200400204290385503005001c000c11850b03585daa02d680540da2101d1b40400781d03008200c610800301080d03140b80180305401c2c0c2803419920b414000300105800050032041100040e5000040120290707903841800c000380e0703036140c20a00c0c1501c0e0a24101042d00060300140c5400e00000c0483c0141d80c1c100200712902d58060340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 948220188 1250 948218938 948218983
    0x90705091c0308100509151512070c1a151504050d050f1e0d120f0e1515060f0c1c081605040803160501270c1202030307060e 55
    0x80003030503c0b100741c1e1600607080409501042520705000c409100f50b41d0a90540ca030391000e0410051581d01d161460240b0f0901000300107541c2c0030003500140b040280e9219004425003518020360700703002a8280701d8541800c071003802607141041031411004c035030880d80045208404140954070784030720391010380e03c03000f41c11070641000408521690710030074000c01d0360505030480745a20005044200c02c0040c6030803170054140601d01503851008040c032580000520120a0b80f104030454442d0f80c2c0601e015400f034040c541ca00d8080d682ca60b0342c0f003807013081d1310010b201020022032802d005903401421000004664a8801035040211100d001c9905140303510380c0d0814180508a110b082c0d410281090342143c404050500413012030b000c40d0020001903160a00800c903542c9a010706400c119059502d48c0c0e0006203407043e82c80010814609103c6411001340d035468110000b40240e4400f02c0c204400b40c00c0c482c0540d90100c00d9030f4941d5001000410305000544030907041551071040c16084400741d14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 948221438 1250 948220188 948220193
    0xd060f0c030b150403080f070326040b06060a02100207080f1303060f090b060906010c06060b0406080a0603020a0626010306060815040c151806020d021b090705091c 72
    0x108079440111041d1004400c1400740f004402d000d00c91400050408442004401c100780701650040803014002e103854000070f08041200c0c10501c1200e0008c4405010080600040c0048802155044607084940340c2c0760281d03100b0003075190f0182172601d41100b07074046114024014480c0481c0c040d4241d0a8590341e6074007440141d401d0a40076404190f0743c00789080303480c0d8010700705486a40c1c1c1541c2c00c2841c405040d41d5082c100032000c440205280d041101d1a041075000611a0080c007010b0160740c01c04c59113035401c2103001042444c005000c40301c101d04001c420070240c1c9a80c0c0030b510a0780d64529001c0c0c00500a9217105200c1c80070040103800004c403203400001480600e910500c1905c01403000e03500000140000b0f6010714009460150400601031010820005140070100202409040c0403103001428540049a020316078400d10258000c400305101050f03050080142040704001c1c1542d52411140c0411030442000b42140284580003071480c005584400d5401c2d0302440030300c00c07120000b0761813 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 948222688 1250 948221438 948221441
    0x1e090c110d080f060409050a06090c060e06040b07110a0b040e01140415090c0311130503060c0a0f03020721030b01081503100203041b080303010e010f060e0d060f0c03 73
    0x480c046409014411015022038070400605001c0c003580611614552214410000144050a41110580b00301c1b07d18030001200790142030ba4080c044c4854041640c6490f5010342003131084203070b0b90b100341000c000a0107032106020603650780c01c0e040340d86500d459080c500482e00004090708288038009000c0340002e004a00c0e844140d041c0d411603001c1401c049a0303041804161410598551040d0000c104184480e940030750140341200700d207281c00704040d880201540203d6020703a80072108032510301e0342803090b818104046500101e51199003881c06840f01030060600d284107800504042c1c0002e555814844103c882280785582c0030340c07a15540c101800003400030070340b07250344501003428600003d0500c01030fa84800684803025014060104030760311590000e6100410458114a008003951104482c030f64004000d46014402542e49504000004003403400581c0440055160010280841070f0b0000e10401c101400b1b461401031a04c0138540f42d0090140002560501441c002105203100e0f8903 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 948223938 1250 948222688 948222707
    0x80a0501061d040807110301060b180f030f1009031206171e0706031d01060b1b01022701020f010e0706170105061b101107050105090106050a1e090c 65
    0xb42c500a0109203032203010b1034000c2c001281c000c0c03e0400d00340f10490108a03a0728010400306070003000014401e0311100d144003a038100c030103400880342c64648031069601b4010710b11080e07907a088005001d01c04995144958403007200c4d000000e040e40b502d07400c0c802c00d4005c0d046080b813602c0c00c240a00c041500d4564000358030311030001c0101540f04070309442183d004103240d015204110b240142043d5414168160040c021500e1540c44440c2d9800c408503564000380704040180c032142e014190b0f070340443c480010300c00491410b000040e9104200900d42000035a51222801b480c0500c000700c404d481c100141d0401c0c911501e0701d40d242d400e10128107000c80c00812400305482141e1114801c9411440f0300c001e0090742402000e800500c20410340c17042c9a0070360a9445101706c40c00413241214441c3c82441d090754040c080b00c3d91700c45404202a810402d00b0301503142d20101c490000c002031494040090030b0f000407846805405c190020461840310388640c0070303070301070845c0040c280a2900e1003800100f401c41c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 948225188 1250 948223938 948223949
    0xd02070506060f30010c271d15090124030603051e03040b0708070c1415090112110702010f0f1d0607020d0308010302030d030c1403060406080a050106 66
    0x403003001524030302c0d001a1160390000082c00300c0640d05181005010b6031210005410a402c5003040b803a01654003d0240080d10051030352603020039283c01e00c9214001447c00c107881441c01e2000803d0188050182c440d0000340501d201c1d2691a45070041050781c16003016a489403c254110700120342a03103540740d01d500001d03aa40c800d2030302e082241011001c60742c181c08028030704d0b00803503a400c0c052007400100492088130982600d02c1e00390340f45180d400c10780c06080222040200825030b1320501261000c0040101a18001c0d82400441701000414080003869034550341d500105450396181d01c2002401100400c08100300100202c0c0f0000b0301d03042e045550200d000458a8800b0791820344107481450280400341c0750944403403140340009022a20003465150406418040d0310090f0362030800c1200c0ca9400b94841c1c3c51554118010b040c14031a5007079a0500b85030510684042665210404010803125074142070744903141d00d000200680519403050040d8403035849000140030341035110004440 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 948226438 1250 948225188 948225193
    0x4030614091b011e02070b121f1401140d090804080f01182a060305090d050a0e06030a02070812070f0309020a0e040c15021510270905030d020705 64
    0x41d0b42c1e01e2a00c84000701c4441180c0042c50111140b070990140484d10040c0306040d00695400588502648103950403042c055a40381018800f8418038080d44071240314818415115500d001d07091115500d04003c014005038108409009100380c17142e08070040e203803002c0500b01e040c00714104504211140f034115005094142c007500040401c0c0d240148281a03240350351303061825124542e902c8918088008400f00c0000200144426034000c1c0d01142c0c01010f055261000a15414048040c62411041010301c0c418441c04121181900d0340100d01080c1900044612550b03031760303d14074524041c1c0101c403001041d1800100d00c3c040c400000042c010320659456540c0301e41052214011000e41d0701a42000e0740100309850305200710021007040ba80c0c414024500c441d40d43d80e440070a00c0000d005e000d40540181c0200280390480e000410000d03401c5a0760100b45030701d0501300070401c10300701c440100c0c0d81e80c109c20111050100d908180c000b00a42a00841601d44441c03010042501a5018500449190 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 948227688 1250 948226438 948226453
    0x1e0a060f020403050601180b03060a05011d07050306060c0106030f03020102031806070503010b0d1b0519030b0303030a02071416050f010203120a050601020f0a05010f0608060106020c04110403061409 87
    0x15200b03807400c60740c02ca001458980d2818400003154064686000660750b124090311000703407020045140071fa24000c0c3c00140c0b5614000250200c5928002031400c801000b0052124842e481025690406802c980d041d030380300c40b48802c4500411440d44010009102c0c042d4507024950103501941c41680c245500f403403507450300c16481c0e4480501b10380800114a09000500581d69a54050103135900a5038000a83d05000b9406008008440e50f076480050750000e1860100840300d0080010040941410700030010020b0000c2e44030b02000305000e24a65010401c5414440f000c2d01e070421710303a890410707130f5031030007000c18090f00c0e9100500038030b401080550300c5000203520000c200c8002d401c6000f041007154841d245840d010340806000c86045206205d907490140200b80041207485101d10000284403103603000440640308a035010710307042d8126800401500e50089802000307003004890004413529402d6045c80d560181d038001170981c51034a0030385072100c0c5070303000f84c0da00440fa1402103c2d0391 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 948228938 1250 948227688 948227711
    0x703061b050a0f030f0b040e01060614090f1c1202030d140f0f0c0910020309130908070b04050709050c09030622141c2016171e0a06 58
    0xe80315410702403002800b40010650f555102e603100c0316a8840c50380c008103031000c0d1180003400390b5000f074090742400d035904da5040100e290480c13060f511441c141001c460401d81a00c00190900c444400c529001e218032011005490300041ca62200c078a0340000d18031400812038400950b250001001d0b045868070708183c1403d1031106507621031003480c4407031400e1020b0b9900c01903802040d4010b440c7d20000b40c0f003808001c0503a84c070010003559551300b9600542c1c03610340c903030304100c10b2521100018802c14508100d0f82c0200c0c02c96000c80ea0780540040015910b501c5d14a0039902e08203840d8030010180d490002844003106d448802884903a8080b400c4550795100c58014469201280513202800519900920000342034169002e5036402d400c8192500c1420030104510f244840420200c00a581c5400c072400c40c480c00340c903c00641e201100208100150b039001820f00c0815406442c4025031411505643c001040200c6c100c980401c0810390585507032402c1e0107980300303c4c140c802c503034203424032415092 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 948230188 1250 948228938 948228947
    0x9030d0207121b08030a0e1e10060b070c1e0e070804021e090711030d02040f0f06111b0d02030715030c0302031e0603120f0405090601030506010f1404080703061b 71
    0x80d0f1500800c0322441d44e2101040000100340b281c03440e040c81d02425407618070681a4803040c1e00c00e82c40d40d0f4050044440984d52041c01c032603c1d80c01c003208020040c00081c0101c4c0003801c0f01400c0d520801c404c6503180c10000201008021180c0c054102d4a110804001c202580038943ca4040e610958207074102d2406e0700014581101c4c0441520740154540c000102110310401440704100c0b440016280b4000e0180103a9099070300641016205450080003001550000c0b5040c030000c0c000e83c03620300149640800f080f520b59010100c800c04040009850b8011540c40030600e910761075004044410345d582e14147c94840500e801c01417800320f8540201d03c18000d0080c002c0300d01c6510343d0100361800e41c040042503d80120003402650b0540715912120204806440040c83e0b01c81e0403030605500c56292000b0003111080040c0017034101800c2409120041e60002c400d0102c0103150b0a107030030355030800c0506070364038042c5c1e50080340d542c8604c02000080c0102e540c02000d0200030002440c070f408088900564 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 948231438 1250 948230188 948230237
    0x2100c05121213050d0f090803031503070f0f03231c0207060309020901050d140618060112150b0103020f071b0501081e0c0d110a030c09050d030809030d020712 70
    0x200642c12117804031510500c0b54142440c44040741c00d004840d192108066455500308941ca40000703056603100700042c2c03a04115000c01058204d42c103802d0b039810030088141d0b0500504c401003000080300494040f000104507034480c66540d0b030b01280e41031a840d0200541c200c0700d14400304094081c0107070101e2500c0c46409a507003407640280c032002c8282d01e40824801c4032400c4000585032911006601d00b403640c0b040c405140158008044c0c40500c2040002032400c1c1981a8000311a0f000341c00344050028003800008140d169004100190b080850001640a445201e0b030500003510009420310411010b0410f4200514100402400710b9403031794015111100c06a071041b07409404440c0c1d502603002807101050f4450041880d0a00b00350016440c401510b090701000e1200300800b00e03440582c15031500c103155000c80f0601e031a00b0020300d0240801c0e01c01000c2c03580a0100302c1d5000000341040d200b00700300c0b01c0c00e021510085642c7d0805061080c0c0d00c91078405101c0c0003502a00c0103104102150b00c050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 948232688 1250 948231438 948231443
    0xf14030f092701060f1416080a0c06020d020c06010f060509092806091401031205070c170618160e0916060905040c05070b010302100c05121213 63
    0x80e241500342020031004000b040e094036808000000d5035680b002007801c5450081c043e40e150700e03601103c03c81010b8000b440b800d86550b0b40c0360041c4150310704482d509001c00031040d0041680740d550b4050103805c80d03030704450080c00f03441c96000094138886074031180d004102c013140c010280d80f01642c803142d02c00c0c030307407500c0f0b10504000610501204440d4a00703400382c82d80001c070301c00001d004140070b41c810a8044100e0b14403181483d99805081000c0c801038055012040c04d4206d403032490b513045907540a09521080ea01d00100a404541c110400942c11214400341005508022014198001040c0e0b0b9000848540650881452698241102c00150000d00c00b480c042d466800d9810103c40103e0003000501c4120b10380300d2040c0390041e041c40d4001441c00703070403c3d80c2e501e401e940c1810140425a0340c00008102081010440303000843c0340c00039081c0c19a075040702d281c140c0044403d8200d900040b91070b000ba20a0142403444000e40210794018200b842c1d000c1c501135020755404040c03045108141001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 948233938 1250 948232688 948232717
    0x803181509061b011e0c0f121a090108011b0203361c110d0b04120302040f06020309091b07061d07060207030b010e043c0f1403 56
    0x1900001e00d4060301401200c628a1080403c2402c0d1080c00c07400c0d42d42e43c041c160401c0b900d4041d4621000140d0140102d0008142062a042c00d1020b0000341000c1d12101c0c030005099a9205501000301ca0414403a40c0410080c0781843e1786d41c613410404e000b04060b80d0f0204401e001c00c00ca5206242c000300565000c03070300300038184046403d111400101c114860f01c6500d800d0000c01400c204591311030f003c036012140b144480f44107070101890555968410100742d5841b44042d0034002c0300007520140200c6d405940036510403503c0040d047e09901078042e580123a40b1080c1c0c10f59000c41e40540c004082d1680e440101d4501d031140c1c0f10000300040e0036009450200b01060200547c401003450f64100079685a8955050a0a4880d44452906100060700200c0041e04042d800708144804000118054019485403041d24180b6503500d40507410098641002c0251411412083d448603083d00c190b280c0392010100300c104014a48a956000043c00884e1680300d8101c080800080c000191100d490010070b4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 948235188 1250 948233938 948233947
    0x70c060b0d1b21031b08030f240607080903120c0a0b0c03152808010c090801141611030a050a120603080d020f0d0f0c110f0d2708031815 60
    0xc08170741c01401c00c48141e40c0303055444c0000002511060043d4843c0030606100c000700d00784002c59a030500b18082a4001155504034a1003140d500c1300c04031040d481c1c0c064103980e518440140420308020b1040b818280803c404a43c240e0308000c0403400c40800c0344108111041a51600140c2c11103000035501c605021084041d404194108404a401c4081c801c801107248108020f40700c0d00b10b40e40a80080381c0c60b035160310806000981007000352014103164002030001480d5001900411907000b40001010301010304809101c50013903001c4c040501d90752042d2643d541d48040084c01c1c683c040ca1211000620b940072401d036030300e0300d84681c0f4203685e48008003038940b506500710000a900a0621508200010004050365600d03030b200311903520801e18808111100c00e403074058482a44c4000c0305120ba08203c815000c9080d01052130f1070302001c030b402c0012840e140601041013a1840742c1c02c64008a40d1074401144091000002e0070324440c92a8082045031405018880c1440b4000c450b103c02c07400910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 948236438 1250 948235188 948235193
    0x170d08190905010b040501090e0705010201090218060a0b0324010c0506010e0a0b0d0f17030c040b030c0c030a0903051e07170c03060708041712070c060b0d1b21 70
    0x8101c07205550141e00081010080080020101c54003a8084e08c9020ba1700c50403c04006030034041c5400925090000f001b921400390046a4080c5078104d1a40d40a00040001038503a9581c5443d00054000402e0440e268034000030900c504015600c44110215060040071100e0741c0705030f6803910394542c440040e00312a4a0403c131000c2c3c41e94003408880a9645840c0018560340361500142c40b094040c21380310500500c58144074440c1c452060082030441e00800030814078440d0b11040714211210040540d03600d580740100c0e09102c0c0036000c0b090f80f5600000a00707440c0c1650040c00c2d0401d8034010000d450080d00940070440f4040411031007119140c12217001008050000030500001200040c02da07000010001c2c006410624101d440c0c0000c568448203202c00d200b03510010440d482d41080d1600e14124140480c4003484d000104280100a071a007460000c102694101108481003d0320b009400b14130752034511962000c210910511111713134940012003040000b40000201445034081d00e26030001d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 948237688 1250 948236438 948236441
    0x40c0f150c0c0b0705030d05060604051503041a0405031e090d110d02090f16020703020a21080a11010b0a050d1e1506030201030c0207060504060c0f0507170d0819 71
    0x1954182e0700800c00600019815040c140100303209841031028642d2187c043c80100d086520203400c04d40181e2050005220b140c031901c904075130071070f50f100c65251a640c0c3ca181c410541408540c8038400a01c9100c140002c0000000207042e240c08400304451100d44000d6000009000b505c6980e54070030540c01c41c140100d00780d02045141c4104c0a0001c02d041c4249401042c6401d0003075401c0c1c000d002d034150400020100e00408001c2d1a02140b024000702440c58001645026a0b4024201046076405002c440c0303141c0180d0400c0d0660340003107141d48070494103601a1481c0384070800900603500702a041011441c1038600752055841c0107026144100ca00d4440c00c08454118071500d0742816004250404180c1d8900c00102501a400c0045103107801d6200040a546034062060b00707540c000d40c0c0a110950304281503d0640d0898940031821114900b0443c0c1c40b5000c0e800090414090600c1c0030801ba481e01c4040140c0c4c240000072640d041f40c101c8012558000d089500d20101030118604541840c0603 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 948238938 1250 948237688 948237707
    0x3051302090105150d05040308091204030510020a030f14150a0e010e04080f072d0317060a0909060209011404030b04081308010e1e0c0a05060d11040e040c0f15 70
    0x1925413960402e6039100f086012260243c030140d0206031003400b003000105040001d40403e5500e0720766182072074515990340c4d541d03c4400700b0aa01d941d0700450180042446640240340702c0c5446402405103a00714034000c1108a4103450300c00f42d82d4015040d0900506210103200121040c910040c0c115a10f440030444c0800d2000d04115401c0070100040c900e9041450b003e03105503409500c00740c0c1e401900d89214120080808800c1190071920010400440c3d0040b0070b03e0b0104503507a03000700a036582c800c0014010342c410340200040d42e141c40b85a2040c0b00965014000010081c0c03150394a03aa007502c000c200f14001c0c1e04c401460808142c00140000e51808003501000b68805401114240c480c0300007429540e606414031200e070300c889106801c01c0080c0c6c900d550394003500c40c0944904e05a000215200340102c1c010180103503000118880410b540d0b5109901c040c160603031280c6c585403180f9080c036048101351360603140643d03612404102d2a41c950307d01340c22204403047c0400d2400700c1c84030a85d0003159 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 948240188 1250 948238938 948238969
    0x70b16020103060e090c0901060804030206070e12030a08220c0605090118060e100f1b081201060210110f09121612050730110d03050a03051302090105 66
    0x3124180003640200d1305101e01e00881d60700015002402170b5009101d0324240507031240c0308014110040c00003107034000c640c841e080007651034161410110724011a41c55442850180450701c000200c1d044420390001146000f03c054480c04000c181c10152001145460010061b00108d141d13001046064000c0b0003e02c400203060410080850070040c09080341326040d88264045803010411752101c0ca8003884241c181d00142c02c01502400d40000000c09007146c180c04000c0c000b41c580d40c600c0901a00c0c1e0300356503030b01c08030800c0f441d029038441c03000a454240d1002c07125919402d1010f2040554a16415540d00c0b803140b50070075041c490000c0c02c000241d02c00c0c040d8400503005509245804a84419001002d003800c290750140182c02454818a0020150b004600c90381010000a001d80051560b402c0810303041c02e42002c0081d07540c02d144850305800302c0e078503500c03400c1e0130610020144c2040c051f0000f22241d480c20020384d81c409404525a40044100961000307101d030042c062450101ca00c003407903e5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 948241438 1250 948240188 948240191
    0xf150d29152d071e15020d0e010203251103180f0d0c060e0406051c02061201061e050307020706030f0225050610031707030e062109070b16020103 64
    0x4802d21045031001c080b0440048a414002120003d00c07843c0001c01404074100d0707542d50000f40c442c1d2586445101c1c015240c8001c0c94000490440b4082550018006000348200865990911613201c0c0b070005403000141c0c0808456850314001c06001e22030050741a48400003451030300d4404011401c105204200440e80521049203802c515100d2080f1040064071891200305082d04005001c0d0980d0b8101c94414480c81c00d0080034441500e45042809071070303042c1c0408449000051000031114010340c07040900c040348000001420980c049908a600041039000309000c0b044240200d80c980b004540703000242c5d000100070010700b4400c0e40300f491084c2d88030000504010304540030410781307076800f64003015540101c051041802024816550401020210414002d140d03603a6062405100c040c40e61403100301040800515004000552110100a003015501c110f15800c5c0060b50a00d01156045000380c4030014001c0400060400250754610140500f030540c66001d60001406400d8100d0405 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 948242688 1250 948241438 948241477
    0xc0606040c210507090305010c0f1b050a0b0c21061e240c1207021201090308070311040b0c010e0c040c020c13060806041203050703020909060f150d2915 67
    0x140003031040b408d1400492b40d40d140c01d03281e94000109a81e40e01c2d84408148611001024001040001d10120195010301da4070702556940801c940c0d0f6000d0640c820082c880c64044040a0a284008251140c401101c1c0c4525600c0c150070a02c000703000072098a030304640750702501111904103003681d0b40b0b01c03080c032454280740054520441b800d0216003c1c0744010b4840119100c811490080c840d041c402520304c000300406c141c0c85d03c0060165801602e0034062540d2011001790303001444007294050035006000b40e076510706114215009290b4016000c055010b071a40ca8991480e10b80030f03900d102c608550003441d0421401081265400482080170002503480e91300294180e0240400c03482140501b445856075003101c031014041e514010010020140704004c4a6150360703940580c82d4000c4c42c180d40b01501d0b0540e00b4081512074240809203035030301c40040341311000c0001c0c68001003109c100e003039510360107040e040c05482c00720b14110709843d03400b90111240010801080004d424000041e071005140d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 948243938 1250 948242688 948242693
    0x160312050c010902210625080703060302090709140d020906040b0406030f0b090f0309030717030903100203100605190f02150a0507030b19030618080c0606040c2105070903 75
    0x29051000103004900800c445c0541c1c180780c01d10401d070b88060465035a42e441e0061171854070b0140022000c5e08140324140303002c41c0e02c90748268044405154042e00e80d10140c240f2060181a02c4440e1140b100305c180c0e1058070060a042c24658425155030140140701d540c0c58a404000142101290b01908580d9903000000444e08241d000c07100d5500880000d00356050104115050885a080c10700403a40b00304245421620300003110002c54032103017402c04c05101000081404d510402c021a64580726480783c0f40480d0342c480d070084d0300032110151121815551000c00340c03480d001d20002240410302071301518234464003610803440380340c01c0c61041d1264503043c801d08410024058480740c0004d642e410400c032941e13405100c3c0e0902c010007195454140c03c201094055081082d010003040961101e00204001403000360040d02c40d0303408040c103034607005070300f022903070307581c8201c0300170703104d20b003444d0365160414002d854898002c1c14402e264580c3d0321403c0c00d0000030b0030028000800308040603900002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 948245188 1250 948243938 948243949
    0x3020f0118240f0e0f280906060f050d18080708030403030506090c030a0c0e06071b0906030b0112081b06090706020606010522170f160312050c010902 66
    0x103000075080c0711007500d160309500440030070b061408009100424200c0c0f50403c1c1c10085052002804035000c1c4445581c0740085901c1108040d002c6005065100c4003c500d0510150110143c0d25080010481582e880400311960100b0810030808680c0070008050342200603001b01482d46412031403e41808020f41e0703030402e258407085003551050070101c00e0104059050040d1034011404450760030300303410002c0034801c8910016000d500402e079543d102c00c15450045500080742030300140f00b01d80768045400c01000a2226540c62840c0020009000c200c0c10b081d44502400d584d0040c94411590b800e000c3d42c0c2c160148005000d40d2440390074041d0344a114074024128038445907440c00307841c0d107050041400e442e10169030444025904107008022182e41d00c00140c880b1080101c208030a040b0800c66a125010b69503040149440120701c8000d410b12800501e03011050000004c0720002c901054040c1d05102941c00000e00343d0300d50000d0900d21600c244080c2c210041540000140c80d60319500044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 948246438 1250 948245188 948245237
    0x2131205030f0708071502030708010b07140d0c1406091915060f03060b01030b060d0f15030302010c0207060f0e010e041e060801110f091207030501050903031602030901080103020f01 80
    0x1148444002000810081e481e600381c40c0001e04003001f5411030134400741c05040c0d5801401160380d0741401040f114107000c24140080c0800b41420300ba20202c041104004141b0441d1040680d0841041600d45904220000d00305204411079006801c20310340f007545d030030300c04d8a042005444100902041c100030314130501c54680201200c40c0200c440c0e5185203031500a50310780346991418580b500b00240070a4031440101c032628001c01c2030004004102c004020000d24a419404041491551000c001c2640541c8070f0018000e00d5000c41c3d80d542d0352640216080c10300b41a02c80000b442920108407254011050b49841420081000c6900002c0d0348100340d54040c04101d5004d15911148200491721003845402c074200ca0740d03480146001d041e01c45a040d6442056450303409101000e000c1261580180072a2020710b87c404003c2c0310074246078031200d0b601d030406d03268505d05640040980c3d00c458000002c036401400c0684800c1c40580c1f03590204103204400d0113015040c840882c00756000c1407a04100036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 948247688 1250 948246438 948246443
    0x2070b0c09011707020f25172a10020c092809140106051c1217040f060b0102120906090a05130b043806130f09060509042003010f060312021002131205030f07 69
    0xc1a100275000801000046100d205001d40d080003e0f8100682c0346c400075203030301c00b80c0c04403da81c541d021a840040c41c01d131210a151a1301d490100e071001081402c0c003a241010070041e001f88880754503001048440b12681000f291200c1401d4102000610954442034013260182804840c19440c0c03d140482c554080f6800c81c4c5035000e001c00750f410401e041c0f1400b402d9081c01c0c40241400c0e8000310b000d94041c81024a0030740305503004520700300960342d0b001642028040242094201c2e18042e038606001d2f00c90b501b052031080c0d05016418001051100040a0032400180034513001c0c94180312544140ca512200c0700c1c1c004d1020000c030111041c030619400b004125244000c8295443c01d980d20302101c0251300b0141c07080d100c0d2000d000101c1c000c001d001da4400030916032810480500d00000e401010f001d03904401e0203040c08000814030040340c0c1c010100d074141c1c1d000d03141c502d460001103034200d10419800e169040e00040051121500c400d00580e03202d07124000316031400ca81041c0110598100d82c2c1d08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 948248938 1250 948247688 948247753
    0x30b0702030a030501080102091c140a24050c160309050303030c040609090b0f0603130c0b0306101403071b02041109120102070b0c09011707020f2517 66
    0xb8aa0340360351520405004164480003103081540f1200000c01001d451a20042ca045085545906002203110311007184502501241d00f40034039803034071842e00030040d0422005004100c0214005161900599105064182ca81480c0000d145410401c40030144e40c00e9080101842c80403401d0385080000303500803c1c800d0b800c1c6e1340b02c40c42d040000380404401c0d0420410141090410f4403180c58220200040e20412107c2c3c545a5031032202098181d01049406025500c921100042200c4a0401140a00c0c0240c9400401d0009d048040d80c011201c035001d00760380c4c1030400003e800c0c1845081d416003c4000d1100221916910b0f0300058243e80020719619a00500001d01801914204031003e903141d83c404000e50802c5043d4a88409103c0c00070500c400c1d0b003400007030001d0035a10841c17030020145907000200500c0e0030040b200945e2200c021070690b280b031180c1c0c45030707404060306941d0481d10140c0c48410808540e00b00305c8485000c54040309079a442c0d1195440100110000b00d01d82900c40441021 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 948250188 1250 948248938 948248947
    0x316060510050301110922020409020d1410031b181b0f09030b2715060f0306180a0c0905151f0e0111101e0605030a060b0604030b070203 60
    0x1481d24090580d0390115100b0780c906030240c020039489405460a040049030ba40e50211080f811984032481c0c591001ca98541c40083c010410014a03070203803516004a4404020340c82410940c100060010b580324188100303580e900b040001c4404040c802d800f40812840c0041942d540000140e03001d40346038821146071104c0d8000003030300b51400034440c0d8041d140707040c03902a4485400901a1240c40c00041d042e0300340040001e0184404c038a4240f500ea0b1214070b003c1602e0a0043c64580341c1800c0b5103100c02c00840d1b04041007240c900300761034100301400280039000c4c5485000b2071070600005034840c0d00080c0035180012010400307050303104008040002010840c3e1500340d0030510018101c02c00707075100d8510948400300800410780c8040040ca103500386503900008540050742e1100802050340c64a00c40c1d0000347c1c490304070303541190400c2d010803268985008a19640182074401e40e014450301a4480c02945002c00c6c10b580294041a90140880c1c1c9016102c2e01d907008440d1003100d134080940d00014 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 948251438 1250 948250188 948250201
    0x1b03120c0c05241305120c01020a030e06091509010b091602010b1929031602100b090f040303060f06030501050102060604050405071403010f020d0902100c0b0c0c03160605 75
    0x44100c0010260006149105165800308803658802404150110b007a13044882d0421070100600907410810069481e00e8071107903482503000c0d500c440c00c0100000e080c244811002c140c00940180030746085405007108446c0c1282490040314014000407040d901c50003640080d843c1c41034254000e00c100c048556000c4016103010342075600b91102d242c002e4046010300780501c0580340c00002913549407500c09100d801d4100400794943d50300b1549c084040400010302c410003604c48000e8a04000d15000d549070302030391102c40021070340300440194201081e80001100c05942c4518954010300c2070038000341391501c507402031500e554650030000c0800c0d95180140700d03e40e0100501503000c042102d0034131044c6055900d50b51108500c1c400c182d844940c80e180c03414035540030740010641c0b41001c4011522291100701820150981c40002e034010341d112840064035900c0f8114050040c1d8000d0900c6d00c99449000c01e480c511741c8614401140f501090040e0000328042c0d12040d03007542d0140e0004a0141802d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 948252688 1250 948251438 948251443
    0x1101020f04030c030b10030305030105100e120304090c0503040818011809090618110907051605010c0e0a0e01050907170415051614090109170703211b03120c0c05 71
    0x207081c56446c9444181c04100003544a01100d054500a98410181ca4035205065540f00e0b0044074056005210114901055000001500c03c07a0402e0034207001c0f1075039205d0155030a2005440240c01e800040010000000d41c00100e640380389030600d4022014218001c0c00c0c00d5021403500b02e904504d0b01d42d40ea8409000180c02000c010034140b528140c43c2c0c0340d041c3c0d10303040e0010301c080d0308501030900880014600c50161065500c080d1034010118510407403031801d41d000b404ca03203204e1000b1801058115005007050001c00c1d06640c001071829440b80d007172108102c86003000030064010090442a0354410f08002e840e03090241d886444086010400501000243d400040c15441c042c000b40c02564145a0702080d04400d03140035801c010740d00c0c81ca036001294440c0154001d80c0c0d1000c0c0c0340d041d2a03c00c1000040101c1243e006045034100c142d14081d1407180304500a954034002000813020704005c1d071045a02c1c1c0c5140d03109007807124070740c4012206001500d9005c048180403d004040000511200307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 948253938 1250 948252688 948252691
    0x309121a0115020c0d080f040f2103081308130b0a020c01180b0319090510050f070c084503010b30030f18030c060a1101020f04030c030b 60
    0x441c0540c2012881c00c40b000b5600c403043c0d400944201298901c103014849035408a49401c0304101c48a603403140c0391004110000042d01c120344680e510b00304c82c00d42c0ba61035492030780440c41e410342c1c80f48819103860f42c807003210824905068540c0002000846100c2c124244294020901c00c400c0940b00c0742481e40182c03c14100b01c0300c140c1030010078842e090140c096564008285c4640108080c0c0302d44640708038100102e4006224429540f4250034031081c0b01d000201c03441c415070070341c009000715520303c00240342401040e0759141c0403130019100d2000013282d84010b0040100c518014088a0900021607507080032600b042443c8410450401010305004407141e00d2318407002d0b0024449260a84041854000100a091081843e40460ba0b4031602c405446802d940c2d00d0100310390311010000802000c4d031307000360003545550a101c00310284a040101d0141704800d002001c090510749120801d450400104200c41da2a5500700440f108a042a601410145003c0d403105440141186440c41040c0c10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 948255188 1250 948253938 948253949
    0x20f0109062f0301090c030e030a08040c1a030a050606070b0411011418040c050f071109061c0305180d0c0e0915010605160605040311010f0902011b0309121a01 70
    0x11981a400c202c42c0000c11070b41150718540d80010030540550048004144800560205001c0022142002d5038040c8007907000b64040c2d60028003041c2c5d20300384810020b04085008028900c01d0000450798041603200300c0e4050409000f40386000000c1c0d9420a2501b02101c044075035004440b159586964052207a21900f2075540407d8900901d0b0182d145100011200080c4036a0315602c05404080c414425945912420449151659982e14010420401c03151910b030284e02c80c0c100088040c0f41c513052462890f028039405d45029592528212420340c40f03090007400f030008800c445010354903102024151a4041c10410103024103016403001c1044000c3d0002d50306500403075010480200c0c01100a044541c20b007003840e550000d4402040d0980c1c00c110000d418030f840c00d4200070034550840400c40350500c03038400800100b007a10f44504d00322603441c3c6001c0d000a181030217682101030004a603541090003810b049442c1540c0d59121100703400e41039011207080300f407015100c0303541100d41300d51809440c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 948256438 1250 948255188 948255251
    0xb0f0103050d0e0a051005120a06050405070903031e1e0203190810181d06040501060e0108100b0d080a0c12020c1003021c0219110606090412020f010906 67
    0xf03203010003c0d4500c0303100d000381c0b0b104050319030480d400540150122185c850200140900c05e143c094407640040125103c2c45004a041030b00040e80c092044083c0400d070380d03040e200c54600781e4011403c031411410a0409100340311026081d854100036001414881424075030003907566002c4062015010340d09a00c90005200d420360074003800e283d00c07000c0d100c02d4074420130f0030002e14030b010400d2001503e044030140100b00711900361103081b50004030707926224038014002448030640c2e03107006510000c024410006241c0120b504e0002c0c0e40802c0d0404c0301c004800401c520001c05054842c52a1540922030040208581924080401c41c1070500f540400c0c629001070b0a5060a94010441404103030986400b0154006800c41700501000740070b04001445d490111b481e02c881810541e00d030100300e03104002003964102499240500080d5507441840f003c0c011002c1c80e15143e83d00645c90f010030340c1403800d5009510079003010344001d1007405000c03030103807030301280c00c2c4a42298040c2c19840b0882400d04c02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 948257688 1250 948256438 948256457
    0x3132312041409091204090b0306100f0603020a03021c02130b03010303050a0e01020a0f08090a08030310030204272d02030d08130b0a0c080709180f06030b0f0103050d 73
    0xa5203141c181a0122206441da00f006540d01e004550070001c810b0f00c14004400c000c240864003c0659001d510002019021541280c48030140804410643d114140c2ea050402d102846402d12980282c4580c400d2810094140844140c2482c40c4d260320051102041e070740802d508160944601054000b0803a40ca845891541561801031152081611803c140f265480340d1400e1640b00f0001402580d80024248140609034985510250b001e000198070031440740d1404100b900c1c0c044100c034002c600e11210721907118078650038000500100c3c10854000d68000c42d48800c0d50100425110016100703042c0c001c00c44801e0290030320300040f050079501014001e1048040140ca0029000d002c10f142c2c2d0402107681e40d906032501721214601c05000340b141c00e9100c10300583c248941c010300214802901e072259143d44031481110141201d104060244102da1240802d6082a90042d140d4103c69200480c03200e40369103803180c900c0d50030340d00c0c040301c198008010024400c05102e02143c50500d40740c100d810 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 948258938 1250 948257688 948257699
    0x90606040b160c091812020d0c1e14010c021203062d0612040b0a0b06070803042120070501051b0f06091006290313231204 54
    0x11070003800360303080e02d400340b100714a424440000800f00040c0381c4000280000100154004288003030410b0480d40640c2082c98101d00a00124591200001c1c41d902c40102c1420760b140e041090f001302401a003a4420b8440b92408503110307002144032540300c80300204031045040030007440c3c02c062030003000c191001441800800c0c0d80b2510030302c401c86604484580102c105c0f400e461455885040807a0707002000241003074131030114454484c070232800b07800010029910450610280c510b2045426441141040420f0000d1500c601035038106028960301c0086a0711090a140002071043c100340105041900c82105003e501c0b07030301d13010440700070080c0c10180d1a11001920b540180070140e80f241e00c80d001123650981040147c226411a0002214034500b0044080c9848606440981c0502c0d41821004038070011502c407032002614034150440d03405502c1c0c9840c2c0c561504047d10303d2485070204289140495420300e68103680c11481c02148001490040c286494450240c041300f980b064144003c105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 948260188 1250 948258938 948258959
    0x20c060f0106032904140108010b0f040e0606060a11070b0c010c0905030709243003200a0c0b0c0d1d04020a0504090203040b0402100e09071b020d1109060604 69
    0x10f44c2d070051390451508040180005020f400300b40b8a034105c0d00012400043c54600540002c0303c3c403d8160303814250000c4400070b00059820201c1034503071a900110220745281841c000070030040d0f006141c0300d000024070341015400c0480383e50010031281c030003058410710181c003032080d101880c4050030804512407078900440d40344e000c40d101e07503c1001d6456010030001002c800605001020040e10041100c0c2c031918156030207400503003200b0700382c0161268251600406450101e41302c2d05034440d03640104580c41e0800303a0151041400d202d5000d981824000075040740c0d000300c01360080c00c0d903142e12070440908040c0b5041040c00410100304158002c404d26071640300c1550860b140a480242e600c007a149001d5032588580e90007203182c036100004010a016555040c82d0140d40700300c40c00320080c03603560011200e1204c1c2a0750298020680f001081500d8090039500241404500e90860003c07026000035491034000344c401c1d20381040080b80035207145071042075a9888981199010f0505062a0381c000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 948261438 1250 948260188 948260231
    0x418050a0c0507020f090907090609020d06051e0402030402041e09052401120809100905090f1e04050c060a0201050411010f02030403062c01020901120b060913020904020c060f010603 80
    0x80c0940590b0004c50417141c07023804180040c041608050002070fa0701e1803100001d40c0300300400e0780e01c54a00040414245010300c510f03182a0203020201402903240310400000794400ba01c120b034016581ca90f88070f0a8004400da140da003d0300e03284002060300f40d038108035040203081594009003150b070f94078412800508400d40c07810b4982406040d04803800354604101d02e4414000d0150707200031401011084c4c0742e4072040c2c01c8117072107066426071050b403070302c1080a01d40030050b941c0c424201c90b000411170070040400c032407990150249044440f4840711070003080069000b480d803400140d45600412051214030701203441e03c40400e2800360700710940c09000035103a004a00005061030740790100309105183c003c1407240d00910303101c050f0440d500e1580c40c2500075885812401d02098070a40d600030000440d1051601d402d0019042914290b2802d04102038034450203811074003280d0038484000c40742c40c0d61010b0007071481510010012800c0860f085925080d0503409401050300305146c100261525503d500b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 948262688 1250 948261438 948261469
    0x12090118062d051204050307170d06060e090402012102031f05060c060c07030918050403020f0106030c060f050f0309060f09010b060a031d06070e01120b031902060418050a0c050702 79
    0x804c058440d45405820351090042c050040e2460001c00e440380712500008191248401c01d00300001a9107480694003801e180c03c5c0c042d0320080081c00940036500900c0e480f10000c50b10f0f00c0601d0301004185040c0b0072a00b080e2200040c0c201100500007070240ca400107080908030440300706007490300d014003280c1c0d03901c4002d20340d507059040442c0142c105030080c1601720180c40204250300707203110011005d0000740760840c2e084c0c00520030307440034028141061151006584d08001c5c4441c0d42800d091066030081904000c04c42004400c100c07541840c62050090350144050002800060500c1c050700c42e50064082c1c0701c2122340c1d1600d50800c44941c0c0d03c03411500810054107001c82c0030100442c0d2510712580c0a00b10400900441c01084010780d441f4200840c80c2200340c0b00c1c40a00e8849040e418202e0b89080c10450301648038072079000c1d44c000301401d26101684010403070f44c503103a02c401e0440a060408003554000326164000e1100980043c000d43c00410f1062504505045090f0001000c0d0380c02000003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 948263938 1250 948262688 948262717
    0xd27090605150426030d11090a060c0c0b030c28080601020d08011404020904050406060905070e1302090604030c06081e0c09090403030f181703010812090118062d05 72
    0xc018404c03c050080d6105507140c0c0800300444d1500d0405800305602c06c10723400f40f06d10b041c4400841c0060007203208840c5a5040000e00c2003640c00c00d02668101e40c00600740e20404003051100c00060900b54031a0250a60084004100e1004844019101490240c042c5045d900154481112140d01c003141904549509100c90100102000490000d01c10001400c0d0001d00303040400c42071000b20741112702110300c41641001b641e5039200003102c00e03108140006620098030500c1f50380c0e082070303900030b03248a10340102030030300e041c0e600c0e035076003010b4849a40004082240c42c010814501d090550000c2c0440714001070b4081441e044440c0623040c415000c2c014800c2c4030420100e001e0511076404035540c0e0000310405c00142200c03c00320350048902a00441d40d03d00b0703242094044011800030360381207480482c014140400c0d10f84865101f5000030f1010b5041240d40100c055001a840895000526a58459445070000d28541c100c4d0a40382810202440c2001610318201680c0081280d440f600c640a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 948265188 1250 948263938 948263999
    0xf1612030f030209060301061107060302090d0b1816080d0c030c0212010f060f05150703020c10050906070605010503210412030c0204020c1c030606020d270906051504 73
    0x1402e8009001e068611508504080004a50a500300410300050200c550441e01200d540e220128282d1003000c44260300700480c68054000a2400342c4010b800c03400394030a000011003240d410130302d4044605008440c41aa40d1001c0101c00018001640310861924086c20010010385024040e0030100e40300078010b4420414490450f10300b94450391540a040300300784901981c8140c81c2003002e89034013426105040101040c040840c1071412210b0315036054001d001402e141d101004040225260000306000c800c02480c81c0d03c1d610750000b0309181d0700c10000099154140030030305207051403e0014540c0d1804000350002010035003000e5508564004290319101200c0c1c6c40c04548607408048000d4019002154002040fa4049694071025003003201c01c410315100005d044058503481d01c83c200168100d9039006070540d1140c00c80f4040341030810401c1c18554900d9904600c04041580501003855584c401030200d85040e2884031100c0440400c001e06141c1040054007100030300c442d001d06031496984 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 948266438 1250 948265188 948265217
    0x1205010c410903070303121425020a0b0709030618032102040b040905151c021309080a11070b0a02100f09050a05030406090b040e06010f02031b0f161203 67
    0x5045482c00720015040d1903207142ea80c680680b0002d030500210008030b0802c1504411041080e014034852525500c01f60300341203c41000018418060f603600045010b00323400e030404106c4640507a40500c00c150365640d40c5510f0b42c2060021078006006281e060203440c148940429070144554031030440c03a4940d49801801c40342003100a00c80d690100c802450003041c006280485a88914411000e10001014900942d81000210440d01c1c011340901c00207281c0300000350400e02c3c1c031000c0901c494a00050000166101c2c103e03d82c1001c2d03010b8000942500401100031800e1000b48014183d01411600304a50f01d54007a4036030490b515000cbc0050f60b41e00c42caa00d1900160007401a4a801c07005886800006040540d12507102c0d010301000b0402000c00011806082000c80f01103520240307038000b0301e84641d80110f520145602c80c0004510081c4144100c24440300f500740c52002c0c02500a088800b2810791040c10260744110006528038801001c0140c10348042c241522242d05103071607009642e40d107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 948267688 1250 948266438 948266567
    0x21080c03071e120f020c101b1a0609010503030d020304051204030b090c061629160207081c0e040b131e020901140703110d0809010f060305190501061205010c 69
    0xc0200232000c0321150721403c184014440f207840c0034162800aa00265103000606c03a814801f8031521b501580304000105107202142e026580091054041e9030140c0e440300030840098000c2d40083d1280c000ca482444401c0a0403c501450808182c1d10142085020340340242d240300624000307881c1c0e04c0c20700403003241d6003160501d00c1c20003032000340c0110103403c103d8024400303100c0f10140355016105000380480c105400003400f000e08082e80318009180806050700310307040a071000c0c10303e070481d44a0701900d90a54a440c01c4d44010700e9030310400181e1503861800c800105111900056010340304012030300e6940d0b84212254281003640050641e103021a10301107454444000c296807481c044c0d01610104594001d03a544e001c0c258002c02481550303aa449900704031041e602c4018415840040d01510031a000300e2a540f00d58010000040c01503520010203d4010154600701c60740c1e552050210a6541c0002c11500d08404100d2070005107000d00e010481062291b2240e12110149000300351640300d01c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 948268938 1250 948267688 948267707
    0x1023d0b03010c05130e090a1719030b0f06160f03020f030d05010312052106180901020703090f290d14040201030621080c03071e120f020c10 62
    0x1e4020840c3c1030036110001c056401009200c5182c035039065000075280c1c80e03100320902407845070b00640304085060359080d680c206900c21040d66444180712510130701010f801001502c12503501c0120343c1e184410208154800da080d1858802c40c024800c00d4242403c4844075284280d115041ca41c0b02d41850606078a4215102c3c400300a070300c80011081034140b116080181202d00c983c0014941455180b010b4038140215000007540c03060f00c60845280b0b8041c0c00c4400e82198000d041c2d02c642c014005e000c0c52036100c1c112040591a0340019010003010b90181a00e8000c151040341450712509003548036203110450365600702200d020480201d01040380303004481110302085070400079040c005d5020304a1050884040c2d02003460282c00007000681e0364526180002144440131300500c10340e9960205403c02f240c042c0540c4400d200e1000000e4400c103502c2e00303800324000603989c00b2049190464800500181127030411120389002c8040f250002621140d01404443c89106016103030400c503801c146 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 948270188 1250 948268938 948268961
    0x190903020a031202011103060904110a0f06020102130506070b010e0a0209060406080405121809180303010807090f0902061803152d04110d0c090504060b01023d 70
    0x307169000420000e10030910000c0c0840380d0002c2c0079041041d0045801e43c042265950f4012100314005000210144003440507448001c2509002948031202c0008811141c1c00180c0540e40c0040d03021188a40d40c519017000b85800c54040d45401e0090f03444081c004010b2160802c0340c07045501040f0312803450b8050b51540c081c0580b11645032651120b0080c8904000d07503003580e85008040d030b900b503040e0b60302045981f044030945000305050103820038051405001010030082d4120b964034020f81d000305000542c003e0009100404000d800d205000b0101c0fa80c140e4218082450700880c4401a1584000d6540c042003038010001d48035408008241480d10030002941c0c1c084030306041109000c0b14160085003102c2114420341c0d5407440240b0500304c91410340300906039200d10b0760020744625041c0c55800e45544180500001c16588a0714482a00c02c107440c11600d60341c0b5840005981d50f03040200c51401c92192011029800002c680090008202d9141c00800c03910241004c04446040e001290002c9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 948271438 1250 948270188 948270199
    0x40305030a12050f1b0901050909152701120f140619110306060c030c0115052b080c0705031204080706110c011209020d0c090c05070819090302 63
    0x80310040041c0360000b00418204201d1600b00450484642040c0142c4100a4018507040903c1700074400c010319044130040f0f030304200040180303002c140c035a6542c040c00344204045240c40d01d078030030302040341c5110040340305610f84030070800100100201020480c112829400391440700f00b00c6080c6004911100c11000c0d02c541c0310030006041600000910303910840e0381d0b50022010112403034015041d40c4a1000320b9134620014808180d003860450028104615071f48212031a003441001d0703050035607030007814000100c860708908000500384803150345400c500c4c41405071002100e10104d001044c414a20260a000d00480e200f07860a0f810041400a00701c014215200d80041c4051824260311074090300d2200e00030b0f584000b41f06806201820900b03450300b005000d000007941e00468880d40266a600400358803515200007503281c500c1500c400c01d0196104d40083c5080000440a4450a100300001c01000f0071148012980040c05c0d29011104019040181100d4401c210b8500c10550030295000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 948272688 1250 948271438 948271447
    0x504021f0207090e030f0418020702090c040905072d0201061d090705040902030d05070f06060e040201090f08151009020310030c14210a0b090f300307030204030503 72
    0x26400192102c1101c020190a2001203280c0030126160300a01800c1507441d0340902c424040b401d00b0908220300407980500040c200748260300010b5007844141c0d02120380c0100028144003018860003495400340c034030301704210b9940d624100500c00f0030010000805c0214a0640317104224400c0d004a8000e004140444005c940002c0440c90314038401c4d5074001f610b10030383c880010141014010b04000c44d0700117010340304840c85500f0580301503002d018201d40b40703604c0484c4540010754a1003150094200017a0340d03405440c040c8000740c4190b03a02d4001c11520011110f08029404000810031000383c2c0c5481d03c10100d4032061440d544501e040e401c00d840c101c0c004010000e0b00c030a00784c42034044038003c1c0390820049a41c3c4040481d03802d02d00302e5058000d030027903421401c44c09602d803041c800a0749100c11a501280f05844083c0c1181007600d050300541c1044c00802e80410003000484607000d003110100381400804840031000b0a40801508540b00011000a060a020b541075800841d08402940d07502c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 948273938 1250 948272688 948272749
    0x6200c0d09120314180306070e090a0e03030a09032604031d0102030f1b0105040803061203030f0f0603120f07150b2b0219150c0b04020103050402 64
    0x450030558042800034010110005600ea0440001600079426481d000c02c44d02d65014641c2c09540250f05030102c54030701121039036481c0c40030070040e44903444580e1400d00884070501040f144210103442803040508000140c404410040304581d048132540400107a0300f11b192401369000c5542146200301c8003290240d50440c640c0304002540b02d140b0a50350403040620f0800204030003900031400900580c0144540281038601400a20a20400801514000c01c142019a0070b650702110212100c40e00403040c00b03410b0510468000035510100083e500b107160000c01104007541c020225150081c01c000454825102403015100c031011559265a8402d0f5503550b4510ba940700003000c6480350f110303400202e1216440d2080004200d8001c0c84654603d01180b4082c082510b50f0040d040c9c2c24212204c5007005a960301c1c44e41e004080e02d80e2000e141240342c25608001c4c03a05807103822007808244c100060008288a55907584079509003000181d540300c50001c40c080c40c030074507000c0b15509050000e6102 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 948275188 1250 948273938 948273943
    0x100207090209182a0324041b1d0d03050702091312021b0405010602030d0f02130f050a050303042601090602030a09050c0f0a090e030f040303090807050a0b0706200c 72
    0xf108130905000d1030356581c0d24000300310144030445a000355a030303962100c1007408616051010045000804c003007528a0030400e002c0030400c010009401069038922245d407a01282000c00380c03940021650448035141c80d40f8054082c1c824420000c0c8a190702000084202464140c100036980c1c1100c0b030745a110b01000806581d40400c45803032000700c640e05040120529003800f07001e040e6005907001e507052000070106840500f4050068003807180c0c080c000350380c0c1080702c00110001400d09000343c44885d40f80406100c00e240d51500010300980003044180844c2c9004004200c00582d0282050240700b10010014018011128020040342c000001d00540b0f40e01a04841d44480c018001e4604400303ca000b0000b04c4000c0c0c00c07a1a8100000010812125480303074802203d0300c149200780d92034400d011001000980c8190403c03400300b01c0300507051141e04000c1010b0300282c101503d102c1040c904042040c01d40b80160768006000d6911454601814056011203641103000181c807d910f842c400f00c00c0a4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 948276438 1250 948275188 948275221
    0x70501271103031303021002070504050c04031a06100507050307080307050d1d061501030603020310062105100f02070609230a0f060c050408100203100510020709020918 74
    0xc41d41248900501d51620700031046428018038000146445440d660901ca08005801d4126096004041d00054240c0315802810b10030b03080040c800355210708602d0862340e15003105410060320f081d26001c0100f02c0c2c0b00d14a8003030600d1043e0910030b4844002e07181c1035180d40b00c1c1c50343c01014140040144400d407500140a0701800d1451242403260040381e6140484400001220507200d5012101050124501c3c1e006c40140c0e00041c94081102c0c1d4076038010038908445101c1d48005140c4d121030410801850181074050000700d00a00001e0100e107817038440e40c599401c120303055500d503038103130010442496034100e651a652000083c0f004054034227280d10704042900312180000c0040b22011910f103004541c9005482d40711030b0803c1c0d0418940c4840b80140b60315660001031140420020508400411504100f10702808001d0380d280341c030140720380d003840d400c3e400346001d121242c000d41071440d004202401612528000180c039110360100280d00d42c0000342038565002040000e11034511812401d21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 948277688 1250 948276438 948276443
    0x11190b0a080103200915181503010501080f1c0e030a0501090201081e010e132f0d0221011d0f0d0e1008060f061812012007050127 57
    0x15580c13401c5155401a43c42c0f13205006544050f16000140349081c0c2c04080000292000d007d210340309640c40701140e011001aa07000030b074040440c0442281d03103024080c01d800b41c00d02001802a2155070480c4a55a00f81001d13140c59000201c007110490521407030f101c1042510040c1190081082c6090442c000c06039800141c3c00240000000b400741c81e01c4460614000c42104c4188840742c1ca49580c040b40290060000d41e80c08811072919000304001c10b00084920b41090b1601310400124106100850800200c0318020058180e0708000f603500c0d041c401c1902000e008150208076000c9814600500c640b0700c0d07041d104003200501011001c40040e081c2010440e203421640400c80445043d160020304410f40707984440410b10070384505125141139504013902800805c8003080c2d013800213505070408140101d200c4120301980505141c0459002d0240c0e850708020001e1001d4440c42d21440055001c0200c2c502c0700c006861420040c0075407100707050314010180c1540802451106540308007101909 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 948278938 1250 948277688 948277703
    0x3030e1c0312052503090204020c0a08030109050f060618190b04180905072c0103060504020918100e032709090d080105010f050c07080304051c11190b0a080103 70
    0x90104d0b006603c0125000901d0008480e020000041100030f0b040342c0700126089502442845004501040400100e81c4a446956240d6040912400807140010944103040c0310404c14020a626410201ca81e0504444240b500c604030940104200700541040c86011241ea03c0001a001c3d084601400564401030340032480007154244d101c080d6a0382107800f510799081036804000c40c0517100c04103421001d0311520110131001952400c4002c280c01d92059a2054890b002c01c0308526041081c260f08c402c005030001820340c2c5206c3c890b80e4400d094000c00403080c0c0c0c4e500060840c4041002998800213054144111640340002d40e0300704074050408070b5015184d50408102d13441c01c0824410301240c0c2c1030b40c81c4c0710b00e686004011250482040306400500604114403169108144041c1d00900003010095503074918110602441c0481101c0140740044d411500d000001d800c5e400b9443c1d0341c1c004a90800c0c0a1903952607080103440c041d03008070070000c80051040e0300640c0001e1164126405100c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 948280188 1250 948278938 948278941
    0x12091403030a0e0a150e28030e040c08190b0d06091208010b1806090402131e0f0b031b0c0604050c0108070f030c0905150702040e0f0703030e1c031205 66
    0x560079a240201500104100c40d080c8112554241c6603000101e021b41d01012629640c4445c8000c1700080b12614054984075400701c103950505400030700400c603040d0241c80c20800281c1c000700003040ca01c8041d00581703c2c100d00141c0c01d060390f45c56810088600e1401130042d02d000c0d0541c03404200070039003100300310b40140d100d500c0000202e02407400c1c2c2c0e048500c5107041c50301e0551041500c0009025501c4071030340c480400c1c840441c107070300c5a02c05454000400206080c4c418200b0f2000d01c040300b542c00304031920b088213007014462030300130704003020403201c0c034800b40b545035142c0d155040c020442841e50b10341c40000104480ca184400004c500e800b860040c01030f141902484001114401011508900424002d40500c691507100e640000030751410341ca400c8155070b8684001450b603802d603c000940f080c00c0030540105603c7d081c401c09150418003402810314a100d000301035200c941d1403002a0512481811191071901d40c1c100b080905404400511014009450040d10601c0116401d1203040e01d03200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 948281438 1250 948280188 948280211
    0x90b1b071e1422091b060203030a0f0b0114070c0e0c0424050a081b0c030a09150207210501090c061b0314070c1a07200904020112091403030a 62
    0x400040c0300360b111a01020707002100d81090090034248100701c403400342d1078001c04900b010546602c401b0b400d00380d000e550760f4180700071074406982101c0501d0140c21f203082c04403a0b03281e804c05210540511883c0dc000c0e211502410418400d180503808916580380303102c200050f10007401c0041085d02d040b90126000f880586291060900c086907a080c00305a003084020000c6004803521984851580112100541c07150082036040c0c00c80d483c0480d680c0d00200b455018542c00c000140d01811a1015030508040c82a40c002e43e600414400e4132034101e4100c2c0c0d481c68940c1c7c45904208825004402840942954076016015005512501001500410100d402211051020450b50341c140c1d440b080080d4810000d07401c4ca5000c420100c891401e00e10000031101e9160054803152401c03101c0311921003060b1f05000c00e0b00c1c0846030041002c4410042310f040c41d41d407051000340d041902840e00c400c3d01b82440d82c0800c0203000d200400740144584010b80c1c03101d050004001c42c4518030710b00061107079042a6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 948282688 1250 948281438 948281449
    0x30040f031404061d2403150d0c06030e0a082d13060503130f050106030b01080303010b0f1812060a0b03010e0304090506040209100903030f090b1b071e14 67
    0x307028200c0010b6010401070041c00c652542d501c80e00c040180f1401003100802d0341c2c00d0058880c0307400c41707201800110400c404072012117801000e02500790b40519084116035a54985c881407030003098240756441c007010400744400c000149542da0302c0120240d50341c600d40149203048044100d04010303d60242c40b4802c8a403c494151200b0340d040d0070350b186410f4103210050350035410041ca8041589501c01101d0b001c01e11380c0d80c802d004640100c000151890860421503503104050b0044c88080d8020001000300d40e0300b81c000c9801c03110601200c02e0300c8450340c0807858100c000301000560b02924001d50642c000038007180c0f42d4011100084200a40080d030340a1500380c499000301074400750000c0c0401c200c8110307190462940401c1c0100014640981030001903105180d0724425400100d5080b418800c02d030304040f00c0c7c00e4401550a04032030803441c18003403c400f80300d000080e4520034880004018121000c1102c50080c00d90401e036201c40201c00c9000300550400d42c8589006000207101c000c0190811 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 948283938 1250 948282688 948282697
    0x61203121b0203070f030219060221060a170304090c1101150602210708121503060609072d03020c10020a0921021e040c031130040f0314 60
    0x1d0760043c43c1091102c0d1102c400081c1001400d40c294001d68503882c1030415000c20005509204030001a1182c0340100039698110030f40700c071501003c11802c1402200d83c0c50b141d0807400c40d1a805150b050140314140a2400c1d401a130b40203e001d5070130407009904440d04001e4880c0f0022641000704210303400e1410b00c0d044d241441c40b0b11009608110b0380300450030b51084459074a0090440300038500303800303582c0d09403095110026504002d04500140011901c20800b48950008210300500c2c81c0e0400400040f21441701030483c01c180110032110b00070a0b20b24030303602c41c92204c00c00702e20031200001040140c084d5000048001035400780e0100746084075030720300c00c0d20440303c00750762841e041e5030414801140741110201000c1034004216401c0c00169140c80340d00500540c8c001c814548080d00d0700600c0181d40300c1c0d07403c1030b0905045c1071030070015802c00002c0d1104180740154010165505a8070104003d10b2904c0c0601c207400c030842004140038142c0b01c800c070054802d544024120320904091072403400f8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 948285188 1250 948283938 948283991
    0x120314090a030f050a09120c0509010914060d05011409010b0f010503011401081e04060b0103061211011b05070b0712110303041205040503060f0105040605010f0e060d06120312 77
    0x24803c2c038a1500703610520240c10b0801c16400c00065080d21030103440c0d06c4550513501119120492074050110381403510100b4014000c0103c240a80d00481009031207004008203164060a9040c06400500509400c801051440040003a0340f90420b81880c90181c0030340c4420314013425003111401003a5101d002140d040340d03500001000c0600c1b12000449a0100180a9241e80d98401050904c00603080f01d003240254480c040000d07203000c9400026055402d580d008803503003022203804002003000740d41c4200ea03845003464003000a200650800381c0840850728060b040f4030511502040e2940c61900803d031803401051201c10020b141d5000710b40503540020b404205410610124001071000c1e5217907070740d02c80c840c14982e040580b42d6000c2481c1c18422a80000d04052000c0100304030300700b42c41408007034042071a00800d039a515440150114015040d418020307240041c0300b8145860381c0c1c1c0b1110182c00c042c100b000e42d9007072500300105030f42e000840b4104250304c0c1080454210b4030515001d0f40300311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 948286438 1250 948285188 948285197
    0x6070203090d06051005150a0221070609080d0f0b03011506020712030528030f020a0e150409060b0c070602060f0a050415180b0a14180a120314090a03 66
    0xc40b5580300c80103010080c03c0500b41c00409480130030265500c1488162a402403100705443e005502c000a2411240c030742c11510400b12140028121150042101c0e6080d40001000c50502007501d805800ba100303484540039654900341000300226545c4c1c000311880d1400318001d0100888460114100c2d0a50b032040c1c00240c1c0c8900340c01c006048903008a031a40c64024201181010043e00900c10012a9021a55580b102040441da402072305071095015940c00c40f10218205528a64090054802250740078825001840c104092070400c0003203e015020a55003030201e0b5545080c102d00580015241d64030300d00410301c0100c4c0c054400100c1a105511207224001151070344002078000b00740250090358200c0c20810048803003105070250141090103400b0f0491106424182141c100c0e07405403005000380d09148640100681c42407034241c001034610740580c10f26002207101e621301803203804000c1049030443d94819195815500106003010040c0d0a10b480750b59269406454022843c00100800c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 948287688 1250 948286438 948286459
    0xe0f010b040b45011805010303020309010c0c0504020f0a080f0906181608030d1401051f261017150717131b06050412031b0b0601020607020309 63
    0x464110360501ca856241c0901e00d14500103540111801c502c800b0058084948003004100120f01e4030b8645503e001031781c0302000300d941160390094681c81000a21410415200010000d00c202d10b038421000389070041c421555244030780c0003014242c000d019454080703981140019103034180c90721140e200e8420b140c05044540e80d00aa00e200440501084150510500e148252590000800c020180030f41c0303c015034551040000c03000580b100d100003800c0120b0007030010007907900c5100310729282c0340c0024000c5552180180c0c04035101d40711480b4000c4001c9002c001c0040c601c440c4004140180c0809d549017a016443d1f0150342a414503d000c1174859900c040c00c030101c41e11429031299040155490b019040d200e0031010604c00b16425209140001418144103003040607105401d990041d664a446050b1380c5000000b42c0603000350f10520782c0c14043c1d0818801010b02c02c6078800c810311401400c0c1042c00069040c218450f48085800341c2c0548244804903000038000801e8440e2020001e0a002e0f18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 948288938 1250 948287688 948287719
    0x40509010806390d1b090521060105130905160f090c0f2307150c080108070b03070509151c062709120c061b0c080307120e0f010b040b 59
    0x10f075441516204407060350785200160a40c110302c0441c12541d240e50f9007602e11030510041101070355108600304201d00201d80c050040100202e50503044680c1241c411055100c0a00c145001d49606d10300180701e80514040418041d00703040c004000d0380c0c5088101e004081c0c0f51078419040313130350b046042004500c060b580300c00903078802c202085011030046e0703416003240e240d401d68510b203810004080b0f400c080441c00003803078201b8034441c0e40c072100305a26004a46514190304151075902e207008450340948000001155280544110b844a20000d840301c10310345403075240c5540711f80108180801040c5400314005881606010754000c5e10300012141c0c1a5140b5608241d420180004607480c0c0d09854418080200b040410926810004c0740c076504040500c44c50074400722a805080d1164074459032159068060b8009202020590720000403035903611500c00503140c02d101d0b40030341e0403c1c41c10401c200c034000304d020640b03600c100020002448242d040070108415200001541da0304892400600c038003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 948290188 1250 948288938 948289051
    0xf1106101202030705120c0906060703053001170d02010c141b190c0f24020a0c27020918060d1a040b160807030c05040509010806 57
    0x50300d6100030104c0f1801955074020525400012409002a4006524100403401d01c02c010707030f9000f20f00b21840e038a005255a0003915038041e50704011043c09000306000810005104281036000e02c0041186207582d46820361a103041c1c0b000c0e1041014000d00e040200c6041c01401481521030780d5440d0b14240e410386018602c0a504008006008241e925003400101c00040c0038020188003420720016800101d41081d41c1840481d40c400020820301c0d0034100300f508010402464200c84c0307803032030301480308001030102c0ca07041203240090440740c91500c0000e240240311a08100d0401942c14600c0d6a400300d207040002c03801010750140d04880384620140001e00b201c19030591040005045420004964541c08401a06030348001d000d02020002e0105204074030f640b480e0310200b600d843c04050303418040d0050414034060721f0401490b40b60035103140c10303d010340159405400003510f1405203680d6040d02c0703561620103548203989510040380d542c141003007600034202c005181d8040c030501180708060001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 948291438 1250 948290188 948290219
    0x6090601150c08030f012d051e060c0c0a0602070503100c020f1b0a0b030106050706150b0a05040905010e1e0a02090d030e0102120903100905010b060a0f110610 70
    0x107040114210494000400f10f40103180a08212045d0071041d6050042c5100c0500f0b80300c2030118a018800c980640d8240009800c800359801034138a00c0846400c06003072060702d52035120040d44540301003040c604201c000513250380c6a0504540002e02669106010390300c4c0c43c12401001c2c0c041d000304000d140c03501800c4d00101410f650030310441d2004100400c22504054000d824881402004040e00040707291010103000504200d80066245503d0f20744050590f200d1050000d00301c40e12800c808282b00d210710308090082003030034406540c0349104400140941e00c1800b4274400c092500700007140814204003418807600c0030324019660b0b03103100b00d058000c101000781000d4415808200700d020b2504c5d5010001e603454869207030701c81d00d030740854006410051503690201800c1414481c003281c41e0760025504c1d000d0045194002040009418202d016200b008441d0703401000004001d104258002411008601c00d5541d480295806c00386194030b54400784c41403410302004440a0012103011020751 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 948292688 1250 948291438 948291479
    0x5090906060712080109050703051333060806100b0726040909110409030e010f17010f05100804051506121b030d0c050318010c1e03030e06090601 64
    0x60304215070303603496505031511190f842002034094001001b80c8078250250607040b40c1e03281410700c003d04d03004074100c0d0401d0364030344054200344050b0701105440c080920a141c5481d452036090281340104004c10700a003c181c80b880f403840c4510f4001071030b101c04442840e0160341d0701904031850700c031664a03502081d004501162a40c440c40d54410101c000114004000600c0020804604200c90741015140c0c0c0c005106110700460820b02e5500c00658840111113500c4400d0810809190403003004a89450b0030290f1401038600090000c81c48080524640c8125030b0f04440120384000d8031102114001b406980007031032503112880102028000c0c8035800c0e44030340d001e03140349180c40800440c1403500c2c942d00102c2c1d511001e40b05505c00e10342810b101c2215034801c28100101d09851547d0380ea0390320700ca80f0906040149440f0402c0a00b2fa2281c08560107a0360403550560304803241c00d810490009040c241100402e1810a250f16075030303c0801c480e40b01d02540e40242100da0b203044000c440200c4441d07490f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 948293938 1250 948292688 948292699
    0x9051302040e1f0c08061002250513060918031202091302070609020f06070c0b09040b0d0302010c0f08010302091311060c06060f0306010315020c1e160b0a05090906 72
    0x1118151820340b020844014524404074812130407403000b0344501005040b0078091001100000074444c0c002800ca514200c08040744c1d5880360b00e0100d401e801094075041a40d001c5052088243c8400712500004291504903204100c0741441c090f9880b080d00d065000240821a15005880005c1d0142c1c0070f8501c1da000070f0903282c0720014442d01e41c0c0480e4002441200d0003076550b0b040b1425414001000741e450001034842d14900005500c0c0d000d104151441101d615200c0017510440549964000c54500180074102101101c41403070081d0182c01001e200c4400550500c400003441c1e8481c00a05048079006001d981c401d4441030000d88104007411420340c0c05103000c581200312078803040002c12405000c2070240c5120708101d004c208074801c044941c0c500c40e9000300c005201161400c000948240c4103034000503030340c1138426251400c1c00c0007440c1036082c0c690072038403502c1c10380030201d00c03035000e103415071240881103407141d825030305601a40641e078000601c24885840c241c10211500741d00500e00810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 948295188 1250 948293938 948293953
    0x8070e01020c041e0e01020406121d03030702030a0210060b0a030c23070506010e040506160207050303070602030109050601170c07080d06060c050d0207121e06050c03070909051302040e 81
    0x3c2401d880c3c0c00b41c843e66a81d8510804002d07001042d100b00760030080400c000350318292402c04010181300000814a003010f5079244404048070040b50036130808505441030f01d40700c0c034040001035207076084000c0c07000c05401401e05100c642d11840c49a2801d498400743e5850405203032207403c4004100800c008400d0001e0b0040d044a1072810724000030742c0c200d8250340ca075610803c51429504020b410790000c000d8038400c1c0f041c00001000820010307400081416020724200101000700e241c006503500032609030000041d54400e000d002d4004505031500c06d401440161034100046805950741516400d4000c4003902140c00e82c000300c4014032409010f1311101c0c1c1494100d042000841d03c05034440e00100d040402501d00b004403c0c8020860038200340040c24286240c640364440300744800f18002e00c1d10320241d400320490601e140b148404690815010441071406182d1104180d20603503ca1001c50080d4030009801c6c1000e001c2c9503c203001020741220200096800d001c094007000c02d64510b103018200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 948296438 1250 948295188 948295213
    0x9090b01051603031e021c050f1824010e0f0615180a08010e2103010501080a020d0f0504111215150303030403080a0f060302030a03080405030405030d092408070e0102 73
    0xa445c202d001d10029401690b8080c5611a074405000c6200100b001c182044100120000028612a4040b140d0352a120600d80c1c43c4480303a04046440c450450001049504c1030500c0d400518120b0503501c101b46498255203a0b680d1500454004440b0282d00030900da070400c0d02c002d00000a000b02481e01c0a840c03c1c145100c07400114074900d039800a4009030754503810a000321100300700e0342904001e1404404070800703107550703061450b04c01401024103214020b404070700003040c143d0450b45000900c44c810080c0c08500c02c00700000c1d1409440c1a40e003031581160111052400d031101c4908911000000c09805007940000e07286108003c0940004905c52900e50000351010f2008500c100d11980d00d64591386046003a0108031466186041a411b1501c2c509100680780041c0c034010b0709405003000a040c2e900c92808500d1881a600165014001c16150a50103a04001444140c82802e03000c0c0ca0000c003800c0301e1032000004102c00000203089440410b100d64001d000320039000c0c1d01071041d00d04003903021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 948297688 1250 948296438 948296471
    0x6031b120a051f0e030a080702030702130b0102060a0b030322050904030f08011202010c113f0105060d0f06060b0a200a03121a0a030b060109090b0105160303 69
    0x440c000d03100c6400020449083c103030280c1a03081c9080510300c0410054640e40d41140d500d000e004102400c1c0a07810006c201c01d68020800d0b9001503500030019454084103000740030180c041000c0e182c1c003500c03613400841d80d4176101d405201388090000e001141003041c600040d032004002e40c3c04142c020415040d01040c942c80c2c030071400d0b220b94002d8441c4100d00680500040480313505a2110442c05102c0c2041c00c0181e078068a02c003040d603004100b403000c0b58555400a10784c0d400740c468507160140141d80300c0055640010141c0d001e850220443c80344102c04068642c243c900403110b2a170320868008021000403d07803142908014052400080d900b525035a40c204941e00092107040400c8104540320700b141442c0314000c414040c14405428204c000350b43c0603169140080082d49229250310080f0304c26150555403e0510100500a154680d40c3c0c0c20940102041030724618006038401002003007011080c011501d0f10756041e51303454a001075030300070f400c4500e80e1400c00f00c0406480381c1041c10b26043c803 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 948298938 1250 948297688 948297703
    0x10614071a0f01060f0c170a12061e05061608031b04030308010f1203080105040e011512020f030706020a060207020f043306020a0f020f060d050406050c0306031b12 72
    0x1c1c418400c2c8950405002405098400c00c507482003114404034000021210000d13402e440107030982040d01c0d02e684d12002d032680c02d2a200100c0890f86420800608030041800304181000c200c091403180c981c0300c0b0203201d1280b080c0503800000c840e0903000d010008036030100465020891640400e04462400c800c401d00717a0169000350002026800180010851210b401c401000204039814281c01c05943c0a00010014850b45200c3d5940d800105045d070802e41004030145100da00b45a811501c1d545c142300ca000048506a02401c0244c00c090032a050000e285c4042d034555030010b00082c6501e82d10f1001170362202004a030807004010559005413650300400c91017044403003d03030b00c8070321810440500028000c02c1c1ea150070700030024100300e8940c000c124010000c3d000049000351800d240041540c155080c0400342c1c00010000300c4060700030741c1d070b4052800346220340024801a1541c00c0c1c5000140401e8669540c950001e00d805030403d0b0391b0030711215400700040c4c10103018600390415142003c55 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 948300188 1250 948298938 948298951
    0x41106040b04182f130303091a04060c0b10050406080604021e0d0323030702100b060708121f0b180307080a02120309040f020403050c09010614071a 65
    0x201103424040035032001083e48246100d8001044100c6071200072844420081c002204c3d00d803c0f00e0807142418221508130b681d0411000308842e4440d65030700d00100036001038803801403000e80074076503810b001040308100c900319045035440c9055103a240d1503003002840e020300b4001c01001c803228001015103640c000c004c010400700000c1e00c0140b07094010b2210406c28010f903808104003402860880d640c640c00f07041c0070541c040c90118000e0207041c442c20f807a44902c0084440001c00030007040141c41d8006011002214034203800e120301300d046828440c143c010110000c0c40c4003401c2c0082810a1000c207032940d8440d9044100b99040d940201d01c001040c2000d81103400f2030100080d040c0e40520704071b40d503099000f60660080c42a01e1411007002d484086050001b440f9200030480195106403c109849143c1d8000b0000c0010a00d4080408000d600c9440220342d60300800724410001d180c41600e2504980094071130061070b425003168800143d111401c1114001220014114040e8400060510414 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 948301438 1250 948300188 948300209
    0x203220815070f0e09070c030302071e1e08040b031e0c1e0310061407140d1d010801090f0e01050f010306110307141e0c0106030b060a1d04110604 64
    0x1d01482c014528034050300e00c0340a0007040c403103800d0301d52110842190300030f1840ca040c200102c4582350440181c0318000c800342588040940050035155101c3c80110700e10302c01c2c6080b02e2034040c00c03d0f07007102100c01040060000301e4180700401003456000f00a59018880750b01501c800c0011810604a080c1c0030307110100210300100720011441244001007461617080b403000303820340c50020008800c218450241c0820820407151500034044480c0030717120619403021100300d010482c2560183d0310a5051a00e03400500302002542c61448482d00e001040441030b550016140c1c01d241d45080608504024070040715983e0100034021542803240398000c0004901480f0a945541092002d41d01c400310010041c500c104140820f194100c481c51540085504140d5120211850844903c3c943c100b410400c90000007003c0150b040c0641c0904180c1c1d102e044020825101d0b40288030080d80310b40501e0b003001c030000c14080d03090144041c1803507100d84a80c172500b807404a0100412041e400031fa21042021 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 948302688 1250 948301438 948301441
    0x2a07050f010501120506061309020d080a14160f02031002040b0315010f1220030103031214100603020c010b21010612021c0204090506090d0809030403030203220815 72
    0x80c820700606005008080b00194405000e841c0c240d180d24010b42110b1151640c1601e401d0019640e4000176034241e0010305d41c140002007404e2101c429800710252000040c000c0c00007009025001007a50750600c00182c3c03c030080f13409507841402998403400d00fa82c3c144100707291421100041d000502c081c0a40c3c17004152641052104103c40103080c1120768103018250070040e8905038044106800c1100000001c95402060804410403042101d103107200034600200203c02d240d080000190f215004a20400180390050a0b03428844c0c015540004000218101046458030a0b0081c00c80790442000000d88490f02c0c0700080c0c00070540a58075010f0764007039501d60150300b40c288a89070081c84000c1da00231101d112980001e4503e03010b00540c1c0514690b0400000664640350701150485a00400311a41401c00d01112a40c90802512100020b01e460f800540f6030300011081c1c0702100d5150f002142032542c005840c20088655914041e0720614004001900b090100710940402c804482c420105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 948303938 1250 948302688 948302713
    0x6130c09030309151b1e0305030105130605010e15090406031211030309030417031306050d0b0a0b07351b0123130b1e0f0f2a0705 57
    0x81040d42d40c043c045130201002c10b819002d4010300100c0064085201054401c0002c1c40d110110300907030a08440d03445840b0b00c00c031040580050046040c3c0750101c580c40e14446d0140101b40a03144c3c0b0340030700c5001039050100c0c0340c1607040c0b40303800e20f4000d4a01d000c41410210301d500811b003111880d600680c0c84114071508203d00c542c0103207000035000740c080091881d41c5401c4a20b20b80d40d1040e032003644110100700d801d95400010920541d40944080100a00300a40c0c0d00001031054004d494032490883c030340405c0801d24908080200122101509203909188141d2100701921240c001c12104020401132101070034508541074041e0700706090412502d07210582c8911484071a0311907802c849070f1400b1108500d010388090446070403400c21342c881c1c0c803966501344407440c00c4010360001081c0c004d5003418410024900d80c00d075404d10f00b03284143c40c072540c0c0d0307088606082c04049e01c1018502121001103118502181481d03108214031003000543c040030b088081650368441c3c038080e5029081000384230710 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 948305188 1250 948303938 948303947
    0x121c0e010509120a17180d03120c030e07050d0507030b100e09030d0f050903030a0f1512021311030406110702090403080405010c0e060d0e0a1707060507081306020306130c090303 78
    0x54042d100c209a9080c480c0812000c43d60012206e0403d02c901910f5440104051141090040701522003000388100b0000d5000034026003540750100c9064000d00300c0c0400d02e400c0800400b124a50888000c1038210b03d10340740c0c0c103500358001d404a2444c050103c404600e0540e039036070460280c2c2e040c1009568450a0140140480720141e4840207035606003418025561800006c0c1c0341c000c0ba015000107290048005244020421520004020341c5400710009441100c00244100d10307000b650040240d40086e03185400b1101307404100001c80c0002e0012902041103a030180c441c492641030000d1508010b44c000820b8064120f03000c400141340181040100282805038010907901414031308814620180000c941c0c0c020708a94400b066522503181240381010000344030150742040c600d0b805280303005400c1400354010b0400b5100c00d801d02010a02c410b1003200040d2007101c44040140c0d4040305542e46401070b500260800c0da1150060b501c01208101c11300c5803284000158654003580d80c0303989009003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 948306438 1250 948305188 948305213
    0x4090c09170601061d0409050105010f08100204060f1b02040911120609030315031e030a0f0804050307060203040620130b090619050c0f0c121c0e010509120a 69
    0x16642c12600c0100800d03074004080b44020000701c02461403805071400410003c1580c04c0002e46198286000011440306540183c8181c9140205503254850001a060306920980c400d00300001c03940c401760000148142c0c83d924032074042589480c2e850a45400180075a030f04504291909100e10b01c4000300c0d403601e0150510840c050390054145071074110503054482c0801080309031006101d0200301040d9405010a8100a080b424054848011498401d503a03412404850307010464146020b08898004c40410f48619400f41c000d5150010550f202400387d00040d1044a03401d4841014004260050038440301d99a0755000b00c036241d0071a5240160501055404441c0558040040c41c1c1c036900e071b5508592403200c1611107034000c40c0e40c0801c00c4a0f2403282c802002d01c940109803614107500b00229008030003180c1120003040c401c00081506407620740070680000d03110030440306d40c0b801500a41c4214280101410010308052082000c56030340c07582070702d20443ca5005200c060023008903002220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 948307688 1250 948306438 948306479
    0xc08010218040b040c0c031206170a050c09010312030c1101180c140a0302060306120f0a1b0e1f1701090501200417190b0603120a170a0204090c09 64
    0xe01c40d1017044200035151071000d100140401001c41c0c0d90b66451f0103a43c00c82c80080c194420303424104140b80700c51589904072128103e501d8080c0ca40740100f82d141401c1080e06803500a2080701103ca88008180c00809030002041c0920a8011611500c25000c1c818002c9107002c0c400341c24007460a503d071000680d1030a4208504884900c483c000300d585891000340e00707403076042c2c0f105507480e1501000210300080c1700c0d142c00d5851083c1030034a8101400843d0004250784036042d0404840500c0721240001034003401082c0c2c0701103a00d000202c0443c000111000a00443c0d00c03a4003080e0780303400500000c00d814640d01c80a81e0b4494010783c0410109120741000c5181000c052882c450031511141c645200350321404a0154211604404019081c011101c0c108184441002c05840d9854a1036610204946440c428001d000c2810010702f203800440b0b040040940e140303d45507030b084551010701240580307451810f42d400d2102094030520351080d16042c0c07406450b000390151516040d1200908030300e040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 948308938 1250 948307688 948307691
    0xc050f070b0904020c0a0206040b04030b01050607030e130912050703080a0b030d11070e130204050601110606010c0c030645080901170a0f290108040c08010218040b04 73
    0x8201e01a01041a906601c20490700540e541105a0106140c012262000795004a0004001501e011003500600481344a980b800d41244c1c3e0341e00030401c071401000000740c0440c801c541400d500e881c0900031180c600200703410010f2110450303202c0039200c85d0301b1000200400d40000d01001419088801c490744410702c0c000c2030080c90601000b0a48903541d812520703043c03180a0526003005035050260034041c00200d4045813080c0f42040381e03404290a10070042e40114a4080403618030352007a141d031550301d0742180003022203484010045880300f11444050301c110342c1c185004030020300540100703081c100359503004132940c000e00f500c44003d0710300d49098581c5a80c00301308900103100c1b104042c502c54680101c0050749882100c80141c4000c00303000a00c442c4040e90a04108545002e94408813100d01c0034032040041290b02c2c0c1440225515519110342c1142c52290180000c1d0b10134560558024840c188203070350607940300c0140342039030001201984490700d02c002d03030351050400f44511500c0310740c1102c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 948310188 1250 948308938 948308953
    0x60f1503050a030503180105130b010e040b0c0c01270204051806071b0212011b030207111c0b01120308061e040c05040503120304060e1501090213090504030c050f 71
    0x101c855039448090001018008007100080211010040b0840c0302d5094070000c1c0102d00d0301e01442034030881c5443c811284002403100214100d001140b01034822988200d522229450348001c18500750420700d9014030780c0d0b490310102d000445035600040e0081c076801001107540425481000183c0f10002c1c10750724260720102010485520020706070350401038a05000b082400b0a04062950000004000e0f40064400b4110a5070704815800088034107054004080d500410300c000710164071907188041c5c507206128038030b908545000081600001d48203026441401c0440d614950910b009030302c40010304110103220030605403c48910745e48017034201ca650b00503070501d4200300f6a00c2580500c4900580da40c0400840e994001d100702c03806444000c00300c0700f90030020190420213920844e0111806030405000d0401c0300000644100703214030445181d403050782810213080081d04040d505030f01c2828501400200303a00d191041a0045000395100c84600b500740c100ba500d04008514071301d680354450311 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 948311438 1250 948310188 948310193
    0x607030209100507061107030c0c0e100b0904020918070e18071b150b0102070b04141c0618110307030b1602030415020c12030c0a08071e060f1503 64
    0x28000d40c9402c00c900300592a04000e0401c8001000c000311440a020b0303000070b180d030502d600991586a075503c581083c1002d00c1d1210140c0103125016280311040c081202c40c280180318046019184000740640014101128240002d007401030084034040c0c441d54041c103004201e0350215880034583da05407941c900303085d81d481c1a47d4040a000b40041c0802c09a403003e03003030101503520401c91080d0404014180c411020b01d01c3e00081004401950143c41946000145001d10000340c030304440c0168110501260107100303000280388216210007403102824040b400040e018820f100340c070040002d10000300581031030407500c1c0d4a1500341e02c82c4070350711a0ba4200001100d00c4500307540004d109280c0f0300c2c05020b16030161326600864100d460f181120b803610948899000862240306c4108507001c2c54400c60281045e6240d01c9000f54074143ca8101050322070108161074000c1180038450300c5450010a0038042c0003240c0301c051407045a07110b4443c0741036190001e403809048000328800390740b100a2851075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 948312688 1250 948311438 948311449
    0x2a0f1902060c03060d1119090b030a0b0406020f040b04090c141303020f040f02041e0f080c010c083001090e0715030e0601060e090a0b010c110609130501080607030209 73
    0x205040c0c4070302d171100c406a0812080710b8440d0034410001c0e1101004030305100086000c029540900c0c04840c0c604040001c0301d00d0005414035455800080d00c501685803500e882010350303c690109004c40604010000746209898000c100920780b0381800100c1109015004040003030314a0030701e031040e000340001d0701e82c890234609180849604031152161000098040760107880d00600c9008203a1010600190215443c0410108102c41c1c84807034000744d441d9000c155038400326011b0412030380d1004018580d20350043c1048681c190150340d1341c0341840310b8446e101c00c208040708114049946000d1441050204c004456805855502e01c00c0c0f000108402500c0d035200590720445c080401c5c8420440e100c180641d10951454111000707131401d568440320040c00700c0d441e100409014409100000d50303158203610030a2864003050b580c1500741100b68454103000c5074644400c40e402031040040080e542e65160722024460007514004c03035158504080c0904043c8000e240200340b5004100d0900d803a940d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 948313938 1250 948312688 948312691
    0xb03150f1f1b110f0f150306031c0210150b07060b01022802010c0c03330c0f050702031006060f090e06093714070f02062a0f1902060c03 60
    0x90744c039210754030b40000000d030213030805c9039002d0b4000903005518146030040b0001980f190a080e01150b45000e1035081403941383d60880b035084016007007130440e40d042d6829500300800c2e0000d0300032081d20b215154201d25107280d000034000c841c0c0aa68070822002560103005418004020704014001c076003500c0c00c100320821002000a041108210020301008649840326000c1c1d07801561029000e40c02107803140c2400700c454150303580f005403048211130303450301030003245070b4655142d0b9080d50038110040240d9040d084020100d0b41400740c00801c0c0c0c5607404c40c0c82500010000d0ba900d00210500424019003241210b0700800e504404400070098662075003006580c1100180742855117854640d140101400c020307100942803011090741804000f0225048444160411041c2c0c41c51511650700c02d9994454114081c001358110a0016a42103d0380e8401140400542070f4041c14010000c0d1901055100c0900c1c030740d03d1000400e10000f1004043e020341d000010a00003080c1c00d041c007290f1000349010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 948315188 1250 948313938 948313973
    0x91507120810140a150201150b090609042d0605211207140607021501151d01020a0203010603080a08010b0a0903021905040c09030501050a02040b03150f1f1b 69
    0x11000f074580d9141c035000c14000040542c2640c0380c0040303202c014001d0180c902c2d900d04e034101202400e00030030200915011510030801c0200503600d040d80c890306200180492003030114008103141c503207041c00740e000c09075030020200f02c102c0050101e0500c3c00b04a5805180c1280d142e142c4040b00b40f03956840800143d6203130700245000e100e600c524462414401c0c98001e101620703518000c080034001990340000e248040342d201c29030b880c04e240c0c3c1c840445a85240b181c018100005450f4496101011700345e80041d50240340610590740c40c03140c140c02107800d41e4080d074130403280d50100058907208258800102e501411070350607651328050135188000e10f00d00203030202030321031417240c1180301c4422442c902410041001520038010a24030382c202a00c10541c51000b41e84039400c10001805401051080310186d800e0840142c1c2151280310100328601400c4240a40100300c0c28200c11080d03544641000307044800511660180f206040c006068180c50301110707500e04034440c43d03080020003504c5118441003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 948316438 1250 948315188 948315209
    0xf0709140102151b0c060105130b0306070c03050409020f03010503060609040b0f090a06061e0b040605071b05181906120311250302040b24030c091507120810 69
    0x4481042c0102d19134100c0b00c4d07003012150300080c031004208010400301e0490f0b40032692104030400c80d02c3e0316000d841c040c00603298107070071140002e140705000b180940e8041e8081c2c80c0150600b41c46402d9242244d10103542410703841004401040180303000c2004075442130090341d000c05541895621070f01000806040140c004d4407510009645040400c00c40015a82041081c8800b968030341001040201d00408460320050446003c148010381c2d104840481d40d8513035a0900d80341243c4c48043d07000c2141102c141168082540010b501d50718510013500341442c00f0342e100030900b404021204c03502041c160400034079040c580200040c0590380d504040142c0c050400e00e1414002000e500d040041180910075170030a1113511000540482c507100c02903034030030784040081c10001810044180e0113141404c500b80c1e403c03448007040d03074800801b45811584240728181014401d40004003195400070b05100c1ca0354022590100f40410016100e14000e4981000c008030b081c007085003103064019005e82440c91 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 948317688 1250 948316438 948316441
    0xc07051c03080414060106090602060906101404060306050a0b1e0102072d030b101e0b0c030d0c05030f0109020705060612250905091903120f02030f070914010215 71
    0x10407803900a4a49511071405d841666031159000780c6200010f014140040c41149d000030300d41100081ca25001e805079680708941c140c0303045201034000d0048226142c02640380e20001000540d80c0c0607150080058042c081134140c0c400007440811020341c0b245a08825050b20841c1e407690300807600c0300c20b65440f000040da11180c0403017132900c00880f0121400c11207409120000502210138980750042000140d145401c9030348030403044004002443e050303641e041e145003c12868074410b006240311005401078a051410ac402c4a10480b2442138112000c40c0c40081002003e0480d42d00d11405004032071400c608100e565201e032582d4040040c6014001d181e806500d00106a0800420301c1ca0380c44041c50341c0e0746148211041c038030030840340700744903009052a0104108260105065500da903a801a2451940d02034a0455200c1041c0d4410128956241c0c40400d0003c0c050004520601403030450460b6420049001070480c0511380c400300020b0381442c04090107a90220350300c0c2054000d01c1204100c1e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 948318938 1250 948317688 948317693
    0x115080d261e0403020715170c0903011d060411090f1311030d030b03102f0904020703111507090b030c0d0c022103010308190909020c01020c07051c030804 68
    0x4600c419440d80c0e81190410b8100800c140e03000444030103903150355801c2e07210020f04180590b00c070000c41100c501c0034444c001c002030011039400302501314910b0040000c41c078a85582008070801141031950105c6412405c100400d01040d12841000307143c080d114019039141003804800d8440003d23050b8269445c0c1858440140000da0100f40400c0308018162030a8104055002d00200030000032075000c0c0c01035001d400001d984600c503c00300d4503903000d0180002c00e100c400d518a4001200e1004888030420702c01180310f522544040c2c070350b051103512810701c0c0b00c403503030441c41c945041c00d80f03650118801d0000300304540e43d01140d08001c42e1940900f9030384036203541c5090325640c00748654001440d45065034400a10340d0000c1c50815508929100340b40a030820300c50a11076200034000a840c8031030030481d00c00110b204240a0004010603c0c0489a1589620b107080581c3d01c25010882c00741e401260311050740c04207100b014028001150310358011003070500102c5a800d9a810040c06004507400090113 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 948320188 1250 948318938 948318961
    0x1724060a02070b0301080102180306040b0424151d0c190207030203121b0705010c0b1f0e011802040f1203270306140f0402040b0102030c0115080d26 65
    0x14040200d1030702d480c1c0d1b85501c1858000c1d004007001c0303e030403c0d26040880b034905001c116107000316001114000b296a030781c1c0302c091903c211081001d0314910682d04100c160b44552080d00c2d02d0840b03082c01751042c1c0d032500510174103000e10305e280b08a01c2200b08080c000a41040d03411904041040009035200003410401a0304080045d80060340500442c0c01c5201c0100e80c0f1300042c100600c03401c5909075101c00c20428582e441805014403400f003490810302c600800c580406541c1d002c81d1f40c08429040400701c3c03816240302c603a5540031844507920341d001844900c01c0f14402942c03501c1411300031820306183ca001d01a80f011244a2040000f4100b01841d05042c0f042000b041c1140b6180d1210646040700c58110340100f41c40d00c000e8456500c1c2c0f1401a01c003e4245c4c2003d03000b01195101c4544a490b10b400300f0004244483c0d820b070551100300403a980b02c0c01c080c01500b046074003c600200c2c05518001105042c54186c02c084410482c48003000e4221001c42d0030000400c82115074440c05643c0d5903a00100c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 948321438 1250 948320188 948320203
    0xf13020f0d060302040e0f0303070305060a05040e01140604090201080a05090705060316140f073201140115080a050a0f021c0f15050402030408090a061724060a02 71
    0x4045003000101140007121940141e01164802c0e10104070b10710082c1a0652102040c07850080380b41c004002264200c2e2081c1c00290b004040280b8900d010f0f941e440004084841074183c9281c0c80c0d444104d143d001c14600070910341d0002094406101c1c1401035400209021030040c0f1b02108541d60354049a142e030341c01c00106010b400081c05843e62401c0050310001c0c9124a10f030a00c002810840341a100b07184442c0c15203940c03d801541c0746082c021240d8404402c040340c0b4100b1070015481c0150480c00700a0b0007261850a10401c0000442c2408482d1304000c48405800000a02c40101022455158028206944444150340005090b2940001a40646521501480194004190f402c03586001812105950b103000c0c40c100480e039402a0030000f41e481c1c8001041c1203842c0c0070340c10803607401c3c203800460384180f141140d1840c0c035104034000783d90150b054000382c0000e131120700c81c074842840c030101594000000c5d15580298042e014201c08040c80342c4502070740140f1021813842c5032507008214a0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 948322688 1250 948321438 948321457
    0x360e0a1b05030f071d0d052505190e16110703120e030f070b161b05010801091b0c0201110106080d030b1905041d01020301060c03110c0f1302 62
    0x4250010184200030202e420554211035a2a01c403000b24a04601900070041c1a104120780e080207807041c00200311494102c91800e48060040c00005003241e44901400c2030000801c624082c040d0303041c0414040e059284050104024800c0c001c1840024103000d41241e02610008403031420040b0180101c4031030032040c5c0140d02c24450440d02104200c00c0f5403101917002025070340c004102c0080c0c020941d5580544000c500300740c20061081c40542240340c01001296019000c0b81e2840d461aa1812011402e50712480d10440440d68181704541c0c0c0408903900400f0700003c10300c141010040710558079401c03c0061030034892a80c410404690150500e401c2c1d007241c64008200880e910713580d407030312107a100d0007040000c0e142504144441c40c1810a545080b9500201802000c0c14001030100401c00c4990580e0580041c00002c40b0180d402d00045000e811035070748035a20810f50780f43c05012450780c41d400d1380c00e9030014036020720f0546486000200ba90411648949007021100e1a08000e01c10581d45 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 948323938 1250 948322688 948322721
    0xb0909101e0c02030a120507090e07030e030c010209040c360801020304060506011404080303271903090605030c1801050d06030516050415060c0c0510360e0a 69
    0x814082c58002c80600841000c07078030f83ca80e0b40500c803220340045400480d48d1002050300c8a9080c032200c0c17401e4008130752041940c28005540d40c42e4010552864000d140448110703900007e41042c0380c1000c4c0206c1c4c0410130070341020300c00d1120811200100c0a5505554400308200039502000c101c0220003410082580030000c642c3da081904025004e0103046620501140b450b02e0101c41d0071424504940c1126000f601450964840e01f4102e50314100760100303074025041003003080c698480d080c02854102c0c03099406080300c1d60b81604c1e01610703285180d07001805112086c400c000d0541d540340101e0f040401e144540e8454001d4190041e286402044141e109241ca840740200400200058a004403411842c505032a503503235004000640ea00b88080c60080004403004200e824007901c000c81966202e0301c04540c0302d075100e60201e5200060000f03a80005085503925000006002003807060410a01c441d03001c0d07141c4070b036030040d02c0c1581c3c610420111008410028004003200c7d40300280c6540729188 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 948325188 1250 948323938 948323951
    0xa051e0d08150f0a030807020315010b07020910050613080d020a0c030308060d060609020c151005091b030709061803080406050f16030224010806040b0c07050105010f090b0909101e 79
    0x71b00d60b800740c01c42003003207000e4030816400031041c102c03a02d9018121b5200c4406c0a1500303109a09000210001420010030400903844c0861542e6410b07000d04911410440d018100e0380c5480b80c0540b42480a00902c41950800c40d0810b0100b43c000924074142c03601801c112a0740c0d2280e00c0850310b403203042d81019164a00e81a400b0a00c89034030380040c5802c0008404a9000e5086524000140b440c00d440c41c4540344825203041040c0d04006448550244000410b4001e46010b0245034134658421244400000c288800600055402c04460880d020511415160a0742107a941003c00e00c180e002d01002c0c4100460748078007a0311703280308644602100c200503400c2100140340c069503174641120740344002514465000102d9601e100f1183c100c40400005004a07101c1d03882e51201d580001c2c1c880301300701104010490204109001d140d0082a0b20400c1d10325940c0381280042c1103136a1000c1c102c2c4a8402c201c1030118a400004110420340c800440c0080d81032555024140212800102c9480350781c1040e5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 948326438 1250 948325188 948325193
    0x40203100e0c30060112020405060607061503060e150403271d0c1207032007030206040327090c0504051c0b0a0207050319020f0a051e0d08150f0a03 65
    0x10f940018000f08000c01200060307100290391200001d0181403940c03e000c55410001d0319180c0c004c0380d04000c0142c607851a1015036103c4100303450500c03610491040e02460100200111846a000050072840c0580303810300190203d02e980c104003400103410041c0c6e1218810040d043e044c891102c0400c4281c0c0c1000301c43e51600c0b8400021464044503500300000000154001d2044045820403004883d81102640d1000400d4004002202007141450841440c00e6150080c15005040030742c043e800900c402d240c00c1c5001800c00403001c981940c8081c85040c200702100440d1800350540b80c5581022a00850814040750240501e13800242c3c40020042014012030a020030085140d0040c4402080e95807441c014009a11038908014550352041000c44e000000c240c050548a480360301c191890824034a990504d444070300034081e102a001914015090303c0818075480c01244044003414442484a1001d403150100821080c41c105c41d54030312400660305d07101c0031040317202d0080115150310340300e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 948327688 1250 948326438 948326479
    0xa0212071d010906091832011b02010c020d0e0d0c0b1305010203090922020301020c0f0c041505011b1a07020d0804021e12010516090905040203100e0c 66
    0x70f129501503285020000308503510310b03002c1c0c015181c4441c0100c1400131071039503071421901c07120b0b07c05040020362021124450b00c0e40149010907a40150f00200c0c40c08641e084891803080340440c18030039a850042c124a0940e00442c00515483c1c0c3c9042c40010701e511340d80824a44144500300601c070b1040d052021940080c800003400c600041d0a5601d40c0f259101c0f0b005aaa9104012032140d03c0040c078070001344038641040c0710880c03003881750101c182c100c52940d01090981c0c0003641280025002080500d4580c0720822406003c54412103051000080100320490b0792806406001d0402c003043c2021b5504c00044000c8101d00c0c5e6101880c801c0031291550707101d102003010745510b0018084e1a1110751094820040240542d070014140e0301840300c2200324152140c080091a9084040c0d0002403482003021320686105440b810842c010642d98258010020080d641189005500d0002440007686002650680350103010400141304c0c0d81c080b0035240b60001025138903070300c0a0b20160300010304040 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 948328938 1250 948327688 948327691
    0x1090503040611032a0c030a032304030209010515070804150806060c060604050702070305071409090619020715180c090b03100f0204030828110a0212071d 68
    0x41e80d83e02e505001e16990031603ca104180071420340302944a110400c1d0002c001d032041054101c030003215072400c000350110f810090090420360204419410030308151910084807061200303074508030342c54941541e0010340c0d030310320601406014280c01036801440c80d003040c00700c0c0c10042e0000552611966100001e514920003a0013a2002880040204000c0c1c20003400b03942503205a40094243c0d540d4100500000700340040c04c410440c803403880c0000100b1001d1001c4800f030031040941102d01c62405040c0408c0c1c000203800b51000f948200b00b005150400350035024014480c842e00581d139011182826840c1c0110b000780020102c0c84c0003448001590814141102d42e84600c100341981540d0303000e00300456102c024015015000101307019032018040c0d11032001d2500c0e40100500305600d94072052080d410042c140c000807080d03103140001880d407118a46460001a10300602c6050b1001c00b0280c4a1801200081c02001940d005a086000c140010000741403180001200c2101d0901616071401e030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 948330188 1250 948328938 948328949
    0xb130c030f020304032309061201230d060906110307020d08060402090a030b0402040608161e0b04030b04060e100b01080610090b0a030b0409030f0216180c03020c0109050304 76
    0xd040c800e8041d1034075070300a480c441c40d059202d0380c0b9a04001c20021070a4602c00e00c46a459034010094017800703a40c0c00020301071550311407808150560502d07035031005038500c1481c900c01200b100541c4c0702c2c065a40705280340855074000c80204e0700f070f009440c0c100042c010b02d801c0c0f0032054101004101c1da042c0c0c00100a0742e4402540e8070110551659000d000c201e10072200399030b0700b000703120030244045005202002e41162028200103800d580d558040c605110544c1c00000d08099042d4082100c440c501d110b4034051481c040c845040286041c45826052169201c010041615240000e062020341d90040c82d25600d0503040c1c0318070040101d0510b00400905403601d003c07404003400300d50f080c10108140426224140c85804480d030030080f82408542101030801c04040e01c5007c425000d8880b801154001071081c0c0754484080c0c549100a4141100024001807600f17200108010090201c41002060842a400000c0d64005518218040d104144c5054032540c03e0192150801c02e000000b08100c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 948331438 1250 948330188 948330191
    0x30e03060703050c19121d240a0902040915051803040b220306140406050c0307121e11030405010b010809371401050709050102120702040b130c03 64
    0x180c80c0401a42210f40c01e448070560007034107110b025113540c1020740c00e480c50314082c00c284201003440400902951400e0200782600b02044840d0300800301c01304180e1442e50b880d1004440408041081c8800001005080c2081c058681c1c00384801c0d51180c1c5d01071007243e5001451651000e034510088c8020742016220b1402c4881039242d0002a050080203840a580298070750501e008d512512a500c0024504a50000c0d40c90424002000a025100b10804042e50700184600d030725042c10a401100c0c0c00400c800c0c1003020030020080d9941e801010b071945201c044d04d0005101c070400c03001c07800960440709180500c600d020740e142c690030203c201440c0300710721400081c41200130300d90046030b0768101030320360001551208529814200145001e003621030030001742030000721503d6100403081c46040314299882c0c000e1582c40c039000842030040300c0c3c3c48060f504003141840c0c075200c0002d50341c040813100203015107004a45c1c40c0c21542ea42e001001400d500500d80c41001082d440140020808520403c011a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 948332688 1250 948331438 948331441
    0x10810081b1e0319023c010c030c1202121b0f0109020d0f0204091203050a05060102010606021005090c040c1709150606090f151e041203050a0207080307030e0306 71
    0x101100e10700070b50610143c0500300101004031061800810341070200e81c84250782240761026004034094a1918010002d40d02c018003201401c110b072102411103281c1003081286081005c030360014007500c1e000780d02c0b0341000356a1608200482c20150305442111074071400103090410400650b00780508008041c0664210302d0080380034508980c2407035002034100c02c0703035003550011a2240300e840c20043d00181c00403c18040c80e41d610424140c11024801c0130981c0c81082c4964400c045c813410364821002e0000b045054204032010307507262108040c013042c1545070400280350800134052200d120002800a100c0c08842e00b4000c1c1076201118003140380402e020000a003a618001299a003143d0482140011a20356405012055000c45003540d08000c094040c100301d178650101700e0f40c41101c011502501d8030002032000490340d0001a0b40c0030032a4050009026850815020210503585410a660b80b00070035001682040810f0707120150758003000c2042c405141c0c01c035544d600f61807011410780305207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 948333938 1250 948332688 948332719
    0x120c09090105090d0f020c0402040e01030308090c0a0b0f070203060c030712020405060403030c050c0d060510090b060306060a112a03031e2a07030201021e0a02010810081b 75
    0x32554202c42c115038503880740ca441d880803405407400d40c5d1040090300c10b48642064500c040b4090768030a1f809051082201c0c4010030034907a02490680e00300d40305001902c054007048c00042c4012420f40202014054005070505101804500701c48207130341d025040d90014540000c0b00000b5400499444002c0385107145030040daa00203100f220240c545c01040141000c0c11620100c64910403618204d0303151250230022240c6a0354105011281762088501043c0c80c41c1006415000600e10751114620f541803184e80a09661400c055a0340a04107071001515001c030780030111204420040ca0407104c1c0102c4400510b08244000d1812081c074001d0328410140c1d40c95814950b0764884c180c0700c0d82c00e07403050381c00b010003a0000324020181c0c280210b858860100c0512410070b40780403d505244120b5100410820031942c043c058440c0925501c00d45040700600310419039102e0b0b003800d40090400c841040081c6400003401900d5000d49412001ca070350340c20b804030304a154546015920b5114111030402c80a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 948335188 1250 948333938 948333941
    0x30206060316031e050102032401090605090603061807030207020405100303050306040905160b0c010e060c07081c0f02030603010501080309031b04020712050304030f0e0913030c02120c090901 84
    0x5000d040d0105069003843d58031400d80300742e2003180488a840d45640500007040c402d0002e94050901c0504500704070022103001050202c881c0e828606010031401e0820086400a00f501ca680d6410365500e81d890f9103000020700f1a0440c01490030403a540601845800b40d403541c06405a07038801d403001c1059440307a0101c07600020240c0310041c001902040019000d042ca50403000c415031003002100c00d8426250308a44661242d608144015900800c00e00e8004e0000d0084507500701250010f8442c40c200140e1820061003416400341c40f541000034041c4c101a1a81c049401e0410122000c015164452034101c0107035005803803043c42582800004038400c407000c412a60704610040c0144100f54080e030600501c01d001200e026407296007400244045559245840c80e00451650380b2a980e00c0c02c0d18020305240c442c10b110301b0130400e840c12121800d8a54000168000544455862a42649107070840c1d800903219002500101038082070a03681c0c0001504080300903085480c82d0581e55044440d50 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 948336438 1250 948335188 948335203
    0x16080307080702060705012904060905060f010c0c050910031a06011e02160306020a111c0503040203190c05040b0d0f12021e1f0903210b19030302060603 67
    0xc081c0301c01084034000514180e030041094612650000c41c4043e04040d11800160381c40c4c1481304550040c040801c0c003443d00f0f2081001505c01c449040141e17040c88408100c1c24241524054140001c0c00a003c0500403580201002014028080000385c074000420444804030340c4011503140194945111040e00b0141e0403074801c1c84181c0d00d4002c102d00e0204c1c12100005031031440230550042e000588064000121150f0203940101d802590b5007022050050400606100c0c01186400c12200e00c22004100301d0144003810712444e040340c50383c4481c000a41071241105000a4140840303645804020f0014240d01c222070040301d0800407880c07600c0902041041c0c800d4010a8101001e0640e00001c004103141d01440034a4412038208148603a40b00071046015407010813154481031088501d4070ba4500b030908481660392040c0410700b890b94010301445003100000e02240d1680e00748860b0b100c001ea00510003e00000c00d0001041880017042110901a000940050003080d0018046041c00907459 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 948337688 1250 948336438 948336443
    0x30201140c10021e03090604020102070e130303052e1401031505100903050d081f0506030411060f071a070503040f08090609100f020f01050108100b041103040516080307 74
    0x402ca282c2103020640300940c00700e080000c900e400c10854240108120002c0c6100d07410b01401000e460034140006807501b20303198840c2c0966080241000308022a4825103500a035050501107201e46030440c560030440c140c920480c801030b100c110a504407844690304e0030704031050002e101201850701001101640c0f003107030072101000e20803841080203080030740d480c05450f980d600c1e06002480e140e55416003004004010600080e10702002d10841c7c0040b2080302c1020401001c0d481c00051410340855458080180083d0502c074403020a034800762130705000c843c2d0714504080302e1641c0c3c8003a840e0520400d480b00081c489000c805600041d0403601503001c890040d504400307645c0600003a603032040303946e03030056246580000c002d000c40da0765503c5981c5601d84001c059204d084195020f01d4000740740c000d400c44490b04c50380c1044010008541c010132002c0142195035408a40181070310003280281c0000352549440c00b6000040005100c40402e1141c0383c540104544180e0300d0303540c80d4060b03880c000c0e140c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 948338938 1250 948337688 948337693
    0x14011e021c1803031b020402071b0605180609040603080c0304031e0507170102130f1409040308060409050a02090705090102120705030301060e0f090405011e151a0f040f030201140c 79
    0x1031001c28041d00c00c01840c0010064176090f29025070303000c2400c1c2e0308494012111403a07003004626101851608480c05270055250040c2400c0d1281c00b1075030301070b92020085000340400240858951580d8018101442e000000645d490107000e02d1903036694050f00c81601c1110080000300614080c001411403d00d8006004041c0103061000041242d170020300303903107807540d406c000e0808102d801c0f0b41000c0007466060f00e1a0340b014603007500a0403103560031065a2095504608020019130002d8501d81c02c800305030f80001e0704044c1031030254904410180041d5119901c0c4007001291139002c001484800e2080e401c2d2003044409224404c507a00941c80001c103550024001400202c0c82130711b40c924500d80c028400d07401e1851403800f2458159082d0740644017651038a221004001490f49881d030b10481200e800c01c4010320303e007400780041b22a80203290080307411211240020f640c45055610340d400c5000c069980b9503403525068400107151108a01080a0a8240d100c03540144242c49546505001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 948340188 1250 948338938 948338987
    0x60a030303051f080106050906032a0d0215190f1d0a0513062610050a0b06040603050103050c04021207080403030608010603050313050d030914011e021c 67
    0xd0640191600900400e00380500b08407451004050b0760801004110f44000040c05c01e0600d402c3c0062103100a0032203000381d126002c5440103005441c1c0c3c0005182017803000d45480429040022088044014081d5000520048000c0803c0d0f5001c000c0060007462805010124030001007691450201002c2c000030a40c141c4e440140301c07000b2658240d550070001c190032800e544a10001c0c41a09010164400c0300d59141c4091001c90750b4140480c140d40208502c0c1c140141c2d90403403042c1d444c1500d0b4030700e0409a88070800b1134040101500714845c410001407103107480342c3d210000140141000d10003a5081e10584003680c130542058403c80344200c040100d8142d40340e0360b18405456509024000f1002c155880d1030005110000784202809503105002540e510b00500e501c112a034003650f0070042c4103001198104002a4000511a040b00e403180641c000580415005840340e49076145484030b0401042e0010030356541c04540c0c4542d0340e042d40c0e100e9900321502c1e04100c68244855202c44804440840b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 948341438 1250 948340188 948340193
    0xa0312062120060714070b18060c0a020406030f0b01050609060304031b0602030a0b01080108030903030406140403060f091a060108400c44120c15060a03 67
    0x2d28501e601c002c0c0001410449682804994550301c891000e46600b800c60251200704d64003445010014081561050300300038803000c669503c100c45204041c85804002401d4450744000c0c0550340c03003142c004204100d06642e90074928603212908604407055040340001103150314140f010b8507000d2401400450440c5e48540c0c0c10303100c6240350141d812900041f082c90000040b511b0005510540c0c030101c000c11070500b144005414840c041e0800b00385c41d0020b010b07c0c003080d01d000082d40c044070750918008188071510340754450144910341001d003545040c072441e44688207450b00181c14032403140702000009601c5494868070602c00759031541c0001c007148086511100820f062007411911070b5400d03d42111b04500003824450310404420180d40b5a0354040c0a01c45000e00d20401071081d1006000c003013035403040040f0510070348501c56a481214100101c6820158000801046809400c0b6a0180680200d50000e500020501601031089480f42514103020b050041c0c09104040c04884d02171f41150f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 948342688 1250 948341438 948341453
    0x3021315020a140f010b011b060209190803090108060607020a0302090a020d140f06030601030302120a09050d0b0a1b051801030209030d080a060902090904110a05030a03120621 77
    0x201550400c61046040c8a400303e10540e00141e640c4400b64018110143c41c40b8115003910204280340d414841040305408070394020901c2010080d90000b4016075914000c8006400e0071998400344040303c1d000d20000c00e00100000003090b14200980740c4c0c0c3c4541e600c034010080b02e40f0a00f00025004440180101b0040c182801c0b0150401035034840035081041c02486101151009021404180b00c4001406000c28010469941107030040c0d01414103507055440180d6108074011007604504070000d042450a4819030000d005080010104042e04546041107100000180c42c401103262400d5092400742c0b03121403506010a03e00c0d124241400b03a040c0b00c1d01c107140e03202102c06050540811085850766414820803021401da9140c0215a00340740c0711980032180c141c0c0140003000d01c10401c080059403490315256020354010549082c0b2122440890720803a0150b004580510a81c1e603807208260700404005c1d15010708040401c1465038551242400080c0c00345111900505911100003050302c030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 948343938 1250 948342688 948342719
    0xd022119090b0f120915131b0e150609010c02040b0a0306090b0403030b01030203040f0f03020111030a0c02010e06060d0818030607110115240905040f06050a06030213 73
    0x1142400c112076581c4a14160340382d844800303007110900000880107545203600c40d1244d005000c0c0801400407105584d240c0c012400d014045041d007000354003400d010051110b4074907061007072221981545641c1d0300721030f40b01341405030350b82240100c060076030310060304020043e550746400c16583e0950306001d580902004041d040d85054100d121075a0210208131f00740159001184140b0a9203054036050600804841240c10780c2810140101f0500020400f03201d1051801074010f40410403251891400744d00400400200c1060002d021081040c440000d80c418103000e4510340083c020500000420b0f0307110743c411a0010303441808100004041143c000180c050018030070808001410444002440c10304222003110000b4030118046400034070038002d0b800c240704c22550080d8001d040600f18107917030681000d406215100c409009840c41c0c4904038030b0000b058054000c2240801c00d001000c0541001c0c02079501908240c14002102c502c03a20031207191110581903180c5d61410100311034404401f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 948345188 1250 948343938 948343987
    0x1e0d0e03010f09050309030d05070b0604020d0f0608061e0f070c0c030f08072108150402070f050309090c030708040210090509070309061a090a050703060b0a020d0221 73
    0x42e282140414070601e8411800d01d140110000c1d602d4041e244205458018461b10000411030103101c01c000060007450342e00d421180450300941c03108100e0884800605481d03078880855400c20b40d0000c0d03030100c081003c50094001c0f410010100030501403502c8086010350300008014920743c0001e00c068810208903003018407a2102c80c2040b42d0320744985d9010200d0313203816a101c0c00006100e40801c000c4c0c44c110540071028165081c074240349604081c151400041155075040041c003207050640d07807203030304581605a1140014064081303608045580e900708200c410300401103138000c103480c2c02800d415030f40b143c81c0507a20307003100703607140d509000b05012a03800f41418003246000100d21940d5036814984281c049540c0002c14540030308002081d44d501d50711241c0d0383c42280d20350f401c0d07980303030340320f40660000140340301003450303111060114000d00c9154082200031402241c4044846d902181e80c0c90041080d80c2124000f00c1d00444a018000700c2c4d5449024202041120550308450800440100705 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 948346438 1250 948345188 948345191
    0x40b04111b1207060606020601061115060a1206090618052104150206040302071a040504152409143102041706131a10090911031e0d0e0301 61
    0x1040d1146805182c100c03a100b202d130a0784940c01480b01590400486005246500d420341c440005404451348030070645984038030840d007040016016071070705c00c4004010950040c00c0d8031940b5050a0400051103120b504031421401c140344003101c40702c01818281c145802001400308070b02c040c02d02034128008410040280c12061000040c80111400c0036110600c094000c1c080d10f15280c50000d013851055081300f0f042c000080d13495150f1035070420a503002c1c0c46080d50005505d00c81508103661550711544226a9501258130442d0800f040040c4c00c1541001921804001c645401e03000d402040d494507041e4200000300c00c045032031a8104210120b0000700000010064551140c0405903841500100190201c1c1d920074204034a04021156110f032240300d410b01d40402ca5030380d1036110740003440443c03007289228020951111a1403240001060710b2031040020042c0c0d841c1c5881420302142043d4821b014003240301c00542442c0c1243c00d4255083c8000d8201090011803c1c0d54040c0180a82605136 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 948347688 1250 948346438 948346453
    0x21201050904060b2709070b1b01060e0703061d0c0f03180607021c0215070f02100504060902040b06090f0103051503030f0301090b0604031509080d050411040b04111b 73
    0x9031621001c100c1445c0f2a0036441d200701c140240c02c012800400703070103819285d110315801c008004459042c0e0303074024150280c145541d800014200c0c0544450b81040b00580a0041884401c0b90958002d00c11500300c0114540041d82803c404400200101c4502c1d148900070400c0300405080390340110ba1105903c0c1105a568403a460342c945410030032140000541e0003190429000b600c0e1030f04080d580b403c0c61009003a01b034904650301c00c451001500c1c00e02440380301d0042042582c0240107040d000140082d0400c860b05e06030030018050b098000e1306900981c0340c41c8078110141090800c940c604e4001034203c3e00c0031508440110000d002c0284a000c1c1190030700d4070000320359001c2c0002c00c17894031110b0490791603506240c200c0c4211030401c4134481c8a050100403c00c0001c51021034052060203410001a01c80d000c1d0905121a200755268080103504e80302c108010846c1c0c10080448459040c5c0342040445091803d200c115402c10700009100391045c05000c04810071900e6003480454510295000b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 948348938 1250 948347688 948347711
    0x30c0b0c220e0c0a0207050918060a020901090603020c0a021e03070305100c080115080c1216020c0307270b0303030c0406030507020d050304080a21060f050402120105090406 76
    0x41c40042400641c4021014000b00410950b0802640d040a400d800303c600d4201c40c0030001c1c0d40c0350041c0c495580510710030f80003d2264540298051f042044601c20385402c1e14100304400000e503c04880d4a000c07410074000461031507c00d01c01d0f640c1030090b450042101030144c0e0200f01204101c42c0c0e4032a2039600d0700c203600060707803000e100c001c00a505c1240104016135610102030290382081000751308001e0807400400426003024038440b44805141402042d0740c0b190f40c1603c0035482594000e02d262045c40062101211a00c030344042060a00e9003034800246401c4101501c4455911465104140d07400c0721148590315061107150842d0751070070001d00c8440080109003590001c50702c081d500301c00440d0400a40d5098041c090784100b8034400740c00c142c01c070342d08098450b010184c80640b00c41004241448070314080d005103090400702c180c0002300769240844078030151000c0d00840d040c2c0010540001018101802a6a0000010611200d6030b82c200401c5c00541c41001300180e40690700c0300720f034046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 948350188 1250 948348938 948348967
    0xe2202040e191109070c0311160b09031e0319170a060e090c0306240a0801021903060b04030b131a15030a052104030b01080c0f060403030c0b0c 63
    0x82c1802e081c640b00e040c0003905004000480074616540500c01e8002041400f99000c803050b2250707030349800c00e0305080e00401041441c1014a03882400030348030001d0086a0300e91440050800b0b42c0c401c4013103da10f080c2040401c01d00e0703070008902040c203500038024840c4401c07800d48200138450b01490011500b031322040c049100400c0541e8600703000c50743e9170030901001400c1e49c1d45a901c0001c080080c4135152001c001309594920040607031105031030701c408410003100d0300007000c216110001c100020458490b12043d000b948500100c1e080405851100503805000b80201421201081d803a54101851620707040f12100c1c004010410450600f201240012100400581001c1c1139038100c40d110310302164141003400410846601c0303070340160b801200103100000e0845201e803003e102c00c51a0407503142600118012604020010454403002048582d0002404503c02001719100151401d40c1c400780840b03403050b80005000150101c0805c00421296092640c001c590505040d203000624002c001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 948351438 1250 948350188 948350203
    0x90307170f0303130314360d0506150d020307051315030c030302070b0913090309080a1a0106080c03040b0c04030804120201080a0e0316080f070506010f0e2202040e 72
    0x45110014121361001d140e032040900c1400c140081c0c48900d40b404000102500e01d107000e40303036184a440c007640403440c482c42130000204180007400580908805203404c5491f0803040b02c442c0412607808110703108501d060511803050540103030180c15410304002c2848420300304c014041e01190384400060002c1000311498000460040e0b00180e105030451800909081d50b45c1d02c240b030911410709c109145581c5000003403107182081c0b040000e91800c01d140c1542c0c89079151344804064000d0908c00024444080c84001a20b0139044054909a0b00c0e04002d8400350020754103085150b20a00010f8000b400400b04c940e08280d01c484610700341607681d9100003c56119400006580411111100031941c00111643c1c015040724410b101c001c802d6030009559025482c00131943d0480c4010a10034840f080c011103840c80086000301d90f607001c86080c01a07660b042842408110301e8a06400200380502e400294000d519001d00202c101d0481d14815140c464080002e0703a00940c4c403c44070311420340400889 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 948352688 1250 948351438 948351451
    0x9020604150519141818010b04090e0d0f050307020106030507031208091b040b0402040b040e0402130c17150a0608190614061e160b060402090307170f0303 68
    0x80c1da50b01404220141e89041c100620184104100d54441c4a19071805031400e00c0d01207505c41c07200b0300340358001403030510710505008004800340c000441c02d10100801041518070204e800d02c00701c0c5044c0c408540d1240200c09600000728001a2441c200d4425001075412400750301c000301b102c0340c4a4035090700786881035000315100101d030482150b90035000203070701d54000901c4c80038050142e0009846244000e1a00d0464030407235890020000a68455054a01400b00402c015482d40d8030381660748480d240c00c0d60168441c0302d00b58503c4481c0211409180e845c0c01d006d5841d1200c0ba40711184c0c483d41c0b00000b9209800505160750b140c026520340441c1d400041c410b55648461900b0070150030701c141c001031b1645d03009040c00e1010a0081081e490186611140242d49130765681c480705071128000c103080b482c00541f4000020f80c0f06401440d00c0407201c0790703600914204d46141c4488040008034400c5142894040d003200000300512050710103400c41c5c0702c2e019010781d21549462000d441c15980b048511 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 948353938 1250 948352688 948352697
    0x307080709050904022202120411030c060f120a09140105040308010605070b0423100b1504080d080408090409051b010f05030a0e070308030408090910060e040902060415 74
    0xc00224030703841000311008080c1a900f250050826401107518512a48800180c1c28005980d803540070b1929030482d0b15801d5404100c0034641064504070244890804015219105060324210700d0300d0614211480105030a803018a0907a4040326036821b07040003010b6840d00c66881070b108010400d0b20f030241c4c40d0300c80700000002e0b00d4a014500507041c2134044e0000010403070207000300b400050b01c101680d50840d4200c42600352400751800244402c1c03038201d800c002d0078083c400c1c5034101840c4075000010312502c02c03181500104109660f050313480c0100c3c42503021a0344114000040103000d0b641c256009801510741c0f900c0c2250310400f2505688544c00c040f6155071107031058034044001201101d0382d6070024a00a40c1c61001c0c090010038030301000c0d06290145680e84d00d00c4c0320424007004168025580400e001e03842c0c0c503080c100311145400603207849000b205144006003180c800840ca007001d03548152a4001901844d805000081520080403078228004200100300c00b003119440700d0f0740701d4141da02d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 948355188 1250 948353938 948353941
    0xc0d0f0303060909062301080d0507050109210201060504020f070b090109140307062702120a0b0c0a1d0a1406070807260307080f07171801060e04051b030f0102030708 73
    0xc900e81d07901c0c03084011101c00703a03014005010b01000410307040c05542d80d515186860301c0bc6824554010851084024080c40c010000c81c8000781c40041c28244100054008100c220b50752000d1100303038441c04400f840e51080c10030440c800103600d1104981c20030490760001074409401d503a50109400c176001c85082c6c661020503400c2c100161070280c0702446e0188511200114401400c3c3c5c80000d0300110b0092003182151844184840100100985030350000b0303421040341408906007055900001c201800240c0c103503254218920145440c1d1000c2c032016000050340ca242c0322151a0070301c00c451080d98898800c210b01c1c000b245000e0050554a0302070f20303160044070b048030ba05c80301c221548070301104003000074000c1242442c0c0001d8000d50150b003a05c180149613449980c1118465403480b9403a488075008020b00110b983d26541c04901d8041c00c0c0c0003000415124568811104401c0700d000780300b40d014205505054100213000c0030004005011180c20340b40000e800307130998004a4900000455600 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 948356438 1250 948355188 948355211
    0x2100f140702031308071805131208060a060c0f110402090604090608010501060c200117070e2701050d060207080d0f0609020f12150d14010507020c0d0f030306090906 73
    0x100b11300010400c8500900505140a034240c40080400552110381c6a4900001d0441c00300d0381d5030410350513803018800180e1040810060b000041c10368844e4003a11903080082065070194160050345604850841043c0c0056920b41c0d4441104100d141e412a8082c8080d004c5901e5050103400504880e03040420074504000000b4210b500580c4801c0030049c02110f00e40c0400c01c200d01c01003041343c0c40304101c05110003840050711a0035501d01d40001440340101041411076002c03a94080308181140c015500300a0072038100082510307820562001014000100003501e4002c40e00e8220503c600c6000d402c024003620b401d00c00d600b256520b47c41141d15120072016214803441428042c0032540c80450402c810003090f19418000d440030000020700c0c00022030040c0030784030003c00880000404081a02a0524000031aa418400d10300300541c241070108440c14004203c0220710b4101808050b003c0e00300f61204400c06010910640c1810780c0c0c3e03013011507034001c0c0c0c0c02006c0003a401070b40040b07900c05805 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 948357688 1250 948356438 948356467
    0x702040e0c100c26040b090a0b03090345030a0b16030501150e010806010e0a08030c01290613080d050c10061a091309052b02100f14070203 61
    0x280381d05084281d400e203405000c1e9a1130415102a1360200b40c2580d01c0750b90110106030180b0340c40d000800c51800100402200b83d2001000308030240f11110503a07102001d0004005442800366200c0166030360108216003891407060746400d4580000342180c10b045410f45036070361605400e9414401416010744180e4850b81c040c0285801490307205102d03c100103118400500d81e044a40c44241040f546101040a036849000d20b04903402000300b401b003240d41d841101707a82e02c1e0b01050407483c1c554249444620300c60790b007480308846240d1172030958074402c0f482410010140d03c08485840301c03030b0002c2c0b004141e43c0f41c01c0001c030001498503101c0603900e20410900500d400100204020075504200052041d02c03030800c1403480c5c0714400509d141c0c41c2c0e451140050300c0d41510b804d0040d2110b14010904040c0040002c99108018041013a0110503106a1b0745059213132a1202400150384007076031904213041568001c590021403003a0000d22000c44418001e103084050380c00f9001a8000301c1e6080d03803101c80 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 948358938 1250 948357688 948357713
    0xd0807020d1b0b0306010c12120f0605130203040206030412021018110915040b0a120506010e090f0a080a09030b070e0111160317090a27020309030702040e0c100c 71
    0x100f0303042030951070b02d00e00003170280501020040c14032030080401c20f0290b01580e644544a920424103210003000340507503800406080c800d8a200d06401090300403445640d01c21a40201d4001c0d142c2c61842c0d440c1e8071034519085909070f8080441c803401e40405090302d1281b083c00340001550300c2041806400c1e0902407440c80c54802554840c508403018401c03031145a0402122508080c0e4000c5003012840c0009410071940c0c0e802002e0305d8090617445003c0100105242c3d050f6203112139228980d84407078030a650f807071044040e034503556805a4508000720341440080c04041295240a080f0241c890b561403005447c00ea41e404003140341816524001c0d0b801c1034400b018007003094014040303180411120105000144000b4110b402c124200c42c4001600504468540744090b0071101d00303075500c084ca03440c4004000d840e1541424046003200c88000c0900849001d910218021801c01c2000d808010007804090307640e41c1244610801d0344016207800c01e4444c00550741e912448030001d124203140018501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 948360188 1250 948358938 948358949
    0x2040e07050f030604110408030c0c120109031704060b0a08060402031c09030b0903040e070809071a0702221a040b030c030303130804051c030f0215060d0807020d1b 72
    0x400b4070001c80090704074010f03641d200c5000c8a012a0030a000032540d141442290007140460100040640c01d140c0009002e40140b10161030091210b28580d1680b400c86030032000c014005400d120f120030030040a0481c1c160440d008000016440d17000d600010100c2c42c180c2c0c01410103410040405c010342c5014840700c50170800441e484614000203140080c8501d07824040104940040c10105001080400c00c1e0340241c01e01c590080c071103003040c00c3d015081c818100c0351800180b041c2c240118044901c064801d40002600c5600c504000c01c031390810200c034800181403080b6010204070079540200e41c1c000e418082c2c0241c104a030300c3c10039101c1480182ca41e4051080d001e584520b40b1000540c0b4004110303907010001a03500a83c0e03a403075291800191240387e1206070300c041d08800706800198180c0440713107124401d0712100e441c07c240035800d0740c5441c1e400d40307854600c0306620001842c0741000324081d11030b24420321680780b0b040c015a0000d01c2e40c048550007a507400e1001c2c920341c92515a040d80c2031000d0407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 948361438 1250 948360188 948360197
    0x10608130b0c0d02161113060810091401050a0b0a05031929010303090e0a2c01060909060e070501090b091e032406060703090e13140102040e07 63
    0xd990391107641c0d0300c280c041c0a02d640000c00003045100000f065059410003403a0340c000c04100b50140c00d05400c035102030941148101d0580c150640388000c0c41c480c90080b1080c05c1c003d40855403500d44c14030018483c001059600150442003452210790a1144034800c00610200042ca07030801420301219503941d412090080c2e100b002c07198844c002091000360b10a611001000000c1034080c040302900d00320013000200c4500d04030020003055000100035003951085030058455554020b0148140d92101401e0030b04075002c07960095100754030000c1d043c0554040c400105480ea55220407204540801c40261140d0703585104e00303100d019082c40000024002460044126030620f056046a4425410298407030300100054800382c1c01f0500541c0c44810005050781c00c285c28281c40260100d40c0d406d44106e507011114006a1075191660540741050f4040d6121790b01e071401c05c644003440354ad010b00b21100500c0700710850000190b40c1c0380001001202c101c001340c2ca803860300d900509007a0b0058540000d20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 948362688 1250 948361438 948361471
    0xb0103020c0606090a18050a0201080c2514070e01150c02100e040b0a15110601290405030a050f1014060f0a0503030a1805060a02060f070e030a0b010608 67
    0x214000b4000f5044a030031622454142c41d00a1404010b240380c40c405503c0c411019902014040e011032200c9100f030007a02d80340f8071070b680c070303141250507100705130001a09080481440300a1000b1000c1381032218410080101c14000c040701c45440d02c2c44e40c0c1d00c081c000425410040c068902070030740402c8003426038100104c000310681d000480081c0c0322481070302000b01c036401c0b50344583c1c0e07590864055400040d20140313009031a05020316440b51615031010100e0b00c1700303032020511000080c019049030b040c40500750f01c1013030340b55028004d9590303600c405821200900006c155070354240701c00b03400d00740b250300100b2404441c07010503410151040038480c1e40d54a48102c861181c40e82c0c1c80300a50100d41100c40b13010b881f030800006448400d154100076010700c4046407041e0a581c00c0300782504003148101041d5015640d0340c003000501d100c0da90400005030014408101c01c41810040160410031504001b404403003100f0203c0d02d8210710020503205000c5a01c0100a45900140c040381c100c001540c110000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 948363938 1250 948362688 948362707
    0x1b06020d081003062306120c1c0c06050306091b09040b011206030c0503011d0a121b120f26060102070308070f050d0810051c02100f030b010302 63
    0x45031003100c0c030384091111000000e079403000c0d0080d2030780186501140411900c604591082e60300864691100400300604d0049005882c00c061800703800c00d9690000c094200f450b00034082c2c460039280c231045031802161610b80004544884060240c030443e41c1e015140d15040c020450540702c043c5c64141c1d0580c41003840850043e890f030440321403140c103590200324200b2440049460042104240764150710700308004c810000020071040c00c50b80f048000b40212017428501006035000c503580740045034008201c010024503494110342800105081289803e0f990468000142690341e038102c910480b002d10031640f007a04048003c0d4030015503d0700e10f5100d0216844958079054070900d42e400c0b00400000200668420814180038580c4104919110a100d240890000040640458081c0189101c007440d151251010500c2840c5113034980c044d81d8500b005000c40440316070642212080c4103040c4001584400030380605048440d601ca480030360807080024112858008820704040c01000403034031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 948365188 1250 948363938 948363943
    0x108030c0c121c1e030504031d18090c031207021e01020a021504090e01020c120918060103020f21090601060504060503090a0507120521030705071b0906031b0602 71
    0x9414051050b8080f5009000030540380d02244541d0b003c001e0400158072040d80360305420582c040e5100e6240d0000c031202ea03a07403d0744504400441c040c0c2005104110006404c03414000a070402d42d201c0036101c110010b40e02090400c1c0361540d540c13040741c0000031844110301b000d80c1c60f500181d00e11606483c07113015100000b911a5181c50303001e07101c3c1c2540940c1c2c01010752800103c07402040b81881c1004003060418445010750054036245080e4040c10345030090034088a0100c0381c4041d0001d01d10500c20801c0c510100161b60701504a5041550911100411007801c0c801803030111031100700905c059443c124891281c2c040100a089903400020041107501e1b048030946042d605641019a140d0380c441d4181440d1101401c0007400740e106900d130010f00c0384c03020303418851014010010380c0d812041a041b00380350640c51906048814204000040201d4424009084d04a1103921110090040400102907441068020820382c80d42c43c0c01c01c1040121516150030314a81940e0f6000d41e01e86081030294 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 948366438 1250 948365188 948365203
    0xa080d020307120c020c01020114010f061805060a050405030c031203070f0e0a0e071b0206160302030912060a060602011e050417070303020301090f0209151602090108030c0c12 77
    0x1428940100100300c0e95405412110740400461504000090890000942e0b0703003c1100700502651078001480550322403481607606a504a401b41c6070f03024030f0a001110001410180300001c0007090740b012600d680c804d4020405201141d40b00f0740c4450034217040605014010b000140700e5808154221007008101c0240c0b80c0c40689814041c0130146150000d585c1c0c50044d844213035102c1c651440201b903600502030780034007842c82917848448900302c182c4050001104808040e601403810301041e0f0074840c008805640b158824819a804d110a41001c0b6034450501c841048090300b16004000104410f44540c10003018540700902c800c09100071403600004282468091150321600024140014030b880158111500d6050301d40d10411414020000e4000f800b9403d04a403d108142c1c241b0206802503995004000b080074a59040002c106d0380e20381c0c05a48110092000907001102603640c4240c40b900070003c05020f541d46680603000c441c182446080203600c9440341114103010140e0006290 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 948367688 1250 948366438 948366457
    0x1b01061403010e1203060a080105040506090f12041e09020304110f03030f031902040b030a020309160324180c03171e16200102520b03180a08 62
    0x140da646c5509010621040321030300846601d41c00c0409200c101300000070084e04c10031240c01135414000c041c0a443d5140c0c40c1780e00414242101c284002c3c001c0c032062101e0030981c1d00070704001081c45a43e0314010002e0760822030301960304118000500c0c419090045803c0740f2030f2000c401451402909a080d003000d408040d1009006c480b2034800c1060041195040741d000c1c22640b900fa80e10f17460460400c20107507202b15120003190040403000d2001307000541c4403006403030381b00318075500142e070000300c140f28048a90800a102034480e4030904020903407401c0300a00ea4010b2010003a041e055007840c407000860829140f00241c1d0400c4020341c407140c20313003c04c80b6104003081617958880030058170642d44803010341d01070152448030081c0f034a4401d08515181d01488203809480b6901414646081001c982d40401420b1a01592928186d8038044c6c4d11907500112a049aa64484540303c41a4400015801070140c422002060058822940010042c82800c1a000b410401b11580d528441c40c0900e1140303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 948368938 1250 948367688 948367723
    0x5070302090607110f0306011e0e010605070b040c0b1314150403121202040b030f070c020a062304030506180a0213051e0f0618040b06060702061b01061403010e 70
    0xa44c3ca55960f080942d0b80500050403074a095071507074000003040d000c94071140d444048840d80003032000034110545040301c0540c0c480c0c50600502d5182c0554030f81004208442240072903401240390b201c545c0191510344a0005206102401d006040e800c42d030101c1011449071040c00c0b108a1341030040b008031001d0f26030000c1c500d4022903a000c8181d80385420300e205082d05500118002c5510103c00f8055481000040641540b6480d90401a06c3c8400c0c0c2181c081d40080845d0028001d01c0e0144c0403400515514000d2804a0f1400d0311407046540c10541003201d0035003150b810703c6608400b4610841f80c007444100030b02607400c404d0340040c0001903030301007142400e1f0311100094543c9514118080d03011411085408992405540340c2a80b42d80c1212030612600221100041c2e0300c1000c909a48120740c800003824154551008001442c2c1098400301e900c1042004881c100c0c2a2500596040c408074a0000c031b980c1d420300d0a800c480c00b00c10141e0758001e070302d04a4030101c941000590030011100300c007003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 948370188 1250 948368938 948368963
    0xc080d1d1f090b1f0e1905011202010c061d0f0c030f060709060f03060503010212011a1620060d0903090b0a1e030e12131203120e011b050c0105070302090607 69
    0x302d01000002c5580310780122a17100007000b50848100800140c0ca03a0010400c21644e0380321600d25004400b04070003c6e002400680b03c1400182d5aa480f0400f80400d0030b200c0002a609105014035019270058000f0403504040300c01c01580c02e040242280314054032010301028174245100030022072246c0f1482080000b641841c921060007540210094003018009541d103503207107a00c02c0410a002e101d100e0040c520010807a8822071142c0c00e44400d4124518542c00180190b04d03604265031170044003410642ea101449011a1b603400024003000c40b2040011030306060358103025008114130b91001080308010480d4010316036102a5181c0ac1c3d401ca0002c0200c58181200100c0083c100080c000003984600301e15554150604030140c1540c500354150742d00f0890f1a5180500505041d200042c0400c22203a64200008083c0e0445091546210000201c51040e280e0740d000d0000d131070003514081030340012110304c80c49080c01040d034041c10500f0250719140803075002c80c031a88507040015141082502 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 948371438 1250 948370188 948370231
    0x506010c020d03031409030c0d05070203150907150804020f01030e070b1b0120031918030f0f0306051005070303020c0111031906060c080d1d1f090b 65
    0x280350450140c0260542124604919015000f441340b4905000c20b091000d00041896900204507045000c0c1c5030040c122804112302d068800380c001041c103e9240c02034082c50707070700640100801841942d1a00003010756500d010034600515800c641c40d43c042000e4803042102503218a0b0420300304440030329001440c070315581103d42c18850310360482201ca400c0040d08030540e01c400520041010301d40307802040950020540182c1c1488220784810f000300c014400625404020041c69a83c19250407010541441510031880c01d02e510420881c0480c1c010400003508a6005090801d14051405c0030404181080001264040980300c1041005000503a43c0d0815110350151004461264000d005000b0510f0101701540c1040b075800c02000a4000400d0541a150040300116007684e1a408801921910b4800e07081c1e014600f85500c0719290103910038a085c0580401003903d0210700941407401c4504041da00c400403140d01e0340c031100c0c101f40201c03001c262101c064581159801896002100190 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 948372688 1250 948371438 948371447
    0x10804110409060507050406020f0c130518030403051006170703150e0a0c05270a020d020403050d0801030b10060509090702151602070b030f0415110403060212160c0303050601 77
    0x81c010411070030081800b0b01720350000040e00a503a0181c007683c017906034201300d050303407980000421a4407010046480c0b110340107030781c025500807548582d0182c0909120746d4240c41c0d81e0103940304403041d5010443d6039143c0040c074402c41d40980054804200304918000c02c4c00e658680500024180c008200056508101540d1100c124a01e154050318103038112400c00024075040c900c10180505015920700065185001c00c1c844010f401110703102031902d5860491000f50040010144096401c02002c000701d0001c0000191641d21640c411002d581180f800d044071b840040c081821800190205200b030301d40082c10b643c11400b00707507412000303941e50040491034102c490b501c2c503031aa21443d0911003081c0800c50700d2900700703e007034003181d1100f65650018945844216807041e090b0b050500801c0004402c5101074082ca60180c80c0425000f05007407098155a01c240e204481d0660b001400c0f0036003900808069074071090200082c00c90070007a0b1406400000340000007020140d441000441c940c1c003c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 948373938 1250 948372688 948372701
    0x50102031801090915080105090102090105161506090c140f0409050411150705010e03071113240918050d110109050601090c031802131517010903080a0b0108041104 72
    0x2540e014000f1412044042c40300e2441c502031b414083d4208400241d2080050086542004040c0d40c3d8070b180032210450b1055500c100300c821517480d01c4550922000c80b00300d000d1140988401400002e180e8841e00c00548940440d11f034403514000e00340907803401d940005058a0440d2030b20340010400e540e50745440543c0703038004045c1990204a51380040b000c0402c50002c0c1c101113100d603000300302d1b4940d1400c49541d40d01900000034131190034041c2d808020708213402484003601280c0c50200b005051514101003040f0b00308082c0d2009180380d42d003004039006601426100000644041c040c0e40e80c0c54507541e4072802410405070a0004864510a00400951200710390a80200030340c0c00558684e0a0400900391003044d8400190500001c003603010700c10103a045960303034024440e613812104554a01d019000c90610aa5410b40c440300014000840c0000c59000d0011000005210700152501501031032000d4001e1245915005030010305982090401d41c1054015030110701c80e06100c40014042c207071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 948375188 1250 948373938 948373949
    0xf03020913090b0c160206160204060303081e090303060103021c0e010f0b040e0d08090a0b010806010512071206270b0906070215152b0b01060905010203180109 70
    0x18220320000780c803066220019482c881d5400c61441d849007181c1c00c03818003039110400f140c01c0d50000b1a100524108000b131076280d0f02c00c44000c002c41c444e40c000904543c8254000c2c0d010804841c1080300355510020000c402c001e4410b901001c904204080d50394a000040c0600c4c10715500180f0380c800c04085881c107980701c074500c0c00d00344014803040340c0700c80c041d00c003200d62103148608001e06c0032180d00e4280030303100c000d00030f5000510301e015045c00102d540000c060702c586142d006005404010600e0422002c0c041c203400740042c000c43d4505400e109001030400180e01654001d0001400001a00303699441100c3d007002000c64461100c229001b40000e0411104005d4111940800c0400000ba0307265849a9170440a454441d81e4008050b80c684440d4507201c400c006150380055001400004640700180c1c003d40006000050f5152158000890900d8800c450a000101d24200a41c56141c2d5001d04020b1520703900003403611002035542c6c018803590303804900c400300c0c210103a648501541e800520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 948376438 1250 948375188 948375199
    0x150c0215071205060a1203121d1c0e030d0c05120a03150e0c160602071a0405010c0c0c03080d150b04172103070e030d0806041404120f030209 62
    0x70810005080c0c40c400603210382150f0f09180009059150001000d8101e80b916001c100f80700c45580d40468000802d42205001160b40e00d48680003258110380841c400c40020b001400c2c010b9034200980d61106031780c100c1104010107100700170481d460116000c1443d403941d05103103800014500d80a404c00700c400150080030700c03010620400595258000d02d8440d640c2024032020540c40d072811a0745040c00f140c40c82d02d14407003002080c001072881151b01c01ca86004404c0181040c0301303a07461a01018400f0b451402c0c0b81700c00f900344001c1c41420f10500e81c486e00b56050034484005550303162401d140c0103200c042c04140c00801c00ca2000d400c03030741202c090b410620f10f9949085440d107113001003076045030258484100000c1200c000e01c60300000d8516440742c0031009c984071001b2541130300d03038640d100038a410f0810100c001c01e45001d45003000b202c00840e1041d260503103645070000900040b1a00380030035100880203e000c2c80040f600700c1499502c2c07409280b0300039441070500305d000e07030207131261216264103c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 948377688 1250 948376438 948376441
    0x3081c0c090302100f020303060105180d060b011101090f0201050d0e070b0d060902040f050f0105041a031e0415020a02010608120a0e060a0509042310140d150c0215 72
    0x200d61242049064910886803455410f080044c2244d910411441d0040541e004102041540d0301405c0034142d540c0101221100c10650080401ca1006100508803940c0c1d4880c82103c00d55a000855034112041c1302000300315045094544518901c28080c000e41407210016100301c0a500c0c1c6d40002003100494030498180554841d8566542d900c4011b2011026140040100b0300c000c131802224100c4980c1030b81503503600e0500c020440b085002440c501d061001c02c01c0001600f454404080e440701608142c2c00e5203c3c5060304440c010446054449000b500d803d030204400107881a00c0c4078041d802075003005844044141080c5d0050005801004c12841f80306100303114080341c800207002c1228a59a0390340c1c407128490a0281074005d007031a05021650910050080303007410f0f0322000d00100c2e440c00c45d41100340c80c000202100401565001c119000c07940341400703108500036040d030745800c064801000303185040e1140040c08441d4480e50308020340718021302411a10803c07222244021713491040125 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 948378938 1250 948377688 948377711
    0x16091d0a03020d030c0905030601142101050907050a1215061a0316081b18040c02240105010905060d110313111503220c0b070b10050a03081c 62
    0x3c03082c00300307511000030342805e105a181c0c5203d05041c4080307071400307801484283d003010031008500c0b141110441d0040c2c114a5013400701c0410315910800c440311400000b42c00e050500110f820328030184c1025016107401d10307003004060032106610144641140364604014404a4090007070b14156011f01c01c40c00b8018034685140700c85a00450140003400c2d444680c82c1c5141005684041088070f4004412100c91130510810080c5002824540c4411038003104039040703800040e040719641504200140c0c400c0d19040c5010300d00e581c4022903c9a0321492488075071414000810121280c003a4a00442011032610001c0710560070504007100b031a0384c425103a24103680c60015100c0340c0d21056a40ca044c001c1c500d0031a09280708485000d940d1084a40d2456a0311204c900505124441b2600002c00c24032568001c541c56040711806400a40c9840d565510365040034009908041d1416602c00b2084000304090754a00711100c0460358055815500c503100c210005010004c49403a8009040c00c1607040c4a8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 948380188 1250 948378938 948378943
    0x70905032a0f060406050a030e0d0507120e09180a152f0313241a01090f0326210702061014030f07170705010216091d0a0302 55
    0x7601000c0c04601455190280c041280c9044410078040e0401c0081205000f164810700c01403200c0b8042c3e0401142075021980c180345041203254020001800210300e03a800c025460009418009241c5040303452110005c0004403960406403041c00c440b130808600c921051024403881e4030305900045d03150708800950244201078003a10200d104c003060754003040840300c49440d00840505c060342e0146401c698030501e4090ba07040d043c41050b0766152a00c0540d20701c0c9924a07852202400d1404400f040c040a064071aa403075025041c0541c0c184041160217200010b80035040200b12500320000c0e24041040c0a1122081d5910130031141000d400080d0584844d030300680701411420f5510b15411260b81c458108a8413903d0640d5083c00034051648204082c4901c1d8882c0201c000004059505c5100c0d403a88141c94107100c0d81c0054803070a074884031619050070911403000200028000703003001400c4150269041415400b91240640c0d860644003451003a40e040541094540da040703900e8824a420080d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 948381294 1106 948380188 948380233
    0x507240906090b0342010c020112050c09090108030c060a05060d0f03031b080f07020a03091e03080c010e2505090c071a01030c08060f0c0307090503 65
    0x300103d5040e072128245c091584000a01400c90303201c00009061071413107810b001c0004103000c05131360480c4001c2440c80c0040c00001c2c05035540c120070402c9010781c001080d0082d0100d4008210710790004020402c800400d41103c14a95922406000751241100c0454000301c00115220004000038842c4103002d1103802c000c0303020580e0a0005c0b9203c01c0c10005170340003a01c030506010313506543c0318540d60000010b2010700f0b00d07c0d506440c00303071480c0230620030403c142c00700510050104035022a07010156610156171913907050540c43d42e0340a07045813100e65456006011000314021000003024525020600e41c240c2250f04e40402c2001c1510010412a292101084903500040c0105010204980100b00038015035055044c841114002c50304844040d03448041404a100c8020280c0303540500c40442c03003662590380090817996044a6880250503110708400b080b01c0c001305031b0451 = true := by decide +kernel

theorem cover : BRFrame.Cov 948201438 948381294 := by
  have h0 := BRFrame.cov_init 948201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 948201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 948201438 ≤ n) (h2 : n < 948381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
