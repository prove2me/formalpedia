-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:53:47.082219+00:00
-- url     : https://prove2.me/submissions/cdc68115-ef83-468b-a333-882225215104

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 449460431 ≤ n < 449640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 449461681 1250 449460431 449460463
    0x30405030405010f0c060908040806090f0d0e040912180902030105101d0909011509050c040608100b040f0302040b011b1101140d0203070801060504030b060409060902060a0e0909 78
    0x40c0c00c2c1001110725074018981c01c810030000e0307040c40f408184075124035035006100b0800556164a0680b0312802d0070740050086c55a80c1140c81d000003d600049940c100c214800d00d0146103540943d000540200400316010701040f1000742008c18040d041000c5103062a507620b024041c0ea561220320f41e0507803109024864101440f441c1106c8018080d8121000d8a604c1070380440c04400c0000100301010401c40f117900301c40e03448100c8520468000e2460602600500c7c206104a01c0c0c200b01c083c4482c4118032a01c3e00308110640010300b19403002030110040d22600307050743d541c0e980da200300c1d58010341c0500050b880303149082c515070040e60254214140300811480c0780c0e0180c140d41e403a400982e03070080c191603041c000307200c0c400fa10141512008104107010610010307268207003507000030410340d4140c100d24103001c0100014004a1500c10800f0b030301010884010503043c540d450200050301e41468000e4101e0008181e40d003407203410404040c4c0618095031101c1e0b4540d1154402651a41454001084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 449462931 1250 449461681 449461687
    0x60408030702090a0e0102190f0c0f150e030a0c03022a0f04020915040312020d02060a020a030603020a120b0a02043c0f03110d15230a06090b030303040503 68
    0x1810f010642e1a40708429880020f403000300030301040e00fa44e11514601c0b41d803502c540141b120840d0000d04855240740a0324000c101c2da12503540b250400c000a04c0050300e4480102039002c0c440c010394006010044204013941e4550a00580c00340103810503100403409805030030700b00000c1e14103ca62103040314840f0a6000882583e070401c0c012020076840060b0b4003d5001c2240714541e441d0400d10030b44244200340a607944901e1414030102100a8a5600c3c00f10b40098000b0b1441590028031613800404a100040e5505c103030801c203070004c0119500c000e40000c00d4800001c0d1aa907219038841e0818001e0710780031400da5a0051613012485070380600c64200120302c2406010350381110001e03035050350140415a0480c400c1c0c2c20600000c02a5200e44404007003100180708104140398544040e8100380d0f2040c1887c0220340c2c404d10449a000c110300c8555176a40900003150043e40c0040740482402844ca0302c95060071011000940040e01411054609001c40d50043c0d040010440303120b02d8000c0302440c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 449464181 1250 449462931 449462933
    0x912011508060c09011b02011206180f050f061e0a0303050301030317160e0a170304060225090b0303120702011b0e060a0806011205090a0218040302060414010609050a0b0a050604080307 81
    0x200008031b401c00343c1c1001581821205071a0480c800d9401a0054003143c2c035031b440c1714448000941c0d0071242078800c150f0900040c08004840c22840c00d4004074110360724241b241517030010302c031400d8100e15283d43c0500d162000209141e080b1009605a900079900d0174145c1c131034880d03401e032128001e4490b4080c025020403030848840c030542010b5400c01c4020144a025640d803610444c000f02ca051540ba4142c000080c01c01100d5010814002d030b840d1140e00240300740680201180840b240c6205050510b620f0b03d0385901140d40600848040d071001020070b0a072400c150310005e0091480001d6040a14005a0201504c500070340070113807080388c020722151801040b5003048401e2030014003481c0c10320002603124104610720f80101c911844080008011020403401000180b90841d08000100c02c121421f01002c00d034081480c0c0e60164001102103024035900382c0301401000d0b594080c1d08100d15200501c40c2401e0b06800c0845c00c1002250f00040e03040e214420000c0c148100d10892480b688100841c0d8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 449465431 1250 449464181 449464217
    0xd02010207061409130c09052b02040615020705100e0d0809041d0307050709060503061303050f04090501080d1e0c06060909150609050118020912011508060c0901 71
    0x40280800c3c03000c40e0824920001242034032409503040060180c6500e003070070301c250b4071580c58001800110354020316516100300c03103011000f43c0c44410042c07469046007003065403170b150402401041c0080444a0bc01002c810017502c503803d0b40143e5100fa4060402030a6240c4160305000420030300a0410381002299071303407045558840f100683d00103403107550508002a900c0360910003528484041c41d40d801c45498031900b4050325822001c845454090b040c4140c1d200000d44c160b001c00e8080c0440c20701a886d040070b5656000d003402d00c6854240005002c200c1100356013015048034100e008541038a81910710a032500d4140383d900c560402e040e9440b00d402c40d480b8401d10040107014500004005488070190000d880a0000540d00341020085080814400c0e01c03500c402010f81c15401c001550421181c030307803510a401c52211065070041400c680c80e80d2800302a08008080ba4020041d2149961030079107807280c0780c400c031b0410740128000940390b041c00704211820108141d4a000f68110031104c00c1c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 449466681 1250 449465431 449465447
    0x301061404050411060307090914010308040e040303090b01140319030816180608090f0d02190212010f0b1206100e0a0e070e15040209090a111c02180d0201020706 71
    0x6544e9064000c50f050800c0d2a494011406480d031035554400e0241031142003400e844c0d00e85034180b60f400d15440100003180644040c0d506079010422503040c16152400c048010b40340c20140a44085403c2c000040c04040c210002d1640c1d40050782078544600d00f4540d9000c0b000452039000c2d002c10200c0000031003c6080d00f911703021101c45400d050401114440d4205d40d409415004440890031a0702072007032050b800c001000c01c80c002d000051100c0c0003c01c1000f502c0301c0e01c0304185401c03001d2400d07405c011942c1d007007800d21404d007860008110b02543c081c402c0e00a010b101201c20b0180007a4401000507607070100b8424401c03034054104048151901103d01c00524004251803207003a80e594a061800c0400c1c8800c2c00140b40d210494034131818200f00508424580a41640c41103204100e8040241c460419035544058140c100195440740e0b00d84001091140018299201e0302003410f00300b003814558060f01020303c080d0b03000c40d840075901c001d10500500b07020740070f4050b034840c00081005a02c12400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 449467931 1250 449466681 449466683
    0x607110105120f07090e16200f0d0e0d1a04060b03100b090a0c092102030a0302010204032306150a0f081020031801110403030503041103010614040504 66
    0x91030024107400c1900000c009491030f0020007850800e001e14681c0c8054510094034000348902c0c1d5034140046d41c01c0fa40d00307400044200b80800c02e280010034100c1250a00c01c2900114169500022417010007502c1d41c1d070b03c85064001c02c2c0c8191516100307091264040c2115a400241c40300f0b010121043c00940c008020401c0f505130707843d244901c450f80c82c14442084040c0003680c01150f0a070810341088070424004011900051920281c0351000358045001003caa4200010340c60a140302d21a600f01c80400e40e0000c0d402d88107550b84441090381c158000e100706c071b000c0d40d0003a02801c841441004003040215117580154010004180491048002c02c8240c00c1c005081c0e807a1035070790322111402c07080194081c6040340c0025400b44000300c02d9004030691000c80b81c04a044c20f050100410055000180161210602c480405c0c52617407000d50018070b0100c0b2002e422600c0b9a600c1c0b400524560013202c1c2141c10048800d00c01c480b50405001d1241600d80005522845002c6042400010040104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 449469181 1250 449467931 449467937
    0x1b0f0a032c0c090f090a030c150c05040801050105040207020a0315060503010c0e04050c071a0406140c0d0b01090e0a020f070206030a090b1b0409020f19110c06030606071101 76
    0x9003044003201e000c92403110700101c0002925042000a040150f5010000e001684142070711003000038074100841d01c1d600c95035042c1010120041503003440001710482078500300a00b450003081c410403035007104c050802c48010000a02c12607881d0000d0100360301944000a4201100d071300280300041100300c1d0500d5007005103c002604550300e00000c3d00b03440101c20100046008131180305e40c581028007945501c842e0242e002458907040703640392801c3d00004ca07180310011114902140800010303030400c101015452070f0001070350420b000050703469400700d144000c07001e140551420b120b501a0414104692a94202070620f41c0e6480d403480181d803000d2201c5013100c80800c111001070b959800911300500e94404002214001c030300d00b04000c3c13400600440c0c0ea440022444444c40d9641008682c16140301c07640250301d410350008480c109010300d8054002c02c40e0503229410b03034550301c40c040440f0800010301712004c051030102408103502c4252052030300520104a01c41c003003031030501c155450b484189 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 449470431 1250 449469181 449469221
    0x50417070b0103081b070f060207060813030f1b03032a02060106050a09090501090b040e0613020f0a0305010507021522060902010512010303110c100e010305100515031b0f0a03 77
    0x1c1c030000e040c506c4035041500314209100c41480710070381c10810800580501e061504150a01144092500c4801e01c1e005081020692000034454480c03001030000940d00301003254001658940603004c1d20002c00c000c1d0307402c03042100d402c008841c41240000100c8040c2c024055903401d0140444072035000e98550421301c001500001204a524440c1c54000d00d000c080004400703074148200004e8944d056040c899560002040c08599144444881c1c01242d0403905c076159484c000d000324240c1001c03588050960351078070b01041540780c1c01007003070010f9400350309100f0032541d2107484000c4800310301d00440d824111140780700c0c0002160b540c450041e0b1801410031506101000240b82c00c0078100341c000302d001032540ca80c4c06105420410100c40728043c1100d00740f02030005008003c041d0b401c24000181010b8480c008034003e144120030030006400c0c051315802012001100790100c0c2da005950b06031040385410359650403c0b400e003055805940c0d902d404d80e4603299003180b00300c000d0b000481111311440108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 449471681 1250 449470431 449470477
    0xc120515040b0a270b040204080d0e0a0e040b0405010e0d09031104090804150e04060b0a0e040b040204170f06010305032a060a14060d150e03040e0a050417070b010308 73
    0x60005100038500e95a13560039120101003100041d14132440704180158010700c400e00c5010804070b9512200141e500d0030701454041c540c00580000450340c0285d80b00c010620a01082c000464000340c03103140240e0081c09109500c0d0b4071155601d2151402d00e0026884140610003d202c0c203401150720b50000300007050070300140d200c6800a43c020b03031002400c10743d4800e8114071540c1085017a0606030701250208030481c1350183e01072940c86004030507000c008000c1c8258555603260b522440c0f1203c0040c2086441d40d4032805d100608404900400e0154411000310404603240091500d0589030301101941c00d240a214450100740c0d18451880c0c16000e0441050b544003000708a2144031b00c2001001188c03007202d070040c0910801d00500701c10f01800105182d803011989480e00204506620000000d4010100810600358015a000814071101080a000007078021341c00403409207014081200e881108602e038401188030301030340200b102452600400c04218520040d1101400d00c80c0c0340b0091860b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 449472931 1250 449471681 449471699
    0x105070312050f0403020708030c0606060f0d14180106030c06030c02030d110a090602030a02071401020a051b04060e13080a140d0c1e09150903150c120515040b0a 71
    0x22243d68048a85000811040c5130381009850000c02d00000075501d45000c1413a110389441000f024540100c80001c0d1008201a500e0100d800c04c415403801008845c4000510f1088040c2c04c0d5982c042400c0c0031007410001c80c206201d028200c0345e00c01f034008807080ca1b0040941c05000c8094001c429030000b0300c440daa4109060080c4820a100001c5083d5905020134007d0140c0002d0b03040481158420300c090030905400151020903900e444000d42c8084400c100101d14200710741c5001020380c0290751030078801703510315501790b800d400c1c0440c3d0a0260700e41300c0103041e000c150100c0e0921201804000e5807404217110000600d020141e9180820b540f8240c0414800c0c0b990103200c08043c00c550320711050301d1a5a01400d50500664028a60410680300074002043c120030350017046664410b201c10a81d801d8040c5400c140116401085200e20320150441c1600525241c00c030b0001061081d03079110015101445024464400d912041c0420010b080500c0001c00d1204003541d00030641520215180d40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 449474181 1250 449472931 449472941
    0x170403050705011412060111030c0f06160e010c150902040c0c1b0b040603050a060e0c0a02190308010b0901030b030609030a0e0f030319140d050411010e0603060105070312 75
    0x10062006050307040c41e0000040095078825150300c100d440601c074242120010064058102c4800d01e0140310309003003101081d06500c102002150713036208100c0c5522a803407020945510942d82901d0195a4000e00d050503100381011012440c001080c21100000007800c4021600c4a0320080340006020b0090380d0205007108c0354084800013103414148008104120007005105030714444980e00c030b0742403604180ea0807030b014500411040c59101e00000c2c0c0003c18a6100100403c1c602c100885a801c5c10301140c1216031000c8200c45c01401800c058400d444012446449042d50554030b6001a80c40d2500c0441180c000020060406465403000c0d200d980c0d040011038000e0900e03801850b40d60031100c4000d009034240c0e050042c081d82c0e1103d09400c503030b54040103031007900918000c59403c650300c0d40011074900300f21003441c8180030340224044407002015800240300da03204000103035421f400030005640c40e241070a0881d520031010400101d4652040c00984007440c420300b45800e80d00007046140068078 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 449475431 1250 449474181 449474183
    0x70c0e0604051302100f05130312020708061302060c030c0718150e04030e0d050a0b04031704020d1704180f0c14090108040305070b090717070b070f170403 68
    0x248542442400d00e41072050781c3d006001c0f40c050314000801c40d40400d800c2600000a081031015503000309010900a80403143c040020120140c4180e40b03d284c10032035a144110340e44014811200c022859000001d07501e4010300f9110043d41000081d5400c100f9950300100101816020030f12403074058010070003e0001405032005091202c0c2820f102c41801c0740d541070014454032206c03540400c2181e401031000c503007182d0035181000d49024004003085680c0c100c0c810042452251041c0300c0144003440402d28003a80c403a584004400030020750288203c0029031300a075120407c2c1c900d4038005005440803500c515000c1d105641020307562034868040c0d4148180002099803504850807601000384500c40c072003202801c102600e040c0f5021851554060944511b051142d804003044c149030240069030380283c4d0040340040c0c5803402001c40360b101d650b94482d82c2d10600303125081000904000c110b0030240d0300300f08000c134184880c03901e40814400c0e440805680c0c540e8403086034901070503030790014000f0f5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 449476681 1250 449475431 449475449
    0x5030702061323100b01020304062102070803010b090307060f020d0c0c050301020706090c0902030c04090c02100509010207060b01020c031005131407150c081602041d0c03060a270503070c 82
    0x1424198064085d24600040e460441d0400c00c0b003030205540100e54605400d028644e044603400c60300d0310715030081c881c81601920501d004800002d1a03e600001002244400c2d020340314810303a111010f80d8204000e44440703002d600000320801d034162007a03c100301480e00039075101980e140da034030200342243d000d41e90a1301d841d6165002c00c0148175221300c8203802016101c5046255182c0034100003040e0086000701e1403050740310503000c0d5030180f00300030b0301c800d44264040411440c10004072160003980050000c480f0346084c0505045558008520344400d51009400742c290800780b4040580280b200a140006100100e580c8001240be0302550400c641440c00051540a041c130f446200c0c5048580004020041380a45000006a0901c203589103483c1c050640180d0030366a20020300600852051141801c0e4503881d003504114001451803540712090301510350f140c8a41075010705a403c00c0400d80020a002d00c0030071003604901c0c11504c0e5040c05013003981c0c10b015143d42e407a6421800d0398002200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 449477931 1250 449476681 449476693
    0x10f030b0921041d060a0b0c0319080402130b0102031801090f060503040b0f07050901030b010507020d08031e130b0603190606050a090939080307030f05030702061323 73
    0xc2c0c0b0f0500740d48000b4100010f1a00107181c5403580010f06c1c411654003601d00c175000d01251008500034100280d45200e0001841800425010800100b106208880682c0f2410082d80c9011542a0a02c17800c908190706074003440c5440ca080f80c00065101ca2520484d04012200000088100001c98044058203155503101d64904050800c204001c0000c0d02081040b48101d09200e001f94000c01200c102c4d03002030902140d0480d400b4016541401141c4020750001d8111402c6020484210b0082d03110300c1011044d1483c0c0d040c0c0c20b40308001c02c0002c0b07410400944540c020b03030000ca141300f007104e0750041d0001c04880071500c007074210030301f601810383c811030342141c4030780f004e0206140617510325020b00108203080100014a407030b011491001260348103a010000a98403590080321400c103190301d20b604a00c002025611031401da6282d020300000d81c0000e2020300e0340101d03d44030750102d034021884e41d801040075465500c0700d001d40843c4504100c2d0241f4101c20144400d04041d44551a801800e1000c0e002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 449479181 1250 449477931 449477939
    0x18030b01230306070203301003022b0609080903030a030207061406010f08090c1c0209150d0b13021002010518071a071511040f0e010f030b092104 64
    0x160900300c10050b40320f6000341c0108074216034004241c62a50708403442d0109068106410f1281780c240c030107010a0405940810080312890000b080303401c980c4251003410b0111f000104007001d800344082644211201c176501c0d500481c8050300500900ca000f43e42c40c610f80344107000083d01e16401480310a020a4010401d10103114070740c4501403201001003c1300d105d900d071110000b01910032003103020042c406401c2c007280c8182c1c4200f10070014140c01800c0700c2d80ca20440001e03030300003900700748040784504c0001001841d2048030f081e1811050401500500aa036500c0d9a4052940002000c2040003400c90442c0005680e4000070904030200c2c07a00002800d0030030b1866009a201405500c2c95a0360010004000202c5002c0c2610f2514108074005901c07444649012041c80d030190340c00300107560800319000601a44603001344115000040041403055413001c080700b55520034424480d07031007400101000802c018030001d50f40035425800703440c154007100f0039600c0d46007044000e0f90120a00890140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 449480431 1250 449479181 449479229
    0x215040e0f1006080c0a0c0209010602010905070906050102070b0d0f06170105240411040306060905010e0108070b030a020d020d0f1b0c020901050d0f050f06040314070b010618030b01 80
    0x35400958074400d42c461070b410702034094034458000d068205000030010301b1881083c030071401c14101e01d40c000c1a581c650359461800a0280002d440141c880e801441c500080c03120240c85107408480040e000751414500e000c0540c01e49400084402c40320b17031307200e001051141c0c903940b00c0c0a001c2c00088014940c0300b4000c24643e03003110700041501c10300e8401d50402440c8031900002024064404a07000b01b0b1840b503411138841c190003240c0c4001c0159061150109600e07910fa0411416203045008445040e07030380d465415500c180c18840c000c8840e6040000c44c0800c1000e0300140f136610b010100c00741c035013090070604400720794840c000c41c04216968050350141a24400302034442004600d40702d540d01074580c001402515040c0301d4203202d1419520300504100382980030703c4a440c0c2081c2561185c4040700c0d40782c3d03190b000444040f80050b40041000745002000310035079060700e400140020f0160708004059034000504040d408080c4800d034000000641042203083c086c001c0c2c1c0500000000e1004001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 449481681 1250 449480431 449480461
    0x4080a0c060f022406030c03060a05010306110712050d24090f0e060c0a11030711010f09061b05011803021b0a05060d0c0905041a09010b0a020703020d0215040e 70
    0xb0110b4000e00c60340420605002c2d8440304a0488000d40a0b558603140000380c07400620004264050141408009c0c0900c299804141228051075051158400d81880e01c103051046150007410400d4070040420840c1c41a4003500ca00380c64810f000400640440381422854107401c4081e1464880c50400e00c900ca4040c00340f448142c0c4958070901040000e440c180362101c0303004001c0402c1540200301125400d00c04c0e000248404084015a070b9551603904090441c80c0958440c0303408103111030100350680e03116045040894807940e45044078840001c2e0781f80255050100155040d42d29000c0d24210902d140c5d40d4002d1491203900104000300151a0210f804407140000394480c0e12503810030009a15030608440c56030004c0080024407022000055407009299049541c00072b103042c1403440072041081191801040c2222a08096a42d031500c1550780d204403503190006804c642e0003000103042050019050324401040ca02c10b07107070042424a05a045580f113107142008100074054150100000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 449482931 1250 449481681 449481707
    0xa111f02180906130e0c0405190605011b0b040c030c1701060504021206090c040305160e150f131b03020703180311010507080903010504150b0a050a03031404080a0c06 73
    0x3100c03a141c6001c0c4009150324241210b009041a201d001d82417881c00103004022101c90014810495400c1141d2900c2442503141c290840403440c20a0200d807a6000d86020a0041002002682018007179580c0149001c8040c10480d0b0080c40020040001058080b16101404c60485005c081c110625125402c0d140c00b54081790149104004101c003d45200099941c4110240c0d540810381e151280d05030414440c550003e0500e003c0c4203001c0036000755010380101102d5070303203601e40d0464440000045d109444060b9007603014000085164003400d0210008006407036036600000c0000e001c41110242c40b00034103203400004d40c000756a00c00c041e008072103201444101c11510b402d10381590383d21024184620700d01814000b010543c41e003040b0b202412144000300140003449a414145000c0002d0f205108800108908007107981c4164100302524030708950004140a01480ca1914242c3d00c40140c0104050800300422001c21056401c104624000c0d21510b00d5070303061450300e08020f0800f004070035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 449484181 1250 449482931 449482939
    0x1020a0f0809031506030a240603060c0305060402030609041e02120c031e2104090e0601050a1512020c0307020d1208070302030c180a0810060e0603120a111f0218 71
    0x17400943d441c001041248141c0c0410840c0d4420250013004c0d500300e04d40d914100c2c80c0b9050a0020003006aa41c1207805120b100b030700c05108680391481040143e0108555068001d1107500002d004100d83c030070403108001d003200080307038400507540100d8290348039042c07000c0642d80311244004c0541400c00c001030300c50b003000c0036041519110600d02d640b0307413258008101c40452022500c02c21016100200c81c0180a01c0c0310402c040050500045d450701402d1103140d00c107003042c2c0000141c1155404041e03441d40c0056a51403480da461401110080d04032080070845032106122080c010788806a085035901c2c0a0081c400c2e01003000346004001000c001c00701e0f0101801401072100201c81181640c020104010400c2c000e000e400d4081080c003046039000c11458841d103100c1c55580c15030f951010040c0c0d010800c0315409a40d0f10f00905654446074401148030300380070448126403900c244007034400d44500c001501e02e01922242c44001c603810420b0320240725a0b00103281d203d42d00290200f5469400c0940d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 449485431 1250 449484181 449484223
    0x1e040812030402010f03050405031902010507110102040609051c1209031506031e1a0114120703030203070b1305030a170702010e060601030c020f2e02030105150901020a0f080903 78
    0x143c0000d01c180d2681c5038000c181901c58000c6410014240161100c000d20300c00d0b0325201c25200a40280a0301d8180d82c1030000c219490b524211416060080740c05541c0d01d6100c00c6140e80c90442480501100b03150721050310401d40c90280001000b591501d20b403241c41d561803203803450440c00d095500500301000c580b111031405102b00001400c980c0281e8503240ca015501c8201c0c0d01c542401c0c01a26a807455126910f6410380000c90041c401006007950f1940582e844280034042c40e40300c5a0342c0d01d003404003501683c418404400043d000d4a04164800409240902800000d076502403940e00700c3c0240c8404100c040710394403407c0740c3c4184900d40c00343c4a40700034018218041116503e0311030140000f4100350301c400144104034000c024165a41030700f101251010310343e140020f241074045c0014024172681400d00c0311948007040c02964143c40004001401034004c03085030aa03031383d01292201d0f0550003000000c5002c11811300d0610a214015640c890342d80d01941c040604107008600d5102d03000d038102d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 449486681 1250 449485431 449485433
    0x190b040e1f1a010804061e05100503300c061e0f2404022811030c1c0309020d1a1006122c010c020c010915141e0408120304 54
    0x3000c0b03202020801c1c240908281c40e603084c4000600b02c1d012440201070b80d031003d00d0014079071a61191b1b124411900d00ba05245484000b00b5498042000a01d240c04081c2c150f640d0711201503c40184190450006181c07a200c601030100d400c103442298035050304440d116401442d0684142100d9004803a610a00310600d840303d00c51003500c1500d5124409040d4020003110282c890354100ea6021502000400c80007161490392801c0c9102070241d1800114440005094500000143c40e21302c00794002070301c03c16000c5146030b418804580b60b40001c16031a054070102603194520300821081c09140c03043d9441c5811114600d0040c4064496240010010070801c03905a03c440b0b01010003081c2c2c00003180210040f2401c040d440d14503001d420b0381955500001402d00c3c01540141c01407100f40c0c013525101c540b80390064a01c800036125400150f103944089003085885444400118441d513400d9a060007141410362824480b0f00c2c0010203003a034005000d100641040100389607007081110711b28914541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 449487931 1250 449486681 449486711
    0x70c02011d0109170606030f010203070f0c02150c0303072312040804090e030315180c0705070f0b0703080105030106050d0f0c180603060c0206040209190b040e1f 71
    0x209003100141d003685421004070382d078898001100104031a0700206800500c071391905840300c00965001e44079101d40d1070385154562040c001e46e17208140310380f19480c00301348180013690411907000d003c9900207800780c505c8030000c0c0c000c80500417154110000355141c4c0380c00040a040340d0880046500b0301044240403000e60f040f9441250909041070311520420b4943c1d00d020504d80c0101d4000703000003420301496414001e07000002c1d40c8200080f43e1b05900350210542440300c1d51106102d00c480391003034bd200164503002020010000507100301c2c02c9030f02c06551000845408210b5400c999500303a00002d01c90b05040d44a0003580c0074040071402000b0091074480044e009619a100040042003071940000070b1222901546000300817070309403c214007682c07201c1000104558001198560300d044e80c00c40c0064400141a880303a079014100034080e403107450140c042001407103017400d0325540391020428261594028140b1415001c001415110300082545050300040c7c88028030140c540a52502c03c044 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 449489181 1250 449487931 449487947
    0x30702060318163201030c0c0506041a010909020f01050a05130303050d0c030e0a020d0c08070308030615070201020a02011b150501091d0307030e060f120402120d080402040c0203040f06030212070c0201 88
    0x203000d007170010707032440c2603102032301c0d20b80d200c0310090714901840c070811050000c00c44070402c4152450080144981e21400c080b0111111480c1c00307034025004841614aa50040b0000c0c03c2d41c080c01d0174400c1c02d00c0704190310f0a9030391205800490018002044680d000f200900524843c11030030b0a049c01000c4e2802800c580e60448075001911034610307010407900340f011280d1a032000e401c4110a0719a041c2c1c690601c1246948140c55007801180503254081061041009079892075505034044c1c40780748400d800440d240654441d00c042e12034540c051030800114030351503600f00703600015400f2515600d806003000c1220003144a65000c448804411002d030140842150300b4160b050404140001540c0003003480c9019140101120700f8001030300c1c1e040c11a13000c002d54800d51084078060100c807514805152607401e6030385040082030006006c01d0051810380c000d84003520301481100d040540c1c41c056100d444c0c19030751200c0c1c080783e800030340707140190081540c1c240d0120301400d101c04102129800240011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 449490431 1250 449489181 449489279
    0x30c07030308060406030b06060906040e071d0a05030604060e2404020306071403130c0506070501021804110f03060d050a0b0a1b0801090e2b081803070206031816 71
    0x4000020f4515162f503c1c441641c5c0a043c40800070780309443d00d2000500340d0b00100c000d40c9000000010180c1145c581500b0001c15100054080d0890703840b0b0740e6880010f400c0c4120565440d020340012001e440750226071000d0b010a040c121204181840d005040c28880c02038080020000c1f00420500f521002004a035080301182041561045860401034640c10f915046240e00c90743c0000d0030004c0c413230150040c004803011200d034207140c0d844020810040380c040403041c0301141018030018140051220155621200160bc0000c11174503d50f101070a0680e0900d003210503240d4502804402d1005201d200c1030f10300c0303400411650940d02d00b0007410701c06051148004141c0c440190181151051001069601c0f03001ca900701c10249600a20341d07108540071024000440301c50000e480900191104001803400302e000c2c0d440c0088a03000d0105650004280b000c036001c0c05000200c900170104140d01e540c0c0078416030900114189140038070701500c2c0545802c1041c00400072080c40d50b10200e6480f000e4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 449491681 1250 449490431 449490439
    0x30a091e0b07050a050105040b0405160501140a030e01141602030f03160e130e0c1e27040602040302150901200c3a030e01030207060608030c07030308060406030b06 72
    0x602c02d43d1402601e0304034001001041542031070f06001c02c0090070310030b04e40258440c03810342e04149400c0d02c2a1742c0d180c1103442105c0c002188004861a0a0700590061502c00030358a800704d0840086442c55082d5003642e05000300404010342007108000300c201c030f00c4194240c1840694a001d40e18600c00c1c00a010150500515442c0d0b0592640e00794007900541080d0400a8410b410558403001084014003101c0420f20b02d42c050103101800600d810310031000030454028105007410700038401d1048402160441e4038440725140d2443c07040114004095104900c69130003d13965070b085106004048214035140c5060000c10b200c021003980e08502213402c01c400440200444850340c03e0654075103140410303101d0300118442c8072040050750090420005029503900300000b5210701c41425640490803501a0009100341c0003851550f00c02e4005201e80ea015030390124440b503c2c2c101441c250f80c8455a1500306034802c000030010542c0081d48154840304c103d03020001075295844001e04e94000800742ea03c0717 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 449492931 1250 449491681 449491687
    0x90a0f030c09050604270b100810020d0e030409060602122722020403020a17100b010c02040c1112040b070f02041401060903030e1005121305030309030a091e0b 70
    0x116444e83e500c0010701e441e801240c0e6004100b04074414a100c2030050042e1f8004007680c0c00903460455091500c2c0460346030070006c110700300714600c4940c001d402003080542c200b42c446a140854402c20406040640800c00d8001481d61a1010103443c214522242594022051148849100404102103c080b00c1080300202c80184a000504c05d6405000e006602080f10240a0034501c2c860340500300750707803083e21001050354542c02c01944500c4013162144450b8000342c0190308042d00ca42042440c1c4c0f1060416018071025540090180c1c6c054100c1a400104124011143e01c0b078104248200c100210b0b0700d06140504001e4561902d101d16071002d0508608203000b403046440f2580040102030076010182110f50b100c110040c82c031034103884140c1c00513203030b00c107140320341c1ca840b81c4000d50246103520740602d000001e600600140d0320040020240c40c49809101d00410001e0005622520010002e5551002030500203802c02105801800d0300003400313813001d00c0c94031903206800e080e00c81d403500260f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 449494181 1250 449492931 449492941
    0xf070f0e010b1b10060b040302090a0504050a02100c0512180103111b03160b07022107020f010e0a08030c072405030619030303091104140601051617090a0f030c0905 72
    0x4945000141c001448070f2174510001407030700001010f0403e807807007110103c0d0300381c0310350481606031202610050200c0e0030210016005103452250135803184064180300f0f0380444240c541c5420542c8224168100e14000204500c641d11a1551030b410341000f4202005240b0b070340c80703b80e9424022500001c104600c54a2054003440d010800d07200c180d41d0512135004407179000c1c034160b102d011f001e8402c1d0000d4445c04507090740c9203031203c00010100c2c041e81c10a0341060078030340070450075002d140340f100d051281d400b1031a90242c03a0001000050000d40c4011a41c940040e03400c0c600c2d00400e64000d60100401d0313685c00d0442c0302c0410030304102040500e0000e49036214400082c0e0308845503030be540019099043d0003c10103405400403003c9174003e85200d032401d144103041c0010399402507903615100c400a000216258016000b80048140500c06641582c1072990381d180817018402c00441400c4000c600c020451425102d400c1c058400740150354091807866551240760000d50042030003d80d2104001340c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 449495431 1250 449494181 449494183
    0xf12020318010908090f0307140405042f0906150d020c03090d0317010905010806180115060c02100302040b0319090803010608100506030114120307050f070f0e010b1b 73
    0xc0d20740303092003000300195062841c03d00c1c090761250b0062809402002580041440c1c0480d04c0c508036100b4440740140b50040741c00700b0000b080028002c40b070350348007000030300000c400c20286180044446144409105200d0080210001008040c00d104c1c0b00c211140b24900300030b10003a02d400e04001355015884070318088280342180600441550440018107101c4180360b44200e140310848540c07100d084841e41c84008902c00d03a02d007405400d4040d171100b80495a55010080160100c28510300001001c8401d500c4040740d218803a84441b000994001e000010b51900d00c4094640f920b05080841c6484c0c90148100d442e408014050445030300d01e42d0700245e40c1d94640d0004a6941d46c01100340b940c0750f0b150b06002c0c11000c0291440c1c1601c01214402040c541440011681610018074148407001540341c10030071800a41040440340e030000740079010015404100d11684a04034002900d2464148400260181c24036800081804580c00c0100407501d040021580608030704e401c000c4000707803069050b0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 449496681 1250 449495431 449495461
    0x1e050c042d200d0501080a030c021215010b04030203011805061308070b0c0414030d090b0f090d0c0303020f0102030709030803131704061803020a060e032e06060f120203 74
    0x210b200345400080300444082040003002c0d5828100c3c0d0800075640c96210584d682c2119a00007404036160b1500f010240c68100d12280b01c02c0008021901103040728400000c0d07405d400c0e809240758034400b0a0a000b113113401c1c050018900c1400a0b8220780d1200d40d1100c980e200303005807071004265180c102070014011020110b980341600801c803490300e410030014041c020340c403c2c42030401806048030070140174640415802c14a49455540804c1181408506440740c1c6c0110328144004108020f070800907141c039032000c961540200c0300340b0030781c0c1d20b90f09000c0c0c00e0010805441c11aa481041081804c5421001c601d050faa0444c035646c0e12941c5803003410070700b083c03820400b8010428208a00221144142c000c0054410a580d01303500b46400385a0390410845034000298001408201032007003d00c1034010500e682802001c03156886d440001d4110f801c0a0006299a000b030702404100c0005507a000d40e00c0100401c0c600041c04071042e4200525407610325100800707664000000c1499007481c1060 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 449497931 1250 449496681 449496701
    0xa09050d21050705030a050301050f031c030209010905030115091103090a1712100311060703080f07170403020c01090f0b090108042f041b02030d0b06071e050c042d 72
    0x3140c0c0d46e098103000c0078195410901c14a031282a00c100b01c0c0707126040100e0902140844420020090b001240081d000794003c15180350421100601c0040c440c2e07400d0140019450190403030903c041d0074401820188c030081c9090f04000318042083c4041d03a174002451981c416009003035016403544405410b091313807181c42a010410b81e850300030301010120001c00e440031240306a0581581c0240d01050100a000b00c04014010403041d000181c00b0001ca208030690142040c50001c0078500601800c82050109890030303001030b03104051307041c05541c02440340350241840e002003440c1180750000d460214410302c0e081504001410000c6410011014184410142560302c01c404c2427826240e81590046c01403c0c00e44070300d0411032140b0002c0440a840c40304408141c0c081c0d440c0050030140070700502075150070990890001c002e0100400e400b0b644440c4500441b2101b00586810347c00d1003483d00d0506082c0910039450240da14980003041e500c01c406d141880c0c24640b441070b83c0a402c200003007804641c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 449499181 1250 449497931 449497933
    0x30a09060f0203090f0d0c0212070f030302031801140304030e19060c060b0609030613170409020c010f15170c09150a0602060c070f2301020a09050d21050705 69
    0x12541c103410842d802462240944c0400c880300034032940c42c01590340044036031040100e10140e2252005d82003844410168448010131903c4083d5103400c4280d130703d1582ea0069005810200e00303040c0704902a90803401422092038110600004144461032501c005080142400340c05110755001d41c403140348130305c140380d03001801030040c65403400040c105400001e011150039103031007445100382c50310505071503440b0f070003600a1045a44404220038003580310503003130328000580404040b4070300c110001800a408100c078090b0b15107004440d07803070a454030003020f48402400c0012003001c501c0010184801c5820f01e01500601e0f5000300030080c20304005941040d003009101c01042414040c4050488034168203440c11b00420b81d81d035034204d0f1169400d86807010008001c0280c2004580071000c40c03034103640a44004008603210a03403a4110b8170206156100e08e0b500410240061a00400748100502c0103581c54041010159202208079218503034006640c062510740c540a03a22074015254441d40c008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 449500431 1250 449499181 449499191
    0x16090603050601032a0201140f040602220320030604150f1401090203060a150807030507050904090b01091109010e040906060f0b09031011030601034b090f08030a0906 73
    0x17a81402c10600d090381074000d0b46c28900040540411a00c0081c41000a0000103010741c8503030f5600c0e00603500102500381c4030780c0100c481d0780ea0452001d4403000210722400802c02d000070107050310f03c6041d8051401d6480307504444100f00105282c0c0b441d5800341c480b417540c009954044840460010802c0c0c102c840c042d41c0c40880086004c0b09503600843c0200c008480080446d955264881c0c441e520306160b0b000040c1444000c0381c0316a0198010036004000c40c24240e0400071620041000c64803241c809a43c01e501c0300c40100101a41c501c540381076100505c041c3c030f1402c00794000117440aa42502000d014a07540e001d00d00602c00d4640c010409404040701031440e280c0e0354640b00b0003d4120101a0740701c0c1c016141040c400e0002d0f40b044003440796040c0c012a0950b40c0b028015401420420b13009112607500c441c0c401c0c010302945011402070001c0c41980c3d125486c0c0d03100802d00303013000036007042115481c0414060104041403024010580e02903440c994035581c070003041001e00031400c0006d02c514141 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 449501681 1250 449500431 449500481
    0x1406100501030b030c21070303030b040b04060518130f12080903180603130b0c040609081504061503020319031223190203040309030303140606040504021e0a171609060305060103 78
    0x10340bc00c08111604503402e0040184075000c010845029202d80d0380d200660816001030a082d17100341a0b8080d0400c100c2880da0307017044d1a00c41c102d0584680440f1a80507440f00c001725130b41c1009805421606c220000c5040100450f45035260001004c0e101c0d11641c00440001c00480050109207801a40006900e10504080e0781d0b100b5035401034011480030440008021034031820024620b90b0071814a804440d06855035280c90000b0541b51400c0444400c0b4040c020000d0303101005000e014880301e03100d2100003c00303410020400101c0303111000e0407030308024004000301c85421040031242030303d4000d042503480d8011415082b41d901e121404078540044108414103030000103034012a8000e45040c03060a900c600c03001071004d8110b070300560011060005010328100742d400b625004154610b0690032502501c12400103800c0040c004e80001c5581e0340112580c80b2165010f03411503900328000001520542c0301600d001560b0041d00b0806a0714030009070719078402d400c0036100c2014a07107011802805 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 449502931 1250 449501681 449501687
    0x3091201090203190803220c060e15040b0d180b13121b060b0402040e0f090705010801080a0605131407090c050a09031e1406100501030b030c21070303 66
    0x29030700307040e4442d005542d540e070150620788107040099603101c030100e031455a8584250043c0344002c1800720882000e420400005260340701c2d881c02a1401e5107034210b19100700070070045d0440c0c612400e05810b0300e05000030840b2903080d5050718a43c070b440d000c001c105611702c8030b0003420059242d030010703210700c080078140200052060309601009018403d890b0300c80d040d01005848802c0c003000703801e0412410081550100b2a1a40030640f0ba510040000d49480d13911181d210b6128000d581841c2d8003494501400082041040f641d8014030302070078072140d990b01d8400324540301c0c80034403000b800f003640340e0001580b405640940480d4003a80140c0f0307614103080d501b01a039030b2008180207400300c0794907012420305514012415510640116a24240d03a41e0031555204011101b050300041c0c009203908001c1d0004440a5880f03030044017960041c080d40c5091500035100105030741c8000e050619024225009407000310328850f00c8401540c40d1040120301c0041c40d030a00c050451881180e000fa4031020080642c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 449504181 1250 449502931 449502941
    0x2409010f1406030108251706010503010e06040203060103030c060b150705070603050105060d021e030103140c01050a0824040e010c0305060303090a0e100b0d0b090a06230303091201 79
    0x600e40071100d4055038120034884030380b100703024048165006850000380e003030442c02e8180c0110207981c3c401c1c0455644218002035100300c0c00d00308406410420040c40715003000d1145140e0815068001c1040e41001c0e0040703600c881041c00041e04218003a045002882075541109822450142200c039004d0020310031040da5400c504000c640c07078001c002001619074881d01610b4140c1d0130040c0014600703c103000340791000b54040010000f041000028400c684803003030019600850007401516142868003103907600740541c3d4a1060706000f03080c800b002085501440880d400064802c416203500f00c131000211050820b581400c1e4420f0501031003104418040d04504181d14440c0c9080c41281c550301c04040e1a8001c0004503904280101e1040141c400c2e0491021f80103180848400034140d01c40b52016510b500105402c445107448402200b0241401c069655200100b840104072a41c01d040c8502e154000d40c0c500f41d0000c1481da0b03071a42c1c0300d5174184200c03803070190002c1c61848a030280e000030724060f203 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 449505431 1250 449504181 449504189
    0x52b090605090607020316020d140a1b061209260c0d0903050604030e1203040806070f050310090c022b030615020a030f0504050904060605030c03030c03032409010f 72
    0x36050102044900c500002c58900851441e0003845c20000c0361086203c850320881010790f030080703000901c007001c0390146000070003141480c4c010f4a20ba003a103040c110000d4041180001d4054001d00e010020964400d070440030607910310001141c00c15050038000310402000e042c0310781655565881224040a201c000c12068840c0304c12750f14114035480b0305a0b0b00a00340d210140c0706410040c005030008c2d118000c0b08800c804000c1c00d00d04444620081d4901c0d5801030b4010001990049081c41010b0390021006504610207140c40c40c0b861401c40c1071020300c0e40b224480c0079803c58541101700c8200d0700038480030081d903000040035040e011150750b410030203101295208020a20b840c3c80466130005405000b032545495030020409100c050340c0480c0d1141c402444801040810300000c18160398a1034182d015901504011407403905000405003021319400b0002e00c6680200300301e0302c800c0808411744c0c0c0d002c10b42d8541c002c024807004155500580c0b85d0905035602c00003000004c2400404c01809d00155 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 449506681 1250 449505431 449505443
    0x51b060403030c21051f080607022a0108040c05130b0a120b1801020409020703020c0a0e01230d050a05060109050f0105060d0b040f0501140102120a0807052b09 70
    0x10000600c0d0541c1e110514090350660313843c02200e107240c1d20f50181c20440d0010280c6c12245044d0203168040c2030401055000320307089410175010b20132000d0341080f0051030b46000813081c1401440030304000c00207000342c640290500c03a24500043c20300940250700c01c0184000b404120503814182201c0c80107006d00d403001d521a411012020940708801c81181c80c205d940145220307015160600e84c4040300c09411f0302c112540d034013088041202d24050020700780d064032940007422018a500104064031109130421000c0801071401007121240c2030070084a40140e803542d00c15508403940215001d401000c2010b4828440d03942d101d01006000649213048a0803e0300411030b80e1940340d54480e000e0801c0c404c041c2d201e44184160101e1000a5104402051004000082030b84045000800381d42c1e01368060442280001c2c011141c2d560103101c140c1c041480036010301d03d0304407030b81070150000d100500040100200803d1101404906403821030030038203010000050354001800000c040c0846500445034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 449507931 1250 449506681 449506691
    0x30d050a05060901052e03091505060616020a0803071209060e03030a0e01030f0f0e0705010302090a120813030507170c010804020108060409060603050309040b09010e16051b06040303 80
    0xc4056911480303024010080c0f000c0c8080e40382900304642d003d01150103014122900510700807402d0f100c0000881c1d02d25a8801145034001c5082109401c095400103142e43c038100810880d0343e070784003012540280c90011078104494407038008a81e0980c03450b0003220303440c40300081e0701e802c2c080c2100c5034401e940703c0e903174a03115802d8542e00102c0d00040401d14035034041c5c1c0240540d10740c80f805184054400320042c0740002c0d44031802c0c850b0303a00751050f4004105146a60300c1a07650100e80038071184010380b40030308041d8501101e80c1c000c01c510b1410303445002d15001d01c440c060410819410f084503080b44084880c400303460780f40d007041600e030304903882400a040801446a046c000e0089581d00c0101c005840356038869540d41c0040d0703580c110080044e60301a60b5001094005107440c890f00c4d006d540500001e6881d0b0000b60300707203c00c9403180c600b02c80c0300344843c10042108004034007038076900c010401042854400701040c1a5228002c400c0401d200380d03450000c8a000c100d0004015101d9400f075a02445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 449509181 1250 449507931 449507941
    0xc06320c100f1508030405090a0b091302040605010e011d06040314060907050a0305150921030109230c0a1701120b0c03160c020307050a0b0a08160c11040b1002030d05 73
    0xd000c0000e110384d4099810610040046d45011284c0544c04000403401250b942d80100c0010807021084452010000340c265542003541014030810014041c282040104412210006080c0c86c01c01030481030603c44020701c405240c3c41c1c40d42640e00035a40004603451030700c45645072a440303040850700031000d4802ea01000410b8a807038a07180c0116904140540300b02c441182d8411840350000b003190030a4840d8481010600b0005007171883c01c40240c40e4140d4030f0b075040c030724400d084e40c42090240084082c00d034071006038a10015170080d0040001180542c1e40e9401c008141c0d00305641c801d6035031607031180900002d100200604070207403851051801400359901e100c1e1113a4035010598189060035008035851b1b00081c01850400c5480e40020115141c081e0388000140b60051150000f600c40721000c1584c08a250f0060851a003000a0615104845584250040001200e144084c00b031034240341c1d018686031141da101d085c4444018081610f0545083c1010350b032580040d048400562505000039 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 449510431 1250 449509181 449509211
    0xd090905060f09130606050a1509080d050a0f021014090d110714030715021608030f19051204050c01260f0910021201030c06320c100f 59
    0x8225450000d06040b00342e100c04c8000c1c81180d101070403c0350a59950440800c160740c4450081009088415a0407004c18841700000c280c0a1164020303d06540800103007a0303007581000030344050082914000e403400d40d200204924028180c110141440e1070f20105020200c40354844a2065004008451041e50100c1007219903c901036901042e580010800f0700250040d90804011548010111503140c1e417a002d00c1078135181400400700140e40807400c18000c0000041150000b0003000c4c001e14103000445000d80c0e114412040b0a00c814441208514042d50150041c0d078901828948080c00903e01458107980e03460030703490f10318042f0703804002036100195413400c0c0000500100c00c081079903850741d03020f9032214000034140c005580100c0c0d015040c0048a0710181950511a83d8200510b5156003469002c291081e003150041000902c81c50102c89000b03103242000940d00c1002c14404009050300d4400c0e400f41d2840f9089602819604070041c2c0350603040304014071460715003082480c000b442d0072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 449511681 1250 449510431 449510449
    0x20a05070614191104170a03030509070806010b0a11100b04050c04180203090f0f070e06010f02030a18150e1819090206190c0b07090602101a030d09090506 68
    0x1c0e55400f40d40214020030000103410903400e4811401e4280c1c10161110b2080314460340c000c1654a20350302116130b500a069060252035002036041000d0300d0400c0c202410952180f805014041009000090421045208040502200b030b0f10000381c580402c283d800c0d6001a011420b801b0340704a0404010980d1200c448089604903030070001d02c558904030b9841d583c406500000c00300d003e14020304152294100c3c2c180a40c04400a030000038104003814175001e22201230001d0100c13130400011402002c042030300002140d5200c490341c2080d0112041c50310481c040000e0582001c0700e00901c004401c581700f80c11888602001d0400c4603a00703a020200d07140c0c3d04502d6000c5401c107110240100242150f90b80d2980160140b90004d881f081c50018020381300600c42c03000c2d05400c0000f42c5240700000c2404803e01800e03400803140c0ca4080007061501000039030359100614185410381da5084400c84030035104104440c0c107003018094555040342100c010f00340b0040e900c915650b40e41402c00150700d506e82072030b403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 449512931 1250 449511681 449511691
    0xc080106021b0406030b09100e010c0503011e05060408011a0d1a041502040b0403050f0f210c070e1b0906030a021803100b0a1205030a050715020a05070614 68
    0x10003025002d80c0c0c2040c5905100c034861a04165034071000b00c085440715003103511031b0080000401d810310a00040e2002c40d48242c038040d603141d00d020f4500c0c1402d640103081f80c0c1101c88100c51112041100862101d040040740c0c8070682c0400c0001d40010340d03d0041d0000010341003421020091020b451090100c0058400ca002300624540002a111541c1007030700a80c01c240240004200c8000f000304143c103d0b40f094100c42080d802c080340400400c031040110b4030305c099804c4040c0007003000e803902d4140d07216201200d0070414102500d0340c606d00500802900c075880340b80c1003107a4989542c3e02c032010b96800151a6204a8003040309903001c07500410302120b07015070024100503c3c6548070001e0070000c0d00822010100d408070261126800e9030100500340341107000c4180002d0101d40300c001c101241903161302085161680400840100340084169000720015041c000e94030700803403510509483e194107480c481e40c0d1011034103c62940e8017201409019104030000c014a2500b8000d040e808041210 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 449514181 1250 449512931 449512933
    0x31f1d06090a060507121401141c030f1107141216050f0607050a061a120705130b0a15030c0e031c050d0f1b080123030a0b07020307060c08010602 64
    0x60150b000808a0340a00e5000c0c2d4645000c0c02c4a6103090401c40a540c24205000201d628080c010310541000150a03004900c080301c40000510300c1c903412401905c031070030019042c82808440c0000003400313283c440d250a448841601d451544904c044901c030341900c07030a5030045810501b00100d0f01ca0001e0103860b180081c01c006120703103140c407080003c0d02d24030103d01500712a0500190001482c100442d0003100e00c00d08000c5100d01a19030541402109000382c0c500c9078208142c1c0001d2405e01145e0141942e030140c404506405805400d0009802d12043c0701d40c1180c1011f070700003003109100c2c001c109040050343d801c1c010004c911008507440c070034400100f603058000c40380e5030fa08030303600181131024082c1034100182044401e100d0003084403101c5c17510713000151721244207070340c4164200300d071641c003800b2414001b0003941012170380e8030103c0e80e00ca41107020381d80d03004000e60340f40e800300b0a00c0d007900d0348180c2c0c840c094500050025220b0b040b55001311081400c105c10b007850940101005c50503034216138 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 449515431 1250 449514181 449514193
    0x1e050105010509210319020d021c09090b06210f09010218010507020d0602040b04080709020c03041208070f0f14010504050309061b060a020910020102030606090f031f1d0609 76
    0x501e130140503c00c2c0c080701032041e100c108401d5081c14a80c514110304002c01d0703000b40011381c0b0350070000390510084002041d0040382922203002d405411041090a9402e20000014614a1840401e03814403410308a500d00c40c7d2002032174040d07801080921031085e02070700c0d14401c50762110500e440c03c1c6d01603440c134800200d2104541008651140f000360503030900081c421031080195442c1c81d1700300e90094100d6000b9101c0010107000000041000e81c0c000c02402c1811803034108520801512401607000c0c07800c00400e446002810300c02c04005541400750488500c082040c45850030404220305850304841c03412442200e080c1026061240a03c11900310300998680316800c41040808c1e40074600351000c1a107601034108017194108982842520017040050b940d1890030300700f01d0484004000c090441e0b0040040048545400c4151081b0780002e9655502c1100c040c00000e080c03070032040510300385840c020861480d80081e134102c10000c00c8403038503101d8240c841e0b500d804e071280c2003100c001100d54400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 449516681 1250 449515431 449515459
    0x50108060a0507120c3c0e010c0b0c031e1b09030f0a08130f211e0b060f010c02090c030a0b030d180902031303080406020d1e050105010509 61
    0x40d000194040c00c20b01e010801c20068210b01383c101d48840d05001c00094400050780c40c03828900c0b0440c9005006040c0030907400c1110b107088040c4104d401003103410400211010032503a40103500c2c40004c598030442340381480c82c006510300200e400071102550b2000015505074101224403074841d0140f440c009a00c07980d101d001d0000c0400d5801188541d0b014818102e40345840701d4280b00c0090340070700c0381c0041503a8a4041444411048054016400e0003030f8100c3e0801001d0795000d003000070880128003000c0d08401038140910b07a1288898480b02c6000c01d003062400300411006e60714828841110080c0840311803800440d0350024a0b04020341162107007000c26240710800380a5030f84101c60320000318042d408840801d05090100207408049402072800e5044951441d07840c002502d02000d045040d413801203508450144110009024054074078045020f01c0ba498044421451249100740841001c0d22002462000c41e04001d140d054544400800c035584264102c0c2e6a03040000d00e0103695000ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 449517931 1250 449516681 449516701
    0x61e03090d09030f0b04020a081005010312020303060a14031f0506120c01050a05031506040632030c1b06010f080c06041a13051302030720060106030e01020d0207050a021305010806 79
    0xc6e0050782c0c810079290303002808a001300b047c81d65101102034041013030b51651500e18842c1c1c48100e9500c0035504103004014068860380d8000d4204c81030003c0f0300300c1403107202000c03d041000503007002c2090035011076482182e40d01c98200502a0b8030588024407098040b00043c7c0d00c1701d0707568054a0000740108900d100d0740c0d10601c09150080140740881103c07448040010b00183d04c240d100c100415002040701d03081503480d208120b117034100d01029510b40c920000500c13209110050003640e1015004c070b806001408010302803c030309802c80c01212495611440000c0301c00c2d040c0d00c5507220b0b03485000c8a828060520805403000c503440010612501c1c04940e9444a40350000741d030019074540c1101000449555068900e414126810401a030381e040620303000304121541c404007400040800384000c2148000071703500341100c0685c940001c0c80400581c006019101302440f14a00701c2c0003098220900c80302141079400144229214038801e19040c01c0c1a003541c00c00d02c126002a005200017588004e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 449519181 1250 449517931 449517953
    0x1512030f02011a0105070507090905070e01090209010504090911030105010602030c010f0b0306150102030c15040b2a0309011d07060f180608071421091203040f02061e03090d09030f 79
    0x4421000c1e14001501d2700141c07030440b22040b000b60350586c4a040c0c1044981203201c066030241076050404d614000702000040d105100302e124109105948468440034414a18101408410001d00a100355603595000a40ea03401c00a0034003065403a0001c0340713124050034412001030840282c0500059960702092402020b0840501c0f41540000c01c00b0042006040c4400e80d034465140d000f036102400d0904100c80d10400003441d80d08900d007074403804080100c1e0f01080c038481c0c1ca05541c69a55130740c5d40d020303420701400e006070300314080103e020900081c00d000802c12000340c420655880c0740840ca00c003021140c2014240e45031011065207001404030300d2050034242d500a1f000c2c05c01441090009007401c1c40e40d40909441044480160240d5031264800380702c00307400900c600000d2030102100301c0b40b2000c0c0d01c00500001c03e0114461040c00854948409032210b000e0007080001e522a4543c9010a8962003161904000d003d41c1c804440c841e8004c0b5040d5056075004401452003140b190741e4100889 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 449520431 1250 449519181 449519183
    0x10308090a081c1206030302210405031b0306160c030f030212090d030606080705040b030a06051203130e0c18040603051c023d1512030f02011a010507 66
    0x18061100205041d0810016203a5542c3c481c1900000d51418030801081d018451020311259410300e6020001310360300151a54501440c9030303800b001016400605080c0d0312490340025003501680050a4001740760195904000c04250155503841d0384220440e40c03041080707980880400d0030000101c001c81d01c2200003c3c10781041c0e0800602d8201036540c4019602000c86428104c2d60203c480d07410665818000c0c48000d00031810103c0550500b07000203407081c0298025408917070360100028021014540240d00184000780580d1468010344006da605c2c0c1d80f089450032220481020001085e100c0f90020350f102d20207401e41a404d007408070881500d50070081401079400b58443c01d000c000308009005031459a0901810b8000e514908100a4100b40760641205129411f00900102d59140211050031040350074840500d08142e241411006000b820700c1030424500e520030101d106100310341101d04081c000e4a502c1d200f40342c812030072400da60805c51520180003081092510550050000e00045 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 449521681 1250 449520431 449520439
    0x91401080a0302070e1026250b130504060608010e010605030403020d111f050a0605061806090d0602210105060703020d08060d1a07140c0a0b04020d060e060106111501030809 76
    0x160351f220b00c4414160b00d650880c004410900044034900d400c204004681440e840340b010382907820703190000a00c003140b803080b801c041c1c0c00020000803411002c05c00300040e1074000c6c802c03c182c0e03403180001041c01400740520001d015003036001055860048007500d11495055005110425070300c24101e0314446552500e00d800e115800349020381520200300650303821a01000051a413900c5010700090b942c0c20750080c0d029980c10000407090103d220050122600305076451981e954091000c9003801e0380c0c0030000f4040f580702190011000801d0360b841410760803038400780401d82e41c8440c1006068841e100005000d030703004922140e1044e001710041e66000030000e09001100b10f840c0c030f03a090688030850500d81555041000c1010707164102907a1490000181d41407818202c0f600401c907581e15900034050090505040010708540d68000c480b42c8082e40035000303001c0e81c211542240ea442030203001d0440031844245e0032609011000501400c60b00049406540a07480c64680d03034075561010b5040750308 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 449522931 1250 449521681 449521711
    0x4060207050306010b0421120e03010c0e010c0b040302031303050c09010e010b0304020d0602190302070501150803121302040c02010203192c010906020a0c0c05012f010b0a091401080a0302070e 84
    0xf269400c0014841100161950940d02742c14908050848580603054014402c0c0c0800040599922203174100340580d002e100c50010380c0b40c4e400c1c103034030790f010301c442100c0018101700303000c403c001005c40c644e02ca06800350350107012640c0310303903000b404030b08240690345441009100103005860304880540409010703140041c0b8000c0307580940d40243c10034640c4040480e800282031802c0180902c200703406a0101001903009604000f080e91b02c91190000030075000d07500001003981c0020041c46520310503801842017000d5100c480029020390021a40e00702105841c42d810300700e41c0850301544048d950342203048840b094030481025403000e00405100300740d6585580c1d07200082d400f031004080030201c47e10781024800c01440d101e0244055a003050b41006070080c1d540c00c0100b801c14000500d5a002c48901e0480021070382110700506c01d00020fa6400107008000042c2c0c40411f0b400b24803940081034021415a80f0b801c145907640c0c5021000900507032281a040110b4036043c504903801031361608000342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 449524181 1250 449522931 449522933
    0xf0f07020a0b130f0906030b16110d09060f02010c1b0c1a030f0a0e100b0f0904141605031c0c06050915060d03080408130e0c04060207050306010b0421 66
    0xd0243c111148440000740062014800096541160303002042e0381c440610a00d810355894140051015001e4000221207000b01d11240b809004080c90520001c030444144250700100209402c0c00380c803410010400c0541da0503a1703e481800383c036000300465201c0f981e00e68100c00c00030705d26807480072080e162a00c880ca400301d01803400c222016040000c01d03075a20b89074102040c1100c100c0d03101808214605150001c0d0075000c1c1404504078104070a02000040c6000f181400304110b1100d00c8032140d440b00c00e50003044100702c201c1c4c1003880300c449980211013442250294201c040c807010b0051a50591200e0240c412101c1a403d040750200746034504050204059036504080d600c058407030020310b405c0b481c400356010140850301503100c1d00440340f900f08a8125203010380b0242d006480600311810008000d1215007800f00b04500614100804400d0740c9400c03001600705800070b00401c0c0040c010304000040910b00051910b060303030030002c030303041c60145008101a62440380d008884100b1440d5201a8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 449525431 1250 449524181 449524199
    0x50f0c06100911070f0f030e0303220b0406023a02010203310210050f07030806310f091205090a0503010626031905070b0901020f0f07020a 61
    0x500807034450100d98065400c100070320094034014034031021000b8050205601052445480c003076129040030340c04d911240241000c880403a014407072103401d4400052600002d01c0300c0700d21031421404800c41300d42c0c41c5071919158006031040c1d1154000587c014651a00a403001040c80900d40f00b01400703030500a007030080c145100002c500c2450016035404802c0144804c02e290408240d1304504950b040c030b0b0320002d00f041c0b42c8044030040281c0a10b2500548400d1680688116000c412200c1426078880341c01e490010150501160000c1c0070b0303248600022000f445840607188a1720b00307004024811804c4510400003010181000103000740c540986034082809252400310300c0c0d00e00c0e030303c06a903004190140003405d03a8a41c0710394000e130700d001d00402a415121040002400001c200044d400d1901c84003180755000e40e04179410840d8240081404480c2c01100a004142c070903154040196a061203880c02c03801411101002400100315000b2203031800d0009051051000b0700001d00c454072001e0007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 449526681 1250 449525431 449525443
    0xa0c051b1e190e0a0b04020a05040e07020705120c01120209030c150f0f09090603070b030a090c03080406090303110a0302060f06040e100e070b07020a06030e0703063206010f050f0c 79
    0x10982c14024081c0441c805e0240d203040d603034290303003d6150102d103110040071881180700707102c0742815807800304020030f1007800650010a402804025024500014540c40e0500d07070075200d001c118201d0180028000b20300a90304010070080190a9105050701404000610441d0002c1004010840140001c4544025040c2080203104680d00d6813098030901004910281c0903a200340d00580080010940c10030480303a00c107081c4440403540d8007580ca8140d50b1900c640c0c000520b02c0c17001003008030f021907018582c00d0072039000743d4540441140f800822138440784000009001600325000041a04144c03100c5150054000b90000170081803603030300a401d110101c3c40c400020b035115101060300c207004000030009844540003003481d04020f603000a10104091050340c3c00d154136802c0000b10040184008001150405c01c103110300f40034815090340e0304192406460641080400100300d58841902c150710503038040c2c641000d4000c0b002c00a80d84c58000021071030013248104000c080f403610501072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 449527931 1250 449526681 449526689
    0x5060901050d0903090617040506012306070b0f1f030605130503070b01030209010609140f0d17070209011520070f0e06091b030414070b0a0c051b1e19 66
    0xb95202060401b00010004000c2000c0f0310003284050046c071000c0b0b640440e00320b04640c1d100071600442c0702510a011201c40000c1609540080041881810f001c100c40b8507a01c1443d85903910a020f0f076808812400c8140c4d105005d98103030311102070a00000b6801e42c00190040c0112220368094581607840c1d6103140d100907411203185d0305000042045040c14103180d80900b50b18100089103506103243e03902d62101d44600031344641007002d40d0b40c0c19500c81e40030300b11080c0d8116002c1c8800b80b418402d12549a40594401c07400344e5114030001440004d0203400800c0395a050380da1401446224030075030001c141401c1c08500c80e0003990800943c03c403003d80500018604100201900d10b0f001d0100301054034006d0800a1181c4050340c1a0f80d0009810200ca51199100030030003882541a001c0c289494140c1e00507424040b80000e1181d2110303008600703d8945d901c10811200c0d0503000d90328240b40c2807405060704e500503610340700100c1c0e40c2d1000300780d08110744405040380101c0d02805d4500010352031142c0c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 449529181 1250 449527931 449527937
    0x7050604080d02010b03031903090212030304050f0607050a050f07150518060603030901020a021003020c011104140f1c1106030c03060a1d0c07140f0c040f050c030105060901050d0903 80
    0xd0802c046a40a02503405000c0c0110055803d101c074122002007011a840d44000c101503649851108566402c185500001c6140c0100c9440746401d1510559613498a00240101e20404c030015041e144900219003814680340c4d2a2418904c69171038074215604080000c070340032000f01415501d007184900c00c80380728107290708011701944110030225051420151030140a900204603c00990342c000030003001c80c55040c0c0348462040c10360700045009014520610105500305a182c0384880c910030302030310646150122803400c01045004109003924804602c64000070356070319040b2103200000001003803500600f01d8224541c0c561001840b540c0c402c4a00241e007074400b1044c010682070039034610000d40350600340180300000b104881c0940500003008043c10f80030024100c420896101019010f1080c0c0508491154540b1000d490300c0f082c0740380707115010700d151445030745610328503000d154011008088a145182d0a0030b09000ca80d51007164000c0c18400304005504c4c40c500d0742d01c118600c0e603020359 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 449530431 1250 449529181 449529193
    0x20d0303020913060302061905070b0907170d080a020d02090a0e010f0e040b06090604020d2a21200301120506061e010c060e0a0f050c060f070303050403020705060408 73
    0x80108000501d4101c154030f0410b03c0c0000c01d00068650030216007085208607a10703604946140b03000c950300d00c03440000402c90400d04091000e508400104002034580c10301c1d0f1031040e55040300083d942c0383c0a840b03003000040e083d480800c8840c891640184501d01841c2c0c000b5240006403804980c03e40041c1d8424203440801c0c20040042c0880c42c0b14540107024059010500c0c0d003007503142d4000201b0058062032044245001050280d0b031203a045541064550405100711600c1c1502c00700200012003a03110340311045103010550500c0f494001c0c0c1e4423241c2c42000004107541c50600740c0284646201c400280545042c0c10103204c07070150145000b00000652005103015601d00303541011000381c0341c6405a40a00d507441400c40d1140340c9840c1c00d0b4420b18161116100600b405800f030001951000b5180c001c0000301803d00803200c42100d80103000c1d0b411140000400402d02410b1300c03407001c0c2203142c0c00f070610180000a1081c2c02c460340081c040d00c1151190b68032480060f5242d40907034030071920380e8441 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 449531681 1250 449530431 449530447
    0xb011b11030616053109020a0807112806050115030f020405090105011206090606021518070303050f220503010b0405070827030c0102030f0f130b0a09020d030302 71
    0x10001c0c01d9000740010f031410300680c0e031a4400b520030301585d8808941c0648080c17200d90150702e5660359140302100d0802280f01181e441240700002d621101101d0001418400016132550007074104e111821440002001c44200c00e14201d0a0011041c1c103401038000c0030108640030a14901881d0301805858000c00c10044114101904403103d00641c42403c40c010300040100d0b1744e9941142d41198404c2c2840c8484002e203034801001407030702d038000da080145071010100c4d074198005461200c200c518041c00d40103440c1c0b05406031005100e1242d1030032683c810b03041400080e00c00d4018201305594003a0190422499400041000011195214001d100a4020080342c03400b4001c642c04440f040d2001c002c0d40c104040c0007040404001c2c24010040c1040d69a41e02c0c411804414650140c600419241c4550b950f00d05d02d0b01035842540c5852000c44036a0103d0ba02e400c1400d5054042e030440490140a02d0595131281415540101420305c843c1c0da51403005c01586418680001c41c078826076005030744402c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 449532931 1250 449531681 449531683
    0xc030a1208010905010b190302130f14030601180c09121104050a050603100b01051606061401110d0f09150f03051305121e040b040603050105090402090a0b011b1103 72
    0x7050b8401c20005080030010800c05c59484202c5600c0b160301408001d140a190314240c0c0a07214491103211483d2201d900068603c41d003464060568400541d02641c1005100c205a0703034240a00410664280550a46482c00e01d03c0d40700441d0000c060405400c90340e5074061864510301d804600752104110030041901e90324282c89120f0740200195070801480c28580e006c81c0d950a007440c1c9101c1c42c01d9555418841c568000c40603a001d090607102c9440388400680b5054001d040f051146c04226440c1080d054215030081d41034801e24000b02c4020b001d065a242030031200d201d1a204030000f40100d21a020030085103407106200400c0054662078443c101c40d410003022100000d02070707140f524a42110000080001c2454064515140b00f51a1180030540c100359050b202d81301140840da60006001071850200c4014104580598404004683c1d840090003d42c460442d8025840300e60200011040d00443d4460008900c061409030818007410491f05020150345109a900701c841035102c141703a00e4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 449534181 1250 449532931 449532947
    0xd05190c02150601030f020a2109050a0b0606040902040806060a17150901060503030a2a0222091e1b0b03041203021e0301060201150b030105010c050c030a12 69
    0x14021400304280020914000c0d02c1d400324410400c10200b0940100f00d080c0e100350840202e04651840441d40e54400e1480031780107807000c41d00407040c01c2c0c1c0c140012005601d10301c07403100390980002c05800159243d40d01d140d4400e03130061940d83d204d1000d0001162800252000c6d202820200000301104d0410104214010031180c1c041d840185040320110101e80f0b004c500c0240000140c443c290b4540c941d400d907280540300340c1d001560035100200d105c41d0320b65844020312601c0c02140380e440a031a00403a418800a1082c5030010390040403440d8422030440216501ca4029500c4d8540055145242d94603904101d108401e0014810f24070340c0440184200c0c4440320b4034400c40c2c0c90840c0707016803a20000c24403a00000700041e2502220340c0810740c0d071500a404070b460200c181808050484c0c00c02e0102c0f030a03a0401c0c040c400056291481c4801d2031201000c144007503503042000142140c0ca0100111403c0e405071201b1152409080354944003621f040000f000320b41d11692088804d4440303050010f283d0347d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 449535431 1250 449534181 449534221
    0x9020405091b040b07050106051f14040f140d0b0403051804181b030c0f030b0106260c12090303040b0906040f060c0c050f0601080c040908090405070905060d05 70
    0x1240c01c00890710049810080f181150360144041c1d4590205040607401031800ea40540d402c400a40310070403840300045021441d207000c1d5141d01ca08a041407842070028040c82c000c01c2448090506d050008107558900903604080c01002c0501219a40e03070303030307000c0c4110030340341107021501c0070411210410249050300408201901d003049240e00c400d829110b074280d03100c0040c021102422800300c880720031040c1d50000c1c6800070300425145503100101805a443c1d4402603848103c1e640006c41c01728496000c032900c80b41a80c40071103000c091103c004c0c0c0301404c06041c000b0608020000e16051050b90000d407440f83c42107002031a180d1410b07081800310400d006011000581000d01004006600759818240f016001040085ea600c4007200a8894010b031107006020341c40b9502080c260700c2c100081c0d0b54113807841801614120f10042d000d20003603a8107041c0090041b02c1c140b0000c410b6040540c40346a00031060300c0c0c01d00d034456503038001c6141644044052178103251140704000160844840944040b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 449536681 1250 449535431 449535451
    0xa08010f1a0301090504050717030306090a050f0f0c090a030813060315030f020f1f0207150906140904021303030e010816080402150318071203090612150902040509 72
    0x80712000e2048041c031050060f2100103030303900c5c046001c3c8903082140b440500088008a2082e03221603421036500d0b00102e6600e480340e20070800050304400513004060041c49040b103500f8058445020640d940c10340182007800110082c40380603d550b8659190500641c010050159204403100c801072110a03142c000009145c01c0c0b14120481c0f03a101040340d0104c9030030040b000f1244029100040c40c20f01074040d5280c0c0070700003508002c5900e16407456903121001a0f02120307031544e5070304031851200d0407000d00500400d508030820170489008540c15120b128010700c0051514904900050413078024801e29032440040311400c0c003c264002c6000800980e090030460320038507040601c900c030002e500c080003081003007800110b0300b19151b0b402e0381c007510070040600315144c1c5032041d400c50038408403000070340350b510641f0b000140300505d40490301141c54040c0d840c164030b107041c41b60031354000b031014400840d041c1c1d0303c2140b200030356082210030024003101c0c0001340c1c5d918941010080c04400280c0b501c1d200f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 449537931 1250 449536681 449536709
    0xd17090a0b121b0c01090303020d05090c010f05090d0b0901050f090303010305330412020c0108060f0111030c0303070f0914030607080613020705031909210c0305030a08010f 76
    0x405101c04450f031010510b01d419028500c01559148a0300680d0650300c0c980d0700748a00d0314100b5030160080d00700c1d003114a404005e01d54410349029a41c01c001c214403804500c8c81150310305154820002000000da020380002c0c0300e6401a5a11004140101c60300e1a041c2d41d650f05102c5d101680180080d0810f01041c0211f00310350468641d241c958021002d1034920300001c20240801d4a081c03000c1002040c031012020103245014201074000c403071014158030040c01100120102c540c025440c0700d0107070002501030850b0070003240054030b00b060501c2c48042c06110901c2002c041280c108011881060141e942070072154168030094240b034480d070804441619807100d00040c83c6c40000b4404d900001c0da00c2c3c028907544a54000c121400030040540c51680c0c0001000350521030000020180000f10f045498a41c26005c02e08461050050086040221070750462490000c40d01c42000b0304a0b000d0720b83d41c40c000e952030b603d4625680c00100c200d40840d030601c00400c011240012000010714912010a80c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 449539181 1250 449537931 449537947
    0x6150d03080c03041410061802120609060d120306030606060f08040b06060d090309030209060a0f1811031f0503070b0904050a020705062707050904030804020d17090a0b 74
    0x2000000506980c082c41010001400384512107000e20300006018042c0c0c0c0303601840308801c82c041c1545001d00c810004000d04c034180480068421209003941099144020b500e40808002001d6006400d003079100c00c0c1c100d441d6000c83d402d620011040079140e107002801c20319505e05241501c0b126481103091041d07003102c555072a9044907205a20650010300115507985840000d0301c580110300323410200c14603120500d000c142d04240410281d81c02111210b403203a0328a0100110440103008030798000812220070092120303846c8600c1d50208007a82d011402c501c126458985903001241c400a031960300e074801413481c220180d00d00c1d01400e41070f00a01100381c14540d9410281c411340540501030381d42c410000b07003080a9541501c4900c0d07403080070b4030624280042c3c1038a4002c00e510500c08203004d05100740d050810001035000c111040680150100c0e49d56441c103548110000b84140d80000c0c868503040e002582e048090314895190303d11241c0c40704c42400071b004042c4503d030064000036008202c030030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 449540431 1250 449539181 449539187
    0x60b030a0e15041217100603060e04020303070b0403020a021c031b020f010e010203120a0b030609011e11090a06030c14090f0609010224060f0607021012140906150d03 73
    0xba502580060303401140c2c0380d080720211840d02600c0500301d03445180300140000400b03131141c254212542c658040c06100c0e10740d03100164083c010313100203505610401c144400140c001c0400303507000c1c0c001d0040c0c40c1155195000700d000c082c200e100c3c48448130200d000c0d140402da004401d2140b5415074000031940c1c400c4590115140340321940810b4144010031041300000da10820071945a14500c101101042c02e00c600c505002e0301101024921074001c20f00040c01d201c4052003820004101510555103c1c2080c05080e80180450007440309081420032090219403503100c060000cd201541d0700080d006401c83d402800781a00c040c1403140312108002c455403558500844e004880421a0304558602c01c9000607440c00b14030b6404190750340021000d9503a60150fa0419038481d000c1540d01c0c10501c2402010040548520f0100961080703610311000320252107542181010f41641c1b00002e00c000b150340c0c3d11170140000f1650062135520004c2002070521500d0004002002c05940b002d1100002d65009 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 449541681 1250 449540431 449540473
    0x11091f0e09250504110712030f0605101205070c0f080309150703091511031f09140114040203010b12130b0705070303140108100e010b0301060b030a0e 66
    0x400544800360010901c0c100c0c081c401c0715880d03444800001c000351080031081051a06512609210301c0c44d0070048044070000b0412203040644c000505040585011401d90061201c42050500a9546d010116251f154412aa4481da800c0d48039150318240940b60070080ea4401003142e010400c3c2e1304000000900c2001c2d140781d42790f900c0f081c081c1e00c85ea02c07481514a0510f80e00c0882c2c0c0349242641c03c0c02031007a090b40c40360000740e02801e00c0e0700030349621105030000da034a03000581107032880401c00210b22181e400e107103014040d8821825484513554a5900058614150750460860000001040054aa8001380c03c5004d81904c040d404e642c54500180d40c28007400074140000e01085002a0705800b0050100b003c890b888803450340306060102e0018155000013000f00c001c0781c5403151030441002d60003511812141140e00405c0d41004601100f0301070100200241c15a41d240c0c01480c1803540c0078040d24000d0040410407a8880c9441213051040e296000d0b0000c1540e005a02d40c03039036042d491506 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 449542931 1250 449541681 449541689
    0x30c040e10020708070309060c1101031d1b010e0a0501091211060d050f1807120c0801060e160f0f031802100203130f080604260711091f 60
    0x1840300c0003100c0d818200726a20400450052000511008004421024000a501036901c004c034541c1c58170b00a46e101074039400b029104000b03075001d10000f984a0b4004802c01c1218000d8240b2030440c20a01924006040343e1103524600c42c080040f0403564812401c0184e00c004480954005203044006032200b0b00c14041e5a170700034402c4401c0e00500120360700d00c0410300c6002d0180f03681c0380b000b0400d410040c40b0030390743d00c04500342107004a82480718200c0002203c00c0e042000d01401c030b1500040e403040c1400b4200885100074446070005803141c2c00c0c8900f00080501130f241c440c1a00d00260302415400b0f2a03030041c000d00c04022052402c1d00e0780507002480d44111820001a10a00311003042c01004407038900961111890200904095011000e0420751548501141c0c0054844a8111103100c180c054004254000390003c0e011a4440302d01914a514400c0c100c5000e80f8050325115841d0701902d01503c43d01802d80e0002c4081c02c10440c89540041481448142c290500100449402003885 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 449544181 1250 449542931 449542939
    0x280e0117041106040f08010903120207121d12070303081e01060c080c01020d09031101060e19020c060103050c1302090310090203031309050a0b0114071218030615080c030c 75
    0x1032400b10584030720044030050460000c801150a0780c6d6403105010300b04455045000440030b64001203065001d000f5201959444408465446003041c03003124001d6042090b100031009240d20702c10940c45004040e07005540900c068a4110300f14100a080010003410354108544440c00305611203c15230a141e040d03440a241803000c0d1200b6080284640c0180200340007207501c000b03600700840d41c1c1c5a2001000510984501c1d40702e49403595000d00300c1d08079110b000c0707076201510300040300b64144204062100d0711940c801030130b110507822800c5c0743c008260030031100c45c0c4c0008030240b079070319003c540000361401000f0290310f02243c10020070740f035a2105560307510860b224a1440c04550b814015039590300000a84100c15540c0d854214002d414161042c5030f05900d840540c10185d4402c0240124891002c410300b46030a2084c0c0d5006c490b0902c0312400010040710481003401d1a9242c110030008500506000c81e2440c04a2742c0400f1540565216019540c84504a10010384010400e22400d2000311 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 449545431 1250 449544181 449544203
    0x90102070920190e031f2a09030639020109080307050a031a22060806010b030901050601020a02010e0d030e0301090606081c0905040e03280e011704 65
    0x44100c0300192410780d14910944041150354501071070044020440340c01381e03161880314100703205164403020038000703101d440c00100e001039600008a070060a170f444054590501225034000e00c1c5030b444515180300600059803c3c508006110050284030820381000500e4094846103820000300181024140e04e80c18001c0350700040360b98000e5210504050b00604483d40d80e01e81a000140180d00945807800171914003c0003046ca068074000b40d4131219406003000d070303c00c01c6240e043d28603080382040e5403220944841011a400c141401564024815a40c2c07050722400e00c0c806217425100010a21030441d401440140f001d80c1e4001150f590401069619480b08031690500b1911030328400d0030341c1d0709903003002c0450f000c1101d2640034008803034440041c1c0c4c040c1d0940c0d42c584504c60850400b074400042c01440c1c00e0116140c0707a80051013545504003240d241a1b910304003007540001d010102c1e616014200c1c1040003054010110480c40d032403d1912001f41c2c494410300605210740030b800500814000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 449546681 1250 449545431 449545451
    0x3060c02070b0f04031e02101e03020f040b0322030e0f1e01140705010e0c030105091b010e060415080a060f030803040b131707061107020d02010e0301060513050901110901020709 78
    0x411020314946130050300c05800c03c103040d00082c000d40c030401d007188a27000c0b80401c130309400b610903c03c1e01e02e03000d100b209503890b07d803070001c1035851900003522190442d1000d00c1c150a840320000c0130b07814403a200ba202c00200701d644c2001c002d0042c60660420b8058000c9401c0300f00c04612100f6442d86000003401c000115042d12440380c01680100c00c2c00a00640c43e0107455880904005025500081c00b00e00130b002a0781c2d80848507443e0455a42100e0034000395102000352980113042420704050080d00d400c1c10541da4922080c00810020700d41070124441074280710300c0076081d000d10400307030281c00400e13083c20745960380c0e82403140310040002d4031118500000c200f0b0f103c2c602d00070b400c0b010781020190344442c110310100041640065821652940303041507400c0c82c40702c2032086d50401c9400405405101805400546800203803007501c07941550303030b01004150740e0398414140d62030071001840001c0c42d1801a10f02d03400c442c0e42003c0000d80207001d100c405a1681d0000d000030a80304581d00100f07500c550 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 449547931 1250 449546681 449546723
    0x2150c0f010f0c0f0c14030406020303061c0b19091e021005030106020a0204090c0b0f0a0e010306050f121005070c0b06041802061b0111071a01060203040b16050703060c02070b0f0403 80
    0x100106c603440c2808002000142c0c168008040c6000703010072070705400341c024120100d1020140c4120028401049500010140140c50500c600c1007084082d0118002101e50b50b41c900081d6202c0c0d000c000c10000c2c820100550410321000301540400c0d040c481e01c0c41d41090030281d40c525080000070300c99619910118100310340e840489006068012082c0d03182c0c003000c07034040400e41080401000080c82612070182542c46409518100e5001504441051101105000c0c01c41525505c03c61719109034110b12009111038402d0511600d103a5442d1446000d1524102d0b00100e00134003d02d21031400c100b542e819613031400c2003055589604403007807039480c070324008081240041244240055460b0050070703d0504602c800400072070344618000045842d0f100800c02c1405028042c2200582c0140028000d400c0c01c50028a40c05c0c010380d01958009910740d1300c681c078000d040e41089600c19250141015241e804110f104081c2010003819800c1071100107114071940507070b10028180003298903410781442c0c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 449549181 1250 449547931 449547953
    0x8060306070e120a06020a030501170727230907060801050a060320030103110a091a0f0f03070801021216020a030509040609020d0c090603022502150c0f010f0c0f0c 72
    0x54400811b645603090304002500030142481100001a8861042ca6a02401081010548a500030314603e003005407001d8802c40e04500f40b1040701250340c2c201c0e4240300c40241801c3d00b40c00c0c410382c07420011885d041c0441d6041c800e86a200109124490005001c0f90b900e846901080c4c600a203030003d140c5000c015031081540d0b00b01030b0315007000740020011044c00300c0714422000c04502500d010100da5031708d810301811592400b20080e005c0e0003074028400e1a00c1c01d0090b603e88400000c19190b44044040000303400c00c00c80741d206280581d400160307545e20010300d0501950203c9001414004841e8820010b0345074082d20354020304020002428071515540d030f60040020f48603099085440e48040d014000040000002600101d18007171000a240c034400c0c0201e481542d040d400d000c1e52054485050900e404411604980c4003030036410791408000706001908007204490018500c0c4440e00050b80d003143e03440100e06000030700345448600c00c2030308140c1c0b502d4030302500e291121401046060036401d84e8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 449550431 1250 449549181 449549183
    0x12030b031c050f12070905090c091908010606030506090106140a0315090f0b010e09070c080f0717030f2d060301111b0118050705061c140708060306070e120a 69
    0x43d0082502e1940b514a040098452025a16614803640e220700070004003003c1150301d0b02051404100750551800c01c51000840300b4075560a15060584804140b803e50741950042030000f99608200700039031a140c0c01490042c48582001503107e14000c1d044161840381c00e2520341819101d0000f1040200d0200045d00140a459010089040c04a002c40302070204003204600044048070700d500546000d1203068056200341d1212101c9000f19a00c441c564cc01400910b501030800780900c0010448900007034814421650000c1d60740d1812480103041080045c2030340403003082c11540c40580070004a011000c0740e800035aa18002d039510030000c0d02410b1200035840001c0c001060414410000b10b03645c0c4005840701c4001d11004c81d140748607103a51b03208110b0142a59100c0c00e0200003070f050410040c0792015443c5100d006110040486401703484910780c1e090403581e410401c00c2840380e07010b82c0f41a0448811809003115040c5010000c01404280364640d01c21a0380c44000b820081c01000040956 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 449551681 1250 449550431 449550457
    0xb0a12080702030a0b0a0c0201060501050313050f03041e06020106080d0e0f1f091e030204090309090513030e0306070206060f0f0d060c0206130507030609020d0209090a12030b031c05 80
    0x44151485c20003040720007625403420713007414110070641040c01801004141d80041c4e49050955079001092205460600000d031894040d000c0c21412442040c0003c1c07001d0510411315142441490042410380c0441e503001c002164900441400403000210301440795004501e008103072200d00000040610a02004542c1d00001c0d02901440c1d454901c807465565036003d842b03100800e42d5501d11400301d010720010303842004500e50742c14801450a40d2080c00c005001f4a4101e2946844800c81f00c03c0f51005d0307548034040d2201c0e400c020101580018082040a0280c01502540c1131144000c0d50b0744801a0a981c85560b0081210019456105200b04d00250007800c00601c0c10072420440010004c3c41c0801005025a000060f080301c0d80e42101e030600d42c3d0020003412a1891511800020204401c089038003480c0d1000510150342c45140c0e4500441461f4003803d00c000803403074070084807842c040040043c1828414a21030599002c82e21440380d02460303c01405000b1084401c1742e06100700a03003280d070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 449552931 1250 449551681 449551693
    0xa050306040b06040b0f0d1401021605070905070c2324010f0509011206020a0302040b12060310060503150c090a06170a14011206060801050a020901120b0a1208070203 73
    0x82c403100384101c5028400541d002c004665071396043c001c188242c400481c1c7c11042c10b001c800300207007024000c1c07001002400001814010002c0c0c400c1030840116038103a40355030091509200300b040605c1030070b030040c00c0b41c2042c0041003140e6480c014800005c00b15603e10703503117803140207840e03000034041c8400042440300b5001c90115070f85c01003d40d41901f80124a00c41c14200e001003654101044443c3c180e034100355000d04a05419a0344002030340c80f00c00032204143d003e00c000200400d400f005004041d0202d40c0180492800b0003c0c10700e400d0b100745200c0c1220741405420070072620041218011080c00011401c0d40f55101c00020f8070314410380711303002c2d0018030300c41000500e04e0780070089480415a400c0e095031079460f003084e940240d0f0031004004100480f00801001884810700d580c018541c414500851880d035213103001d50071990216032040300a03400044403961507034025104c010407004241d04209031403184000c54003204640c01005040c00b000601d80f828040c1035010b4842a55000b411038403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 449554181 1250 449552931 449552933
    0xa060e010201090611040f150c0b0417040e0405010507020d0504050d020105040506070602090306131109091507020708010c02030c0a06020a110708280b16120f09170a08040609020a05030604 83
    0x10958070038400c400010303071400c7e00410541051440e00d10015030b13036070340d64011100c50340315801002400303001240e01406054003c60b1102c004c0c0090001024a002d403081c082c5004e00b031850a44000a05a60454100000080707000c3d0300103007510241c900545072003905510602c01a90707074cc440c503000181c1c400008101701c0100540c680042c54007550a070156096921408000d010300d02c24400c2c010210004100802c4403400c090004a600c20118401c55000e81100e00001000385402d80303402d00140c014900500036200240500541410303030b40300440c41e00a06042c4241c9800348107000400c00350300001c0e102d00c12032044501d4540300080c403040e1480a543d410201d6a525540d0a24403649260812500d542848251716050025000700204501d0b43da4130394800d003a05044400e000a011540448021682540c17048070a04039022070700240101e580e0805c911107099040f030002c082c0104006045400307510044003500b180e0b0096002c1040e10301440000d010036081e40290381c0503c02c1108100c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 449555431 1250 449554181 449554211
    0xf030506033706021e04060503010b0a0e040e0c010e1012020309010e070b040501020c043e1819031e0201030f0e15010905070903031202091c0b010605090a060e0102010906 75
    0x10080f100e02c0c00345c3c5000003c0100020203140101e10491000c034034140010490466200000c000d0b10034540b070610081c01c110000203044900740366080000343e100008980040d6041908140c0c50f80e0f0407564041075400c0300313034000c0c4000341031310300d0900e03207600800480c2c03010303509400c0907400310b441805680c0f0349921000e102107150030521070280180700703c080e0000942081d110700003101e000807a80703d034100e6040610f00c100444081c0c441040900e010b5441c089007228070301806000d1200005a002001002c04204071100c2c404800c0d14000300d82e003002c000040c011300e020050100d56000d006034001c1c21b07000580090003044113502e00d0790304042072942c0d890800f0940b01e41502010082c006282d8a41c90580e04486040b100500428402907090000c680295078000008106203009480d0003d413001040000030031065500c240d5182110f244108418013150b14050415451308906002004000078034800f81d900c20030b4107109840030a5042c5910030f41000341c0d9680c10407024000141c1c049540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 449556681 1250 449555431 449555437
    0xf0c03080a1701050a0f0e040c242604020114040b0307030c08070e03100b1f02060603100b0307050607061401060905030709090b0f1806090309010f03050603370602 72
    0x20068002d0000022606152040ca0388096a03400c048800c01c0d40d040002d01000044007600541d182100543c0001b0b29060401c011110f0000f02454800e080300764035409841020b03230041039480003600344202c22614450b0300450754083e40918024003d000480382c00141882a5000300c2c01140000042242d81c2d901a00311240c800301c076950760702c0ca42d510903d0072038228801000b0079500da0046010038080f4500354014034840c501c01803410208450001c1050904803880e2841400340e001303401007010740d01d803d000042000318081d10074400c2c0465500081e89580f05070180c10320441000c10924140801580700c10b041c0301039424400100d5841d6503020300101158800caa20a104440c000700b810810ba000e0703143c01c0756011007201200d0311100d40d00600710304018001c02e001808100e140e242c0307610812000e0701860803e40950740c0c4500c0a4001000c6034104c0402ca41030504000a1040135103000070031391a008404a02d06040c038500405643c042c0300c15010080c20f50217070341801000d03c0226401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 449557931 1250 449556681 449556707
    0x9012d03081908010503031603110c030304170d050f07171b1b0402070b18031c0906050f0108030904050403051b030d0e0609100b030a0602120405010b0f06070f0c03080a 74
    0x2240d041360b81e19020556a07120316840f4254200c410803041d00003d000303002c003070408294102625548645007001c40d245401560001c8041002c0f9203000c25a803405006040d2040860b00d0300a103800200140c035540743c4201e41004006400c40002580e406200800795615108260200c0400c0c094202c10365603161030b54440003c85074001343d61540c003460140308644000c6d40c08000303d812507440170b84410300ca040084038407800d800108240d03016950444c102d50340010b144000091803114504040c000c480c401010501d415500c1390041c44140000425038207200000c89001c95a5981ca03d81143e00d0300855400c91070755020b0500d08040302401101814000280c18400c201680d54502c045c2d507a041c050300d8880780f40d0007080f0f455080e0442d540120a6411014003145c2150105a075102c080743c1c002421100010041c00900081110a004042d92510102d82d403103010520075000500340d229048000f052159209101400c000c0709481c507000a5400c13081203621a00500c50141201e440c0c00030b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 449559181 1250 449557931 449557937
    0x60a05131d0a0f051620070e0f010b07020a030803100519051509010905010c05152d0121050a0503190807020a0803180c040608031809012d030819 64
    0xb000d03031800300580f090074803c1103e010040c0030580585d0041e12215042e1020000054940307540c00140a4100a00d100400103a500f05c1d4907407404070202c0003001410781000080c40360030081e2001580c1c4614030b800c02d498100c42d040b82d032500ca8100c05441c94926134461038210310521082152030600317400c40c20071a0025200c00003814200c4402c52098410010418042080c945050001e54410000c8108443c8208103d0324458650461926144404c990130308414030304424103194807440140b404201c44000001c10015410151282c6903403900203914106621060750341410f0200400c1300ba241941c20400750f0f41c1c0e41202284034191411078540d120041108a0003080810780b00140c0c002d041c42c1c002d8180742c110740b200710400c1e01d9500000034810191150741d00e80c924550740c40c4150700c02041064002c40d0307500740603d05810906103d01c0e845218510000040007403151804443c0000e103011a0441a8040401c2a100a000c0aa00090700f004400300d4410103811012001c5110350103951 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 449560431 1250 449559181 449559191
    0x22a061e090103060b03041a0402280f0e04051b0117040b0403140f09040b0612090c04052413060e01060e181e150324010f05060a05131d0a 61
    0x521160962001f80c3d130080c5400e080e28003440056400324403e0350071030b100501041c04400c084107180f80072480c000e00d0b00f42e01860501c01b081406000700d0b0200042242208480540ca0b06407a215241d8500c407031400e80712100219100f00700d80c41040c20700d4014200c01602c410300c4c1403070304161029500441c0c089001c40c40a583e0b0580a0b140502910740369100104c11a00d0042c060041c032024004040b01c003a044101481885201203600fa002c0340f00e041d8140c0209400e000c1036040000740c42c005008851000d084a0600748141c0101d070000505030020744070b14060f45030030440c0f503006000ca54030140c051581040045038030340c0d108030403200d0f0b1107040b01c000700c3d89076988000306a0b01b4400d442401d1013800c1625001016082c03980e14540c002c14080001c45030300314a0000c0b034100210b508200c01818444a0708807a042c4001d5805400340c207242068249450408000c10311601c101d0f210b0f5828010045142c2800c1d02d02400d0a001800494280180701d05059002545440054030071000310b03420320b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 449561681 1250 449560431 449560439
    0x10c050c060a060305070315271106031512030403050f0f010c02030901050715090203060a0f140708180708011a010e090c341a0106022a061e09010306 66
    0xd030081e0f4081d6900100600456407441d9140200d00c4003214805207860303200c4120540c4105401d00d17802c044041c03610400045280c6140c60f15032114408225031207081c01780248007031f131103514404415580096480c0b10b0340b01511440305242d0b00482c0d1004225100d10b05a240c1e0b84840828a48498259070000b40940c01c4c0c59030082e41c503802001c15041c0002d00c28442070011903049065040716404800001400040030340200341001e20403510001100e40b12194840110303c00c1c800c00214540c0800c940b0301e14101104001c0c41c014000c0d2050100780c0b10860103a103c0c040c00c0c403000b0000d154520081041200549182039204402400c6501040c00e05511800e01d04142d060a80310b007003a51001d51a2010140080c0c01802000952884001004d440154400e0710300480c040014000e020420811380012151034422005812107001c54103c00700400c8580f0035030050000c600102880d0801c10074425020614a000340103030b001d0320030000801088a410103800070701e40f031a0203076414042d580d15 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 449562931 1250 449561681 449561701
    0xa030e12031603021803010504050c121c200f060f0108030c06010b2101030605100f08030a0f0314161112071b121101080610020d1808010c050c06 64
    0x8116600c0c6501c0d4075142c441400c0700e01c00d900911114130010000c400350385920000c02d0031600c00707d0302281c3c0c82c4d10070310b10025507142607940c0403100b04d20304004000d1400950441d2b2030010301c0c05400f00601811302d418004250224015010070a0380ca007c8980600c0c0740c40b0526564201610300006840303000b8004a610307000481100c03108007131440188501c1c0d04c2c0c01d400205035802900c401c1c40700071078101203245524005030141d0085028030408a0141000f0550380d084421640c40048035104444c42003088000101c140c3d00a11807070700309000c9034080d80310143c0141c0207501309041e80324810300c00c00c443d00c0d8488e03003040b4a0880030f9a51945098540c01d8590b560825510701001c2034800f4003c10f0002080c3d88000301c40141c1d8410a110002d61f1110b41d4039070100040001c807040c0a07039008a19555a006540c1d81c0d01c500c7c21284ca100744040000069296050450300030100f0651109000e100748031688841d00400c2400000c2168806008006016802c21580b031542c0d80a040086848801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 449564181 1250 449562931 449562937
    0x13210210081e040302031b21030105100c0602090628020111070f080d2f0a0504090b0a03080f071b0303082205100507020c01090e070e060d020a030e12 66
    0x80b80c0c07540e60080d00e4240740d850008030303802842142148010840c885986800d181014000711400004102d10360040d001c084c4c1c880c0c18040303400c1c50418144010422941c0b44004501b850a4500340140d1084080c101003019115281907070750029800518400180086541c00c1d10690503980c00007000d144580b4100d0030b903100445007446031102400300d00c02156403000c425015500c60302c0c1241c40d01803120440015076048203040c3d4a00e03102502c000b00c140410701c0460802082c584111494039003201c0703015000d4040d5000c0c00361000ea0b9222681055140c210141e405950001400d40d02c802c0c20320701c4001c0030f90000d0700c1152901c00800d9035180c0300512000c00829240d05488524007036641c000b103030781d4150407411780c1000a03914003c9640864000d00074068401c200020115451402240203440c225403416100e04025001c1c20800001c0302c005070480d0042503d26000768030003d80c170001034940c040d52002c0100b944c80014803a60880d0540c1c00070806a87c2c400a5910081881c1d0101920340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 449565431 1250 449564181 449564191
    0x5150f041401090e01020403020901080715020d0207060c0809092a09030a060e07030f030f08010506090102070b09041d060105030f0d021506011e360b1321021008 71
    0x40d0340d41d0061000c2e0b212908191032900d0f10b0340005082a68a80006680407030a034009110340d00300712824890105864100100c040e0b8900080589140e5988020754403882441a142042008038400b401c00c9024000c55254070801003040e0303e03d080c150300c9981c0d032203802070f214922092034119174240000504160b1713035940802000781c00c4101058032010090604889454401d0080d803801200080030300c824854014041c2e83c451402091611024028100c1078000c20302c80e4405000714403450303900040003002c0d21400074040744c46000e00408500900980300c0d100c90800c2d1003001d40405900c00182040c100c0300200c040750040c004501c078651701e4400c0d00b20a180142c000850404035102d80340c000b03a4001c14189480b0145490541c41214199100c404a100140300c82c1a9059082c0c1e034841146511ba034025848551111300c0714092200c5501481040d121820118405040105007218200100801c8900c04500c0211402050741c2c40070140c0100d2156429542100c0701070704c26005640702d6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 449566681 1250 449565431 449565461
    0xf0e100b1305062b0b100305030307030c050c030a02031207090e0c070309170c01080f0105010c2a030f12030614011b06020c0703020906100e0603090a050105150f04 72
    0x140c601d1808102804008024981080300c4040c01c0d16012048045008414106601607103090744505e4600544600502205e0203032080c07080034004a0004000c40c1d40003403450400140105030040103880a00031824008071340d010104585080030b03008001000680c034085040c00240d80c4080d0242c0b4107140c50301448641680540000c0c5450044c5801000000d0090a01100c3d01da924401080584500f5402c5074080c5c0046502c1e000d2944c01c41030f01074014031740122400a542c10300c0e000800207203180b2809003c80441e0109032452040d00741c00b06900e50003441c80e0850042c0c07030b1304043d514a0380c5c120040303d01c0c0340c0001c00301c0c2c1594428814201995a059244043c804020004440441001003080c518141e54440c40d800600d20380700810403001d00d900984002c61079801084000080100402e00528030403a554420079480201445e1102003214502d0302d0f82c480c071381d10398648460403000502540c41c00061120000c000e19040d05022011541d2011001040061009072910040c182e104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 449567931 1250 449566681 449566699
    0x111602010c0302030c06180606180a090f020a060c030801140a03110102011508010506040609090b07180801060621021804050a02090621160e090c0d0f0e100b 69
    0x150710501014900d2800380c812a828100f588801c1030400c1c1065826540301c540820308410b100009101041d80710004491058800c81000c2031041ca115004086000039581c0e122a4403c0145046c6140304c45c0350082c094608064840d4000340020381c40c04404d601013451100006007819120011900f101006003000044a00d190389150304031070070208240c155501c409100d990b8004140c0e40304000c0a01d04000710312402e02c0400d201c00c0b20520740044040c82e007040e07001d44c0070031141c2150039001480c51400c40a040024640c000d0f0711043c81e0003101c0294280302c1c002802d2984007100380400400289450380201d082040d034402c0307100c1c640101341e070041030030720200d050316203507104a9002c490f038030000d49455503510000d4269444003855101030450903480754a0710703a039690440d50000300c0700382a11105804000c040e02030400c10b006203109100e40d00008202c443d409041c3c80041000c603130700f03204004116402401410011408006a10031414202c0c4820381b24014010648c6015092100e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 449569181 1250 449567931 449567933
    0x522020d030908030324030c0105093a03020705120d082a04030606050901050603040807050c1e010e330c0304230303070b01210204051602011116 64
    0x284822410300a400303021900c80b000440c00020700045d8428096010b05488004c404440c0311507542130751840602a600001107416266003140840752000c2c2c040b5a0381d81c045001158031400d0744c115452504100d59010b207954000d0145416100072548070341c00b940c09003507c031824030089500c1c1106140f225401400c50500c400d0003802c41e581c1040070304610076620411802d5030042c01d0341d604d4480c86003400c006000c000740280c80c42071038013802d011100302c1401d5160000007602800040c1000c0c02e580070004040040000806c1150300c03080001d40002000c0300f0048044000c003184100150104008561600b010314281c8004680e20503410a020714010032001c024052801442248500901c01c0140d182200804c002800060503e100450044072110040360b0040b4801990700780207034024003440f00011420a0160f040da00d4509007141e84a51094a2100c809141c00f17001e904a40781106022160315000d020040100c40d80d0024400752520325014040c0740301d000305d480c0c034400440300440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 449570431 1250 449569181 449569189
    0x110139020a02060a05161713050307050a03240f0e011d030a0c0206070b0109020a0909020703090b16061a1206060a0510050c030a081b03040506190e03040e0406052202 73
    0x150020700703440e426284c11b9065030741074400c1c100740310841c0c04d5880c08540c0c5018990300c1c0907200003805c0280c0241581d06d10b8200413400840980c0030003092140c0c80c44001c8420b080e5480311400b480e40c0c03044103220041c010010000106403c0400c000c032942825508030b07400c2a0340701600031000c40b100042d4a0500010f400711405120008201d9010b9003c010b0b0f040408c508410050203420080c40043c0c1d41c0000c09800740c40020294890044180140710741c1c80070980108504003120010b003c49944c036030125041d07160402c0d1180c0001e1000e4641040f00004420702c20b40803803010801d9880d984024681d80700d0303941d01e0b00b048886c1076101d140f8003014016802c00c0e6a01c02e03550702071810044e09201c180492641940c10008025001901040030000404512544481c014030105032440c0380d41415290036840d1440104940c540c19131580340071070b001c0055030041060840075401d032074856444111600c19404147d40c00d40346107003444003003420310b0f2032a00000c0410300740c80c0b60800141e0082c1d0901c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 449571681 1250 449570431 449570437
    0x4309090b0a020901210b060316020f0708070b0d0f1b021b0a150302090306090d02190819090b040e1009110a030e191103010e160303110139020a02060a05 67
    0x40e1000d502c40082c2e001541f0394602440c05800d8203004080d0101503000d00a00d4440b000c02d00c00d04030342c80042d040242410104d415415030300200c81440c1d56000c542040c001600e505101041c006203000e0782003001051030326540c1c1c511a425400d641d10170020003c12010241c600c07140c60742c09408800304000e500a0742d100f84102c1c07001414050304028455000a081240840f0866015004103000482c299410701826070005450100799004000e640c580c040b4600074050302c00401d0000c0011010701c14000c00c8060010b0203d0001c850f40c581c0c075440d003542c8402098034581e0f200303801200003142c1e00000780103030b091006031070706468204100b1450440180c0a8007001440c1805111058981c080d2100e8803410321500403d409070030030090f036007490700712000b2000740b84007500401100d00350416001174003412260180341c030342402d0341c0c08000240105900508103213060728888407890605480040d140b080d060818013034a40c644501c0050f61110081c0c06c0081d405401044078030714040c02880a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 449572931 1250 449571681 449571737
    0x2101a060d060902070c150507110405040c0801060b0a08010503010207020102030319110a080708070206040b011214152d010b0f191805034309090b0a020901 69
    0x2c1809590341c441ea404980c85040c0036140584a14010300c08464907038504500760205140c01d910302010b649078215581e0342c0c803550034480c41d00c0703034040741c240844804070102420543e0002c01540359200c03012004d66014000e51000309070f002000040514040c42983c0113181c043c3c000d1403556036039800402042d000c09a0304d100584e80d5016039455454054081d003075001d09a110183c07170b428103040140038000020210b0085511000030480003c10010b402ca0444e000c6130303000103054815183c09129004400e100c7c0317904d40700d14005070004281820a45005103220860120540c04610340103031880b0080c40d906118107081d03c0100b100620b490010083d58100b2550141850041003c00201b0000703400064001500c141d0081589001c0c8508a402402c00b280104440c010320b47d88001e02409112406512640c400402d101d00c080468042480490541c0500121030315481c120008003040101034500940c51400104070030424400c640c00b03210f050712a5000b13203100c2080c0303003110011108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 449574181 1250 449572931 449572957
    0xc06040b130b0406020c040f18020906030109081303110907080705070204020f0c01090605010b0a020709051503240f010803160501061203080a050601050301120b04030c081902101a06 80
    0x9800140c2c00d06880203840900510303805131151214100c100019151303500c0070960890314004403540c041c1943c0448200706541070303404522998030200020300402d0901c1014118020004040310901903100759201603070320951105417204424020f000c005c4200700e5183c0003298950022a040c1800f45002e400000e1000b800585800498050390402d600800c5440003140e46943c9d000080140354022240507001244010f4188081a10020358400651041a003959070310004903080030b0700400410481071004c0c0c125580c0203091003e104120391880c000c45c032180c2d0800007080048036804541d904854080c0029401c08414640144c1038402c0480100c50549d81c4c0c00c400954413000713482402115010761560300061808041586c10b48500410341c904011003000103214012019241c080c09940081d9860a5a0b48501d0142d40e0542d541c040078250034400329004915114010810603a0f56041d8265231075000f40700228403c0d54501c1d20303840f00120341d043c0c020106007450710107090034140780790b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 449575431 1250 449574181 449574217
    0x1410270503040f140a09110f03061201090b0901141b0c010e010c02010b0307050d0209040308041a16110a0c17031306180f030b0610170c040510020c06040b 68
    0x219800000f9440d4010b1643e446001c000900a10300400c8410040414403428400c041d8000325003460307441681d0541d041a0400f0001c6416600d52503003149002e503120700204039150f42810610700e0711004407828001503007448401c8100301012240706024010500d2448a841c161489069482e002540f81240d152b5072400c1e11600e00c0d50900804000410035000080c0c0d50700180107041c140280c1d9002a0300640340f4003001360042c0c59040140b60b001c7c0d090726141082c0d843e02d00e40541c2040c07600c3c091101c400001c0d401d01c001c544070400d40107002039458a0705015070441d07000187d140c3c900010301500280c8800000c00103183c0300c00c90742c2901e542c680c0940340784c2805e07a00420a030190715048031001030171050071003007410010207807032014080500b20040b440d45541e0715140b800344001c09040c0624100c440c4514a540074500404940042001010b502e140084468503650014072800c0d108000c0f14900d10b109900215500b40034800c0900b05130701e8242889480c25440d0302004407080226101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 449576681 1250 449575431 449575439
    0x1030e011a0102120f03180a0c030803180a0b0601031109150a27060509010512180709020c0613030207080f070609090209060909150d141027050304 65
    0xc1c8a11410108101d5000c805800703070030300091070103280c420000c0f140801000b203d40042401d00c1640e41c446981b401304540b0000c48001c0c0740c02e0a086183c014084105600084100301d62817020714410846200c40101413034000c1111aa585006d40000d0003902350000442c8055200c0d410014001310081d05417071034000d074a000300e440460760044a0f50a55800304400301c590b6800740000f0b840401c100b008800442e4201640e060019140c401c10052140002d00b410032a40540181d4644480c41120503400b46084000c1240c034420000240b90700c3e000300c00020446600394802c0d40c0e48451141e00410066990b01492030415469110a40541c0301e0305400245001c403c00c031411020890201900e00d2900e40310001d401c084840d04140081801030200c507140d03498841c10348100c00030803180c0c5503d5480c0d112041c10001140ca034001d800c0b040300d0304c0c001c09002c45074824040300e848140032902c140c100791078840201c0304842c00c003500c0010807951400c0d82c000e00e2244880381e07502420942c0d10b030603a9 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 449577931 1250 449576681 449576683
    0x90506040915240602070e0604140f090109060c05071103071a1b06071706030c0d030c0c05130221060a17010204090c081f050108010b0a02010603060c0203090307140d08070201030e 79
    0x8258004c0740107900600091180c01035515845401050a40d02170002d00c0e1f84004006030349400508100b207110004000400710b003000d41244441c580c002000b0403412401c0800148294460042a101d0203000000c441d0103050003d4000210b0b852441c04500b803c0c000d80c030500d01c0c0c0e84184402824806988014200100107111482c000c040300d80350584400c14840c40b90503070342e800030505807003504218810f40b0a9140c8640045a89905280001b440c850310300e4180c1c0e10300401d42020f42c000c0c003250700c04200f030780f00f40d40140801400d04841c088a0403940e01c0d0b004050f64100e83c10b54011603005010016480c100032180705001e4624000760416848144c041c046a04003816440013459100034000c0411480d5180c0201810b24000340d50b901b13082c080040c20781401031040322102400061440030301031007940150082c5510a4040c462041e00000080d540c0d0030070400caa00c0303801398101c001510f070104210380c2000d071b0f00070b4030352107481016031140c41244c1c00c01141a0306041d103c0140d0f80001038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 449579181 1250 449577931 449578001
    0xc08041e05280e0709090e0109140607111207030e03100c030b09060102010902010215060f0d081201061805040c031e090605061903140c0a06020601090506040915 71
    0x2ca52454055441101080303604000d04640c030196414045030184428164403440b034406550030f107000440d00545d03a11440340100815107026048000c085203101c5c56610100d26940a24032030355580c0d511741512081151100e0b42c44041500c550b03000c100610002c1d000c4c46c40e0340c075074a40060a032403044200d4000d03d0282c07800001c0ca000020350b105501078040c40e1842a013030300218284020005512558000b035507401c10042e4074142c03092510000ba00c07617910079150340c00c860800380c020480d15084d464110111b03004948084000d0070018000720f04076100e0310003498401480301d84c00300c04e07038a020700307000c003c1030114550f0081607126000c2c88580c001035650154100404c031400112041c00d41044402c0380c40190465205200c152024070f01d00600d00303040300541382c108001240d4035898585191401c2d880380020340d0000d44402e000503a13180c01042c1d00c3d0490711107444c180610ba0341e240c2003104440b10040f0040888152003035003092455580d2180d041141180001d418084681525a17060704e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 449580431 1250 449579181 449579209
    0xf010221060a3b07020a15020f0f1801020604051005071403070e0405060f0d1709031603032a080d0e0f07030303140105030d140909180d0c08041e05 65
    0x2100d040c1088240d004010f40b0141c410307109854080b440d00705050000c2d281c1d08802e102400003c00c1039641446100c41c0d60440700010409104256900356600d88140503030040b003845140400402c8800009500102c6d200c2c2c0304030303804005442081c001d100d00350020301c2c3c041d0804040028244041030860f904400440c026072035500c0d00200c4c8100802040240c86004041c0c9001c0c041d1010b880c51680c80e6580c000c01003540c00000101441480d40c4440443d018009400d6810700c100f00c914804c40000100040a4901036600e60100385c46003092511009501d180d0303000404000420103001c501010082c04083d800d141c0041031803105101540d1514a4070140064035400003141042016010700c14020280e81034088588190300d0400000d03220307407003078070a402404070034411501c061140700c0c11100900300c024030118560400046190000c0c2e504035481e0040d12440c944000094000c1c0e00d40d001c03956111038001d280c80c0c200104000b02d4054400c400d0103002c5240b00200c0d8580c0d503d80c2502c400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 449581681 1250 449580431 449580479
    0x807260103060c020d050d1d0a06051801020405060304140c18012108040b0c070902130f06030b031e0f030d14130503030408130e1501020f010221060a 66
    0x154114104102221500507800084d075000d152107038241034000d0181c80100125590000d014818814141040240c545408110f401042491010002943d204a004001c0c01390f094005e0350303c0600c840e080748168042d0b250720480034000170b0002804040104412a280c0080c0d4107040080c2012980112042038005146001d22006021a250342124054884c0503c0f11025004000b615408810300c1540500c5004407400114108405010480500100385e01c2c10215030340c0d00444040c8884500e540528034410712035400c0062030b1403180c00340b6403513000d0081c003400c8066082c088580c1c91815203030313141450740103119244801020500c06081c04020100002c20318811101c0c2c0d40101c910300800c02e99032031402c1803002c00841e2000081d4ac0d8004e60240d0711640c2d0300c4000c1e02454072001258010100400644208048401550b40f081e003060800e0302140c4401e0780151041e402c0c1e0080001d0900065841e58049442d10f0218941d150006405490307403e0b1300d9150181400c000082d0112458a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 449582931 1250 449581681 449581757
    0x20307030b010f0903020d0206070507150f180e1812070f020a05030312160504030206040308090406060809100203180102120907080715030507020c09130209060d0b0105010807 77
    0x280d60040801c0443c02602e1904071070003801e5034009500a00c1e07c01020b0b0083d800032800f142003010801c1100d014044400c03420b91014807400d401481c00c003c0d060b941d0005500360900740c2d0741444084c0f049083e1404c40c0c284107150b544901c405006034a002c0001d40d0240308070358104001022003c0103108590007000c031a01800c20600610855040700c0d40614040d03801009401d83e94018058002e81140744142090b49440d0b501c101150300d4000c54001962022000400208010b144002000182d0041d10107200c2036075502c8081da90580101d501a2068211024050321110241e00852b80700c4540140c0c1c1c090003680c400d1441c01c980000d2039a0540f654100b0078403c440b5020081c1c00300070481035004183d114104000c0e0f5681c918452041c00901d5152400708401030b00078400c00320402801740020380c80e0710b000780c80e185c0344c6203041c80c00b85d0007a84c040010598509120903e17040c03554010f0203403215039213071400464161400410010411458a031102c60400f402030b001c040030303156020320b650 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 449584181 1250 449582931 449582951
    0x1b06090e2a030a061e0308030c07052e050a0e10091502070c050a080309030d080c16030801090e0c0303090f010c0f050102090f0301020a1e0903050106090507020705063a02030703 78
    0x4070714285d521000e9500c20444204006140d800469a02c604078041c0151601c00e0380c41d20500c0c01c0000071130100152034810102c00381d0040c4180303942d418000b180c4180040d450b12900c0030121078503840c180c81d0310b8020800c031465091954011400302c0788180703210143c003c204400c040c100e1b04295000c60340c034103901d1810407181c13a10b400d0b40405002150081e5290180d0b860000759140403080810f01401049000076880307241d03803400da030300300340010005001300c0c1072614000f0010070090207a001890315201c41d05401100001e00710880b60000f0300210300e4449580208400380f19602d002c0350400400200c500001180c3c16015030b01c6911840000d40c1b83c080035001c00c4094a8125070160203070b841408510559544007011200c580810619920243c48044044880586541000c1c2c010740c2014070000d100310180d4403080c0b00300c04a900b40e075034442d2075000700540d5115121424840000d1021405042050040c0d5030980c40390000070603a80c804c2c1d40d8500c0060b42c00849502010954402c0d8845c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 449585431 1250 449584181 449584199
    0x30a140c0909010c021212040605040311010c090317120408090d0507030b0910020306030a060e010f090506010e01060903030503070f02070f030807020916120203040f0507031b06090e2a030a06 84
    0x21000c520300001c00d504103048078201080c1f5240051015001e03030340f01e1010600340f5015511403d000ba100c04028003a411804802404480442c030040f91104228240701c85080150300c15280b01c644040c41e07440342c640302c0d5151542c40390050b40101d50700c11045182c0200003881081003070b00035441003030103055510349060500e051801c1005107455090041080182603540407481c001055030150000440078000b04095005001c5141407409081c030f002140001d0040008a1504a8100070201c1845a894110803542c0c02524031004011480034808920b85d0760144922201c0d11304507104455401d943c43c0030f140790020b899482610800c50004021055013041e5035207540c00401c010710103d021500d41e40040000c4031200c00020060790100104003080740d07081c0718030103140e007003000c0f00c0100e9104d090807241c280c000e034880185400d000900003005801440d92500715030700302220214554603290342810301400b0000d8002841c00320001c240320000c121000d140200c82720080080e6003400d00b0b40301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 449586681 1250 449585431 449585443
    0x609090b01020105070509040515060315090105031612050a0c03030e100207051f140a020c090f040f02060c0307120807031104230604080109030c020915030a140c0909010c02 76
    0xda046906020030002c2e85500312040340d5a2030300c1aa00005d055403641d40720010702d060000300e0b035407003200001403190800500105940e420400c4581c1c0390300340d03610010983d072000341402c0a01c015072095404c102c4550f10041040a07140260281d40480da2aa030302c08451240c0c0e6003040f0042912800c01031894203014282d1544036016000800c540340c14500003440700526100c80b20400104000786540c07452207550810720850100304c4843d01c030400035074013035116004608081e008030380da080000c5400c411707080c0007170044e43c00065000400f01c881c0c09020032030703005c1102030205220030411140056010b80c11102c101407243e6a0800740d080c030b4200141500c00f0a0007016083c80d052101b41700d0a0b055090b4001103200c00001070071b01c0314140020a6007801181c1c4512030300d5203481b4a01090581000400ca985442182c4652960f82c07014400441800e0354000c2c0c0e44c041d88114150000280f0314a01e01c0c0c0f030240410100c46080c2e00c44000545c1300740007102c004080d82d450318209400b00e42c04000e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 449587931 1250 449586681 449586701
    0x30706050406060f0e040f0825060e0d1812060e03070506091e0606060d111206040b100516060b0a06050d060621020d02090d081b010516032301060909 66
    0x20074410b80c05c03d5203504810315003071f01d00607240141c00169040d8614402440d080d010350040a62030030784085040c4100140014080c1201c42e008503102c461415118250201b05000c228130380c0810107052407001d01043d0304070034080714050341c0c440342035040400c20406441510303c224020030292800d500028100f0521401009100c0407220300c0004406c1c01203801580044140c400c16200d401e8444c600340504800e05030a40c4005000030036601200b241726540f8450b281c251824041c00000d0803c1c081825804103024002400602c1405e00d00408028040b10040c081c2c540031600a1046001a0040001e40d01c440082900040c003036038240d01c0c0f805202c005241d1800d2290074100000c0c102096400b0348603040002c0780d8001070201c03400781d80c0d038140d40e840b040203846040ca0f00d51514040051754481c4c0311030000c0c821075100c030420000d814018580300d91204101c820900e01310310025406800790300b41d84031002400c0b030f411100210b00103003014024000b90b9151540310b440c00745a1412507101a203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 449589181 1250 449587931 449587949
    0x91103070201270b091009050f0c150708090103060b0a020c030114070804080309071d04051e030423040e030a0f0201090c03240c180504090209130302030706050406060f 74
    0x4203000f001c0014a90485421075800003c6130340d50840c00703061200d4a000001140e00c3c1c41b41c0d00c021710030000350306840800001e0459501e01440c02c02c014241d2801a0102d860791410064207000078065009006080300c10f04000c184242c40711408481c0350401c005131302c016405483c1d00d003400c2c9001d004500700203042c0c1d192000141000c2e1001004d01000500203070103000c00001003038682008201d2400185010302c03c503903d088074456044140041980e090340e861040840340c200803412a41e10103003250030301000b0751070503213400344034141d0340c100c02020350180b1a0704c0005911501d81e8060100005000405541c3c0d4102e006c00240001005010010445e854020f1100004d450309814400b0b4a401400f218025000d200c510f0101101d4920740c03011040c00e10303c03c0d100203034004078030944490b134a12084a5a40e00c1d60140308c2180c1100101035070010700d41c40850714840b8071010714a07a070f40c002e00c1542d140040a80300c0f00305890b0151400c03210b03d50f4a14003000b0a502c000400400344c12504 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 449590431 1250 449589181 449589221
    0xe0a18060f0e0117150717010b030f071d030609061e04050d08060f0409050a0605010b0a05180103060e1005130504050d120e1609050901020403030504060c020109091103070201 77
    0x2605a07036459005003d0002d88004c031210310500360004101102c54049600c034144030361318051100034501485613819002219203640003103500c01500042d00d20500d1120a4075001d540c176020110303496032040c84c084142da00000800d40c002d4a00b4040b141c403e01005004203054144400c40d080140002041c0d10782c0c040b60201031000081d13000c00c1e6080c0110720380c5824403540d110400010340800410030f1041d8400c0c0b030b01007170f50200200070444002e098000c0320208566070340c03600c08200ca4030880d005000002c50402c0900310504001600c4400d00303c0601d80041c0a50b101c00e10b03914495019030f481070341c42030f100f81c00f00070314a0403207500307a12a00d4214092049083c141e440039542d6007401c00200c18085c4904a03101c84641d02e600c8500345a01910894070151500d1840c414020204d024602c0c0d42403c14000a02c03025050084030b040700e5241da9028a0301e4035141d0111584c0000b400120304102a000b0001904038440c000d41c0460101007407001d0307032800c00500190868000e200d03540f80e0f02030a5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 449591681 1250 449590431 449590439
    0xc02010210020d1104090b150301081e100e070f0b040f0b0d0e0618010f271a04120e011d190305120a140301030506070f0e0a18060f 58
    0x3060001c0700003036504000d43c07111607012100018102d030220a01310b00e8800b10b000156022141c0242c11198400d4902030321007405464200c8803031009014482c6140e0101d001070118050301001907012071503140503600060b0203c1c0381001950580c1c0c1e070100d0389034012041440300c810203520620042c205204102c0c6841d150a0195054143c00c1c0b2410001d40004141101d80d26807642020b42003c1c103400680701c2c035181c40d01101238400040042410190718080c0d99038000d104178400e900c02da0141c942c0c08903034a007810101c4540506030f610102c0302c1020490080341800c8035811281d024a114030750300e0b10303c08038901c40102010154044103040117402a00154007840c2d4480b00015210140c3d03000340092000140c02102100c40d9000612911648003503030010704150700503081d071850700c0e40e6044d403029455040250600083c00302130300640040d0046501540100d51b003520320740003400c000c0c544600307000004041d1010750f482203404210115503071058060380c1c46040e0190444204210a06040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 449592931 1250 449591681 449591683
    0x10f03021503091b120a121704020a140d050109050303010e0c0a230708040f050418050606040c0c0209160e01090b040905061810061b03020d0e0a0b0706060e06010c020102 75
    0xa20030840010740203079000615156841d505d495100203804079404e882041c94041d925030303060035034000003410443d6114004c10960749041e000b50340051404000e41d04001c60401e4038511b02010340d42c0850142c2c01d01000442c203004440c06c2d1070040f00550703200c2d0f1412000400d0481e004000040940003005004041c541180340188480400489400c8120102072001f0081c40341130b5004c0d14020300450002840c151030186078041d150291024030414001656038400b59a0303254006110fa009030001554506040d400000e800c00300b0f00e40003400310410340200d402c0c0d01d0240c0e160f6000c5142092008103154100c0c3d203510703141f1420310b800710401d8500502110305000314002d10881c1d40e210404919640d90301184c1c0c40c10302c841702c451075200d4101300c070001c10084160720507a03000c07030584491102c0310964079940c0c00340150540c011b1705040504a004660642360740c030a15901000c800c001080c841507100103040002c0c441c42c2c0016029003400d8142020100c010122410000d01c0703045040140d038 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 449594181 1250 449592931 449592943
    0x120b0a0905151825091413080904020d0f0501080f07050d060f021c0501090b06071118130b0c030c0715020c15150904050304140d0209010f0302150309 66
    0x555a21501076a031602c0303d516600ca050080e20b15524460b003d6040d500b14441c5a2201c80200041c00700100c4503a959032070b90035112000320b0845995001c00c0080c0800703200308104105103101e4020300e4540345500001030100e80000d040103140c01c0c0c2d10080ca0003450694811b040c090702c1d0800062070300700f4000b0012940c41d0110300a20b4000d00c01180b4090410101341c2040407080214501903441d07180c0c1800381580c45030303000e039005940350901c030001820440c7d81c803940c80080c00140045e440c110b62500c401803418a2070048540092600c1001201e580c94001880c0c05a07611840003000350f1017604046c0c88103813024040e60307a0108100140040d958603034081310040756203c40c7d0003100c1442c240401c0000e014054170007409000300c3c8290f10703c403482101094400c01140c42d40d89480090384040c4416250704960040a6a00070403080c032403040300d0341d145010240020050191441c00703601060000000b03a101203015904610180214034010300d05250b1904400d00d49411403510300070882e5144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 449595431 1250 449594181 449594203
    0x612060f141513090b0601080709061e0512151512060108070c08040801061503090215130b160201080903030c0702150702030a20180a020a1107120b0a0905 68
    0x20410000c0b00100e0721490751100004510180810008000d41040c0380815011100307940094894400100c01c00c0c00307a04808103482566840b80a0a22003002a4070103d02448082d414058140042120a0040d1f00c14510a225407261110101c881100340995440c0300a150b5a110000340000e51310310400400c0150302c58001d1030080c1032511405000e4807620400800179104a10001d40031a10030340540100044030f9680a00003102e1496410440860f072860070000e41c8a25000c1881154010860252201e0420f40ba000c2050b5641c030305001d401644000d240540004092a1030019076030407580050384050104069031847c90030100310035140c0b15400009125000d00c8401c2c0c6215050300302940d4085a024086074100c3c001400d0107900650b414104010304400e6400824160800f00294000f4070651143c800f6251102884080a50415001642004107404081403c003104211800c0180501006c80f040c8e10003034104070400490040243c1501c6041c0f016080c001500040c05052007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 449596681 1250 449595431 449595451
    0x150512060607210503161103070609050106090c3f09210e090c090a1413020f040305012004050f18090c210c061602040612060f14 57
    0xc0d4060315008041c03c0010300a020301ea0f810941520000380c2000007140030b0368219441540c1a1030041044900d8044080d01103201d800034004000040d409070442c10440d481040040fa406407030780c4059007121304541c81d400c0001d01d4081d401c0e140b003220007058003800c0440300ca940314055404178108007203030002210307a034071950340c13440a0240268401d492546082ca0745031240d43c0001c11000500c0785d9603416035213111380e5030000420705589205003200d000d1300c006005aa1114980740400381e16443c1103c003036410005a01942510640510003801e241d2030f13203540b09480c1c3d411414014215019401c2254565121702507032205c284205050f1821100b0880b17164220718030402c0880e85207a400c0c0b48403000d4001450500c558844049540036030984152015504182e01c44011820040b0f001c40030090354100c007142d0f000d50304003e0000e0206c040071b02150000e03070701c055020a049440716446400411a494541420440035000c4c1c3d400345422504144049501c00011a5445002030809011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 449597931 1250 449596681 449596687
    0x20a0905270628060f030b01080d0f0f050901090f030c150203040305100f02070c080f1207120305060d05030f12090c090a020d0b03030313060c0206160528091505120606 74
    0x11403041d6802c2180905803911707444030442e503246050510032000b03003e000ca203402000e002920302442403118541561b069a030b1002d054421001c282c0c2e05500104800c1e0400202c40000b14001c000780e5500c030010340c0708122230b694982c50070b00c2c4c503601039103007544103000c6400410042021401c00034106030f20101142000641400350100c4400034401c7c0316000f4000c41d0201e1000900b0b4401042040c00d4100400030346080c0b46442c0c00d154940d100b0510000d04040325641c07034000c5244a50b1103c3e0b40507901403c00c1715005283d498951440d04581d20080f041e020020b9500e15401242502ca5000038030200100300000003140003a01180c4010b0100c4540f030703070200380306500c400c550700103d94a0101070300790fa03524105500b1138200204038131800c2c0c40c01800e040d090200a031000607038520483d014800c0c80c0e00405040c9003140c6e19480014030012802048101003030300280203120240450003620f82d0803450b854101c0706104003d51441c3d00050210600c549205075124ac4c0e07489a000b01c04940041d9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 449599181 1250 449597931 449598001
    0xf0209070207081203271005010503150f1308031f060f1d040b06070c0302040b010c05030316200606150a0e010c05070b0f07110a1d04020a09052706 65
    0x490046c2c1d1070203581c1e0b05041031501300010040442e400200c40c07000401401141c0e03e40d000c8c140ea071882041e41c17a58022403140003480810600c030402e50040c1056903900c40542054a48059503081a0349445072080a030480f40a24070440404100600880c2020b151056242d04003401c1c0342d0342007542410019a504020b1401d640d507501000359141c0007000c45c0e45a4006003020f0f0102e40c05800304a0080c5d24154a0142d11360085401c041c0240d44040110300d103545842e0100b0030301075402c3c0c0100a1081c6228690842c0f0000790340c001401441c60018102803030001304000724050007081031071011004000c1f00d03904603884200c8202d051400e0a1903000b0078964640503207407100b190300901822101040c00880240c420340140310440c0540508044200c8030010400c255500b0720030250b0806000c4c03004540c1c4d40d5054403d41d401350004001488440d940e00040d400c3e503400f02da00a6840c8540403425041450810000304803042e644010301c0d8501d032584070303008602c054625844012180700c0c5044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 449600431 1250 449599181 449599201
    0xf0106080f0405011b0336020d050a0f0f1a0c041202060910051e0a0927050403033801142502011e09090e03090d0f0209070207081203 59
    0x30540c032070100b05d200c1408200030010300440e42c00c0d0848260035040205644090380b42c2240f800e125107002405000d4507405c2000c0014820000c030703028015040c400c00810f4550090101060080248030105256844e1035041d0390585503c8884c50203e4034240f02c0380c0c184840545081e10111250803036040000d000040880c0580b545055108d01400350110409a010740941680480d803010301c50000c060611242c254099840d80600040080c0401c000d040104070380c00014040c01d90301400f07000400712400d008d035101102c0960101c0d490b03242c14420103603290881001804000c0d241f2030403080c2c400000100380034010b42907040054039040007002400d014201c0e1928807071007061140d1000503800d250301d680310854090707010400501001038500d10451640b103034034619541e80b034680c504100a20006010406103a841440188800e02c0c980d00c40480d4642c07080e01552005d100800c651041050300e082c0207000f4011500120401c000001d800594460038100e94480d542e1250358030a00c2c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 449601681 1250 449600431 449600441
    0x1e04020f010311030a0204030c0503060c0a031104050402130501180b190e03032205090106052a010f0614031603141009110a06030204211401110c060f0106080f040501 73
    0x43c0c52020000418001d00486950082c0b0490b0b104020381841d6959450801d80ca80b002183c0440c1748039820030081642c503201c1e52281070319402c8940201c1c14a45c17036101040898200010011041e17800c1c030030601031981c000d02c0f0001c0c0310031004032010000707040c1b105c004c00741d0141c65546114a0046841400d0301405289141540c10707010707040340d031a02015030780074842c1c0712868440c01a043ea00c2d02c0100f054103000e000746040e01e1503525114a4108a03109009000d15107800c0741c0803900008000d0031580c4420300581ca0304884155000c01c0072820300c40040300c074202100f0124480d90100c1d0909041307085188150003100d4100c40049051098000780c03600b000c08010350600170602d054411000c110040744801c601c40750549007000910380741c2c0000c1d401c901c501e0040d001401d1000b80076140043d0800788007802a482900000e1942c14502800c81c20344080030041d24007200040f402040040c0100038403680000a8148614954506034000d0840c03c40500542c401d06016070004090000940107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 449602931 1250 449601681 449601701
    0x120a020d120f0c020105030414160b090406050a0302090f0c070605010605030f1608010b071703090c130b06030403030f0209120309120601050f010f09090c0507020103051e04020f0103 80
    0x500040410515192428a0300d0000311404155003011511142d4480c5200d480d0031581a111a072454407151500c130700344001d20102030b0b518402c00b24003240d1680c442c10000010034640c02c503c0c1d1284070000801c0103965082c1c0126000780c1480f4400c00140c0d548070691604480d048807034042a413151900002144148103010b0940390510b00002281603100c401180325500c0003101000644640604442d00c280000c071040024a0810041c000703041150001d00c1000e208058101210a181b00c502810b5001210b011419811541c491071842c18840c1c0c01c6403600c04607620801211140400040751408060400383c01c042d078a00c21a4031011140d4101e034100c401c01454460000400d440041c2e903a449600c0b268010407a400d030700e120701c80b0b0000d43c070303416500000d24620400034482c004484000c02c215038181000700c50580040c400c1024410381314851243d64a10742d55169600014082e5040a00b004040d0121020140d06100c8441882a0441d81c1291952441200940101d02500d40c00300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 449604181 1250 449602931 449602939
    0x24060705030f04030b0105011b080a0e090f010305060c070302030307030b010504180f0b03030f04050d02010302190f02162106020d0609090c0f0e0705072103020c12031005120a02 78
    0x39441d0810303040c040500102d0380305da10410070581c1c03580c004580d01005800388090b2499030401c0d54000038142000b0b410b4400035850031044a0008000040b00c0c000140d03160700f0542c0705000148144202480000e070b104140c584014644841554000c1d40c911008200d0000c040e901c03110b100450380b041c81120010701400d80002e40340030242d80e9100082007901c5007a40d0861900c01500d0550402000751007003940c2c480c500038203192900d800d02030408884081241056404c10a14603044030055039001082e1161381d86989a000125002e403600401311041000c422201900f00b101c40d0b00c0360705e5050300c040b0480c1c114100481903d03041e0064001e400345611924100035000c124500c0170ba025440e0240100b840c0410a90b80c1c0ca5901100307015809018007100e80900090300c114004c40041042500c592801030385001d904420005c810601108040066000242c158104608108a080c0c50794044da500d495414002f041d01c0c0c42000506c2500e010300c0e081019079805071010710606081d250050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 449605431 1250 449604181 449604187
    0x6070308060102060a1107060228090914040c05010c050709020c0a02031c0e0d33051b0a140f2a0106050d02040e0a0f120311032406070503 61
    0x216000e00000021112280148950030004050315805d01540a1683c641b0303050324900f002c1c40c3c54600207580520040b01241c1e140c81d840e402018201340c2c1c02035030308146a4440380c0c0a414083c10200780c0390035010252090a00200b488085881180c2500880e45d090a25114421191500a007401c1081d8003441c40710f0703c04030305002c000c080072812980e414821025603509044610b04500c018005006801c00030710f801c080c415190801101151600f4015914407808280c0c0c88101600489100b10411021200c4042032040c03a0f2180929500030340200c080290355038200d040c001d49402480d942000f046800109030591071500c00803524400740328007441d99106442c18884281032000c200c031891451940c0d8107140c2011041c0715a01c255140141030031356044990f004c1202600c2c03000d07034624050081c0b50f0030300d0000303181d4220900650300c2482c40341c0d1240500c40c1c000d01211900c40180550210400400078401710245440440d00d605840031508900c0000120380075000e00c20700144544400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 449606681 1250 449605431 449605433
    0xa05010c0306060f110325120c030e060703020a020910030b09030c0d1e030b0105040e070e030616080604050405070f030c14060406050a0c05120f1c050405070e10050607 74
    0x580c100800365402e5132520303100c640350300d401128100031901c2070301d403160020f02038406d012070706c0e8803510304000310300903e01104a41600d030380307040c0d4818401c41e80c0030503200c5081104150308502c00c0c1d420404200c40c0e15042042c16180a9111406140b00034400c801500000b4440052042c0c0311009e142c22007141c0c0c16500d44400066030fa03620048119020307200b840d1010091a100f62403844d0000912440407502a0704440140c1c0902803014200d81485010701002c100406000b1010307118450075650220081c0480007418203114000d4204100c41029a89400d0050707003120040e604104103407400074003559242403250900c0c81c2030b0850030080038018000000d01440b010342005a80038840c0b040c042055500030020140b04910aa00101d4018041d8503040ba005510f8130b4112750050054403c2c0425080041a0950003030503030803800100272661514081c1c0000c2e9601e422054540304028900740340e100c169032840188103040031007003007000064615182180c600010b0074040c02d100d03168011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 449607931 1250 449606681 449606687
    0x3120e0120040807060509041d010b0f120a1502040e090f010501060c0c050607030e030628200c010b0301050a0f0c2c0102160801200304020a060305090a05010c 70
    0x4441d01101d4500d481840c21044804581d007124101c030b0801d401032100d28507000080d607054011030b0245074029911101b00c807008000d0b00442c040c4e084070034000a14164900100311844e002c07400900e01914501c2401d045400c0005444146140c0118a682c880c00c01c209584019200c0c40d0840709030300c94000180007219400043c802400c0482c90004d105a070780310780f4100c54241c4441d6001d4216aa9003204005030304000300101203007070007450688245c4081c2ea02180c40c0880650b6603d40000b40124a840d46440ea003208402c1d1100d00c010900180340b481400b040c504231404000c4903e41000104500130301801d500c2201d90440150080c0800d241510880005105200f800942a03082c101c0c1c030b03046944a000d925001c8c0f143c200c1171404043d0000c1d81d03403203e9550090364505610420130f0703402520100c01022401443d20340004164110100d4a03510300100307903400740441040c14418080140d0701e2000c400142c40d072074500000c0c1640d0340201c1f103203402c0f201071002e0039030351904209241c1954 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 449609181 1250 449607931 449607941
    0x6030b1519090b090303040308030403030b03070608070f080c0403021c060c080a06061e030e010608030c03070c0f0b090d020402070218100501020d0903021c08030a020d0501050d080307080403120e01 87
    0x2029480d20070b5215502c44a580551194003146503041c1c104101c01d200042030700b400fa5420030700a203000036000d05110040307032034044240c200324080b880f040308015005034080d42c07501d501c0625180c6503000b03081400c0d803000540217a001c020721803607841088201c200c040700b2b2100141600f151040c132100140000243c0028401e072030454426003400c00108200703024030000e40c21402c07070b143ca0000701185804220000c003104511144207540319030001039072100400180c070440742a64061692409580350601592400d07501c20f14511850720020000e004404054074241801903445500701ca6a0f8800a0700138030404a00030741c001a1a0014204410080c0344507202c2c04030540b00c00545030709c90005a03074501540803172800090341c0c0c000074401070a0003060b00541480c810051250060a9954046c2507041259052091503002c0740700c0215118a006043c0101002e41d0400000d40345901c6800e0507200c014101020300074000040340030503200f10195a001414000308028007040c583c500d84c045c003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 449610431 1250 449609181 449609227
    0x90406110f091e010e041d0307030519090b0a0809072105010f0b0f12030405040203070f020105060607030507030e010c06060605090924011d031e151006030b15 70
    0x7490b0086a221454403004030414020142c45e130760103401015081101400c4600c41889105141e04403048030001c00b0009484018440c0d11010380311029011019035405034580d0040030006610002c03c850045802180c40912851420504659818001914020076540000d1005005d5600312103800041d24203105401c0c030903002808072403158507601c02070341c020a0405a010015210a500d5441d144015038451486001500d04065564000074102d8200311480c0010500d030701f139038a00459081c41119800402252000d0070700038107440c001c000c0d004100000b0280032280d04691480c0c0c0c00b954030101c000d40d000c6800c0c00001d48480008240350401100e440c0030380c40e0710b40896500591100380100e0303500f501504030601c8842000450742030604400d082d41002c5090344940c0315440506c0b1702d0348505d000003a09002404409013141c0f520720780c2c003ca44404044242031041106003a602c520817074195280204e4a40d2220b070000f0000d070340440074400c001c040010740f0700c00030403400c03500c0c4015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 449611681 1250 449610431 449610439
    0x40b0a0e0a06260702030d1d240109090503070204050702011d01241503090813030b0f01060509090a0e0f0304170c1905040f0204082406100e090406110f09 68
    0x520038440080b0403c00301a2030f401e0261300301380600c0c1100300160707210740381d00707648668403502c44c0d50302400e6513041a00c506c611414001019080c0e03006250454103017401854407800c00c03c084500d90300c0c7c03180c80303006082000b48210b45801c0445e03a03092007508800112116111440c12901100000c58002c06a50a0700785020901420075041d215451407103c0850f401c2908244010f400301d0030480040010351400c640c0e5a40c2403042c0200210f8040907000a94410604115542401740b1a0b030f40181301603104d14104402007010a00c941c5542c010140c10088200e400b140301c01010700c080e428450032030700ca2060f0703100116001802d210492810001203036440e0030b40322070100e807505006034030480140c014801c54103440d00b00024201340c0d1181c51080c880c0d8500500705a195000c0c00d00307141a01000e9102500480800031050a0b04120b660300070000300c400002244416101400042003410b03000c0c4610405400603090042940140341200250203d141d951b9106421646090700b010fa001401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 449612931 1250 449611681 449611727
    0xe090a050d0e0603010312030e1f060b0301050f0d021507050c04050c0a080f1906060206070e040b1c1407030c080c010302280215091f020301050105040b0a0e0a06 71
    0x2156008880542280750043e1034146968216180d4150700950f201d0001c040503038a42007504d1400b014000004010100d544d00000c5091458940c010745965800800072143e08100400c0241c1e140c03141032b10b2060003510f480d4441b04c0240001000c00c1c00760140001d91040020341001040008540046c000300110f404000b50b448a0407200041e0080c0040c000118440350b0201d45800700c0f444049920941c42805540c401482048100558a5960241c000b5030b01813400d0107a055000404246500c105407000c0100700c1c030b090001610b45021180340c540c10340f40b030510b0304103001011980520141c40c40701100d4000c4e40d41e103400c20355a0b201e40300d802014012142003900c00e41c428022242008030038003502900103122000c2020b402c0c03e10a20700258403501070103c9000c0e01044d480e61040c4404e00c00707014000600bc80ca41807941100f4450780b2a030344100018403050781c01c074084e03a00b0340b01c80416054523042030303150a0742c0d200310745000b603035004411950003c1c1050380030740d048014103010203540c01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 449614181 1250 449612931 449612953
    0x305070b120c0c0c1807021b010e040b04060b040305031b03191d0409050309040c230f1b06010612090209010b030c04180c090806090d0c0204060e090a05 67
    0x4030301441c10308640010018011403150702e218009454401d00080070303943c0390b1207200c002032003035804980e48000300500607040000b9590180710706a41202090a81a011f00700c41c000208021039110b03003181f040782e485841c2586a242d0343e00100140070b000c42d100303941300c0e1a400c100381c0c2c98200e00d600301062020005469240078010040d05c00890958524084500002401342c0703d10024444c40342c0091031071003500516030788134003600a1031130156001c0c43c3d64890450038802076401460041052055024000c9224640b06466254101c6003048080d10740c01521200c03580b40c403c900184282016500440c1111800810000d04a0760a03403a601441c408030f419560a40b001d1090281d03200d01c1950040000700c0a071402150320000600403d0f2070036849088188411440c140c0d900c1d43d03140d03905052410035400410031070103800303400000c1944c1d20700f10404980d103944040701c25042103401490302045460b1034120307202034480242580360710700d0321504c1c0d43d40c0c9580943c03041d2418031804c07200360 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 449615431 1250 449614181 449614199
    0x1d012c03160f030e1809010507140d0f0204050d030503070905010305060f04092406050f190b0d1b12050c0a0c03031e110417010c0509010c0303150f030507 68
    0x14201a0306160900d00d240c10381e8030345414120441a050f418001c10f91003c2000d0f5960258640b8030580101c0055158140194a00c0c00c4410042550080c010418580350000310344078169505801381000c0801c20782c800d14040c8000e4091684a50b0b040200030640208041d000806107200c7e82265807015070042e69200114181c8005a0f9403a402c04006a2460f03403a0405401401c600c0d40101400031101030a98003100106402e41e82c0340003c250340300018043c43c5408007070300e01c1005c2c0484011301c0b44040700c5015690602c1d540300b2122151400940d120004e000c0d604146c24103600c1e031031243e0101d25401300207030030700041122443c0301e40c0c6404c0005054003040000d603411021035039101280c510043d9000d600804c02c0b4091101028030558014948110314013a004013a07041c6800591510f140851082200902d030740380d084282d0606550540c0280d005003550700f001002d19041080c0c9120b42016001001001070400c58400241408030321040710310310354130803644500102d821702c1d5a100d02103 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 449616681 1250 449615431 449615437
    0x7090302011b06201201050904020922020604030c090e0a0302120d060906030f1202151b0d1a03070803040302061b030408150f0106030504151d012c03 66
    0x90208014000b09990b1001c0000940340c1d0078403039040010001c031100e8403076403041c00351020203074031131000121130a20710300c10182c031401002e05448103115030815a0014001c024002c06000d018803d00c480c201c60382c1180c0502148164010f00f815039240d40303a00302860319002038065414107909200851000110020742002c8280c1c05501034020f41100f0140702103181e210111050146e5201c03400403610244e148a40c4004502c01c0c942d1034000c25852406200c3d0345400811203046d9001901c4090000040d2080580d00040303034001d45c40b281c2c0400b0520b1403180210540440c6c41c5140c504401c1101400360014080e4100850031200c1d8156203081455807031295000080d00f1590511440158110030480c8400300c2400e841030b20300705a11401041d18100034000e0048540d03400340144a1010401d401d003901410aa10741440307203281580750b04a00308420000312a034260354506a090118030b40c21642d0003a0320303220081c454031a0310100c501e2601200850350100480301446440c02d04400011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 449617931 1250 449616681 449616683
    0xf060504060632040b0d0501050f01091a090105162a030804050603070203070f0f0317150d02030c0a080303041b150311090d0605100504020f071b030b1608070903 71
    0x38043d80480c102c403041080c0800444451008000307001c0499183d54171000380c0f81ca1016424000350640c909030400c04503811010286040c0244000144542c01103000030380d104c2e8040544550b0340d1040180100d17401e2040c082000c0444030740c8440d0703201f00800c200d802d5500a8030010450304010249800c4880c04295101c01015031601700803c00460529102031507000310726005482c1440200d03100d201c2803014414003192060221204001010381080c209088991380b860440c1d600e251800455003180c1c44104040d01c6010000c06400842d0b40400209242400c050b00c0b080c00c4580e5070300c203a941c80e04240c400300c07800a0248101c130740b40c500d440296012a035011645280032031151400740c004200c403149140c09134008220482140d1100080d0100f01071044500240600e847c0751040d41c1021542c0089200d1401088410b01e50702000c0d007525046604865003a00ca03030030f41da174240000a065407000700240c01c50410010800765115100301184015260942c055070b0b0844111842412404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 449619181 1250 449617931 449617967
    0x510020319051003060e0c03060105271302090115030e031c090f05030a0917011b0c0f06021603020d110601090e0a060606050a080115020307060c021615090923060d060f0605040606 79
    0xd8cc0c1003900b210266035070494509906000c000d000c80c0c0104101203000d03007100500c4044903075502e1016606128080c98000f111000c2e5040a20800882040001c8400301c904225100c03240d41090181c80c01002142e2603202c8120380c0e840c01030b00c001078501c000c00e2203052040483d80200c81950320042c041d0440c00220090001c3c008146240250384102d081a015282d4030415020200060707200e10081c000202e80f400b0002c403100c664a802807410120f0010728041010008040009500001d415415240c103002e0224115010055103441d10141103c01b600c61ba040c1103000540c15004801041c03a004d45a80c0c00c400c0b43e8840e55007500303002c40e0f880c4000042e8010410980800c1960303018030481440fa10584e6107850003080405040410342e0400704000c102c0300440009241c01c440c04c2002400d04c41802d000241c0110b80103071300e000c0c807007494100c0060110001515a51840444450907038001410000c3e4540c540c00c4900818003030064500503468207401003000745c05540c6007103481d50541 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 449620431 1250 449619181 449619229
    0x50903070b0a1206031a01090c020718020c0a080d1805030304030e0d0b040302150a0c081303030e030304081e0906180114070501090510020319051003060e0c03060105 73
    0x64825038035031000381142d00f0410903016901c1c6203000c60103514011030041042482a40032040070031080d0380e06074000d03403403d850b00d20603604c11500031a000d0120b0304c41c01075000c0b5a80000340d46101a105c0e03c0d440740300030302446021004010512001d80071404450b81c040081c125403444c0301a4400b180840507120360300901c0050b00107445401c10221450002e425007401c0303c03e503a54206001000d54044015030021500510a080780106c42c0e03074042d05000c410b00518500390005440040003421100d84920b603400c205051600940103032a240b14801c084940e00c2c0342c6130400c00d40766085488821034800704502c030421094850f40585202c054000c0c4818a07007110985060b44041004403404d06214195200410141000000e40a00c500503000030a0000d46031400c281498403005c01030000703a00c18401e00040d0311080c030b02c01c1c1607041c03494000111a262000110b8103003403681d01c02050301d8140b8025044022000c102c80f480c0c045c040e0100c9900382d880b141045214406407440340860200c0c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 449621681 1250 449620431 449620439
    0x109151202060412060b040c0f0c0212010e030a090305010c02070f0504022209020c0105161b03020705040609020c37020f150712081009020c0124050a0605090307 71
    0x200403020111440100380710300d86550b5011404848010f030030140c51455036040c040440c0e04280c01400f520280358940b901c2a00c4803054054000714014102038002d18031001c0e501e0013014254820811518590100c94454420100c002c1c4644203500040351254201040d1b1034009000003042829a034103645809003d900703140c03e0100030b41040c0002c1004040b40822103030754041202240c4040c207034226025944406a91146080d0f0f500030780040c411000311010501e410f644600c2070400f01d528802a0080c1200034101245420219080390382e20034504480000c403c4000d074001c040004104041d1241c4c0b0012922030f22071205011030311904000201d5524102040000c0395444040c401056019640c502d0800303e03903041c4080110200a4200040043c01e00803405400c0721a03160a182007030b003a02c0c240004000d00d190910a40d003601c0e4001c642c1c5c101c03806007034202b4450303a0002081325854a07229100074010008912605001c1d94124501054072841401100c40785000500102501450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 449622931 1250 449621681 449621699
    0xa080a050a030b28120b040201080612121306030b1e0607080d090c0e070507030f09080303090a0b0105010e03190201031508030d14070c14191406010915 67
    0x1100c044401010fa5542da4a8420f540f0a45007003054640c1202826001400c10b06441c12100e040d003014400341419880c0c080000c80741900c043c1d01540c2071800c0e0030759440f5a40803510030700c0404403d00203805140d010805000c0d109001d40041e001d40c450250206644075000e400319154030498641001c81318500750715418490624071104030000d0040c2d860308400d502c8003419a000307030200303140c460b4664040c88144082079284c0b07409002500c05070251800d050030060043c0c4100813000702406900e1041000c0d89004141000051203400700381c3c0d5982c50700c11145900c98081401c2140c0441d15400042125441601d10040565018000f884007030314000b03011607000907441d07089041540700e10440c07404600244819009043ca880103580380c1148034150800c0d941c1407021152844d01d507404110240768804078207140c446e0080214030030444103019180c1001c1c0c02503201d90107071919070b102d5000c004442c400244100c040070705844440e40c0350442034041c1c1d903000c1140240701003902c10900c00310003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 449624181 1250 449622931 449622937
    0x203130f0c090606080603100c12110d0614090901112212030203040305061e0c070c231c05070b1c1a03011505090115051b011d0a080a05 60
    0x80104160041c2940d6074205100f42c0d80303a40c000400094500d014003981d400d04102d203581c800381035036040c00201600c0100034800704400c04494003694441c075260082055103021102c417143c4080c0d092000d2500c511808014840700000c01c0e004031a05c1001502c00b01c0107100b54661000101c4c0305502d00031080d01c02d2244113851910300c0f100b01d24a07400001d0441003092030040124460b801642d02c40745141000c0b030800100400400000200810030701c0848404581d080c0d1041c244180e00e610751140b420440300c1081c80d074004281d0141c4204a044412419800203078030038004541800c0740140c04103031151001e0010744004d2483c0d000705824040e40290b42d018081d00310014401c5244038161488980c1a10340e206c1c3c4003078103c0c00c40d40c2150b03134074102030103001c00e4004c507004080401c1d4070300700206403445014410940c81c0d07041c0117041c81c1303030b103110301c044924440c1c00300004920f0b0580c2d034504c40d0081c0000d024590307866401e10360005027040c010070622002900802c0f601d0034440704640c1525254 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 449625431 1250 449624181 449624183
    0x1701020c070303020f0d02031602011d04090b010801060f0b09040e150106030203070f0e0a0b0d0f050f0a06150504030f08160506060102070b0c03070611090a0b03190203130f 76
    0x55000d012603410100108a070384001d60003540240032004801d6555420400101c10200854104010402545103d0f1400621256080c038007444114252350003422001401341c0250f80c460305041c101014403002070091030688403514000c1000a85d940829280002070384174400541005010500652810364407010751180780409881d1021400d010a480c1b4240036009000801d6012081c03101c5c1a902c40c0003021004402c3c1442894400303401c00048010b50329209118514000241c001d103500015006403404400f0400c3c00c1c849401c1858414002c0c880c2182e082c83c3c0103181c6000001c00036004a9040941d100070385540745001d080d03485440c245240014161060041001041c2624a882d50f880c0e00c03044c00350028054909208000a0900c044d07603001c01440030042c00800c005400100460701060740c043c07130008169091030324500940c00384901459004040d60000111500c0d007900440c855040c0966140d80048100302e0300c3c1c1240070983e2024003444000720100006016007113031038081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 449626681 1250 449625431 449625433
    0x30c0409110d1a1602010f05010e0f09030d060f0e0603030304020607120207030b041209082109151c06270b0409150b120307050c1504081914010c0917 66
    0x14680090a101c0f42000b920208440c804181044ca00c640d4280308807000d151100009011359407501916080001c07000d017600800f0001c0310042440c00c80100201c0700700d000005e42c00d000842d951101205941c2e21442000380c164040c0300040c0d4146000710803a841a6401420305040080517101d01c809803500c240c0100540c460b0080210100e100d80d4541071049109a188511081c24080014440141580007403540e9010f0060b0110f00d140a0388030074940104a002c02c0e458184180004140e45040e0440b0b2194080002e107641c108000058847c00f03d5003aa4004e01000d641c4543c440d00311100f0031660a09040000300340c000f0007401d81c00403007015200500200d034074605520744515140c440001550300380d40e07401d40126107080000c1090048800c44000e10709150243d2102c46d01c1d850701c11004ea2190602201c02e0001c1603402c02554080c2049201f201c0034840a5010b4902d5200034000c00e075400d09011415503d14001400740c1c00c10201c10780e03a0450720610b84180504003860064a40e461 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 449627931 1250 449626681 449626703
    0x10b07140f0a0b0414010b0627090f0702060c0702010509092802040f06021c0806011b05011a040c0f120b04141807060e060306131406030c0409110d 65
    0x141040a044032034018075058919007410310700300440c44005c6401401590600b0b5943c0c203240e85450079155089070031054051a040c003400d90100405ea0180c1c04e030b6000704054203124841821001e554401c3c078a1f07408907074407034032120304c00803c034002c0300c40080c0042d404001000311400d103a815141c000c04403c2000c1e150b0040300d040300f00403410007041e05000b51343c045800c000380402c29011034001d00b1140043c2c00c4407018000842580300a040d500024404100d010031603d07442001818010158901e00647c01c4089107403140c0a0101515100090194417000c040145001d10a10408040075141ca012902c00d14605072001d00341d030742d40d040e0710607514080d0002a0700c56004128600821700c000360801d15000301c42c0000c0325111840d041055024079406d1060755084000800c107908111011902d0b42d0302ea50024490b84854002d0410080c14443d4084030140460340081c001c4074100c0607103c0d0103201c4014007040311003a990251851001c1d16130005581021400c1840e098010340025070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 449629181 1250 449627931 449627953
    0x30f07080d0504050a030f1b11060403081b0714130b04061e050301050a0e030a121104080d020f0d0e040216060207030203030a150302010f0513230a080303010b0714 72
    0x104a0b20300f21002d0b1000d4210b88410f90030103520500080202003242000c41e070168420042c510318044402c0002c0c022442000040360685c0c80200b51742c0250713401185c003665085012040d0502c000305120a0b80e03c1e11440c100131078900c042e508603d80049010304105030000c20070401031701a01c807030503103640c100f42d5524011400d4440300348058a589400c080c0c2c1c0c202c0380d24000a0608552000b400048401d1403c0c0c42c4c1d001300c54021003116481004c17880c104150541c0117031448020002c400181c01c551200050005208034045284100030720380d5001d407400c803991403800320b440c0d1b481c0201321400500780c1e00d00d030390461516502410700600e50780c50694028030160b07a000120380c011501500907070300100401040c899a8001c089450342a42ca10069145c0f45500182105002200443c01e10402007404000c0b5585584030f00000c3c4900c540450f075400800c5a810101520f0014550107481c0b0174401281e2048000212230480300308803804c902d0a0304540302c54151806410a80d1010302444003506 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 449630431 1250 449629181 449629207
    0x203060a150503032b02040e040609141506040e0703060624020106031208070e041e0c031a010e011e050415110a0209090102040504050f06010206100305030f0708 71
    0x1500c240403164000403000c4805807120450807042e88541d1280c1c0c01008001e003180c10791401201c50700040059031802d91342c0d1511120284c0115003248045003820310800040c408203400c16840140240b00c3c09407030482c0b503080d041e01d031141024401d018000c450301088242c02c00f90f2281d0101049101960341c900e031aa61040207031035543e40400c2100c3c140c40c026035a81c460064103541c11620a00003002254955030b902a40407104202c031400340503040000600590103840880b00c0351000400070441c0a0520700d00c0d521055110704010047c901d02014001aa40284030311842c2091210420510354142c100440b4440300365500310341001025060b8000701004014501400c4ca81910344075100d50622001c680e801780aa01d03400f0403c62401ca041d04801343c0071569020030b54060b00c1c9681130381da9014400c3e01910495001540081c90314080000710b03407558103858040c4209030300fa1000d61310b4091b940100c0300400d01024001e80c104000305465102c01800619015200e0207000f414040214054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 449631681 1250 449630431 449630443
    0x80a0509030f0610050d0b0f150409030908240c0906130905010302191401030e070f060c11040c080f070c06090b062110110903030417010f0b06030f130203 68
    0x1000d90342d03c81d00520000c00548012103001c0c04c01a03640108010081c0c6500c11541800307810100f21070f08680c080740116111502840071044050018410203030b06203801000d5030120701c100103440c050103080d2484c0c1c1c50f0004180c40018031081c1018065280c0f003100619960154445581c40a010418591400d600010b03046c000d203800580042c1e40d40c90740c014040000d000c50417481c03009585000034072881005c0b65212150130f0003031a00084820741900075a1400c3c030643c1281c1c88030b111080c40050110b0344580c0c0512001d1145008206070105c4c0c030244001d8902210341319000c40c42480000d100b460321041c45960040761842c00030a40346040d160001100d4808400b500c0508195042200034200600c11102c50a0081c16001807816110780236510b4600306460075003920f0b16400ea80c001101d040d0280c84141c0d50041c02c0e65521a035800c051540744104058100041d4288080c02684613a00c6c42500c1607400003030211442c42c0c1e2060010300c41480700601d4076482a8010400c1d03c0541c40800034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 449632931 1250 449631681 449631703
    0xf030c04090b010810050f070c050f010e1f020f0a0c060212070905040e0606031209010c0c0608010f210204050c0d1103370c050d0c021e030313080a050903 68
    0x32107950400c01e0b0703141407841c017200e0300c01d01c40c3c10301c01408039400d1020708484d8890030030301c1c19801c103019034905541001410308001e002c0350309212011070300801c0450341c2c9803400000c00c00e101030009906054010ba000c3c031400704641e0303481444070488a45c020784010b80c0c142c0c482c03940145050f84400507081060310550380b142c0040d0040000348540d040c40e10604a0b00c0300080000c0c20f0300d15041d000a42c1d6502c0c2901d524503410000f05206c0741a074016050880031366401905900115240c2d00c001703000e031a00f40f003804e18400112100040d41c0300c20b29540462000d1014903a00c0284198082c071019200141501c02030707644c10400680e000341d15104210b04c480702213000c82e40d24202030400856006002021845610302005002d90402111220034000040c0c60000704240c1e000c000181c5660103120f0443c4101030074503501c480072030390106d019540a80c944061901c400064640d003942d0380404c440c5000c1e400291820702000c100e1220203051404500c0c60601d24000a84004c40e0034030505580c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 449634181 1250 449632931 449632943
    0x20105060406090213061d18100e010308091c080c010501180e0304121e0c030b01060503330604030b0406050609070212130b0a1805060c0a020f030c0409 67
    0x5000407450240981801403061020640c20415161032480c8040481d210305020f20041c240b4440340da04181c00100e0203140002d1041d034078002002540c2d00c01c0720045550251403c041d81002ca10303001d01c03400c0141030300d400c080c9071400c01c0715030400e07c80800100c1d1000300c00615801200c000250300000100380c00407103036001050b594944400110015038414500800c5801c04550460102c400800d40d012a0010451b00009400500308698440d91080107c002e00b000700000c2c4003401008410300046134840c2d44000c5440c1e81c3c0c3d40044403140801d44040c0d8004040f90012074071003200c01d4040141090320403d8a00100285d4002503841d800350f442140d88186100400007032001d84e02c5150ba12070001c0c1d60a404516110030025220355170b90b030301d100070941c0c04102c1c401038030810b01c085006020b0541c075a41c0e40300b00020025003203545007414503041c2c569060001c03c40d410510161807801b070b0000003c150228041c0d00b0480d0315a44900d025425215002c500b64281d035a500601c0700d0140a0b80e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 449635431 1250 449634181 449634191
    0xf0c140406140609060d0b0a08060411010512010b0703170106020f010b0321030408040308040303051c0603112403130309080c06030a05070c120909270314040f060201 73
    0x500c01a2540c960000d0071220305001c00007060b40350681107a1210703108450385641c4d054628040b03402001190502d50f0009000040811100070000380c0d02d00132809000f601e0b410200d6100111120700c1080d842c18181140a001005107070856000307008006d100f424001c52481100c030203005101d00980c03000b00181d00c0300c1c0e0030b5511400c082c8113145c41d02400380c0107481c5052100034001141102c1c070003034819400d00080000c1c140008042981c010796801103000b503030740e03a032400c0040a41d04410944e903030036442ca1031441c003a1070003482107004880d8003400280d2543c402c0010444401c549510040e00d00d003a0912542c0e03081c284100840c03054000500c2d000d041421814014114201604114842c0c0c0c440220b400d00b543d101e205070b980c0301d91041404202941c40d0481240c014142140c01052510820a55280301e0382202e091001e550401000300085c041d04040048110308490808284a1000c903664001c00c0c8928180c1d8503080c1904e03003030f51806a039504004041d2901d90700020040c2d40d28 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 449636681 1250 449635431 449635469
    0x160506091f0e060105011404080a0305030103030e030f060402060c070807150f0908070b0d020906030f01090f09080d020702030c03031c050f01050f0d05070f03110f091003030c0f0c 79
    0x251030101c40101d01480401c251282882010b580360410700441e418098401a10810340a00360111006022210181d0318003503900c0ca4041c003650001c1c00111f01080c650b407042e0f0110306000801d114031078120f5000700420f0b104e41d02481587d40c4001c3c00481c1602402e5800f280302581041400001e01d80c000158400c3c40717000c0070040c11025800d990104000d200102004407240000c1c0000c26030b4070b5a10900e54800c1000d04030ad000b8803c694a03030750001d20200421400013078420081c2d0481e04004001d021103080c03900c41c00201d80301715000a0550b413050000910844903940546106803019045031040c501c6400064555040341550312403080003801180c410305003c2c002e482d08001404003000f0194108800110618094003996005501a03042101404410008800104070011130104820b03100c1c207181c81e1112440b03442c03600070340b0340d0103e0303000509005415078443c0304030410684c402411136504071200c03860440182c0c5d00c0302044401034045020100c5c120010b22445803580104079107 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 449637931 1250 449636681 449636713
    0x3160915110d260901140f0610090b04170c060331030c0b15040204060c290105090901020f120a0507020c03060703020d02040321091e05040216050609 66
    0xb00c003100e80300700902141c81107045030b05402400c40c2c00460700f1141010f582e07086213060041046060342c100400c284e60030b010601004291060103090141c4d80c3d12030214a850041c0c915180c2441a02981d0008100401129208040c0c02231001206015034442c00801030000b10b00341c1081e500851030841c1c81007440b16481c02c0c01c0002c1c044c80c4246520b4181d80302152406031114001081c0a0f20041c003d000040c8900e140d40b12810041000174002c41d260380e102d0b80010b01c00f64098104441c00c0009100f41c0c08002050b8440100c5085280d80240c11682488203002031000b029203c1ca0440d0740901188403500400d5014140108000540790780520303140007c2d03000d8500240401c0e00b55040100c82c180136440c0412641d41c044d050f801e0150b030320170707001071b03800002d104030741c80504040c0c58005500d41040c5030f803008071080d08840e074954a041d40c4602c510b401440c16030f031416240c0c8000500c200080c1c180360b00a08214203500f035050b45080c00e152201e03400e14030b00300c84c40c94141c0c1015241003001d01d5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 449639181 1250 449637931 449637943
    0x80a05010320031234030905010323010303020303090f0105010e01030f02060720100f0806091807080d27050405060d020904060902120a02032808040305030c0c150316091511 76
    0x108805c01d683d00d02c00343e031000741c14040d075400b0b040c1c10191900d2540400d4440d0341050701014200001d52580e070b41e0340303040003500c4e030300142d4401c01c503402900030242c5140814002d4505031000c0300c0b900031040c1d00c1c0d640c41000c00001007904070f8010a05020708404907400c8046d64480b895118907500c1c426510908004184250031615030900c03040020302940c1c943d200900c10340c41030342513515030800d84400c0360400c840140301120340054441d4075004104200041060070304450a41caa90f080807181d82c0c09690951407941d20f041c0f0b2488140400c1042d4502074014a0f0009400740078114010b0b903d8001c101e4142003200c040d0b0701d03103460b201d0076001c6041040046240000007070103803140c0d91140e4000ba80f64440a2070b400c2e1000014040a030301a001e18120880140e80401d0240d0348594900d026500d80d0400c2490f16500d000d2241070312690f04000c04410006410703241d5103460340da81c215078440d01003c0e00113550b042000070100031410900003062000900101d4940040710380d20010010300e004 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 449640287 1106 449639181 449639257
    0x90204081b0a2606060f010c0609030e0411121b0706050c041e0e0108070e04080c0106050a17060a0b0f0607031b030807080a050103200312 61
    0xd85082c240350740d43c1601800740d404640e00c074004c10205c40c0a01040a0208140c00c1142d0001115035004d503000b40d2007070610b0403100c0c1d010340126048035445841c070990741a00040c02c03800c144845200302e6101d0755180e40400202c2e800000d030401c5026100004108685980c082000e201244068030301a02841e0360001103244100c00903583d2100c2485150303c060944800410b0f8040045540700030b4400c0301104550304e0315150390709010790b4041c0311580700d55544c2d0034000c119a41c4140905004040c144210212000007040705428100041e1a0b078940610f84041a00f007a251001c1188000c0c41c2210f080d41c0710030290800b84e1700b0035203145880b80c2891540e40b00c50308054012a0185c0100011350361416503a44118003041114800c0c0400b500300c0c55035001010207404500700a0390080c0f0b0143c162008440150740d0782c0c0700b40d00544020030080e540c0d041d0802e80189544903601ca04 = true := by decide +kernel

theorem cover : BRFrame.Cov 449460431 449640287 := by
  have h0 := BRFrame.cov_init 449460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 449460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 449460431 ≤ n) (h2 : n < 449640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
