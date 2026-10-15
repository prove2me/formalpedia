-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:29.400317+00:00
-- url     : https://prove2.me/submissions/12f676f4-5f57-4b91-9dd0-05c8fae38199

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 799820143 ≤ n < 800000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 799821393 1250 799820143 799820149
    0x5031f0207120c020a080105040f030f031b110f010506100e0607081c051e1501121e050601091404020f0c030a020d1d0f0607050a050607020105041b1401030f0b 70
    0x40c42940c41c4994603d08003008a02c10022880c0442c1c00c03085260f8034000404c8000b40b070300030407480440d401d0f040001506840c220120040e1800f600054401004203d100400039001390354402d507502c10310709864485503810003c0e801ca61046030856441698024580805802a060f641a204000d40000d26005594441c610a80e210700c2d6517440d0450f16540e204203401d0a88a0036411081024402101c044000511001d41101511407422000e401003004200c0e0b01a440c0303a411240000750611240d040a0780184031030364401c607541c5596007000c0c0014900e40c0301e4182503013940c01156003200c102c0a2407003800b00075040003d400ba0400170400c406054010200040c10b00d01705641c1c01852403102d07540008002d140088000100440001d840c45030f140c0d60200d56901000003590342540302c501e0382c02e00d14504034050700301406c54041e110034031000a41c19000284103a010300401c10400318400e51540c5541200d104070408a000c5603030078940d546c86500015860709801e04041804c003920000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 799822643 1250 799821393 799821413
    0xc0327050d08090102070b18130b0d0303140106020d08011509031709030c09090d11010b04060f0e010e0f0f04030905150d050f0603070b0c0a050105161805031f0207 72
    0x30a4802c0c1a010806140a40c4d04004010150460412140c2460043d11201103a00000440fa0b40b080b15040541a8034140c2c07903000300348400c1c0090100c145180c1c035040240091034441e1240603520407100000c0303900d50000071400c010503140d43d07403149a60301c0c000d4070b1142003080c008600e040211080002020650000a280c43c810080d6410390352452844105854210410321840c0075005400412000302c50200c0c940c0c86010140c101181810110040305004001080321a0740c403619062004c03039620000420ba82c15510540201d40c02a40c07521018010080102e6203500907802d0000041d006e40d000000e40c80d04540300b8107200041030349460004402d04480c240030303001d000000c82e00c07058441a03401116049441c4144018040c20034202003a1030307402900610314201390000d20b01c0c80c030140c03c00020300004e401500030001400e244100000d1b4200462440c00003401c030030302489000c070303025940504442c001001804102c030258000c55210401c2d48088158030b07800e110101c042512085 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 799823893 1250 799822643 799822669
    0x6170d081b0301031505103c0906030201140f070f03020f010e010c02280204020f040306060b07060c2613060f15060c050718020403050f0604120c032705 67
    0x3c40c9896000b00e100c800c8040314001400d104158040c408100000400e40040c02405040c0c40e00080c40c030b41c8500700001222208d4921544400d810407000510b554040e03003c2c80507a8401d0340c070906691102c8070185000d000380101c0b145401400c104110004140023400c106244c424015121880c501a0080342110015804100665120080001010707810b1000c0740c01190b0741d0303180c00c983c00207014001d6410b01ca45100207018a900040014002a890069074011039001405004e030039201c0d80601700302c0c1c100b140100d4543c0d04100e0314030901401000440468800352044010b8500f030300e4030801541d04054288140c2140142e0808046603490003022a401130341040400c1c071445003c2125030000d500e03400b400400c060b9603c00c00004802003400310031140420f1010207030089601110f0001c0c8100c0c0e0000340301e0703c151044100d503001c001c00c40c0d500c5036004544100c500b10300b1040a840b60120000c0c01000101004513019459484009444101504c02c1c03401c0315050719a8041503030a80409 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 799825143 1250 799823893 799823903
    0x9041b1b140313060906020312011404061205010c020c090606030a0c0530011a1914161403090a0512030c010632060d090201021203070c0606170d081b030103 69
    0x24900340450b0f03405c00890b000501951006510307084d4980c4948540c00c00c10f005006540a40c242440520b41c0e454100c000a48118054818014185d03e001c074000c01d00220b140000d802180603101151800444151003940003400b40b502d140c1c0d600b0800001003003812110004e1003418040079074080440b400450003040c03581e1941c080701d580c044180300f013600141c0c0300e103c01d500c215025110f01d40350130060303810a50481a00482c91456540c00303449898126440c001c14500104903580809444140c5011980c010740381603910b0604140800c2d1240318441c0b209030007049510080115003410301180340220b1121058904003680c0700960f500f5500c040e8081e00420f40c034004a4501c050401c030b480000c68502c0700c031071a0b040078040d0102e102c2e4014481c00c07480d000e030750f80520b0bc00e59000380041c0314030a01d1000e140390382e86049500034002c190012001c0c0c0b0b540c0d2400c000413411441c60125003514040c042c0003002c150b400307100304840d000d100608402075030000c25040c0243c504044041e5020f54414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 799826393 1250 799825143 799825177
    0x20a061104030b151f0909020f031f03050c130e030a05071202060702121b06010f08010c080f06090c04030501090803060108060103090b0705030711100209041b1b1403 73
    0x40c1010140c140000d4040065801451300e4403800369181d103007039016005001d2400341c040888620a440041a0750705c80401b0780d00004e0142440314000d40118400d200c0c08406211403910f1403000c405410890000900d5540650b048140c0303441c00d41030300070710341b909450046541003040c0312050840d00400310241c04110045551002c21005a50380d4500d140b036403005120b28900307040000c0d0b8800080d0789401d0328940008240c0c62001c00002489400005002202c05a580d5020448840d803c0c034443d000080d46800042034066120702c004500440c0b200386c1c1e80b02d0b42c2c2c503460204403040c40b0160840810800c20000000010001c2c014111300030b004203040e540381c1c42c14200151003200000d0283d07042500d030060040008080d00c4245400c4542d51601d140c5075a10400300b60303641d441421416042c1c0c40b40c0456071440c90403540007803a006100703440c280141241d50074110300c0d0f210329501c04004a111240c0c082414128400340e035803042c0c020081c0c400036030910003405040d0741c45141d81d06403142d04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 799827643 1250 799826393 799826399
    0x90f0507020d05072f06030f0106110304061e181509051804030305090f0a0b04050d05030c031b121305010b0604060c0206160507080609060108011505060a020a061104 73
    0x10300841e002a0b0b21401e00c5482c01e00c05507149090680f00c0108004022015080e240d02c81c403042001e045440c401a12080d0f403802e00d5608141c8038482407050400080080822201481001c0181c0301102d50948074019040e42c40b044880c020010500d2800422103640412245003c85580c0e080040481c1e845900341322a641c00020003209660f003209000d5a844108040650700e00b0312a11740c41074151a00007000e4031030140c0c82e801c0141d83d92811290381b140d000c001b400d002500c2103480c01140300700200e07085250f00c900c06407820b00048074020202502480004c41e2544540b2951302011014004249000c0c441c2040c015102001c0d55607002071010020800c0030044240f10305507030139404640c81c5090520305003004ac82c00580c040f0081c0100300c0402c0031308401489171446039602d90300005a60485072a0521959281003c4941c2c0650b84120341c00054141410b100720640c1340160809500c405080c07405200b103542c040900b02c0110b01c500400d40c000300e200351165010701401182105e5841e85 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 799828893 1250 799827643 799827647
    0x90f0c0b0d0507140301061d060f18030a050606090a020c150702010c020a0206030109020d0605100c05060f07120525120c17040209060310090303050f0711100b030106090f0507 77
    0x4014409001c0c848105451104d0b02040000c0d2811240380d844d001c625000c001390806a0b1043ea859040d03001400420061008601e1074040c0840d00050784c41e401c1495140c0003010381c0d0701c2a90300007400716000030300800d80c9410481d020950040c107a41000d46401c150f0b207903581c030b420245620601110080d03c24448110342c20300414182201d00d2008050084280c2c00043c01c42c881031180400e02d03640021042d01451990300410000e00000344208855200e4000140c01c104400c01c048503240155400183c92924811340c10f409a03109503038000018990b01d142400414010b04a02500400d000d130117401c1c91a0281030205005855031802d0b203a4554034002401c0d180c00c2e104000c1400002400c0c1903518010302c10140e0b005804403100b44164448401290a00a08941c4402c0690034071a403441410b03050b810050080c9a4803071604115544c0d00c4041b41c0781c950020000e030940e0441c0c04411220082070b0000c04807281d00a00004074140e036050349808480f802c0101d002955112020000003503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 799830143 1250 799828893 799828901
    0xa020606090112051e010f0905240705070204110403053a0c020613030506010b0c0c040b0f04090606180e1002071203020c0c060301080307150b13090f0c0b0d 69
    0x8002c0315621088008684d43e00303900c85001480c41c000b014414070504c0440d500c2500300c404031051088040105540718101030361906200452212488a02c10007180140c1d43c58072100d204030341540d9a107080561035030800003d0b03c00d188102d44584024400400858410b022242c40180c01a802c07454480c0700c0e411154110000050140300e4400c507604581c00c1030b03000380152503002d504661840d9210380300400c2104040c0d00750805000c078402c4d00008602c01d182d0500070074918007800200c0d0b4812000c8005c10051359032158001d60454901d1503051071a003000e41100d945a403240e14081006901d03a05520b07240400c2c3da2207401c0141d00c5007c00800b01c00709211b1094101042c00d4254030303000040d110042c0210a2500d02c4081560001d0f107004da4010a02440307104a4008018990382d5035128840e07a82c0b034114507003c1d40c140c01d6000504110a0151013425505a40a000c2940c540003100120004022248050b03a1001601070a03c00252340c4084040140044503911030301c848411345c0c00000c407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 799831393 1250 799830143 799830149
    0xf06050a0e0a0506090907060e040f0c050c010b0616061e18020f0a030b0117032203120306140d02010e100801150207050d0b091011030a0c0e0a0e06030a080a0206060901 74
    0x141c00d170a05001c44410003241c0201a5181410b25104a80011000c58001c02c0610385402035289460182c4800e26884002441c0d01c1d00703054002d0142d0345169041005500c690402205204d4076507034684001002e41d044034008104941050146501c00d000d0f020983d1340c9544910710013503400070361008601e07000040d81c020110544a0400080c1160f03034075080da42c3c044c000d030799804103003113100207000f901001281c0c14015940801000113408210100f04122580001c1ba180d0341d000ca02c0d0b009140c42885443c081b0f80f4602d414132101d20502e418805602500c54090b41000140344e500d03080d1b6124040c0104c68100f05549204642d854049007038904006c60b0098800c540240d101041641d5812004204a03900a4001c00168650144840c078024030b00000092003410510050301030034002c409548100d07a12042800b40d41c900080c11034a287c16441d101e5800025600d0034402c04600014150348101301400300c481c148601c0e100d81156403c215015001684090200000e41c00d240d0102401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 799832643 1250 799831393 799831399
    0x19150917030a061701020c07060c060e0f333c071412040809010e04020f12130506060103051510090618120f0503070b010f090b06031303030e031303050120070309090f06050a0e0a0506 80
    0x201010400d0400d0080d072014fc41403102c0e402d40201c1081c01010101d041c2d20500002011211280795400c5491014000b203e011001c51035048440f0120191002100c48060b00654042c40c6603482c0d94801c0d845400070605241007000b11031142c05103854a20042034840e0300c80d840349031a2800e10134101d80e90040240001940c04020300031500107600014190b8003c0030900b0007151607076500c03444018034503001c2911544900000f500030520764004480302e013036070300c0d9954043c543c00c10112a02c8036501c5034800d01e0b00300050b0307170103c00c0815008800c40c00003034844d81c1603c0c5040415251084640300a030000100310302c00ba0700c10010344d6154402c00440c0c5070f05440140c20351802d584524101d203005000078080c1511446c00364410401441160300d1400c1c499410710f4200e0312030034058001d103109421604c46201c12208030254074800b4042c0e461050303050380d80004113803c1c07614540c05020719065a6204075200c250204440da2540d4030003020b0000d0f000034080c40d18100c1603600503546c001e401580 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 799833893 1250 799832643 799832713
    0x901060506120106031806020a0f09061d06180a030c0906120305120402010e10020d080c2a070803071419150917030a061701020c07060c060e0f 63
    0x10203000c0c2c03110050458240707040c0050010034401e0f214640144603640201142d1000881c1c0d01d480340c10032014840b4082c2551140469902c03240305803240c005e0b82c03005040c442e111289031000e0740380c0b8200410020b5005000c04000403103140200c0d2981c0d0607030b001215003030300401c400e221a401070b20030503000380703504481d00010540b16100601030384640802c14034002500c030300280075039004000d14400700301c0160249107169207a42c4020b44408042d000e000006283ca070208030212041000e1b40d201c08051200340c0310400d10144c00e148a07c0d22542e004649014a0000040580003030015000c240e00410f402e0700381e0140103004a0030802d1141c4031039914001c036280d400c089440c000b8540001d0688134000181c1504500b0500140b00400b0900301094900104020301c1154581000701120b00910751160004601c810250a0f03000b80007041d04541e00070041080341710b1007014211945800b030707900001d82070044006a81010b80f00f411443c0c1035800b41c0b840c2204032881c80c450203203280100c002e1403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 799835143 1250 799833893 799833907
    0x1109090f0702151b0d1e020d0606030603470a0b03061b090f1504060305010b1606381002010903020a1209050913060b040203040b041b0b0408060901060506 68
    0x41e080e50307100c80307043d032200e200800e94800d41741807039010203064201950340105810b110180ca20180d40001c403c0001241020f100090441c042c1c0118002d07250300500d24a0341441d181c030043d0142c1c0c80f1a480d40d0307169038898462100e52042516002c0080301118503242da41c5401c0a2800644200403205402030f44070900b00300c10030004e41c0d6001c040001f445078040c0d491008800140c000307000707040f916502c0000301c00c0030380d01e0411000c004e00c00c540071900c0038000da07030b43d600c9441c049000705080e4001d0007025000c88800660660300c030711070000070070200300d502d00c0f54417424083e4510001c00101500394004003880c014607040b07a11010145040c4024000705000395070080d20340700840b40082c110304800c1500403e45020b110048081c00011780010b10601d0586004642948040400d0307400030301e0080300c1151030030301c0d00860307214a40103400101e281d26240d84109000240d68582081490100d0307001c2020300040c8010801008110020704171410007050f01821074010342d02c41845841e041281e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 799836393 1250 799835143 799835161
    0x12060603011d1f020d0c020c041a060706020c07180c08060901060c26210c070804031203090b0907181b0f050403050102070804061d131109090f070215 66
    0xb40c01c40c0740252030b40c1d460401c0c0030f10003070003a000b0700210f405001d040c40d11a890b019070009400025280131034007480002c00c28061004403500366208582c21840030030400c4081003041e0010710380e84201c08100c404071030345c4da41d8402c002e84000b091407008540b2030031100a1294410046034124804503941d15603945888000740000c4000750008291480042050114a544044c0d5a680400401400c0d030341d29070603031440c1801c072180000c2c6054440c00700301043c001e900030700c291041075502a14181c41d190440d03c41c41c00f128000980d040802d170b15448c80a001a8130304600c070740601c11002c0108011410304c6180d8003000101d000c216066031070107241c508002c0a105813060010f000303042c18001002c80141c111090b20964001400310360001035107200300f000b510018011600a43c2d0740343c9420409421211150940f1524964440000481c407041e240080c1c1c008203501900220880c0b610503400301180680404543c0d03041c981d1094420421041d4042c0418400801001d40000c0545800014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 799837643 1250 799836393 799836403
    0x4030302040503010c140d0902040603140706080109020f041a0d09060b0307050108060a0e070c1a1506090306040308100527090303010f030b0601030914010c1202040b0f160212060603011d 82
    0x2594500d552202c001d01d06540310bd5008401440e080450443c003c8140b00c901d5a80e01e00300d104540000d14201c000190005427403007503074135442c3c00c0c0c001249400d15240d101e11414103021007840b00000100320300614802244074082d81d40b40301340c10118540c08090201410912194011780c10300a101c8204100c0c2c1d52502ca40d10195a1000b4141c115500e03440022100c003004200c3c005c0080c06000e521511170010607031440e21586590403a2820b060908043c8070443c090200401d406030700c18804240000e00030880d265000744041c550a4029a07500005550305401060681c01d1814140c044200602425181a800a81c0d45c3c002c2d0b1031940b610791071101010840c40040c045415940200b00c1581c406c0d04400e03001c68000c40d07144108041268124000d240d0f00c190040418816803000b1f40b44c3c0c1180c001e4408840d44060024280746248a18070144e5002d41c08103502c003514944514010303581d03c0c081001e60f0b90700800030116450300307d05250845d241c1c1c142828240d03108400000c140c03200015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 799838893 1250 799837643 799837657
    0xc0a050a2601110a092108070b06190303030212061207060c020f04050f090c01020718020306180903071a0c090609031612020112020f090d030c050604030302040503010c14 75
    0x60480403088007041c4550041c00c0c50b0058003450030000401803245507024410794155102294620100043c80f03000c102c0001d100040201003103018084c51022820740c501076680804041c0c000f000c407012604820080520b2904101c002c00c0e40030404103600e0320712102140d8080b00646104044034481c10036543d40303003031300e200d59403c004e0700b12042c00464541b40018004050090300500482c00d00d0400010f12440440318440544140302091165610020f428822514040f1142d02c0340000b6100c5d0b1000380d8801001c840e00507405d0108540205405101c861050b10080f000c2d507200d6429150413120b070321241c08103090358000340d0b0030300603007600c0c0408a4180c0c0030308544050391104071501103802c020343d8030910b9810b10854a400140c0300d0381e0b0403441003140d2003640c9080c06121a046076104178002c0c11403402442000f071004c40f609080881d4603188840c0070f4103151400c400d10741d81d2140f0b4000d0455080300000c1d004034042100307007000d0081c080d07800b48500b400c07000003540f1201028139010f010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 799840143 1250 799838893 799838939
    0xf04021534021804080913050411010f05091e10050c07080f0c040f0902030f0105010611060412140d0606090303091d190e061f06020f06010312031d0c0a050a 69
    0x2400b06017000001c03012600c0b0800050300180522603001d1118000388401c440545071000c00980f5030300e00b5031050f418141c100e01c140e115507041c400b40b102442000e1104444a524289580100340300b295640314107110500010782d5003039035900940b9030742e50034030070745600c0a18980d00c810041c0700005070104001141d80c1003910006289031412007044c01520380e20074040d42502070601c0c003d2006d1410340106040e80c100b91100112034050b0100c05555000807100603000b10507225180f121540b18a0031003480c014610b6045080c10000c40d03220f4201c500940c0710801141e2401c81c20070800d508607200d04010320219100c0701440c01d8184481542200003040804000313035031540420540656441400e10f00c0c200012510320780f0749041103c1c01100e008040c02c600a0784400005941c520005d04c00300032821110280410364655503901c400d41011003001000e1545803048807207904101c50403126209200c0e402040300c480d505040c000b0408840d0401030003401a90403c3c0081480c83c040d50400340415 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 799841393 1250 799840143 799840189
    0x1060f11031215040c0c02030105100b0d0203130c06020a110a030302030909060303040909050a11030604020102070e06030a140312070503060102071e03020a0f08240f0402153402 78
    0x8070a0b5044103d4040c0300700c0e9807191030003a51700d2840741c0c400d811070740d00380c801d6008000c00d0f12044803a6284003010300c6024140e030400c0000800317040c0340b6006103401c9580c00d80119005682665601c20311030642d0440401a07014031100310600ca02045660400c0c031043d10f0000190b800c546009449104200c0c602e402004c0000100e20a600c0070001c4034020010120100010802c41c50015110221650700b03076210041d40255424500d800700c2c0700c0f030103182d0503001010389034a03150f101c0032091801008036900d0f020b1248180007240701a81221141c40060001e941c0d1105560b030b01640700c003c090040f01c20860140708005950341c0008000040d07035036a900860280440c00c0c0280d02c5200e1a030002500080c1d154000203080c050404100251003114040d80c6101c0c40488451420024102c0c1c0e12500c6034904010a43c0f540b258030000b80c0146c0080c0800b4a0a0000d8240100f10303440858210b50f64980ca411509140a000f01004000b204240c0904501c400a8000034060082c14144025140c84 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 799842643 1250 799841393 799841401
    0x161a040b0f0702070906090b09100509130f0519060e010b09070509061e040f080a051009021c03110d0e0901091e050108030a030e030310090b0109030203120301060f110312 75
    0x800118000f0020741c2002c0c44851f07103030018070015041c01c04e0b01c10b0140400c0d501143c04407191481040c161140074181130000c0d5220140c00c1d1440010310300c00e999982d498940c41c00400d80500c069813501c0700c07140b01c0d0000c81d44e00303140000c04c80351902d100408a034074050079001c5954400030255040009490400d03124021030740003501030b100380030403a2400001503010542c48038071040034104403030a500c12401650703030307405846440b000b403028003c000d6007000c244407826201d15030001e0b40d10f0b4005044e514000600751000701c0844451803081d004110441d0802e581918200845044c000041c50440564100040401c0c2d91041c10b0055461558980d084c1000d10310000d054510825480b41c81031010756991a5081d8603680440f04610010342091110f0410781d00c00011a80103160b1180244406490030003198010700c1c0d01c4406504000c4074440010240ea000c02130081c1e070365840c4010b660389524040024280c03d1861001d603040c0301120740e40403146040403040c0c1320120150400c106c41551 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 799843893 1250 799842643 799842647
    0x5030f070e01030e15090708030a0e04020d0e031c0b04020a051207050702030706230412020d0302120f03100503012d1b03050702010c0809030703180902161a040b0f07 73
    0xc4060129940703204410101603d0088108210b01520035038081c2d48006842d2310f11951240314000380320000c188026943d03581070406038010b1080b034425001c00103000041402e0641143d000700c00100d40400c2307040c0101c81003003551091101c0f0200c101c0e011840c00582c890098000d001e404504540030140703000040109001e042100c0d0100c0c0d0007804d4a0111b03403100000380a20701d8414810420112500d04400784003010012101503a03090395a00303107a45a41d90802000d442c07045400c600718020001c02030201400500a000b1901380f103215140c480ca4a00e00e100d90301e080aa01161290703041ca0310022143c842003a5040020524410580a68009541c00d101822200362685058071158455414066040e0b004901075004c0d40d00a0140748207100086030124001d44414601b6082004088006401012143c00d50394000304449400759640150700c0403a04035103540030309042c0e40b031201001c100d4181d40245080e040b15031400b20713506282d150505007190007003070010b141d40d2039070200300054 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 799845143 1250 799843893 799843901
    0x609010c09030b1005030102070b01030312061a090a15021e0307030801060c111e010e100509062203030c1518082d0c070f081b0105070807051c05030f070e0103 70
    0x8000038001355680d80080c03910ac001a1341c00d1200780d00181d141e80d850754035080c0c903015040846443d20b0900281c1d8001206a0700b8507802103648a030710a003d1100081c00d04c0d000d280c461007203292034001d132141c0b402181200d400c1e81344030760f05002c02c8c1c0c008000400001ba00f140c10681900c81526000c43d00390b14926082c01000c0000c0c501542c03040342c4512011418000729440c040c800c1c0282ea4420783c242c1100180000c600c2c0014246000c83c0041c400c1e0b40030b40c1401000b03828400b0360a8400c83c2d1140c3c04099004200225030000c4e00010080100c2009001e4501041d0094400130001080072426075a00382110300c608650041c02c0340740c00140300e40404117514281d40504503001e41c004540c65001e0041055510100550b4018011110001001c7d1002402c4a085916520140c000325081803001c15441420701c08440c10301c142400310102041c8041d01904406e0f11402c01000c40121501f8061007003200c40900100b081030030020050040c500c8003109030080c0702803c20465410031400140c0140c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 799846393 1250 799845143 799845149
    0x90c030106351c030b040e06040b07052523060403030b04060e070c0b01080a050a02062101090f060b0405030319140c0a0c06020c09180c0a03060e0609010c09030b10 72
    0x14480c0d1501602d02ea0709903c604a41021075860403c20410000140002d031881305003900f0b210342008000502013400c4c520100c1c3d0200e207030319190303180014140450003075120036220390307140c1d45820080d40108000449041107040c0d41240c207603140119007070441d0303072900c004000030b00705070b00e9070380c81a015144c582047c4080d0040d1744d40464079240c0080e00900403d1003a000f035036103100000001800314004140300510a810002609075819123800744061035200344281c0809070301c00801c0300004101c5552890103004081d2020400081401520017507444503044585801c2c4104020003d43d41c00008403420a10a406801050503000701c0c20b841c3c400005482c517803858030020b008900d00782c011131301400d034510071900610301c1900c61104990390130300900c00603000200d41c03010400842039485010b83d001040e03801c03100c070a21680c0100e26000a81d41c0704940041c0c0f140c590600e000024051107900a190344000c1006421740c0900501c890780a11016180c800c83c1070204071043c06a010301005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 799847643 1250 799846393 799846499
    0x308090d12030c030c090f050603090f1c0801140607060f060503030f1e03060603010b0d09051501090b01230c07120c0303090e060a03150b0a0e090c030106 68
    0x807215103044040e01404000001d0030000b0b10784020003070301c5d0b03014088440030b4580c01c0c0d0030000c03800e04103003d03c03075241c0c0042c1c54000e081c490103607840c02890302005440300d00e0701001001261407524000151040c1d2041e0000c0281d08034082070000140c581c01c054030744c09500150b0220b400c1140c1003841d802404070b03406c03541e0140800100d44126a9420b0000c3c089003504084400f40500780700a5134049000030340d6074540c48001040104100252080a086000b83c5018009802c50844d917809190281c11404542d90034000401081000f02501c43c6000307a00081c01c00c410342031a2a8100c40c04260307680c2d000000c3c48004a0800712108c400c00c2100c01900c840707044800d000509003403100a0000511048000540807500411040d46200c0c0c210b0154402420309259182155245183d2840007130340c001d0015070b9000c42e15010b0340c80b681150001d00d00070b0b004103041d003044c0c51810305103605040424000c0e030610004120f041001c40307014407030601d40202d402c0380004071034124098120000100310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 799848893 1250 799847643 799847663
    0x2070605181b0a090c02030c0706180509070806012a051c1409090a091e060c0c021f0903080a03060e01050a23040e0106090203010317130308090d 64
    0x1d084011114084107540441007194002e007840e42c900c14003103000b0000e09400000c0203804000c0710307482d80c01c006081c0c401401920b007081c400c0c440c42841c0c04826440200000c40041c140e02d0303030740d440c5d0b160f03003018000076110386c0c8075442c2c5002c0c06040a41c01610503410443e42d088003000b100d8200c8e084d810700b4007003403011044411880c1051951142e5941115920789120f888034072800b4059200a2000090595050306140c40803040285201c0001e002442c0f203138580610800095660044d00100b401140741010103156170b091034011240036001c104c00340000d4950302005070b44d9100c5191401c081c40326140302607060781c0d0b034111201501540014a003040125011404a4040d0007032410b5a500d000000090381c1d0b03910800285e41c466110343d040e030a90782e04c1044620412105040c5400c1030280c400316004281e80c03500390869040da48112229a400300040c000c020700b8a070342030001021030442238140069104030011024003032000030070074003000414075655203480c1c4006040c550400301c1c000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 799850143 1250 799848893 799848901
    0x1d0303041806141c201002100515010903060e0118120f0e0d11040603050a050d0311030f040b09010b03030408070906240f120c032304080a030905030c03070c05011e020c0d0602070605 80
    0x1c1e50b81c08c590b81d070040300c2d00d00f403000143d10301ca11001c2c5007034082d00503522074045520b16110000100600f1103800002e54275550071040d01c008140d0f45100e56407003070b200716000420401009040c8464034060000b000603140c0e10f25110340d2001c500c4246c1030340043c1080038036403409000a004011541c00141103008003000c0900307100d0013044624900c44261030900044a440030080e1092100311b41d00400b15900c1e8001c00c011542c1e116903190711840c1c05000240c0b0307083c1e100010385540c0041c2e02244031980a000140f00714442c5006100080400300c948001c280348015800e91041c443c112200100600d9581c2c00c512580b084404400d006600b074020401680e1001000380075007002a08911600248144450b0205441403424840c5400c8a003813810003c54940803005444010400d95840c482884070310150300d0140002c0040e18070520031116880c0c601000500b0407075650800300b0485020304051000f031a0042440403d0960885030540700c00d60034900f0000034000d8500203400306240c0790800c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 799851393 1250 799850143 799850147
    0x120a080310150206070c1b0305010606110606180402131b0f05070b01031e1709040c0c03021507030603080a090801050a0c1d0303041806141c2010 64
    0x218001c8140a078011450350b1074801202c80300e03240c035400314016404100010301c8a841800785460342d5102d03084503040640703001c0704400030807580d400c1a40d01ba5500c28040000e20b411000c5103095101c0c407409004c040c40c0c404002021803100800942d1089041c80c001011580c500209090421800204000304640016150060154880c079100030230040700103a05a14003400990f2407040d840304c204811070f801c594904400341d1821900803840e1304002280e02c00a0342ca0040144440c111031942601c5081c01802c00c0252a0800c46030350a020005d402c0d0070100354041046103100016460700348058039400000c600800241d400030b4104030000c103d00300056841085a030031074400000078070258480c2e2100c1800c50b46000704070340210703841c00280c03600c500c100004007506440003030560f0f060941c1e98800a03070200c4440340070b0517213583d80c00b400d000b41000308031104c0c1c3c0c02e0400c0d00e104401000c1d085608200784a030400281a41440103a020101c42040036502c000314800350000c00461401c07100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 799852643 1250 799851393 799851397
    0xd020106051516171b0c030c06070b010303110703021201020d0c0809100e250611120f180a081e010c0504030b102301080f060a060e120a08 61
    0x11103100344449490407040c1840700d026640c5444150400c000d60407490742c0d460783c0c4030180d4840081c01c2c28050200e51040448480304200d052110f030060301002c500103041600300234440c061a841402c09102c08804203580f06140780c1035a5260520a80c8505003600c51890580c0c40d80c40294058180d185403440d03034806401920349d0f084044014032030000d81c41c0d8103594805049400c4002c3e9407149014042820054010350080f10345007007a1020f80c245d14545a460034615024000c0515110004101c041d505c000100501d001110140ca0440f07005e00f2175800300d105e540388068041e040800d03000054001070403001c0101000070a42405141e07140f041d0740d00d402a20302d40784183c0c00310140046c5c8104041c040c60586e042e41c2c0d62118985400c668444181e440080d152242581702d844021500b0340c0d240c1042c002da1000303031038148421092a0300044c00150010000b0a642da0111305000c0c1d00d44404c0812001d5071500d04100d06042e49120200b0f024007515010001c00f445406d85080c203101010300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 799853893 1250 799852643 799852649
    0x1060e04081809090d030b0402040e1008100504020307060c08160c05120703020609060a0921201e030a05060a0603050f0609060705030a0905240105030d0903120e030d020106 76
    0x48103507024603040341040f1141c01c0448201880790004901e02a8080c4a42d006000004004000506103a03c0740ca8440c9000001c490100c00c80000080a100c00c0c4810024004054900003042c0b0141c54030783e001c01c0c0c84041c3d0b4802e074010f0117001000042001011000d035035500b00c8180c1c00c2419a8181e0400f144400010300ca56402400c6ea4152075071648030200d0740c00c056036005841c040c6003103140300034401c0c2c55005007450f030204a150307040805e00040c0c03041400c280300560901d007207208200b424a20321442884006403c1030401c0c032054105500c42c034880302c402400c204904211948028042070900500c0301000703009005090802c10b03e41602c2d8404004d80e4050000c4481082d0070080e001c0c0d590400f0f541c9040258000c00000f000341d442140155444a05080082102e1080760f681c0341c5801f4500102c4415442d181d115190902d103501c6070706005010850040c4111030310382c0001b070302c40d81e8507000c003800c540c401002c0c44409500550721220314510183c2107910b05064900000d0080c0900c2c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 799855143 1250 799853893 799853917
    0xc040b1612020c010c1520090312040e0f0403140a1107060f0813020102010b0a091e2d0605030d12060f0b22030c0b0c01060503030408120a0201060e0408 67
    0x1220198540c800550710701800c1041c3c545110071801521380d1b40c01480390b801081940754480204010400300345406c800c1c070301828250107480c0ca004201b0181480d1b58105c40c001034000c2840200145488181a41d41045d0000c2c000f4115481c0c5007800c41e1007404281c1e10711441d020020704c4a040036400340c881049982d080c0c090f9401603880345011a109a4048a002d001038114404106170603224041691038620500000541e1482d41000c5002c00d4542e6008a0980d80d4035600400c2c980380202201040015800b000c00101d41002c01401c05462001e03800d40364001034041c944030042c07960b80110045c00d40201211120b000c4c04d44001d0418030035440c41202c3d60b0405200080569038800040e042d641500a0700d8144880e80f500c404000103462040c1c202044699070000200d03202a072043c028124240c0c2480c0d64a41e01c0005038251005c40d48194001e60042004202c0c41d0703404030743e81d228036078050105a9600e2080b4400c0380540b00a8000c44200300f05102448200200c00008000c042d00e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 799856393 1250 799855143 799855163
    0x3061a070c0e0606092e17130b0c07020613090c1e090b0307121508010e03070503180a0305071409090a020109091509020d020d0b060f040302090c040b16 67
    0xb0b030741d0307003440d5901611020b82002c01400352130124545082805599100395005883d82e02e0742e8a0f00079140c0743e100070300b540070454942a00c0115a03000c1c03005a0b00c01c030b451038810800000b50f510508800c0c8001c0c240c00c01c200c80840d040c000c643d90311086901c00d00030792006c501d02c01d480f4052a401040300d400500d000c544421040b10036411641d02166103000709440c0c5024492600408070040d610003002c0d801000303299a83e5000d064050300c80c4000040d804511300d04e0003414500700c64212620301454009591042c0900400100004110751103800d5400320f0f8451070f1480404148030071800d403c020302c0e50040800120f1400c2c000c22401102c0c0c481200c4024041d141d030109e032a2190110340002c0e00098008000b4040120541c00c107025000c1c1002e01c03032241558524040c1c1c00c90708614810740c0d01c2500096494008405800b510b401d40c00202d40892030b0648201700090749100d1444000d0140000314006091004200c091f5001806403a1450740e0f40c3d6900f883c0c100e4540c180100440e00000710b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 799857643 1250 799856393 799856399
    0xd1a01060c080d051e1302010801090e060c0901020102120108060a060509010b0d092a0807090209030d1d06071a0c03071b060b0d0f0c0603091205030703061a070c 71
    0x1080e0360078901c00d078205041503c1d290a40e000d00015001c014100841040c8205054000c030100350b03001e610844100f608110041c12510004005c100706074070180301a03040c0088254424004190282c1007103a0741c01e841c1c1d6030440400140e01a0040d11a40c0d03a61048640c00003030038040224001e1711920b440070040110503145c50400c405000d007170041c074240800c280f01c1e002c020307056607100f0406540a501d51b01e5605405027409142494201551100c0d00f0010100304148041000401c01070070203a0390039410401c142012039aa030b402e69078028100113030700e402c18101c555440c0000c4882da10103468a41e8030042c41c00c026018546e0702003241d06001050000a00703069801054900400c070a50352030b03140010b0390300880c595000030142983d03ca0382d103464003281ea649889012240c18032617800c841c90451141080b641070102588401c1c05d05040184010015860100050f07400000d03040440c0c032034841c2c2000b01d000349115003080c1d14600c0d00b041a0320182020001801c4031038820b866043c1e916071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 799858893 1250 799857643 799857647
    0x1806090305181f03021b030310060e1e0d060906113a0b04181202100c051215041e0b06040302061801050c01020307031d0d09090f0b0d1a0106 62
    0x110f03c0700f800c0b50489003040080c0c21446500144502045500c00c40110889009001e085a000380c13416001d50049100421909400403c40c900c182c0088a1055403090391030000c0c4070160902c600c0901c04e1950000031820049968444015560860020400c00300b031503a145005500c08803204409160140b07075040880c4403880132042e14407400b01c05036002640751842c140642030404001d5800745e2180700146840601b480a1810346d8001d5800001000ea0b2180c041d0404600035100090f00d420003242c8a05180c01c2401c4079030100d0604010314141d0350349a5080555101228400e43c41410018580d40ea03468858038507403179a130741d0b03d0f04000400828041203000c4c404c1c0c1c0310013500418240b042d000396046855072440c5020060408902d005640022542264800c503179440c0869900e82c92a80040800d14410303084480c92001070403061125000542040f00d140b14041180e9110403411443d4400350f00400320480e80900600d6510780c05140000c018124510000140700c50b00d0000940d241c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 799860143 1250 799858893 799858909
    0x10e011205100506010210051e09120a05130503011805061501091502030f04090e1504020105030a0e070f0e04060b01081902090604050901090c02100519180609030518 73
    0x50740240146440c882481c1d90601a210003481c3e02e055010b18102e140015110340200740c4550b140943c0c078a045c00e20012050300c1c000c0081c021001d15071201161108540051089401055a600f40030f901d4807647c4400d40000116030b04500c4c0c240d42018820044070030854484403040c0d110304169015540e460380825032074030f220b4031490f00107842c110301004050800c81850a04007814816641303000d006c080e142140358030591110303068a90752144541c0102003880119419440f10f0f41c0c0c42002c2c18240c000030f000e4040070304403000c142d9862400300340b00c4408001c480020030403290814041c0e40d507803807109540034048070162040e5007800d03401c1003298481d4841503c503050a6004041031b40c84d9004050081d0001ca034559008402000f011440340e0301d00706054020030081380e0120f181181400001d06040320002200c1f425410b0106100400c2c0e0644030414102041c4000001c580303884101240b45d1200008000c0c0c40140b40c6000e00051503441382c01000c01c15072915030070614a40301e2040c48108 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 799861393 1250 799860143 799860179
    0x402090a0e0a1416020d09060f180e1617040503031810020301090f0e0a021f050d050a0b1e09070f0c0c060e030d03180803070c05070905010e01 63
    0x8801504024007064414254980e0003914207080020142155490f00c5408102a40c0c00c848452024031110358060341000720b40601115460001080751800001a0180c03502d0f110f5802400f503106901c4411200310030703c0c1c9000304000d100c0141b5904220341c0358080a004d43c0c5a41e00000c400e001c1c1c0c0718480128000ca14081d503800030065156580d0090098024000070210300403d00030341071113019090103800a540a005001030000350045010600d5003107a141340c8900d21070350450f202c5036000d030b0345054801c1d204c10f0b201d01400d4070380460014200d0301440b483c404100c00b20300d85402d000056620794095074400c681a00e1101c5550f2980c2515400c000070303801e80d5584400760300b0012b800079105441807051001941802d406140c403560310329141e0718842d00100d00003050f1030040c0103540f4041119101c007598606007007088508080a84924949205020b4031428000010501061091088a00542d000025110b000c1c0e21035004001404080c07103041070824440c400810004d180c80710110786 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 799862643 1250 799861393 799861399
    0x60918020708040905090724030608010b01020601050f0d0c03061b140a0c0311060a0524030a06200409021309020c0a0b041e0b18010209090112060b060705010515040209 74
    0x1414031344018240a0400203200e81c0ba54083d19400007070000c00807000c1d100700d4107028080710780a842d040c402001c80c1c0e401d0380106003e0781820080c032800d13600864890b054403010340324140c5030803990300452440702410720018803e031500710000045c412103902040c041e0fa031038110701ca1544440c950031a50810200c88250711000d0070044034400c280164000942e6038440d04069001460320728103d4108407044030380b005c0c52915402000010f0850f20503a620012002d403c0c50003500d02c00b000300c4e9840045400040485a885035040c40600c1103000340021029041001c2e982c0c0d5856039580d40194000504203aa007a8180c000419900201c0c000d0f51150301c806401420600d03d543c480c600d403e00050000d035541e0405200001c440400c8040386001c06000c4c4029180307a007441070052909107210310028400c0e034814081038120f603403190001c5044500b00b51901c1120ba1003402d1260042a92109141d070184002a40c01c0c100041900498031880780c0b041c4007018882c1201c1800181d20a002c0031680c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 799863893 1250 799862643 799862647
    0xc01050c060f0603012c06060306152713030201181e061e1a060a0f050d0f060f0503010b09010510030c02010e0a030c0b07050c0c0603070513060918020708 68
    0x20301205542d0082e9018100500100704c6100d4906810300b80c82000380d140e40d00301040c645d2105190410046182c0044040e0000d16042ca0a032004414581c0c400c00402c0c030814184850482190031100064000081326500c510a41454508005070903003550b42200503500b4034850116252090b0840810103401034245000e04083e000d050f100c15030110802c41c1c1244c0d44802000d99803d0080c01520b4540e118800000c188030118002410940411070320703072180404100f4103586540c003020401e003c0d40d09041440c0c464040f0707030780d49003d880b240304202400703403420178001002c1343c0303030f03200e88084a00990003084001c2140003800b040300030034040c0f41d4002c5040201d00c81080d109601621008400c0c2c0f0000802d1040c41c1c2c0d0310380c1489030b411000d0300010804000801444504568280c0000b0103080140c07402c01082c400603100d4a40f1802207100b10004000511010701820450300d0000009174240c0d5115143c540c05400d5402034000c42c402c07440542d10500f86001a442260380072a00490918 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 799865143 1250 799863893 799863901
    0x2060c040b0a03090506040b010f0b0f0d0e07080f03071101021c0e13060816050603070f18081510080c06180a0812072010080403091a09030c01050c06 66
    0x80425880202c00404043d0b5403507013100495014007130140035034401c1107511140d504d0803d00c4c400101d0a508551906201000b480b00300081400c122840300b191342501286850712204000e043c60b25a922020380c034085d03080702442d050800300c020300c4150f2140b5003003002900064012a900c1002c0c4241039190f00f0444503925586000342c00d5074a1746180281010841d200621015060b41e409038003518142d0300c0f01e04044506000240600b01804054520500f0b43c0342943c1d000f010030041c00440c400303020306450352030b403905c0f0442401c0003c0c0c80d10000b1036403103142c1148282c58080702284c003520804068000880d89101c089000807014400821450074005014400c10b029040307940c0ca1540080300c018001840003003400b1340100520070401d001d8981c0860704020454501641400343c0c45428030702c200219684912000d0341c54002e0b85054429551685000d90b6581010340007000c040804400c02c070090500c05004110981050f000d88141c100040c0055540c0d018409500c142030700018006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 799866393 1250 799865143 799865159
    0x30a0f060608040611160326040803010311061e07030306170a1103030d0903260c180d0b0907031b0b0a12240501110a030504060c0c05030105070806090702060c04 71
    0x117008181c022112107250084a0b80d00d9030b42d040c4c03148001c40214000c0190300c0c000c80b0310703690b0807110051081c1d070240852515603581551403205010003401035180c000704540d00d4403043c040e11043c107d502e24500d40100030f039052542d40d4005a508800081c00d00d0400300d2210620384c0d04000040d007400c02091046840c1c0d03204514150454a1603405210a0000c0d031216000c40c01040a082c0c02622004c0074010503002e10128400614185900c1c411142d09118604070702d901118042c0789090b10f4500464800300004195010b02c500c064901207600052242800d00440c800044a2180505001216610168044c42c140900c110784035520240100380075180140c014040240c600301c400106850060781d165884605584c070209002c5110105012030b50b00700021005075000c510061109500d1660005c1040c4158025a4104032500e1100b4040051070b0078810040e0500600078010351170314001c01032080070100c03542441905040e0101da2094004161103021342000c110032072a00f804d023688 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 799867643 1250 799866393 799866401
    0x702130204181a10020a02031c1701210624081902090103030f05070c06030b040c03021e2a060a0b01080f04020d02060f030702060411030304060516021c08030a0f0606080406 76
    0x1003001980a905c001400582c4e06011410700e034407142d020003480c0010420300400c0ac5604102840d2040403210052000f1103142c4501e0300300b102406601d0203065101e01e02007020300103291f440000d1b8211003829030808072030b41e14001c007a40c4040c4101d404103100500380804110000d0340180d0017190420050002c01d209a5444420050600f4070a00d8500b559035024030a2119501c444e002960350240d6134007034980380c040c2c01e405008034078066040440c40302004214091600f042070364030100160304512070014500c890f0f0321a008801d441d9203081010101520703100b0458895552515101d0f9848107503008005e0f0394000c00a084c120041a23a0755824881050101303581039070301a0003400410b40d425007900086101c1e00303a035406001c42c2e090514001428004000c0311501c250001e11040c04541d5000c0196031280b411005003200e61004c0c0d0001c101401c2001149500c1201e020030680d00b8410264000c6000726a920820007000d184069100d0454049000752800140e840c400301e0045042900 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 799868893 1250 799867643 799867669
    0x16030b130507081b0f09040819030f020c03091003050f07030203040f021f020c090c091c1403030f010e01051c300809031315050702130204181a 63
    0x704442070aa10303a040186005880e042c00031298440f003020702180d05144120b503800c0d020580e048001410a41e4600d200d500900c0c1a54003110721021100e40514840e4000c07494100b8890030440d6907495103082242c89500c036130745090003001981c2062041600ca8402c0b01d00c01e1220700602d01090b01c0d5500c0442c0a544090b10903144052a64030035000750340d600d02200301d0f07000000c00022004074003080c0607080c600c41c2e80c10140325019000800543c01c2d001002c542d20034808603044140d21585582c905503044d11000b003d03010002104a07444490301c0040294001c400d070403640703007091303a890010f800d24140034040c15400200c545903002088031100082c4042e14400c2009e8a240346a0049940f494010030142041881615000c10102a000402950004c000801452422420040212407a0b203039103c1c110042e15841c0030300100c94810310681d0f640300c0e402002c840d5085011304840c1c001e904140a901704022000314004c800107200c0c030803004e11900d4107103000d449240c0f602c04c01610283c010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 799870143 1250 799868893 799868903
    0x50604060c0f03052703010b040c0f0e01121104181b050904021605070512030c060103110a0801150303110d020c04020306040b1201020d050f0f0f07090e070e0316030b13 74
    0x21010400054003c00d45c00c803950780603040301003105441702c101400d4503804c050a500441c90841d40b0b050565100c56010003224850410148040700038004940c0380440c41d96042c0510726089001441a02c03200082c8111011380c0200343c80320800302410300032962403000022043c0e00b00b240070107415016030040c1104943c010401410007086046148014120302c50840b5070f80c011807800d104a2914a10540741c80a0300000ac0d4102402078084956440040c00090400b440b09103820a0540c2e506108c2c07009010802c0c003c0c082a000c07442203405c441040e002c2140030501c0c000e901040d80070002000060281c0660080501110080a200003940050452500300c3c0e162202038075140c440d980c0b0b01c1e030010022800107035a03030307100f403408801c990014250070500d0140300b05200d080d42040e41c04a070403448900f540c03580d0761a543e0003500c51207201d52011010400c19001c0207051030f0802c0700003c0c9588240d007035500e0280342402d03030040e404d0039000c010440c814880c04901c02c501544582c05180d8410 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 799871393 1250 799870143 799870147
    0x170a020d020d06150908030f03090c060403140c040e061302010e0d050c040b04020c06070e010519051c050601050f0706060803071407080a021f140a030e07050604060c0f0305 76
    0xd0900c0040c0ea120480d180c9800f502da05003085000d00c201c2481600c81898601001d04509002a1b243c9a1003800090709140310f010010403190801403003002280c41c002004590f842e90f0301c2c50b0048150703050890400880c001c9a130310311200e0500c1c5c0920314041038900081c04843c1d5034070107000816400040c0980c100709106000d414151034074140340800c0c030b000b44000d001080c83c000801094401c1c1c000c8075400395005020030104441c00089403a00154603040001c07a02041d100100e4060140d010350f48248861030068034002e80d0050010168402e10150003101c6418118600080c0c82041e42c800d0b0000d03d0800085007403007901030181c04c51503c503080c04509240d803008000d01c0c40d001004183d0b03001445200319404200e0030040500140000c1c0c010b04003403989d40e00055040142150401f4800d40301c0101901d141e88202c5c22201c40309040000c203034a6075039941e0024010601d62102d04898400c801d8041034070700c5d04606a400b200d40507540c510350481d555441100411000508409219003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 799872643 1250 799871393 799871407
    0x1014070813150b210627031207031d1209040f061e0e0f0a0e1507080612011a012f0c04180c05040b0609030f010903110607170a02 57
    0x4034810700092103240070108038440407030100600702440700136188802c0700180c0358840c00300005c0f6400307038030000a542450503140606001c5018925000c103030031590000241440d040d41e01400028042c0819650411450b0b103c1581c40086040c01406003c0950086000000c00d03042040148444a070180021131480e10300744d4801e05440b0250001d1401c1000190300c220703079900c0950440c00030044c0300d000a40a040102401c0c07031444015090f0180d140e00c41c000802c0d03191041281c41501d000c40ccd09076a029140032000113104480a4403802d10032107003101110700e10001402003030302c541102541803a01da4003010042d40c054003840103a80081105207480003818160100380c2c10720a1400c4040c1107114504820041264105580b4200d403a0b0002e4100740441d031446002c0c019140c081d20000307a0b564108001440074040d022001d075240c4200d020100f030b40801900007014a512a86030390380b00c0c4109a00c95516940101d07011000103600305c904a0b03c2d0000861582e40152601c1c0005141c016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 799873893 1250 799872643 799872653
    0x18210c0106141c1109060f0d1b080d05090d1e1505100605160203010b04061404050105010c1203020a03090c08031201080d0f0507020a090612051014070813 68
    0x800398480700b030b00c0702103070142c0c0941c2c2071030501d09001c5081e0b009030314100c411690722529201d40445000c0d01486116000481c03e03184c0c0700d07622012650007410140a10214940040131060700301d148100380c0e10078900001c908800040c001c40da040951140340c1441ca03035805020b510030a061050741c6407175139001b040c1000b8944400652020b40620503001005103602e0700501610170250080800000c542001c0007c140d0010903954080300c00440845040314a00029000d81008180a540b0903e00300f40040c14920640304d9001040c4140e03818003081c1e0380da40054540140c200d601030101e0001d4480030a80a119600074084401242000903101c003103622603096101c4142c10002c015440010101c01c0e520b40710302c1d420300500c510002842c405542e0b080c014442840030102e0700030701c40e0103e500011075075032030044000b44c2903d2204000403659615640601d06200005490b10f0003010300c1d6000d105e42e5809640500c0503030801001031034585d550100c80c6480e004050080314800b40c0140f40c0024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 799875143 1250 799873893 799873901
    0xe120705251a130b13080d1b1211031b0c040e0a030c0c03080313020f03060601140c011b02070513140c0c01140703050106181d10090f0c0818210c01 65
    0x15068000000d01d080200861400c104042d03142d003803224800070301540c2c0f20300801c0c4114140d0b01c500300c0d127a40818154103454006c020800c69491303000c0440e0700c3d0b41844269002c5001111131804954012503081e05110489280c1070302c965107a00300c1111840840d020f5407008050602c80e144c1340841ea90b90380c8a000d038581081ea24500342c00c3c0004200002d500e01240220301040c0d00714003a002d6401d10a0018100303042e038a041c042220350100d50048004000c0d80f00358000740000720740c010b01d00c1e03201c0c40007916a01c1342d001e80351054030004071308013014107a403040030303000921520911626240c0945030b8810b50418800035040c1c0d1f403141c80f0b100500c60002c1c28540190545d45001c1281d50500d01c0140c480300d81e9083d442d24061006004214126004103e46a048070403008100e03140c4800b0452141c00c1c269800c007020003401e0101e40d0800720b405501c158804062540d4040150304c409010080300390040c100c01040d6844000741d600d0340c1c11207203807042101403803141142c50840d0000800e0700799 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 799876393 1250 799875143 799875157
    0x4061b08120105150c0c011409120625050306131b170a09081603030b03060903210c0a110c180609060103140a0e120705251a130b 57
    0x1015098010441d81c1482c0e03021840e0445130707000c0f032401d240500e40a2940c603200c0d500384e1410080840d40503000440990100ca50350344001d800c1e55402d1034a01d0703805598a00584607090300306002003c02901080d4030306c5c0c90021401550307405103540c4410003006a0b0b9a0701c44202d082080d078480e410141d4110009071400710141d69221507042c02c452215000d8080d400a01843c0f855041040c00000640c00c1c01c1110004146602203640d11200c6007400c400404407000e4694061268070140b180800c4008003810480b5032003040b41c0b428201c00b5030300c602d0325070056031540c51500d4144200d013a00b5010f5807013009800100005c881841481500280300c0f080318070041c40300000124140402c1d414400c0389564050020709041c04010110551160704000c0204411b0383c3e543d44e01000b03900300303000748041100120b170400050f8a0300f03da03040c96502c40c05591407540d00c035040907007a00d581d010500da045003102c2602c0794068801d006400f105100d40e2017840e004803286411100403828002200180c420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 799877643 1250 799876393 799876417
    0x6160c0b0a020f030f040c06110703080d0e0105041410090804050607050c03100b13090f08130801050403050901020606010f0929130f060e0a262b080103050304061b08 73
    0x75604080c04e20440c102c5140d0408c40c02c0250000e02c0040300f1f240000e0030000c80340e010341c5842e681c54082446c41c00800d01494107100301c0d400c0405100c00e110340b00e640350b6080d156460541e04a44007004d0720a04940303071280700a042e59414001000395207085400f07411114068426115401d2400c0000781c140404a0164200d8a9640158007010b0070450105c1c0842403607058204202502911350350b4403c1c064040080160000280b491086207134000f01c0001440000000d001c0750515160250554005c03444085c018860781d400240250f11580c41500c07003460f1030300c4280040f03080c440380780311090345144160255481e900c0754030b03c3c1e040800e00401c80030140e4662000c4c2c06080144120303002034198400010041c0d10311030b40d0040e69581800c43c0031201100c42003124001c0031800c5c01c226840460780c0011500a40550341d000390a1012403c03500d1500f5003041c00908130510b410f4803d104280000b070000e034001d003c144170a501604101d00305500c0785030f00502400c480e5441d4002a80b0020b11048 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 799878893 1250 799877643 799877671
    0xa0210110a090603020c0303040618080a17060d0209060427080414030325030306030f1103010534050909180c0f0d0314090301020a08010806160c0b0a020f03 69
    0x940c90b4070110300e10103080180760561800b03100d00b5116a881c0000340c0080c1c80b0642e0340602502c40180085440c0d0030070b9100f80c606880702c9607008c0c05424481480f0b0840f00c83c8026500050f0246803000035031070040e600503c00d4034261a0441408001e00c0030a015132440302c65001d4000300403c1000350001103600c40c404455907142000c2c2ca10701e241c00c0b86030040d40039900511415900301d0000c400b8401004e800c40400d5510422070800320050803140d80050001003400e1032030702c24020340601424540e00c0036402401aa1140c07004510382c042600c014403110303038074000b001c40a00c0030410316200091091a05500f00040c20300040e0400c482561201154900c0c28000d005408081c406044020001c88a014a003400705d00450201e4400f2000103081001868410214042d07210541e40d942c40049c00071516000d8552010740018800c1c0580340d103d02c9100002412104010a41a003800b007903902c50321410100da41d003101d0720300c000d446112110380900c1000220b250400146115010228178a5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 799880143 1250 799878893 799878907
    0x170307110913030c0606090e0c0a0b0a05070b09010209061c0e030a140c0708010c170645070c030f0801080330010b040501090807050d0201050a021011 66
    0x400c4000200344058040d02a090401010092034111002d0080d050b003440c2c2c4c2a0005441d054004100682242407070910b01151000851030015a9284440c2d0a03141e1003000d9455100c524898060301301200700150040040c0c000140704050b080c4e4014400304005070900c040200001c80940203120b510074a0111500808a045000d0243c00200340c003480103546806000312008190510002002026800c00030b401400c54004200103c004c20b0750b88001c2021100845000b40191002809082000c06000104036540751840e0380c0321005600030742507051100111024240c84a4124072080a2640c860a100114041050301d034403078a1180d84190000d58189006844141e116a42c1c00070001101d0040c4040708000040351140400104481003000d1039221860f0b805101d030f9044540b01c0010000007621504100c0904140c030000d0302ca01d65800d440d10800d603035035001c40c85100c0d4001c954941a00265001d031000302244001c80c4143c2e51812310609211080c0c60300000b541055100000c2e4030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 799881393 1250 799880143 799880153
    0x90203030409020304150e031207110a050d02010c050405182d010e09010207230a020a0f1703280c1227030c030b09031c06030c0b0412031404170307 65
    0x8074806c0003a000c204240e06c05126031607501c1c09088603810031166080d01080c2000d0088032040d07040300044084880407240740ca440d9888001419000015600709601d0380192402031051b2001d6603006030425020345080440c0e003c8a910280619403803654882c40081c0310800c5014008580382c81a080c140c065150881403851040006c1c5030741c04d1b5910601c1000009640c0c50480d0348101100e0480c20102d40c5650f440078100328560340000d501035012100054400c55041e03440040300d04241c502041400b0b82d4031015180e204021141080e030030000c851160113060540202020049480d10000d81c004030350f00c00c01004022100344011a071a4004080000f04400303d606001001223460581d503071850351444650381136800000c1001842034000303041d100e420000c0e40c1c510300c80c280d8080841042c40c0440c2c001007504d4082500d144694800200b031502c0d4603000c0f101120258000152130341140d450860789018140070305241502d040100142c80014080c24102d411070200181d543d52b2468508 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 799882643 1250 799881393 799881413
    0x50a0e0d0914010306050132070606090509071206200406081506160311030d140411180c0d0605150a120509031e27120f03041701090203030409020304 66
    0x80c0303d042605014051100b41d0b484585515a08a0304882c1c180d1040d03000c9006000c10030b0340304035900d0114085243e0090240c143c01c00c0d012560707a10f0b820851900c5035a00e00d0380b03845440c014520316041c90100c01000810070b40c4034401018112401c1081c21058082c2c140d2036074099440000020b031100c050140000400340700305a224800c81d41646049142e8a000d003030142d0328080681031100c007400104540e5001c0c41181c160b0490904100240c1e00160300d0001c5040d4141d80540e001220307a02078081034103089061300c2003600d66484c2ea80f941d9444d092803d00310b902419150310038540300c150005450f210515150f12408180a4843d22a104a035000704548540e00d41160464145018000206404411100390301c0134201c81e41030012280030640c2541c82030303105044a0404221461142105010190301120340c103c4400110010048000f5640d000e44c514aa49981041004201040303002b00b142d90182d4040c0300100d20a462900001e043d50015403060046030f4000041004002486803 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 799883893 1250 799882643 799882679
    0xc1924060303020d110a0807320c040b0d0b0a1a0f1804020114070302011b0503060a05060d0f0e210307080109150b07030f030c030915050a0e0d09 64
    0x40800c003641c5580c50084da100390b00c8443c0380c01c0c003d2407041d4505150080c03061406141c0c012240d075640e04050b1401100ba542c0c0c0502050074201c9503403045125010408115450443c0c0b1002402001c11034810400142031003501e07140c0c0801c044c01c0b444c00190a414405114801c44440003407403100d0903020072000b0020302d5500f1b01c103040b030b120b201c4003a40c0c1d080c012240d54244115410310664961006880400101e14207025064001c128942015415040200541080c445081408004220655490109031030f41540300a2000f014481c508100003d403c0510b1006070101e8071072440c4240004444000c6100d502c00e8009441c6603074101c04007642c00d0b2444025545441c0b40d031410350b80c014280c40e07041c000d5070600c0345c41c0d041c0b290328003958151a1029040d004010781d80c80c40140340c0602001000c11204022030b05061280c1483e9000384614100150003648420031070707840d402c081004000c0144124001607a0380e4004076006401c115460301a5003e468601c3d81c0350030f000080d460084c54007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 799885143 1250 799883893 799883963
    0x12150509030708040e310302120c100b030c1c020a060915030c300e0303060f0904140d02060a061e0311030f100605040f050702030702060c19 62
    0x12000040c0e160300894080300c0b00c401d42030035652038142500001c80180c902400c100ba5110314900d807040806e084a941c528402c0e0201c1d01c402100c0e02000c5664061a0048040398006607078003107004085403c40a2810701c0103040d5036811400b000000c942c0d010100c0d00c071403100102954481141407024800300684040d040450aa82ca03128282102072080d1106a04140e1900710840c8504e004440c1071500c50313480700250105001c440101c0c1024000506030400791800c200050f00054004401c9901801c0043d04d5040c00501110a01200c1c02c2c02420407202c1049400000c0f109010a21211000241c41c3e4003800d25401c041014400b034503141c1e0000022107c09035008200820b002c0700007030071030742c0c002d00a60b0518030050002c3c1c1000103644041b002401a03580d5100e800c0b40300c2c0c0c0720405940007210b040040207034080f1040210395040302e5003400b40e40100b21020151a20703001a015821040b070440710740f40003407a0584079910419800700c0d4100f03207c07030507200800301128450524051503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 799886393 1250 799885143 799885147
    0x191401090b0c06011a0d020f03090c04090b07031503050102070515090d0e0d0201051902010c02100504050a0308041e030e0a060806030606090a020f13050103060602161e1215050903 79
    0x14070a42520f441d018401c80444100b01101c0c0c002e00c9000e641a80c04036030441e0000c40d10751400c030184410342c0d0f004480040b0180030700318501071103141c00d03c10300c04c1690b007040c2110030990703c1c1d00c4190002c0041b045102a01c006608000000171000d00040504130b2240c07000d0b0140d5540c1103c64010100040c21410036600017440030341090307611122000c5541c40403205c1101e40a524001038900c1d10400c07080b2611140b90641e0203011a4054118602c225440d908030368500120740801401c4a000b91001820390b04a9084c034030209110305c29090301300f405020b80c0c07083c2d800c9070641c1c000b14030a03902003240070036441c25500c0f0003072801d0010b4034002c14203810440601c0c600000043c0d1a4400240014482c084000c081902184140d06035a240c010707140499640d0340199820800c420941e200710740c00242040d002003585840032807050040600c56075540012428003041c60742c0e00c14030300402408400081c41c00a81142c1d000c001c09403080c01107602d40e4038228101070a4058a800030041c190903401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 799887643 1250 799886393 799886407
    0x2090f0a080a03120b04090302010e060604090305030a0e190606030b16050d09081306021606090b030411010c0611030604060b0405061209010921120c1409191401090b 73
    0x400c0040d220383e8185003031011603110000010080c465410703540e4000345444c0318030042580552100c0c0d1000c146c07104551955a40004000648104020042c006842840440c1a030300d8243c00c100a00603101003901e086000b10403034654810080300054400e15107406080050081c2c0c0390b4529001305800d004010b490800310702c0500b06200d00c2282521103a1340e400c500081c0020842030340c410444503480c0803a5103644100080d80c450b0b9900d161420004004400510301d8006c000460440d9203205840382981c1c4c0f203403a89040c6400c000e48003818400310703000c070f01d0001d0038501c0380000071001039884580302e090003014001155059000b548004000f000140300d540da0702c0c3c094a40c001d00300d00c100e01e203070384d22940d40a02400e40034000170100c005510f80a940200302304035114145015581c0d00c4000444d5404010503260641214004180d018520b04c0c0652034410003800758000113804d0f462800c200003000c103006c05281d480025129400841034000e981d001a0b403070b00904008510ba410002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 799888893 1250 799887643 799887659
    0x14010503010b0d14070f080c0304030c0b070c051009060b0a060203221203030b091311091f060f090e0103081605190c0302040c020d0c0b06061c02090f0a 67
    0x30060007200307015003021a114003a4480c94200b90b07108652070122a0740c5007010803010b0050b80c25200c07200007288001d800511001940420b880c803440c0c2581d9030411540480e06c5061014001401000400080d030100c2c4011580c20809114a04c0da07100c000a10b1002c141000c00c121803000c14070302e00c00c0094200801401c0e600000703540c41000100d4010f9955240040c20002142003503001c00507034502032041205154140c0e010403c0305500741c510b95000d03522190301103c12444048000d00c00954401090b041b42448841184e000004950b040744103103440c3c025402074407143d030082d0006914204203105c00c1c1c2d44001c02c24001e150710141c10340c01c0c4d41175507108402d601480c0c0c0e2a40300b0590400200c002c3c13040c20006280128490129004241d840e070800d191300058600041e40030780d0400302e0107222a80300007200c5140300500c1d941c20041d58090b903210101d405003e0041640304400707001807464500100740c459215182c0c0c06e001030703a4102100611405414001032030348078241c0300380104079141c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 799890143 1250 799888893 799888897
    0x2090a020307092d030f1109070816030621120e03190602120f0a0606080c0a030c200a11010201090507060e211506030c2b050d051201140105 62
    0x5032241c004004c400b21320f07041458802045801001c00800003480041840007981d40c50700e0f200e0141c0301d031501c0c2e0030101080c403020301001d47d00e020000300e040000600120114400b41030001c2c661802040c1d80c1c0ea00c400d4040040f42460542140108450425040154000b091800c0c441c4908046e40524041c10001752181c00074034201184500310907403642004500c0c1c0c1220010400c402c410301c4a4202041c808600040445180b040a442c00318080341d80d90040007014403d1404415141ca06441d031181100600302c841c0500c2c06100c8007180e07132031034007142d03908108402d01c00c0402860341070701a003019104032000c200d0003410740e45003003406008900d01081d044251881418019550a01c240200e20340b41032440c0c0420845030034808208030b00a02068103e191500c184e051401d5484010400d6120809104101d6010021803113043c21010b03020f80c070719040e102061800380c10744540d480c0c6c141000c240c14080d030002200040d9010075002c13075003a058050140508802c4030750289100181942c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 799891393 1250 799890143 799890149
    0x92a0f03080c0f0d051905041202010c0606030204050c091f052b0c03022812180b040f05240f0c070510050a0f02090d02120f071202090a02030709 64
    0x122900044010702d502c010000800f4000d0150100d500611200038010810707084017580039884400304003601c0d000c038802d00640c1c0944031164400e01110341d85a0054800c03411205003101c085071200800401740c1d0f114840c00f44100008607030b03a69256619010040f6210171000b1140902001d141906800e0b9444004d941401c50065242e000704d040e60110344c03008031071600e460442c041c1052010f24499505401800f69508140086030000c10810306c8070306d640845420483c0040d08a07040c10440540340c3c0c01281003485c1107114101c1007101501d51400b0300800700c40c281c0303003000c258010008004040042071103216070102c0894015140241c1c101c030003400038080446000b04000402d0030507010704d0440e06207650007000c8401c81d0b8001c445080280904460710b48001e0300c2c0c0380026140c16460f0084490075000204824030a11050707080010003040c100c0d06100714454680c00300301801d4100030090203000c0700b40030f622008206104005040c0d00080403007000a00500900003a20380080076181030b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 799892643 1250 799891393 799891403
    0x309070e071709030a110c150a090315050103140a050307030315180c020106090c140a0201020f0c0c042702010c03020c0a060905040501080703021f09030204092a0f03 73
    0x3580c9a441c1d044502d02e0315100310403003556240081c8080c40100200801049000340c0315403865252030754103a612100c10862160304005440f00c2c0003400706182000741000826414404904d40d1280c40d0714400b203101504103a10349070380d1300050041c40925446188503e802100074034000c40103540c3c0c02c0c0c480c02a19001000e1545607440314032071030114000c90b0003504550310300004004038407891101424522003140059481d00101260107045030064245640c010f0302c81842c0101c0075140701b80c082e0300902c072280c2155800d0004c102080d503408000d0024260301001131001d2080e41040000b169849513014407204a5002c641e007040b2180500304085039024200384550000c03605080c1d0401a0020200d68004058034000c599160051040c1043d00c800f910704015981c1c941c100d0641c0c4060318040a036100780c070380050300c22102d0400b03074040b6903030745074034080580d541e8a50102e41030706c0400307000b1076900d0681b40000012201d00051031500403062040c00009d1464495501e52400c014000504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 799893893 1250 799892643 799892669
    0x80a0e030c12010504060c02060702191b06020a0c080106030b06370e0c0901080f0a0207020a0308070b06041505010c050a0b0108060412050a02060121020907051806030907 75
    0x1045503030034803428048000c060301c1e0b02c0355400c041800d80d00820781250111030443c98201e446d12442e200080c1d491080313490b900200080c280c01c87c03503159600c014101c00c0301c5901c1122440301c071540c8800f50f400010302d8103400400342c80300039150981220610340c00c6a01da50b07242c54402c1000c184101c45441c2c01440554100c62881548085580c001003050441750742107880305481c17161061030303900c09412a021103203022040c0d202c0405004481c45030a0000c7c1c001902c620119171200d000c8405560441c001181c010701e00780e038640c0840d1040c10540e105031540c00000c200325003030207188805070358004402c0313804110f0100f044000c03036030082c01401003d0410214251f100b04011040200430b0905411130850602d03036070742d6481681c0d070b0041203604844944600e81c031100094020000d032880d01d58550043c000503070910404a9030012649040c2e01d51403841c4030520056104c1c020214042d4070140c0c1c0700703940d800c0e070008101d07000720f03031041c120b80210002c01c20880340700004a910815100c09020600b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 799895143 1250 799893893 799893917
    0xb12090615010311070f0b15120c01030203091e10050601030e0d03050912030f07030605010c0302060a0c091212020601050f13051b03071e0c1e1401060902041e03080a 73
    0x80300d0b0045c500c3c010b000111120b400c40c1070100c04001d85110340010070700760308225050001d22458441c0c0d03569070345440c6c1c441403811400750f0103a006554000c010008452101036001c004420b10814900d503414190048441c4800310002800380300da12003000e003030501104000c1c03004980e941c1411460038082650300d10105840300020302003800004017491082c0c0d100c0c01c00c414820903510080d075030300010a2603c000000c0720f50040d402a40450f405070041d120b180e60343c0c0301c944090180c0714030041c20020003400102d0382c0301c2c0c810320b072207500b5000b180d2101c264091043c000c1d26011040c1c003c684105040e00c0e12034260b07074a40c501118440c03002c50010640361503944640803c06552070301060741c820041304116280398041c0741c02002d40803841e070742070011103601e03001d40e020b8950302c0002e440d03c1c5400500326189001c002c03c650700a442161001282260200c0c56821907004d904007401c040e03000501001542d40c9410305c14501c144d0f041c0017946040c59903030740512610480d0403071010b00c84012152 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 799896393 1250 799895143 799895171
    0x21002070b13140108010321050d0c11070602070b071707020a1203080c03040c0e130507120c1a0a0810211e05072601060b120906150103 60
    0x90006112032601a900c03000e40c51407003a000b0384980107580c0d0752640c05070159243d61040e07041c10304803604000c807a4909890240e1014501190003699001c3c44010403041b00c502d0700e140b00f07200b042401e075510010841d40310040d139030070001c03168050000c550012000b405042203500480d00083d600600d014001c810081d05c011f51809092800703035120440311000a442c00701c511819071b416109944807a50341e9680100104c650005030703009860f21100036401d101507490300ba01c0725008103400c1c29040d00c43c0c4065540510340030b4103809c100050f01d40d18494200b00700c00520084090f1000900c1020100d592114040d2180210f01010003048007050200f5036825525004002a00100010a60044081e8514240c161202400f02c1c3da02c1850110040d00c031005522280f0202da204000e091042e242ca03240100a212460305207140401c1b00c5050340b07403010240b00d04802003840c3c48807a5100e1105d0083d040300301c10700401c000981e40203001080b0807802075104520300b8480c2402d000520b4810881b80b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 799897643 1250 799896393 799896403
    0x70e06190e060f03011d01120210200309040608030c03030f180a0b10150905060a09050402070b0106080c071a0408070b0a270c17032104030306050109050d021002 71
    0x45190441c1002450f6040d480722034008605031203049a00450341a4200754002c002c02e400d03c1051100c00340054a40014039007913160390080852482c2215000e60003000d03c05800f60009000c145035400003540301901c0c00d09020301801001c00070091400d18500d0042c141e220710004040e032018006060006401c0400341c0700000c091008007044408980062925104144bc140c911300704d400e0a19000183c4070f1086881e00d59180d11301d40d00c4481c0e0764500424485942c0007021881c0c14841950408609070300e40d4800303054982e00400d00f14543e5450281d015040180182030100848010801400071441152064032a0511650008040d94642c14101c0550160010060200b2044024410480c9154109481042d0b8190102d075104d4284940782d0312000c2ea101c1c0080c103041200c5402c01101030084522914410700a040d42d10b090301954030340f059170745100c5019550350b81410a12060541c1882080050030080c241020940d0820000401d40c40e8580c3c0000e20036024030340981089442401 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 799898893 1250 799897643 799897667
    0x61704020315100501030506090c0a21091113050103050319210515090727030b040c1404020f0414130507020a150b0109120c051003050f070e0619 64
    0x14200c051400d00b0f11a50803840e00c0b51007154000780c01c100105026281a20704075000301d02c0d008600d460300c085da2100781c0f855118100140100d40080081801d00406030045c0070300d0754480c20301c010341c0e4290705040040c01c0c1d8613001c00d4800c0529000042c00010400011500b0b640c1544a650303028002e0b03510210380d1440c0c0d0b05540d051002c02d4a140345e420842641040d03016500c27111007483d00310003500c02c1c800408011a0448002075000c0807030040c2404042c02d0701060410501c0340b000381d54580c0c5513108401800e4600700c40e000f007400350800414505c2e0000c01e044400848040d484c01004c1112452280964000c080c00010b05009040c015034484540e0704808013040c2c014030403450007000c041e4540d980c6110982d61100c2100c540b0405000c0c0348114000e0f4481619203602c03850030324030542c420b803407400400c0340c88883d00040411142c0d0394204600b8140c010b954003048a01c0c0051825103480c1000e40114140200c40810704000e50303038002501c881903888944040c0d45802c000b811105125056 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799900143 1250 799898893 799898923
    0x14030402100c050c0a1d07080925050d0c15020a0b01140409020a0b09030d0302041214150a09060c05031003110a030204020d150509040302211c1b090617040203 70
    0x15000007030011b41007407009500000000030282c56502c0c010207072106081140c48004d0f40c1c000b880c02c10644401070f001c264a552240c480c900155807200d000c80d8001c45070314400d5540420115042112070380103050421441814406040740301001d80e691629624103008501c000f001412218a440d203d41d0301840355140c0081805c48140c0d0b40c2d15502203583d100c4600d160003070107014051602e0b14042d0080301c04a4040c0030743e1500b122036540703030f821104007180088031850054008020301d40f454401b03c5401a2800900051480e505140c01c800320b0310f09480c1031013400030900170000070b400d19000c03d400300c81c1c00c020282c4048036180001a50405d00f07401c002d40c02403010581c80d103030013850343c44071815400c0034581200b00f5803039004100c86100201d800400603802852455a9258040c104100f50490794441e07604050000c42d840038201219080c5654603550355950400700c000142c0e038816180e04a040120500341409802400c0318840000001c0c0a016100030508544007004460a190590 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799901393 1250 799900143 799900159
    0x140a03020d09020414041506050a050d020102031201172b08040c120605191107080d06030b070c0510020421110409080d0c0504061704230a0314030402100c050c 70
    0x3171110002c0120b01038400703403514801c034004144540c204d4441d60080e580014a003000d198509420824007001c241c000300d0460005000e031003042d100050302c25019202d4100aa01e880d080041c22a00d0110440002c0c0348100550034249510800b84d82e41d858805032520f4054065034442c02d0424554000d44e102845690101c401d0809020850340840c1c0a28640150740c0c0d6103004840a101c280c401901d0080602001008040300081420006122000843c900440c0c22a0b90361210495964102d03a004081002c1000b0201080018810300403680700c0d00c0e07401c50909017800071282c1c0600014083d0201210085400020f00c6140e00110501c01401042848106090705d081480c6401c0040390606040c24400c01100143c050021b0320166140303940c90b441e180880200b03000500c5030190007034480888200e00c0c149402200d0040e071210340800b00003088203150700d00e00200100752580344840610000d006000040c0d03500700c612803c4442a00d885003184000d82801401c0505030800264170802c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799902643 1250 799901393 799901411
    0x20f09040506121c031a0a0509040f050a060501060e19050105071b06030204060f020a03171f14270c0c10061211010302180411040b0c0106080d140a03020d090204 71
    0x504003820100105560140110a42105c0c0710764201542c1402039480307c22800306121034108424030a80c02030041010300380d40c01d413580798241800c40c010003c1c2c801075150310042c0f0130560002702c52001d10340d0030349148102c0c03840056200d10703034010742c02242c0c10000000b502d202402032000191031140344103100091766555604c0c001c3c00035880b038030802001c04d100039258240c403400403502088064240d100c0c8000400c240c2450410303c20300410205070360824001c0341018996007409140a46003941000c21212030742c804003c6c0b019619103c48070600031041d50601004103180e09a5006035440d54003680741c12940022a00b0b011040c04d09481321480c0c91000916481c0342c590030115240910102c10008407403100441c1a8030514034254a43d00040b2041001c0b030800e50312940b1655108100ca07414561520803031005948400b5041109070346441e024041607406000c5040b01078043d00b40451144a4201c91041900400c04440c051680c0800c800d1480c0c085908000c240e10b038010300401a0b094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799903893 1250 799902643 799902673
    0xb12010603021207060207180f0c031a06130302130612050d080705250804090f0f0b1c0803090c0a120507090b0a1215150e0703020f0904050612 63
    0x480344016841081c41d240300543c46400894010709855855015110315410010b00141c00180098401c24240e078440042400c0c030f0700c0c0d100c0c4644809859401081c0891302d107804e519007666514156108081c04c20201c51000e1450080350304803641510000000f00c0d0000e001c000405041e0f100e240039019051f20b8008011000c2858200000c2c0d40d02c0ea0402c50301c684204807403501844040108021300c1140461405240134000b4100901c62440d0500e070540300c01404056410140150b40f041d91200d50400340036002d4080c1c0b0444038401d4846520240000501c01c1c0c08074003480c4044c000010010104900301400e005a200001c0702400d01c402d1b156488450400510705c41e03006588600503083d0104031041c2500803003001590041c4041455800c05c500751082a42c00d0504036038440030030b078242003a040c1a0062040840b102d05007103000030b00c0c008075801010001401042054410000f03041e4600310981a0b07103503888103031400512940d42001046c400714541c4000b42e0240705200b100d9079099 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799905143 1250 799903893 799903901
    0x706020f0f010501030b040f050a3e01050301030201052127060105010206071d0a0b0901270e0403030e1209010f02060c222d1403060406020d0b1201 65
    0x200c03810484034200000c004240c00c03100280170081207607030181d01140c040740880109400b213500927800e4500b1070038641c0d0b1350070b0407000080d0300031128015049900e5041100b61074030221011205918a01014118002410391205020013814010f010030340ea034900d09400803241c00e2030803898030a5110309000c04203041004034102e00700310303918540c101b10002400115003c0c2c121201030b0024001610b91100030741c0e040410f07886096420400c80509a40e564410100f0401031005000443c1e40d180c200780010050540f00d06404800c101c03641241560184040d004c000b00e9298811400007915249801c03409022004031306810351240c414004420380a50001704940c01e13098845c6500d10143e82c1059071503400448803c1076840b0240500da6280307400811a562404104d4480b45c0c4040d210190040e828240c54014102a5a18840c40b40034190400555019084480081e0b81b14105040001c1c1e0f210740080c40181243d8000c00c000b000034a13190030001080b10003c0c0303030810400c02c01040714028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799906393 1250 799905143 799905163
    0x40503031303090f0b03061f0e0108091006030c05030f0601080607030c0e060307030b030106051005030a020a230d110c100903092c0f06090703150902030a0b0f10050d0b060408070602 80
    0x241852803070650160b89401c982288d02802519640607000b41400155071019000f441045280910348081704920058030404bc0070350f11808044c8c000328200000d052500c1600f411001403580100010300543c40b0010340070b41d00c0045031801241608458504684c0c481c14240d510360400004000e20024a4061304030340c80c8000300760000c003c0f2030364540c04c00241c01102840440032901c00c00c081003000032150001e10200c4080d04107641c43d0707040186a9101c4d0800786884095403e8089142500c2e2000790084a240000e2200c03090300703240f0f503100400d031200d03042d64481442c2682c03008020b00305402805050001c2200760603842d405488008030149450a28083c034516800c020001050540040c050030700840c4080c0140e40076555400c416001081d000c2c14140320b06025690005c1c02c4a681d00055214410b0030780c1c04a40340c1c04050500007400b200c0c047d400e00c5008080c414000840d884000d495251440b02d5001c68130411081c04901184107503007001d5a18000c0d030300302240581d00003c424140d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799907643 1250 799906393 799906399
    0x10207140606121b01050f040e0103150513030e0d060e060702030c2505190e0c0408240a150909060c0909020f0315030114040506011805040503031303090f0b0306 71
    0xe843d143c42c02da81c0d1180c05400019260002402241595510803400740c40c2100f448035040c1e140070785680707010034044001d91044801204504840610580360b0007a160014400c40100342a02d10136038024040804020700309015a904000b03490070b0007072940146100c098207400342c0c0e0503030820300f100030b450b0b41c8882549480f0b84101100490320900e0460b0000d036001158a400c4940c07400d040420900301c0d000103542000c0c400c0381e0300105040441c031541c10702600c01c541115580b240b4001701c56017010382090030220451a190110241d240c40c1810860384070840c03c0c800242240b0b1400482c0c140744507900020101031a03c1d008404110301a0301406200405450381d55134a651251890268030601101c0640704005001182081080c01c4060400d040001d00100e40380d0325400580351003804c1100c080d20194031010041003480018000c112031f00030612800d00807860306881d41e640d2072002600125074003c0390455a0149845041184d0181240c40320130858207540710b44004050300700352907040c4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799908893 1250 799907643 799907659
    0x1734020a0308131403101808030c04030b0a140402090912030103060204030b1f030b0c1216031a0d1209080304060e0112090203060f0c09120106080c01030917030405010207140606 78
    0x131611801031309440300210050041c0f4000d000d02081c03c000e05114124241420403018030a000201600c014500c100c0b0809a01c1d0707100d5166003056032410314068482c1e0704103842c050321003401c2a072035082c1c0ca90003601503803852169140c0c0d60001e440c3c0000d90400038031a400202c004410003410350010000c0320b001700d0326190a9240c210541c1c443c00c24402105420010f19601007000410080b0401c0d40840400d8849040c0403100c2d12150352403c0441e2140003464190b140000260340610a2071546c80c4201002d4240b240e1010104116407590070000d00340000022490442c54442c0c007608001c1d1228030181c03038072260f0754000a02030542c000c81050114582b5241d405d5950301d0362052a1409800074010b086644506182d5410900050a040f81941c1c1c1044511882c0d1194413444804a051100004011313192110300d40c1000200d0789103d04250074041a100410758041d072036419850045d1040c2c2e90380d101d40c50402d00910034940000c0c0841c00c007a02070400e80340041404c2d032040c042a11300310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799910143 1250 799908893 799908899
    0xd03080907061806081905180f0105060d020d0203011d07030c05030c0a0b1c06180609060506043b160306080d0c02180c071734020a030813 61
    0x103214143e040c1d04102901c8000701c01005014840c40788207030455444121400d17662940f10806096a01c1104c40d0070140400ca00400346002042142400344500b4000070402800c141340042c04220a104000e441003002c05c0700c1000b55a402c0d80303c4100400b40482e1130300051141059039803244e446100644100f484044005480e040229610200c0340700240003035440ca081108100b0240c004541f03000468030404103110138820548038510142000c2400c40769030380910a100b500740c424a4000c201a1410540104250f440700015a030540b4013540d46141221014010301700c0c103d0f00c2280c0c190700d0700d2041460445038500c0800940c01200c9020030004000c401c000141c013900c52602c1452200d134000081e03c445540b01e070482e9801c15100070030620320701c0c402080909910109684e0a026050002103140400514200c0c82640c0c0000130312a5080229280c03140b640c0600c141e0700c540c0e4480392618151a00e408640f0003010b015802854501f8903502c3c0d05104020780c0140030b15a08070861001d003c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799911393 1250 799910143 799910147
    0x115020303190203040302162603091003020702060d0f0b010f030b0307050f03070e09300a0c061404050604020306221209170f0d0f08040b150d0308090706 68
    0x203034440c1e00301c004071400b200505410b000003503200800941c1140a481e080c0f00d44900145503500050060740040c403070300c265001d405515040314520500c4545e0040045c51800d84410700d1500070019142401a1241010300100f440c0788600018403508c00c1c6400726075032900c0380d550700004040d002a0b0341c0a50000c21302c1c209800b02c2d10768503900c0c0d5050b8030440007085035181136100d501c8910000740581c0c0c1070320b55a4040031104c072800d40f0006501d0300402c2c1464103100c0080b14803e0350040c0810b0028203908008420610b0384a050341c810100110300c40f403807080c001c1540101c0440c80e240705440403140341504081d03840b00320a8404910034090340c00812040d118182a644080c084800103a02c0c840350350b40c4042016002c40400c0e401e12100e954005454100c004801d40b05041141c0a00b41440201040380d0402c0c0c0c5110000d01440446000b40c11582c1d03011959540c007661186150060792107522030701c80700081640700a64000286181c2c1000c140d4440703200b41c05420783e07904880c0c60030303225502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799912643 1250 799911393 799911397
    0x20a080f040b0a050603010b040e03070209070203040609090e030f0f0304020907030b130203190204170709060617060118080c0405090105010b03160c020d030503042f040b0109090204090501150203 86
    0x702911030341a0300e000ca107141402e680101d400c580e0040000031152104c02c007060540700c1100503015160004900003013941070600807641d0005942c401b4600d402c1c14140090b1010303480f8011021a20707503a510451640104008031203d10382c0e110101501c03841c00201c03441140e40200d8040f401051440040380e00d0710300a01480700c402c5402044221900441c284500094200400d000c0c4029600c0d008800a05050702c0240007a01c0d802c004850000c0704c1d0640c581c54440b0355403021424a103070900030070115500c01c003100040d0135129440622a141e081c0103d840908502e411494179411490004404100080310a000002030307900307010700d503184540c280c2210424814505c01c8c41c42040080d0b000760030016848040505030610701e000c0d6005401140003d120200704401051f400000d01c401c0c400c1c4003090041d110003030441000880c11410040f02450404044980101d031100c4982a05a000d400c41c50041c043c550710440d00c0e65524000c0e54007a040c28481c8800e500c4420b041a0706203480402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799913893 1250 799912643 799912651
    0x8031603020115060906111509010b0307080d0804020f12061f2c0402011107080726120f120c030a0e06040c03080d0b18100f03150e0313030303020a080f 67
    0x5460117400d01c5d02400303480c09617a0f03500c0300003a8056100c81d00c107441c0f440c600060290716080f00000d252594002410701d00300e016001202e69600c81501800d071140d001c0b06060380300d42c0c190350300d806a00506003c80c800524060310800f03a80141c40030007902c4200b0251084456040c1c0045a821541e11000d1590f1401072a1100c03941c1d0803504445030000f40440c01080d0440d106150000100070318442050030088540c000d032110f5080403604100322400d401048889080c254906113200c4070795588141d1303d51080d00440e41030000480c901c440403580c2d90607500c550012512030412868002901c0c44290700854038014030713615008104081c000006655403099501007440c60b000c2d07003191a407407120f0f048140820095070311240e10b50403070780300c4121424044404044071301c082d050140c0303103145d2b51303100d43c02c280004e0304a5281003000ca45030078903952540510f0000055024000398409080d403040f0206808004160b580000030560325030300030220100c01e030b42c4040298075580501c0859001c2aa = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799915143 1250 799913893 799913897
    0xa12050408030d021803030a091a0f371718060c3004170c0a0f0606050a08102a36090608031204080705070803160302011506 55
    0x21110302100c0243c1d5000700800741d00190b0030782001300701c03a00007880c3d50320141e62403001500c14001085101441c0c01d0054803013110208441c1440ca040c080304641d4052200b0700300407140d01c0a8407403202e942d08400380312601c0d40e48074500c03c07150340c2d004050b0209540c0d42c01c442264588800144000415150048612111801400d80794070340340800c0e000d0750440c11181c251000e8003405900030030541624511958040f52006040b40b82c20b0424203070750301c02e60001120384402045003000d00c81011401010303080d031200800da17041c101c42c04c0444c010201c0360002c0d80c0207209441c0200d41103030006100801030b14000d00c184002440f59281c01d41034808243d081c600b80f00341a0741000503900600f041d400c0404000c410420346a0704207515210940700d0340d00302070364010300001880280494007400c1c0281000000031858000c00d0040000c507000028405019500702003544020440180918402003c7d12030450391103010101880c0d100b19129001200550320700034440300711340305001c42542207503c01c2d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799916393 1250 799915143 799915147
    0x1109011218140309130606110f0c0d060207150b19151101020d0c180e090303040201180e0108062202100f03020f21070c112205090a1205040803 63
    0x19035605072082d914081040e480e00040c881038460351241d621006484c1140d220205180c0d161200181c003110620b03900040e244c1100000d01c0184600180c101441031081c1e60701c103107206040c1450790007070041d01001000500c035803905100c40321894102042803070003200d1892102d10441108252817149110381e1750040521031002c0f40c4240106090540103040358005442c080a85210200b1034002d94090008103005082e43e040050000342248058400020284410305002c0100c81d80c3e0300009000030704001c80524005514803004440078002d20b0144400046941c560030810385034103045a50460140c5410200e00300c0740300300200304409940280c8104822074190201700d0307192a4032030f40071080c035800700b00c582e514401d40c10003444040030034100a0b15141622001d80781d510030183c81d25081001c505040b00120b0700b030907a00408544101c5907003441c10315100307036400319a80d042080e409144c58001000480c03040814540f1a41d4491161450740700b0350003600303880701d020341d0040300c00d25401 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799917643 1250 799916393 799916441
    0x307171f0e0c2202031302060a090312030608060112030201110c0a03081e130206160f02192303100f0509121827040503072612130611090112 62
    0x25a42c000d540221b0020100103032001550040b42d010b5107c200000001902c4050030003e02200000c045502c400a01d014001355140110f0380f556840d040c0202c00d103514446082804040c000d504c1a00b4000710000d01540300c483d0030080d262598405e5200341c000c290741d00001003c0f09510190401003000e10a01c00340c10b611030215840761074804034012030300b280c010030540d544001201d0764505894801c6500694610107403043c4016061089226003108102c2c03c0c3c117000124009159420a4030350003040314621001c4400645490030103205045a80c0c40c0c5803151072001207940040748140c4940040710402042c03035442030180c2c0318000c07420705400d00c0800e0355005458031240c0880a04801100120141c010030010f0600200c1558100c8880c0e00001d410000c002000e03007158051204521040c03403041c031904032100d052103815a80304003185054005241100b5000740c07002c070641c1101d402c1000150f615104100740e4400c11010340804c103c4d0341c00160011550180b00c00ca0510f4490650100710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799918893 1250 799917643 799917709
    0x1d09090f160608130204060801050c070303140f161205180f060408030109181a060109060903030f081905010b041e0b18120d080714090307171f0e0c 65
    0x1c184c2c2e0101d91054495000103500c00f001d00805018281c02c01e0007990369185854058202e0312141d120340002c540100800c50f5810380b5000403540004210040020711741e03502d9041b0340b84e130500120b02120074038150500180c0a0b030050303000002904581215480d15488048942d601c0d01160000c140200801c0103201034426a00301d0307004a4210b410a0303c881d1710341e54030400c80c00e5204070175501e0716045004024480d0b9000202e907005160500740001468159140180100a444140400d03c25040d01046400564012601d20303901c00000030406941c4030510040154131a10400000c440c40750f1200c520321040200c00380807501c2245a25240c00e014500190b11992001440f5601c030107050b81102c02c1180c2446400345014055480f58003610340840d0243c0790040c0300c140c40004101c103105400003600e001600c9420380300341910b0b9030241d09000070301c5464003803003080b1160201900c80c40341014035100d41100c1000d5002200352480e440c1c850050111503140c03004580821030754040c1880e9080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799920143 1250 799918893 799918921
    0xf030319050c16140a1203140f0d1503020310020a0207050d02060702060708120c090d060f0612030c120806030304030b0712050f1b0a0504061d09090f160608 69
    0x1401005680184020480064002007164032010004c00c0c5100640024502003200d5006450f00300b030407030f540d240c2c6038078010009000c4c03080300e940454000407040318691210702a2103011660803800e0004800c082940c003054005423004902034400c5500c0c03041d072900309000f507602e8034805900410740b240c0b90504200b46a181e00c036040c2c1c4c010400300061405a11400010070aa80c002d2081c941e8480c412907205412850050000c000050184644481aaa1407041d450002d400010205c2d0740803141e21504d0082a141e030000e42c040c003200480204064200d180c030304005001701107941c08080304210640792403a0031540d16034590001c20090001619060038160052554507056a2504015460004551003035a400a020a01008024103c100501c20200002000542c5800c2c25450400900389008500400090181c0c04a800100c03403400b000703000c20450000c04600040c285446c14584400a0317154a4100d402080344102049000d55407031000c850196884c0b401650382c28019112070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799921393 1250 799920143 799920157
    0x29031b042a0e0307051806030c1e180609040f210c12020111090f0609330f040924030507050f0906030c10020f07080c0f03031905 57
    0x215946005280c1d81650080308a03460390700d01c80521944102024000d8a010380300d10989120b81d00c060307418061500c3d440040d034500010006890680d07250680001e00785078900c1c0c62942c0180d8802c21071084443c512201d6625400305480c25404010030041c1801c5c80002283e80c5030b00080e1800115001411145030a41c4c954028148205420910703110110700038510080140016003e035a8030003440805000040d0b800170f80c0c0001c0201240c2e080040600d4000c0d00465071007a510100000b4442d01da6504441c0413900080c12600c050300c900721180c4544140859004260f00040403000d640e0702079000b11400d50034600c001c5c0e410107180a1420000e032040c18016102c481e11811b5081056054445450245214402078051036007041c040c0048008000d0425100e112507005120498a0120344c40f4030170b00301070303515034000206800143d280c1920308154002c14452648002543c0d00085203040240702d00300c0d4203407141031803101003640e00c4c02200152075000c0c1055041079441c1d80680d00070031103 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799922643 1250 799921393 799921399
    0x1060806120d09061d030a1b18051005220506040b06070b01080d030204051f0c080f040810050405101d01060e0f130c0920040929031b 59
    0xc405040c00c4142c1002d0000000c2800f080c1203250600400750415000c940c4821210358010900940c400000d603600b4003014050900340d4240e43c00308074000e080380191301030407680c0701303d1903a40c0ba240380e0700d80206012654480c41c1b035070040f40480c26140c030b041c1285000c210030ba520012101000740240007031a02a10032540240c0d030b15800440c1ea00c4a41c09000d00e28014401c0300c80e15813400038102d04010724036124400301403040005000c60703500d8030110303541c82c000304686464440d860344051790040003084000e0071960000c01d100c0c607802d020900030402d4070030040c142c40004540401000070303100d0941d0014501d801203555005051034ac0d622404070440c514006092002c880309a00c0d0031a0204c2d000040820221810800b8580c4803c041c1ea8001c00c2510b0441c80011036074aa268481145d402135018150711101c14584682050150650100988104665640d6034a10074001840740c1e408034644500c200421000c2030040c2d940300b4003607841c090040c12408900f03e1184900c00f12500b5030f9a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799923893 1250 799922643 799922659
    0xe1801090c0303050a090f0f120c08010e0703060b0418060b0a05090a0608060609070c080c0309060a0504060f0e240c190c0e0907091a09070302130506090901060806 72
    0x801c07081940a4011030107500e07015681c460000d80281180040d800000e0600b80f000820412100780070415800c0f00d021556140201c051860940300c10080c5034040c40442d03007408036928200c8808120310040b00c1c403c000810103040200c00380420385080a071807600507484800c0e0b03540425025009101a0394004002030410354490b400104c45510030f441d110400f0b03503100818406410200300054100904484e811154030f07280070000c0000012800090504002150030f000d142010000e0300d083c004018070440d21000350000c0240690040d10401e800500304816140440380103405e100c41d00c18019081c109005100c1c403281240e2032540d0300a0040c188204216000c0700014801c400507800b030b11404003418100e90510005120b565001026105502d20500c5600e42002030504100c55000401049210070071020800750040502881d400000d50380c01c2000f561b034140c5c02802291340007031502d07080f2900c41c014452a40244020030f604044400d00512625010300c3c1020341c07045000344858 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799925143 1250 799923893 799923911
    0xe0c09010c050d180608010b0304030c050f032b15050111120c0a02030c090c12070c0206130e01170a060f0204080d05040303030b2d1302121503070e1801 67
    0x52070043c2c40e41c10b0f103001840c400021000b062054240781c00900462030149165410108043d05a11010340300800780300c00d9403e400c08101080c85000e0031414007500780c036103448000a001c0c0000403961001c0421149407a01806c040010344036000300d070321001d45aa41c03880d00300b400654424110034900b210601c90100780e00e0b40003101d0001000f003041250082d1001c280d0520625281801914107103114640f480104030310007198005031091021400c888000070303191600240d42c402e11040c1d000c1c0d0040c00007e41728000442c02c0110204590103030001131020380e624907038040f60800e84469038070250055140b01021610360b0f08541c000c0b480440005140550300e4501a04d04001003003010013048004c0b07410014143c240c490308050305d400b501c2100c02e175140048401e18903a02c03c0e06112002c1e11103100844591100c0340d42005644c2c10410440da90107248107040c4100340f0807501d4001d8407500c2c440206080c100802e502040318403281d002c8031291200c4a541d1041221000007402c550b40c0c0381040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799926393 1250 799925143 799925153
    0x1a070b04030504170c0f0901030201120203130f03051b060903041707050a0e0a240302060703030e0d020109140d140313081207171504020913060b0a080106090e0c09010c 74
    0x4030904d56035190003401015051800d0219040265003000e03c6400e95200410150340c01442201807849a41030040e560765901202c1c0f101340b0316900c2c026140070220383e0081c0030150448000d0080e05035841c030610680103046850303990b0344401c48035100ba03508180001c00400586540140396801a402500e04480c0c4503030100e080c40c1c00c030b0b510298554040d2014804081020b204020260482d6400c0058000142d56010441183e07444028014400016140b00b8188a640061500004181a10380c241c8200a00a0180448800654403042c14540d04c0c45909400110810b4984503611206c00401c131b00300500c5d12079000205294049400e882070320b0001092040285000e88504420400606040302c0042000c40d0642c44a9803640b01340c42440340030b1149000202100804490160751010090b01250361102e800512100e1b0034146180400e00c075000c280640401100c941d68038000783c0c0d84807021900c004581c8560325601c1036030000b1480048007130004100340c10060404008880c3c1c0d40e550 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799927643 1250 799926393 799926419
    0x3081602150703200309012c12010507030e19060c020307052a180433050108161a031003081c0f0e0c04020d06030507080d02071a070b04030504 63
    0x200301c00040e10401d40080001c445136100544c00400c6000b503062099500002e0440302000c8040c0a54400300ca4460b0900a260040c5c003603580005415104d002110306002c0d8003820f0141c880c0000320381802014420048002003901e52804000311880926206417548402030410b445001c007140410841040400d104005045048641c5c030b540e400d003020400c00041d18000204401761107020300b1440c880e042200f40e11006c1d0425003083c06501da0162520b152240c6640314a0000da80d051000001d441c1130066521080c101c600b98010342d000030311500f55102015600780110140c52040110100982d01d55001942d4415903100301e1f030407015146c0e1103a0b005500030400000d500f0000c0a4501003128407406103000294085205020138650f03c510350340c6404810700f920740580d60105a007030340103030300390455001140c01001b40e9110316211801a038640f4525503101c0050300c1400400a40e0f89000b6882208200c0c4044100341003106554540d00050b84c00b40056040000a000c08209003149040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799928893 1250 799927643 799927657
    0x60305060906060a14030a060b0424080d050702090a090312140612070f05060d2d05100e0f0a2c100b06030610140a0521010308160215 59
    0x402401145058000c000c81c186050f04172543c0810210008002c41c0c50024003014002d501c95804100c0c1220207002c28000c040e80650503024816100b054140850b240400720b09547c1402c01f0707500c2003000c1c41e5003640c4a210b100c200039000820000045d600d4140c507881040340703030300c83d1826003044048101d401044d03499082c03103c0d110b403c6e032030144051842d165000040800e0b042010b480c0c80b501d400080d5501a10a04c130b0305000c0d540014a604030300d00d8660101c0c0040c001031400d41c02014071400700c007000c02041201410786a00e4203000c9524014110203038021151075403400740b800da80d030349003001350f061010f010380d0346081d25800f4480c521445404a9032642c84110f1601200041d2003132100e2074480c882011007186883c0200c0781e15261250011070380e000303000b41c810100c0c208040310212524401c0d55000f203c1040080360644205c1d42c48002071503000c0c044290310f503074804841d031240580d41082c44020020802040b40030150b0700101541d0400900007400e801c40c060002003418050b503c060307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799930143 1250 799928893 799928911
    0x30204181a010c2f09101a0705100f1503050309040f020c0c0105070f06050c0310060314040b181e330a020c0109030c0201030c030b060f090406030506 66
    0x6201220a4400ca00060300c21410929002da0240000d868000324045411040114902124524092450840e800f040c10413005000480340c0d150900880d42c00700c030b01d800b0b030103c5540300301150201c0c0807052040e250b0700c030b0b0064045c00074071486d1000e4000030955115142c0290b51034040080c54510070f14602c2d0000e40c05040510390741c074102d401f04012130300768002e8140954810f01c00d13542004030005c1c007810b45000a0070000d81d034a0311030402111148030444014045805c0c2802c20410b880d010014500074012280c2400307080d500c40000303030280d6101d07141e241d000e602500002004240322110b0245c002507141142410304094000d110704201d0b0b844040c540110300030700f852040400c01c10003511031403c0d0303c0c01401c01007191041c0324902d80054045141c840c084034003048003142c1c83d50459035030700180c07002004104207500e0041c2c01080541009e80c04a8504040041024000d0181d1101840002d00d124070b0542c0c00000180c541e044480c4440d041680c6900120000b0740401145000351f2003e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799931393 1250 799930143 799930151
    0x6130c1e051f0f14040b220303020106060e0607050606010e01140a02010207020f04020301180f0b0414100b0a050a140d06030812090304030b0408030604240905090c0f060a03020418 79
    0x1840040d124441d0001c0480800c1114a021340d60440c0ca1810354054130140c14501d592601d00c00800c000240c0c021000c281c0c00700010703500204040d0154440011a1459240e003443d50082d00200500f5000d262409041600800e00140c501d41c4603101c582269038050514442c01c91100e0f0145415030061607440000d0b17980000d4000c15490020822031a02800720717019071440d8100b132508010450a526090521901e96001210301000303900101003100b000b45c07082101e0607208001d490300c59401d54036080780c0b00366904049100300ca580216200304065459491808140001c03c65000c00c9100c5c941405100500861105c201140100380003580030711032194079134140440e440c060b5a0b02400c620201c0e4002c200800002d091401030540c03141d0000c070380036107036a0350b800401d0151000925814030341d86a1101070b140050021041025038117070140400caa80ea80c0d10605990f03070041500d65178450340c01103900c0c0302ea2030160000d082d0100c440c9005402c26a560813040d540034480444d103810545c0b6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799932643 1250 799931393 799931449
    0x63818100816080c1e01080406020903060406020a030b09010302032107171e041514120f0a1d0606190f090c0f020303070c12050405061201050306130c1e05 68
    0xf0803044c2d55100c0212076030700f942010515608540564401903505120324000000c060002c154150741c45007c002d410349206281c039150901c003d6001803d8100441d150210030045800d210740c025041c1d0380d016000f000c075405400c0013000c040e0001001d090300100c003001548006900d01e11040b5a10b0381400c0c50305d031a071170740c2a0790301c41c0340d485560303404502c642c20300042000290012441d10f80d203607a410814008030040030040001d01c5400304810080340d100d8244580e2007034100e806841440420000c0014421040c0392110101e40140c10510541c4083c020403254501001c101c1c10113070000b01c82c03101c240e945032111000320303845600c4038000da95245100c40320b05810008a50102860744041c0d891482c103282d018000030740c00300bc00761150040b9100c488406008004550141c40010a81070300d50550010340d00c0e04420901440e8000e00604012035000b0191008070b10311254045d942c501c1a504107011145000b808030781c0b0705405080315034001042d841e600d10486202c00c1a041c0a442014 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799933893 1250 799932643 799932659
    0xc0601061e12110c0a031809110f0a050909190c05042d0f030804090f02270a030b0c0a020111091e0a03063818100816 52
    0x850200441ea41c1c05010842804941c4503804446100300761600040290324948845064003d40240300d00b02d100c0c80b044d241c1810b401c45460380b800314400130500911a118600700c0c003554040000b00340a618144020b440c0c0c50f1901010304400c1090385080d50415100074002046040c0940380b17500211015030b000e00c0002424000d000b042c01c0f0500303101d460303c0d140503c0031460040d2941c02c0101c01187c0c0d000c40044e6410f4110600c01080161206c101e446e44074284010554021700c12081030616111020045101c00e000b507030b60b0440c3c2c0070f6040c491141d00c50340300c60180301010381440d800429410007100046081c51841c0c05503103074003007140e103413030410202070708450082d801c408940205022100983d910200c0402c42150076030b000c6005401c0c0d800106503c103202d80c00041c841814031041541c1114261015003105c58411516050b44083c0a8050503080000f002d2540268881814406191504003865000720200010445450b41c0d0400c8a042c0714120040082031010758104000d003007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799935143 1250 799933893 799933907
    0x602010b010c0b04030c03170720060601200c150a021603050705060c0f0102070809010216030f0f030c02030d120b0306090601152604060c170a1107080c060106 70
    0x1400c00c0c20110203a009589507100e400c1c1004000404220058035140d0826210f040b0302010030804031021000c1d4102004060004100880080041d0086d085000315158000078803e00a4a060b110500c82120903014550705d0105010001c54621401132042020b403108a070f101400002800d00d2511071030001030007030400d91603010700d2000e0f00800d40e003800480c0c07011400c4400c80c0e608988565035200c0305000e9a08044405041035040e500c0030904c038090010342c00082c07807608003d81c02d4440c1c000400130301949145103400082d00031f0310a52480c0d00060460050030041d6030090808081480c0b142d03000070301c3d202d03000300f20000041192003002c10200c814014641c3c104c808030003030030381703403801d4401165501414450300d06a1020713000f030703440400d000300740b451a89400b03100c80e01d442031f40c042000107030308070241d0302200c1640c581090810b86501c103041104c102c81034120030f034256072a030000403800341040c48440b000040040050318001420500201800101d54010348800d40c90100054408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799936393 1250 799935143 799935161
    0xa09021201140c0d0b0a0f060f050f070f0c0801050a14150922020a0f08060705180d030923040b0316030308070203070606180f0219080408071b060201 66
    0x507810b06218041200303002619580c001d03400c4286503200c100141e02035000d01204044e0b5504a03c204001003104000c60004d84191285510380304442d4989640441c1c45104000b2130a80d46542400201d0020b400d960295102c2c600901c0c0c0d01c1a400d4440403c035007101c40c00d07241100440c0d99280410650300c40105181e501c80041c9a042810701006800704070310b07036001800c0c5440c00305074100c40000c40d56410520403001d80c0280030540e07510b80300d440b4070300d42d20003a0084242c41d100703820018034810303c10000c849610455003205000000c810f0b05100d04041c072060120700307005e04000080b821003000c00070680405280c010710500c0c104000d09000c201c0e180b8441e00342c02904002e6200065031354190300b1a00b103a0b454a04114541d46078841241180554180184007500303100300021030540c110210038030801078820822840c485040500124171926070100450000d404214032114042e11920358014091030509107444107581d2111040002c0e4240e480d41110107241c240409135092050f1081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799937643 1250 799936393 799936429
    0x4020102010f0b010e01080604060906060807080a18021002070810090201090503071406070507030f2109182408010e0709020306062a371a0606120a0902 67
    0x81e510043e00003040c0c20401c03100f2605011204003c1490380c0c4656100d40000c044010b403c000072074035020003c10419051390b401c1c1c00100c282c0045139400c7c0e03151084100d500303244002030004002c41e03030902041881070103003a810b6000f0b10341c00140440f403c4c000c1030304138000b00f400010000a20300c005803008003660081d85c0294008041401340340c1e419030210b19040d004580c0a0b4a030040717803400302c5c5401815007005158440d50b482d803008200c00d40f603900b002c02581c1c0d20702e0380902100d00001c45000300c0318850804081010140c60001000c0e45d0302944100400c200080c04002c40400325904201392a03018007610381d5602000742110b50240b203120041c1c20b040d80158690f0401000217840e42c0650807011002a4070440c0b80401d50f540d16030061889102c0505a03001d0a0300a01c150206145650911803c2111a41d21125803840341403852142d55110b049040340388903c42d86081102e00080c001e0f070308801c2c1004580c1c141c3c102d05072580d110b14006800410620700ea4410720480303c181408401c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799938893 1250 799937643 799937651
    0x80a020f0c0604060e0a12030e090a1b0e1c0812010503190813090f1401080d1b0201210209031c05031b041a04051f020d0e01170c0304020102010f 64
    0x10650781c4142c01c903021501d00d458100c006a09180019820031b240303600c01030808003081c060004064000500400e031038000c41e411121980c41c07034081000d48028440b0000a8415400c6010300d071030145980c41100e0901401c0c0c4a005038a1400a0841a0380820150380304000400c0034548450191582405003505a0260948503801042c0200060948000603d03100b00403e10900406410403078000030000440140024014559100001c202c80c4401c2084094000004500e0b20300000d108402c3c1c48041d034600d01c403866005124480007440d210200e04000c10701c50b52141c0b507000c90040325000311b03c1d0030006070380703159800c20585400320b0041c500803010026241c0f0080c1e25085000d50740d1140e0500f284c511174040324400301000e4803c50700009080c1800c0c04050800d00c9403100900280c030f100f076801a480c08407000c40030340403266034096100164012422418460702c03a4801c03003002101070410003040380c1c0e40540008001800c8a10b5070010001100300310a40d03a090051803003040e18840100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799940143 1250 799938893 799938913
    0x1706010609050306012c0112030906030605330318011512080306030c0301021309060504020c030a0f0c08030115081003031b0201020f0a03080f010b0301050603131a0103080a020f 78
    0x2a46130705051048603080448030110084521180c040c0e548881180d07501d0f200c05e9030b121010301d01d850280590560005040140200e000d50081c030802c01a541c005004c00020085010340440d41281121684c030f50b650390b0a2822240342c600c9029501070004400140114a1207144440c21103203401684c1c0c00221100404100d41410328100b4401c01c5d1708804c081703540b5039810002c68a007151058429425600c0000e1010158000048010942c0d81c641d80c188440d6544d4420171050780641c585416880d00200100190180100c40c25030b00010141044950741040d51a000c10640007680041c0c0c90b580300c900c0c41d601c0c044d400f01b02254001140ca40c803010150540e10024501d00c24101c150700200b06400300c0718251780c020040110311603951720449142c042140f40c0100418800d451455110700f40c0340000c100721583d40c059038140c1c1c80141c0910304603034030a22900c92030000210151005425640c1c503900e00e41c5c0920700d4030b02031405640b5255582d020b0b01c90003460040312030380344540d580140d50f01d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799941393 1250 799940143 799940149
    0x5070507080a0e211b060409180b011202010306082a0102071a0414120d120f020703031b090f031218080705040c05030601020303070c1704170601060905 67
    0xd94903480d0080203a035200c0e000d41c0300035103680b00a81002903000c1c0381e420300150b28600846500405280d4034040d1522240548941c050f404020310003594840e0302840300f070100d44802c0c1c1c4401c10030040e8601400c0268080c2e25050b43c1c058082c0c0003803c1121100050f202507503014010030006004801c01480e00d00c80d282411007000084c00242102544d401c1d81d000c2d907903842080340303402030b125044d03403c44107411507080c401590f4010700c01c05510f038003040300340d03c2e030b600d410141d20000411400141c82c2120700303880211180742d1301441180c482c80c1c0c0c43c0c103908184c11180c405808080d02c6900d0006039150380101030603a1040d001507240400441480c1070107444540f1490034220703580070304221245882464180c0d01c429041e5035441041429031f0000401c4840020003200302c5009880c03c00c1410300c081e0040741ca80c4000c456040c0568010400b02e030340b40c0e03c11400c2c401118000c001c0507000510410340080158001e50100921040304281c80d54512420b00c510f07401040a818030707070341180ca4503000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799942643 1250 799941393 799941397
    0x4150e0616142406010f02070902091c0510050f2809060c0f0e010206010b0f0c070e0a02090f09010602120f0d05070507050f150a1e060308041503050705 67
    0x10a6203200040d1454900700324080d1002d001c42401c0340142c0c0d80c3c440c0100c2c081d5031074140020294000c0404500401d20650141c4100d60000b40a54007400c0701604082410020790b0200c00d425420030440074000303140304190405461654400c6000e00030921820309034200b9140d02400100402044506200d600b410310303440c409504800780d070101203901c0d004c19507500605803518041c01c00e5082a8016040d03d078403144180c854103083d1100d48141030f000700120b0f501c1e402405110103d200400108031070001a4000d403195401c22000c442d030307031500e4481402007407030103840c0780c00c5894000c60400c0152038a541d0403190b9642c191480401036241c0180250b85590100c039800c460310002407007204201c2042c04880e036916012030184518141410010190740c4444015210350060f20300c0041400d1000c119802000c1ca6180f241d042c1d5212000e0120052a2801d1000e0b1010745003400c1100e00d04a9010300401580078a5050b0b42f40c1d49080d014071a8800c101200c1c604052030103080055064010702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799943893 1250 799942643 799942657
    0x1060f1205071b050c0402030c0903060a1a090c16081305040e1510080601030308010614180f0402250611041503110408030c0d0915211d010204150e06 66
    0x8000280c0e0060303401c3c000d0a10140210091b00031b80004100044051248000c0c000e061042c1c0c00c880e225911307101101c1c12180c140b4a0b4800080000181c1d898a280c520b58542c0c2202d880001c0c1032030f003400102040c02c02d01c00301c03000329580e070004a80345100e004142c0340b00000f0700007920103001d40c149242c3e0958a902035a1220000381900502040c80754224150070b0001c0c1c402c0c1003c83c2c1e81035850703090180110b84248500400036400d82c24580d0140d42d03600644000508400181c10485004c3d010801c60300341412940c2d030032560912020400407024114030300041e070348200c580a0380c0f1072403c09400784c0703080c01c41e101a17002c41080100520300c1b040c0d010f20f120300100e160000e038071040554010101c1c840c2c2d80c041004c920000c82c01c810308070301c040f40c0350401c203007641c450280540d520f08040000c00603e007404408202c0b808100911041d51a9104e8040080c840340080c0074903406141c1010440d200301c090441d85e5010a0511400080141e26268201c5506224501c0c2c940000040c50780e101e401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799945143 1250 799943893 799943927
    0x608030f031906030c0902070605280e10060f050f1801140a0e0705090108061903030809030705070308070309081b1e0913060b0d0f02060a11030301060f120507 70
    0x55002008902e140d80402c1c0515482080d07010440d6480c03001e00040d400003101500d5251908002c95111001c0b03c2c80d20010203403034040e051800380c044640340c0040c02040c940041134040c500c40d0440071204c80c852032020300b039840c1c040c001d801c1c2854203011007600d810450a00030007001c44010700d04122444418115030400808c80c090b0b0900b8004205400c01c15400318107a00502030a10040c260000050100614203030b03a403050380c0d943d820802c1001480c215494030071400040091002c00d11601020b540110010704803413500009070ba4603460326a00da4419190b440000c9000b40c02c05034056079050040150740001c00c80f1b040c45d2200c03c1088040f03c0d4400c1c0c030801d078800314494962601d503040c4809504c0140072030001c1c508040c8210100c0019001128980c0c6022607902052500981e4065519045441060f0f494150340c03e0145e5079010300900000d1001d402000c8084042c01c100450203812190349582c4005542d90300940b0f02007003c0200d0a803039003401c2c01c011011740c3c04200c01c001160b00c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799946393 1250 799945143 799945171
    0x108010e0613050309060f0301060f1706130902100c0201020d030b01142b1a031606140c0703061406010206040f03030213090203041202150112110103020c1b040608030f03 75
    0xd0f20b402451880b401c041c1030b80101e0003040d480040e041020185040301c82c9521600b020581c4810201c9a01069400c0309100404500200d001420018445900700d88030980004140c2c0700c50b0002400c084078440401d00003842201c800045580c140154001d004040c01c0c01c1c01000c040b5000079007071083c420b440b5001c0160218104018104401c1c003c25040b11001e01044030702900384034032004d40044290000036403289000e5160380c1c2000a4000c2004010020b1282e001741000c031708590900100c0b0415a1101c0c0c01c0c41090540c2c00e0a002c3c440085105420003c0c200d100c1920100ca0900d000302401d06540001e000c00004c502480445882190b052500603035a04a9048035441240c59030004ea43c000e1000c0108410090070700ea2104501e1065000c40b068030031082030700703850004240602c00d42c066429000d5000989945140214881c0504000d4200900010102d141c000d005c5041c00b4420041d008203040c3c1e041510680d009866044042e41c41e0000780c4600074881d120281091030382c4101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799947643 1250 799946393 799946431
    0x601031101120c021501060504031a0a09020a06020a02150403110d061803020a21091a0d0227040b0d030c02030a0f0804060e060406120f240e0108010e06 67
    0x82485814020070100074100100f20707046100940d50304c4502c2d0b2032240c5910050006c24554013850599080780d130300c20703000041a420b051b201c4c000044050804c1500e20307190f544800050355022410b002805540d40100115803050040144015000f08002043c0c1c2c0e00b08270500101316030030f40340003013000265002411f00021b0324001000f00f111080f52401000c4008140003090303400b00b43c15041c14043c0300440400502208400082d1aa0455540114400700b104204618600c0c188100300d1ba840e00506042c00c001c0d141c00f5042e41d10090311641c1d070820140b05070003004c2036008242720010060321704020140c2100c0100e003910405030405000d0002c0684c180f004c6540c01c010044403d9840780100d01c524605140400154009006070b401098034143d24607141d0411704166400c694483ea9441c1410208100203002403050b0425141e409071600300d000d60301c0404816100f000d81c80180c1c940ca100345008e8a04010326410303080850f45904200302c0502c00f40e400180f183d0455200d80503181e401074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799948893 1250 799947643 799947647
    0xd0204020a210608060c1615020d020a030603030215010e06150714010914061308210106050c0106050303120f0910111306110d080601050f040f080c0a080601031101 72
    0x9a00441c84000ea4000512030242c0550340c202400702d0b001d643c12644603031a49000e2001d107005400c52101c00208814250700424512290185007840b0504018a810801c0008500f030340d0101440300d0100c0e48562080041580c100440c1800400c050030340903040d4103003270034210080c0300a0300c0144a858081d40103440002ca98044512403a44409002c11645081e00c2c80c90190a0044081d5120321091800d013150741c00100349a442060120403230346001102d5130f9100c540b038011407013019010003c0c14007411396207148500180070707000e035484560716a00840b00f01800d449d5190031460007600140610041d1640c1044411b810a000c86c6440082da566004024580482c0400e40216681042448000c0312602c0b0021700c4400c683d00d044014041c0c07201001d17106014204000f010b1548400c5841d250313148200200f40d00701d207052510038a04895100c1c2c80d0340c1c80e00940c00030088002c90b0401080f003100100300c0d000c140f040507158044105e00c0c3c40c80b00e45e141c820512025090461264020985038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799950143 1250 799948893 799948907
    0x16050a090902040e010e100303080406091a0403080906010b04210206090607080c0c18340206090607140a080901141503060106030e07050d0819020325020d0204020a 72
    0x724040c00c0031519159984a8041e0741c1501388035240030074032030601140d5005201103000d416250103458850942d2192369420008180c00102616075151030300084038400c180c0300426008078003e5079212001e00344092000c0c01c1c6403041c2d11840000c40c003000104100010070540d03001032441e000182100b55120b00114403c4e101b0383d49206d5112000191002c10030840b01c1c003400303200c00030368115450320380c190b03061225040d400240c862050340b5410001345569401200800155900d403845010050308003000d580800c1000402405a0811010001c0e4030384100240c951200d8145082c000c0140300b0310900010340b142407954020414040000f80290381d09400100320082c03646140c40485c44e0045141c801c466a0050340384c0700340140303800003ca03e48640500b691084c4c40c80003802425161a040014140d0660790403181c05101380900c0c0018190355410300d42c035140030380196642d4070151480e496840341c5030f246000d18080200b0104090386403044040722060f0706480040c1e5841d0501400c1c0c60039 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799951393 1250 799950143 799950149
    0xf010206090a02190e01180b0609011209020f0303030a020a0305220f1110050a020f0601050f0d060b06070602040515070825050a080c010605040b030c0d0f0501060905060f0916050a09 80
    0x101742c00c4c070000a00504100400c07002804000780801c51414002c040007100e2040380d6100740061800c0b541d8034040c1100d94000c10710340e44010400a039898000c40820300390703001150700070041036001c9110342501e034050084590104005417414a4046d100450b070b07004103800752010304a00d06070100c141c100440445031219a007002400030003847c030750810013491507228503516001400b0f0100c800e8801040007071100d06844e0020041002c10f02c1040c01d0000c602e41c2a0426900c0c10345600c210303041602c95800038100c0c203000301800350340c45e1304003401d000720184102d04011980300c08000040100714004e05584100c400329285600d10f1a13445044048940c038854040c1960040a8442040041000040031940f43e444000e11100d40e662041000300c42c50403a1043e0075030405c680040d014602503e1800c45640b040080d00c419500d1911050708581d82c2d60043c2484503559030a00c0b8480ca4034085801500404072000041880c20341118510b00e00304056001c18010302003000041d40f03000b11208009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799952643 1250 799951393 799951409
    0xd0809030f0601260c01020c10020c04050109020301030b0c0f0a0518060a120c0302041d0603070e0a0b03011a030a022e0305010e091c051c0204090203060f010206090a0219 75
    0x800c2d41c5401341d00384030300140340c5038000803000030b04128450140800d0b00350400d54160040c0400c40c1c08081400302c038a2600c00c03100d046009944495442d135403280b0483c1e000e004184401038032581146040207100c0806400290540414407001c08403600d01012101d0020302e600e0030584440c2c2961041e4103148815282c142d0003800404c66804107580507941348403608a46606104a100aa500b5000ca2085008014141720699441c0407074085214100790008401760803110003d60f205161035406900341c5000018603110804043c191409006010080003080e118030100307041c20300069550740d0103010003800340c01d003071081c00351444007140350700d60b11f221aa07101c00011031480d03c0180180401d004001103101c0f46008640d000a001404010b4030003285041240000304120586072900010132281a1580c000d00ca040b402002d400540000d201030f03000940c0300c0c00d2a41c20403a00740400003c03541154492001c1040035600000c032141c88079015503440300401a18146803107180b00c95040b40751 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799953893 1250 799952643 799952653
    0xc070f0803090604150c050702040911041b02010507020309010806040b0111102003010305030a270f0602101104180e07080607020f03030c1b010209030a080301170a020d0809030f 78
    0x40409000c00e43c2c40c451441608002488120b0900910440b07210050201c0015028011344c00141815403142c01691700901e10950680003800026064848410400d80c1c1409030405098480360240200d41d0052061700166090490810000301002c100420b183d101325111414500c959000300105480d46104000b680e800800480c9148090900300b0140000c4241640002d00300b41c03000310640f07040e00e6112000c0c40c0380a00744d110450310350181d100700d400e00c4004820006c0007540319050020041681c0400f1030801e514211000c2e0901c03040910041c005400d0100c2209605204c50807a01510703c80034040c50f55200b8018488020200da11b4003040d85c2c030880e40301083e1586c0000b60140304e6104c603030840b0348941014403150785070300023034035102050b000903c07001c0c40c221807104105d002c407034a1034001410540248002454a0b4160000780e0300488008014084000860340d07080310003001500a1101144a0707004c1000c8015032540900618000705911107695010711941a003c000042118 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799955143 1250 799953893 799953901
    0x10b0f010e04020706092d0b060d0309080708010f1a010e01080709260721022115090105180714120d0201240302010f121517070803040e0c070f0803 65
    0x304403103000c5021881015140d04240b06d4890b24401d175034444580c4154148e034282c8444042c440c1c0410640422010b0064020000c614001d00708110001004918004948030300d403240080211003206550901d0601d8800895a090341c224000b800c0304030080c600b035002540d4414003154500580c2e0000d1000b50075140129030884840030307110465071020015110401c0e52440401110361900322080e4500c0380b136072100400761a00b40203044d102002094001c400610039080d09041021061000665030084014041c0300c201c24825968042102d40d585112606110390340b80d90360045201d0500325415100c1c42900e2a160010583c481510302c03c01c072108801c0240d0064040d140500f150071030303c10345c407411141108040429904580e01a1030341d10301e1103060340040300d040c0c565020303110000d62965028851400101e03000001800385900c0003000b90041454503003800d034558801b03a9075520a00c002d02c04074114080050300441d031b20081d150707200312500d007000540030054000341842802200308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799956393 1250 799955143 799955153
    0xb061204030e04091b0819060e0c0607030807271406090a0602060405190b06010c061e090c050603010305030301170c03010501060c1b080c19090e0d11010b0f010e0402070609 76
    0xb141c25100c00680c0d103001251150b800c43d544040c1f942850111000c9105002c000c110180d0181c1420003400e0252a100d01d103082c042075461780188030403000102c8020802100c5030784000c803980040e070381004400004000d4482e6808402c0c41d8010881001a0b00703400480d41d075038401c104c500303a0001811200c2095030380c00c000f0b922400200c90544841c001d9080c0e88016452044021520705e80c4000c1c001003540f1818011a0110034581c0c01712001e41c0c0c0c038080b0039102080d2140b850202a85550003085108903403031310310102003060b841503005039424001400051380c0402603038156805041d094144091211000b441c0042c4a0f90403034240d440d02c800490382a5228400c00c1074140900b5103030043e40c0782c031815031401007001e200e0b1500f540c1220f444580c01e840d14004d40d050f00001900015492901c0e110550202d0700a0041e40c0c400b540f0485012044907085000c101107140c500b002041342e0390100001c80c00c0ca400a1f15601d04004850706903008654440d03040d2580690040020404940c0303a1502c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799957643 1250 799956393 799956413
    0x906060a03020a0e03151b03131212090809120111090d0c091401060e0619030b0d0506090a03030506011e14120720070b1b031c0903080a0b061204030e0409 68
    0x4014075483e07e0802443ca40e04170000301c80c02522000000c29a90701240c8030444100c41c1d0900c1d500c200480101040d038080313118000c00f4407290060b07504030b50b1215040204240307011300380b641c2284c0764100001024218a04c0c030540ccc106500035140600000078a18007840d09241e03d0b0081c0714241d1810343c2e4008001c0e1041c3d120340c103071502900da8000401c0c40b03800b00001c500441c01c0440502005070b24400c0454400d40100409450261003a00340e10f403581d4030281040c10403604010564400460001815070500895820120a08103500c1c1d00c065034005015518110f0741c01020321407102004c00d00e6248607000c40c0e1841d00c0c046d6640f0080d0070700140c0101031019001c1890340150b4601000c03c9000408241c01e800c99141611f541e02c0d0403c0c51442c0315070407001e40d11000080c0002d0045401d8011548413040401001d140002405000b915002c1d16508010703041408503450044a15120b0b150700c4100e851031a410b060500c12a40c2e1450110b8013840d0b03840341580c0280c14607400d0400c01c08003041d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799958893 1250 799957643 799957651
    0x203060d0f0506011401170a0c1101020703080f071806050901020a0f0311070b030910050c0721080c04031208150307120501050901110415170709140906060a03020a0e0315 75
    0x340101005e51340c401191030000f20040d06425501010224100d51352540c41424440610300702585418189a480ca08a801000040e40822000030810070800e48900d032040d80f0043c94284006184d0f020100504070040034020355040c481d001900850340e030700800502c03643d103a10046800740c2903010f260040400031000c040075410321074020003189004034241542c0c4584107080042205060408649020b0040985000c49480d420050900880c14141c40d0142c00883c4964000c1c0da40181100240460002042109032800c00e000600016840741c40c4984140140c0c90315042e0380d103c0441c07001d02511002e2a660b850301c203400340024090400080f260405005800810460b510103240e00c0c00c4c0c1d0bc071641000154401044203200c850300854412161100b94540b041d4018840e103410004880142c81c80c9010a010000411400000c81c140007804070041d1511481750a000c000319080303021310441081415000300c0c806801900c42d411602241c58018102c0fa031080707400701c583c03a2503501030b5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799960143 1250 799958893 799958909
    0x161a010f0510020111031311060d060501110d0509060f0904050411040e06010e0c0a0c1703040606150903031407051b030f060106140a05040e0a0606030e120702040203060d0f050601 79
    0x3450b46601d40c1c010300c9449020810070311a40c0c03855030346020320210b074400081c00710703a10f4043c800310580549911019001d40c0101440c006403050034800098440c1d03001040c01d603203136882881403101a55004040d03400c10318050341c046071078001420060600d0302030040c0c00780d003061404c000c000500000382442c05101a0070b4034100981e0f0031107115991100402d0294083c00310511012034424540c0800074512750466182041141455070359000049021003c2d81d0080d4a002c4280010700c035103403141c44010015110342c07401480c0701d2000504a0250340c4406000d01558003c004a250381e10340454580c01d5116060340d0b07601282c521080b24161505100901901c80c410380261104000180719050b5078076030300c814684149184444283d9441502c01d4404c2010611000800b03030889203850780a0300441c400801d0580c14814000c01302d4481c01303040703c81a400300440d54108071602c0210b9804c0d980540b40581d59030f64420105450f10144d01000b08501c000004440030b00030040348180c1030310341c1302c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799961393 1250 799960143 799960159
    0xa0c0f030824090f13020603130b06010507030e040b040617010906111c020a052514062701020702060a0c05010c05390303070207060e0303030903161a010f05 69
    0x32081202c18405482078070780d0040288808180100c40c80140c06a000c075a50301c4212030003c10f5801f00748250070a0726201d40c24407445c0c800c1c904011228002c168428001e203003c0781000c80c0c9840091030303000540940ca00403982c50301812155101d942120005d040340759909070f040040000709900a001414003070b1041480c0c144a40c20903203162040341c600100d00d0317440f10f0420f802c21154000a43c045842507050120421210329850f003511061000781171a00000083c010711414800b084902009111107590080380c1041605482c0c0700300038640c54441c00c40c41c540d40e80345410071802445103c4019600841c04241c6000701944a04903682030b9220304000d0012111841301a56140240c403185800c0d00152580f5981403243d900ca00c076900c0d10300aa4a0035203403568007005003150700075901400181c01001045c060726411140030060751100760f000314998900104099120301804060100544800314118244809511038040700f0f0500703034a0545950f520300f0864460112445118000c40b80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799962643 1250 799961393 799961431
    0x50a020405152e05130f030b040203190302120d060305070f081b1e03011811100905091f1a0a030e012013090e0609010e0619020a0c0f0308 61
    0x94811103800560800c2d030344400c1c403c00410a0703440d504541103d1498100080c4001180a2240c08a00085020303000e00c0300c441c20940141400d004002840b9132034100341d110600002030340001e00201c0c99082d4418140c6604400344d1007030107400745038000f400d18420200e0129440b00e56020303500803140c803d402c8035401c89041c940440384809450001e603020150900b0000b071b42826030351408005c0c03001030001413404c03079040e00c41d00c1642070f81d0320a58201030940480011802c1001480201800c10b041c078041c2640745c41d001503c0d1501c0248440c10103916001001940010105603001401d07031a800385622a00316441002d01d60004680719000030708226040030150010711500c59000c0100e211100d041c5228080103266a02102d0550380d4201c081d00000b841d002030b803160a2000e801381000c0c01e0075042c0000f5090940c0c02030600102c054001806221091000c0341b4070420011440b1005a101c0c4a6240c0c16200258414030107000e11010740501c0302003681c851011440342951f40041030b84445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799963893 1250 799962643 799962679
    0x9180606010207320907200a08030c0a11060408280507020f0303090406090905010b090601170402010c0803040f03110c01120203060a0b0c031804020a0804030309050a02040515 77
    0x3580c841e18624031442d071040910000443e00380607101c0c090705160644070308410080f401c01c05c000ca43d240006014680002609401c29501100c20107054000744600130490b2101c002c0b81c400648050802007000400181d40f50040346007107080b03090300d025103995160904080b500c0340d1003800c03c8031100307a8a00108400c160140203d001c02240360360380034140170070307a0b00344902e20801443e003d0f894882031202c1039072907070340d405028058804407070042252981e0b460f04509485038804107512540d5000100042c0d640d1241c010061040e910103549101d80743c5000507941040764803009490300d0400003c00051000710280034011500c1380d555a140550302c40132042e1242c0c81d01d00d1050006001008225040419030091038200d4001494081d105669032200c1c0c185510480645c83e00b40c00220f079103a030303043c0b507a490b181003a081a01d0540c40c01000c424003c1203000c0040008050540c0c07000c041051003002c0216400c0541d02a0040109040140c142111003a05640040c0b048100400e0615401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799965143 1250 799963893 799963903
    0x40914150703060f0b030624090f030d08071d04050403110c04060e190f0204080a120c110409030e1302030126030318190f031b170a0e091806060102 65
    0xca0004c2920440ea0800c2c114060f69800980401d0303001002107600f9081c0a02c50b480c050703110f6034104403a541c540c098400c0c001001d4040010310300c00c0e0000d0101e6582190055001c5511959030701d043c041c45060703031b440c0103808450b0f618480d4005241c07400300000c140c1c00c5480811180c074840200d43c401c5a801c03080109441c031602501e94211000c1c17020890091402c1c01c040c2038080300b11404640401600d8461040740c101d540200120340c003c0540c001404040342e464800c960032031230845111185600c91420103406042175501a950f666041401e051203156846106000103195403040d80d10305500314040d420078000c04003000014452075804191006078062f010322508083c1d4159940c0c10340d4080346240740031903240c20b40034240c2c0f81c4030b0000020080c1c0b42003134801c010303407a1180494180107000e4404d0507010640c142a40718001d000c10240c0d22665400c071002164a56034444c40e01040310b0f1409044401604980384209000e1900401e1150480408044007251629038601d001240e5903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799966393 1250 799965143 799965149
    0x60b03030a0c080c030730300902041505030d0c0203060412200a030801090b01021f02040f0e0105040f0b060a080408090904060e0106151b0204091415070306 69
    0x2041c0c04003902d20015003504050046071410f84280c3e8100101380e1038000c45004a020b101c040748020040e9034510030640c14100b08611000d00c0c0c00321076052054807100070031032503e40184449004004409007103400e40c20031603050f03902500a10a2030180025200110300c6801000e07c01c0c000c5081407a03007284126482c80c5c80a4008006140c0c1d6140c80c1c94144051000a81c03141c2082600c0141687c140340e003404003d0110808001030140b80c17064200248000740c181c002840884c18400d41c88500c0c0c1e03000858641c1c008a51182d8480c9841d2803454a0080c4030340e500038840ca003101c4400007004503070200303000d04840e815913007407000104480c035110407294807040666210800340203643c1c051344503107010750344240700d258154a0050018006003600d5821a801c443e01c036220010030407402001e000d1000100500c940c11105080c2551020b812070703405003000d200e41071b102107460066541e542c00202565401c01080080f907903140030040d031142c0d1000000540d081c411b2000c0f882251281c0b14500131 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799967643 1250 799966393 799966397
    0xa0c021305150909030c01020403030507060c18090c031d010c14070b2d040609050f06010521031c020306100e0d12020a050d0201051f230316030f060b03030a 69
    0x8a501c2d0b820403000c407078050241d02081c4814090001038503c02d1000f0005540a6250f0315110741461a00000395080c1d00919410005200c9129240b00c4101940b082542e141c1c1c0300c00305c6d00b554464022801860106146130110380400151901e850066208a114030681d6560b580200320071030313407140e4903c40c92900502040d15034002034071451388182140c1d1800b68041144181c0025194100300c0200282c03016140c00341c0d01c89507803003040b6080080c20400025200503284030741c9400c000034445407020a450465050f8211000c1c0541024807c455040c040b41207080310b18860100140000c1d08103d90290080c0d41403000c1e408400c1c0600e0340520486001894030034200c159540394059040103000150652080343c2000001880501003400004170b15800080c140c80d28042540e440c2800c5040c05039010110441401413101000300d40155007a500d03244502e092046004c649071859404c80003580e030301c4080000c801c02040c0b11005000a001d280180400d464103400c04d07440f4405d40c400540 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799968893 1250 799967643 799967671
    0x20f090a1401090b1201140d300c021e19030f030207080f07060f0512090a030f0302070b24090f01050405010515090d03030f0e0708010c020c10080613020a0c021305 72
    0x8002800c0e050740785901103000e0920708820341d40b036590b240249c0801c41d615140e190074042004581029018611031581d5610341225111015004518110064150900c4440101c1d01d0302050303031224504840580940121609885d9513410503420890b21000d0840c014000c200b0300282032031000800f01e41007a0f140c4042c20b4500d00d0090280c440c2000c0500c03160070710009019044480f0100440588241d524101070b140ea0141440c00400084480011906040c814460310012828a070101540000c0307941f070402d0382e1400d03611000c110702d004002d0958810304200402542902d804a107604a0b5401d8a09002e540d0f211700c10440e90b4250319140c0d000c0540144455540b502e46841a0107a1b40d00a0070001040c90b4903000402c00e07a90169192810741d84489020042c8100910030a6102152031019100e085450000584002c1c02c212141c02044002c2c00032074626a503e602802050a44550441d5240010b50010b0610560207609912030030300c0c0ca00c0015610014007955205800340071250fa = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799970143 1250 799968893 799968899
    0x9040605180a051005060f0901020c060f1b071a04030b060604050603150a0f38030105102d121b120908030406151e0504020f090a1401090b1201 63
    0x107002403c0c01420212a000903580c00256074480c08024100081589544d43d07681030210006031130084510406405000c003080f064400d41c8400080e11600000c82c031a0180300ca20301c1c0c914a180c01441d401000c40f0809101815010b035441500500031a072095100303a0107a52440c041085074000c610650740c020800704002032810400002030303901c80300700070301140085440d015040d103c4501604001200c5204e04001200d1000001c030b11200241e02845003002d9034001200050140818468240a04140003001e2111405a541e414801c80c403120509000b0040d51a00b4050704802100d50b00400d075103100ca21001500da0050604080b40001c1c028548281c080d0100d40c40d203c820100c501069980c3e180d10002003008000314000c0d402620b002c24418400038440c9003420f60356101281003441d14001e54004040100755004a40302140c0041e02c0780060b00040c3d889200b003404050380300a10541c040354101c2c400b4900407509d0400e1341d42d52480d030303207074bd00100b0644542a500030842240038010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799971393 1250 799970143 799970161
    0x30307120b1206161202040b0a050a0212030a0c091e140a0518070323010b0d090f060903030b04021305091b030c07030215070804200d080904060518 65
    0x15150074201900181c0100d03144400c0c42d0802c40c1c00e032200c1c1c0d00105498280841c00740e022141c004085c1c102c0c54218a0b10f46443d1505006120fa0401c0e0001d006021400b150050300138401c9420f5034482c00702566480c80c1c03000d003d2004142e1900410045894803001040c04004103045003416000e911030001d05030305100202c007541c2c5850301c00c20741c44036a480c0081125241c011710040070351a1a6061420750034020006001d40d141804e0342c60044000010388034619404d0440c00f811070f0b05c3c0c0400d095860300400d00c0d0300c000d000e50202c0a0181c00f451107495042110503440044240d009540803c0086202010032050344100d051900680088a038144071034540500340c40e400004141c08013420345e20b848001f001c680c001b15803055540d00041105030601d138045c00030b030880e05460500301d00c00307150020018016080203080604041c20071050044000c07060000c0200c0a880284090180b695500e40a0601d5000c07540403030049060078800941800d102042c5203c0354003c0140200c569155842 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799972643 1250 799971393 799971401
    0x608060c03040218091e030c06131a0703150308030a0605010810210c0e04030e030a0c09050a2004180b060f0309070f0e041a091207020103020d06090203041403030712 73
    0x6642c0d41c080c0340240b0380c0034641b007940103401c241804095619482540c3c0580d0070010010030001e166503030444034000041e4500882c0d5480c0440c10070031320641e110780300120010021003003081040107225001009001d5408051442000d9200341408815115401101c0340c0384251410038984080b01c0040c0b02c0700384050031b1051800050501c51060800a032130700c04030366040d580f000516140640510042c55445040c0e1200444c3c107500912101901d9a01e4599840d914030500b400743c0d81c4d840205031900c3c010707013003140d02050081d50380e200d04408061440711a842481000b406a813207220342e0380e400100380101450350f4002000107040c011240d0151a0031740c8001e0460300a800f0386c540206030050090401c0340903103507000900480349403614081d60b03035440c110051480c040901c4100121f850001031030f54208480b0380000c648418091006802074014007521040050500c403012600020680c05144030b51b00a540224005040c025800d80702c3c0b10a4501c1e00003d00340c0e01138800c0001c51a00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799973893 1250 799972643 799972651
    0x321020d0e28050102060a090807060c110d0302030105030d11060f061305040c0e0702010b0906010522080a030906140306040506120d020f1018021002030f0a030608060c03040218 78
    0x80b40010480d000c0300c0500811402c035030070322081003a103101800103507810080d0300da01c90140e05041111860035260325400f802981c00061956888814000d0218402d042c12100842124111115244100000382c060f4109000d424040d210f40c0f4100300d25144510b489180058815000e000180c461030210b1010400c001d1070290003040d02551800c0381001f520805104501407050500d00c9410001001d51842014081c041160304090350840c40d40c0e103140c0d0682c0c01200c242001c1e507540c5034588640129503e88401203c440044a800141038000821040c0b2164840c0c0d0310104805d0701c41406444082070b0254075041c9042c2800041d1881c28654401038014400a0418110035103094165190483d4904500700603001060607491200b410044042442c02000c414400710203281c0f00d5003c03a000f0082c01a11440e900c180d5090203d00a10840d800d0720200390030306507510070b6600701030003401c6035100c0c41010340b0a00d40010150100c80050300c2c0034960083c6070007902c4803140f0a038401020090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799975143 1250 799973893 799973899
    0x91e09150420071e0218041703090c2b0c080717070b0a030f0509010b1f05070f1a040f12020d080402040209040b030d1d060301060f0c06060807030c0321020d0e 70
    0xd00b035400542d5800299141b941d031340b0184041c0702e1426150241521114142902003400c0c2401407044802c004a00c5040040054840f2100e10f10804282082051807140030102c0e03030420464a002d1002c03094810f81540e10620441706c19555661400402e8900c1841125840c0c006240a01580b00c80000602c1d40c1002841c0c0030590341060400d001c207c803420703111909176a568080c042c490742801140843e9a4000e140348e6880f46e00e605002808910403000011f00c655900f05820b400c103e154440705005810310b00c5240310b546002d00e03220002c00804281510100c01c10400410040e10000308481c0240c0242e0f9000c401780c40c0d59090101039042529615440740d11841e0a4030140c40070080301640c0300141e540e13540e441072000421100c41e0031310108540928001c00040c41020b8000705018804c0c1c81380d152207400a14a410000028500d94100d03c00b24010290000180900c50b04c540007641c0c0541090101c40804c0c0c0c170187c1c0c4450a40c00c43c0130158202c1e04000c0461340c040c7c0c80d5079210000c00307 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799976393 1250 799975143 799975193
    0xb1f0f08071404090212060d0203060a0c05071a011d0402030705010c052e0b041a0f1309080d1b02060610021015031106040605091e0915042007 63
    0x5034070304410340d401c183c02c900c0c03006174042800501c54000a121503006201500c2210403c82950086a2920001844454000e0700c90070b010540521880444048c1038000d0b003104800d5220342c01c0d00d0001c540a00ca00c12858445804041e49000601d0300c141c091130b0300800809505103440300544c0c0d0012040c0e0140c80c18010042101000180000d000b00c0c00240d9040754a100c900c081080b0381203d10100a040c080e03072400320f00110300d1002200306008190205c0c0c011008400c01c000040c0d01c42c410000080046003414868010007030144080c06c81020302300414001c0c421600c0b40c4001482c04485c4020040c0e01000c0481e031103050010700d038804900c3c1441641d2003903160810103402d0340e10582c0c1211408046285c20014800c00b101c5030306404900f11015482c280ca03028005245026410269100f034031138030b044041441d00c00d980d0082214028000c0c406074940203020203142d0071691040c7d802241401001c208040c01001882e4140c222143c00c2428940c59480e0b08420302c0300d51410040700c1c0e842d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799977643 1250 799976393 799976417
    0x9010819150504050d081f091a06120a11091c11120604020a060201150b090a030c141e010c030513030b0f090708010b0607031b0b0a0b1f0f0807 63
    0x209000740c2e4422809400217110100381c80c0d80041184000404c110700c24905003401c81c21144404244d482120501030380418001e0780c43c6031503c0000b00d200117080d800000090724058980c2d00480c5140704440b0540704105100030500514030500c100140240d21544501c113202c41070311490710f0202203a00452180140402a03000315074021048054450998820030400c81145006246140901000d03c002e20621502085c0c43c1d4540200d4080c828801002290b051240e8441c4440c5000550308500b90007070301551119000854a00207030440e000c1c4240040180c03400e400000030480502d03040c1d4070082c2602d8152001c686a070804051440c81d03c404d01c0000000c6001e12011314020400740030710703507004e043c020f4060789410310710380c088141c0c2e90600c0c165000981d01c1e0010785000c6a05410019802c004415030782c220f00060311030003400089c4041c24007808201742d41c030500c8a0030307090358280c1072400c1c01910780c143c00c2110740030200000c003001b442e01c484031300c10021030b50800c940f420a40d43d141d007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799978893 1250 799977643 799977683
    0x20309073b2809020f040204050114071716050c0a0b031513020c031902010e030412140d11070605160609021f120b0907140906040305240609010819 65
    0x211508090000c0b0340c4480716002945851102000d01401c00c84046280900d410006064215503000c2d0400c40b15003c69141c041c401e25107031002d010b01da03488850f48d4030103d00c07202c2045612504020b541c0340c8a000c0d21a00740f801c2c8100d0920a454510780300078107681e01c1ca903140034170001c2030609542001440c02807201c0c001c034a00149c03484102400196445200303082030410385010402c031080441e07040c240400f645070302c04004c803800d850b40200c6d480c51843c1c00b410b100c03802400b007451980040c451903922a00169019510b4a45444028195544280d072400b0840d0b140c001d001100015960361250040000c09a51002e00c4039071014001ca00901e20b8800429030440341807400c000810388030a45140d49484510900c15000c004450000160504d0b5070001c00041d4241250210520001503940a0b60ba0340c0059400031030740303e022600405500c0440390480307500c4602c2550110240c1c03000c50214902850800e0680d200c440060200c244c00c6003613441500305045054034000d03105001e1040f420 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799980143 1250 799978893 799978951
    0x4030f1d040f1d060103031701230402040302180a050a2a020705060703030b10080103051e07080724020604030c060c1403010321020309031908090301020309073b 71
    0x10025030003600c020741c51410090103140401d22521200c0d8441c100600c5000c00c1c0100ea07055a00c101041c032b10034003a2040c0403500921458102950240d02400420900b440144525200b19003c0005102503102d0a00340025204002c0300c080c407401d07103450400c0d20300b02d48a520384009041441110121543c82c40856199403100c04140d000946900040415082515003100f08698900d0074150640c51900c1d81500d81d07024010280b0343e09854840c680b00344904212502c0030701000000e45190660751004503d400e420bd10020420000da00c40b960315990001c58000d01c21074260311102140d1840f540c401c0010034803010180e040c400f5a040c188107800d0000061030196214a0210b84070300704d00e8480340e00030b14040c0301400441d4000c0240e820151000724840c854040c0f41c0e507100c0309810705854500114000c2c0c40c1010341661000c070821078051400900e150840d6440103c1820403040c200904a140c811284042100041c42d02c003880c070301201300c0107103034441091002070101d2804889502109 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799981393 1250 799980143 799980191
    0x201210c05042d03111503090a1b030b1b0c07060c0b1b090d03050706090308060a0b0a0903140a0f060c0f0318020906030a06090b04030f1d040f 63
    0x81c0041410700c19290480495107031a442d001c0900070b40211401e180100c4491400000c000208034080544161500104810140600400b158803441c05c90307041e075034030341034060240c81290555a05508070608114440c050f02d40281101120355035a03200c540384240c49030b44031070050104028404041c003050040030007420a5a407000103034146820091003038031019003d1848042203290902c1702010500c200e41d2901001d40d800048880907080c159018014500090055420000d450003016401030356180708801c121140e08940c0d03100c0b8500480c50140803500b1011900b10b5100b44045050690f0420310704a1290840f101d1001d1540c0d11055a00c10980c11a0305640301c3c3d41c00250340303400085100c800340d12454100203208650b84803918124440c94080e0182c66502c01040550701c09001c1b06d16401e03002007041c0420100380c80d01202e0385004031029030000d07449210040310700344500b2a001007505e0201000903c40321060402c401004900c00e00f280300d6a613000407042c8441c0040644041e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799982643 1250 799981393 799981397
    0xb03011509170d17070806010f120203010308070605091920030f010501060f020a020a0e060117040b010602070b031e3d0b0f0a0507030513030b150102190201210c 71
    0x12007021024040c00700006084d40031510004081001302a960110032541d12076400d00e82042c51030482001a2614000304442740d804500000c0044103024411004090a0703114100030003d6a8a4003441038450a00900b0511600903124910002c0741100e0b0414680f40ea60811040c04003c4900000c0d1800d00850700841459455800400c00d45411403000034032095540040c003083d807004e40c002050800180144540098400049411648103242e40f9140c0800e86c0450800d9042600b42024a01000d22881c1e0040c807500b007010031690705e51410342e400340c0101101249004e03940d0000e2a004040246810000b600724001044200e641c1c2000f000104941e40b0250444418207811004003c0e10303030030010214504110203080d0b11503150480303060303800500c0c02c82c0c1c0304da0103450704564512074010084900f1540c02c00c00b1003401002018a0301981160500a48103841c0c05d005a80762030418401d02062450b0b0558034000d940982e8800001c02200c28503c12141c001c044190200d8803c4104980 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799983893 1250 799982643 799982653
    0x3030b0402121503061b07082101120b0a060e0c0c0f060705090901120206040608090304050d06050105100804240f060608040c060206101503021c23010b0301150917 72
    0x1800c081c130006400286c001500d40030303034007000381c64203640c45403010090a0800c00207035950a803078038005d14030911100b82227054080d6500c40e1210409640803405031200030340e0001041c1d105172240714030300448500c0444a1155034603840c6100140d00030140b400ca40303003d0380140d910100024000a4410f0b40243c07101610b400103101030001c0c11a058001240707070010a039240026a0315002a1412210949020182c559134070400d50b0a6004030f50042e0340044140b00c103c803c019040c0c0009050310002d685600c5900000c507400c40d2443d10586001d01000b0345208000c0c0350340c0400d24011070741c00380d960000c201850447c141d04111400ca80c44080080c02500601c001c11803100d40140040420344000c0600b81022961001d01201912034032040100880400c1c0300e00c1e0003601503512905603110603040b034809600110f8080d00300310003041c211034003040c0a000d2100e400c82145041c0c0700c1c106011411a800c10075212400c9102041c1e801c00d0001000340060320702c0d4031454040b01c041c0200082c00d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799985143 1250 799983893 799983931
    0x14070305160b09100b1305041410050703050a0207030906032408030a0206091501060c0f060f0b09160509090402010c0c09020403021305040b0402011413230301140403030b040212 78
    0x5410b010740300800404550801145c00e2882c1e4039070500704000306c2e40319000150b944a5203000c078840e08020061211600998030101110001540124460202c03a20140030540e101a4010100c0c030502400401088105006000c0303684280e02003100aca81e603480101c2080c2001c0c00c1400301191681c0101c03140e034030020795845c02c0c1d94103001180e0400c5800740100f02421030203e030700026540c140900c60030040090f007007000b400300102c0806540c52b04040c2c20040100c940303100c400a0001030140301d0054200e0700200354107050900982d9070210880c0e5440e81040002010441c0d02403001d041a4100701c001c8080c040841d01c040f018000801d00b45600690707880c41c61050010503803a45134000103180c540020800852410070000b9442b56091910040c240880301c1030040500038210103c81d600c0d10384c0307070105042c40454015070742c840c040d0810900310314410040500b83c070300c1c5591815441c03413500040340c0024000d4120309100d240042c00542130003a02c00b03c18124070011a0503840b11403010b0003070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799986393 1250 799985143 799985161
    0x90213090c0507020105032a0a02060702070605031905100902040b0304031205010302211024080a1e06110706021b01090206160602090306090d021c14070305160b 71
    0x1d480a181ca03007019030a1003110340010300349000087c289202c0e6030401000060b80c211107070700e80c4214601c0c0060743e902d072807964000a5455504481e51405845240f80c0461f54078010030039a482403030701c180c1c1e0881c11a0342514200c003601019100040c20443c103d17003c2040104c50000e400030b48400b400280c0c6a00d001d00b03000f0611200b0a10845880c0d2514005101684614010500c0c5944000d204003001e0210011585020101020280218a0521944c1d4010741d080e80b40320b500c800c0d00072082c0426840d400c078140c44004088004008181c0d140340f02c0381d01108101c0191002d4003810000030002c0e100882150198000e0310200c03032180e03000440300400042d8507401c0c0700f041d85403002088800c2299012800380c1c8a5200d141110000c54142d0703108001d100d030100d54000202400f681c0032418490041a6218082a403e901602403031801c4194110121240c0400b074416030b8a1340155034412407113846940c0320312802c0e0300300038007081598108a040c14004010a11480c01200c0300e140c10010303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799987643 1250 799986393 799986401
    0x2070509010b120a0203090c01050c1005010305010623060904230f24010804110d1707060506091b0901120507020c01031a030615040608100203100608040b0f070909021309 75
    0x10b13a401c2c0510520070b2100b07100c030000c3c4501d0703c0d000a00741140d40c2c1e0b40c4110b4440c03805100d5414032002a003008008003c002043d0803100894950b021700c105039045480c0f4801800d801005160741081003408843c980d860282c02142c0c1420841c1c96401c078142940749004945c801c00c540909540c0315441c1405a00740508500d8610994400310040e00a2490350000381024070190000d0b1200700c0b0307410110404d61b100703001c20500d141d00601d040d00818a840300c106441e0405030055814928100000f1a241051a0b59034813410503070844403038189030324102e07212941100e1000e1381000400c071507031600140c2c103204440c011510381d0014580d46210324001429102e081c0210784182d9050aa0a2002e84000499940000541030000070340c10001c00428010103140c0d00c1100c1a00c955001c80c06000c0d000d030b00031400b401403440343c1c0e00d2840d200c0f0015100c0da10159402441c0c4044030380024406840b50081d1508108030f403034107101c1150b5810200d802e13600484007400c01040110b50801404690f031003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799988893 1250 799987643 799987651
    0x314131a1305070b030606031603020c0a030c050c0d02060a113903010606171f1814130b070c0209011409010911031b0706020f09030c0306220302070509010b12 70
    0x131009143d454108003003010b90001501ea03a1209550304c000320382082c029015100c9280d4a60112008810242130041c544804807000b6141c602a006a03030856040c040e0300e42003429000303000e8528068840c42c0407201c0c0c2d140541d820640f401900412511041e160803940080e0600c280c00c3c2094144c2e0940c1d0b03446410081e0040d6219030724002e8104849a00a0a07400b0fa580d50030140340695030380e5400e00c2c2481000030b2480500f1081d040c0c2c000c80c110440c074086684609804400300300091200c102c11444440c00d031400c2411a40c82c19020001852450440d64000501d1a20f104050259800f152000c402030b00a00c035050000b2074800d003c2d0900000860040007001020301020a1a10716590f4170310000d0302c4e041c444009007054005e0204410100c0c2c0c105640840c04543d5010360002c00d0140f50490915a0322a0099060807080382c03400064450003080200303e590b184a206001c40c5c0724040f018a0110258020b49100003015640e0318211402002c03c40d035800e41d100031000f801c218000d4020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799990143 1250 799988893 799988909
    0x60314010e011a040b01050403050105071e0e01050d0504150e07080c03060103020d080912070f090b0117071b05010e012301030b070309060b13060806070314131a130507 74
    0x400f61040001c001c1070020390440c003034400141d02003c001c0100c07900d102e2a08003401270b40c205028010f030750381d022100e401d811425a5808200c410140740c00c0314024402c150b11800980c00384035800070315050780d201c180c01a200f010710401400880002c402614481401d1200d6600070013070030000c0030342c240150b00083d1412400b42000f5070440d400030721400141e403006040d1030070204042c3c0080d120b0380c5001522050400072141c041d0b41c0c0380c15a10600302540203080c120b50400c60080440d501914410000c030741c405208131a1540c030420110741650002c9103c04002c0d28220340e15001c900700703100d00d5100f20000d40000c0341051003001516800305400a0703c400d03003100d10300100085603074011901c2e000105440c01045030034a5040400c00b07002080103040d4000300392081d4010a0140e076005e001203924403000d41d01c680d594140300350115800307403009001986443d800900403084804003103d40c00d110341110310044000c8036070080c61500c11614034036580c070300d02d06440500100700006d0700107220392 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799991393 1250 799990143 799990151
    0x180c06111002030c1c0501031a09030a080901061d0f060303040302010c0321050702030702180c0708130305030708120a1107060903033b060615030712060314010e01 72
    0x15004003a52549008030141c40c0c60b90200c046074605404800312424207840848040c280c80c0003a08860003407100f88000c03210419070103200c508650040c05071074401c010300f40186040007120441551181030060515005560300e80001c10300c8800701d1282e00441440410f05082454161403009030600064401c5101e5401070000b000181e07807118241888a03418030300550341d00303248008201c09164004603244c41504007010080b5007503001024001c2d09000300d8051190b107100303100e2900700e03800c03e44410940074020002c40020452040080076020741d090303c131200c929500e4950b1411604030003004c58031154005000752000390001e68850f000300c030518007048010900b408002e00307032144800040c056503c2c1c249010a2500a601201198800c840844005204102c144c402c1012944032200c1c0210003903110b012420000600501c070308405451054071084c00c100400d01a0802030144c01080404407410b4108040e81c09014001d62184402209800d5030711a02402c0d6410008240c107142c0c54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799992643 1250 799991393 799991417
    0xe0901080c0307180603061118010e100c1b0807260618010920030d0c020f1203041e1d19182009060d0b0f06010c06180c06 54
    0x10126440049501600e04c40c220b0b0507100a0190103480d50781d0000d00341742c4c0350000101032410000018107003601c0e445503040c180001400151043c0140440b030075040b512002e01100c09a02510307264940764000c09081940f04004013100b20911480d40047c00d4607000110b042008620b185030725810704082d19145450000700710b62443c2d5400c0000c1c8100030702c44501c101901c41d11001c2d4401038580d0b80100138020310711340305800c1c2d40c0484480d04440d8001e2103210800308019200310f41601c000d40d030050400c0c101d00119001c20110b550255421200d07400704200000c2c0e0041103800e03414400c5030107043d1b406113601c1c28180c03d9046803403100e203242660080d000c00400c11402d01c26500d440782c1180c0002000070140c0c0c403100c04d591000800810a903801c9080c0d0555840b45c11100300441c00844c0c100d0340d41d81d600001e0040602151500603d003c64100205032800100b01c85540d01450607d002c0c01d00c00501c0d00d90f502a5840c1940c4c0800350001045c00c0004d104104d02c003400604203606000020340b030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799993893 1250 799992643 799992649
    0x501063f410f1b120f090c0d0f020f0d0309060914010203090d08090604030b0612030a0507031211120406050a15050d0521120703110304032006070e0901080c 69
    0x10006003825540000302002510442190400c011400c8403410340d541c4400c204c010a684405098844404114680c0000b80c808540000c0d0300070000005060700a40045a5851042c031400a0a00300e81c8031060512802c0303d074542079a54900030f4040c1d0303104240d080ca040005410150290422203c80c400070320300c6c8076166000403c80d4005a416540e400b0314044604202005004003012240d01590009000050015180ba014041c00e02152020500c0600d03210903952413003010640808128103101c0c11010901030b07107400f8203034001c003140070071108040c68501015510100b1104040c05034103080c0418401c1510a266000600003c1000000d01c2c039100040c50340c0301c82c4101ea1052390601006c5082007010300c02039216080d43d001d901a200e00000302c84d085a04024607940003010800009244103100c2c0c010244500c1c1c1413400030345581c40c2d645048600d5551407080b2006902c4104a844e498223042040620a4030a0754505958034076510800003c0c0c40183d000222a91103000700315500e903 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799995143 1250 799993893 799994021
    0x60b0315180709020418060b160f0f170304120801050a1707051003020a14070b04150207211704050601090c11030a120501063f 56
    0x10080801407074940c0c80c0c5004146810340a40001600c540003080000b440901503558101c50f4031107031414419a0380f64201c0c103032540502d003000100700c0010403e420206040f0802c0345502401010707080f2484407580c413001c40c0c00321401800c0350103040010800090001c403d8001300c5051203403038603051a500d0007001840704001070141503910074024681c4400f43e101042500010140601040d03000c22400d20050000d4120b0744200d07020179002c0031001d40aa40d0a41180c0da01c540c42070020351142c9030358564115a6424030510b035101c560820201e804149090035668001c030142100b0078a868181500070002d00611944e805c01c0c0342c29009000000c2d20100e501c41c19504d041000080e94444400100c038003890010760780000780000034200310203940c401220080340102101c2404603036a0780c0c0048a4507000490300309400f82c0d4008900754445900007400e0030309045010300411b90800360700384a040b20302020301c1c035045040d0381034441400d001040c0d43c24044803a00f001c01c50020201e1024030050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799996393 1250 799995143 799995151
    0x6040b0d03030b0d05011806140c03070315030f060608010b0402090d06240e040b01050d030203160c050a0f140d0305181309060b150a020a060f090210020a060b0315 72
    0x1242c0c41e803c416445803a480510308425812000a02c20003000c2c161407181ca4143e041c003540d2950a100889001380111a01c4d81d005201c2145018510741c0c41e490228000d040c1d04d4103245002c0e4901200001040040e40711560050080600103005480c02c5074460031150b0859a0761301581c018011003a250381c030020440740c1d55810a0340451800c1d03c0520400c4608100201e0505918002801044507a09020034a10842c0305000c1103e007640c842c020000d19003c07003040280144d00400c225814106080d01510740c1078070644c00403110030f45070b100052000903140c1040c40c0032851840c04005106900410b418000c00c190791445900341c441c1c80040052061461002c3c040021011501181e2103040700c40c0490303095900104030080301481c0c650054002041c400340315804007030500b800e034043e100c11581c02008030740044c00c0100c415500d40c4c0140a10044081d840ca9a03104a80c0150b00c540051031400b0010390f014010001c03a07480d0180898900540d5180664040041159030400310b080035900 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799997643 1250 799996393 799996397
    0xb04080327060a05091503040b09071e0510120f02071b03031719110315010216090e0c030d0c03020607050423130e061801090c0920030108100506040b0d03 68
    0x6035000c0e85003c0342801c00f081d09091b9020708000708100501c6000041c03a8050845103013038034042aa26840d0b8401c00d1005041102c0c01d1500120030845841c00264207001c004c2241032044400c00841d4030a42100e890030000350100360002110380803c01c01d42e1442600c8032016410300502811038034010101134451588103c0c02080705c012034801101c5c0d0100c4e0a1702c0010400911070100160007020080d0400d032001c0d80c1a401c0c48200d41d003698000321700c80c50940303041340e80c000249203812140d002410151518480758094021001000d450038403072040b02c0020f584511184410a180007480c2400040209003041014003051101c9136580c422a40245050040d80d81c40d0010080040c0d4042d02094041c60014613000080507001c02c0400d1062090400041e41d200c001d200691a81c01d03075003c40d400410311425650184543d0a003903020051640d042d28003080742d03411044403005540d0082c0c014603c5036000c4505000b600d14503002d070f00e91184054070207008003850000840c960007c0c00e4030042c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799998893 1250 799997643 799997647
    0x6050406020d2a02180a02040f0503150705030a0b15070c060503040804030b0403051b0f01180c033206102102040519020a0c1406042303040b04080327060a05 69
    0x82517645400c801a4200c007106907014090415003101002540304c0d01c84d8144070380010300c0c0060503281c0812080f070368038502d601c442e03205e43d1451011500c40d44002c1035001010381d82c225054050b1100f440e408900c0d4405400711f0703600d04090408145100307484e0b102a040110810411002414030429542184d910007014031032511140703070031b5070140038001c0e8034449911401e810741c1200d600081c5a0780c0c0714417900001c0204079103a000c4041c003508444006000300060040800c00a0300c68102181080404002c507050a201c00042810101d50045000c03e1540070344c0034007901c1260035600400038120103c034404080c80744e4415400b40441c40750043c1c8074681c2d410001d0f203822800c10144811000d1041c3c115940d00031280c0180c50410010070075261282c1c02c0710f01c0290114006505800b55401944030104088000b203029203a100031800020640014800010038030800406003024000381d0029603260450851641c80c10801d4642103445400144042031550700e541c8220341d52000d407450015 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 800000000 1107 799998893 799998977
    0xb060108060609090406020f0a020a030215011203050a031d1510080601030b040501020705101b022e0209090403031d03040f090f1506050406020d 64
    0x86402c52000c10040300e441c9070a8200c2030303101c0e03c586400340c90706540301c415007841e070400a80c0501603400f9041c070740101078060054418811039419000c100390300d008006180038140810107010300500103000700c00c80744030f90040307c2450310844448a00603120500346903101c01d0328030812001c1a076103000c6820860080e4501c01101c880d40000d108690035515004080340028104584641d03081140300f0005a0602000c12081554100028003000e0043d10302900c00c82c0c1124802150005030000018540614143d0407013a45e100ca003403603103042504007000904c0340c40b0450394051074160030001055459003040c44081c035100c000c0b0009030081501a60f0301d00030b501401403200c650090038455107881d40d01213081d00328990720100d480303500141801c1e220803480d044a80041c40005040c00a250100f00c01078150384540303066440405036101540101c0041c016071120042d141b0560 = true := by decide +kernel

theorem cover : BRFrame.Cov 799820143 800000000 := by
  have h0 := BRFrame.cov_init 799820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 799820143 ≤ n) (h2 : n < 800000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
