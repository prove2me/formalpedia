-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4565
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:01:46.629025+00:00
-- url     : https://prove2.me/submissions/b952c987-aea6-4474-a1c0-9fba3fcd2d36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 820863309 ≤ n < 821043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 820864559 1250 820863309 820863313
    0x7200105040f1b03030e060304021c0c050a0b09010203070201030b06090a06050919060c0b0603150108010906050603070503070902030408040f03050a1707020a090911031606030b10020606060a1b06020a0f02 90
    0x2d0304e1a02c0c0145480314050440e40301d0400080800c055640350040381140351601d00c102c024852051403d500101c6807445110b008038039602c00018200c4100003500c10012040c0c010b18940041640110010100a5222580202d0901488e5201e464400c04007000e001541c40d6255294026000c212a44642000204c40c0881a0b1002e100f0146d20111303201c1c1440d0302060701c00140d01c510000074240a440e01505e41c40d2070811000050801c0d0540055045601401c03082003a52206810716845101e640035550305684000070800071042c80b81d005503032243c051455141415250540406800da05520940342079008200718010301102c500740500620441e11682e2500d080d43c2e000c50341869031407180016030365840c2d241c4000d200f04150b003080403d000400b602c0d120f001101e160100c001c803a004010020b4500ba015076941d01f450521888a00256001030059a4504040220315840074100c3e07420031070381500e0104802c660b91003400c20903214500158640c11341181c01041d0100c4014524119 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 820865809 1250 820864559 820864613
    0x41e14122106030a0f06022704050702151305030d0203041212140a09060b12010f0b01080c030c03070909060e0a0c05071a15190509010f0e07200105040f 67
    0x40d5400150030b8132080e512842100780ba28990034403c00a0260000034503001142c0b52003a44d1001400f03502460f8500c007194104816101c002c2d040384d07101e04201040f402d00281c00d0200f00c4401000342c1e0350315254031400c1200e207084040762011085c0e80054034100c41e040644400529019089524440101c20b400380c01c00040c1c3c5c503408040040003000e0300c1c040409994a85c0c001c103000c01e582040d03055040c0503110b0b000d00300004001c2402841403d240d4405c0c0361800126400c80e6103d0801140113038840015a030854a03100087c00c02e0b1b50001d01804144005820005a2290203020b01c0005117903d10070102c0300d14090f00c4204c10f40e0801954003040202c01c100d03050000380c020089001540780300200d150300d5036800102c5441c000300401500d034010380700740426507200d01d100d40f4501035820560b4280680d0740d0b92200f207c801c0ea007030b002c1c84130b20340c1c400030000d1a003603c02c0340514865441c11401c40d207a8801880d4242c2160002c0d10300b5241e00030202455404d01142c03903400e5070303528420000302204e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 820867059 1250 820865809 820865821
    0x213080c1807120b01030902031902040f020406020a060218092d27010b0414160216060c030c06022101150f03150f080d02010c08041e141221 62
    0x10402c5200c02010000c4d5403620b40300c0310b03a4440c0d40400d05003a405401c0326129030750a402400c0080c84110304070b00c01e50504003a518907043c240240e0701120980c1d0010302c9810310941e00c00c0c0281d044211040b0042c42e02111002d0565205165a0f000e9540200d0452050103025110b44000c020044c2d00c2c8001740e131823028080c0c0c01036008020782c84049020750b4044080c1c4c120103814050903104e00d0b101d0344282401d50404498507450880c6004002c1c2041e05036180d4404801a41c5815003400079041000550504202c05070040041c621040d1191038051000c141d180d4440c4201c0c0c10211180301c0b03280e2041c070030b5120300c9079191030340d809809150108420100081d10092441813803100c440b0805444004501e4070840300c80f641e00241080240e00450142c41c2d1010a540752648207440c0c0040d03081c04c4020b03032414000c0d50f03128003403500300c4104041d0089080020700c401c0340e001c0c401ca44c40203000d600743c42c1d210024030403080000c15000002d40d41d211311545040c00f0300040e840d0580c00003d04814440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 820868309 1250 820867059 820867067
    0x18030c090402120f01051608090c0a1710140a20030a0e0f24010f0f0509130c0e07020d172a0a050403171911010213080c1807 55
    0x10340190304483e03225610480d503040a060500e1400c41803000e600302400d00440079400392072480b01c4502940c60070280d607a0b050803550340f40c15100c02075401c0405800709121429400040034900301040c0116150083c1c0000150122044542310a550a0600c414410f4040b4140144120b4203041c2480c86140301c10030070040345510001e85800201c5a6411040101a000307101440907003244000b542d04a04c6550181078440c540030300044054082c0500200c0e44032100110482a00c00c45040c007076840e420300091004404024124103502c00ea1010740b64001024a81d86002401c52080310b11031509113000b0103450010304080800904c406580c5070030100070904141640440304101028407044003800703e078100c172508142240321001c0056000107280d0820010401c680c400d411140c03040d040310322160458001c1c1490444c44c041d20310b100c0c0c00614810400c40419080c0791000500d07002044603075140900465004040c00d400c41d0300311806c585050035086105c0340322101c2116191400b120028 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 820869559 1250 820868309 820868311
    0x9050a020a021b0a0302030601031a24011412040f030305070c0209040f0f02030f0303072607120605040612050f0708060127051510050412020d0f1718030c09 69
    0x71030300d200c4040c2000b040c1c4e132030001d003000a68016083c0c84655849003404040c1c0422800b11004080071000440c1c5000c2360404042855018401801114100310004517140d407200000c440020034244000d1141d03020b8404c503136025a01c80d002c03402da040070318580503041d11802441141030004641c480400760700c60892a550195100360401d880c0c24131803901c1c585408040001a4143c0700f440e440750300803500000250300540b525100c05003c50038660145000c4076043e8044a01c04450001154440340501a03849100f41515000300b072803612800402d040392003aa1140d0340c8400b140e007440c0b081c001c0a00001d030080940340040c1c21070a0425111940d41c40041c86030300b20681e0804104a218402044503507064079105030103001a0134030300c00c6841241106040e81f485004200c0c0f092481e10300860840b012244032000d0400e002c40c09408015214010710010b0701c8032441406d6110001d000240114114040104010380b11a00103000d0442ca0500c03460042c040d6001980016041c2e441e81c0c056 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 820870809 1250 820869559 820869583
    0xf020a0e040e0f0613050708120708030a0f020c0102090f18160c0b13151a0114071e03180e0406020d0935030105090106031508150109050a020a02 64
    0x800d150741e400460a207040150540f11403d402a071301440000c0500c0d034502c0000600510840d00c4080e280d814030b5480d0000c0d5800d40701d840348200592000039500d400038544c014010500080c4105081d0080002d03079100642001180e51b000510807080d2a041c0c011040090054403516201000d00c5c0d01000c05010240a800c01007150324804080180300d1041402004e0740a5002505824145a8140c10360300340c210455440748a510441428074052040800b0b814807140300d2103000004030010b407221441203c003d224004108170040109003c6a0743d10200c002000700401200410700f402000f43d00345681511150310a13880030400b0b40350080110b60055080b8600507582c1c110182500000c0c4010718000303025980390741c454035215040941500ca41c0143c00c0d115003200a40d8012540c0c540702c24080c003540170300040014814079109600c818524065100c0c114b0703541e6220001140342070814900807251507007480051082040c1400390903000b282442d010350070722000e0f0002075140d030024041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 820872059 1250 820870809 820870811
    0x7120c0306150c051f0209100c05100c11070f0f061d060901200705132a2606030115080c0904061b030509010501060e03070b0a14030a0f0f020a0e04 65
    0x200802c0c8403090217100440d403140d0598046124580c02c190000c2d42021390350900c01d40d15140e1a110b0706010385030f01c0c1e5859a02001030907085d08030801d40c04c01041c400004138100700329010041d12040303003084500041d00300c00040c94403282c40c008080070803040d113070070020822600f22004068503c602030346218180c3c0071107100f5101c0d448000102e031040c42ea203201d407400340d400c200d038117500c2070021411005881c070640b1240468101c030707900c150a4030a106120110009038091950442c0313080e110762001600180b9205411050300c003a07044102c0d0041c010740e640380d2440c9003405151b03d024460320b4403c2c000b000700141058a4001010744070600404403500070020f00e4001070030031800c0da11901c264482040d18041c10703124400010700424086506c0c255039860400089080360069070700d6044020010001c181081c1021503400b5183c1250794181c1c00c0c03041040c2e49440003e1014055881100d01110008003800ca1011110542d402002f8107456103104010340c2013803d40c000d1002944910549c9c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 820873309 1250 820872059 820872077
    0x2003041101032910030e0307020906040b100807080106020d0905010c02010e031914071a07080d0606050c0610210804030501060b070b10150e030c0907120c030615 71
    0x4016400303403802c15a81840100c12058581141480f2024140300210640d002c07280500300107400e5003120300070084d0a0706503009010340001480c0080384168800703000343c0046400f145000220702120401020030020400030380401001580c40003105005040601c000c200300c40c205c1c200134141c51218001c0c641003102100326907040da400b4205070002410301030110b400107001c0d40404403c186442d00c084402c49442d40750301c01403450000e10f0b10140e0340a4412103288003082c03610048c0a07840000f080319a26414801c50003105180d1048000800060716000e5070381d082181c030300d8200b40c00241640e00382003201409000009020141f514403d034501c24000341d074040e6050281060195500003492982800000b041006030034028040d01c5120351152661511100c201e03d4001065000302c0600c05440c4101c2102680f00b10008410b950000e000e07a4940c402c05008108030b03a0040700c0303880214034120089605503c10340700d529078003031b502d103002c1000d6810a1900d498110803407000000b0050007403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 820874559 1250 820873309 820873343
    0x30c1101050909070203030601090815130c031703041a27100218010f020a05030d090c05120f0736060b070c03020a0509011d090c100e04200304 63
    0x14040324040000200310f0020351504110003940d83d4030840300c80f8000303040c41d000040c807018005841d01c6848000950854250399030000440140c072600c02c203423510031101e9000030124407102c20b08a140620b15616554903d402e0a00710f4046903a081000c1c0402c0503071003007090030301ca960420110300500d00c400081000c01a003101d4601409420151012840083c3e4403070b81c00001142c1c4206054281c13a0130450030034103030341661607410418003d809038004108400c4140d1075548046500351044141c0685c4a441e04007060040031694010f42460344a0a419452500e0401080000b0020b403819000f046c000b8410000b13000b08910031b0071424141d01e40c40507911407107641094002c0d0000c002503070b03160034140c204003a050700d4901c41030740221030701840401d41c0c0c01c1501e00141078400c28030002228000c280e064103c0c03114010150401c500030b10300a00c243ea0340b0707070703c00c265214231039601d07131200c0c0c0c030703070303200b000200d8184c0405203d14141040380e400d840e82e04038003580e03131007508880b4445140900f0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 820875809 1250 820874559 820874567
    0x7081909050f16170a1a0402210c01030605030d020c190306050906071101050f012d060c061a2d09010608160207030201020c060a030908072d030c1101 66
    0xb01078a840b14042e4512841800e0f42c016151021150301c0319492240049003004503485407541e80740a1302d0074598150704051159030890075034000d0320280c201041040c80404a000421038441c071450b507a00440081034066034180588800f400d42100580000740c42e1180c0a5034802070800c5050244a0115602d0010898000c0c900010340d0031180a0223a4030f01400c9030703501c070b0710300301d4102c0e01192103401241401401441641c0c4580d51380500c8100590a11003108071041001600d80c0c645070001c0c200340802e804a081c9040140100d0300c600c0d803009414a024020344513650f01e2045580304520041c0300a50f120800381c2e0001a844620035a103090240403091440380b5020519040220700c0f00004210754010b008034410501041c2820801721840c100b248c0b900114800a8010303403110f83c803070f2039030b19000004000c0103115090003d515081a5260700068106400c01d90b0480c40314030380d0009480000003445024034524400255410072950058064a0210009000c2c020150003100075a402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 820877059 1250 820875809 820875823
    0x60d060902030601060e1201020c070620160f06020c13020705030c01181202061e09100504120206070216030f0f05100905070f050901170a0812010501080708190905 72
    0x10b0305a541641c1c460304041c224040514610b401080c0b0400248001c00c1c06200fa500080030304401391408520749034088070010b10213804010486210480d01c00080000c20010140d00e404508020201e46483d00038003500031294052000d54220b400c1c1c5c1003081d5500101443d20303107024100180c45401c10b0030414910f002c0c03940c0d004000d41c0780480011030340030400403480c0514450300034802600d0007440b080343c8510301901c4850a0b610541052584081039400c041c0d4084c0c680021180302c1001840c440065400030f82e816280c0082074a41c1200c1260f06000ca25401410703400200004d09034000200082800c901c0003909501072115030310108200000d05042e100d400004031002002501100c00081403500070441e00c1e032080c0080020314194101c003100031910000c281910b02c0c1e280a0b42441c011080350004c00d01d5000e07801c60f180003e90384a02414050303610b0903402c0900c0d810140094203040020340b4440500c00c001c1e0403c11183c5002011110003e82076802258041c20b0389006480c000d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 820878309 1250 820877059 820877063
    0xb07030c02150d1802010e10030e12040512060f0a0c09050406061214070c0209040f020a0e0103110d02060a031a0402030c0705060a05100302190504051503061e060d0609 74
    0x1038050b071001003a0580101900d00da4115860410207000c802100400e0419404002800705026986405032882e0980422070f0207011401c0200714500e0324a04a8140700c0807115404524002140901c6541442c0c1a040a640005001010b890070f0181c80801000b60007414041c180740c079940804062407045c1c01e01c13002410068014040244c503600041c1c10414111342c007503026464501d5281001ca841040c0c0c50250f09070f07481c2d0b401d6441031602803007001e0200410a4a511000c0e4042c00010780b580400a80100451141110345504514101c1440300840010901c1006403051321005030781d5140440381c0f103890a04002030f08084130744034066030a00040c0c81300d521500c04810001c007050400001e026007481f070025175504d44c1c3c0fa00c1b0007004450060b00c4481d00071540700c03402e00042c20310450549494a1130b0b42e6200c0d4440c2e031040041c050b00c10440d007003e000740c8407100c1e50b145820100210350700074140362035241407100e042000d100e60180040500e4031841100d49058203114150380211700c221303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 820879559 1250 820878309 820878319
    0x519170c100f0207020315041e08091206090d021203010b070614090c03071208090f031203090106051017070f0504090603050105102403020304060b03060a0c091d010b07030c02 77
    0x903024103405070084d00003040c264040c3c00b03100b503121201240500c40d41d21490340300180c1001d0f8070710185440b44a4480c02300445008104001442a5a41e540c80104d054904500107003035902c0c00c3c084090424100e607404805642c804800e60304864580b2090303030b0548009031102034881d8140c0c03c00300c003e00940d0150041d4a21108103000c0049004907100103604002e80c22648115030300d131700b0300e0340784001142e020348002424065010030b1301e0020352808880c0001002c1f036522840f8582c14451981c0140c444e0361480c0c2d52a403081200341040c034034054200002e41810742c0c141c9001001041e424200625040411003400211141c01e0f001e030080d240030300466002000300c543c481c60150300820b019541202105100301c40011004850051a100f20f4030301c1d920041200c10b6110150041d41000d04210341da5074440200641c691401c0103c94414a4011400314071031412070fa0140c00c4034495000300d0b80882142e58644205842c0140403811a040c0c046096501c4125080882e05111002d000940c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 820880809 1250 820879559 820879571
    0x110f060a0c0909150608010f0e13030203120a0b041a0619021e010510090903050a05160f0f020a0b0901020a0f020f0a03151802090402060d09021207030519170c10 71
    0x8004241d03844181c1d09607440306c15960b600e4801506045145120f002001c035035000028110306100c400600103244a80102da003410440d00442900e0002110800001a40c80e480500240b42038042c2080980c10460001002080c060114000f841400c02083c16402010300d41c1003400c1c030800c00da24410f508810780000c182c241c1505580070300001d0707030940b407004100400410355051030b00c140c040203503254590394130740344041e5000ea6258100c0b500d816a02d003503152503400410304901c90380001c544035070026044410301e0301c10819002015000310260030310502030b0700440e9800041020782142c00480c0d02c0d41004041c03001800c002c01c550a00c40d0031910381d9500008002e41c4648000800303052101c1800514030381071951a1030001d02c1c00c083d40c0503903101c000c80c0243c20000020049400242404513811070030340c010170740700c1050890000c1305a01c0ae0300200140841400615003c403a24140100d11503c00d0712103040d118005035001058041c00603402d1054441004031001e154407000701030101d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 820882059 1250 820880809 820880831
    0x10503060105090a03050714040f060f052b030f02010e01060e010902090d05011401050a0b07030f0f0507050f06010501090e090a030f021515090a020c1c0507080f0a110f060a0c0909 79
    0x5423001c9040c0203001c4c50408100803034034606030103880c1c241c549900c0c0644445282204000c2c8200c20043d0301802041c0d185001210846103801015583e4000e031074400100c018103d0090840d400032000100c5a40341880030b105242e22080100d0440c0c4001c00007503202c000d1f00001130248800541d00410543c0307050505407030680000019030494504550400405a850101d174034244030700d0200030005042200c040784001c0c024900364082c400140b90103424100c0f160742d110300c5c120194050700d850b40e05c060300410407583c1c00714002000d0401c0210300041d60500230603069641c2c40c1288002e040c00107a40201c48100d10800142802c44921064040e00f81490740c012600035600002c101c0c040c801040005035440003500031140c2004110780244401500001c504001900c011081010030908000d11008240100041c1a01142e002d4445076508601c10026052100544e80021180c0112100034000c1e10301180451780021103507408280c8910b00c120403908445141c0040c40c1c40c9103803a00d0350780 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 820883309 1250 820882059 820882079
    0x90102010f1e0b0d030e010c14031612021609050c090d0b060f09040b1f0b0c03180109051807030204170607110613020d020a0801020a05070507090b010503060105090a030507 76
    0x40708440500400c48075060341c2c00e1182c0d03904159405404607002d04006a01c87d442804054401c0d80240340035079914a00c3c042240c15a400044104d1942d40103150540600003c1c07078810381c03510701600003468074803422448460344415520560094031740d5840003408441010013242d01605009003801a6030102c0c1c40c020260800175901175010f035001903008111424911010b0740102d80010b55070946030303035920103941404c1203900f803041420242ca10000d03070314940c6005495607080800156480b08900c1000900001d200d800c0d00d1f041002e010300c100f20705c0c0c6620300b100c112000407050b00f2000342d981d084260040e1299600688241e00000840d40c0100408030b541806410280d036a07100028000030700541e1014140c5551448411305075800700181740801140d05030340e101404c44081c6555440b6060300b20382100050707401007080080c085017005424810000903040d01a81004100c80c8280004c16a00008005d541405400540c458840c2ea450384403500459104c411281819105c1c10000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 820884559 1250 820883309 820883351
    0x50d080c0f10060506160605182d150f09010621050d030501050328020a03060b01080a2a17070302220503030d0207150e060103121d06090102010f 64
    0x2102e4a85841008541480d102044884e480040107038400000170548418005150140c221807400d500c0d81135910406105024810001010300f900701c003d070100c0f44046025507480c80c4060015040354050b59107a4042083c2590802c0728144440282d41c1c90964043c0101459004060140055480f404540140c1035000c51800d100d842a610030881c00300c1c05030260f078428003809034580c11154101040c80c200429042c0510016441c2d0403e00f040382d004100c010170f254005960481c0c42e481d07104240e581108082d60400070500301040314170400d04140c030350307001d800d1064540303503008001082480e40304002104440d404640800e8a504100e0780c0070b40203610210400100100c5025110401084040c1500460750082c01861810ba03a01201500941c44203a044824094910780c0c80581d070558400d0340703502100c1400401035541103007881083e040002444104200c0850716003042280344001300f01414800ba00c1268031013071a800184d0240c00360040380002c1d6840c196004801d03a01100b80d103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 820885809 1250 820884559 820884583
    0xb03130201020f12190e0d030e0121050106080f0405190c0503030c01050a0605100e130204150c030215090c01231303020a090e0d0e0a0314030a030f15050d080c0f 71
    0x82c580c21742013028103454030411801119802218407075000e0119004100c110303800712052400710303020240600e12101c20625881c0408800341e40324014001642c00640c141d030006805180c06a091405075121aa9801c1e2b80c05201c10040441f8005000c0140032031807400a4440102a25201c00541030542d000307040469010f00c21070700f17200e4002014101070300d0030340511107c1d56803d144c203000320b000d014554040c540d00e080c60950030400011003182e21200041c180e11203030b07540e90001d0064140246030481c2003401c500700c40180014000b860700b002400d0301c0c4000e003e0828071441461000c0311381140100003104003c0c4840010000c07182003110300050309403882124000c0d14240ca82d529001260005001c40f00c071079101c00c4d01043c0181c000c003202400720300c0060030110041d40326035502c030300b07031000004540d0190700204682c0c0a903505130007a120032280d524001c0000c0310900703502e000301d03884511941c0d00401003070306010103001503403040301c2518407800101c0340d02400c4d2081b115645c001a10074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 820887059 1250 820885809 820885837
    0x111f05070b011502070b090d050d0c11040212070309020f100f0908030a0f20120a1d101d0409050303040201090906080a06020901020115030813050102070b03130201020f12 75
    0xc58000320b6042c9103240030703e00ea4000e00c00c4034181980c9002550044042561000702044a040091810404001c1c00742541e51010461045490085078040e060381e0a00e20480c0140a050200700f030400ca03940c0c0c04109841c000c540c02d4081c0c008520005143c10000e500102d07a0914800500d030060402d056255255540d000142c0e92924003c1d01d03030091a039281e00040ca20314050410790300c40e01280f0002c0010040703180c008014112441c0c078100301d0013580b4026080c0400c0145125400000c11140800781c05014041d04d046800014011040c1104c01001d215101441e9441c1800c11000072841020280c0104800c00c0a42001640c9400481d42203001a10445020542d00a280104001c540c0039500034588a4696036600740650010404141150340e144501c0c4061032441142e60025409082c50720350301d00c04003011800800b902d800450541d40019402c010311200741c0c041b00e6005081c28090740d0035000a05c0100e0902d11900ca41c44900e1044e9a07204000c02c002c0701c000e0243c00c1c85010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 820888309 1250 820887059 820887061
    0x8070c1403040f120209070323071706010c0f02090a1d070306050709030b010e1e070f02370609020a0e0717130303050a02091c1b12111f05070b 63
    0x303801d14045044c00030094006244402240581303000c0e130419100081c1e0000c905602905031011088400c004941200008184d00180041c255801011540111080c80c0400d803100c13641d201c429202000e000024094444200000c402490b550702ca900c0c060b0f12400d420480301c00741602d41d03550310401d003c1590210f140101003943c0d14068031010084a80c00140382c1c00d984e18002a105803003400504085140240307483c84500084c02d45007840c800d030300e107031070381c006201c441d4a00a240c040078407120b0005103e1244d0078505198146914040b441c00200c14054070140380c501000540410740c0000d401608a0901080c03048200a1a922401040da81c1d03034500500c401c8006800d0300151507101e900310244140401007886500a00da006002150262828403036502185074080665440000d41c146681c51400308502074104e10800c8a8441401e5501410151041910b413000a0002c00e01c2c405079a081030071352603684a2005406212058901c042008940505580e110800446035005018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 820889559 1250 820888309 820888319
    0x20c030708041d04050604080f0d060306050f0604200711030703050607230a081003020a0605090901080309011407030c0507090614040608031c0b030f240103080a08070c1403040f 78
    0x80c40c2610039038001d0011b29044c1c03035a480e844d8003503011410040103c042042000c10010403801450000c51140340e00042d10f00d84004500b1110f200505203520660402c100c4000021180d10000010400000441d43d1203405183c00c180d01d10390348011701c0c2c0502030024000144040490b5a80c811402c0342c1701c0d515860000116014071114004a10008003028822441e10301c1c81082002d50004d140c1141d00d40d09501da4000a024003199070003840000e500245c180c061341041029280100f144400440c00c1c2680d00c3c0018144000c0c0c544072030000d11002c95040113261007007072500c408030342000c182c0b0359050b22502540c000d4509401040104180d07800e07108100d0800d4030420342100c0c0110007940c10041042a554050099040080e2125441d281c4410715541c050000c038000c141e20318010160210034001004d080c14011000718410486003004001088069040740e1a0907030324074052000c0c0e5031b1500180d9800d108000003900c0c041c2070b030040c2560488004002c205843c00d41001d000d01640da4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 820890809 1250 820889559 820889609
    0xf0201060302011b1506181103090a1202030706020c0709061401080601120608030f0d150308040504020a090801092f0117100b2d07210201020c03070804 67
    0x5201c001d000034095000c52103000740c001d005041551081504501c5149806980015100303543c00c142000c0901c50303200740e00414a40700c0c1c20807071100100310b0b500b1486d20210098a42813a0341000c0e040e121001080150540700f40201d9000a48c400000c6444001d0003900c030740c1d04c1010340a8094060301e010fa001c100d50401c41001808144142c0d1100b100ea501d001c01100d048800e00d18512240da155078010550300c00074405400154051406a6200c8996040003c217980c0240380c000b4003003010480610103c2d80100407601912000d80d800b40e9510790f83c51085030348200550012400d0751800c1c060b80200310200c3c0780104032594403171075510345512881d003500c0032541100402d070218000c100601c03a40700c00341d111030b580b0140e01200f01c50a56910390340803c803a40400c810110308800d1000c0003e850061866406018100400b010309107003490b40c50359501c014980c0ea80d0300c4805440c4004403503e00c00d40440f01c40412050a403074480c126458101265080307401203d034503400500c1c00c0c881e91606 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 820892059 1250 820890809 820890821
    0x60403030f02160308090f060c0f160b03010503030a0c030e15070501150807171510170a0f02010309020d0c0f030605090613030f1701030f050105060906010504050f01050d090c060f0201 81
    0x841c94246c50320030b44104221200f00030480d820381003082409840b0988000380024040c0f155007070040d0511408032040c081055209401c01c01a5040c11300040c8901c4d100081940c0d10b1280c0c9081c2220301d28440c2c1410703a214004002490780c051014079404a180300c0c41409007055911600003131218500c6140d1080c22052503002d070418580c80890100f0011f01019469661016031106940d017000da061640a8840022070b140144283e0000e801c204402d2964410b005601400f00600f8001c14150f9844203950110440a4105a2501403c00545d60b50900301903400d5807010703ca1084698410440404c903080f440309454891420780003070014000441c01600c60446049c40c80c2c001340166506650360f0420001c0340d810859940e032080b0f2248034140c0b580e4065030180e00c0c1c56010b0a500e1402d5429100000e108030300a0740721606120340c598001c0d06940582d00111f4007501d41108a00048a050003840403a4042034100b649010501c40303d0000c1800f81c0b00d4903504c2590806107948103a098440c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 820893309 1250 820892059 820892063
    0x1106030103080a1d090c090111030a0c03022a0f190311041a100f090b030108010b270f091005040f12021912030609090c05130b0303031b09060403030f021603 69
    0x245e40300c00904e00c0d4013240010040003405041c9080c00c284c01000c66032445d04a101e51002052306182c100003132540410580c10696a142c004120810b044400594004042d1070b01d0fa000d62038010021041d55140707071405010228207100342003400e076207040900420b05c2406605010303614000c070307515145c9000d84040d41c40080252206001c003010f50012a410341003940740500304407110102040282c00365000754000c0a401c0c0001c10441a0314040121000d03444504412510083c61580340000509102d240c1c0202c21071000c1450303944003c601824120001c803110541480c110400081006081e616801c3c0d6018001009000341c1665059913500d40c1c2c03543c548080d41040706407000094801c80c1c14805002a8540420703141d91390180b841c2958140942100c0c00c200054084c42a0300700004010201d4440f0f540500c00701c0c2c040000b294882c0300281000202902c0407001000707040c0b00c0e038110303054a14058010b580d83c55882c10020309800384d1000f058018042c070030318020070030010500101503039 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 820894559 1250 820893309 820893319
    0xf1c03111204150314041103070906080a030c06060506071a060603192c060405060c090a09090501110f0406030c0503070813050c0301050133090e041106030103080a1d 73
    0x150808075481841c00e282c00f2150300705516810080401c01003001c0503406035108039200c01c00420514100740c10410f140c0c00c0128600d1401c3c02c01c04c400303e03000540c12036240e0141801c124060050602c4000b803d925001a83c100f080019000204000070400e1003200800002c0380130316458110802185100540756080740499020564542d54582e0348416900790081d815110800c82003508030941e0f2443c4071548019810900c01c100c02e002c0140041d907400400351344003e20780030b408000034070a00924040c804540744d46080d06401c1020075401040507000311407503180c071040d4081c0802e0b419800ba0150760001390614015046640c01901500c2c0250003d4441034929624100510240003080c18140c03981e204480b070b19030300da880a20409018003060b6010f101d4030380d00c5003041003d0000c490002003485c00a585400c010590141101d0f05880103402d0001c1261182c1c2805094407200320b91955002c000000000100300c0000c008100030002c5c1c0d190201440c0c11040c0905030050440141c03a001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 820895809 1250 820894559 820894567
    0x602161403060f0c0c070b0a0f0c1e03090f260a030e0f030c040c030509120705030a0810180902041d10050601052802060c13060e0f1c031112 62
    0x183d9002207030302000b03488506060100301104145840e00c0e40d4045032402c0c00004d4034980d25079011001d520803a481c1d04101c2d51a20140d40c903e84864064101c805c81a070802c4080c0d01010301c5800403000800008102c15500c90712056403440f1500302c2e02500c118101035810701e00506001003603022409816845040d0704d541045c0501c140302c140741a646d0b6041c01028082d4203550340d14400c044040301980e500040501c2c0c207525851a10342100380001d2848801d0040ba80059000011079096460b1460305412a840311021043d008160760002e055810b41d00c0084041007540d03074806690107008036030074030001d400c000003800240c1c0c00780b040b407440e0f81102c1d01011440050f0b40003941c0200040c5030851400d030800b0002d298004200300c8041031a055801600c4900b80d04102079078201148118880ca044110001c02e8070991072032044100740424404990590340d5055403903030400c8805841c06101100c0c112580440440c102821400b150740a590807501e194000f03140380c4141007020f40e0b2860 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 820897059 1250 820895809 820895821
    0x20304030303021c180203010c0c02091515030103080a1d1309021c15060501030b0a030f080409050a15060201060b040e19060314060601020303150f1306060216140306 73
    0x654001003a000590440c45502515244e29210301d0f0f40341d841c403000c0601c40d01901e204050079920710a100c402040240801075016036a0117080710380201003001100302024103080071400060403c3c4604400c2c26011000206000b9014014030045401d03994019429401c40310540c18003601c030f000ea541203244250461103e40566019902e0701d400203140c071150658418410152291114003100e0240d0200e010701c5101405002c0e400280c0400d0a051040240d901e000c10010b840b140f101508103003d2081c01e5083c004000210780103032860704818031652906900c504050011941204007060441c1070004500b40b045c441c0e002a10198a1854034152034443c4d442c00b000d01c040c11070f211a07035182006030481c94907071103240e004600c80da2900124483c503071141030801c04020900f0303055400070000c1008803443d56030640b21221044801810822055021402d010490300b440300010b4680400410f2058002604c128080041c0c4000e003041512030700da02682d18600f500d100d4266201c6004140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 820898309 1250 820897059 820897061
    0x6040b0a09150507230313080601050405040209040b0a020d02070c0e070e010926031801020613020a0e0a0905010606110709060308030a0b12070b0301050a051e010e0616140f0d020304030303 83
    0x50f131720404401c101d150208401301c02d0b003035903c61000c80114407000300c0304104918083c02920700418048404200a14041c3c0202e213428800400042c01d1031221030029142c000c1c1c1e40d05840b01d01e02c0100c0e0854a54069103002c20200b040c901441e4002e000d6440000d803007601c02c00c40701c02170600c183d541c03803c4a450520400010a0715107504142d100d05006020b50b0701c4001c02c0640f5480481208240b0520083e02c0003906042d0003400b864181210721520300c01584440762007104540040c0d00c01c02c2c85685101c0f0b02d00c000c10000100605a500b0402c002070215807000704422000c03002416104411f5860200008031106031100a01d500d100f44001907c203005a0300980d50701380003800b88025000c1080c045030610106030030031031005201000521980c101070505201400066411880001c013050303a00050583c0f08058604200114016403269120001a56070000207010024541070b45407910052400703488880300d14610030345030b00b000d208a002402100d5004103030041c41c81c060960714120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 820899559 1250 820898309 820898333
    0xa02310803030c030709050d210504030b0412090b070b060910050d1a0a0603030e0f221a09011203081017030c1203280b06040b0a09150507 61
    0x52000420824001160601031009501c502100141c8556900e0214809840a4000c4d00071034007405000724000c0000b182d03004c0800c07a40b07032141e026200010021008445038030480e00010701340041d0009220410003401a02c04105419444444010391605614a0f00d03004c0c045001d8440507107040401c0d05420f1801d0b540340c00c40c00030080303d0b00080e01c1d5404106088003050048606500d5082051845405410083d8200c0381d140e909000f00b0340745880090003842c80045140c0705012658507015196103206c0701025079000c1c0b10480b100c2004100300c04000f48881040d0403256030350f108020382c0d203180168240f81610014440d1740790200e5903071070448403080c00400320701c03120781c5001010400f80c80106050048a480e4401166074418040607181000c54420816807480400d00a02004190141d281c000c004203071410700100718240071031040508514482c050b000b5900050224290550100910f1a100b01d034030b641c0c1c411aa16100d00c80030160304160702c400640c3c01c0c0032010002e00441260 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 820900809 1250 820899559 820899637
    0x1050705041412120a0807020703080418090c060c0203010f0b060717070f060c0e0a061202090307030213022203120c0807052d01020f0f07051f0906050a02 68
    0x89021008160000c80c07800e401c80c1350850380040d003c40c080e016240c0c461940740d40f112080c409001d143c2c0c50340d0b0b44d42c0c60500a071301503240c0c07000c624040001c038080d003903100b02501500524003039600f40c3e035940c004c2c142d0003210100307030300039400c111303403124032451502074140941c0c8050b081c6450030206880c1c40c44800c1000c0c00c0c0104c542000c01c01a4003084900404800d0705d8020400000c0b060454280544a8248030154a00400c0302041c10418160010850581c41004d80300141c1d03070b00180000a0f05120f40780e040250f00c0030034030003480b00246d400d03800b801613407056502c040e030000d83d130f140c0941e0352800a100040a0340343e000d003602d46082c49220f0b4145603501c549403160500200381e48240c00c10060701400d129886404908180841d626500030303500c603083c0d400031460100c45140c554601c2c41849981081010001104800c0140c1006510031315252101d186928510140045001d071a101c1c030141c80141c140b0b800715404460520071150300c10090000803010609040d00d20030000b501c4004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 820902059 1250 820900809 820900819
    0x6030c030b0a0b210114090a0e150c0903070305010e0c0d0c091a06030f0f07030207020a1202031606090311090105030d0c0206090d110414040b040b0c0d0608010c020609010507050414 80
    0x1302c050a25125070100740038003420011185807205032414004403040092060300164144543c410b5401004a0011500c2002e07640d00e00d41541c0d44400500e103031048044d110b4042c4160bc9001007030040641c0820099403607a4180c0f21070300b021008129420008003005440c0e8040c03041c0401c49110b240c0d01900402810740a101c06824010000a003513030030484041440f19000003c100880c00000519030b886070340f034101182080429004602561380ca8000d541524480ca404902595030801032030005c031508030400030070142c4a0344001c2405a103480300f2181c031a01c2081c00d100c94074100c08000c2c140d50001d00140f904001622080390200c80c0d0070750682c3c010108005450303032a1212030841d00c540e0f0207500d01d04c03020440541884110744a041003a56001005000e02c80040c8185502c2900309800240c041d501e511418170010561254060342e41e242442d2000010742d01c3e006410220b18604540c0036518640c2d6a0764509098402c21548600003030000c06c010b1103440819401c800c3c0d02940940 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 820903309 1250 820902059 820902097
    0x4150e0708060301090204020a0c0530160606080a0c0603020307050a2304080a15020c0607080403020c043902030307031131080706120f0b0d0c06030c030b0a0b 70
    0x3040427030307120034a10400158a070310044107100e020040407001d000e00e0100c00d80c003204800741e081c8507500340c070f6110701c04160001081d410360400303611500c02003074004408102da15075450506680e072174144400c8900e01954000001d200d4000d20a807071181c030982c0c5810b450b20502d9041141d01003403006100c081100382c42012412400c580b030203800507080381801450102034500f008000310003c030030001c41250040124004c04c4401143d0182c1100c00d9003002c801d070303455514080e410206c0e60040d41d0b8205180c2101c60403440e65a0281d841017101044070002808080c2101800d085141300c82c0002580c020008100b4545c07003a4000c1c403240070b2410702e00b810003000e803441e14188450f14504100c82800b0a2a244505112a40c03050090a5180060050f280340120107480381104c01442d01e10242d42e9040707410b214030142c0241c80c08601c020407000c0129031500c0c00344001580f501071040003c1c0b03403400900300385001e4031170040350400080c85607248514140d119240c503800300e0b8a11107800c81030701d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 820904559 1250 820903309 820903313
    0x3080105040b03031c020c0708010908040620010c0e09090a020901030b100306240f0e0604270506041b0305060612031204140114011d07050f0d0b04150e070806030109 73
    0x1485e51910424403c001603920071103410154580101d035006680385900d883c4800000580440440703084640e40e0400c443c0800c404281021210300c811840704495007048025484194410351441b00c0e41c4045801c0c480c9a103030190120360701e409162001303410031507200041c40400c505500c410341c00032441e40c15100103038490382c48500751a185103100b6161000e045020b88401c20004112002c0c10801b030090300305a20302481c140140750054001c130301884d500da124036416800412807203c609981c881c1060411014075007140d4071002204c0076903d00b15203413403840b01030f411108410202e075007200c000c014640340c4000300040e0003651405140b252208108003001c18440103a558811070081040241030104052240d083d16104c003c484030030b0349200014060045d103420510b5448808000b408040e58a660054a5070312a0360110030014a01040400c00c0c030401d42c0142c080c40d281075400780454080640042d03020f0141d8000d419290404000061000f480340810a6001100030b001050704440c5e9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 820905809 1250 820904559 820904587
    0x20d090302160605120703231509010f080d05090303211008031204241805070905071b2103020a0237020303090616140a03080105040b0303 61
    0x45841100540c10034015000c0c002e95980b003040080c5420700b46646040c0c4007070070352100840b00918110038583d07100d4001da001c42c90380720301d204401650750101c1010305103040680c40c1800703206ca030315200d866000e001103018401802d9a00031112010000c007603c40c00c03170400b618540c001d8034005802d44010300440c440c4212100c20340f000c510000f05181850704204d040c0c250203003841d4205003c43d60003001202c101010a241240e4442d0b0008201194260584a210211500d4220700e1a405040c00e043d00280b07181011030400a0344550110384800b665038039a8002d580b001c07a20700001c00d544d0309403511100c1c50014086c00052191b031100314041030461041da40c02803152a01400a031380410131044164041182041100e00307181d102000e0241d5030441011030390095480c1c104914440030000031510200b0546903440300003400151225040603914092030749205054618400b080b1102000e0300000c2049030803250036607a6810030303030700309001e00c0042c0c0845203000e901807004001011a42140d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 820907059 1250 820905809 820905821
    0xa0f2601111902160e07020a0b160e031b0405130b01030b1e060a05040f0213080a021516080313080c011b0f02100c02210409050a02030622020d 63
    0x1d10680a44642d9540c80080c40581041c0001007590301c0348100501c1540ba00d41c001c800c0380e6035541d0070141c695400004034105071000344028a0403a06c002404442c0d1a0242c4c00d050a51555079003100b03200c00001010347e03407041e01c10680e01508000070040d2160074a47c001341c0d4403000d256107003402c011141c0d071200011030099200780c41620700ca605020b82c1c013041d2000100c2d841d107400325002440c00c1290002d404c03000d80b4800d4911a0b80c1d24501c1d40303216006078058500c60240044104d002680d100c0301c003a01c410035110201d200b80342c409900080240914180d405007020001c4100c0c80302d0884da41d840260340064082c0c506110000380701c2000803803190003000302e0700044d00040340c1c00ca01c200b100c280d0244040000814082140a2040102d0b40040c00c5030b020200540d020030121000c54007a0f00380391260f8401d02041d2519612183e20b00b00d0030005200325074002c4401c00c15580d410312140101e010039501c05521181d0401b14008400d0140d910801d1111042401440c00450101d40c0c801c4900c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 820908309 1250 820907059 820907081
    0x3070311040902060903060a0b191d0a0b0a0311040f140a1a040501030609060b09090c060d0b0d08130819122d021b010c0f0512040b03060306060a0f2601 67
    0xf440c0c103000c0c1c00d06c0c00d0040d803004252b800c0082d80705065083c501d4114404286602640c40c02c0291000180a03010036040f10860b800302502c2811800e0b240c0c100310354010390401285000c1d07824191904900b0500b845200c0c00e00f0304950080c0c0c0707640c48012041c000340004190040c440b401d09440341f4880c0e070703441c4142d40c000c2d0700c14400091030140515055007515044a8414411051a4100080d85202140a820b4000e00700d4040c1c1d5a116042e003440002c0007031815031608010250444010072031598024106843d50a00020249945404c1e6031f5841001600c00001211440c640e031000400c4007015482c80520f504020b5540f03940344130001504c90110008540d400204802817a11b250148810030382c0300c5000100203080401c000003e041c000712000010b040d041e410801c8403d000707040c0300c18940d603040580b8003a0b60b03d5070f40f0700d40003440c1c2007950098880d010f16008101103140010f0414101d415280c401c0950a1030101440b0081d10300c44c00307041550140e80302580b42c0040c20310070b141c07041c0c1d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 820909559 1250 820908309 820908311
    0x6062e0903060b090105031009020d0b04060c090911071709040e01061805100b07020120060615130306020d061838060d0219020a050c03070311040902060903060a 71
    0x51035420030000f038520340c141050251071100014021074502203442880f641c1a540041501e090324404984e00c030212a101500b2492900d05000807c034144d006070128850564580c800582c840c2100f02c200c030101d40180c00d000404109000c0002c2050407003641403c0d01020300c908113251b2902040548411654425882e55200401e00944c0001c15070303280750383c0504104104924003a100c0c00c103107407803034021344e4984440880d00c14110ba118800211301341c003105960340d80c0101071080d826a5648107407400c510503400359422018440080046d42c03000d106214500f50100d1554a41400030360005a021080c00e0725140045010f00b1115217101a584450303000003890942c203030451440c544012940f040d07400e02400301c240c041583c0c016042590500711000307561000c2075060840203210300309110040440400003880d00701e40110b512400c4c5030007141600c0300722100e001010380b41d501e14000181a0881010600c1182c24164032403003001d403001d081c40c1d00c0c0c20700039800280303012805c48501421b1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 820910809 1250 820909559 820909577
    0x30904150e1008281103190c23030a1b0f0b03090c01020c060712030603021c02030c100f082d07030605010905130f0603020a080705040e030a0206062e 66
    0x400c0100520110040d83c044210001082c00ca4422070554456001500401700d002840d1013a0354280400f810107807210405282c40e00b0030703280c8007444901d036100b0001170011915510301003160b4201400e4813158004d01403d0075012540c0d6209030000031000030400f2084614010410544800000020b04100710340c4603220701d41401207615018400380d015045402200002300c40c0c2d12120196034020307600c0b0603905d041101e8604100c008201c5544040d5002105000341d0035450110030100003018026801da44006c5500400e028141403207802d0907001424010300b0502c1c240c40749403080d8100000c0d079122540e801c4a8803168010245c648580c10095452005000b00d5039014407445008150a0170402c421a02c0c1c5030001703100d8078101c11101c05454485070014403540141d40010003855000b40742d500455115a421030742c520640c080d040c0114036211000010f480c00005540c40f1072140c0d03006000d10fa07030700b00501524034125819460300142030514010000100407084c5c480c2c498a0395003000c3c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 820912059 1250 820910809 820910819
    0xf081008060108010b03010506030a0b0402010f11030a0c03030b040911040f062318010b0301260d03020301060f1728180201080106050c0d180308070c0f05030f030904150e10 76
    0x2312035020b0700ea148203030300c80112030000800d400311095100350242440200300c06002000c3c0d039529040901c001d2035020001d821015950440d0491030303d5806541c0401480482d0000e100450362250400f902d09000404511618501900034141c0c0203400d540103d40f8603aa0360810362490144103054100403c020b1141c1d029080200540400602410104070a540f60210388a002d01c018000c079a2150501104010710034500ca041c0400300955500300c0f1800c0c040f591703004000f90004c1c003842c0002290461407494551060040c02c2402c0b4411035039034890344a410101c07455808003d124080440d0a00200c800259503208003280aa20700e40b12880756121840018140c3c0c1050b0461014001d0a00640c05a09000559400880b100e03090030b5540b9000014280c099100305d42c801011194005540c4042044891000c402c86030a40c0041061980350410561640381c1c01071001c0050f40b0a00a118452902e908190400501c2c204000200383d03c0e6013044014181c1244c0300b40301240f0503030701084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 820913309 1250 820912059 820912061
    0x306090b090a03140a2a050c01020c1f0306030f050102030601022b030b010e040608030408100b0105160305070c060c03080c1801180b0a110c0904030f081008060108010b0301 76
    0xa44018424041d1402104030b6401031301900031891307046070048000c81c0c03022031980141c2c0c2c05407198480a120400c210300d5a203030180b208100807000c81e40780c0694951115207500020ba180c064010042107070040d6003020840503070061034100c0040070141c81c0e242c0000071900c600c1c111480c0500071800560307245000c40000e440d00700c00e189041040841d00b100d4407104811014004900d503424a4085910003407600100e540d01c59a09916500a2400d030340001c00700710000c01030007103030501d006031410303104100c8442c4215216914194080351040001c256408144102c0c0c0e155030344203062107820031116032555001015035030814404905280c60384010301d90030400c1305621551101c049490b02100181c0100c807100d420080c68140a10040c0040c01d40c84a800c0700c81c00340048010480d16051013080c020040b52075141442594060f004542c0c0c01802c24901c814801d64161320740d60b44166184904403241c002c01004c0340146801c11402084908003801000e000f0010100003013100b1070074008141c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 820914559 1250 820913309 820913311
    0x503031b150c0414030c011704050a05031303170306060703050a020a17041d01080d0c03122d050702060115030209040c0e0a0506180103022116030c05030f0a0b0d0209010306090b 78
    0x5120340d00002e4040c2d01607900114521408c2200f401d4419251200d150552400000318001801e501011030415a032015000d0208220317405001030200700030039404111054030042d560103402c19020046000868080c4006040709011841201c440c800c240c5c54081d600c5e0300c8040205560000018100010300070591905c0e48103040764006005949022412541e5456110030031051000c1150b2400c1030602403c0000b1110300720b5901030117a40020620030000c0070300c03403400b005040c0c0a00000c542061032482000c0c45050290010806a420512400b42c1300560242c0c030710406800f0031074041d80b03459030300501401016584a102030303200c50504000c6682d8141c1c21480c007a030300510001a14560f015040d05880100b0f00740169154114510001841c2c5080c0642c11460701d03032824403a80c010180c1c0c00c0d9040507410342d0100b040c000c083c03070100d50510040e28940d105041402c040f82242c0f03507a6204415016005029171204c0315598081210110240c0c020340700c441e82e070b203c41410f0200a110341 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 820915809 1250 820914559 820914599
    0xa06050405090d1d06160614151c061e1815181e021009060c020906061c02090f0d02010f140906040e060301150503031b150c04 56
    0x1030050b480d01100c502c0d9158220020801040f0315103000d00030702d08059804040b0b214001e000700383c0e107041c5450500030405000384112030f92480c02c03900c00b080001c007a034194012519a030000443e00011800c00c400c0c0040300d0001c582c9002c14001550010700c6500c5000f00b15500b4888012200750017001c5502200c83e800c8a942101c542440548000703503100030650303685e440603580000e4800000c15802d0303480429800003000811401b0b0310111140c803030b0f00c40c00e00072842258103001417045a4804c440c60343c0300784603050228a6030590b031001860180c806541c0700402415280c11304e00d4000e011318000306220740c0d0103034099001402c0c460a0518071a02c0c03a9017001038400000036a8070364002082c45611014074000c110780000c100560703901c0c030070480f81403120003032059454a40390620b02e04046010349101d44258a0f1050403140000d0140711801220001006103017448083c1c00f070401da01c1c2d80c0590030000c03030042072404640b980101003002c1c040c0584201c0305403258282031840031180000001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 820917059 1250 820915809 820915811
    0x6031a0c0f0d1407082a070b220b010e0a140402010e0102011413051204031101080403030b1509040b090f1602010e0f0f06010602070e15220b0a0608060f100c050601030b0a060504 78
    0x241b4041031071044942080d80300340e080080b42d60f00c08120164802002d658500b004220308010180440a080c40b0b060b283e240500075070548403200943c046030708000c00350b202a4507680018015600442080c80410410b00020070014004114004d06c9a400c80e0000c1407070340707480080024000100b22510f00000e003051003034940b60454465100911104001c01e0402601200140c20140b094201e00e62807030b805411000003800446459806070400000d29014a140005944107032804a074654010b91250207888030503100d04040d1103c00244130031047c00d640d00c4d2a03000140d05000c0046600c0c00700740f440604103e0004011003401c1905c10f0b0712800031540031180c10702944282d91262038008001c51350210f5900f01c9000845d10704c4007682c4000401c071110f01903040841d0000e80100f480c0840849140c90300c80e407070348000c2c1d0322108241c508030713001032900300b8150460030003032a60080fa8090341070946442e096696500e207840c90981080700d40f00d510409000c1001c40d94014000a4802198 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 820918309 1250 820917059 820917121
    0xf020301080d170609060102070b190f1e1b05150a1104030b0c0306040e0312090d0c0c0308070c0e0115021005040201121d1006031a0c0f0d140708 64
    0x81c07025114000d82020b209282213808200d1b968000c000e0b4900400841c83d02945503411811400321244203141c101012862954000d101140b194103044c000199070115045040352456044801c10002e007024001000080403800108204200b0341c81c1c03a5910075099080d500c5c0001c1d6040070b49604080d1000980c80a000510005030f2171305140d0361169281805644030b56039100081c0252502d0754a4540700e010010b016180840c5046005200d01c4a402c21580c0c044421001120361850401003e010a00200010300005801100914113517004809180300b0b16242d8001c500402401c0e40014403207101c1c20740645001d07406020140462a81401c204040d01e099000601907070703298400030f10320660f0340c83d1030801c0481d01c00c982c101109403a011200e980518100e81002400140410b4a20b9003502100001074041c034080e0a22491704070401c0c42c10b05840c0c4002c0c03c0346401038400091101d84450400003201480f03c02244210600c1c0d88010190902214810035081601d038045d590702d03a01e035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 820919559 1250 820918309 820918337
    0x11041205011e111e0d05010608070207170c0d05150c12010e010f0e09160b0405030114071e0c06020a0305040b180309190e0103050703030822020607020409060f020301080d 75
    0x1c1e0a4801040b000e003500030844c054403042040341d01c03600c02601c4582c3d15117400403c0080c0d000300001c0c487c10341a02115541900d4107800d00655a4000e103452065005a0b82d0070810b003443c1751450342d2640b01d1000c882e84a901680d81c00c098070003c940f00c0f400300001041118004041101b418010140c0b04a51400e55050032855600c1900ea40910700300c4400314404100301901c10000700d884a8900310798000416110301d1441450f03809840b4203807080d8242a954450040d81c40200c03405070440e61503044074203000d41090040071064040d00d900340140c00b0010004a006030004040701410f80d0340009841c60039140400381004040c00441d250783c0d04500841450340c00104540200c8411030700751800e410441a0304a9a500360703000300e60401c290800020800100060060030381e8881c0d00e804580d42ea851400c0f0300c2600e80382428885000029030180003501700b09008200c21030020f000881c5e10b4036103031104070540700c0441d98000181c4d0700100401c041081032007200001c802500d000320044041c1c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 820920809 1250 820919559 820919591
    0x19090305030d181a0714250201020a0b16030f0203040b180102041805040308060108100501121407090311030c1815031902100e060d11041205011e 64
    0x502d40c1c00030754441c01d444034402c140841900c1190b2001e401c9640030324684000002c80c10a980c00c0f40401d0301c80d40094601003000c4156070900004000c040c40404003a441100d00706c00d80e00d0140e06502075480d00c2e0010400600495100350302c8922040140045514014129088500030f1020240b0510a120009011260868220340121101c440c0910b400240310b00a00c9140c0c0402410071a10550644101b46a004288114000d46580c20540d880d40019220a00100d40385c00c009071107100c00b40015070007000b804100b0707920401e00041c80140ca0400d201c1c101d20948011000c1101e80100f0410400581140c0603100410707001f4080d001c0001c0e010034100c0d6406000307080068400f00014240148941c00e200c15858010115482044100c5008081440200c801d0b0b00a01400140d001304500421117841c1040020b00524608541c51004400806001c40c5421009104010018072500c0e9142c00d40c0c02c0d58000d000000d5600005602c060388000c8150800410a0814803002406105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 820922059 1250 820920809 820920817
    0x4060e010c02031905070e101217040906081507030e21070206040605040905010909150207030e03070b0a021006031106180a03080307031a03030d0b0d171909030503 72
    0xa081c1074000300e0380c520000b41050700d084902c514043d0310000720342c14004006000b40881c0c041d00104143c1e5110b90801544404140c010190070002e640a2100000e00d100424400c0d00c11f900002c505150300c440000044e121164860355440d40003152140a0500d00748074250000c0d610b00b410001c040a21090035215040d610800c51040c40b01e98414a144807008103d41d461940108160390b600e0f211200501103400901800e1692440c1c1070020550300c00c82d2040390380c80c5070040b0900680f1030801504038040e5101010450812540c000d0301c0460343c50800054010f08001c011064898418400003842d0203915100d6030507250401c01b041022a041010000f882c8106440c0702c0d954a0343c5c014020300d85075010300c01c45e400c028810300000901100340c0255015039250f940c2407080140c3c4546280307100e501d003c5103e45c580c10820851500c005664005000c000d000741c100b5149404035101d60300211081c00d00000c0704000065411161002024401c00110342420410800d5045894860341c0e805 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 820923309 1250 820922059 820922087
    0x702060a1d0a062703080310080d020d090e04020301020d2a020c0d020907022e0c08040b0a0c02010b0405090102131a0403060c09090c0903110402041409060f030a06050402010f050406 80
    0x100300f488200300104a400840103150004006da580342002910401ca064040c400c480c07644c05900c40c0c0d0400948041207410003407000e07035215800309080030145070070800054000c0340d06640c03c0042002d0380b800760051400d001401481013060881103620070300b10340e0507510942d0464003c6102c28074295140f0361103c0a5a40550310b6100c1c40e60b480505914107403506540410840c201030f060498002014111300200c40b4006040c452070b041c400c41540d402c0000d0f1802002211280e00207040c94906a20030f104c05001480003040500901d001b2504840341039400403816500006c0c4c030f0080382c507500c0c00b81e0300802c401007502c0e05a00c90900100024000e900000300010f456400b4505840c1c4241e00c2c072000303042c6e0036104001e1100040b070090400ca445100442ea24000440e813081c0718a41482901c00329406654502c250342d07000810000c841400801c07490340300750050701100c4192410003040c2101e03480345400017003a0800d4000503110582c0114064201b00040006100d610b900c9231609440074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 820924559 1250 820923309 820923347
    0xa05010519090503160813120312050609060d06180f11120d030b0301090804150809060601020a030c0602210a050f10121412130b0903030702010f050702060a1d0a06 72
    0xd005442d120300036200307c58005d6610440e035000032a00d220300d00e02001c1c555110351100c0320180d0944160400391441140d009a02951401c00034545061003c100e80500d0b106913000522016a60b407004008802c1440c05d55145810908080802c0702c3c0d01c0041c40320301e03001c4510002e46a40554a199543c20a283c0d00d000c05403181500f05282c0c8094009511003940400301c50b84960b2541c2841194010382030120700001c8054001c00d000c4100890054000c00d01a405072101c041c040c1c90641d0010017201d012518603600704031841e1446110000c800100c1840c0d0b4000d03042c0d061074107101c0107454001d03003007249205004042c402401d04403101d1800700c8803c03903c2c0c040002c83c54140404044003040d88030000c0e00818251055010000c0000c04800342d4250350105917039140d00320380c0d10030300070b1201d01905540100508030256000c0c039901c4449a080c1d03d000c524210350f81d404034406400043c012000310700c400c65030b003801e0507100c11000310614040c0c4440c0c0c0c9051529a00030f25000f00e82200e15502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 820925809 1250 820924559 820924597
    0x614040b04022a0304080a030e010201050708090d030e070504020a09080709020f0301140d1a0612150106180b0a0305010302041409071415071208070807140a030e0a05010519090503 79
    0x42403081c400e40d0b00400c06d200540301d0f40b0350103080c0a000c1b05007509119005510381360001d5403035402803403d1800380010300c000f4200e421200300c040d0300600e0862a0803411348500c900010b003d0f42c070341c001000c50354080e9598000c030502d402840da2600d82150805043c090052125118940003a07095a0440d104007115a41504041012a64411600c58040e028061a4101301d40040c56264954021381c0c0a0700d0100310307000e104140176110118140c0000d200b544031070040101038440c50300708502240c401c082c0c0354910303507511203041c1039809108504040707a00c500040040d45080d202d8501c800c83c08040040003880c2c12410103491754524080c0a0001c421000b9002d180d03182c0605c0481c80c0301c0f070000364556a902c2802c00080c0041102a120002010540040d403d58840d001da24040c01c4940c460b403400d142002103c10781034020300c2c0b9940405076200f2034130000c140104115031a280c0280000a2072341000284440107080c443c190500c91400d0140c1400007850000460301c50940c01919000390f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 820927059 1250 820925809 820925887
    0x10b19050403061a0906030106060212090a08030a11010f050402030d0c0c091401081c020a0b040219170705061602010305180d05030712060e0403120f0614040b0402 72
    0x30740a90307000509403e2610840001c420034410a00c410707048226480c00f5165a0042010b00383d507058010140141c0103d03224000070840d10303026040c903100040201040300d8603110001d255401c80f03411280094410101041070030000e206410300c13003542980030b00c41e525040c0c000c03c2d511400040400700300540c2c030000d6010b110783c14001c85c001d00850384c410300000c020400f22009d40c0400b03000b088002d01070140442840401c0000e4100c010701ea64028014072309241e19010300d44180140281d80100f041250141c0c941e5050342d03440060050040e14100d1100300741c02e501c1c07800c001c40c2c00490007030f0020805840900d80410160a40c1a8246004a2030341d0300e201c0704e0b25075a058075120803ca07100e008801c0d040523400c0009588920323616034404490f0145000030310306456a40c4180c506000c00032020402081c4101011080100c1e140300120b000c8103005420400ca9000f80e09c506801c060102400f0707214982809007000c900030864040d4103080080380f00b4041d0350400260841e040c0503c403110a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 820928309 1250 820927059 820927067
    0x50607030e041d0606060315210a060911030706021024060f081b07030323042009190207030c14010903030b0d0b0a050613051815010b19 60
    0x11001e240508144102041c0384030407840d0b06010003030160703a4007598001980a0402006403803103180701c2e9070540496101d001c28020b082102a41c0340040210b0026040c0b0f02641c10400924018400c030710004100c2c030141816040071200703038207151103a08241d20030000b142d800a18501c1d244860300d0002100c00c0044409600541e0f03500c0410040c0500190001c0c6680d04641c0402083d040b9440d0484242e40381010703c14102001070880007888000c0c8036802c003282c4690f215054081c100d40b0340c1150303181d80c1203d071464030104807000c4075103514050398860a101c40188501702d616099400b0100d50030015644034401c00800342109545902003508030501d03102e1400c2c081fa813500700d6241035881610b07903c140c0c0640303400c3c58240c0c040703828003d4450407818201c017100c140070f07040200e0340c0c0b41f900d4103603181001c0c100141400f40c0c0801c44031880c1852500d103102e4180a081231070610314801013003d003c982440560811403221440004c0100044c418100450b48005120500145084190401070b5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 820929559 1250 820928309 820928327
    0x9030c120c0f120315030812060105270102010e030906040302040902030304170c012303281a090a0b011b0204150b03090c04020903030d0902030a12050a030501090507080105060703 79
    0x24102e00c48840b10300c0d040c000070b03030344011900c58190303402e100c0030f841e40d00150882d402c03038800200341c900200b1000703004074448200a40c1101c1c0501d030251074114128410b80003802c1d14481348100c1200d040f40b0468560b024815205990440409941000c40e2207000130080d006501c401303806280c031044a10110354061084070b000c0c011024201039508000306c42e0698411198010368081103030403600411303003001e9038441e040000c1e0b0105002d246036900400c2c0c10390f40c5502e443c00c640f200c8100e000d00740c0c012198041c080c045e00d40b070300d41c59803948810010080400c40c050401c10850745000b00011084c0d921224580d504440c0c00c0b80440300b002144003241c01021110303111850801c4581c070102d00c080d050310085000e261a0307012640380382007590800003284034151516a05a00402400075040125040700e0a0980000c1c203031170b400038043d15501e0310381ca014500800003480004e00a08126018031405000d48110710041159142880d0007400c0b056040c001c19111310b0021485101300344c800c030810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 820930809 1250 820929559 820929563
    0xc18030b0a06080d02071707270b040612030e15040b16020901060c1104110d150305010f05061509010903080f1308030a031d0a06090201020f0a0309140409030c120c 72
    0x54484d0365807907000035140c00c454090000190400e060703a84040714000780c4182a550608483c1d2100094411005c100c00b80041d4a104942c0c0c1b0742c078034400d040d41c0350311a04e40180700406400302c02d800c0c01d02c0c0040c03002030369000c802d200c5c3d0002c10203080c410680d00152800c1d192208812a5143e0042010104510040c080250301c0307031400002081079a88201c41c1140b180c410b2181103913140e208003c10080c0d440442c072041007030350103004949440d0400d8001c078141c1c500710301011001d0b6459850f01401d6900024480b015261244140031481c14148004010010f10540d030505003d030303400000300500c03013611020785029004130b4040e90004682d03081320340b98403003568400100d680c0e030007a40e6181d40010902002091600051920f6801c00b00c3c0300c60b450055070b0026005818140c0d030f40c030004207541f01040e81184140c000100f0120402c20100302158082c0e121107014501e841001040d2651252000c0c0c052400d00075154002500010222441588000c410343c03100005581204d0a010200300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 820932059 1250 820930809 820930813
    0xf030303110d0f0b0112020c0a24050103050105100b0a0905040207110907030b03010c050405090610090e0f06032e0b040b04061d060102010c020d050d0b04050a0f0c18030b0a0608 78
    0xc01462090340300083d00e0b0002c1c1c0340d0784240c9030031455020072070140704440701703a03900441c440c2d900150703c102b20090807103041c0c2001410705810000c20070480300700360000c0b40e00703a43da00140510150000c40c00c034020001c440800303141000200c00140780642600c2004c1c003070b90300460000100400030000e185a00320290bd800306030f24003140028003421110308640c0c082c1d442e182c901004180b140046405440d000b0b803071150117031111000d2080002001589034200b0040c0000482c494154801c4903014100001281c1c42c1800e0200c2018248200000c62003190000f00300e000c601c0b050038869105c90007202c41c1002900030081408280a0030b90208250b920034a000c4010035216440704031551035400701040480140c1d189001a400c070f034201c02042000da070100b000c800741c1c20303c01c6000704000101882d000c00d42c2d80107480070806694050b03440b50303602070f125002c0340204101485041869012807030800c17269903041d264401c2c1e410300c0d0301000c2c00b603030a6140000c0301440d203600810000c01128003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 820933309 1250 820932059 820932071
    0x60d0908090108060f0a0311060d02210604090b0a1802040f0903120203070804080c101401051002010b01140f041203030b12010603080901030f0b15040815010f030303110d 75
    0x6401089607209141403400702d81c4410110318039040913002c9001c46803015140e03c0c1040d065072075038020603602000050b070001c0100b0101c60742480c4c0303001034108154124055a404500c0300d42d4803441d0f0800500c141d002c0c610306103010001ca481080c3e030fa5004000000c0020303424480c04443e1444c0301894001039001802c08000c8011805a6401188814000e944014506140d0400c9109a10081c0c48400004003480c1c08940840c8045005081e500044c0040300c1d5080c4d0308248210580303150b00b00100120350000010003607030811400404c46520184000c0010103c00300020b8102507004104840f1110b000c100e0210712400d01c406c980141a80350b034126060000c500c0c008000e00300340400795014564224007810035807014060305040d00c1e0f101c03135118204850000110001c00e03d901f0804034039500c60305c0315031903038942851803c00003221700001a80d480c14196058540407951405008010200c4010030140c1c281c03445e00c40c00c1d2030b898500440e4602c0c806c0d01003091401174880d0220883d01d020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 820934559 1250 820933309 820933313
    0x70312230a0212040302030c040b0d060e01020d0b01020c1008100801020d0f061a1c020f12180f070306020f0906040f05090f040317251214010501090b09060d09 70
    0x2101402080740c07507508496190740505049100c9010303030320000b034069003c41d0001659203099080078481c00009080c41425440310b0311110142c50200c2c213003c02c00d9600140081184419028189140800380001c020100e042c2000c20360002c101c40789035007000081c602042c03c1c41000c40b0002d00074003040000b552101c664141030700042011505080c0c000f45880400180000014206201c600014403e1030030078000000c03188604114a50760203d4540c00c0224890b0007140b240076007a045058141b600c007a24114804855246c5415482e8015610040070002c0e000c600081040503664042c0c4090788585ca8051030240074019009615440000420f002c01c800c2c025501400495104882626854942000030391081c002502d002c4d00080520b85643c2d03121440c1003096400400e80107402c5171525503113444040015000468400040b05503070789180d006068000e403040f00481c81114080741d45000000ba1270a41c241c8074050000f60042018842035603007030151806c0600c502c1052000c0a140c2c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 820935809 1250 820934559 820934627
    0x6061b070e07090b030a05090106050d061508010216230601060c06050109050c07021c12051e04150f020a051e060f07020d110313030b04150509070312 66
    0x14000c0403110311003180000d00b01845a456002203a840741102c524681b20310080402a00008145010941d00c1c0c04001910307031280305951921501403040014000c1c02c070a0381c0c418a110b660310000c000c1e8018020906071462051031458080ea0181d801c8d00c246508a4444c8541c8203280d011032598001c400001425681051000c81054443c00d010407840c1c0e00c2c0c840d544102d54050340e503510350000c01d1013803800508242c222010300c54460700c004002031415940c1c0c0000d007503d5044240016034046541c903d0003101359290f034409030b04a00e050b810141000e5541d800c020b8a410304104001000c62032191060080c841d40480d00e8112050300d002e09aa503803400005003c0004501c0c00d841403c00081400079507502a500032161a4098680c42c0d40d60742e0125064000c614608070540420030218a2030010803c2c5800154401e05c110b1b002c9103020b041100070a10b140310405c100500300001c00c00c3c40007003c140d60007901c0c1d0201c40c6240b00c000400b0211480140c00d44131034280d8108607003241c824988 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 820937059 1250 820935809 820935823
    0x408010212180d0c030302071b1809020f19120818030f2104051c1e1119030605070905120c01090b03061c0c08060708061806061b 57
    0x41d4004640058031400040c90095025011110840d00481071614019104142500c021402803602601340301c110f031907410414601e244407800174517041404001c0310b452866220460308840b041001310340aa600429203040400a40a214a01ea00510021102c3c404e8400c3c003c1d00700745d089008104030300e241182441d40400c1901c50040f000b1854080a458009a0f400842c158180a05800007800b080540382c01a02484080040c10500001c2816211190540800c4004600c11204e021081c204015510303c0341e0484050120030400300d5010403682c141da070302105030a5424034094900c4e21040811a10140c00c02406039040c1802e10200550005548003656001c580101000c1d0b00c058030580e0b00c202a0342164042000030304100040103000b006580e0094015014203100c0344000750004450b181004100c980c99440d43c2c080c4201c0300d0800125910103110f0626444a040c490f0024100c030030f032a0000848600c4000009015489820a81e440b4194007064a00040803c010003615030b00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 820938309 1250 820937059 820937077
    0x302041e0501181202040f0605032b1b0332130b04120f1719020607031e020c0127151416020a050303040b0109050a090c060e040e0304080102 62
    0xb403c100084511040301c41200c040b29160301042c0c00548a6900344005401d5124121220940e500b20000d041e8a09205a205a1441104401104030720a080c802da4483c0c0e040c20204101550407111b901d1403520b182070705403642608010a6040a1380d109031605004800c1100000072140c0a03000e41c0400c2c98081d0a0f805011003030341030499120b0803d03039603a01881c0301d005017040203a070031907000c01c80c400319500c0e0380ba002c0c180b108182070751003001400310f90003194868070405104084420890b41031121540150241c907040c401c1c10801d40180826803504841100061350000d450b012081095105007404842184000c07500220030502c02c051801d503901c282c0320110114040f080c40f078030741c2c401c0000f10700d0403a6580c0c8007600d55000d451141400501c110055215010010307010900c204003840c400c0e03204039142941503050401c07100036030f940541020000350074403044000141c07000103480b003030f5101031505894411000000601400451a058115000010740401d00c10819001400540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 820939559 1250 820938309 820938317
    0x30c071208060f040908041e05100e180705030412271508042a0812031b0a02100f0609020417011514130207080c0d02060c18100302041e0501 62
    0x140c3c480c010b00c4181c41103414024080b040811091101030001c4010000d044c40b142e941c244200d8460b00801d111307060402c00c00001c11101c1d0303080401860110035202c601904520200c00ca41041d200150050001500042c0780740d511030000f02145100700480d086030005070503000c2200610070b901c044035810354010074641e031002c943e1000449000d40c890900480d881948a2000f0748250b03076a0301c08558462440b200001450b43c0001e003084c007001410700c50003000000300e5680c100511003001c2800d0850340310612843c02d01c4815842c940107d200c04079035080220124800b00740700346141c001c100300d0704040582403001c500415182d0001980607070b450f962600030413403038010703003036003030b1031001e6407080b03403c02541a143e5114604125682c1007450205800140c140491541c07016552b4015824004190f886200210170144c0d0400500750440144081d03140350040c0403001ea104d00050340c005078041c55005518440440c4a503044600500c40c0d621020b000482c0c03208000c0702d1003201d219141c005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 820940809 1250 820939559 820939579
    0x50904020c160915080a062d0605040605180703050403020f0a1a1f0303030b010201150b190f020307171e04080615010801090f1d0307060e070302010206010605030c07120806 76
    0x140c903842c1114010b0343e02d0b400c0102000c40d5035580b100f0142291003c071240c4100d40525080700389401900c03a414230002c4070004120b040c2020300344000c880f801c0d8491881510b9400e818804c1d11140800503401103030a290101d00765482e03040c181d1801502d0300480c1c0300d0303108646010b000d002c0050403498400500040581c7d0f90b49841034078003d20350508030b0502a481e081c82c410400039010741d10508414006000110b08800c0b03a5481c0d102283d010350204055140009807940d81745602c2c00d100082210301d040c4280d0610020070002d50b640203613038004100483d03114125071020034544c291140441400c0c1104034000d42c070701e40e1032500e41203481380c100f0511541010441c056019003210000c0d42e0181e441045c560b10f411102400303854500c6c1d115042c0e56580180b440c412030700581e084081c0c440e004c0255a203410a1a01c942201c900c80341e60380c11600031450602c01070381d001c9141411140545000ca07242d85611740840404d214004004010450600048803802d0f080410790b0320482c000c5521102c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 820942059 1250 820940809 820940831
    0x4020705070b0c150a0908030708041a16170411040209030c040e0325030804060f0b031506010f1704121103070c0e0603030a0801090218031f110a02070501050904020c1609 75
    0x25a425004000c07c084002c2c0300049105201d4100c2a9009000d06c0f04a40c000d0b41c401041c01c0640010340b80240c0000710031143c40d80c015000783d120340480c50907a414414034940781d254101d10018a004580c401d0b60006886019079030100044074203070317a0040040080303010f00c0c1c1d450303503880e803110024482c01c1c03000140120b130060340000740808454060302d80e4501540e46940e03c10040c00c030000035400d081c1d9280290480c82c2c8040003941d031050200030f10000103003080c00025090107403a003410020440345503141e42d0201d0309080707055003050703200c1400d82c0200c40c40c0340e085e00e0403001004010240c4c032001ca004400d0159001ca12011180c804001001c03640340c00081c1a00c92058011800114164000400040720300368010a48801d055407241d07102c0040d41e00080c00c201400240280d00341407100342d5100840a841190303c0700c840c01c00d00d5443d050004c100a0349500052088505024020821115a840c0c0d80c04880004c10300c1e00603151b4403c90140c14a900c5c050f42d003d074160291500b11240c0c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 820943309 1250 820942059 820942061
    0x300c170a11130b28021b010309080c07030b1008120f040e090a0c05040e0c2101090501050901050a02070c180f020c2413230d050703031103060a0504020705070b0c150a 73
    0x801320f9819070103402c4441d03100c50f201e1007000182d4881410185c1e02c00f03030782000c10300d00b02c0501901e01d9000d01510000f031030360401408040780038014040030b030031441040100140c0010380084a4001d440b0740c43d10b510020722081d40d44c2c003c643c000c00c04007c070750040020300e003c0400c104041c0380c41074256000c850385840a00044443c60030b00c87c0b1441e03014031050340075072810184030200301646503000201d8990545400d0300391030a5101c12107042c0e441c1c1c014880014420b019140e80040240c50440c204030050311001c07681801c521820203040714601c0c0e5200b0800070380e04000b446400c580025960382004d6100ea60350f55402c10900d02c1e0031a250942504000000c1d203441c7d0140c40720181d100c0d20101c1d2511784030340c08603103134400041c88006c00c544003208410901500e99403000c1a02c509840c0c044d01d080140039034550051903c900c940800c00c0004a03511180d05406548054070016115202441c12600e4a221a04141c07042d1b0b1020800411a040006005500c1d1001c41e0034940141c5034643e0f414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 820944559 1250 820943309 820943377
    0x71a04121e15050903070b0112060603060f0e21040b0307090b0a080609180c0f120a0302010605130204030309120f050a06061811030412300c170a11130b 67
    0x807c0c1515500040050314000304120710300900428002540302e6a030303070b1207804442d0041c0c9a80c0e4100c3d19140590036040d800d0045000211000b55030400c0b0a1018294994034405e501800110780d00200218010502c15560440580b0b1070030082d0307070b0b81c84c3d116038058200c0307004981152003201c00d440010000c14a2182d202c0c0800581d8005202d420408810041905200407845400441800413100c100380c1c100960100741e4000d4000040b020f040c801400103100c500340d10108094010081080000c2c0e100349007004480710f075101c2d0398031040d56192000c2d003001410005409482949000c41c281b001b284d0100c4100d8120b000e1080010140102c040103682000a91100030041400001c2c04650100540b0304290700903e0081c84c0346c0011101e2511604903d070108542e45445212540504410310804400450301e0400c0401001e2940c803c1c18015002454a8441a100d4000c880b0740201c0303205a038011145150030048070b0f902e55480001f00d130001d106003900050095138601211a108144c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 820945809 1250 820944559 820944563
    0x7090c0e0f120c0a0b0301050f031f0902010e1306090e0a0302030f18060307052106100c020111030c0a0c0905040803040f0c05040c0e03071a04121e1505090307 70
    0x290420450302080105505a410181503000f01001c1c09071a684144802010748001d40c58591254104414004e58203440104079010713600001c1c07200024031007104584a410f411403008666140188012205450390030030f070580141e191904008072581c150003c1c81524428603082001e14100c440030341d501d500100c4050050307001005010030641b04074004042003e000b8101890003401d002c0402c515034021a0f030100041e10100b07005480b64409031050702c0f8040e8500080c03005050071000500c070203101080361801e01c46144036110859010b0211402031500060580783c41d40c1100d0f40b402d03203403030307540713404440542000301d01007103654243c4501c0e400740b03420003107003411a55503030f8a14500c80c00d00007091342c01107501580081d117990b0324054130701c001040b5602d00755076051460605240440b560030114002c0407588500d042d00c0b0b00d141c2035508480d07410105080d2102c503403c2c4050000c620b12900c030010364000224009102c0018000364506140d540c042055944180449880b40104980 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 820947059 1250 820945809 820945819
    0x1110307051e090d0515100b1206011806030c080f0702030f030907120c031a0c03061009030506072105100501050d0b0306191409060c2101030507090c0e 67
    0x10540540944154501c002e080c60144549040041c50000300790300d00003081160558000c00041074007241600245030029032050120b185242090f42d05002402003507940b050001c0740400040c1280c1c81407602150901c444030807009515120140200541940c000f034402280313900d07010030300b510741c0142c1003446800725902450400702d4030b11001085034006040120148200d00000c140040c60030207841c54103120b0004100350790700e58034180f6811464200300e40340c1d0b81c12160401000002d48000c5070741c0164112014030b078103803031410141e84400c429040984980300360410840f1040c1c10070022501c50760101c50043d4545000d50103401610800c9417080040d080ea0322042003294000da014003511800d503100844ca0010200c040b0349014030440c1c28009503501d0003d030a000321200d101300610a041c1341001005c9103010591250381d0800641581a40000090340c112044000a0041ca0500284195142650b5a0706141b0769a240e5406a004900d29100c0e00e840114010b0091400000010384 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 820948309 1250 820947059 820947067
    0x130b0a062f070f29130b0f0f040f1e15080705120a0506010e010203040e0c0c0a02060a08070810030f030f0203041e0e280203040206160f02030111030705 67
    0x6003206105081400c14441d42c0b01d180004504400e484503c1405071000c80c018000200682d20007803840f9048090002d03c05404201003101a031040d5010302c1904c04403c14a41e48100c810f4a20005110343d4585d80c100440114002c112a00711003d204100e070b980400031083c24040c40150210f4251900c9050700120314514012401401007082d242c0c48100390804c94140f4030b039502981680c032011070f00120810f589408100180d83c0000400c00c00103002c2c40110308060074a030100c0624035010b0a40c1d12459800300707610803521410404202d000c1d601030103443d100c060080001d8980d003003e8410902084c010380000c1d40300a0f81841450469802010600510086807070a60701410702c500c44000b1404100004035219040c8846080105003000040e03410a1906503070548030708000c0c140b880b0714600e4050000503082014010741244041e080300590300d4441d803000030f0007031151814501c4803801f0407001d0740078082c4891203910024002e500a00014581c2e559251151001b00c8400011a000340 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 820949559 1250 820948309 820948367
    0x180a061b2a02010512071e020123040804080304081501150c080a0201270c080d052205270f04210905030a06051b1c020f09130b0a06 58
    0xa0070000384a0041c10031900c1c5c203900300c01c4004000030844402c0003041420b50740f1311442c1056414503000380ca80d407000300a114102c405101415080441c40016a00800d0101e01808250012207000700b065404882e82d0703031303910b859850b1502045041c084107078000400008a02c4130041c100144400140d03202d00d81c0010941d40d681c42600700000080845d90780c2e96051106d02400141410322880301001c104030001c152030501488961a0807e400c15081020440c03d02c1e50045d0136600e034100d0f040180382802d00710007000714001025601c5280d01c8505409240304071840c152222078900d02d0800c0800a654641e0344d41c826038902a02c000b03110007210980000d40c0700003044181c0c01410b981c900319200c0740c0c0d5100000d00c0c00d8400c90060360050354400a0107c200702a0180b62200301085000c24100b20241d03895110031b80c01940103092241c1c0002c0e100301205501401c4520b040001443d412520b5441d6804500420881c0340b46405524003a401049a40c0110594000459406610721102d01c40c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 820950809 1250 820949559 820949627
    0xa020c0309060f09090a0e010c03090506040201110a1b090c0e01090512010e011a1906020a0201050a110307030c020306061804080c07030b0c0306010f090503060f180a061b 75
    0x80c04642904140911412184d540c4502800e8041e9071400008210f4019845e110303030840e081400381c0030506107480950000128041816a0b009809003008100010200d962a040c82303c03a0100403e00e038210017610110141c00382d6001e09843d200e100401040c40da403601554811103012031580840c420ba002040b2324500394810340d840140800001c981d04003000c01140c2960032800c11050340901951011070303c0d0500d0064641040c04007144180204d140c1503020f500c60512000c040e0400400003103210107180131700114001380032050126541c1d4002c0c0d04008042d85d0758000c04911a00404000c0354075403621500041a0380400803240029440b03540d1444070a030701403501702209000d001c40c0080860f1011405c984102103e01100c1e0360713460444001490700403c81c3c807800500c6109070302030005031030005107a64081e03d0380f0451801512000f030f188840c11422800300210b44105800c0c47e00300903047d0820030300e07800c10815824078002c00e4102910011180c1607204070407842549150313540d00803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 820952059 1250 820950809 820950817
    0x40506060903010c1d0a061d03011b0e04050702010b030337090801060f0b0a05070614010828020f01080411040920030a080306010f1b0501060e0a020c030906 69
    0x100400140c075103100180400d00f5903840ca5294404121070103103001c9a48810102488111800ca0301c0104130340c24404040d1440c085c4084180c1014644c10884030151825440781c080c03000c16083c03000e844152200005c15000c202843c0c02d00a80c00c02d00400c44450050250a40000008010f541840310090b1614407080c0300110036000030305035402110a00006150300b03090919203945894810341032030901804d41d8405d0380010007000000200300602d544075000e55520641901d80140d07107401e9810715402400c85255170700440d80c20780d00006141c200024043c0554200600e59081505590314400e201007001100607422401c0d01d014140b066100d001c90702e40c071611407010511029840700104003250519030007254510610100b0000300d0040c80c0304490070040460040410f11565520003d040c000580320905028004c844200f01e140208000320110488084903d00c0710401d04001c0d02030304140c8030b4042e4000030030002c0740c13403a00079000710b0344034520038070007180f5004e0034a0500c0a00d85c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 820953309 1250 820952059 820952071
    0xc0b070f0605010b071a06030a02150904050703051816090908040b040605070605010801020901120c020a082701090b0406051602180405010b061206040c0e060a03091506080c0405 78
    0x641541003000440070302c2500d0207420002c102c141c8407120341c58588440c00d031948030100384130444420041c032070750005002a0503030380c1030310840c640f00d04020111013180904802258040e0030030b4200008183c1c142c0c0321a01c9009400c400902c6100007184a60712401c00f45079020100b540820706001e1303954140c0001d0318591041e411545895511800f5030416003050704038000040b4006008024800140620750151480400031403500403c10006000003c004c0714070039a850311042d1192455000340f00c000c08050b08128890b039a80560901074082000401901c41ca10000078080c0c082540b0078002d120591b110104048e240c41e05056003555290050145c45070540c900545010068030b81c0ea115003940342d01c141d001d4003541060700e01a400d503402c0310780c41400303202c080c0820450024a61820b6030803074020b840008042c000e40c00c0403900d00d0454940250010340004810079102da041d40920070585c0540ca45500d00f401841e281005c1d9000741c804c0700d00540c000785c46c0b02d459140903030250ba0011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 820954559 1250 820953309 820953323
    0x130b150909181c08071e2709090b09010c0806090a0203040c0506070f0605150120030d1b0f1b0b13021203090418030f1805040f0501061b0c0b07 63
    0xf80e00010814800002c000040001414481130102c4150000c8407401040601c50881d020584400d9001303026155541150040080e14403004001c0308901000e4006401a84001e203c0310015003040c1c0c01040040d1178405256280c04030045000b803050390054010b40780180300c01910b80703a107040340c0041c0d00068000e4400d2044964005169541c5900901101d480344940899452050401404541000b07200006c407004036040856107a034407106d140e102140c038200c0c40105420b42080c041c83c601034076400c0b4640501c6c0c554080035003c100403406840024559825851425a0108440d100d4180701462800400c40c2035403400910180000d5070b0003900003c8621a14840350001a48100c1b01003410b241e41d00006280d07285424240034904504021030b1102380c010340143e4004003d4000080c00c2c0c0304204010040700141d03000400d0600c01480020800e0002801b51405000100420300c01e82c00410403207040c10007550045541c0e08107198006280e00c0b2641e1a0072083d85c07865101403c219000c1d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 820955809 1250 820954559 820954573
    0x90c02032d03130b09010516120209120102071502090d0b06030a02031015080a17091914040b040e1b040e0105010305060f0702070f150e130b15090918 66
    0xa0030a0700036500c6006266080c811903049030502c06502d020181080c8826414941081285103000c02c89812500741842d002e140e082e441c0903844000c0c05102c551030b61201e0a0120440035980540141c20494080d485d407030f0850400411200407441140c241c5600081c3d20003485000c82d4680e0780055004d40d0140035500b5001e001d50009007480070300d101c106240c581c1c03174000c102e282c09042c14000203443c8840003040110aa5100e510200c01c0034821501841e80006001000e500d8103082800d40a0000e0328203034038540c480040c2d05000c01040c0140740114508400124170703180a0103440740d001e040e403002e49041c5894403079540c0d143c40c548088680050b02c80000c2c50240703409124882c0294041e5000d0210350034240030000101001a005000710343c010790052100d01c080401003021105001880e842c20481032409030f902501c0030740d44961101c02c550303180b00e0949040e04800184001101d4440c180001d8400202c1580200007045070445d040100046420b12400421800300c44003104032602d0b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 820957059 1250 820955809 820955887
    0x12020105071707141207030e0f010905060403060e011104120204050c1e070210020309030607110a0b160207050a06050f030a11040815090312151201020a090807090c0203 74
    0x8a50b000541c00c540500e1003403206103880c0424451300525404a045c200d02d40742c0280c400174a03401c0c02c00c444520514070780c14060140d038001c006d004000d24000d44916241c03641c03818141c00511506203051003035401c2a21012406988008450a0f51a03080145480704000d40a0000410004200c2090f10780d003040325028800c054081c00e15507ca0b044400340ea41c409030310612804254201c52074055500502814480e0340c3c000c030310075520440d2860240d848801c600000c503d00088844003800e002c440c0001c2c40300500485101800c8030701e07070342c084680d603940e184103010f1400c070710703200750b40001c0d030180114104803080c1070081d0740041302e06201040381c65000820310201e610503030048032f15600861081203400441035020782d1240c1c204019605000340341040c03685c440030041001042c1c0e20b0161650300c0390355581e151031034000e403e14003c544503100c400020f081500140070710364140c800d0300d50011711007065000e800c01c120301b660301660a202e440080800791500e900007900c41c15034540b105043c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 820958309 1250 820957059 820957103
    0x120c06112b110412030c061a03011401030503031501020a0c080a0b0a0603150207021c0606050a05060c0d033206011e0206010b1b060924011202010507 66
    0x51016509030072049200c0c00c80099801203009481c484424203080c59950045400c40030ba90444540724250041e03000f20340303411202c0c000d260750300409030340c03074429078000c1c1001410040d040918264003c0104c884000e003240e110042c04d110060032580308100186044459804900c156981801155031a5500d03a844910300c114540102905900004010007401021f4005540105000303004002c1c0d1402c6441e58290981f02d200c116131030507000104842191502c0600e0383e142c110005010a246240d4548803002d81040c0c032403603210712020000401c2502d0800112482d01c44404001e01000041c1c00041c0c0260140318000511002d005075190b030318500a81c140d050581401081078482e20b00000058903203141d0070808014104403204803d2101c3e0002a400d042d6000c0c0c00560307480300084080f180100788107040c01810ba018487c2803101c00400080c110586486009101c5143e0759100c080e0071707a03900240b03d0005c8a005200c004005940148028405907010340000307108202403a501d02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 820959559 1250 820958309 820958317
    0xf0c01030c0309141b06270d02090a090b010611100c0215010605120705190e0f060d06140d030c120903060203070c02040e070510030b0307090c050d06050904120c0611 73
    0x103152034008594200240e03407410500c2c1104502160780c5810080d8602c0000c40c400030110450700003400308107d241260742c501000b0315805500600b4030310503207442e0329610064165124110f0b0b80d800e09500124084c3e010703444951040c1da04034000c01412000035001c2c8042c025000810096000da00d0680b40c0400c0c0d0400e5442c06024292580e03661b03070341c441540c2e803000a4010401410884103000c02d0000b014018190046c1d0400762030310300d07031802801c000280c0e44503d1080c0720398800e00024a00d08504000e0f0018021244507111040d00200ca0f03a041c09081c8101c090000c0005501c4c0c150400044c148010600c0207450b5881c000000a0300ca540e0f801c05c030f0344191004004100402a81801c41c90b140c09024404455100039200c514900390200b0804038aa11145041c1515004808600d480422100e80117000040703052002084030300018000f640006c14040b42541004c0020405040003000749016950001213010350201c841000c46c0c10b103956400c122801a140c004000d00306030722002070 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 820960809 1250 820959559 820959593
    0x230c0915071703092b0e03121c0612020f010807260609060a2405070804030804031e02030601091a0405011e0e090613050f030d02070209090f0c01030c0309 68
    0x10954900340b4131030311460301c42003040071001904514070741345500040c40203c1103c480c0c40c0c101003119919120000b402c0410056002414400103d25408000740c14002d00b10040c1515a0810070300b07807540d5401441d075800300340294000c07007404040421544520b100c035074031500d10300d0308190b09010b010108580e83c00c918a1144244208802d010b07407850850001e6412a40032aa0082560f1400a40c2c0c04901f00d070b070700da0403c580c4c403e01d5000d4200d40030304210303401568020032541c2d460740c41e407400c0c2c0d010ba0010f000c20b989100d01c111107030300c540410501c01900c181e0010000d1038a60b1922400c5006020488984400140031840d8500b0329201e9000d580d011b40b8042c11100400312070013100281e070380350716445500c00c2d03001d00382440405140880c030103411800c003070032070400018a810110700d846043e42140c42617100010324010b45014641c05441d040d80f00321070104260b00d92181240c3c0d102d0307503404064003179040050b085c1e5031980243e00103c580c03541c6007008104068a42c0b140c1501c0c00402041d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 820962059 1250 820960809 820960853
    0x120306180f01030c0b1201170a0c0f0e0912030a0c09030f06050601030b0109140f01020715030c0e01030b03151005060a02031c09080304060e1203040501230c091507 72
    0x14410411403101c80b00180940005c0503060400030030180c03080c5041071080ca1403982d1803050b205142c031414041350703181c0c58001494071075156031410000c0c2e010060307208201e1510301200104010040c0840e031440001c900103800d60640d1141c01c1c0754401403101000b100c052022210000002502041d5441c144601400000a03d444c000e40050140c605004409042280226088c042c1c0400000c1907100c035042901c0c2c0c0031501c1c1c0c070600142e01d80b03d01c42d00048a180d407020b0340050095819000310035100120350314200342070303018401501030f03c01031641d281d4543c00c42c41c0540344414004044a90080107815419207881da038402096055002c3c43e1184016000000c0640c19019151040c0700300100f1601c040018610644030719089001c081c3c401801d0795295291a950302e80e04224010208640d00794503652820320380b4086009200c00c0ca0700c82881c1c08510b1b4940380c15240c1401151048100760300d00341c90b0540c07071400c0050380700150003070305580c0d0b00c00c1c4410b40c081142d10810b14404e48000302 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 820963309 1250 820962059 820962061
    0xc07091e0b01111b0f0a0f030c08012a03090602030702010f061a1902010f2a0905030d030b06070c120c12080712020c130c0f020f120306180f 62
    0x280d41055426140361141484094084210b01e814000380c40d038910020080d0103100300c0700b030000186113084900d01040d0b01545c42c10780400c3d24644d01c1c000b44126032040700180200c03170781d5110040c00d8031504180d242040740d962090000b4030402507000c2c4090b120720300d00080e800c05d4940c4c80c10100e81054942c20b0044c0e40d01c18054452101501c1820050039450f20188001c0300101c00c2ca0905100b80b9003080600c181d07005010750741d18000d401c600b03410300c180041404034080d8200030320103100c281072502c1000740400c030105010500400b240310550300c000c0e000d000030307241c11601500039007080c0b21107a400400070080a000715042a00100203400d007540c1c003005002c46c50410031100d000c0e03134002c5042070400d81d2401001030041c0c421180090340c411824010500c541400341d06003081070052580180b40200d4013001824507601075041100241c882c0c10b4212920241281c0d11100800c440440313600104840c0320a9064101440d4051070003040079466200e00c0c40d014052a00960b40b080e0821070482c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820964559 1250 820963309 820963361
    0x1810020c0c030106030c051504030605092404030e0f0112050c210f01031b090e0c03070915030b0a0b0d03030b04061505031b0f070506100e04050d050c0709 68
    0x1c0104028560110000c0c4a9a41181c0b54000c2c504840d2040c94840c85c0d480d0340740300c0342901e10300070f5400545c0c02100402103494060016a203910400340c811031906044280c12940268140b5017a004681690701d140ea00d42d00c1c40c044c898403014000340a410310400d4003014501c1c1086000b0544900304180c1e01302c0c1c948410801c55041a000c806071584440885010480d000c0f40480540b411a0f030041030b10340b040c1c081c140344d580e40d044036500007418090403c00c01c0c1700004030000d064288100d0940442d100140c3d100d1403441162164081495500c07604a410000b28588480340d80c0c120910481c0003608590080c000303444c00c4031403541140401d4541310002164581071207213000528900f14241000c004805009295120042a03903080340040031000400c41803660689880b19031015a0030b66540035802c02940d141d4080340d42c00d40c0341d43c030400d0201e40507107011029401550f0010003040e002024040588080c0c1160040060030b10403600d0001c3c0d6242980100005202018200341e090a140 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 820965809 1250 820964559 820964563
    0x20d06170d0c24020418150f06120e1006030c091a01050f071401020d02070203010e01090f02310e010e010b03120d060902030c0c072c1810020c 63
    0x1d01c0d841c0500005a00d04004682095824a44150b001c450840001d0303c410044000740641d40002c155081041c1062202000650000d02c2e030360809030581c680a40d07654401402c0003618000c96001900b2051743c0d00340e40385c542c0c000241118444059840090208540e401200c103107a00c26140041c0010003008003045512494604089241c2c107004134450302000a4030f20b07c40c11060020780c2600017260000e1003034003512103290b49208002999140b1401100d43d001c0c0d004940306901c00d518111008040080510900c9400d83c1c0c005117002039003c10b902017121683d030742e210050400100c0b9041e410b200001417900c0c207055005000000721340c182100c005003110a80303000e00c19141e2401102e004c030b9a07000100b40300c0d041c420345941b954400150f0b10642c050410307035101005040c004400c0c03108030110320380508a440a01e00484120340d954045a03202c01e400c17294403403400400002c034a4030400b46909460340c0500108000384e00c1c0300007040d03101c0c81c00302068503c503001503000c074501d2151602 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 820967059 1250 820965809 820965823
    0x71202060105100c170d020c060109021905090a050f060c0304061d01020a0c17030c06130b060109030f0b0a02040e190b030d120209120a0302060108060f040b06090a020d0617 76
    0x21850001094803142e61642c4c1404a0700761803a09017940421108036040450b01103440402451040d0f0701c007941c2d150701440c0a50400000080c2c0c24400c0c050480c8031520480a51701594030080c1082d001901d84001c0c4050551803541d001e40244081000380a2804104000c02c01000195101000205017040818000c501d02d0344490454009008440100e00c501441c10207503918150800d80e5400402015490351255403181c20071401090100301c540e101050b018403450380580c2d403545c00e56540d200110b40c10000c0b03000041001069120b83c0300481d04280704150310581044c0014500b03900c1d90f104100e0580102c1358603000045401002d80a00254020004000340c11b80082c0074840d80e022003c0c01c1700618844a0040d2580440e8a4113241c2d2a0414075106044c010306450000c0c600d4117000392118003d0040c06003d114903404a0f40c0030480443c0c40b88625003050140340309407500b00801c51000e10107005141702c25024407102410b4002449443c0080000164507400025803020440c10004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 820968309 1250 820967059 820967089
    0x30a140d0605120c1f0c0b100f0b04051807140f070b1807060e030a020108061906020616050406091203030618020c0c030f07051c0c09021812030901050f071202060105 73
    0x204a55801c03080540100c040e100441c0e01031f51b01c5200ea624103c2401d01c0120541c07166030381800f02034001541003107500082099031000d41d04c010301004002203000c0e00d44001e5030b0446c00110208040c0e0401410f00010784806003000da1507500d0803d844e1a0428400010b40d40c500caa0740e0292404a00030b442040345070000d01040c10403880c0303451000300290300e4010004019052051490004a05540b48240860300364051700764544000e4803a10020f64940045440182c00703034240d484411494010402d0f10202c540654981d0b00190500c2d25081a0b80c3c0e244c04214203050701d07001c000c01c00450042e00071440c06124600143c440704904201894892506e800901940000f101040d4003000400e405054030029260490804111030740321401017903900c0003801c070501d001408a0181499001000c10705480c1d002c102c0c0d445008010001c59140d90141008264010000e4041e2540650054003107080010f0202d400d1281e1526003a0f030060003414a070300103812041c0180200e180c194014000b1700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 820969559 1250 820968309 820968349
    0xe01210804170f010c02060c0d060308030a0b030d0e060a030c020f010c02010e010b06131208190207030303050c1323041d01050705190302030402061b0d11030a140d0605120c 76
    0x4010b4180a0f46a4a028004c03003034503d000034182027054004e0301302000440d40405429541d1401d008404010700d41245118428050501c8440c900c610a8203001d04481300208a00d03c1d000c80d0500a9000342010003610b0154090300c4901c1c1002182841960798407100c81d000401c040b402c0f0001c00b400c4030f01840e11580300e40820300c020030201da00c0492400c00d0344c5103400c1c0d075100f000013070078040654081c0c21200401a5421100c040c2c0d0703141c0c0403c078141124444c1d01c0901642d220b54030b0320349071400307070b44a986000c0114110820160441c61314150a0210901c280016550048085030543d8a2500700300c80c54907880100150b144424031401d03070300c0116803900b9424100100c0c101d011410a0a42182c1007540220110b4159900d62040f03404140c4840001c880d12100005c425032601e40d15800f220100b000b00ea440c042c00c2c0e030b0110031501c40031200d075590158000b00310311b40381c40c58000c12001050141c0d6848041800d458412803040042e81040080010b40c1e036000401c01440e094100c990984 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 820970809 1250 820969559 820969571
    0xc020d030e190803040b0a020f0714030d0c151a1903110102030307050412020102120316110f0a020910120b16030212060603040314031801150e01210804170f01 70
    0x15203c040151401e83d541030480956402c1c001408a10f4000b600401504074066410001a01d404404000600307100a50665194449400082c4da0182ca40c03c80503003c4403c0380401c40303014007254072010110850f01480d202d90340340b4801240441c64070aa629001c44c0350440c0500500030045a00032401d5024401540380d8070f00524020094040d0780700c1c18418540c461020004c5a00074070920340d000d05120216034880c80d205100716800c03242d004450011400581a221100c080880c141815404c001c008022548007036090051200d80200030381d00c81d07440c1d00c8020440d83c000407107061515000d54031090351410011398480045240f0f843e8002407510400a40d098100c80c20002940000112411512940d903030a090700c401210042c510745055000042140c550b41914824141c42e8488008000c640102d5202d01d00842c1c0314000d11441021080041040e4010002c218000c206c3c1182e4110350040103584840302038200380c224074030244495048203150070b01000b00d00c909000c02c078024811 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 820972059 1250 820970809 820970819
    0x7031e0b0f0405030a11010b060d020901030510050a0515070b070801061d09040312180615060302040503100902031c020114070f140d0b0a0b030a15030507150c020d030e19 75
    0xe248074145401c800c2c04000c80312821130300c03008c2d80640d040c0356005e410346581b4600032002c41c00960052008074007007890040402e8041c0c0701409542e05581303000d0092840f95060208105a00e8810100d00f2028507041044a0000b400440c0840c012609074403203089035410060080c281d102c15010072001404541700028450f6117843d14243c0168150a2070303100000509043c6021f400441c40703c2c8110000d030030840b003c20820b03600c0703580c0812011901d041425103880c41102680308510959905078004e40d8910a001031680c8022a101d10040403038610055841014226a10310a0302d000540d559500c0c250384072080486040c0c1c8200c1034a00345010b0000c001c0c016182081031074603d0b0810304085040d1661f04511350004a000388000d091a01c4a0b90b2610f40301856401116041c18403420a80b074850142c1c0c2e558400340c02e8039070107030182c9581810319000301508069031480d803081019440031000540c80c1d41e2548100517010f540c40c03d0307070083c2d64000d001ca0003004160459540346001000c202c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 820973309 1250 820972059 820972063
    0x3060219050c12070c0509070206010e090d0905060d150902030103060f0e100c1814040614031209130501080a0b101a0c0307051c0306050103050c0706050907031e0b0f0405 75
    0x200e5180d4440f59445240c1030401c2601ca098a401240e0402c00c4c52040c0a40707107800242d041e0482c0c83c00c111400403980c17810121916000a00b0080011854580c070900c03880c903005018011040c403940c00040d006e41c081c1501000a40c3c5a405060010340c00401813051100500a4412500b04a842030206401b00c0c040c441e641c49844080107504e598800262925611036001d03062a4042c1046000c0055101c41c0d03901d688241e2940907500ca01e18001c00062180d001a01804180000a003d00f440701c003817050000255000d44801a8000800c0754400c4c403144480c030540c1e018104480003882901d9241c6000450b1042c0a07200d400541c05086040040340a968016a54155010403881d101d125501000e0316600403458000c11902559114980c18200c03442d80400401140c0d40500103250b4800054085440035200b920310503000300080f001081d00c0e50085600001003008556905d5600d807100036031032111410404c10100400410780074071500346200ea4100c0580103012105040ca50b441070303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 820974559 1250 820973309 820973323
    0x9070506070b0714030a0c0201060e160f0203090a0303050c010b010306080606041d010203040b0f0c0f030a110d050f1e0c04050d050304080f0309041a0901050f0607080403060219050c 80
    0xc000c02d01c01c07030014001d184030b4000e0b4003149039000d642c60303140d09000c2c0002020701248501c50005600c3d1502c0000d2242103110024000c8803000b00401810001408c22035000c0b201401e0181584000c022040030b42c2c6410340810003c501a565058542e504078103030900b900c2e07601804030304245c10104140840080410000d810800032100000e00003041e0b00500320700c0c092034410381029403011003080140320700c840031144100d08280380d03200e46039100c80e1b568225000b920007030a0007050500c002007210105030b000e51520090401c0711814042114108025030700101d4010146219074014030074269040000c00b04c00d001d0038140301c619481d00450181e80c1380109c1c860a44900446a1030070140034003071007101c0103030003064252500e40c0f90491080b42da940c002d14000b400780703103060062543c0d81c051032a0200c007210300514446680e4038041c200404a401042000d43c080d804100e00c00004e600d0400801c0150300c900c2d000b5849900c050a4900d840307001c41440010320404200d01c105600740800c1e50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 820975809 1250 820974559 820974563
    0x30606080c1806300d090b0703120b01261605071203051b03040311010c0e09040b27150a05040519030324090c0c05070605030c1c05091c090b0c010e010204031a0907050607 75
    0x650b5904240041720840c00036000c8dc50741c040310800d88241082041103080c442c0c800160484030042a1b5082210b46115624016100b049409600802907109800131600541000851001048180e846405130380c0162003c5001c94000c1c0c00c03c0d02001020700a4148444290070442d0b4400802e80c04940b2802c00204010901100440000c0c13440121181d840c42440c4007603488a4030340d8415640650b9407018043c6211540a1074002420101316030040510941e400b00c050410703a0b0f0800811114806d05a05c12070900d038449031020300340d1524140c0d50903041c218019000c040c87c0741407000411505908495802c00c10395101c000041240024050112280d03458102d5803961403c108060034021180d01100a08410240512644280d0800d6020b8220401910f029030100000400000e003180001c001080c2200e1b4200003410125001d864070300308200011a600200046080c22603109400880c0d201e00103513480304100c0030700100546e101500f0401001814141000501d49004000300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 820977059 1250 820975809 820975811
    0x10e03070b0703200307080a1d0604090b15030a06051f050307050705030d020d0203040201080a090c140609030f031306050a23070507030606080c1806300d090b070312 73
    0xa0349200684e1140300c0f1a418030b0f02170b0f030303241c460750728003083c0030381c04407420f40002406049014890001402086c082c00c000a0803149004e01c1c00f000040548035481b580c9501405030010010b180d41500003c0d841034004000000c0c09a00700010416110304846901500c420545103082b0340030380110407650001c906007066a22803402c0c0c03400d04d1444c4102074062100500104d0242c4800455401941c01103100342c1311190943c0d603c2014030304135104031002800a5001280822030000c8004048134070081c060701261a00c0202008249072141e0001c003100d00d54000901502a600038665076000b03050035280c41480e001b07440c0380c01014540e241900031445924941b5a0305a03070308a00c11202304692190030749101541c0c90a000c80104010301c1100c0090003011840d10f01c0f0f141811441e40b40011407906264241c031200c00748040d02403000014581c182c503a0030b04d04000740b040b424028019412000400b00c03041d000744004d04154403076020585c04e1000b401009c0c0002d8001d080c880140e062180 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 820978309 1250 820977059 820977077
    0x80d0c05090d14100f290102060402040b1c0f120c030225081c11010c080c070c1a030a1401081e28120903080d0e0a080d050402010e03070b0703 63
    0xf84181c1042142c0f4444500a454040d01e00d0480707030f40e40c02103001e21000721413031840050706030a0070180800c600b10190042c0c01140001c3d00500e0554003003441800094400c0300d00404040d41da1402c0b00b40c1d040117545000440544000b0840420b040c0300b002c042e6807030903003800d40c4965000381d55840c0c10041d20304249202808101007165070700545004000ca24210b0748448480c4207a00d41e14403406a440c1c0c006040c141010a40350414010200da404140d0303180f00319503407241420102e640085030111502c8050103000214101074042d482a010410f12000f640c03401c02c0c80b110030868960743d11040c5800414001002644030103d0240a546840035080c060100e00207400381c00c003541810201c1100c82704451036400b81040690909001d44a0780080003020000c0c24140c036640da140c880200454000c00500145650a40041c80c0c0552000f044850f84101541c44160740d80040f10041d0006a4460401080d0b42e4804001000100150098101d00d4100407141006210b1401d0180030700007100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 820979559 1250 820978309 820978343
    0x230a0b0d050c090612040c0603020c030f070203160f2306120907150905120f0d0f17010902070b07030501080d110705030f06012615130f080d0c05090d 66
    0x1c484441000400403a580d00e242c220844089009480a0b07a0090601d140840e23100d009108458400940c140214180041548042800c2d0701894049070503000c0c010640c8022001d403c518409020b0807408010210b0410706c82d81a40c61200103260f25010302007420039000c6e00c03004103e4003442840c4130a07031460b507910000c0300c0c604685a40201c112440480c4284021940301107210305861088503a000001013030010f181d980c2c0502101d14405d030b08498442400d00d40900072645071100302d0b050425002759141e040300e0071403800b40d1011000c15000104041044008611a68042c11600b4104855410310001d0341d681d800f046111014021059a80c80200d4810000c80c0014100103046501c07050700178403890380b150070030312442c1d28030002030980005001f0700511885280408100800d040d2006001d21200d006020b0200400c4401d2010250042101141600030702e90007400100d81d6100580100c100300c81c402074006041041c140402140c40d40c4200c880201d058100300d000106e8103203c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 820980809 1250 820979559 820979581
    0x140703090e061212030a0c030e0601050607020d08030a15060302210c1303060c030506030d1b14030d0c08090106060e06090a05030a060c021b2413230a0b0d05 69
    0x203502943c40b4031410000032100c964080045200d55403169045c41009130040c0705400b5600d4003850094242c21030401031203d403d208002d42201c7e400208108000c2c0c14645034119603503c19178a284001d03480c2ea5200703881c6503410f4003110080a1703914046250840300003034a08004d41c020501e4000c103420501041031250f40e00165045c000021510304a400c0d80c1e441d100d00141a0040c0030400300e410800051164a0081a0900c0002d104d858840c3e1032403400340c103002d4080304024104c40c044070700840030000103820000307850030f100072030800901013401c0c40b0040c00424004040f02d58070303030500750144070307040d4001c0009000c903801355000c94035040c6010014070502e0140d0806605031060004210610240d0b800001d400006038084d40d002c04026034403d0f9050005821898111950960280c44040e021803500c0d00040c050310a035080a802840c0d490070300c0c10641c400c0c0b10450103414140e0030413049804005444400301c6070151380700c1c81c01440001c0d600450030a44501e640d280c00140341c407081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 820982059 1250 820980809 820980829
    0x20d0e04060510090f0b0702030304030b1e010315050c091309060905250b0403030e011116060c031205041703090703020402040b07061a0303041203020c03010204080607140703090e06 80
    0x2c003d0007900460001040205410b0345807040b0a03052503803074000244d0081c0c00003201d1169801074091440e282c1142c464840000020749401c20401d0b0808000c0e03800d031501c1d01e601c0d0186100300c041546c2d041003207900c0c1d030640e080074200407040c10003085a0340007503485050103075503000340400105040340941060002041c00310701c05887c0d07000743e018902c40c1c205054007200204005441d0000026201c040107000fa00403408000d000c80c400040f030810541c01488030510501d40d500c1110895050544c01c203044400940c0004049950041c48004154005d10303030152241407807404100c01d00d0705865010300840c1c0d801401c4041075002010802440040c0041c1c0040c40d009001590386a40e034180c5000c0540c04800140d600034505950b0301c920700c3c0d90f8041d1088080000300214209410300e40516020040000b0481c103502c9010b0551030385403403e0029000500d02c0b5405803580b4a0400b1002e030041c40c06241c00c01c1d03040002c100d25000250440303100b50036101c5040c221b1203540e031017402180891071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 820983309 1250 820982059 820982069
    0x607030c02031516121e020a11060118090f0f031206120503031b0d050405030904141315020702040f0c020609030a020703030e0111011d0c010c050604060203070203120109150b0a020d0e0406 83
    0x50385070700c3d981d0900e20747d00200380b4009507a50302e0300c0b4001c4d40c00c0e40320346402c400c0c0a401042021844000ca1a50a5030028503006014040e000b1450645030b540b1760000d40d120b40220041018020f12078908104d030721419000b024011040c5841c02d04e04c1d9921070b100c0c0b10081c22001c20b040309222802070010800182c413500b6404440401850034282407140da66040949810f04c80d41c20000c0303003503e80503800b8006016160702d0201d419240740315038510703040d8414a452425182d509000d007202580c2d690050401084400c2c4002400901000009040c400e0040440e030b410f5204000c42e0301201d900090540c112505850803440c0100daa01c0100c8146c01c00c0b040410080d800c0c4040d0302c000100040f000103032004118100da02005100b40103403072034007480c100030385560041c000140116443e40c00542d4040c4292040e240740000f15514002c00c40341c20707040342c80e24503503500c1d0300e51300030320400c000801400c24018501c1c10010b101c80001e507140072480303160b82041982c541e100c2c190f07240c036004000940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 820984559 1250 820983309 820983341
    0xd030203040f0f0305210a0f02190b24060a0c0c0510050a080603060606070f0519050d02071e03060c0c020a0902131401050a050a05090607030c0203151612 68
    0x1507640c00f40c0b0034044100e400142c2e0706019a081c0039800030f800c0b030086035012002c0854541410007014040d521090500c100000b9030146013012844000801140d001c007512a104c6110300707081c24000c205c0000c40c0d02920354a071443d02621044540d40303035402d4078111001440d0030850b042d19840c2071345c0160403592016401650b08081c0c40c401303a411101a2040710f94039502c800741542c80c007081641c0d5030025200503800210401c180c0e000304500c0700c146000903008004450320100036052a4140d10790007503050740c080c0c000700d03c80c0c0350403503046c00040c00808062003500004d0062074401da811950b40d21000b4100da50b1120340c1405c2030300501e001c40382a6001040c4408840e80c0f11a510041d500802c200b04001d51842c102240c4205011504040740ba0186e50303842c01c02030002c1b025a40c5030b01007001030b01807003c144860060b96032000001d14400b40f1130b03560401d4604039441810318121102d007524005084880070031a00d40500940040550f850307203410700141c1340642051004001d041400c406030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 820985809 1250 820984559 820984589
    0xb0c12010e040b16080105060c0133060e010e090a18080a0e030619050c0c010f0b0117040b0a110f040e010f060c11040b0a120b010603050109060608060d03020304 71
    0x1001c6211540340300d50b014030201c1d0314607078030a105402d800e241c600c44c040109044100520907405c04a0203028407030000c000001e2a194644203ea004c84000d0004051002021511001c007a04c1d00c0403000003401c090408002c460000030000c1d110100000444c7d00581d10280000d9080409400c0203c0b1a000f10001c0c5100c18218146101c0b035901140e143c030003007101c00303a038646142000030704188035003000950b0355030204400980c94060708001d400d100b8907036414051114079600071311640901c01d803030b00800102d140407040098132109000301c5450b020f804000800000c138015001c002c1d40080d09100008940181621a29041c0036001c1c1d1111035002c0414081007003001c5130409810b80380042601c030704840d40c95004031006501c0d003c004005c820046400981c0741855080140302100c02404003c0494482e400120960502c0c00b083d1403045e0b01000410500c0c0e0188501409804031403c10701104d0f042120140203003c0c0074100303d005005c030003203040500d031007030040e50094800301140d00c40d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 820987059 1250 820985809 820985819
    0xc0c0b0d150b0724091a060a0602121617070b01090902010c030305060411160b0a1e0506030a171806090102070b0d06120503030405010b030304051509010201140703230903070b0c1201 80
    0x86d44d40e000c0d202c00c540d809100800e50782d01c0c0c086907101c1103480030b074010000003090603074000319500041c880c4060090316074010400150140f109030b48500213001d44984500c0c12b0709104410643c1a401028080d1070030200c0e0000d80da00900c10f034811b0ba010704000c03450340c980402040c0100751a50b0080401c080100d0219091105402c200c1c00e09070044102803156224040c0c0300c81181c0d1400d08145915204140b42c0030581c4594111a0b80200c00a0030390300749062544580c40617620356620480640d03000140c0c0c501404940060f00b04144058942606201d5031030f00103507503540107008a11201c1000b050b507508030704160b000700e8058641101006002c007072520300107a480c0c01c01d0b01c0031550b550a1035958501814000191400c46000903e0303000303250140d00074010503600580c07140341155280c598002c03102840104860085e10195000113650400c0480841030b401c0c1e60054110040c01c01c001d01c0350071000003064813030003600240415256103030039403200020310829052002002c001d03800004e03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 820988309 1250 820987059 820987073
    0x3051e0901021b0304350d03020301030516050102030d1a030307050304050a12020603010e07020a020301090c0611010203010e070315030b0108010b01030f0203090d0f0c0c0b0d150b072409 82
    0x100056484514080303c0301d010180d45a025070f014007280619100d440703c4084c1d0a180422450800c002200d1003c0c421596100d401d2042c828094004203800000410030082e00304821403000704035981103d601c0d0f0601000035168801c908031002e01d02d8685209844414041e422950f440030024101d07a0381c0d140500d481da40305d41052040500c2100b00e5000026071a44681c2c100b4482503005044500d1a03081420312140c144010740351100b18440d1448540060f1424498860b10710300079402d00642c2c4d032404000400c440501848a0120390050004114000c0900c140b1a009041030a002c030f041c81c40d42070b0758040800d1550000d171510810307000000f407400040d0300820004000381d800307004001c8050000400c0e844203480003019548646442e500c1240725031010800d000c0c040c5052901c6905c21b4880c6840d0400b40d820018040a000407107107070013000381c031038140d241100c0902c8800d041d00c0c0c02d28469450080c0b1101415a590b482c1c505840803c0d118505c11411959150130400d184682c20240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 820989559 1250 820988309 820988317
    0x11070b09030c061f1d100e2a04230306011203020312040201170c0a08010b07020d0f0303060f090506090708090727050702030903070602010e121c18060507140a03051e090102 76
    0x3140383c61406001084849501c4000c610405810340b144408c1040030141012090b0203408061805005000c040f49c101c2c80c5511034102d10184564603620400100200341c282903040c2e2204454802045a0070002034020068601c001c0c3e1142d104440703a561303800181e0398a80301e8000c0e181201d02a138200694201c4600103030107402072599544941d030303803503102e8041c0e00e124002e000b96015000940c40d10024024070700c6680218031034a00860750907a544100b0a01031070036085050a1903e0f1800c000c40c03410300c8841942d1062407407401800c40d00780613500c00d46600c4540550882c00c103640d007150000ba4a0000c00d091030a502d0b0100b00110b143c6100029241d4000400c100d20074025040000713040c030310500030142040d1340c00001d8541c1c20040750b083d21555004088220b0303034449040c4501e4454005209955590038558070f120024966450071030200c61008109100303003c00038612855440c010f4007500c0100d446410300080c182c4035901c01100300c918081b2940d90b130300c07003240c00c2060584064000d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 820990809 1250 820989559 820989571
    0x209060318012007080307032a020c0904121103090a0e07020f0a080901051c0e0d09080303190b01020c091612050c1806040911070b09030c061f1d 64
    0x2041400706410721070f54104051205140d40c3c07141800480081080380004580068a90400042004121b02c3c0c20080f1807242c5a0481c10403203800003081c8179501031080300241d02040340c0c0340600d0311789a529000190f03000d0041d60100010903901c2e50050b6420400c41d0300c0300710300400000702c85645149101c9001b6084500d9030040c000c0607003c40948100040290700c45900190080c1801d40403401100d080e0010601c4100300d2810601030000034505118804080130142c0c06041161002e800c040d00c4000b46034018141640200100419040b96029080010003201c0b40072400c0c20f80080100d142070508a070099111a10a041c03084900808400c402c0c620035680300d814823034081540750301c2200c0c02100c000c0740c5010100070009984100200403040c40700020074050500351075200c8601150b60188012005c04000201030091003007400901c1d60110050000b146840c001c03101c420f480b244d000e010b03a030000c10080800141d4998005c09030300600039455a00703400d0a8014000d07004420b06480c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 820992059 1250 820990809 820990811
    0x603080403020f01030b01020c09060307051e01030b031501060f1419080c040833070302071506150309021201021809062e09050904050a02030f03180f04020906031801 73
    0x81028194004d000c0c0304940a0141c0181c8027030402103092244100c2c00505455140c054030b000401d803a900c401c004540f80a4180f000b0302104d4880c8009030803980c40045640c0719500003c14154120440c00d11181501e94902d04151440460719068900024511502c4582403002c01d10021107542c5008175443e0481c550742d47c003020303110240c0044d0301c1c1c82103020700f903d9030300600360405a03d41e00c0700c0c42c001c203c03503d0801180500c480c2c0341d2284407440141c945070006500000e4190501ca980b003002c0891140d404010414507140c00110044d03142c0d43c2c0b00071024191200301d02c2040d5510183d200354020ac90314000e5545d11040d1001d160046030324020a4400c000a901060301800c0034042e0f40100c210340c507000a4050700c0503464805c1c402a4500c00c0c4200503802e803001c502a12199800c6010714408d0303000b07240c5024144100350800115003104082d907401842540182450045070103c03030704040e1412040d1b11800408580607109a148213a000040001404112a5890303d03008d600c604080c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 820993309 1250 820992059 820992079
    0x4020f060405031e030c0601030b15090f0a0e010f0c0e091812030408070c03150507030b0f01110f150f07020a11040209010c05070603050a060b190c080706060308040302 74
    0x81003140c41e01450180703e4040d84074081c0a051081650070500c0c5602034442120700b400c1d54040402e20b0050260001c9844407845410b003e8048035200c0303180c06851080394041d85511300003242041414008204000c52500c5200320102c8000070360004048081404081c00310200445002e8248405001305a0140003c00002200c40d219000403110030541080a0100c3d003802c4402040240c10180090383c4160081225900240f4100d070410000c501c120040744c99041013000410813228010000380605040811240442d610702000400320042420070001590103a2011407811103000305044aa200d000041c240c44007240e01010722a00300320750300c2e511a9503109000c82e191908040010468030040000800910301900505200001850404001032681d240d09147c03090b2071340a82d01003a52842070103a00344250045d180544655a00d15240001046850b88512052010181005050b200d900c040040580498007141d81052017800140c1d101d0814850035407181c4801c034030032442c1135 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 820994559 1250 820993309 820993339
    0xf020c01170a05071815170411062a0604061d060408030411090f0a061a0306090a020f07031d0103062102061b060a0e0606030a14030405040609050402 66
    0x41c500801c1c40341c2001c0c0300a603100d02c0c500701d0141c40040c0209042c003820b00b0441d10000e4604840300700408400c01552400082d500c0040d010400714030300500e010a1100402c03010403c018260150640d06451055444c412050f0078000800c0c0d00881320750794074203000245000040020518081c60040900b0031a40c140c400340a4281d8500f00c00e25a61078103c54001030105040c1d90103164058001d81c07410280420110004007000320494240801403903040500c184403d00e80710b118090003024400603e05d186002049178940030040c882845100c0780d01c00a04590341540554140e40c40c0384002d0350b140d24032881c004c0c2c040c1e040005081c1411000c510011111b610038000e000032212a010000b22448400080b03801210002d00260303000007003008024400103101c00300b2252a40000c024002905141c4252015030344204411610b65220760701f1b000490b0b401285000c9001e034854030441a18004844150a6002782e40c0410782c0145490307400944064650040b600c04d500c2150100c164190328 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 820995809 1250 820994559 820994567
    0xa12030204031509111f0305060405130f0f1a181f020702041104180b100807081b1204110111190302010b0910170d1d01051201060f020c01 61
    0x244000f914002c0b1164400080f0101d81d84004680c5002d040880e05a031041004508803800c40340041301c000c0800341c0060b850301e0b40b520580f40c01400c00ca4040c005403e01d01d0b00b070890581c0c1403401400075000f02c421300c02000452415184e245622529211088400c508034ae0500320040b075042c0000410542484544640812121071311100528102219086c0c8001c82000350840e800880c0c110303a491208106000c1e10502a20082110350780400f00c0b103580d10512025103c0441c059402540c5450803d564150001c1215034482c0e05407410314040e0f40c410003042c001801c42c40f449080780384001520150001e410720801d100703034010703298104040c1240e030044a03607aa52209200c0e007a00440d9011900f0703107828140082207402480007052411402c0300241120038240d50405600741c07404002c1105010466035102220b49000c05010880c5400f600540b42c1280803210484d840c8081c2150f91541e802401a92074001001100c2e06181da110000903140c540e01c0604100036110301c02545215600c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 820997059 1250 820995809 820995817
    0x4031a0615093007050d02060901080615070506160f30020f0c07050d1515230306100308070b0603190503071b1d06150c0a120302 57
    0x4041d055080304511201c1d184400d802c41c080960380610a050341008050048070558210a45001d40020061404042a103008843d90000d80a14120750744000560b45203c2900e0040d46c0c00e0030003e42d00d84c2e2300c00014500c110703000742203416000d012a0b90018042c00003859842481c41d500190380c41c202d03d0000303460f101c414150781c000017030145440031000e50b08041c103101901c2c80350792344100201250134000283d82040c03c03a10071228011656081c619410440b0700300520b0255520743c106413107500c514a82379074041c07080c03821a4448415410b24459800490010310880c1090702c08010204800044050f542103054420300c912400300700422515840c0381c0031242c1c84140c262909130640c1c0d4041d5a481c00a00d002c0e0b05000d2200001800390010b014165218802d9000c2c6540d4101440d25103180760b29010300c8240c3e40d104500c10702000c0030310f40f9041c0c100902181241801e03070f0782c1030000701e80c50114060f032000c030f80004c038400c280b03035038006944c1c2201c07842501c0e2400d0f43c000c0c01000b2012402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 820998309 1250 820997059 820997071
    0x5061b0d12140c0d0b0406150c021305070903080a1e0806042a0305100f0605030a0501080a02010e0d170c03040503070b03060913151514030f0318010c0203010603060204031a 76
    0x3c104a12000d000071a0b205000448000c1c04c0814110358130000031040071000820100032802c0010344608618002801e843c1c030900c9203004021030305200ba402801c0400324040242000800507440550138014030350030702c0500038120100d215650703586004101c000191403a40c0900c0c18104211801c1c511040084001001c801c0107510290f88028100c000d8140540031350001405050045000c1240c20010b0000c4c2040c3d4440603503078200105620215001640f000040f9004442c8400060381d0140b0b01e90160241181d041010f80b503103013004160310002d08004d0800e81e4000030bca0231340400100281085030f03022401d03608a00d40e5901404490b00c412200107030701c0007007000040c050120f00c030582d4844a0140000869803038500c0348100c212540207464010512450808101c0032421211b0060040400d0f0090107001c1c82002070a0341e68081e1801c14044403001c4e09000c0800d034031401041400d9038004000380b003240c0d903a05010000b94814001520515840c511211303030107030300f84a010b000394 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 820999559 1250 820998309 820998331
    0x150111010528180609050f2d030d151415030f101a070c0b0c0d120905030d0504110108010b07330b090601031505061b0d1214 55
    0x120018492052103a49900345080c00c0d40e80700f0380301110702c0c0390f81070704070080381326880000f51201c0d20305006241100c88415080c0d507501c00056110240c051114124180e00c0d21001c0741c0f4039002c075a151500313502562042d950054944850503024180c07002420b411503103039901c80d1982400c4501440042200a1400782c05d0103010000b1484e44a00208040e0303011081c40418603000307480d5002001104240d046081100c500031990106101d4070041680082c150136008600e800300c1d081300302e070312030500c4001803003440003143d58240c025085800c565a940d50000c203490740c500100000b01c00030141a5019504901824800b8030554050306607203044c0c90303148094d41d081c10760580ea40f2808401d0781198205000c41c1641400c04034220310380c07294088140610102e10010b0401c140041d00c400102520304040c10320601111f40c0450801c42c0f020342d10180d4540795a40d0b0a11054842c19030806c00e800c00900c180c420103010154030061402e288000350300c0c02d000e580c503c3c1c1060169071701c1c1035800d010b204c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821000809 1250 820999559 820999591
    0x6030c0c02100e15041805010302030a020d1118010801050108210d1509090b0603011b1805060a0206010806010605070b070503270c011e020705100201141501110105 72
    0x589040100c903640d2150b0340c5043d40180f00481d001c150303041c00c0050a0450040d001c5418406140440482090203000ca50200801d45c5076800280e900c3c0b6516102034007034220b552100f802e21a4800d111911240d010304084081c040c040c941c081c2180302413140303500075442e0000209040c000880c0014103e500c181442c62411110300d03407941613a01c80d1030300400c210340e1000740c40070091014841c88028141c58a00052003685400e10107145400100303103d1190340740000104105c1910b40c0c01d111883c0040c80d042d1003000c0d0300440004040c006400055000c0c1c03012888090b055030000c0c1040c103072100c5005039905a44d070340c04280c4003402062001850300c46221700150b83c581c41a000741d1b0340040300c07000c003401ba4107400d4403070642c4019061004035250446003122519503084442540c0f0b05008030141840c03007081082c000c0d1103c00500403d0321412848201e10380300c0303200750400d40b0031800c4070034a0390050805003d441500c9401b11145400f0901c6044046103010061288c107102d030100d1404d0000c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821002059 1250 821000809 821000813
    0x14090c030c2e0e04090f03080a050c0d092a03140c09010e062707090b0405030a03030b0312040608060a06110726061014030303041101030c120c08010f06030c0c 70
    0x400c280d10010764007041070380f0324124003a54844c019510414010503151105503d1401d000344022402050b8030852410003050090240509081346d900042400c2d0016100c4030300d107400d02d40400d90028030301958040f9003119022144280040041300c0c41003821026000d400c41d146074613404040070240d07024058500402180c0c1c01310580990100006210b030414030303000618200740c6042c107852489401c1406040110494118041501414000082d81c0c03c15141c0070000f41e40301400390008041644805210360191001c01c0901401e261800c130550b1a1900c0d403d0007071900e5000c0f50218800d43c11030030001450f9004040c1c01a0701002400a803c400c3c0c203001004401d11400e05c1042140344542004c2d03143c200e0180040c0c1e0040034440350f4140381030b00d07001c0d1800c0061a40c00f6040d100b90420002c2c4400208448809852100282070118800380c5440e000c1d500726082004100c84242081c1e8110300d06a0300220341c1d2b068801500208040d035450310800c5048548000840c0e003caa580305141c80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821003309 1250 821002059 821002129
    0x6040506060d020d0506090d1b050a060f0207141c080403051b121c05070201020a020d0e0a090516030f0203060d14011d03030114190909050114090c030c 67
    0x4041c600250800c032130300c03240303a4505280403012540035440c0c0e00300096003e12181d000b001f032a00600c500c006000b100f034141d11600d484600c11900240380c41d9640044440d8528150143d485554024255804617100b41d00284d4540d8086034000c4a21601d9500c041c050324012071203103008a406941c0d01d0f060541ca044a122852007080c140b07d43c0348140c002001d00c00e928080100485c0082e881c06110741110014114141c40c0c01915070029640141f1030405207030760026155801114504e020000c005040c0e01140400e09d4540040f01c59078142410403a0760501480408682001598200704070843c0902d0a0200e01082da07025512034032240020002c2611191182c071035200d600000180c013001203200683c1c0a08103250b0030882e40001c801000705240c0e051407060340d00000d0300c0c10062002902d100340b9440909004070455140c0e00d54402c0148102548055401c1c08044084291401d1400b41c0c40e603035042c81d4944605c648116003480c11142001c0c020642074801c0320103d15555554410800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821004559 1250 821003309 821003329
    0x310140102120f0a09052403070918020a120b0604230d03030507091d0a0e0a05101a040614040504080c0703030c06050a0515060d022106030601080604050606 69
    0x1811440b914950380c440403508401406070703105080c0500d80c0d40603401c001030681e02c0e01c0d50001d4440c221880107615802800031001941c4580381404658035510b18100751240903003a0400c4c4045002c90502041c0b10b581d941c002e09080c1020b890700803001110110b41e50684035071103095604034a00f40400c1200048a080d11048a2802550a44110018000300d8035882c4c0340c000030f0b0000307a115400d11001d00c0d00300483c00d024224021600340100140c40c1d00e1062220003400c1c0da840e007540ca0044030b60a2070144012102294080b0541c1ca41c0c9035114003190141c40001c100040103c51010030907078a03e09403040f001140c81540c880d44a490750742040000800303006105640f40d0380100500300703e118007070044c40c000e94403c3e12100444c030303080e040100894070024030f810072052405043c4a4401c800b030744950304849080300c400740c0ea041140e181c032019000724000e030b00b82d0040c00343c1100540d2906c100d003c0c1c4107110130ba048079020ba13079800415540b80c0c01902c01812540141e0046440c3d420202114 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821005809 1250 821004559 821004599
    0x608060409080c0a060b01110303060d0f0f03120b060909010306020a0504050a0f0305060705072604181e150b0c010b060d020a111612110603070507170310 68
    0x1911011502da40d522a441201c880d22141c0000c10050100506880340c40104e030001c1c40c20301624541d0f040819924417010f401c191040c6242e011020030050114060b8403400e03441032000003105150f103070151496500c007803800405800c1c612010740c0303828a035043d0b0b90702100081a50403280d04c2d41d1a190001d501070381d140b400700501000003050949038400c4010041c001c82da00c00344460700e1820101c2c2404005080e010800404104440109901000a00f44141017403210141c8000c1407034420780f2845541c0c00107603022100c602044102e2040e43c01118000c41d040c1000d161001c0c145010011940814060006600c1c880c400b802809803082c0a401d1003211200001405004100002e820790031000c00e145000d500050403264155002140c580f01d0003804008140d0135240805000740e030400c5024002980703000f0a600010b00820b0301c2c1484500c0b40c041c0100c0c7c0e403818000c1e001400d56000d90300903140900f60f115228851300b060400c81744500e10000700c121915085c020303100f614070400307170030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821007059 1250 821005809 821005811
    0xf0f030e010204050a0810051b0306120c1e090604151505070c0e1801060e0a020a090e040f14151501051e03011412120702010c170d061202010906080604 67
    0x202003500c0c5c0b40c0103081005054610010a00065208085400e5850007800d181058010040224005074204203980d0014000c0360510340320503e0f096550b18150b041c03400301c2d030721240f072003031a000e0410b030000d001c4109601940d40c100242da4a60921081c1d42c2c81031082400e0b42001d81080080c00e6101d56842da074004030749400d510308800c0c0e498501c10b020441d0024040034580d802841901049042002d2860103000024440d00d46421585804154028010440d1540003e92805210310039660180a40014620030380c80c2e080c0b5040c1400c20694100b000c440c1c0603240c00303040080c0140018010f00c0319030641c203203031459520074640c216680300d06080d4906209051000d400c0b0030700d40340b451694000b0301015040d12585045090101c628440481d82e00508607488140d487e41c2002c24140702a12100a4142d0384405920049403281010500036120f13112048030b0401262215004011a0980174020701ca01c03a15a1140020040490002030100c0c0074681c040000740d000703c040726031003100148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821008309 1250 821007059 821007067
    0x62c0111010903020105060f1f0806060405041104051513121505090c010e040207030c200d031805040e0c01030c0311040f05091e0417190201021206010f0f030e0102 72
    0x35294252100e5000480160351034408008840c2800002c94664060032502100700b100e503494a4030a486130007129100f005507100000d00707641c54088c1194020100070f80100100400598090310366000360145a20400ba005990310f0600b108c0d4050703404192141000300c821510f4058826050184100102c0d05901001e030301400c841c4952081c01d1081481c58060650450301c040010106070310001c030380d44030b2407040c003802d00802e03440b200c0e4100c440d074007032000c92842c0a14050b40f00d50700f046194580c1c0c04030300620032030105075120b42c00b802d600c0300810603140e1481d141d10412050f0380036045a10b41300d60260401c03d05561290300420342c41d0b080e500b000505998068103004556105402824810303980d23690800460500101c2d040d032200c510990020648081c825035401d180010707102408c816602d0800609e854286022140114000b80d03901000020021020b8041d411200c03094498112140004806e0f5000c2d0701040c414003115038404240c04881c0909a0041925040841c0a598240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821009559 1250 821008309 821008337
    0xc0a0204020a020f0c190501030b04020405040207035c0d0906021e0a080c030412150f09030e100c080a1808030f07080c10090b01060207062c01 63
    0x3100038400c45190381c0c0540500e2050100035441c05c0e03245002d2a000d00001440c4820401d0031504820517900c0901e00411845030000005020f4056500301690040c400201c036800c054001401d282e8007a280c0701c146050300780c41030a00079014040041000768005820b503c0e206510500c0300d418808d400c078000d50000301c5200d04124900f024008a00f0041010200d081c840b454040002d6210340318460484820000030041868440084e240010482d01010440181380103003401a1009490006002c00b09200c0a00303014501d80b12001c42c849907a072802d4484e9610307483c5802107441090701038a0340e050503002d81c81071005000b242e490070005c21142912000010302c11100410605030955502160f40d0b02c0a82c04c0410320840d50b0104a455104000e4070340740049010a0b1034410350003030452030300c60745401ca569080c01c007203421100344146812581070401c03c0080c02d86042c7c6116a007240c1442e81c6840c81658000030206c03c941c0b180440200b200300b2075001003044880c609061501040480300c003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821010809 1250 821009559 821009561
    0x170f0c01050c09130e15090a060c091d070e060d1409030a0f08090703020607060615090f050406060813060b090420010f0503070806120307050c040609050603060c0c0a0204 75
    0x16101c44039141d40005165085141007010f9140003006084204074000a00028607a1605460115161b0800341070010704010002e1100d02c070025000001440004003880f801490031625000700625144006100111440c038145d04621420b0b82d9180c0c1885140c01d0810070001360040352411084c251111101840c03041010300c1240643c048400454450001e95005811803401d000b80f4410080c0315020020007400028545003202d4068901c20307903c0c1501d0511304081c10702d6400c500000c8041c1c0d008418600d900c0340c1020110b807844081043c0e071a40b95400c03c0240c51003031251000040c40f18022510842c0100c0c011128988105400282812054042412004115010781d01b600c4201c542d5402d0a00380110201001001d10301040015010800a0054000900a1700802617190700044041d01c400311800c0e804005281220740318260f5103407141c0e503a13a03116103840c0244d00705080013440300050301801d401810300030090003a82d0f0390700b0140d00b09500151507230401442800000405602c0d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821012059 1250 821010809 821010811
    0x50319020105011a070209010614120414070b360d030816090e07052116030f050408040302090c040e0112020907210b03030417060105010206070309170f0c0105 70
    0x2140c00108881d0300d84001c1c030881540c0809188036106040004400582d075448826040d2041030420241d100701200504400740290300d0702c6000000e40100703000603c90750b8401002c4c5402c4210480b007181d034540040700c1c000d001c2c9a2105003d920140888100032049214401e807444064490880a107400c200241d10203940400a50210b1440c90610a02d104c0300942034603140b401e400c01c0000da62030042c1840c10143c0040c0f040041140114040c20030050914903e000c00904449800c07003400c100904c28045842d011645e00032900c0c000e200010308019016851081c1e40044281e41843c1c955024000c00c0c1d14010540320703c10701c08000124408207440750003400307000c400d241013440c880244103000130b00d80040d02c1202400050790025403151040070006034288401e00e0042a030510040c0030074954011504034000140b41c03c0d400728100c540015515048620903403c9908a888101050b01114130004000d01015180c0c941daa041030b0001e030060000815003da01454500058070650031204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821013309 1250 821012059 821012107
    0x6020f0d0221070801030602091207061d1c12140705010212070509090c0901050c06091c050301060906141b010b01030501090209061b0a0203060f100605190305040503 73
    0x640442d4200b424105486030070310201015640802030300745203102810781501407000514850f00050480c1140c2c0b20031000e07100c070003150021a0700c0b040e20b940c0050301040941d0030229000042811200341403a1250341d80a40745501e41d0600f4000d9803581300c00c08004034016403d414000c8911b40d03180c0810086005010b050301440005032680e00d01e08181c80d11960141220042000900844001796658410070380c220074030707100e1070b592907130154010386190081c00f00d05c400600452040000101c0d01186170440546541114048810340c0041078420380428000d050015200322020300a490264880e2039800324048003060402c0e14145050300b0480903d5030b42e4903580d4440c10b03845500d5130540542401340002000540c00c080d904c4001c14410301030390f90442c01d40300d142454401004020b0200040a0343c025064036003d00d444000762842c048281c529604202105200049561045060f541190101c1383d84811074030181d1030440c0031301300280050341c0a010402200000c10780f00411501c2000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821014559 1250 821013309 821013311
    0x20a0c05070e07021509030a2d1107150507030302160c0314010c080105100530041203090b060d0311011a0a0909020603010b030403090909030e030d11061306020f0d 72
    0x224000740c0090500841c140d8003a08013005c04144110020040141c8407454624034140c01041c01c25601540540c9020190101c0000030610010a0561006804103041c0d400710032610781c00d69a41501002448102c50b41000440502c000b4001a01c46d800820082d00300140b0350380c01180f1901d40c044103800c1907008440d180c1b00340c4103d030809102070103155070a48140c1030481643d0716040110340002280d13940f2104000e400648109449100340e80003d04050400305200e0025104e4036000709140c0c103442c01c0d20b4600e403401444540c1ca1103400780451740395002c6030020789a100c0d00c00340008004400b100710244003a200914014080034819500394030000c000380000c5401510500107a00d24a41202010600348038010700503864880490307044450018905580303603942c3c101100c4518841e0810490141490707040400d05034020100c54105000724240c1e9070000c4c0c4490b06982d01d111500000906800c000006109150220f80a641845c05101d001d031a0400e4160780b040c5540c803001d00d0500b16 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821015809 1250 821014559 821014561
    0xf0916170f01061412030d060803070c0e040f0807080c0d0203031b2d0c0d020d0f081303050f0904050406091101020f070e13060507020601032001050706020a0c05070e 73
    0x20408201459600250340300810070f180c100f107a490300b0781e445601d019014421310b0860800d1080b0800486903c0300c034100c030401009413182180c80d12940445400e58040100c4c0d0f80105e500e151a46405005550107400c88028003142e6076043c0c895001f6480603a007a080034002100b45420610602c42d00880d6580916600d20301040c0241c040742110301d0003112000b0611841b01c082400050f0000c0040801e10305c0f804e034001c2d030780e8084068860071003070b84445d000f084d90180c42c0e250001811002d0001a440341d45001514a0080319009070448101442d50100b0a240011901540c010104000b0f40601285415085800703e4282c40c02501e00300c41c410b030f590401e00d06015848406100c40b0700244082d000c0a50920000e540c0c401407800b45042440885005c201203005201c40c2c01600356200300144000d140500000c0e40b94002440240d41d90440c1d440d071988510101c0e40401400803058541d035003030121580361200290000d60780380c0300b8414031290386804a03804204200042607611850700103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821017059 1250 821015809 821015849
    0x15050d0c0c0203010e0106060e0409051f020d060b0a0e0f01090902130e0a0509060f13141b0103060513020304020d0203010e0a29070c06091e1e02090f0916 68
    0x2112894005000300f40d141c00014031900754043e049409c0341c80b0444000c80d212816040003420000c0c280500100083d01c500740e049116810b4000d06000341a2050400a0555032101c2110318410003901c0f00014407021200b8180745070803002c2904039181894164402130321220003100300d03440243c0051440c0c84201303080100002da5019070380e209001403824040383c282942d160381d80da01d02a003090404404d000020f40d1b0314201d030341d1442c04250000d11004d29411002012074485000c080025400001c4406959940d40a80a01c0c800c480001c0d0504622104003a215002504094001c0b81e11074a001352000c0540e03024010701090300803000c00340c01000141e01c0e2901d000f5000c010740f0301900701040ae010304031f17414038650994001e05d58104912040c00e00c0c039048008000d4103100900303d0b902d040680303400311558240340c2c07580c0f8444c880803010302115000300c1c0301ca034400120081d8850251000101c40c0821012800d030000c29420071204102c22300000ba1008030015004018141c12080c40c1c400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821018309 1250 821017059 821017061
    0x30b070309240222030309031e150506010e0102150a0b01020a080d0b03060109090506010b0c03070c08070501020f070305190311030708030709090c081501183b0115050d0c0c020301 79
    0x4c0c0b80511a000c40070b01e500c0e503640501902940d1101614042c408403400d061451100000340100f6400a1040c110701d00c2c2c03941810042070f096903c180040c107214003000315035000084075900020030002c00744644e078580c0798010250003c5002d1741d0450041070500e4000aa02c1c1c405444000c915040c085016040700051514040d4140c0c000e6204038284900103003c40c00100b03015064610312070400e0381d01c02e800481240755104111000f08401f03903508002070b0b6903c1c0130480c4410b0320401d07401d9410550a07100010380e07a112602014101d50031003540c11070711940d810401012580f10b8202650300d006005402e030300f1900088001d482c504000030800c86c58540c031200c400701030580e10104114402c800000104a207100a19100c09060b0f90040c20003c1d078000c800d1808207040500c0c0c50750301d00b511424443c03c4c04051300c0910701c1901c42c001444002c0824194a410303030b031007207000c000816807910401e14101d151030070032907007031000400100041030141d00440c03946504d07507250504880d00c2c51040c14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821019559 1250 821018309 821018347
    0xa05011403190b0c071b090f1512030e0a06020601050a0f0608040f032f010f09031e051b0105041202010e030f0f25030305060a030b0703092402 63
    0x68481d80003480d0303140d80d40200c0c2d00d005505035004084401e8584d10294008650710400e100500215943c02e1071400d410301c100704840a4a040352010700286141001900c1a1149075100c407084080700402801400f454803000c0d00e0444c000e143c040491070050001c00c00c1011103400440068000400521203414200301e080d00829040c1e0f1300050701f5141501c0105040e002400c000c00200c03400440100b49440f070710001b0207010112001449410f07822503260540c0700090109d01e115400e1001c0400c0c1d01c50301e417044050464042e250420181c7c0c24000401c04035201c180c0c3c0c2018000140044215000b03081a66061b071142000001600c0c101810001e041903030010ba42021603040440f205441c0c800401903c14440c8403a01460300c0b84450040ca0203070307000e66000c04904004012010882060304668840081c0c002e450421881e202c0c0c0c8140a8140990b0102414445401c0086000e4030b220fa4842a151800742d5085400400141d030110551009040304945a5802280545021422200e5130b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821020809 1250 821019559 821019599
    0x603191a10030c0c0c0803070b0a0605100f030e01020d090201180f0b0c010f050c21070801060c05031b0706090f150302070f080406050d110903060406230a0501 70
    0x10890301080040041c0d01400c048a54504154840c904506024003a0000c06102d66001c004e4015203901c030350716595030380c0010030b00f581d0010030200840c0b5042180c1c1721380380030794001604c0300c2080540c051040c0c41040d00b5061340810142c0e22081041641c000b032006e4040b404840c070001c11a024540001008140300c446e48800a1507408000c0001e00b002400003411a002c91504075119400b01c080315006000c8444a1150542060100000384408034014510310318040021005114400044d86a001303040b9441c0011902440041c41820302880c81404254410740440346083d0581d4140e00500d07443d90302c0303c2d009901c586018002182c1101185015010325803800060601c0c0c0a500b042500100002c10709055000400d001448440c0c070f0701107007040d0898803d0f5500c90f51103c00400651000041003c140e02d012400c0b500c0c107140604454040703100600818154449440b01c20050131800074804584001c0320b00e04282010800d41a031003000c0100001a4940c54501001e040c1c004007410703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821022059 1250 821020809 821020841
    0x305031801050a0c020909071a0409110a0806040510080109031d01023007050d08060f0109081015090c050309010c08040b040b1905010b07170a0e1905060319 69
    0x85070300140d1111300c1d8a40250101d038081129211070043d2420040183c204440e401000c91200ca0741042060042c000c89a990008000ca00210300b882c2c0700307502605151400140e80c45012426914158101d56006180240b40f420250390703404201d4212046001c04802084691b02e41d2042e405060910030384048003030018045200013084c0300c020a0108844101c644181c00d040da03d100410341c03044e01c400590000403901c40c0300038028090003009049448070320441c1020255012941b040310442d049500540c0140160b002d143c0b0440060051391030420b58641042e03000107034410141c001c46c1c0000300c070303500d8455480c00c0c5521118203407030a201e100030900c010781c3c09010014402c0e801ca5540282c1003c45100b82e61200c0070509841e01c92920b01c46215424000041020003415004041140c4100110b00c82c40c03441114103400740c081d162482000c070b400101d501e009420458040c01c6648180c00e00314403083d0f1901c0001d10b13160003d451100c03803c1148082100403482c81e1003100111241482 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821023309 1250 821022059 821022067
    0x207051c020307242610080601050d080a08090c13020418200c1005150907020607120b04090b07080f0f240102340608100605030606070c030503180105 66
    0x140040c1d4082031a009a04120100c400b02c046001844121400a581d452540a1791b082c5402c0ca520712030064040c201c400c0c0189030000074035103446000200c685070300100180c10502148000c0e42c29185c0202072030003e02505c14041c80a0347e0b42140903200c14200000180c4403410803805241d01d00c041c01e41c103080245015850600e148004041c400f880011410b06036444247c003294500709103008c10f55900c0d650a140a0140c5c6580842440d51000803c0e00c080c1410381e59000202d1352000b06407458004501505101c004914543d00844200f0340003500100c0e0000044d41d8206520400b15042c1000402241c14880c00340c2d05040000d400458003445d03004a41049682d03862001483d024080c0b103011920340400300c1e82d0080c801d210511500303000d0411003135840c00b030650071143d17000c008030744a680c80c0e000480c4150246480300c6c00b85090701101440c1c1410018281c0d1540c0c4044e202d10303030010003071001100242c000301c0d401010f03510450140d611048802d9000d1203103207205107214148407040c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821024559 1250 821023309 821023349
    0x8010605090a0203040f21030f09020f1215090f0c03070614070f2a06031a0d0c0b030702100b0a0e040b071b030503150a03051c0207051c020307 63
    0x248064100388109001692510340b4980f038203a410148400501118518000b004804203025640c105c7c0d5000d5141409045418441001100c6803141c0c0290b00031420b0859003a00e040000b83e05095601b0041218500b0088000e0039400000031a100551a4007076400b00351035000c14403584a1003c0b00380c005000540c20494060405200c410000e03035184c3c40410703000c0601010300c0403800701d00d0300b1841c03955a1801d000c81001d020301050120700305c1000460f5000400130700c42c0c4a00c4415141014035134802005240c03c118854882d100c094600300c40703258000c070b00544480011030241040d5002400301104180c000030548450392354040c41004c284808002c560000001181c1c0700c0d500030030311038441d80d0b403000a68451420b000340440071508010488201030b000801140204101c14455158040060422441003600c4c04010103c2d000300e078034102e032a000f40c5000c50601030302e401603a5540c0d03151404180c4141000e0426030710084030300710031015400e0034099280a406588a4200141740803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821025809 1250 821024559 821024569
    0x30d0302071a090a0b010303230903070b0c010204090c05041a040636140a0806071e020a0f061e09051207050106050d0b0601020d050c0a0b1f08010f0608010605 70
    0x10310b0a46508003146070000c0e40120040c4241002d00d40d2110040d44256101d00b0020f01d03010107205003407030200c100d0001d15814402ea2040d200105001401015903d0138032450350125006040382ca1410344d000d11000c034480c407041c0a013204408032540c80d1511146010801d03541044681041d80d0710004c2008188401e40c1e114600c01d00e6203036029112030794003030a1114000f9100c0c0c041d00c052046d001d803c0010820800c0c0200100079020100e511824298442c44c250385c5620b002c2d00d0f00e401003201c081d100c842d110204100d5007007450580c010f5842902640e1107143c215601c6000c1120340e10307590081c640e143e4603030030402000078247c0e5808200141160b5100742e640d5581c91100c1d808486c01040a80412400750405000703020040e0142d6080045890141503c0d002900c1041c0540960752071404010321480c242c480c5c41c000c40000309010120760301c0340d00040901910b406100740c1c1c40c1da249440b036400c6510010060118800005140002c507035400102c0c3c80d43d8100251503410900104079030350710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821027059 1250 821025809 821025833
    0x301020f071b1203141201090f1409061807030c080105040b130302100e070b0d090b06010206071e110102160b1302031e0102091e01020106050901150804240605030d030207 75
    0x125040c81c12417005201c1c0c0350b26003400340c0020800b45601900000c150b80700395800041524a00403020b012081300400100c0700001c00f102e103030055074061070018251500c2c401c081404040034030b0540d50a00d0b140d4552040c0f4401d50b4000c07200c1a0344030030900080010000b00035034482460503141401a9803030b60000e40314501c00040441030f5440794180844200140400c0e0005e001c0340320400c0d81c601d0b4154501010b800d6a00094410300896000a0b6840d4000f068140c480d060380d030717604000c01c40d00038501c922812900000700104020340f100c44070007a00920080071280903045602c44940c0c190300e40345a80d0310004006034031480044d5030070b03401a1400161004010b1000a00c64880c00bc410403985c020702512112039801012024900d08494941021850246c42070b0700a11406441c1e209000a40e0802e01c6500c5041d080746081c0044144100c1c070f0030707800500c2860070b0185044004120100000c00081103654a550351004000520701001060741018140c1415030030588283c40b00f060700d00d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821028309 1250 821027059 821027063
    0x9060503031207090824010801050f1b04050409110a0801111204052d2107111315090e010e0606010c0c0806070908061b19030207020301020f071b12 65
    0x1041c00200310818081c03011003002d0700301981150861100d01c00c5100181c2c81b00391400c090105098008500500103004103441150301200015458a40030800c540b01002808e200c0c14107007082c403010642c0c0e5207600aa480785030050440c0e410400c17944041050002c05503014104036850582400a1207140c4000c0d208540031809a01e9416030350350500701d040c400c41400d0030307a814400300d00e001820003100c405c0300e0340e140c0b80303000710740320440e0307001421081078500494400207810901c619800214624840c8040d590003402802328400c0042500059440501c01c0696503142d030301c0c091100c141c040c070440d1580d031202d400070b102004605005c40d1701c903400904400d04110700019220140104038094000030f0500c801180c2007490825402020009140212102406060045903080c1c800b055401803504044c00050319106030f03004421f040c0f00f00d00e0448000c1c185c080c00f8400140e07500b07201806141b110303d08410740d0b4141a10b0003256211829500803064840c0700c80a00602c85071860b0b00c0c4a1316 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821029559 1250 821028309 821028337
    0x1401060912050307141e0a030801030b042402040519120807052802010e060903060a0e01240e1f03020915030f071e0b1206060403020d0605010f0906050303 68
    0x110350341c205a400d610940030701504500176540302c0154113500291010f00c1d0340701d0703100c0d120415480a442503282d0054620103130000c1e4200d401030020030f940d0041141c025110351a03030039840e00180000d400c1c5520000b525102242e002c02c0400007402e010b14131005d01c00401c00d440200c01d00b0301088050400c08068041e1480700081603c80c03c00c0300402c617040c4106084809a0f031700c1c8005c15403241c141c4101150407400189003484074140c07410000291a222840100940010350720700c0103440007040508040c0f403941d901d80c3e003403500182d5a50b000c04001c440750042d02d02100d05100c40740d52041409020392280b80316040c800444c10b8550480002505e9044070b10301c040351503c0043d00701c00c3c008050310607414000d1085000152030002001000c035415406840c40700e010452074a21a03248d0352141c4022079908125010061100c2c1d60a55440341008041d00e0826031241c01081d40c100040e88120382d02540c40c0d00501508070504034410017001500c10510400c0e081c000070948030300503082d0a070080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821030809 1250 821029559 821029589
    0x406050414010c02031b040b040e0a060507030b120f010c09050d030e0a1d04120e060909060a08010203010e15060421150f020a0e0f10051b0613020414010609 69
    0x41d0b8400e031042e00021341c0003803c0354090480c0c154103900c803890542e03241e1701c10782c5803c000b200581054008e40b82c10700c00010103803046003c1c0341c6408003c0c100083c00c18080680e01c2c0e69510840e0baa206101c140703001224004e059141400310070740c1c07c503003003103c580003030281450080200365900c2000b83e0009515241881440b007212000c01d8495507185c0044559524542030080c80c100c0f0903400b144a40d00a91104141c4840031074240c86140340c41102d00c0d0400d4003005200110b0a0003103005400400182042600030364652001f401c9030402c2c0c100d41445004030703040c81500c050002c01d101c0c41030b00840300317249021325000e00d841078402030341311000c01400318803101030511255002d540c1e4200178013442800780b0041d41520f54000e61041e060407003c103820b0602c825442c1002100550000c03005042c0b286900c240000070b4505400c820001c0c0c0d002d4851003415100d0700c500b40700c41d0340200741402032020000d00c2c0c0e204010030f90362040c090714805041d41004000c074941c0700350403504591010034101c2070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821032059 1250 821030809 821030849
    0x51003020d170915090102370f0203030a0309020306100617060409060903021f0905030904051305070f0303080702060f07050307301503080702060904270506090304060504 75
    0x10501800085544c041c4c180400b10000f420380300010407a400742603098407003011048003c0746024074404080700803080190241d0840c4181100b40005007070080f540603041640300e5001a1840e48028030302c00000b40c47d02140b0b0114202003100756008800c00c403407020703024100440200810510b601400084540c0d034003061051312154010081c8641195082c07109a003c0d00b03010790344e02c00f0101c0c1d0036114522030203405840c40251040030003151f44000078520f0720011400304030140602500c5100c210110803116000240e0030030084c80103061100e80401c806145017405442c41380014020703000e45d00500c0411481281c070303100c1c0e107511000e40d007021078403030b25904001c89100011105242d483c01c040042d0700905201d024540503c0710010a041c13000201c420301140405503507120041504105124550043c500303040603000301d0402410000c2c03508503030807107002c0d022071101d82a110031031070418040a01c2400d0190681c400800300065190038602840182188203074451004d11625201c01c1c0c0303403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821033309 1250 821032059 821032103
    0x301030b0a02091507030903031206120b0916030b0405010609020c0303160504081b040c020d08011a0d020301090b010f020726120c0d0912080904091112010f051003020d 74
    0x21030b1042004003a5110405c40c500545081414081580404d5032a01030000d1010603001c0c01065540c2030703451784900151070759001240e04002c3c1068103240078500c1d61240104a503071042d0029030040760703c0c00c2542001d0606908580c60794005142680c0108030503440d4010010499070418a40c2c0300680e5500002c00d0308580600440c0c0001c201401071890b18140440c61540c001c20124040305c0400003491a68801d0380d032281d85101c1e06020a4071301004010590480c1c4422a01640c0c2942c11031a050703600400c0802c030791007600f01e190455519041a5010350f40f21401a804148900007000510305292141455a1040503201f440580100034000010024441204c80768440c202181e111254200003903121011200c4400003d60f05c0200050340c1d074601e40c1010b00194100e00814500a03144043c84060620200c0035107503682483c0c00204d080d03c0d00c641e000314242c560000060303580b80300ca800f8030580700060320f1780c28886020141032003d40d0399100e90212a55001903810748040446008030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821034559 1250 821033309 821033329
    0x519150c0c29030a0f0b030a0308040b07020304080d03050411090103020f130e0a0c0302032b120e0f0c0a0e04020a060e120703031701061b060b030712080910050301030b0a0209 77
    0x20030b81d0020040c0080e8050581082e11018428082400b54401740f5003070641ea200c0c0000c02500050454011401154201b00655008100d5205891030981c840d03d50603c1d0111030340b01340c40003903a140100070038803030081d04803076406c1c50440f20214603502d941c000807401599000e14600c40c491511415031141034503401511102c2c078103001d86101080c507041840f03520751103100c140c0c001c1c01021845e607480c001d506032198500140d0b824400301c2c40404041203560a25924030003680300e07a5243ca40c40002c00802c244695008031900030300110110328140542900c0c15070200c10300451010500c030040c0c7d200c1040d079059076003900c3e00c012022030300b00000b00000050380441a03680900c8002209040e03100c0c0403045687c100443e40c0050f80d07a9101304480701810062511900e80c154070181f0002603d0b0b030040f000d200001001c8405003600d0b1009440e88100e10101211b01e84400503080c845402c00c2d00003000e00300418248903040d03602d9612403484550004001c01526540011402c0150355031038406 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821035809 1250 821034559 821034629
    0x3080a1b0231050c0c060f0705070f0201110f0c04060911040e15130207050c12210c0d08041b0617040c0e0903070201030b030607020a020114040519150c0c 68
    0x81c0840d060003940c90300c180d881410402c81e0b502038140090580c3e00e887c0c03a8103000c0d1402e0307074030545403100d00d444075074100d074051030120b0401c0110000d10265000c1040725124445120010b01520401103080208407880307540001e9181f4100f081103802d400e503a109440444801c403003100940e94500c1d10450f4080c10805400382c1c031040358402c2c00ca01d20f4840e03010f0f0070032074411000c07140462001010402151142800001a50300c0900f0320f20210403031665100d005840c1402da141003000c592205401d060001003050006025078041100f804800d503640c401c16800b1804035040541048001800040f120050f24440c0b46400045000c101c140d00e2000010300400c0ba03001e5640c01c044a0542d00ca60180a050703000900b0072801145030324011900d103000c0e10558001300880c1d40c4550054030034581c042c602052108080c0300014144d22405800441c03119000107442002d4203144d0481509400314268030100280e9091860018011205100c00c1d50541c82520300003803c1d0020340a0030008074201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821037059 1250 821035809 821035811
    0x5060f06180a0911071106160201051e0d0e060f1b130b0406050a1e02100903020717031c1a0d0f020d1410090f030e01090f03080a1b0231 60
    0x180010100309001030301780300c3c2c8104900541008054104156800340041c184564811070b0790400c0150b014000402941c20000c01707020b0006d000c5c0b4080e010a41141c1c400044680d150070f100092940c062002542c002c1d060310500009041001d00a200088031484400714171000180311034031140450104402000b598020300e0b9a0340c2c40744002071041d00452a031300045924440c14440e510341220358039440c002a9030042203944010780c1d003c0302070825501c00783d003540a40d800105007a00b00c8850b1101410f0018000d681d61211903a21101080b410112009000d00d08550a080c018800070303900c074042011620139440d0456410021070205180d07800035807100030310f081c2c5820408007040e0b050709004c81c04191045204424917010a0f2000b01c1c0005050300c2c3c0754803c103c0020b01442e40d50012000600d002c8651644034488401c03207020503042511801004030300700f0030b00740e48412900200004541d101401c02d096038041143c05403484042203087c82080704000d8a95070341166146441d0751a00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821038309 1250 821037059 821037071
    0xc0c0102030c190509010807120b060d0e280b04060e0318100c02091f080607120f1e091b060e03010f140c030604020d1d0105060f06180a09 61
    0x4881e100c107510401c030035240d41c0d81201c00f8400c5180a44280c0304150b80607118404140c1e2980c008a030303c0003004d244880308503901c25007104151500400341c0003600c40b02d0000540310000114043c500207481c100040102e40c89203800144c14020344000d0300341c5a00c50f0700300400740c4861900e0340182084952150300e510020030821303d10320200c82030210f0f00c070042e41c0f801d601169034207084904120845c40a5000034014000c0703180780100d144070503501040c41452079541500d4038403032800c10005890b04000039240610b40c05001586100c8c0850300381c03100904004000070074260484820064003089001d6035107121420600958101d44c0782e0182e0b6400041803a10380792500501901ca400b1003240c000c1d840c0468a803a8240f05100310500c08042c5010f0201e60b03a10f007442d946950f80003d0500350015000d01c010302c240d03480f0703000b001700c0d1103880345519049068400c038031400c41d000200b240d40724440c482541009511444e04903005004e03404d101e40303400c1f80c2050103d0a0360800358003800101d45080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821039559 1250 821038309 821038321
    0x1a0c10200a08070816090605030a0b030a050604201315081f0e1209060a02100f050402090907140f010309080703050408070f061713060518010c1b0b0c0c010203 70
    0xb20350500c94115510350002a07102c0c80c0000000b41e00380e0600d00301040038900103200c150702540180d6800000c110000ca401050100030a040017001c150072070309a40200c00b4001040007403601c13800320b5000c120704010100b030750760700150741eaa0f24141c039002c140e40d40b500f600141d0307007803c0e4200000e4001700d4102e440c000403510492509040c08081c0c520340c145880e82c852907031180414121040100c0030038850505161104020031544000d420005601c90482c901e8400560f5008440c0c001c1c801860005e22480c044c014400010001031080d551500f000e45c0c244000e80e0401003070600c4d4082928807403112150440141d0040141e4030001e080150041041c2d82055400030003130098440d00010f850700300360b90300030b8603100c5000e0340038000110b22000007061415a000300d100382e00c000002d0061454806c8c3c1e460b62812200305031914003010503d90819042c04400340240d21100d000d92604881520402c0101d20352036840110080c841010130300803480400d4a00b05030740f0450443c4000f15503908080e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821040809 1250 821039559 821039567
    0x51908090c09060a140112050c040609061b030806030c031504060605030d050d020706021603020a060b1e0405101502030a0f30110408071a0c10200a 65
    0x100c4100146114903030600300141031401e0000d01a0001402c003840141c01e002c00d50403500c040c0c00081341003010300000c02c4c0c83c18449000b002c1c02910a4205542e0315401c1c484c0040c1480c20076000402484503c02d0210341301101030110381d40a580615051886494980010b4245419492000da0604c00e0196000c40b0442c03800786503008600c641c00030040c40b80c0d50000d01d034403801240640d070046003040c480c0400d03500b59a001411514401d0400516014410201000c1301c0e8645100350011780c0006160820001c80b4454250525400c440c1c0c001000c0c50b01590800208065a5160181d6214030220724035080c05108880600f4803580002808002100003c5d075030340081505000040c0c01e5450001c81c01c0c00b840e9015500c8440c00e00c6200201c9012450000311078210100f03a02c415500c40002046941c0d00014202500c280e102402d0110715140c058004038500712078610444030100683c034800700300004c0c800070301c0b103012030007003021058158211680d10045291130004d40c40024009582648 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821042059 1250 821040809 821040811
    0xb04091b090501080d0f031409030307231e0c011d07050103113910060509012402190812071110090503130e2e05040903051908 56
    0x102140c925980303540c000c040d50401e114800c0550085070285007440d110300748110140d080c41c03d01081d020701c1c1107190f44207036100f01d1b1000c58903080072003845034a0740d100c0c0340c45002030071040214444a9440c1042405032003071036031940724410900512204120800251001078020720000c1140309030052450300210702c10b001050843c000c00030081240d6000b403084a0050100245460400d10038240500728441c080e01850541d818171205011001080240403400b0b118100103800d040d18880121403ea0320b1982200d0310960b040801030000007c5d401000c0c0e0700d060581240c14498032500c1d816814524982c0c6006a42c0c09002e59860a001c3c4040041c00101c80d582c140313088581d66080300311180403590b0304091543e0010304840400c1d00c0b203500503a800e140100140c901d0034407441c40000c0c40400b1a800155800b0742c7c00c04102078440e15038008401940301a04001e046809802070010361001c0b8028140329a65030544c40f4241841070b42901c203404502402d06510382200d0b1030140031850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821043165 1106 821042059 821042093
    0xd02100e0d14070b0c18030c03210d0204030302011a18011806081506120706141c0207050c10050c060109020a0e03030304030306030302150f1305010b0409 68
    0x245000701340c1d008114076100c0c0c503940c4100c41004444c910b94456060b103c6e400c40304002c01c0302c1d1404038203100d00e200c1414103a01205d070640e186102c280a03c409084540d0320110f404000c05805500002099084050050f202007001c000c111000955441402c000c049aa004000d000d07170405056203203800d5040d0101d034031922401c0710752800c0202002c465503100345c90184551424800c1c001c424100c0000003802526007000702c06045100e0401e100300101c000000c024050420140040b5584103030070b203080d5580d83c200d00b071459545000042c018800c2d00020100c003043c0380030303000701d40310b000040c00541150f1386084002002508003481c4502803001e1490f80c1c000640d030070b10080d8440c43c800e40b000104141107050007460400ca50309002c0705a0906414040158081c072241903024182440d1010300307880c80d16180c1d001d080540f40d119081814680003800300012154000c0c5442 = true := by decide +kernel

theorem cover : BRFrame.Cov 820863309 821043165 := by
  have h0 := BRFrame.cov_init 820863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 820863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 820863309 ≤ n) (h2 : n < 821043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
