-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1406
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:49:37.147788+00:00
-- url     : https://prove2.me/submissions/23e5baaf-a7bc-4e93-8d02-b4b73e5d114f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 252697841 ≤ n < 252877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 252699091 1250 252697841 252697847
    0x90d0506250f02030a080c1308060103020301180b01170304050916020105160c020f0a090e061b040f030b0a1e1512020102120304170406202805010204170d 68
    0x9546149018016007a04001402d9004015205120341c43d040c00140c5a4400420401e1881180e810001c03008190390301040c100000207201d4141c80c400c0d40208003c146103d1140001491030b00c006081c000e500b0014000d215a2450401484029100716410302d61210000350040b4000c5900e50041da9115005841c425424080c1d180c1096242c6c03030707181c0071100000740188039007020200640a020000203501654403801683d400824803582c0400c4003d141c90030644d03c50b5010348404000204100c00000c0407105041110100c5401140c06402d607440d5507241c1c104401c4c0207107003015140c2d40b0b598600e00b00c4e0318020750013500202c6250000b40100c44c0302450042c096241c1281342d1003040600e00d180140d070006207480d40080141c41c10f584a41d0750745032079000e030f040d505024629410701003400507080da0440d101201034081188407490f84024000141d98039180d801c6445021428062902c0301c8014015200b254031b4051000545059110903160703486800350442402c2c0340c0d00071030150043c035074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 252700341 1250 252699091 252699151
    0x70204050a022215050c0c040f090c0b0c070504050405010f05040b01211205071b0b0703030e0f0616020709050c0415020f2a0405040c03050c0409030212090d0506 71
    0x2112003d024900350605a0a5001141c0c0803884000d2207000140082504410010b502441800038814402c1003140d192500150000030821140561101408607020b00b54006840000c8241c1c0d000744001840c0004000c003a04020f0016240d5559402c08002012000e002d000d00c52806851001030b01d51500c41d110301c00c1d04114078075580003058516020005000600300000161030340c5040350700c1c1c100c5820020082401c200c01d80001200807000020005141c4c0301070328845010792030401c950700d08107001548851403007803041c200390003e000140790310001000342002e0700502d10403121240d0300c501c00d50341150015502060b034094049800c002c42d030107141508911841074805015402008041c180c1d817144058165007142d03d0850380c1036415050107848000c10400244140510b08250070155040303800350009590b280036200d4008840e081a020380031900741e140e0300421030303025160024480381e00201303103c5038425007228050000c52010041140107081c05a4061004400c40c40c000819030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 252701591 1250 252700341 252700387
    0x80408250506011a1b0f100c1209020102030d0914010204060809010e0f070303231204030315140103020912010207080d0c090617040c0e070c060e0303131205070204050a02 75
    0x130a5040d041c0c82d107542ca50080d02c4055004100300184444400b01303990a0004200e0700044e01d00c01c0340d601da01122040e411280020070a0740750006034080c40c2010030103039441c101003e030141e03004114200e405451a0300260086001d5102d400303940241c061082c0c261781c03141c0d010301300042e6140240070011b030b002c1c030564440c21200705c02070004601c0d8800303858441d0305a100150500c203003040503050100c40001c6204a210342c64903540c0d5540c04c44011040f50010598081c0c0000c0d19100100c07040d0544812a807082d522610000303030b08c036840140114042d621409005400941601c0a205090424005081c009200c0c09405403540800283c6000300c841c45c4a041c420000985010002c0c0c54001c070116180e101d10382c0c64484561754500b001c081107081c903070041c800c20200700108424075900c01d8601000c1c0380303e41002e000c4d12502032140c41d0743c0e0005840800a000301300c284400090380c3c0b10003468101c1c105052060425a65400040c00c9030f00c2140d0702122a030b0001042103c007030303074165405440c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 252702841 1250 252701591 252701609
    0x3010f020c061803071e0b09161e092d15030204020702010e03060403091a040e01381306030513110d0507030c1a0a0f08040825050601 59
    0x140001040b0740e00d56001d0000910b00d00690f40000b0604000c2c400c580c0b03a160003410401201800c840c0b80b03250301c1c001420a0310511207640100e100300da401300e03520340d81c0c0d8041c020b02c1280314201030b1280d103010b40301407031001e510b0080440021621400c5c05070441d884000580c00a0364106903d0030800c1c00c10050180382c400d45400c81000c00c039015654001c2c01d40390161030043c1c4403a058030041e55648142c4c0b842e55814030404080004247d03120400100743e5151a1040d04036482ca561380f55018010790180015002c0c6010051020a0b5030040691502d0102c1801c8074580e25501400d02d890075103150703150b40d03c1c1720005a11401190541c0188000c180c03a240800c420300d440964070340720f4088500700070a801280e1012401a40d580144000c0036508241903816496982c03504200d001c11510500074000300d40e0015801047d002c509503003160b401070704d940003000c5150b038040700c528030024401c407007804041c8040c003071450916104c04021003c1c29008182c884c01400c144d40340200590003070441c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 252704091 1250 252702841 252702847
    0x1515030709150506070506310609150204060e190b03010602010506011716080402060f040e061912030305040602040b07081803070b1812060403051803030702060f03130804090b03010f02 81
    0x102d00140380c0758030030703410140054905400000d020b48c8030341412311034000301088008007091000c107a0209606900c140c00091209456802102c10780c0203d01c519408600342106040c010f06001da045e040341c85442410b2035a00b034481c40321242c1a0800c1e080040143e5490f01007001ca960440c035107030200066922920300718500040f00d408960f1940380c11404010801000c1400c6490301c07000d942803948494480340e00e0310b44940304130000d90001c84400d845100c40030004420a1001c011440c240c40504640c0d035240c4e8001c0d201038000d0600030744203c540c142e00304000070b643d2030000d02074150103100e081c40e165152480d00c00e90b007800e0300b41c0018078031941010608010084c20b400403908103401d400711042000820b140027030f01d4058071401014413405410104000c040d40000100304803013131400c030000030601c00303018550740e802903240c02904180c04100c0100006a8140079542c010b170403503a0400c43c0d02e0f4603558030319981c0040e4002054591103482880e8186420b0040086000ca59141182 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 252705341 1250 252704091 252704093
    0x20c1b0307031e0c17101406010f05030c131409070206090303070c0f0804090203160c0201050d09021c03050c0d051602040504080d060311090a020a02151503070915050607 75
    0x2c03140821180304149010400d2254100134112040c0b6000b4240e680ca2411140958400191506c048900c40c069803031400701301c0d0b850204622481801441c040c0d4941c1808a880c00c1c0a5a25030f00160030014043c40070311407c100c0e03d52609551380a443c140c01c4846081000d03c081c0310a03075802a01040546d0010010810980b00010940303901c800e00345001088090a410100c07481c1e95000c90140c02c1c01c4c1c0001d00450100d40ca900118010250010381e00c0c100b80c013040301120703c1d03000d072880240051800c02c411808201c00340c00c000d801c140020a507405800440350480802c11400c032089001c12808100468800024080e840e0014007900741680340c0204840080320015a1038002485213a5442c0814207100c044420b07581c040302e50002c20031605032642003004092452450f10341c4106003107030005015440a00a442c40c01466800901d04280e01c0340b1404890354009140c803805100c18103c01c9020359081004c0c500900c1c07014400104c4042c01c500e042c0d020021a00f200e4024481001030360 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 252706591 1250 252705341 252705353
    0x1107290307020a1e080d0c02070b0f0a08180307050115050d030503060402070309210b06010914040504150212010f0e0702120c070308070303050702060105040e0a08180301020c1b030703 81
    0x84080384d481074000c1000802410003808484c0800c60181c40000d0115001000014641c032403040c00219401711114150384d0045ea09003031003144995101035406009100302c540c042d080300394000d080101140c01c0030b045440002c0c0703190401c100955641c2e44418020341051110004000580819140f0036040c01c0c0545014000d4030002c0c0c185800349600003400701c01c0c90310417174bc0003010b410310b001e8910140c14102e08119441140d490306882041403070021600350360180280c0801c4800d250500000d01004070104801080014010f8410107440c070070081121920b440242800c0900001c03041c2d80e5418000d564540f501c00d0b800c464604110b41d818440121b800044d4510100e0076200640e607115000758802d81888410b40c0010718904000c51698100754260308041d210744107581c2100c2e020b82e40c031010082600c0d01e5141078aa170342c00025581c00880c400e5001080108140b1140390300142002d40440e00b26407000e42150f605030884000005207501c04889441d40e040124020140c0500319102e00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 252707841 1250 252706591 252706603
    0x1051b0d090e07090e040501060302031507020d1b03030b03010b06041e0e0112021014030703050405010b0306010f05060f07080c0106080f03031627030b060102010b120d0c03110729030702 82
    0x2d14806170300d13000040030488250003000c0590b5000d010340b040320880341150030348101305a0341d8001600451410502070391003200d40c0031013000c1074000c00940d9072a030f4a06038010040d0008040d00340d500e442c002d4119448400040004022150000031901d0303c142032205040802d070046070101a84100400030b116020304c100c9030098044500d080101d4000009981e0300410b40c0d0140500903000c01040403003600f42e0b2249115501450003400140d00c1c4408240d191074090003001d02c14400e140080c0000d0611901504691440100e01351402d030711078a036035010350030010002c0e58683d1252000e00109405000203041c0680707600040d42941802035074070841e404080329942c10441003d03460320300500021000703078440d4040f4103901074580e12070800c03d0111400300d860501540c280040c07560071f420000391460100c442100980400081c0308021500309104400039010001c6503d000c1301071100a02c806001400c1e007010046803000041d142d8081c0e0142c8105107103a491b020320401000302d80110300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 252709091 1250 252707841 252707849
    0x201111c05270f1c1e1e121206091a030f0307110415171c0e0604150c05120301030507050105090906010e03011805071403030f0a080601051b0d090e0709 67
    0x2406058401042d10302c41e0001307800c5002d40710101e401c1030100e003959030f0341c01161a20b00491908091075844144604145e41d01c1400a1407082040141c010062050b100c0034071040c0c1d103001c00315059594100e1401590580d20250ba481405401010168941000043c2e10001d0000256082a2058640c1c4008100d214000c600540d251204461403210410540c006440801e851610581200700d1a658034400010020b100146560f0b103203040703500803819480c0003503009040500e09810100c80c1020508200c25684c24446801608000140180704100074041d660a20503129850760a24920700b03030361680600e040c05820084200b9640380d981d1010340c0040207003401e12174021180040b9004120b8541c020741c442010031000002c22901281d01c1046a030511050603040044408050301c1c0c1c81030115002c1910350402c054280d40340120021540100e0506015003082150f41c402115090b010711049080d0f0031480c074000541d9000031181005d03040c49000860380d45841e0b007000e000b100d51409 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 252710341 1250 252709091 252709099
    0xf0507060b01090306051510050c0a140a080c16090209010c1212060906061106060d0311070e0106030609051008070605160503040803120c0a020601030201111c05270f 73
    0x98419643d018440e00303401140c1c0050708210a1400d91080e40406105082e004c0c420559000c015080318480c0c02900c100390681400780054005596621014094190001034503000c1d0244100120b2404409460b07503540000203032651240c600c1c41d106410402d50400078003144188a2041c040e607010900f085a42e901c1003440c1e828462440341034800b0000d207152803000c81c3c10640040744c001c060303070811000c032021501c0d2401d085120079860ba46401e02280e0380c0342c00103040301c201c5001c02e201d0070701d503155400624150355140d500c980b005e55400c00240c1042011079140c4004201c045113a03c511781d406407139504003500c468200741a00e0344800b202d1082004100d0040b6012802070520360f61081c0c0030b507000c41220b03541d5603542c03a4035480e504903940b4050304060940001d42e034091350408803820389810340d010b40075a07800c603401910107191101c0c2001d124429054089086000846600c54501440d2151a250104d844e06036640d64544010150b052500f0405017100c2d072520402c2912002e0211 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 252711591 1250 252710341 252710351
    0x5100306050702100e010b01030b04140a0203040f1e020901060206040b1504230a060605030c1c0b03060403020109050f070612050417070b100f050904060c0e03010c050301080d0f050706 81
    0x240c403c03864480c92820401e40140350800705150100158805d460840080c0c80510400301006c0410086030681880610b07140c403080300290320349803164002c0da405807040e15103148800040e25080c1124020000c0071412400f040d0324a402e5107440c034101401031000e440200200c1c034059890400000c800341511220390700946200055075100d4001010024801034111010300910010b803080900c11344442100e00c0c034102001c9601ca204e0800c4920400c1418840c600c1c0c800403001c441c003540c440e00304802c5a01c0e0b41c1c81c11481c01e0303a01808460701840c0070b40c0c0082808002410142c0c103081602000702e850340d10140c0b040005a070009021001d01c40f680d580040c04da903030b5080c4052a0401301180c0f5103943c000240712810004c51004240c09082120707208460561516000b0b03a840e0007501866901a1420b00050001200390304054a17045203031405000e030741c1c50940800c0c203440c814031200011510100050200802c20801c140c028410392500c00c03007031102c1d500054070500c600e00b030180540c0c3d00d0f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 252712841 1250 252711591 252711601
    0x90306011401410d0e0d02071e1a09040b030c010e09040510020a050a0f0201090305030408090d020415030201081e070c0f0813030317060102030a03090c030506090c130510030605 78
    0x10914021144880d0185044196103c0501c1c1c203540c400c1c03250b9242149803208417501d151000510004800c401e4006103451801c2ca001c0c04140c14620541451070644004003240b10980d410418201d80c10700c0c1072040d10340e040f613010402503030400315503680a58410401c1c08020fa82c0500112000b100070345001c080d41c0c4640c00c0c1181021256140d9011032070000847c42c0b2030660140080c803c0c45401c1d600e0000c8181c000f00c0490994031303000401750010304240040b9020600d00300c000c229510004010960301d10b860390224090310584088910b10011443c1d0410071741d6000080345601404a48955501040c1100c0d200658103001c0d0000080040ca0403000080017681d070064060342d03400c10a100c0d20b84d9600003050800140ca804100c00042c0c3da24144121001340030713061030048505030081c50070080d44e000100c4c0185051102074440743d0b12001c000003c00e80a0103614004d04000c0c02070084040c0308400e101110309114580d8003160f1800c810041007031050300340f481c10380f64884008101a01c81c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 252714091 1250 252712841 252712907
    0x91f0c39080c0f06010f0b0a05042709030302031e13080c030d02040e04122607210b0f090708010b0702060c0d020f060a020901020604151e02090306011401 68
    0x1100e0b5041d030284215080d0a03001d80e00042c0f1181224204a80f080c059a140e410f264094000c52000303601140c002d10040c4002c0c0e82c2307003068103410642e503541050000002e402c43e82c1a20346054054012950000620140c0c0400140c000c220003103c02e07680307001d810304926450400d44902006044a040414540e940c0e00090040f5400d80740c01000030354485440d10a0000c0094003624121105000c81ca40101040d0155400d401c002407040030392080101107540034000410010800c00070032a080301c4a50000c0c0e074840502500c0303003806000042820003c810f000070405083c3c1a180710f030a901d02001052a40811001d0640d03403510f14454a070050381c40482c200303020315192100345019403a0b08041450b4006042810300d0a10812164940c0300e200707400e81248150394000740140c101c0000140030901c4103201100c4011242000607241c600302091f994407881d80c985118140303400151901c50f03843c0410000d4003401c1c1e0000103500301a442c1002030300d400d040500700040e0320b03507041e41c1c0b0344c445003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 252715341 1250 252714091 252714097
    0x7030e0307020f3705011706010f020304170304080609030c0703080a14030a0905152703040306050c031605040b2a03030106050a181409091f0c3908 65
    0x40c4070130800c540115452605118410407100c10212403101100001c0961003421111a010501020f440054980400451f009070300004030034150712040000051340c00e13000c0040258000140d003e96213403800c00c0f0070070b030038a0000390201926a1080c020417503882c80204040c002c41e54803042c419980d00d41d000055840c4c2c10345200403020520080104080c500c1213402c1001d0b0389200d40161481f005040000e90440d0100742d0301410034035494200d00c450041c0c0320207981c2003101c40404480c1080d69a0ba603540136a58203c1c0c0001b5590400f20034800b4000382450303603140b810454182075003014244a14505140103a41051895254800c0554801804202002154800c00b0152940d130b6071030303c4001d00b06502c640040d0f00000e00c9400c0300544004242c0d030b0002034625804004010040c0007080200000c000703003651925000d4441040d01d40000350106d81081c0400c01c40116412000070406801c02c0c60400c079035506e14982c001c400800000e1340c0c82085540701602038400c034600c034506290510340 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 252716591 1250 252715341 252715369
    0x1104060816032a03180804150e03010624050304050c09040204020d0e0705120102030603030d0c1205010807060809030c0a150204180f0605010c050a080a1707120507030e0307020f 78
    0x810a16030900d01903d4006000400c01140d2014803800300980e02401498425000241ca08502808203005c204a2081d005903031740018034200c030070a50800300103400c680d004d600800500b40480343c5008441c1c0b19941d840d00d250f030b240c01c105081d4076090f144c50340c49000a0103014030643d10007000604640d52075041d95810385882404001d403000004849507954203600405100380140610702142c600705000700c0c1d02c5a02c02801943c241034255980c00050450045003009120051601501c14500c3d480f0700d40c024441c00000b0501d00d403030810044c15078840601504815001084a006103202c001188060b440d409070f0000403114105000c44001d01442d04145140e224010307440d2804041604814080ba88005041120716900c10042d10740c240088001000c030b80000c20702001280030a4080c120080340c070b092500010407002d4071110307400400c584640100b0004d003440650707040ca51190726031001c5542010401a40303081c500c1c9a8034010313503074002d00c122148140c06110780c484980c2c1001c0700e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 252717841 1250 252716591 252716621
    0xb01050c010f0b03060127020702120d0e01031401150f111603050f030313080c0309121e011505090a020d02040807061701060e0405100b0f0904110406081603 69
    0x2001c0b1488004041c11164001070b1083c400e1000104400170048501c80e4440d10346a00d000646034141002d2001c3d410504060340d2040d20000640d0034144180504504d000060f6504220103030300d00005022070301c0400b28248085088001400005189805107403c03040d03030f0404072000482c0c080111241c41d5080d01c048101d000b01410441d001071088600c2003628812020385441440c41d203e05941c901085640e46440712494480364007150b0048003c0028000302d1042e20300e00f017a07020108540c00005140d038030507548100c0c1c40703159000c030291010400e0344103039000740000c041a5588054150b41c90141a209403900030114a0740515a0304a5409004603c025502c60b95241c10154841240b48208004648250420100450701d440386c14140c5143d0388408045006003030502c401024000d00d05194128400c50201e4030940c2c0c940908816501ea02032140c1d610105414803003507829038072030000110410700040c0003c81e001240c05520481d00c1d0100000c018565100702d02400e4003001100719 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 252719091 1250 252717841 252717851
    0x71b0203011d0c0d0302070501120b04140612010501150e030a0c060c05161a0a020307021e040c05031b03061f0c0c150903080306010909110d060b07050601090b01050c01 74
    0x2d24030050b5121205454000d0580d60646244000d0000c484c0400301c2c000c0043e04481400d10180d8014443c080c05101005000516866000082812115550401c0d20542c043c03004100c558507049004202c10b0b0340c140d0003408903525261f0000c0c00395111001c114180081d141e1042005d03141080001c01d6250001c422240d034644d1000d0140000c801d800095485010328460300e6201c98408440700c0c11544000851400446244110307103054001042da2001c502040000320302507070711817803040440d1100a04001036882680c040101b01c410f082d941206100081c81003101c51340c0c855081d1588540020481540c0b50340700b000042c004062000340ca0413551040ca0202e500b0755002c0084260940b0039422049800d17112041c1e001c0c00580c4100300800a07014900910008010304095a088417043c1020040c1540300d90701003054031000354200608510120302c001072500d181c005c080c02841c40700f0300c1030319110322600c2d43c07034492805010f1020341c55120381d00c510075070f4802c8040f01d00c0e200e01c0700004c01c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 252720341 1250 252719091 252719111
    0xb010c051014160f0e0d060203070e0a060c0816020d020a08151b07060906060b0d0902040609020717071a0f070f09080a03030b19030506070906030212071b020301 71
    0x1c010400040700d103800c002c080700014040507050502e0150074019803500402d4890b038010440766034503807460b4203811400810b1810006107041c00613500440c01c503141c1d45102242802030000300310303040d844101040184100000410020400c40c0c3c1c010fa0b142c8800d0740c0c6a4090b0022480000000500a4008509440011701414082101000804140080285078550507002c0800d0500c110340ba100034481001075500140c0360341e110065803131203002d010031102d030b80d0082000b4035082000803090040d11004003804501c0c02d4030692000e00003001c011410200310f07803103504a128104080c410038000001d04074090218180741034003a6540c500c0c0040310742c5009805a2004001070300c03810007058054441d955610701034080341c0e06862049004005403042520124003070000d1f803003a16000300d4480c4014001c50000f00000000d980070390700400d07460514a0004207900c00a40c4504201072051008104a196940361941c03c10b905242140440c0020f075021076080f020f1a81c004d40c1903291420040e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 252721591 1250 252720341 252720373
    0xf180b0d12080c03010302150c161d0907060e100e1504090c140a032a0807020607020105040f030e03010b2809091a0712050c1b0c09040201030b010c05 66
    0x1080107260356007148984611589001c03900017800001d5000c840340b0b8000112141c0c1a0140108500500072a81003282c10300041a00e6005500007801c050041525402002c140041c86a01f00341854000c0c4040b510300703c40201200c0e03034030040c548a12004c03e41e02c207900f84180215040410b005280100880c1a44403016099005100e20850781d401c18540c0c4803028001e15001c2d1080000c18000d43c82d0180c0000120010070440c1014030f000030b80c9400c0101200703074034680c400300b541c1e054035046011b00b442c00f0080d140003001462203085a040201b0030000500c2d00f00070f8400d195050030310342c0d2842403080000f800342811070804ca0f0051b01400090500700106004042c0500c40d040d480300480741c861010405031003404802810001d149110640803002060703150383d00550a2401030040c00243d40401c3c16210280e0b40f245400c00e000c03079181e00c803401e0f004000b00641011001840901030301000f01b02020780051001e4141943e0b04680d0040c0e0340541100d44d032059000f402d8a440c2d854184803a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 252722841 1250 252721591 252721613
    0x703260417060411100c0305090a030602030a05070201060e090d081801051f05030102041212031d16060801150e0301020c070806010e1b120a0b0d03031406010305010f180b0d 76
    0x1610b0684403180740030607a0034181111656685c90303503141030181c61152000d07100386d8020800150450b01121001000c00e90910107140107400d0090f010445e8202020004d007550f00a8201d01d80480104081c0070b10304800003106174091426090440c0303181e4940c17120740c50106012030452203550a0404100caa2550060b42500e1030004900c007078002c03602c03141071600303d0042e40100b9824003414964140481c1184011214004440c0750100d008544481640d00c007000c0708200d0842a40b1000244140710001b001d108064000b030b1400348610340c501160342082c1450085001c0c00d101d02c81104580c039482c203404468000c3c603100100c804003079031005600e9451800740304080c203000d06200812446a244200c6600c80081420400d080c900c0941044c010380c480030309203000c101c0d9100914281e60300c0350060b5000c007600948000620100045c1c011081c11801040c00d4101480c110051100800030320001d401d0f00c100c01031250014040c203070008000e10b2507c811b6548103c807811758400b0440348043c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 252724091 1250 252722841 252722843
    0xa110a03170c0f011803030b04020706060e010906090903120507030902030d0513090e0a0201080901141302041a0321070206181c0b01121a0709080f07032604170604 72
    0x200c1d03003400321203c10b09080301d0b0a2003800490313841080350302002c24444d4000c0c188052008000511384205035840c0c00803100168044103880010034010043c400c15442a80d0007000440703018002d40f00c0e690340003404050090b081821995844020070301d8284a0f0b80f046903e1580a800c65590802c800d8000c0e00981002c40c495041a00c03c6801051000e158090303034588030714a0006000b1030040c1d0780107517141d40e00201509800e41d078a08410721041001200113000da8005d00a00002201c40c0c01444291111614103980c00c0c10503c0300c40d045034400040080002d010310000d200103c42d00c40300c0040501c038118010b50321150204225190284100b50034040b044215500c0701501c034101960700200c15051000791a0580380300041007a05608011070105c248200420521041214650150329070283ca020001030003028003030000042c2040790f82c01d0030701ca000050445500d9662824a400c407078180504408082010b02c1d8a103412804c2910301404505181d10801c0100e802c100f0350f14101114 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 252725341 1250 252724091 252724093
    0x507111302030a1d03090d1406150414061f030b03010504050105010503010501080d0f030506040e0f0c010905120c1513061707030912030506130c030b0f0406080a110a03170c 76
    0x400c00100da8005400344e5040c1684000703503040c800c40c1c00412641072210300c401d941ca500700350300300412503c0500c083c91154451102500c0440300341c1d4103200071603420101c44040901c62070180b00c056601d200d8450b00440708500d410060a0901c0c03000c40c0a4043c4030a01900366007808140004c121040d040030381078820a50013001a40e0381c03001403d0343c4a01802690001ca40081040e44415200b81c018036403090300604042040440c0c4e0180c10314121405041d00305a030003003040480c803980e10060744001084215100d80071002e0200446449250400a02d842a07a200100302d0002024406407220540d042aa59042c20340c1c941001d402038403400384818602c1c0c82c05002074540c078000d01c0360158503500700d80c0e44440003450443c160b00800e030280855600c0700341480ea0344209605806500a03c04143d43c010540840007010b001d26000404e18030740c4140d082c01c005106110b400100070300324582200510020440c0074000c60406070080d0405030400c203180d0314040030500818010685050504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 252726591 1250 252725341 252725351
    0x80903030403210f0804080a030b060403150c02010203060f040b130203130b0a020304122102270d020906090a180c05030d0801050108071103040b0307080702070b07030c030507111302030a 82
    0x90f01192194101200d19020880c1140410003140004018284003589410f00060b0040024009121074101d640110303085080280070400c0c9140d24003a101894220380002d50650a044001801c02c0b06901c1c0b020b03000ea0317540c0c2a401030690f1400880d0b2001140d00070f085580341820803d0000c502c0c602c40b001d4a49442e0000400d507100f60310310803a8842d43d005144450100c1950300d04031512418100314480881c842540d4070100798030303840104100c140740056644800600c0a003014104055200d80e13102e48800d4a1000158a95080941d8800406c03a0010f4455590b2a640720080000000c0604a030750110084d50070042840c0c641000d03220100c044076910016964201c401a00901400380010f0b44d030710209500758007500d110703c15100311005481c105030f225048002c043d04203c0d548400503140500744a12b054042c00460003400309546000e19041003500d0241500c040c0850043c100b0400150500500283e60400c80e603256008100044604c880e01200e0003075001641c032800036610381 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 252727841 1250 252726591 252726653
    0xb06071b06090605040e090a1a06010e01110303010e09030717070b251b023f06010b0d0905010c0c0b010503160b0a0504030506010806040501150e0a09080903030403 72
    0x2e41c1c18808540c000d07500c0d0791500c1c0c10240b01c00803040c4003912003005032284240301c3c00040c42200c80b1a45800c002400da82441ca0114001890210080101414071995038a44210781070040b0840f0705481d003401d003149032a20b07000101d9103944a080400380c0f60780c8501c0111008a046600100f00791405541d000840b5141c40c40d1505117034024803845004181841d032450450760207125101c2130806015024641c1412030307004128003503102d415819008a0500e07101120025486001e080e01c00c86501c0c03480d606444440c046e9942506015466079500c01007003001a52425820441d61982e008009002454100002a004000404082307032441034a01c000300301410f0000391540408507090800309003601c0d1485c040d05070b6200c0300d4900c1c1041410000803021610800c6000d009250000050013985072508219084940305892803071280c0341c98a0421030500c20030ba84941103d0100030026170003600c0e1411040910603100641d030107003c04035001040c044180c1d80040b0903010a184581d210b03402c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 252729091 1250 252727841 252727847
    0x14030a1d040507020a0605280207050607020a030c0f23101a010f0302160215030405060606070b06120a1509020109050a06090b220321090305030a030905010b06071b06 73
    0x3243c440005900010f400004500c40b07401c01d940145000721a04250309101ea1224481a032428040d4030042d00041c1c4801002420081c1590200162010b4018403c8581c2c0060056900540207895042e01d4905007003403041041c18819041020300d060504503062440c0346840e070300b42644030800d10b4905800062540601c0c42180c400c081c05170f60322004102241c000b42c00a400460702003100d04a00c3c640e501c010703118844070007200028812042d4607441d0034a055460324100902d1a4041c42c42489003000040e5840d00c1c25400043c2107a030307550b448032985486440c0804001c40034002010082100400390240c0d0311042540d4000c0c0da6944000d921101031041d05048dc4c49103500103102c0301400c22160340c0c0000034100100406086003075141e17401518480e242d01d5504152201901440440d80405064039031078080880340c1804654149940c4031641c590043d89048010306880340e0696040010030741c800c2e20203000c002e080c55112505400e12034100400140441c00b0603075400304c00300b034542c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 252730341 1250 252729091 252729101
    0x1e04030e010e0901080709020a140c0609070b0705150705130f0510030501031112070801020a20010902031e0a1b050102070e1605130302040c0c050105060402160f14030a1d04 76
    0x251700001844140c0c0780c0080705000790300c581c8030301c420007036103484190400d1160030041c010a4085030060105042c035280d05030908020b41d01101309200300708252800140013150f01461015041e048c240a40d444c00c070282c505100e80050003400b04210300f000300307003001c0070241c610130745605a9500d04c204407810000e42c110348080c0006000d21a201180001c0c40c130700001c4500d094424001512041c5e6a00e558150a903085101190041107c2c07040a07103400305602d0701c070694802d00c4002408a07010315008607032134180440b03a12000c00d00c0600203807111102000301444841c2d000e10880d500c080d010340c0103902c1e2105805804e00500843d0710006000307080b88400c9015100400f40048042d01e0000700f6500b591000d00c0304100001460301c00005a510381c89a010114102d460f40c64015005151103403c60304010010b81c8168418010612046813800000154550000c100c20640c0814100000f00420796442140940310009600404560105040c1d610303901304c00440000d01940010807041d20 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 252731591 1250 252730341 252730349
    0x415260c06090901120516060201020405011805180a06120c080c45010b0d1409070303050c0a051f0e0105010509070f030f23060303090604030b1e04030e010e0901 71
    0x107001c00005000c0099901c5040030106d1180b01180c5140c6401440d80750403000310b521000160358085402c0101d03503000554100000d485504101c442c5040c600081c40000102e01d089415004060001b08641c0841d0300c008041d02480301c4d5207180105a06e03044d02815102e015090086c024800a0100703400c1044030b206c3c1c410103204030010500c0859034600c0031801080e0392010040704402d02c1032504003603030081c00d003c0e0800e211003c0d9505000d0200ea000d651825510960103e414801c01c04881d2003c2004e200f900c1d818905155500341d090700f07081c90600c1c200000f5280f80200040d410980d2141d208041001c0d042520511012481c1003005003260350034864144c2148a0000140c01103100d408031400c070403124200069100351205000045640c1d40d185c1000c1202c0816034411a4015844c04070381c018800c074000c1d0b00e040e0325000400ea40d8069032000614040c8820302003904510058514000d4100700314941c000c500e000e060090001901d940014045481c140303924645082143c1254142c4d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 252732841 1250 252731591 252731599
    0xf20071703060603180a1a2a0307030f0906050705070b0f1b0901110706090807081606230d0b0f040507170603010e0a0804150516020415260c0609 64
    0x10b03590b099901940c0e4070310321100080c41c0540303a061000201d41040300050250720700703104041480c29100c4281523954481c0309640d9aa150000765400c59000f50850703038849200d180220360000b02203159030107401102d100034400e42c2030a00b00002a40d1010242821038001c80c0040701c03507101c040c000018400241d0707280b2610b22402103a4a400c07000031000700314072403041c9403d03201e50415282903810b01c1ca46803c4203000a905040420400c0700c100150300203421440c02a104085001a0300d01424002d80301382406d12106415404148800b42c02c0110801c5e08205038640e502030b442e0050005003141c00042d48aa8808000100b01e800d0510030310388540385a86480f0307184900c40e030b09588035180051480740d066403521440ca491032006d20200010310302c2804010703121401d05c03450b07040c0c41c2e010b0000441004020712001c6948181480d00608903501500c00184042005a1640d1544000d0300003480070018200c0c0d009402e81c0340c0c1e480c1e413030091503a008c2c1c401748540c4030208005442071050b15948 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 252734091 1250 252732841 252732847
    0x40f03020607021c0f0311010b091303050403050f030d0c03090f200409060b040501080a0822090e03070b1b0723060405070f21060f200717030606 64
    0x50030072400034424a0300041441601002006401c80401c0240c0011214a5400c20200e0b041541203c060b088020030715009210002c183e00200302c944500070b00c6400507118010301d0300c0505005200b1034015582010989107034002a4948030b65030344c0025210b01c01180b40c0300034110074503c00e1080d1380406070300440d000b840b20709603102c207094402d000441c280b800508100c02d400c80c0c1e8882c400da01c840d03880740b080441c00145020812003240d505a0040c0701d82d4110f0380b540c40003d2400821a8483c80100000d01e031280002564611550019000044d80600c0c2142a81075140004082c00b112031142c2c0c502c1c0100d6a6444152400d40441e01080c6000b14040c449200040c00da50104035038095000e0100003452314000800b40307010400d03a001d44171900a040280a455a01c0c016003000c1c0c045d400002e42d00c0c10070b6103460310702208402401b401c2d40e87e4500038100c41200c01d13040302c3c007400980d100c1c00d05000325207060054954801c0008481c4480184c17030308038980300c4440a480c46040c0080450703013 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 252735341 1250 252734091 252734093
    0xa060b090405090c100918060e04080f040f06080420010e01110307060204090e060a06061d0d0c03080409060e010b16030207030605010906090c021504031b0609050102180105040f03 79
    0x1020b8070002d001802c1901884559100603118600045220203255030307002001d40c5450055a485040c13210700050141c00d00703d09003c5194610807158000ea405180a6a9010006001c80481c000d9401c40000b001c1480d8002460950100b01940114040c0012040c8000a0000c0d05410728498500d240071685490b401160303580070b1900500c5500c00182560302e00707445955050100e81c000d40090780c1035540d561008880c02c00c10043d259101d49401e070108800c0b41010000740168503580000c1d018802403515203071583d00d50141150b0707950342c4280042043c41e1a490711410781c2d0400c0c01021072441c030304200003800c40001d0b00141d0484103000d0100c0d2400640a0400d50350030a00c503c00e03020352142c0b180020010781030340300d414028201518000340c50350804414109496803251070104551103400603600c46c641d41c000d0b20381c0207581420001c131035503003072030280c2840c03014082d002d00800d01d40601c94041c4401900100104041088241f44004090005407814001d50107044002400001c041c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 252736591 1250 252735341 252735349
    0xf05180111010e0f010903020708120708130e090105180d09170c0a060314060402030114090403021e0304090b010203121803070f140c1509010c0f06060e0f0a060b09 72
    0x34205034a000814500c1280da140e0f40b4052001c904918130340c0d59111040107041c2d043c80700c031001d0f1141300064402d0442c0c0e0390f40c50000f402560800781038003500198581d061150091071302c004240300d01d9880309504c1d100714201d000f090101d482c0003601040850380012000c000c1110b0344040c000307840e00344c003490600d00201c0d038440e8941e110407064861211604681d50f151007180000f02520707503003c1030304000c81040c0c1400341409014240a640140010711002042407256800c60f8400c0e00e00b0070132070303031542005ca04e80030140181408060b459114100c2c402c0020000b08181c032818003051241041c00401280e89115128184031308203002d4021a10800d002c1d00550f481c0c40e42c00f1300716410f1205a45441b2590480700e101103e40d0550b610156942da207041c031a0351404c83c5c0848a40d400781c0b003040702d0091184031700301d0594100009061404100260109a02e40103900084100040360301d8040c10000d200d0280c40502e441101d4400280310a441402654196074500940350308000d0148144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 252737841 1250 252736591 252736607
    0x60a0e011820030a1506060509011409130c03150b0903120309070e070908011b360308130e04050d030b060d0e0304090f020f070f030c170405010f051801 67
    0x1c1e0b90318401d541e60401d030682c1c0c104090f1103c03034024002003820300141c8141008076615903000703c0c1484414000380450740c1e00511607100c00c14010b020a6912900b120003d14880d46046003800c0840c81e01c11208409039040d485001d003c81c600344118020740c5c41348ac080045000e11002198103501c014039041100b40440040c641156600003296072240d2036202d03080c0c4800381100c905001a480304400c0240380424025103107001070208140c0d80c0c04102c14001010882c00ca01103111803810400d00481d00c07851100402c0c12002d040094095403a1246002951a401040c00c2d0071a0a0b010b00e01140b800c0740c611490b40190f50020060200e500444c000f41e010b04001c0e00000c0d4004d009102d0007104011900078042c91441c1c40000d599039a0611580c0e0044501241c02009c0c880d2060140e4410b188400342102c041680203c0f1030300b0504d04030f24040341d0300850440014a0f19040c5045000030503110320143c03080e40e400340c072042c0740c1e0546544111500c1c02890020707038402084041c2c0340b10a50040c080 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 252739091 1250 252737841 252737873
    0x10203160e061e07110108090a03030c0e0306010f0806060907081b1b0a050f0f150c040b0a0f0e0103050c0702010c11060a110601050406032006070c08060a0e0118 71
    0x200d01e052990071514a08480d0b0540302c1459030007000600c44c2c04011200d40f0742e8a113041c09080010060801240d079030341c7d903458072400405040d99803200740d0034103001da807210704070800040880d94550b0311095104201d41d0140710300398141c824080802d5a07843d011040900c00c44455680513400d1b5940829946407030106e0b8016544210100000000c020b40010481464560440240b903002c2c528a0424504242403031007481c50f8209840b024488203001c42e041d03800d0844d030384040c011034070340b010424150320940e4001104668006441000c41c5d803c0402c18412104649910480d980701c0030055050f210202c84041d00c1e0741c3c04014240066000b18034202219000d1140000b01100300700c089400c0d03034050242880401c401180c81c8034616000c00100c0d001d40804e03034092050300e140d580e036a0b89006010384d4880c04002d10408050164031240190740c1c4898028003a1545990703078141240c1c0325141a03e0b201011400c2051038051548140a00d40107100702c641c4542c0401c040e44c03203650400b407a10007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 252740341 1250 252739091 252739099
    0xe0105070f060f1a120c1305090c10020d030f0c0c030324080c09010909020102030405240a030b040b0102070302030d050a051c0204060f0f021b06070b012303010203160e 74
    0xe4100000c9103103110303120154206514092134007500900f00800d0034072840302101d035a880030154910a0321010b0120701ea01d8040070005c1086d403140050301d0304000e42403e8030f5401c48170464407134103455400149841045101e0302d04101c41200d601050041d01c001c62194804a4426110880060304c01c1c0e00c0404034075203940020742201c030202c60080f07000413140d11551003940101c3c0040e06602d02008980e00400c900e800c03c000c050b0503a03002035113034080d6100e6180705d203189404502030044003440c0c0c080c3c0f43c90501c004654030000048040d00030018001c90798016440e0201d00e000a500008a5006480d0010020024101c0c0d41c0c1007112158056814142004010300c0b654031100400004070008948400380940c079141456402000c2c0072940120408015003040c40010150300407444a210031742c1d5034400c28141c0005c03004500a4815140001c011681724800090482c808a40b0a09045588030310300f0500c02030300040500303074041520079101490036910942045030113110500c400200c058 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 252741591 1250 252740341 252740351
    0x6040201051c0515010306080a0b1611150a050c030f0c0a12020412050c06070b07050d02070218040b010803040311120c090a050103020a1d0a0b030313240e0105070f06 73
    0x402c0c0d200351481a50391190030008515111055038050003004090402040180418641d5845808820030050100e08400701078980741041d140c0300301da0b00004480c04a0485501003521b01e003080e803417042141d980002500d00004a15400003590840707004101c00c0040012a032a02c1200800030351115151800384007070446411150105800a08010a00100701d942e100406040641c00c114121340080e02c6103404000300d90014401c06a010f0308100d141c6000b1ba01c4920f0551404000d21800d40d0281d805003400004250000005a51511991241440b1101c03a641c4801181da030340640d003c014821805e5501000306810002000c2a004094008498180c80e0b20000320f00340d04026140f19225985400040c800d6003071480c41c903001000001200c10f4151101d020112180e040603189000554803030402c2d40341542e040050b03074004441d001c6a01d9040d580c50140c20740c0300b1440d51130100f040f101805d844001c1400303042d4400301c8000684482d1b10303219056450f43c00da10303030300030301229a15560 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 252742841 1250 252741591 252741637
    0x9010e06011d03011d070e0a0b0a060c060b0a03121e1710171b10052203020909070509060a15080a090b0c07031106070210090204020403050307051606110604020105 72
    0x1482da01100d00302c019014200342070a1056407e031030140108413100c050b04040c2e252500f5114007803250202e5025103800424100207103003000150200450340ca600c13a111900101c140403090540601d01b03002c540300c1508822082611070040f401d03450865021039900040001c51440d580307030103940010050aa400402d85514801090400031607162101c0d90201c0420008010906040100d090046079640255014444001c0461241e90090b402034804880b64a201148114558000d1680209001e01c1d916200c1009030b51043d0501c942c41c462240c40010a00d2800c1503101d0400b0f4039600b030307003018844000000556039550042c1000e50650b035030302490f1002c50f00e04001035004007503a00419036940010700f40102401c21503020042e15403c22400d002c1259000070380030b0381c1050701c03207004950783e855400018001e0080307510240c01c500000409034200500480c90300204108941280f400726100d0100301c03034050001f15180003651012020601540c0110040c0064803000d03040a1021005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 252744091 1250 252742841 252742871
    0x4020c030d0f061502030c030316051c1b050c06010312110a030e0109240e0f031b01200d0309060b04090b0105040c030e1b0f0a060c0209010e06011d0301 67
    0xa03206110b09080d0741c400d002d20810841d2031192840a00f240700550400281d01d00c0c9549a10000d01800139a4845080144006004000765099600c80d518940b02000c0c3c00744e440c80c06040712000540000715440d0440d00124094415038144102e488020801603003107541d43c000135000c0c10700f06c2c0300b8099044c0c1c804072a01010444a00d00c41d2207503841d1818500f07440009072080d00160400c01c50440b203c005a4504420038007000810703101881e01b01914041040820000c83e221420306825024007a0300202c40b500c48840f41c5182e8600303070780d0504081c0100c40200403402c6178003074400042d0010030795203080034441d82000d6001c07401941c0006511822030300103404c0710101355085422181c3c0c00c004021a207000d01c0340703640d100d946050030b200000c0c55400c0a42c40c0d10300c401950080312043d0b10f0007045074a4040b9001740484002d800d03c2021138039034002905a040a81003244034a49440012400c80c441b220ba050140c8010703140e220090b030504e203d6804d072154810300c881e0559079a0711416603400c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 252745341 1250 252744091 252744101
    0x20109051201150b09010c030e130905060f1b0a0c02011205010603050a0509030406091e0812040f090b01080c07060b091303090905010608040b04050106090f061409040c0504020c030d 80
    0x1459400010000540c01d245072100e010f0743d110b80310b05542405101010b0b40c2000120640b1a0b2500c3c040040440680000700e00000070307000d140105140c00d4203901000000290a070003584041140100c60341c0300d041e0610607100391548440390800c14000000018010904034421b00d1050502d0200780c5600b036840822148240d00003000a51603d05102001c245032081c182c02ca0020005149404d080400142182c0380034480d1000f002440c81c00301c25104221103045020704044016201011040c0b440084c0a800500601d803201d28803031400604510248a104032011040c0c41d8400396a50312032004402c0e400507942940c0c025161550701c0f400741e548025041c0f2031048081e50940f003c0c81810014006419a004603144510b0400181b000b01e4015540725403003641b18401000075603e6282803800b40080b0350144c403045082c8070f260780190034540c002c0700649014400d070030000d4030400e00f0441e41079002e5a0190440c107400205000d903080503002080400b0a1104692400f12140b4407601110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 252746591 1250 252745341 252745369
    0xa1101090305070b1e010b0906070804060306320d02010e030a0506011811090d0c0806070c03080903032703040513050907050a060e1306150c03020c040905030d0902010905 75
    0x401c0050f4180401880c0311416800c090480d41750704186480c5521300150500c180034a04c3da400e00030070380c1d0341c40d961100201c6404940c000300443c0c541c0c0e85c90382c010717015201901070a00400c0715207144080d0b03e56816800d1500c04960381d000c0b400c0e070411f00140500504141d0007641001641428404591400c12402c28014485c0d4010302c0c03107624189941400507825403524030214107207074003c5901c07403e48042d201c0847d0126420100320b541c134905080221f45642c400b4065000d20410409800d8100045031002d80c0684c80f481c20715030311858103035140e1108031001d041540100b001c4d5039a5546003820700ca29028640203c0c0e24040c3c03a11300041401d06c10100c490f880f01d46800c1000a00141827180c5401841d007604c80c095118104003000d480c0b80d9403480b009000d060300700d410100c0358903203801110040855241c1c1e00c0a01401510040803041c0403141680940f1a04008020702d0500e803107100c0c03095401801460401d03c146510f0009480d00090903030400084c00c402158a0742e610100c45005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 252747841 1250 252746591 252746597
    0x50f06010f0602010603020306011503150e0712020301081504030302040b160203010b0108130f050304090501080c010906140714031b1c0f0c0b100902030a09050c09060105040b0a11010903 82
    0x541c5408180480450960042000c6905011003000183c07000212103040d5216280d03102041071345c0803c120011700003a510a40007042e0700f4000180740c03420f480c0260090126a41c0e080e580401c00c81d101c01079100c284034800c016449072012080400201a2054000b0322901c0c3c050b01e0319540d444840d119401055202681e410030003c42c00c1189000d2081c0810702e8402c3c01c2021852600f40080c414210881401400030300f1145403080400c482801114045d003032844042100b56110031140c0d598013414821640420310f04000454107a00810750304000112110700c0e1403929000e80c0c0e41e4501c0545041c100307081031209104000e501c01b10380f0480c614440c0448018009044203512100c8101c4101c00360700140400c031800094150361140c0390323102032034100610003407646a43d10110120101584114070302403010060051866103500700010b4680100121000488010204a0400d10549030280410420801004818242d85c080c0c254038210b070411100e25108c1000039420b450000c2011800 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 252749091 1250 252747841 252747853
    0x60b19090605090f09030906032203050904140103020901050f011808030c060703020c030a0f17011832180307030206010f0608100504050a0f020c030405030f1203070813050f 76
    0x260341843d40419500c000614038202e502c0c01c02142c07081d240d214a212240c02a10b000000a81440403000f603500340c07a001d420700311154007840c10010520b8100c04926071265041c1706080d4000d280c2c0c40044c1e41a26001081038000da4038120070028500201c0308400d06000010303020f80002000113800000801555024548d10420300803040d040c060010304540a042c8180040c00d0307041c00c0001940d00502c0e040c00c052200c07850b141e109507541c00d080105100076010140001c1268099400c103049664810307101403200d003000e40a5040b0501819a0340c00d080d19202c00b4550001030b0000d6603607040300d01210a62103400b03600e40524150b500145040d409607022100402c40c540d446c08002c0c2c01050b240c94200d21509101c07241ea0728000c4917200e464031a945983c0400e1202006600c1031030f900405400466554030442a800d40765005407007624802d00400d000307070150820228108481054040b980b07171650703035101d000303071040c90703010302061490020040100e0001c1c2080102c1c002d40c104100060032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 252750341 1250 252749091 252749099
    0x1302070f050c030303070c08090a0b1603091401020a02090612060705030f0a0b0d0209070210020403111305010e280f090204050c0a02070306020c0a08042718060b190906 74
    0x45424111242ea034001c2e801001001030f0381d544a5900500c42d94010841507545061000082c1800881d40100c008400000303403d980002c041085172218620a45a400c0041e54560401002280680c00103015030050707029040146080c41e41540d1250004019101c601e900d4181c0501d04101201c0200124000105100030103603080c0348143c1c00b60f10b40100b40200100d210100e9400140d00c0c400074000e09910010502441c000d104654032111024411526160703a4140401805d098004140c0070b80c01c0342c1c100c10701c0c82829004090584000038107440d0541c40c0c0031103495030642d44030070082150312102465002031185000d0901c2545070154042040c41140c010041151405042451051000c200002d0382c1d580100b00501180e422800058940e00052407007400d1281c4c3c40d2005124440005001c6011100c1e0981e038500c2e600d40340b2903a6080417501c01c40b48100c9059140c4402071071400540c040000300e0035004091034000141a1068201c1408045401c524464002102150300d401c0244 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 252751591 1250 252750341 252750343
    0x80f0f0a03060b070f140f0f0c01080108010c020606060c0a02101d0d05190c0b030c0c19080d05060613090b03010b0411070b1003050a0c0e1503070905061302070f05 72
    0x5000d410403c9002c0d01d4200540d44141d4030800300000107110585c00400710084010500403005010220026109500c400f400a01c2d10307009244040390101e4032401c00030402400510804021822580090030240c40320410420180c1050901e0049032041b4940040161160018445080e0244d1242001e0050b050812146200040440c90040741c001e035041c80841c2002803402041400e407105000f00001d181420f030441051034100101d104000001d00c1141ea15110041003200441e400399960214000a088045462140040c0040d481440005041091a070005411000040140745480c200e9100040940401e51010424550310005183c42d803c0a004450b00100101e40030031641080004400e42c0d4014003101500b0784a0b454002201d100301c00c2030800c05140c000c4105c503031564041ca0b000306090640c0c0039000b254100200030440d04070820b560780c508100014042d040c25824102400c0003030200904983d44901c10040803080d400b2180b0080c000c0c0c41c024029010300ca09142042c07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 252752841 1250 252751591 252751601
    0xd15020a08060109270209060c2515140307030b03100e0c10050d1d0604052d0607180b0703020a0b06010507020a270e0a02010f020102031012080f0f0a03 67
    0x307226600350314055481c03400e070010170001400408940060b294440f82c00031542c00d016500740c008007072040650b0b51551200070600306a8825861200c81c0072243c883c50b29400d4200c00e110420b01081a640c4420b00e151128805968000500e140020354010b80d140000e02c5c000c9201c40d000c89165483c031107243e0120b000c0c80031155540301600d07801440c02c1d001c03600510a100380749900c3c050a40e00c5004250314214000e61100d100503200031a98507040c0380c2803041d1500c40d2140a1407052120403000140301c500c0030f41040c02c4880d1a8080d14542d81d5191054031100c2109a8031107071484e8011021421151010250841c18080e0380144501c804610f00007041c444043c0c2114140a0309000102c016030342c5004000517a01d41520342d13540348003d81c04807603070b00c5040c0364104845802c00c8091b0a044000080d04038409000b640c130074101d0540044142e00301e101c16100c00c05400e403001020300c41a80742c00c6a22000e24858140c503841c0003850398040c101c03500001c03009620300100007042d07010107605002e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 252754091 1250 252752841 252752849
    0x30203151f030f020309030f070804030b0403120510060c0f020f150c01050105030a1707150908030601120c0912050c042f040b0406300516020a0b01050d15020a08060109 74
    0x11880e40c01e01072105642c070b00a6a204c1c421234a000a004010002316000340c9009550182d4080544d050900c0c01402c10000344c071441c00124948400030301300f0050928214100c40540c0c4607120001241e44504040e084144c10503604032005249210090302d4a180c0501c1c1400000d401a843c0c1c441c4820741d81c01d41d001a4481c030b1003940443c140b240840d15240125881c41070401209544440750329045040d2020350b002100c0e100d00d0100000c05001700c00c0d00039807083c2004d07039610003203001017041e110450b0011030b12440026003000050050101c20811004040d0180044901211034200044c00f44c601c1000350400350b6204036140b420509440e001c034582684204012410542001960442d6000e00c2c0725000030400c0b00088102e003040a0049080c12051001d0040100c08281706080d01600040c2c4032038946a200c0c08602c00b00c180701007228041141c0c00790f03141c09107074640010020003000c08030080e140b6908071500790103e5180c900c000d003201c50303498550a866203000e134000360000c2c8081e0300c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 252755341 1250 252754091 252754121
    0xe010e060903030604230108030405040f18020603070309050609010b040506240d06150207150507152304050d0e0d0b13050115060513080c01050307030203151f03 71
    0x1806040c101c040281c960041c8107032000a00d8551403540d0b03070b07401144007014062070000c240020800403400310091007074910943e010306c944030305400c5010032110040c0c060300c000108410010018a0080c005581020b998074001c503601072551070ba903042400c01d0300c1740c3d501e5a5594641700c0702814203018a0381e004400b11040140c4203240d0445000040c042e0307240c03406803107000a00c22000c23201c50788400090502c0510702c0c07203141c00c0140003a60b29207440c028504a00128061404a64880ca081b10704955011010000baa80351148000180c4030518407450220040784ad00c19000d054590503501c5940242c000301405140c100303015200c03010180d501c87c016000c080900002c039111058a41d00080701012444d4412000d0801c0c40c018916040070141103164204000f48155100000d80400303a0284491003030703199500b41055449420300e0216000c60014000542ea55000380d0183d64090b07036000401d9001000d21000816502905400701107036910a055004200d505208856000202c03072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 252756591 1250 252755341 252755353
    0x4030209131a0a02070b01090213030321090f0b011508070e0a0509090304090f0c0e0913060f02040608070c02010e210607020a0201110703021804240e010e 68
    0xa0080355003560020440016507103490101d40420450403004406800c51266003600350800c1d0440c200a540309850548180c902d0700004961000144219070804500c654a03926803850755400399251a04003082c0740141e81c0c0920003c0c40d1400c00c1c020303448078901c5001241c1c0004198504046560381c10380002c03004003051185002100c1e00190959084401410499031440200000400d4101d003500025008600d0905005120400002034419259916001d0046e0f020100c0e40108403503d00c82c2d6500000d060b015610900c0c2840c0340080c1d040b40680322898001019626074a00b550300c1040d00714401603002134208a840e07800040d0795007004d01464035040300700958000801440f901070605226000d200544000511071840301401072051400b542c000d450000000703510782020b070344240c1c04544c0c0c61105803d00480803d082043d00c1d4028400c1218103000c082036450b100e070051040300c003550103464011018546080c2825502d9030380e40c0101d0351400c072000359400c0d01c0c0c854a22042c10380c054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 252757841 1250 252756591 252756593
    0x81902011112040f0f03030b040b0d0203060403110f120405040c03050603070902220305072409123306120308010e1f06091508130611040911040312050403 68
    0x101210700d80a52544086050340307450601c010302ca04d24003002041400b40043c03883c1010b805821203840c0403c22a0b00708000c1c42c1d01410701082068015000354140c01000c0054006801103c6a1030040001b00494580282e040e182c81d182c040d20900703940110001080411484c44c2500a0742c040c50145c0c982030001d0300f03255012943e5044240500d50919402041802040c0d51802e4803e003900194207046044941e2828403a4443c80c09000e5090700261000306017141842d400340340007542800395108004c50740b500703442c001c41040781c0e2000ca5210b4403818008403520f00c04107155401001e900c4140440904134080c160841e10b0301e0780000459000344140102082c1c0021a590459000800241306a5989800f0323103c40e034081c001c0070016030840c190101c5e40310382c0071000c00e00f40c4180d45a40400c2c094039074000d440c01e200480b20110541c4480c00ca410004125400076a40d01c0c249804503802d0a07190b501e00e000750789008040060075500854100140a24403051003080c071241d0511074034040c11 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 252759091 1250 252757841 252757871
    0x10f0c0203120408160807020307060f020304150203210702160506090f0a050a0b04031707170c010e010e01020703120506010801030f1110030c080612070603110d020708190201 77
    0x681910410008a410b00190a2040d0801202d000d41c5204403054841000e0f4030302002e0036001260140d0081c440c100300400d0f003500a085c124070a4072036030011804d1510304116074041c44041040c0d4001c600082c0409281c0c441c0034000901c81650300300361404c0c60b1520740c1c002031909411302a04182c0d10f243c0c0340200156102c0004030ba08184003076441c403003035140b040089041a02c4591116400001401c0b0006030000d04030050001d072403080c841c0c0c00c1040c0e40e850006403030b4000c0903c041c0c02030b0038085e41c4064010401005041e0043d5130740010441d14415002a03084039880040803d040c1d400007130081c101640714070300100070020000200001e080c010002031030002d0501000b080c2c100c211240c0d2041c00711440040e820020010003d11130310414074001806840c9030b019074030225a640e4041745261030543c18004130648108000c081440ca001411400f0781800d25100304032000030410100000e1417030004140d43d0340100c1c9101d98030b81110443c1c03000c0d06000c0d40100c0859141c11282444948 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 252760341 1250 252759091 252759097
    0x5090d1a100f06031512050d1206050312160b090c1306080c0108060102151f0509040209042d0b1e0c0406050f040b0315041803020312040303090206030711010f0c0203 73
    0x503040c9800104500ba000c4400301e030250300d40000003c031b03180103005002c02400191007030707003042e543c0d4a8428801540c80103000fa138045005650b4590450000030035444001c13806005100b078190b07041500251713591516400e04c3c0090704c1c0c101e9507410803840803401e410700e10780440c0344402c0c1c40c600f00155440d108a054550500f407110504000800e80807030603680c82000080007843c0c407041c0d2801e56040250442074603c00c3d1000149c0e4094041400080518141008620641d009841103030359540300d0703480003440f614200b0b030300061180c0d18074490491103941003404100c81c450304c015811070801c94034607591000880c00005040101c4410820582ea05030b040d241101c01070b08105072644000c0d03044000380d00554118030140070022013045050000116441c8025205407001c00201600550303144411601000c090f01603841040303000c0320100c14459144d07000f40030346800030300b0320056070003c5d5013a032066805100042110b003a0080d014028800d5010b4a8510310b810005500041c4020b51640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 252761591 1250 252760341 252760349
    0x6020c011b020d0813090b03070518070c140706030e010f05040f0f0204020d05070c02011e0203070f02041d0a030206011517190e0f010605060f160305090d1a100f 71
    0x83c030450540400c2010030700640312008211001c010485031140e41280041c030b084d02d165807081c03081d50400201420584030202a202103060301c08419550140151128034003402c003103d40f99044615048000010300c00d0802a00180d036011944ca18058001403d42e0003c0e007607041000c0c1381c030040c840040c0340c0c2c82c4107401195020b010a0302c4008240000f86c0240941d1003098403250030107080103000c0390310001c282e0586200b625a181c0c455041810300c0448a84d4625000140c0c2c802c005000105200142c4800900c5c80100045030301ca000c1700748501014650418000ea607804540b089041603018000c0a02404001e40380c00445c00602600600c031000404c00030640300c202d100490b21801014480070410700c1030300310a01503048456500341e91113880d0325800d41554070f440d1000ca60f5203440c0007210303c003000c0708034103604111055414200c64248080102c0600c0003c000f50621500c6115042244600614203500101c000e0130142e4a070b00310007030100c440f08400724000e00240c1800d800c240192 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 252762841 1250 252761591 252761599
    0x105070819200f011a0609131514120d0815040603050a060504031710050904030e041505040e1507200a0c03020f0d0b04142e0e06100e060a0b0d050106020c011b02 71
    0xc001071041100400c5461049c048508110101042046500c4200d00311424165107000c1101d10902e01a900c415501c6640b900048804001c03c3e19515040c1c0b500e400b23600c0081001580556a41d281460700701c0e01441269990703140c8c000c1006042e044000800b040c0c4164140c52a94500402c410700200018091340d48604070b003102203000c0c144116250454180050300c10005800c004a0b00c20300300b000d500c9a90302c00c904180181800c240d020442000e1155500386141e80e5131148901580c100705842ca0315800c441c9000b6820304c0040007001004603a40c010652188040e0940c0140f2640e40098042d80d40a10003031110f4000185002c0800713075010740c024007003103980022641420304105035070060550002185690310b1076410140f0090a202007014800c010784041c035444c40f0349520048401c60f2202c540c2c00c00070025042ca80106580c01500107000c115255100c100b0000903401602e80400515030710300050184a404010505c403602007400c00c0344058440d107002c0c0d400f26201c904000e0007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 252764091 1250 252762841 252762859
    0x3030c080d0c120e07230315130201030c050c100905030f0409050a0b010306080d030c050d06060507020a14060f0d06120305180105070819200f011a0609 67
    0x14004010199140540005018041a81030000090400e40c5040f507004040e444c10340809000c8800180c07480c2101c4008200e5000050440c001400f02041b070160136406010b1301581307151010303111818034030481e1a8417041640702c995000040c200d43d958010041400820422100e580c480001c415200d001142000303c0d0300c62031840c1c12800e50203078004e09400382d200404c00cc41c0301c550f02d400151185440340e9042003c62003120046083d0361551103010745940102d42d182c03141600c250014401141d00742400d07031500c208085044c0441b00c46500c010b00142011400108501d05041184020091140082004202980000c005100e010164444004001034040317500d960380d0000e0006042160100e1a00c0010b0f0401078050752041d0010344c02030303540402002c1d00b58004c0c000e407078920390440070032801c9c01e070880d481689811613a60380780103010075900005003104a501c400c1e000b00d09480080c0c6203140398155803034290b8202a030501d01c4c0509010540090b07440d12011b9401c6d0350012102c03111 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 252765341 1250 252764091 252764093
    0x90a1119061d0a0617180102030a0605130204122a060906170c030a0c0309080a03050103150c0804030e0d1b06020c01140a03050408120a0504290105010809030f0309010b0118030c03030c 81
    0x1504546c40080d0341815400402000900b4226621800c129401034130340186802d0441c80b124200e10aa0180284403445160700401080300040001501030000c9141040181440048510710803d90302040008801c200c0c140041139001d401c0c0e9441092101032264241000d52402c1d52501004080500c890703a2005a8840503109800180c60185c100805641e80c01120300f000f00031b8582400162040100741c0800000310318144035840c41c1032075075590310981d91074a9a044403040b50b030801c1c040d44142c0c1d594404010603440d0b8084802c0c045070000044400d850120080c0c20000711050300342c1400410248005400402c5007110907140d040d140004490783c40c1d1811104901804601c0903a500e03a000400840ba00541e002900a0340200340390030007400c5042010081c800002028003503842c2e40001003085501600035281c02451081c02e80b070804841d401c405070395130011103410415a44030800d45010356006140c1e403010501d01c1c04c3c9003c400d070850311602c0c440b0342d01d480014104040d0100c660 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 252766591 1250 252765341 252765361
    0x506040803060613290301030803040f020a08100e0705100503010e0720010b011805011e1b030801050907230307020304030c03050105070f0503090a1119061d0a0617 72
    0x1a6000ca4490080107040d5181c6a41c000d455100070000d100321260340c171a40900101d410305680c126580034603d1841c6a840d036549050390b40440c4412a0070550704507010442d00014050402c030b68a000030002218540c0488042c60318003198404c9006449519a810351280d0050850707054841c43e1100004c1038032405821200140348188482d81c800060b030040000080640191030a25402d0b42c40201e150b00060503ca42180b540c403d0a01081c0703004110650205111904008035100d4107080b6198080c031150f5185d041d89000040303000405010040c895854000041074021065151440c04816504e070341d2044280c86281030307070205001100041c0210310800845000c1e69020380384250b2580e59182c818040c01c0c060715405c0206d08540b042c8000d07e40b0034010381b48a02d903c1c00080180d10501c0d01e84104128096141e030750007181c00e4900c802094082c264603002020319942d03602d0b0b2405400c078010b0045c50107050440c0304010341c050400006602003215907101211240011541d00d940c9620 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 252767841 1250 252766591 252766597
    0x160f05030709180f0b0403080c03010e0112060902191e1428090203071101050403020d0302221d0c0705030301170a05010f051005010c080a05091207082805060408030606 74
    0x600444076083c641c0c0c01c110071088011b009038480d44a07102c00303450310504152280002d010b03c01881c248003004014544107440059249030007000001030707982e10364010070b007031186a40140000a48213401002402820740e56440c0c54a00c0d019000303541401d00d10342c02d0b000c614004440e80703d10341803a00080d40c1503501c00121401195000c003050b401d43e5685080740650821180314000c281c0d404040d9888001c18029148a19031640c0074106182001000390000d4010041000c80550b210309615681030035036003a50050034840b0612480c10664850014a0180040c8a6054520188407030000200c000041e80d0544a03551050108040b400103202d2520580340030103049503003000e6090038288002c2e0f104a00ce07004102c100d0344110707201c00066401c01051440101480020411070640c1c600c030780040c2c03450340790042c10100c071321480d0340b500c1d840c0200c1ca81002943e9084550083d03a041258555107600340000881c3d10304a2000b5295942c80d154010b1000c0d100400c0040050800d0740e5503412 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 252769091 1250 252767841 252767843
    0x3020901090b18010801090b010e041a070912080403022706090703020c03030a0605030c030d080a0b060702130b040c0c080d0504060b0301020d0b09060a0f0603110d0e160f0503070918 80
    0xc0c040f85580e490b503681d406044000e000356409a541d03800884d8000907502100d10646c2c0010f8038000850030790340c0c1c0c070b03820701ca004100108119a00101003075484076201e050300791b41c1c01844078945860450041003203c0324020b1101001d85140000311b0386241c1c0038112079030710190894100d11541d42d154402c0d400791050942140c0b00d4040041001500703007842d40b124043c0c41040e4102d0f45c4800714041410394585400100f400411810000a040d0240d0390300030328200c1c6405002c1c181080041c3c0e0105010a81c156007a51107207890b40135440e49030a091040c0c03098003090b807815060542507a03c2d040b05030311510102c8824981c46c0d00024041c008203410041682074050021552600501c1441d401082c840ca25148649043c602003602d600e441d0b40700c6000e654103003a944041c10b1800000f03500a0100082103050460240000403035000580300394104120014040c1c00d1100d82c11106e05900030050304040700340c403000c510078080c070748000503010180c0d421180001614039100c0740000d0b0318180010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 252770341 1250 252769091 252769129
    0xf1b02041b03150504020c0c040b030106080a030203040905251112270d020a120c051905040c181814011d100302010c080912060a061802030103020901090b 68
    0x764250039038540d000c0c1060603a030b0030036801282e403900100000e0b8407030b400c201400340e40007803100b08071032900c0d902031400c1990040002036913503a12000303d810402004401c0d0b0258002141c104615041401003650010083d000d810002c12190700115864900c14a907400300000c56021402a9104201282410f00e038082c6143e2034221042c020b060451a440361050345202001254806040c122440002160300402d00301d64141808000d1680610884c0c0030383d090200402d0000301d5440710305e441c4419800c090000440c680c2000140310903103160b501c55008100300500100401e03450b503070701d040503111100440c3c0445982050304502a0000f0320f44283c1c80100400001914060074951607505400b940d0040701e2946c42181c0031841140340d10000c0d000c143c04501481c0002d40c18001464107030002481c0106420042810ba40b41403002c0396039030443c44d038a80d02844280711880640000219140c0e055181d98110750104200301d5042c8070740a41c003a180c0d588000b1546e240b501400788140505 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 252771591 1250 252770341 252770381
    0xa08090c0a0b19091206051e070c020906032b02071e0501020607050f07020904031205070201090b091b0402030a02120901050109112805370f1b0204 65
    0xc032030400e9110010014419524484640e80703d802082c0080c200d90f0981d016507000e901301d85421025000040c080b140b07880c80020013010344820011454040c28071940d5007503000c0024810311424881c041c0c00d29120394010844880b00721604003405a51003481c4400d101ca5882e40741007a45445c1e41c0750854a207100e01c0b5030420b1130740c424071f080d881e0844800b41e00715441e50b03d40a9050760a84a40c0411001908040003200050300f415111690468400d18081e95034080da00c1e40401141c40548070800142d440361003000a004800743d000d604454118040e0007048207814400226000300d0200d00d0003260003100041041850b80c1c148e0701d0701c6480564600e15480c0070100307140201024019880c1d4640b508006050f0902e4400070380d5403101d0032051140740f648500c0c02c1141d100f44e00003c800c2c10840c04001c0321800303458001c00c1d00560740d441c0d981d55650f04010046c048840c0d052480e20700411070307440c0c044500e0a6114056510305508030500a810090600100c0c001d0007004201083e83c00c404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 252772841 1250 252771591 252771599
    0x30907060e06192a1502030105061e0d0501090509010e2a03030702100816140301210501020a021b0f10080c070803180c011107061d041b1d0102030a08090c0a 69
    0x21104c0808218881c0004600c0a01600d00c810201e000a00846401040a002c034814120b5107480d081c0001c0c030225030346403c02c4810064501560000d8101d0100aa250028000c00c1082400750080100440c405001c01399598104000c240c40c050a9604031301c03034103440300d022a4034140700b1202215006001107111029044002d008603800342c80d00d4401c004000040b00316640b1860380d8084607000170b403200345164070348140601c03001c1001002800406c2858010000280244010b1a840328150042c12000054550110814041c0200d50b8090050b019001c10140e40e030001304c0f1508407080c01c203060103458407540c0341c066000e01d01000381641c4000050004c00d0361325031114801e0040d10b9084400c031aa902004460060b032155022465900011342801018020004400c0302035051391000281405400007509680ba840c840c2d084100e0704084594016a00408600340a811403c00320444411540000d550380303d4101e01d00200a21003021803100e520600c91442a6480181030140075a21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 252774091 1250 252772841 252772907
    0xf0b010e31090203071505041502010e0a051b06030f010b070f06060602011e0e0715020c0303030c07021807090b0306060c0d0f18050f040213050a0b030907060e0619 72
    0x2038842c09911922400000203039a1101200030098200c0d59903801d802d1038541051710800c1013040009100355500c0d00f400e140540303020400b03806420700840082480c1c0750904d4800d039041c2000e40f0010300a1a04108101003003681e0003285044032100e0304025500c04131741c200881d64842415000301610b040200000d082c0d039054014030120380f510250003a581d800000340104075500c40c5081140c98005c402d0030007104440c0740c07014040c410301e4015103c00c451074400080c21640b08440048228401190003002d50414015054403141441c80b82066418403032000380c86240b0600c107804ca64000000040e2040c1c480d0400c0d552404640d01c11940c50b03002001d400390450429551100000e424108058101c409140e5008201c0ea0003901d01042d00c04008240030207940450180c1c210b181da42d0f1400103958480040c071400030403441c2c20359500c0b400c0030501c150600e1034940c807030002c05ca008004408181e581004582042000c2c2000000180030024265442c5a0010007a4071611454201d001031400c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 252775341 1250 252774091 252774101
    0x1d0618030a2a050409150e0309120105010f0501050a02063c150f0d0b10030507081c0804030503070309051501080a0302061008030306011202041809060f0b010e31 71
    0x10b4124980c68070140c4600038441100c049600141c40358141304051103c01c0301561049180f101244142c0745014014404501001100d481e06c0042c1d0303564030700400c00b007600c50700c113140070b0202460594902106013800956540c400741100090101802c25180310520195015844040c0a0481b11540802940c0c2203281750084501c1703550301c3c1100310b1044503468461407010400701d0040911101c0a11511070b2072054400801000b82c150022101002003041000210003c00603040101801450314110704010102041c1420601c1500400d200000f50004103407035115880340f50000c1d1511a44c10b200340381001e441c4a18546c5140c401c000304d07081c4801329941450500a0b02200e015884003612281052582d110303450070b6030030900c080b80480d03100e18118800c0041d241000344c10a51103134104912400e280d000403404550302c55040080100ca0301410046501c440003c00400b0748110020b0011461518614440c80e0300700e40c55060a030082c00903018024400003031a1822034680101e4000b08 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 252776591 1250 252775341 252775403
    0xb0609060a08030a03090f0b04230304030b01090b0402130f0611030c030417030c1204090509030c0c01120e070b040905010b03071e030b090f04031d0618030a 69
    0x465400000d40c050030030045a80445240a00944c64140900c03000c4005014040c8125401d030031010150000c1860360f19070601884c011000c2e0384a807250840c0d00c005e14188200b1040325030700705000810100340030030038050440722129400f20f20941c00301d00240c024880c8103a00300c4a5401d2007408076035010140106010784840b82c9407500302600442c0c040d03aa900440d80d10304802c2e84100000c0c090400768101c41c4813007a100008507401d000884074054208403c0101804000d840424200107640b82406682c1c3c20000e02000b039443c00304010f003025154582c1d0301c4098180440c1841407021070160b03600400c002e010013000e0300d640d19150034400020303174072910511012600b07000000c100f014400003200c2c054585500e6100012283c604035900d407114a400c5801850741d42c0611700880c0d117079000318034841c14400425003c640750a16020f41030a00c0480101c171400d181e00f640485a440f11000c03207490394a0031510602c0c0003d0307070380000d00e0025812001403103038030400400c5890a80e10f2031038a0f614 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 252777841 1250 252776591 252776599
    0x803160f0903050a1209120b0708060d021f020708071e05010503010e13080906041509091526120712020606150a03090b131a04080a0f030b030a0b06 65
    0x10150303018003150051000e00002d072054006890b10750001d6100c4040f948102114142012129580c01c03041030078080d000c0c0140c075001c8402040043c01070b8002d43c02da070b109100300c4800c002c0c04040e401007016a00c40340449031000103a0311001144078020010003005106000840d15160f840349114068601c4084c26141d11821482010400e58060030549068865445600b140d43d502c14040305001c419000060b40e50f03600410403101e80c0d845060081010b880810403151101c4900c1000034500442c507406805c0c000c2c5024644d24404100180d00c038211442c442d1044600b5000102a18000402c2401d00b0014811138140c3c000120302a00502541ca010705d143c8401201c5109050340c40e4042101e400c1d074031814014088481c03100c0000902601a050306d000030300c07c0307200d50320b80e001c0500a5074031044000d0082d11b08810000030400c01ca0a00039660b51190701400c05039101e40d13150058056520034400c81040b9154114841e0348005101c003030082c102d0b03602d601c817400d01c070f1aa01001e0368150b0203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 252779091 1250 252777841 252777857
    0x12020c010e04022d07020301090803040219062118050c010f0503071e050c01090b01090b060405060702010309020d050a060507030b041b110c0409080c15040b040f0f080316 75
    0x10529181c0700399810000413075000c5607490707a900440281071040d6002c0e11007404c418050000503840034400c0e54a07c5228122240c0d40b828a030040104104258000481204c03000100340407042d070140341c40909401d07400005490300500807030302c8081c000100c0103118550241c0c039920709020000842d224514400c0e01c40082d0142c030103030101c52620044502b07002003014140644105030101401200300810307450700c1820491003220041c207481280d41c0594004001e1390041c801c902041c4035900c034000e400c0300c0c19440d2529010100b810350159000c042d05140d80c40403200159100c2003c81c40e46903912200f620104c440710319100340109410788807038000901d0181c015020342010300c600804000f09280e10080090300358012100500d03c182d00c0c003042d0090452a580d207031a54058541e0081c41102c985485030100080d031890a180203681030031003594103050102240e4200f110603003242d000741448120110f00d0406440c211840400203040460000c02c02400c12915004508039901c2540c40d01a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 252780341 1250 252779091 252779117
    0xb0a08010504050c280b030c0c010c020a030908030405031506030c06031e010f06080412020115080709110403150504050c131401060509100815060417060604050c03041e12020c01 78
    0x60440da882d451700405454100c018000340e0281806103a01500c0c2603081072401c183d0120403801d40d4250030980340540c1c0301542d0702c0e04043d0420212001b90420400035400c2c640f0313080019030366003910b216451603282c0c504040b4602c1d1b103050044007944a4090b0141d6500d0a01d5108e000d4101d141ca03020f42c1c10b00c01c840c0000b04080300c8071310b000b40865000d40d8401c00c01d03072520780724443c3c4042100d00c0039055660390103180e281c03008890203c40c0181108006004078602e01907442d002c0d900340d0300c2d1041c0107107810041030000a00e0308074000c05c4140c007110000384541c4c13203142040c070380340c00d034101c19031b001701d840e8860b00c0a18502e400c009180c0720903003002c80c920390744c0e60030507251401b804c8291a44440341d40600302505128800707481c1c0c40070340b1045000700e00700500301060944c0c0c00b80c0c006105080c041c014a44021900300401c54000740155070070001d40c40d0200e40006d06000290000784920715440203219031095a4408004040d000561010710000fa054003070750310807441030502d012030307101c9007101 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 252781591 1250 252780341 252780379
    0x20d030b0603010302090606030a09061d06100b0406140403050a06020c160810091e0803011a070f03030908120f010f0e220f06050c0901110a02010e040b0a08010504050c 74
    0x24100c075400703040e030700d11b0380c407900108183da410050100b161169581c40100200300760340240d480d45200280d00507215180c018880f030806400a000c2c080c0800b002d40200040c0c0000c108803821915a450040348a144039188401e40e403041d0391010307050b449031030713403400503c03c1950041041d8007107582111440c0314948080c6c5521001c42c480c152903a0050301c1c041c24501199000410316500c40d540007034411103002440c5407001c0c01140155420040880140868820f9031404e6a001c003801d0303080750030030416584940c41c03160a07800040400d6200c103240010049101e0540b1a11881096406414a408c10854503c031009102d0020400e40811001440c820049041c0f4090f1503001704c5c2c2e0741c100d4599169243e6160305100100c0c0c0f2120701000e200040740c40e0703104d054016010303211a01e40d82c1c40408001080c02030300c00341c0380b000c0d504403c000b44010303a080500780007030900542d0007207007242c208400240ca4141540c4038080300e508000801040080120798141350b800c0c11116080c60040c202c23484 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 252782841 1250 252781591 252781597
    0x207082d010513060f0e030412050c120624030604060c08010510050d0207021c080403021801180e1c020604020414060d06180c03031d0306150909030c010606020d030b06 74
    0x121071410800f00341d804a10a50064100080d1001011a14465a40f8000d1031603006900110502d000b40301c0c410f04100d81400f00d03000c0d0311011104903a00003581c250341f0b41c8410024200c078101c900c241d1800c010820a61004450082d0010305444651500d030500034040c01c000c3c00a1000150003000200d82d0b03191010041c0213030452035a400741020011b0385100000c2d4403562069900240d03d840d1144201610000311f044030344207048180c2ca031461441800311309158004c1800151140e03400611444069180c03032001c00c810040007041540303041e5512803e0140c1a043c410560745070440301440c0c0c9800180d801d001da0b200380c3d0200b00c810140183c03e1412141518400e50150803403050801180903500224501c25190740c0e24082c183c3c050755454140b52039584203d011940f07401d40f4608548a150140c65000e00c107401401003032400503c00c1a80c0d400901c2c080c2e12840502012a170a01010000c0c0d46040720100020441280c9034000650b9480c01501a080000c0c144103c88404d41810343c15 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 252784091 1250 252782841 252782851
    0x9080f0307150b06040f0314120d0f0e030301062a021503150a090603110d080405120a0210110d030b0105160812070503070f02011a0d030207082d0105 66
    0x9035081c615a0768402491542c0ca00e4420421501c0b0a019a200e0742c0b1040140000d040c00241000f43e80d186141031002c085c1e2407800554250001c00503410001001030032250000a810400603122010403010801082096103203001d40c44040f002103103954006145a4940404100092056440080020105003403d80003500401da0300b5100c400441020043d5401c1926003841f0950040c1f0003004c10b4011138a5400320b88100d41780c107410410f00040900c03150340042c0c00d69020b002c40c810f0b5107440c5054891446424000d4549a01c1400210310501c0316031070040c0d00a088075023640791814020f11141011920491900400111341c07406402031180d40302c40201a12800e041c0048804590904030354600b007036402403000c0003d803d0000c00d100d1b005208041a480c1c1c161a4280503a00410710a146e4038003034156031400c00178800c415940c42ea03400800d54210744a03036540c031407031030304a00b4070203150b000d40054032841c1006940020407420240c034100e410320700924034080f40d076651401d032041654 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 252785341 1250 252784091 252784093
    0x240509090a0f140f0106051203030402240f0f031b0c100507050403150606080a060810050403020312090a1205270102010618050a0f0606090b16120c0309080f 69
    0x741d00000201071805910700b40c0d002e21144908201c0302000d050070b03c0ca14254801113031b5540e100c1400325141c03c0c4140007401e40d04030025415850268040f0342280c0880400075401000511034208074042001207903851300f03139820f4003a240c00761140007000780c0c0c0083d54541d0742c07220304003500101624010103031024191010000c010803100c000b41c803002001c0240402c010040700b00000700110f610380000c4202c01444190025901d441c00c0c0004200c0c80020b0404003881c1c2c200b42042104100c001a4186800e444d1040043c483d11145001d034698401d20103100e11a01c0001e0400c0098140860b242e08140c1c061000c12003500806002110b1f64480c001074101b0b5950382402805008441c0c0003d1040d0720418000020001c5c0c840d4840b800080d0055042c092035a01c1d04100700740c520322805401203250702d506050080506205000d4800c07440d034016440c008901040c00c884910605100007c200e411803921540303c401c40038000e11584000900b40d010811820002400140002c0c1c010b00030000b0f44 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 252786591 1250 252785341 252785353
    0x1018120b16030e12031510121406031b0303090a0e010807080111030103030e0a03050105160e10020c09072c0405062b0201031509060f0e10060e0d050124050909 70
    0x12100e20751341e007001d4621010b80100b1003012499880311151040c118503d51608022001440540c005030354403401c58103403801c806000d00c1101c1e240000d803954a1000420202800350804000c2032a500506140581c0f2400e41c4000040941c449070205060369002c0b800c0c0d5800b26140d815441c01c1e1007401ca40b13074980032010070041001c0703840340d00e065400810060003225051340d641c481b0b900f90f513825a8100d40e13041585981c555241e030818058650100d0681d00c50360f20b00b0018030003a440742416620140544c61040001d82c00328410301e41007568560901c6c0c65021001d104000d060712030f08078000d1078062403a005c0072030510305d008020b0710622041d44600d09207180c03910714401d1030b400090100f01e05058641021011150043c0303a8440601048030b0700080e0319107000000020300100381e00005006034000184aa484041221102990002d0070840c1c05440d244000c51fa060110b848041d0aa500c1d041e225016040800000706101d000820940800c0f6201d00030040a880161901c0e11581c1c091 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 252787841 1250 252786591 252786613
    0x60a0212060d0201020c030d020c010905011403040825060207030f03050424020c07080d02070f081b0109050409060c110706020304120201091a040305100b1018120b16030e 75
    0xd10b4000380c10900c10b1050b41c480c2c41c440404680b621031901e90410240e0040114096203590052400008050910b44941101000d0602150512000d40058000003001511828600c201d01c10100c4081d25400390f006441c0032420b0480007904510383c118001407603036000c1c040c0300f48039004290045400c8108480780c940b0700800c1207030304034182240c00340c096000c1c404c41161310b80a02c00c0d1001440541c4c0503204052407600000d0070502683c02886000c04080e40a0041b014006101c080701080c0e88171120782a6505001a510039145602044c3d006040601010400c00300340c02c150b01f06203072502d4281010014254068940d01c0314052640168000c3c802004071b210400403002401e03006050921045445d0038185071895072002d20b849140900103005c0082010810099220b0401d400c0c080004d90790360710000c0d80d00d42c0c60380b881c40100820314a006051540383d549680050000c0810500f00c0d200b20701d4170b0303c1c5001c42140c0d20901c5466094000207054064000c81215000300009418540700f0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 252789091 1250 252787841 252787849
    0x5060105160c05120102070212010908250f05100e010c120b0406050a0308040312050a08060603271f0902010503070804080f04090509061b0d020c010b150c060a021206 73
    0x8075900c1655460160040002c5070b88404401e1207101c881c40c0005a968200b40c018405da1410100401040d0782c0b42c08128800304800405407032650032801d0748101c00030a20404248465205640a4010780342c00102038104040000c86c0a16100c4c00b1105100940d40191801d0813141d4442c1c1040100f0700e186031050303c0703a01c030f6403100c2d28101d001000003030107a494401207452114103401c04c880c101070005040c800c0c13040722610040451000e180040c6816041c40f80200f41c4500075026038015040840030030b100722101d294044001420461643c1000a40d034003090b542e491072135140f501c4058090342c0b504a41c0041c0030701488660181c40789032842d191a081140c0201d8010011786680500b48200342c00d02030500010070041c1b0324000040749504001c1803850a0076406003200c484a0b01d8080300d420800c10030300582da94020900e40c010f071280095040b0078090800901c21950101d0007106004076840e418018084240400c2e045518035900c0528010807071140d0002c0100c0c0443c0300c00080c1a51034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 252790341 1250 252789091 252789127
    0xd120e0307090c050309070b1305090a0e0105070f0e04020415050919080a060b0607050604060e0c041509050123060a1205040f0204110a081501170702071805060105 72
    0x14090101d034503140d9510030a03801c54443c10402e4000601c00400d11001500030000744002d0610150000d2601c540e4040140e4101100c1c4905405041d0705d80000d015a1b6865100324002c02d8200001e00c9113140800e0000e049081e0310a82002080700320268102c81e003001e200780c078144d6481801400481400400036a0f0a070420800d6030742c0f0140040c2c41c3c0c0141c071603901d01c40008000100003402c20408070300e0f00805035111400000e016090a00040011850000d0800e81144d08000b00081d8690301d44286810103001c00710142c0c0150070190000e9541220807580422a41000400c201c5c0ba600d515681424442c02030400306170744607200c1184100e280c240c0050400104a0600003603071b4208800c80d0302503a800711070a40d942d0501c08003000c29401c0500a1814080c20346032018a015a101d9000e444401c0240000c000c0c46a80942c0607407a9016000500c400d60f19011181c04502c2c05d110000c0d034584160040c00d03d01c203041240d0302d03481d428600989016010584076607007011031181c0b1104e00c0e50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 252791591 1250 252790341 252790367
    0x70f0b0c06240303040303030f0609020c060f1005030106140f090103030816090314060907242a0b090c01030605211513030e06030609040f030512240d12 67
    0x70350103070302c01555070360100003c10080d84030340c40220703000c00085200380440e4283e5000003a5180100010420600c011508940c040640e0440003101d440d1403400c0981a2415000203415610b061404600d03645420b0341811174003800c40e8030301c415121520a02c0420202884002c0220f01e20401144d1118020220140807242c80d11b0038040d400d82d80e4891010204548510098940045080c03060042c0184450070181c20b030710740720480501c2581100b42481948084520030403410b03c13180f20040580c0b41c49800594104e61070544212024140300703030065070565a0a4651140d800382443d9075000f4040c45044070002402c60134002030451103120580c800648034600c50140a40d5422038540e0318000d507000395144001041d820320a49005840200b040a42e076104071030038170800017995100c528159000b41d115000000204035454152000c1c02a50401c00b012600c480030440000320981c803c40c0501908842c070000d101d4207009010341c03030410303a50180042803600342c8403000702d008182c00201c0c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 252792841 1250 252791591 252791641
    0x20f011b0f0b18060103080405060f04080304080d09080d0203090f061308061608060a0605070c031505040b0705090904060e1504050f0c030d0c030e21070f0b0c06 71
    0x300503603541c010700900846040340c00102200c1484032450300a8468865083d80000030030f0154156211480c40740103510685110300390000744565901202c10665008107041400c0b00c1e00d4948070a28103884020300303001100050754030072000452500015195001d148550040c502d00b50440f001e00c440019904005038100904000c00c405c80d06040040100030b00080002e4403031403c00c4080c2c0000e142d210a07c000401c031100092180f01d503602c1400c0b00072102c05080c03003551001e007450640c405012079407020b003104414503000b034aa0b25031501305920a51040200702c2c5a03648107803064441d80106c25149400c464080005000124aa80030b403404a50b0b1200700c8107460f503d4161900d542e81d089500719045d0700468510040083c0030445003c040d4030031405022a541441c800800021422070b000d01005031070030208449441c0d10600c04c42075900e201043c03483c0c038491110b560340c5024511401c00c81752a2030000060b140100c3d01a21820803002d400f404080d281d0300040c0101000103c45501c42e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 252794091 1250 252792841 252792887
    0x2419120606030206030a1e06030201080612010e33091005040c051314090706080c180a031101081b0d020304050f0312150303070f1211010c0504030507050607020f01 72
    0x144c4c2d6100040c41c40b07244c01c07001c042201021a0100039803204400ca00311582400c001d414001030382c0004929502c0f0000ba242001103074650284603014100c241203900c6107028004112007a0050b03554041d0600682018407080f1140786280c840740200704480e942116006449800721500064010a4020b40120560b041d01c0c2d03203800c00200300306416411010103da658440d0002c50701c2d200c130703825032010542018102c058907080024100d5200101450f2084100045003e2a80200740d580181418042c01803801c0300d4607440d182c0c040030150582280400d040900090002d41c51103402d24946047d03125080c00d0036800c0c2040c0c4080e4001800c00c441c903000b25211007058800400241440d10b00e500445903376030400e01c0c8244c2c1c0300b45050011500a0f0000c0080d00041559861a2000581e02003110105820a00030894001000031440c03203080d42043d0a007010a507020b000f40003641e0040c8143c44141d9900d000b00641840b40b00b41c000c1d00118580d005540545c006c0c600c0c1120b403806c0204202e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 252795341 1250 252794091 252794093
    0xf030402011e020a0b060a050d02010f05070b01031104050f01061d010c02130b10030b0d021c0b160e0a050a05011110020403050703060b0627010c0b241912060603 71
    0x38410b02c0754400c006034460600f2005214001c2c0710240c100b0416036040710300605003c0899003419020802a06005841d01d4001005200f03c0171a4145a0040c05010b09540c583c5080040c00140a42c40c6100d50306100c007148410411710340701c50484040341c0b54022446602c416100758241c2c41c3d1102414005410506d0005d80c035100d50b4800038003c05040000d0075407030b801c10044c0c20403152401300101441c1551507400740d11448140f40c2e400e0740450300c031800301d01072620010308032603480c10040c11400310206015005840c481c1d40016206a51189500010782209101413140a882880c3d0711810000c0c0c1006a54000c003049124107044200740c41d1010101032040c1c059902c10392080740d4503403084008200380701d0705110300125200203c400b541741401203401c0e0704030f040e1480b100c01000aa41c0221607596802004002e100551000340c040c401d20302081d448050244a0303801c000c1a948004407016546480c81d0440c851508400305044201e0904289090703654a01c4021120580c1e1004084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 252796591 1250 252795341 252795377
    0x307090614101106060d11040c0e0f03010b2103040b070f0b010b03010605070b101a09041a06030403080621060a0f0b0310051e0403111603080f03040201 67
    0x5805003050301d0607406101d18800038001a105400c06400c2040240c6144142154001ca110394104504032220202c0480e60b0074009850000c1c030284d554450b1414030541441c0b60492050358003a10111048030500b04210181401e0b10581c0e18441d500c443d048520710640d08d95030701c01080700348481d8100d9051a48072034030a000341e4020f03001610301c80080200e56041003c2655141e014018000344d40c0c0c01e5515198026086026119005016100d098001902c80c06034804020040c0003200b1796690142a2800307454507588600d051034091414440c0112440c00c0415904803410301c068281461760b515528100c450b0b500180070b0550290b0312021002040c4090821101c0c9020f0100c060112400e10140c03007001c40c1c09154480d0020b506111701c000080e138020800c1110442a0580800c0c141d40d01c10304550820400c08451100c92000c0d010310042c1507204500d05002601c0d502103d602804800c084000c0b00094800202449030802c48101410940c401841d0028410b0402d00e01c1c0e03d8007140c0d20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 252797841 1250 252796591 252796601
    0x902031306021614032d0412050a23060603010207020306060910031b1d0115050711090405030c0f03030c0403060c02150114010909020c030a081306140402280311030709 74
    0x20759400820040b004400c1051300c808006c50a100f4891942559500460507000e58401c024095001000c00801d010060058040140d0b026111614040380300c0c03030303420030b21202c261f01d0300300d070301c98500021400e090500c01c941c521a0020002c01c072075610b02c0c08001c0c060800408a0500486040300040001c06907015020441900345c46e402c51141030020010040c1126211241c07110303201001048803050105e0754012100c22460b0084e603544160403e4200641d1035000c150700602d0460030072007440404005001303843c02c12000d641c030f07102e04821001d60764001030322400c101038010030040000540a901003c1260100d0040d01c4101000c1028003090b840240d0241425060f40441d41c2d030b140d070344486008040c0c2620354045060182c0000910b0341d03805050904024020b01d4008604812499610f034100c1c0c5a10400900600e00c10900a03c1d12174800d88049008514543d030400880102800d407103548000d418031000c156141d0380b246800c2417801d00700380750503000302c920124005c010780c0a0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 252799091 1250 252797841 252797873
    0x1f1203050306090601021524091306051303120b01140d06050102060709030f08090a03080714010b01090806042301150f08070e0a090c050d0302060a0609020313060216 73
    0x4090301d03460042e003032041454000344500e045400c810100c5400503029090541c001c18442c0d122102d5242103149105003204559030f00d580002c03100d0030001d01d2244d0341c0440040602c0ba82c01032102d030b1100441c1120025000300028081080b1040d1114840560f5210292040313051600301e042141c01d12014086074042c0d842c03211f50944448080c0044d580400c07060b50480300354038012800354035603202d0305076043c10440020300110000130408a55074600c8111006180c02c0100140c0d9a40c192070f1070741e1072010302142c01e903903542031603081055036009605107002c0701d42c054060040c5070796680d038030b40141c0303014264840f84280d0040c003024003400901c104211603001c03005403108181400442040c001c001e03841038040f036212003400d10040074003005c070356004030050740d0110742c05095103887c460342100d0b90415900116107a44003024103600044032030060340c181000300f1004d519400e0f0b06081e8401202c44c024100d52640700320b4005182e1794000d2020306080120002008240d565024081d800141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 252800341 1250 252799091 252799097
    0x6020c1f020114270c01140c0f03030f0912071205030402031e0703030201060b0304031e0e03100515150405061602090106050702012a03080c070605010b030901061205061f1203 77
    0x30b1255035035214101318a00184005005003164080400020710860b902480c584c4074030400300d031980300c2c0d003010402091061001e03016644c0b03034544580300d01c014100840b81a59540706540c001111401c401d0225280c96801c1040d9240381021210b0075241940050700498141c070a0584000c46c0b14010318580b0840301d440006060791521354200282902d4090f04948a503080030824480041e0304102480042071300340300320805007500c2c21402d0b1100000380304100d8043c02820126149240300d5440144141000950306100c2680b0005000428441502000a0301c00c100001d1200e0302c1c12001510b08000440320320842c095440e804508400030aa114801007a00802c080b001c541c6c210300740d0103040e0310203500380d8541007062002d441c005134903e0016050081c1c01b80070811a49198007181d800341e40140b8144203030b507541c5516002e00d51080394100060751804a02192010b40d14140ca102260880002e2003541c440075141d1102200045501da028000c0d00d07400140301d4542c0c0001505d86009803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 252801591 1250 252800341 252800371
    0x92101090311070806130605041e0602070201201b0f04021603030b12030702010c14030a0c050f0a05100c0e030604050c0108010b21090304050a081606020c1f020114 72
    0x248802e49885495080301e0740070340040c802c05c0b00503400344200a4925410210200380c58035541040c0071140710085540285641420301507081c000580c00525031240300780d03a4002c041011000c181c03030b58030461542e0140c40e0403c402540e150048103510306080800104401c1340c1908600008040342d004e0905030035500741e01c01c0d00d5418140c16218844940509482c032816010222017090b4487c4110380f0000d0600c500600c10609000300751800030364400010301100c0d600c4507000f6002e0f24425120008031240d115442550b90000300105420140c103034060028101c0382d000e865240d025083c081001410080141c0f040d2505580804c9a00c0c0281d0040f07003c1c042c2d00300f0500004140e414140c0081c0350146040008214540340c02c0c00030080040340f11030401c001d0720b42c481c00c0c03801c500c190782c0308940c8800040f1000c0303058203022507000c038000d45c264060106199509070030380c0c59001756810550300c28100d641401c0581a83e40e484445109a44000607080c10f1010000c5440c1e02e00360390740c4603e10000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 252802841 1250 252801591 252801617
    0xd170a0315050111071e1220030c0f090c0d0203010b041401090f030305030a0b04050711010f060e061c12050304030f0c15020d0207060504030e1c02060921010903 71
    0x105980d01c0034040a00e040340b04014400340803a40c2e280702c1d10480d442c15454409182d402c0400c019408090800700d5441041d41034503040020403203043c00c102c2103581070b441084416501d4001150782440b0380152100d40f882019004000305880020300303c601ea10303420049000d49500b284029070113400749152040e2a9804c1c000009003050002003107905101d0345202c01e0104070100203500048990518000d9542e5443c2a00e09021304500819035800a040809001c400350b0088030020081803103030300801130884030b4402030301940c2192180c04c1040d0108400f080941c100344111020b016520341c01d0b00c0e40040700f591790001308040b07040c0c8100062400320070302c81016440b5106c0c4042c4006494801c1ca80303807441c0c980d5039403040d1459903091842d43c0010300b20920b400d0758058500f95900300508018608d0701c3c1c140030740b000c0241c01c2024403501d40500640714080242e40d1000045402420403030810080c0010310840c0c0c1310400b9403d005030010820a80380100c01d000d504c0300a8440e5441d0b503915418 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 252804091 1250 252802841 252802871
    0x1b0302010905070b03040302060c030603010b10050c0d0c0c1a0c100c0806030d0807110118060501030201030b0a0e01030201080c070212300304120c020a06050301050f010516020d170a03 81
    0x350f8004c4e4020590400c01d00010a90010b00380d50000342c040d01c569a41e031aa040000c7c0100443e00046410800104103850141d4201000e4170140080405840d807245010a040f10b260641c18402404030715801420f00505c0b0009614583c58110182c1241c60b040006448034074128030100c1d0442010707204c8480c120300b81d51050641ea0400e030300758000c1030f01c0b010285000d402030340014200c1040150b107100c8403040384000d4000081142c0f904481c105c20030a10306000300580002d000590119003022249025400c2120006040b01c0710b40c01102e1242c0d080d40e0045404203409404c0c411307110b070107011a00241c3d8400f4141250110607000504100e000180d500c844804805070041c40760034204a40030110312000d0880340c0c041c0d1b010369002c806030392410007941c00b807948901c080e400000c001404681307180c0100086050b981c0455020608103042001104d1034492104001d855103180c01c0180c005090500e0a081400d10442122600b080c1291030403078a40c12072440b03100000d03203030300b0813400800c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 252805341 1250 252804091 252804103
    0xd0f0309240f050f03130302120703110c15030703090213020c010b010f0806030d1809020c0609010609060b0904090c08010e0307020109050f0901060507050f010606120b03070e0c0a1b0302010905 85
    0x3620f400d03e00d0500e4014103841100b80001003c251001c0c040c021000c042510a00c070446080303008419050321550582401031107070384000e5019403035220302d080c40d0040c0d04c0d002204040c1c100078600210f00e95503421904801811071494100d030003070b4001c0407403c1c0460b80350014000ac151111300000f1540e84d40c00c00100641204140b03001030018200620500e614045030f02d8003148007905143c000f1505d2140b413191406c1c000e40c000c004c407501c041041e001008011940354001e0382245d0083c450700c7d4403044e020044840c41e100b880c2610310b00b00b0120b1264209a04040d00640c000e1500d540d400355180000b80c29500300740e0300b41c0255000000c68500319a00484400068241510004c00004649020561010041c0a0001482030101d10304003000030800401030360030407075030007444095522078001d045003d00900340050103081c6104a5000c0c20300280ca00b00b00e035494034242680e030b200d0030701c0c101995000c203488408200075111915040001250160fa503d4407a030300015820300e2508005080c24 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 252806591 1250 252805341 252805367
    0xa020a12060f091e110409060501030b0c0c0705040e0a0b040501151e05010503040c12112106060105090a08060117010c02060108030f03072006160302090d0f030924 72
    0xa45800e4040f004507648040381c2c41d80b5200b85086400c1001c003820038901c03940c3c0e0803140302e510509200891041110315040346040b41c2c403d08000b101c0341c55081c1301074054000d40305902c13030030f03071151204000c146880e421100d2444207440c1982c12041c09622080600c0000300d03030554141c2c1d146e510f08502461007100480040c001004041c20780070440c6507040c8010010301c500c0d810820003001240511800103060b40c020441c40c1071120422015182110740c55911441d0b0510541b10f0600150b0b841a00e03c4064145401d024060001e50b41c2d0080152619000401e480d074102c1c43e14080490601001c01a10307000c3c014490b00c510820319560701190079502c05101c10821500440010401801d00109907440707803c04040247c0c0720f40c0e03403050440d4082c14100c0d1442c00d62001c0d5042c000d40220100300306001d5105107003400ca20f15800d80c4182c00342c1c404c1420301e42c1c00c03c01d12036100c400305a14003803d6410a00c039142955026a03145541c000e170803400302800704034640000f08401c600b504680036002c60 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 252807841 1250 252806591 252806621
    0x405010b0f0604080a1101050f040306050a110703020a0b0c1905030402030f0111070305030a0f020301180b0108130204050405010b0409080c011401030308272512051e0a020a1206 78
    0xc1030130840010340700c440c42c01004144a04007805620307180c2c0078038107031144e00c1004008a0741b966980c1c144100540320030380d050122180b40081001110343c0311011540959010b80080c00380c0d180550310007028690042a221800c030f81440400c0208540c40c901121280a03a50b50603100e0a09004047c1420f030006001000380e85012401c48a101100301902c0111b07400d410455260365a000c0400050501240c01d0903246100000104840350440c24501c0060b006c881c042100301441001503c640c1800d030342c00854405600700c08001440c0c29081107a000d4800d40000c16007400b00800305058814612044501180218841482d8002441281c44242d079040104032a5491a100a4010100605887c0500000c114180c0030710b42161504050b080c4000e046440c00c001c4032000054031240c803066003180c81c0d14940b0020b0030f4030506500c1d40d407054111010b0701003800201108007402c0340310b4a94518500500c1500c1d00540c1d10641c032400248090000008040458500070003112070b0f0511075412 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 252809091 1250 252807841 252807847
    0x60108010c0e06070309120f060e0f0705150408060f0402010f020c0603041104021201030c050a08371505040b0f24030307080d020909010812120408120405010b0f06 72
    0x204035441441842c0d050310a4401507074800480c1012120084c1581001d820b03040b0a4814a040140402c10003030303030f1406140100940c2070302b00b61403034031903060300d40e1150680c1c40814103200501d44030107910306c0500c5d001c889610b45a500e40041c0d04102c01180c1101d00540d40c1800c100035940c03c05215504148588007400f10030008900140d0302e800094405407007450b000481d04e415072659411100040300c2d041d1403540741d43c2c3d02d2170600300f0000c060040c0c500a0110590001c0ca404001a16007500717820b41c070740c440d0741c01800c182c1c024024540141e0440e010400f03440c1ca50208480410403080300360135240125003403030729003060354620070054256410b603502c603003c01001c1808409480c05071a10117040900c681c1181d030001386140100791010340188000280d001550710a903006080c2d019040d038800c40301e0381c2e803550983d454644078000d898654504100701b83c403000d0351208042e0300500c01e85041c2d05008001c2ca800001d9041140c00315110380d51410341030458070b00500020344440c011995185 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 252810341 1250 252809091 252809111
    0x30408120c06070c0c08060f04140102040f0b031e07050702011e020d320903060a060b0f0a0201020714010e01141e0604060305010903050a030621031b02101106010801 73
    0x82d556000a019000b0071031092500c804024192800b100240b200e070342102c60904007d122507074010f03400e440c12200118024001564004103000303640c211440c948404d09154a0012044550b900060070b00302011903c0300e08011141000002c607000d03404507030301c141c1c40e0007040c0f00240c00482e016180c0d0124180e030302400950f2650005921065072058500041d016124514040307910000b40030b4100440c2c2c20381c44042940a03d00c014081808040302100c12640740d08100b2422240e2900400070060030402408a018602100604511100b03200044ca090980d440f41901c2d1642c0d1140d140c103d03515051034410040b824011100c80d00341d04020301c1c0503403c0489030740c011200c2c08100703002041c0c0100005400396403994407000c025a0003000a210f030040700d25000f040b55100e64001c00210386010300204103400c3c09140c80b07a60340407502103034106807000e40b000d44640107004140c035840b1002901401c0141c5a20b481c0011400c416110340c803040c611011600d0820f078050300030541e280c6c90010466 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 252811591 1250 252810341 252810343
    0x103031214060d0f0b01062c060301030336080d0201050606090d020a030236010f0b090301150e011403030c07060e011e0e01080c070308010303030f1805030408120c 72
    0x142c010400329500382c0340001c10320f4131108200d100a0081c0c0400040d900000d06250807602c0c0b28502e208441c84403000522100c2501316920314a101241c000c0d4043c0010b02c00603000e00e024131040c218516002040c0d04400001002100c0040c618140d441c03010700080003210010030404e0500003560000b4002c9184c0070012603c103010310540c05225010201450741991100e144040281d038018140c03032481d648080d21f040c068403081c100000281103c843c000498161881c41c64140c0303203c010f11b503050030329182e42e442c6690840c0c4061981556a011034560000c001c85444000b4032007521030042c150f00d000c240d500104007445109000350803c100c0050382c404003003102020764541d802e21100400c98000100e0b400820040341d0745846035510102c41201d60454041c105c00802680c9048041c0e640c1000203420b4000c0741c200802044200d00180700282c042d40165941ca40c0360032000038042000c110120014100a005640036000010180a8080c060054050004d01124131902d410910300e5a1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 252812841 1250 252811591 252811631
    0x30f020c120d06080304080109120c051f020f03040f05010b011d04020c0127020f0628030b04091a0601080103050303072d1e02121e0903010e030301030312 68
    0x1d504000c07000603104001d18255015402a00b0042d088a0301d5680340c00020b802440250300c240c2c0d06200c2d805102d010548034180000c542580700d80070304440c0c09038013100340d003104580c0d46040071160207000400c03010441d207002d1031281b0300400c42c40221340d0460400c00d003114003040200341000960000310b403801400040b004003074030082c4c13001680c80005111060041048884440c0340d00d0348407000c01048080203003145580c03402241c0e102020450030f82000b00d030f4458090001035210000c4032480d46044032003000c0304e00416034100841d4460740000090300b102d91110003200d2070080c40200b444a5002081c07903540c0101d007070074131100035411503d449e0358a0000400304010003d800c1c10f02e64000c0f0b40490550b05074014024800404189000c020703103906034002c0805648650000d02c5007200d0304c001110b00070414001041c42c80d1030003848a00520210030311003140803074410800f11302161024408d4149022501020359225415850028200301d10aa011a0103605154551032000c6514103c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 252814091 1250 252812841 252812863
    0x70b07121505012012070b01090f0203071e02151e0604050603070e040f08040f05010206151f0504030b0a0605030d0c051005070e1003050a18231606050406030f020c 72
    0x41c101c0ca8413400794045141c400f90412100c03c041011641400700b024584860741a1429041d00344010f00420120030201d020407518800007801d0800a000444284000d1012409051040c0d84d00387c2441c0301026100322055501d0800c1d0103407801c0b4031a11082412240c0e402c110101c400f4006803d018001035590411401a0842c0c60002c401082c1008036102c0c214001c41e9100c010152202c0d52450034859480092103114050300030040015a460b8124130b006000d083c00501664407881c0c00c454640280548000c0401444800c00011003ca07446402d400e10a00010001041c428207007428907051083d010700700b03002d1040103007100e400130f00c1c04100c50080034400c8800203001d5981c400c0841d1540d1001080325004a5500d01100a044e4180c01081c45508803c0b000c0c03250509100c8900a210b00c8070360041c1043da84a0341100c1c449000340f003003403421004141110000c2e071403101c4090382d0919503400342d40419800a030410690307405015000c41c090320f111342107080000004510351610780d8507031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 252815341 1250 252814091 252814127
    0x3080406030c12050702030d0c030b0d290a09030906020d05180f120c03010506062802010b06160b0714090d06021606020d05061207060503060105070b0712150501 71
    0x19280461203040030310b1140d0f03004031052240d400d068002035100e521400c4140e501900f09010f90314028060300491040d060058800f1035076482c151200e0f40700e042c5c5a41042070348013046440c14540d61003a007095019000250b800500083d0604d0084c00c100c2d501e6004000b95045050603109a5420106850481031100015a010b901e2140005c0a084e2050900c55100c1200c0901025000b40007410102c11714003a00200030545440c810482c0b40d014000c0303245042d18258400040051405413000d00501079400082584100140002d20703540100b94191100c1d10b04c1e410002c01c1c440c822410541110041c18040304032206696410514481c2548103409045600050401c018a0f541122a0464401040b5101d4185850200302070751141e00344944840c14000490018901448405a1481014001c1c42c4c0c07185861802d46260700024010350601a082c401c0f10003040310800101e1150b440c1c0d40c0c0b40c032a5010b6030031440086640d0888a08a0881500800e019a0740c0240189800c801810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 252816591 1250 252815341 252815351
    0xd0c0f060e01060e01030812091216020a0f030f0b0a020f0304240e0706021011120c0705070b270f0d05010f06080102040f08010504033c02030c01150308040603 70
    0x740c0694050708056100059808002000006005920016221822948040c002e90342c6030301100755035a01c0410011100e2090404c12502c01178030050007212210320113800c2101131540d0b0080b00c0001d0a1a80c420380d0a05910344a110400088140003030380f100152001b103041c0f07180d0200c0c110f0b05010050000300101a41410b242c440c010320070300b00146100480c0184803180c003464210780ca0f840710744920805407142c00c0ca0440100001d000704900400c072142900d003010315955031004241d802400d1843e80c2c50341040380002050042c0a02800f070a9a81c45507540c605007500c1525010101022006e43d0800704521901036a6501c61403048480c0c08441c01c203801102828030600500a408000801030301c1d0400000f0729000c19000390044811300c029401d0b000d80c1d00c04426081c2e9800701c4005000a40d10080c58110b11a4038141f0501d1010b0b03201e0202046000c907900c02481d0344108843c00150744081800d2070320360024000c40c90220100308080710400d11b5a03403001c11038060783c002c038800d040d150307 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 252817841 1250 252816591 252816611
    0x100306050903070501050c130e06090a050c070c080c01080606031e090c0306010e090f1606050708040e0f040c1a0712020f1c120c0503040f020a0909080301080d0c0f06 73
    0x2c00c16102c00341c0d00b0200800290514184a04c943d07804800c08042d218503410340018215882c407802c0d44a008040e01901560b42d40b61040801800c000380040040d06050290030042100000c40c0740c040d00c104002860595421800544500002861a445203c080040103008214034101007809800c10150030070310f03140c0045860610390000c1105030544510360001a07510003030581c642c041c1c40f43d8801e95054001c0e0b0041144c81d0007031002186100c9081070300400c6114880d4004186480c0240e070740b1800d01c1d8036040c00140c544810746003240080081824002401060f0f41d07100c0c01000001d1000d0b141000741c40c24100980140341c0d000e000d10f40c83c2d0b0300d1180c640b4024042019030011030815201d0b040402c0c1041da24403031034090303044005001c0210310301803c0a284206142c0c1c11503500d5880c11940c5070b41da2130100b030107a450704a0700826040350004503040140614040b103846800c541ba225810100060b1030640040b569004100700484018003003099141014050b60304523602145c1d500d80c07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 252819091 1250 252817841 252817843
    0x51c02070b0d1d0a080304030c0f1a150604050f09060607050607120e0c1e150a020f0c0f0114180307060e030d0306050f041509020a030c02151003060509 67
    0x51940642038007000010300111400c001d40c4185004034003110ba0b0500d01c107400b80d09640e21011004028401079040001c500801e000308218142d95104924000520800703a843ca81c400000d161404901c82e00d1005012242c0c0300c140901240030070581d003240c10b0901d01800900f100d40e42c000158080c103404000b103056921890103ca200c42d8100040b2758503400c14250080c140200c642c9181205843c00040070000d80300403c0030300c850b410040c94148098614025909130305100700b0481e0340601019103c50001c81100301406440c1c8072500a0303d61400b46102c8142840405080c15110b42c5400e41102000c0c0e07000114103d01c2443c2e49400c9860b03040581c2510040c540040510350b0600c20700d03900142582d0b000c00400d2016100f0303030070b03140007005900040d41500c01c40d02a0543c0318010359046d0f520343c1829801a40d20300c040840720405d16a039000101c04036800f020810740042d481d4900544c51341d4040050742e415003000003001605140440307500390390f80201d0000500141c0c548000c01c10f2000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 252820341 1250 252819091 252819103
    0x9210a020109021008090d0e0603040212010b090f010609080703080f030402030a21030e0105091507030f110904060807080c04020d0204030b070c05010f020702031e0f03030903040303080109050103051c02 89
    0x150113045940342c085088005001e4003005c80d59528175110f4012070040d00c91140800c0d91100300301070906405c607120b81d070800401408800762480d00b59038540c4040110390700da0407103900813404886005465414100c00070075004068105001503071000f0300030000195000100c0e287d020807040401d88a482d28400213040c0303800800090680e00144240070090402a80c0300303001d40701151800c00c44411705458090a03500101e50b00c090607081010207440111a1a81042d0721043d64500011980300844210b021150780030110307000c24001158418150505120b251f007c0c2c070b02e041c0245580d84c98a00c410303070380d804a039008070f0050350017190f0384007801890340543d00503650100700b030b0302c640c6001040117207100c0b03000c0c45c2a00c06600b49624400a04520720881d22820303006030103081024038168901034081e24140040781c42d8480c0c00c0a61000a5007407014500aa000340301641e52140745050040070a10181c0000039154a840300410014000040b0302803c1d01d203880288000c0c980c0c600d4160b040c21 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 252821591 1250 252820341 252820343
    0x20c0405150604080610050a080a030c1403071406060f0d1b09020a050a1e1202070c05100206040308090111032a0a090603060b0405090415060308070b0402030609210a020109 76
    0x440040303070100d444c03040444d14510410410311300c61610f541e61810004052428030030070310141c005220b032101180c451003a0030b441d00e0040b46100c205408622880386183e00200c400ea07100b03a5054030307802c9641c10900c145600618201c88229410301303440c2c00600e091082900040050b00e000031044182c1c01d80300c0c0040010824200d04644035208a10060003c0c1c0c0150410b6000580c0420034140b1030100101200c0034032020760300c40800c202d8408002000398030000042c0c42050100c0b00000700d42c3d40d01a10003400c80030f140e001d05403a05007880d020f82110307406440f0318516410420100381c3d502034841925448103c5845101d654040360204511480f125810074424880004200c4522508030b602c80e811039025a608220b05070b80c40c1003d070301d18001e0340690384d03000342424081004124405001c510301c121521000417101d540b80d0304c2c05166804400100c8501d1413131802c000c03c1d07141c00d00031a640702c01417102230000e1b04070020f012006000ba220301550210408100c0344a118406d5102107822 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 252822841 1250 252821591 252821599
    0x51f060509011b080313051f0501150908030a0e0d0b010f030311030901170c09040507200f0a1b080313030c14010804141f0608061807050f04140420010f020c040515 72
    0x4800c234083d2050181509001d151503200d020501c00100b03900c5038a60700d007180c00500c00396040445845040f03424680c6104850740c41000c00c601480071900c44031149000305090b1222202d15441d6142c05421a07010000003c010780080c806084240d030041c042000600207002e55a486a45050091006003d80000b454105c1e180404214800c0e421440e01c45c281c0c0e081001c0744042c00031010b80142d07a104040605001c94020f00482000101c9549a0080f22200c100003584a10749980c141865070301b000903a42c1c03141888501c100180a1110300b280c1c090525210036007440c8186c40006403070641c4c0030300000d184121408946282c80400e003c14200d03541203c1c0756180003503c5441ca28050500750060301e416004040104010b9a00c203003600010038802001340210030316010410640003210290396801030303100c0086d0349034101c15024040c4214810700c4105281c05151b000400c041400021060522030f1020302c0506080d000559040d48040031640400d0a80da46160171100c07201400c40c107600 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 252824091 1250 252822841 252822883
    0x30f030b04020409051003140712080c01020403150f0b09040503160521190206040201210b060d0207050d090b09060f043c0612051f060509011b08031305 67
    0x1401b95032003003901124020320047d511515072400990b01c0f048148246101e41032500407020000314240040c0100301500d000040c10aa60794940786001461040c5a401c1c240d550003880008402502c034404079400142c8448990b80b409550b807a69912840c0c5e00700c40c50000d040302190401a042200651408001c42802009419081d510356280c012003035a62000305141d2581820b1440007601a02c02c1d07805030745286002c6181400415020081200e90808603118240c41e500d5480d4000103020301442c40a006039520303034504080d814800f0251502040040c940380411075030f030301542501c1e005101115499030700c1400120842d00e52203264860302e0007030701e0301d541d0f003100084000c4e841552501e2a172000400c410f0100304460850698041c007000b0501000511180b07500c01d5100d40c0d8085580350483c064807400003205c900d0001150321840008000103078204043d41c0c0140221091300301c035000d0500f4010b040e95100103c5c00010240e64100744206400c4040c8013040000d0016606c8250000b03038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 252825341 1250 252824091 252824101
    0x70c0c05040f0e0d03091104090302070303050703020309031f05090c01090603110c06010906030c080111161b0b04170303041502130317070b130201020607081f0b090418030f030b0402040905 83
    0x2000e010b6003841511f80365003140c2c50008034280350246040c40c2d0b81c10b41c0581b20792825642e05480d6500301040a408501c807d00410344952801c10a200720a021402072040101c1040e15940a49100400c2c90b4095000351040c01d041d0791b00141c200c002d584c05170038045160090b41e62454058050303c0e81c4070550784101c000006084015500c49000e60b80251a0061400d0311341c03101d00e099940110501c0021f000410620700c20700c2030340d80103424041c420035011071001c15807003030000400c0580c0c000030350800001508102c8008501c05030320440000c0d81c040c50a5141c81d40303c0803800d0900c0910161200d800045207120011003041e080047e42e81300c50004001c85254406100c0d0343c002003022241c2c0c480741c1000c40d82d181e00071180d040c04d03154168014515607503154001c0f9485140500b8003400954908440d460aa410065650103031040304030643e154103403441000706807007103815420400c0601d9040b60002ca540b064800203c0c0020f07080220b02810341c0c1e80420020320480d8801507085107400c0c1408 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 252826591 1250 252825341 252825347
    0x3030903070e0c0705060117010e12032202130c03060501230a030b100c03021b0d06090201140d050f01050108060a0e06031e1b010306081e01020903160e070c0c05040f0e0d 75
    0x4230303404140e000200f107a00c03640c03013809582d80d02101404503050301c24000070b00e20130245802040800c2e80c00742c840118400700d50100c0e0a00056000b00c0f0300720b584419003010b420b0342c03510821005001c00d207403540351106409000c5001d2145030305052001d480010b004581300d40203402c88084824003602c8204e81c0c0c0000d400060125202c1c040c120014003c60340068031416481c2c05005d541d403002444160030104559842d001400d604004034180014002c1030400b041c5c5007000340441944902c0e01085914010081d1401d00c20142c00c543d05204240041c4840d54503130190311010780350b0004622420343c8491000901c0c01c11901c1d011a111400b854154131440000b045d406001c0c0c18092032024015030500c01901070f10303911302820025500450400c00e24584040e01e8800660406000625003410303000442c0c14403a07680d2006903040a102c0d01048000030958a4640c40324180c905851810700564941101941e03a204561207191140c00443d030301000e6038490040030f10000708680c002d000845002e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 252827841 1250 252826591 252826619
    0xc140a0c0b0a08070f050405040b1503070306172107050111040303270302060d020d0209060d0b010f0305060d0b190608010b0f01020a0803061c0b2403030903070e0c07050601 76
    0x1400040c003c82c02041005005240b40c80f0780076080c0d164642420b04020611000704141100c06501c900491580645a9003000003540240480e03940400c005003840c02440801c4002c0c0d80b1071000d94020400001100d071414100304c010405e8070520b958807446c1b401d0550260074010040b1480c81c01c0060001b08054200031030052050740064840d110070351203009540c2501c564880690800000c00400c00e000748598020b00000c074110500504000d200d80200707200b6007000180b40111503651440c2d04403503800007022041c0c01c520740303018010b0b8608240402ca80b800f02c003100501245440c004960071040d84040c0041d6010034000030022166100c0c1950f02910354000054080c060480c240030513540f01080e100a10358000e02050301c7e545690b0141701210480d036507807035034203c800c0040a001070b060b40d0342e850040084e0080c0c80c20480119813810004c1d4809507099200e07610400042c0300740d4401080b1f0404841c1900300700e880070340d680200c84005206880d0020480d015040c0040b4150001e0510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 252829091 1250 252827841 252827857
    0x703260106080f0906040c0302100203040b070c1409040305040902090406090f0615020d02070315020c10020d051311010c0204020c010e061008030a050d09050a021e010806040501060c140a0c0b 84
    0x84050a40b03480000d9170b10ba00d420345024202c10414030303060002d820410868282c0c1185841244e1500703645014403103484e00141011a0309015124041000e5046c03011a010500c00803110340c00142410b50300506144940e01c1009900c03034004c00d07900040e1742c0300c0d44854000c03c00034005000781c2280c0003000e401807000d4061031040401400c82c03440e00350310000340142c00c1002a0000e05045065441d0400e004941c030411100e420303002c00202c3c2401c003043c09695801b0400500250311132a890140f041561300040500c03440e861000002d60200c3c0d099072036410341c10400c0c207003002c0c00407160000c03501034403524400000c07a6007400040400030100290142c81031142c650381c0d2903040d4444410350703182d01c5102c0c01c00c800584107101d481c08480455000c09007641c4240c007100c0c2d21007401e078041041d05008206000441403c20041e4120396040814294082400c40e801c00130740d8100748000e001d640e03112401501010b50b00660700c03801c042c2000386008950f084903070300450b02e43d0782c480d01c0b19540c00800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 252830341 1250 252829091 252829111
    0x30b0c0c070e010815040516030c0602070902090f01030c09031e0201080a02030f041b090c050a0f210b0406050409500312010b0c070605030903070326010608 69
    0x10700040c16440005882e8140c507034a0000d4440720106900b1042c081c54003400642d12401841c0d501d41300c000074542420001e40c03080619420040c90080082d0400380c941c2d00c4444a030b1f0040002074103669420852003614038003428009489045500f0446d1584c0340e507080107100c2d10801910a1683c5407102c268021070b4401d0b6105011a5178102000f0140d000980b85c641000f10600003050010310342d09007910001101484481c0c400342d0703628100d02501c010812910114030b00246401c5040d0380b022419034800c0250500e1400414040b00001026030008819401d45680d486400199501d6800c03600c0101002030003400b05424074144459060b556040594400d540d0240240503803c4941c03500d031380700000d0303200f00c02c000881100011140c1e100b0102d12645000c10820b1264682c66844424064140e20000030703280c101c1c281c1c0403460281300d9001441408030030700c2000f40b001800800c40c1d80a50f49854110902c40103510914080c03a041d0f40d86241300c078603c000201d03071168880341841c403960a41d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 252831591 1250 252830341 252830353
    0xb010309020a0308072103020310120b0c0a090f0905010e0f0103200d121d0414060f0109030b070e150a0203070311071d06040507170109090c030b0c0c 66
    0x55044501188000b50080004042000404c0c0c0d0305001d051071a02500c1001d1900319050481e80c48101201d070b4000200703501000340300c06915142c0980020344206210503030024800d80b01c008010750000c11071140800c00080040507544110f014000030480d01e0080f0307a0b62038079204040c003e003400b4000d1120714640231001860703102101e14014100c9401424103002114000380d00011400900749164010641d1070041e00000e101802d0b1000c001c02c00d940e4241c0160240160086048400803080d00c200d0034108400800c1c0c404120320364201d001160306d0407001c009040140c07210195940060b016000e540c04012029811a0319074a03132550440303206140703800c00300d011004c901401c1100c030010703441802648000390040c3e8941003103440ba07001310303107549603a00070940c4c441c1309202c07569000f0384401040c0300c075074209801400c0c0c0002141c1802d0b031804030410100d1043c11014840c0e20074443d00c0b4070f0200c00b0b1144c0d01c3d081102071034001c0c0d00c4950380c1c94800030355070451703000c28540f40c0e96210356 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 252832841 1250 252831591 252831611
    0x5100b061e03041b030f0203010c1d0d0212010501030813050301020708040e0a06090507020a060b0306130209041401050c07110f0918030c0106090c09060201060b090918010e030d 78
    0x48045420000c031400740ca07685035524549425240d00700402c01c99400c4032001c480f038101601c5808020055104421208800503244103250a40e40707100b1440c824440300080362013007007140344a0120302590903140710105007601e0000031710100401c2412040c03940ba0100220600040f440200417051400460b000025628002d041c00c07440380b84d10103400640284007c0c001034040c1d100c816004104640d02080c0703107440302642c1040f1401941c410015a02c4010300d0000c000c02da00906400000c2200902003a180144000400b4803a51030001d100d0600c1200140411603401c0301d0040f4416480700030804d1346403901d000790040d40003060035903040300b0521340a8810703e06a0466400c411000e048000540c48001e00791600040168000300280018400001181c0c0309209090003010750000102c0c0104140c0d0001d042d00c46250064401c590608c00144501050001190200c0d4400e0325600c001d903440340144000c0d0f80c0f05100c041e081d9420040040122540040034010107611074404015084c21 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 252834091 1250 252832841 252832849
    0x20702100e0307090c0309021201051006050304080f0a0c0b0f04031403190c030204030501020c07090e060106080402060702041b090f080f061b0403082b0204050609121905100b 77
    0x104151695042d0f1011070103000c102c0442c1c00c610141c000c141008511480690b0000d403c101082ca0501d0b1180c0d903a904000014044415200083c60107060862640c04c044d103560965215107101520810b5000541700c036413a21940a565595412001c211440d0030401d04400c0e600f81c0503101580000c1d055004c10020a2031f2208032800344541e00c000000079589500298080d00501010390240b5034244400004600280004c06000504401805280b4105002d100465880004155080d48014014801e894001810640050301100d1b040c0d19020741d4400500600090300001d00824540b0381c0b03c000721a0000320800950700c01c0000142030380d40740c1c4409942c40b51034410204403039100102080c1d4545500c800c41c00c0d109800c20905203801e8903034907422041d500a402c7e03241c151103102104d132011007103008031821020030714409518183c40d040c0041c034a03020305440d142c400c01c0c22010201410000704a006400c00a01e05480e42d89181418915285c0204114000a6501b005c034540315a10b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 252835341 1250 252834091 252834107
    0x30b010617060f01020705030f07080d0903050a0b0415090506090609031602090604090b0f0103110d02010906080a06030b090a05060f01031e081201150314010b040b09010e04020d02070210 82
    0x403030040c080780340b903031003400b08015102d00610050540c000c9a40100c0c0a440511561445640d42e00041c002545804d0b0403a180004a18441040010450013400081d1001c03600481c425003103d20b006560b151818038540c083c05c4400841440c3d894000260100700c00452803901c40c07003a440c140c920135a910306480d9142d200700d440350580001d1059552005280c21888290014805000081d52071031075510300d071905105071807214015807190700400401100c00316954a8120a442031140c4010f10741c0060300220720f50140000b808280400900e4210712603111000031600046815035604001900300d803a4210b40d01e06680e035000740e8002600029180090074122648960708400048a06911129040b40c0345001c50314204104980c1d4005e07140d03030302114082c1c21f540080c4030110005080140441e12981b04180c4d07042c18100c0101300d606050010349007100ca03520510340e9544500c2004031000d03400c40b101164028408142d900d8903003000d601603d80144240e40c1d0000700410b0b403400340e035150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 252836591 1250 252835341 252835367
    0x180e131704050414010320030705040903020109060617120a020607140c0d080a0e01020f070201080709082b030c020d03020903010e060a0b0306010e010e040f0609051522020a0905071b0804030b0106 86
    0x89c0c0030000411a40c105584808416402440001000321480d51000155540c540c0101c40000101c004e00c031040710b0a10103094003030300016a0502d0102d01100c060748aa000030600e100b4000d50440c6040707100031840407203905201c80c0701910100c1e20050800b409904003504c03403006842c40c110580c1d141480510880303c2010500e100c40d030400c1d0381580112200c0000401d503004008500340d00080015081001a40080102e03038080801c40c401e6610030b4034007842030070b140e0406007000c000b0780e503068001c81d903100a81c00c5403070b000d660354603140c020a0160440003412500c510418040145030940c80d403210380c0c0c0c5c5400f181070700d0326a6600c01500c0f18442003801481c0240302c0120200340061a800d00c00071407507126040c0800c910a481e201d050134900243d1030404640640000c0208500554455801000c442d000c84412512a0303000725103813810a01400d581982ea660204140c81e00414401d0500d044070600c64000300c5032031411050b650400d10046030822070081c0040f0304039000d610341034040c1c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 252837841 1250 252836591 252836593
    0x131506080a11190903080304120201140601171b0d02040801140103020102060106050c212107022104050306090d09050306240f10180e13170405041401032003 69
    0x11414580180d101000700743c10920a00483c6900080007444a0016611407030040b11000600210848080d00392032111a1f009100301071103042204e161f8100c039940010741c0300c1040310400c1382d0f104410894030b0415940222580b4002007482d4515601c41c1e0000c006440c4018028000c80500380e41c64101281e0a000081c05a0020401404098442d10152010b4010b490480c1c0060303107048811030346899002070710f8408103000107200b100040301c042c0221500440610444003803030203e01c02522035515a4032100302e4209417071401b00e5070f001c4038107680c0580b0b4010192040d40c180500259520320351050003001003503410030000341900d00421404e100308070041c80803109031240407800e1660401c13142c0c40e541c06501001001d00d036485541a44440e080141c80f117243c161144082c503104030700c2c0742e4450b42c0400c00b80010040e01258100c100c0340a103912000d144400c0105070400342085c09290800e42c0c120b440c0000d14203a803038024440740e040b00c1c020414552096a00000d10f8081d20520080c00d0f01 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 252839091 1250 252837841 252837847
    0x1090c12111b010209040207082a0705010513050901060903120e030304090e030d0c030b0f0f0f0108060d0b040302010c080601020a03091e09110304021f09030f02131506080a11 77
    0x603408400b404654944280c0018035080419002034100e030031051041e500c64002182d01132001e080d241942032650300b900c0084400c3c10400c1996541c6548a0280e54100a400300c2c0b83c1d54024100503404018001c0101040d54a607145c0800528010302c920042e0340007144041d0300e0340b00a00138450142152805000303140f83c0341c1803503010400781902410044240c4010462202000201d00c240130700c08241ea80c0100314240740300100324a204109009034070600d000908203240d540c42000d0540740c030400f03003030100003684e4040c0000c0e02d15810f60809003106805d40d040104050307042d485494505048d48036480b00e500c5010049a03651412503000700400c0c0b40034414484416543c14004e10b8254401030f082e14103840f4620700e001c3d1030b6080d04d8801c084002000f800110b181050403440060801b07001c403d62070034071203401070241d805884041c010614042040041d500c0b6030700d180c141030f43c0c1d1000030300002140a009030308100d498411600050b0f100b50100d0141201c40c00b910100c0c03d074084071303541 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 252840341 1250 252839091 252839107
    0x816020706081305010c020a15021305150921061b0715020f04090b090c0703120c020c0d1a0c090a061107120c061701050904060c0e03030301090c1211 66
    0x2428100075014140c3d44400e140d4040c0011002d014404000c01c00368041d0001c000d0b50700d00f215842c0100ea004280003401440002c01c0d034080d02001c902225000c95201c920b070f1030880c081111038442d4410254202820382e048128013105251303030386200d212034411505140d5800b40d080e80e020022401807114810104510404942c4007804c1c0030610305184401807801003800c203061119405580070500c45601c07003450440740c0c90721150055000700540040c40c580174981c3c1d40107040d5030103100c5c4450507540c1d43c06062202ca100b0440c84507041005003041c0014621402d00340707180c010110403c4100103503071000031600c05000c019222503c0000d410300003410f081000a035002c600071281e003035142c40369200016070a940001154140d500032810242d8445c1404c8004020b400b000034000082d178804d000401050b02d4006185038800c8e00411300007026040148212640583c05c1100c90b030510000c0700120710000107a0064120046540381c2e404010034280c2a28213580001051076126442403141c0d403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 252841591 1250 252840341 252840347
    0x7031b0b030c0a030e010e210a1e03060906060503040b06030a0b0a091103070e090f01020901050901030218120c03150c070b0601090305011e050c2d13080d0816020706 73
    0x482c03107001d82808590903400d240c0c0c01b42100d0b1041012600e5601901c80c042c0d45615410a5840c0d042d202c2c100790b03152072540d00f005040000e20711583d160b40c440500001340680d01c01c1d8468809444c01000504c0010b598820090047e0025207064442c0800180810558035000400110456001c4042c07001c3d541c80c0c1c11040014000410156084014041c1e0f082a555040c02600060001c9180d01d080a08090b611903107000354000034005c081e8030402c10082c480ea003040603140b04410910b4007603912022402c41d103031440e01c0d0081c0349421100f001c0c0c2050700d170351020802c005410000c1d000c0720604110a0600c01005905841d0b004403100b08000401c040784101595a50040701814020f604559958400742141c80d50ba4001105190024003800b40c4001409681e4000007607000c0c032400d16078603981c008410303418200040c1c14040e101940717803581c0440b4829685c880c45801c0040e20055603889540c1d4681242a0020001035110800186100034841c007081000600e0f41c000c20425007805070035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 252842841 1250 252841591 252841597
    0x1207050f060702030a050105040b101a0a1e0c1e08040311030304030f0303020c010c0507020117151e0301060b16032109060902130c021f180507031b0b030c 68
    0x3958020380104049405070f02c040005003405d921030000040c0c0c1e0b2405040075400104040d200c48003203000d00100300b084421a200c801c10350750080d001030b540c4500c5608195030021081c0c1c00d5440480006001c01845904099111542c43c0a5664855000c1500d8a031101c07102d0000b17802005010240014400b003800c01882e1074100d10046c080700d1a0940360b45540c0e03403203544c0d1142203001a400241900a01000303004100100c110750410038144100c541c00a00010301450303440001180c408001010700707007656402c600156016002440240b4680e09040315400906003160180d800c2070b40000e00300c4001012940c809411a0703240b559960703603980840340c50881140c0380c498885600c0000d10400307160b00c0b44c1003495125010005042a0a106110328552085003018207031b844c1444c00e0ba03500b80c010443c805e080d1107003560a241000c8924924008104170303004030003500c8400c01d1440400000042070016640504041c01014034521000c5040f00681e00a038940c100003072010400848a000117 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 252844091 1250 252842841 252842869
    0x101a040510050618030f011419140f0406200d0b06032205010b0603161e02030415140403050d08011205030708181003060510080423071d06040b120705 66
    0xd640020411480380c1f425a141521400308a4008506105819200248280c00124201014420040350541c82014031900400070400258100c001800b046a01c0c0d00502040000c523408100b030003413140e80c545031500000d06440c0581d1506182203000d01d0400c0c1a280300b145132040509414004480010800e200494221015920b4407410021582c0b8038015520071240c540014016003c1351100400748619104c20062504202c2c10390004168040b08807015194056484c114010400e02c08030b40200011103404031407600400c01108018010a5903809002140d0340c890150340c0740c0343c0040142d207800800408a0b40300704041e0000030401c1c1c0191011194926003803400a590002007600c41b00d40c0103108001941c0c85e00144441c0c580b000a1481d600f400b03150104942c0352903503500301102603c40c058a044408103118015540d410410000a0b2841599040c03007030070b03060100480d441040c4c40a41c461802c0500040443c14949603c24008071004c0003004c50910705018880c92100c1240303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 252845341 1250 252844091 252844093
    0xf090c0207090f0f0f09170c19080c0f0708060115030f09030c20130203181005070219030f0c14070803070c0f0608070302030702101a04051005061803 66
    0x25000454080c0c0384a84041030b0f503400d5000c610b108002c0454001c9555402c04032829030700d01003d00d130115690704070040d00302c10280401030342c0c0c448480d40b40e4504000440038219021581102e80200701d0a08050b081c0c50f80494121105855651050754941a1a014003032095000200402250041d4640055500c5a508000403a2a841421102580d12280066010030420481c060411120300c4119646410259020180c4d600705c000064203d1302c2c0001000c001600407022401e115a415140343c99080418100c869402c040c000a00140208460101c054010b50003100d0410860200724582d0380d52646d6429901d8003500821740e11811262403d4136080c40d0178480d010141c404101013000ba10b4410000d603210302c6240b4140d0b000300802d030850310b44030745454000c01407507403c42c0300703140c10844604015840740e03941c8408070b14100d00c2459110036182010780c3c038036904100b0b42180c0d10b2040d095406101503518017038800541c001c60b00c101c40e0404010002c080d41ca01c403031b240303204080314014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 252846591 1250 252845341 252845353
    0xf1b040605060a02010504030f0801080703030c080d0504050d020601050d030c030c050a050f011d01060602062d040303050403120903080705070501110a020616020c0108060405060402070f08090f09010f090c02 91
    0x8281e40c3c3e04008440c00140c0c1d501c50600c0103068202d20742e082d03d1112460000440c1d0304214419889207414400203081c080342ca0180303420442e0407415110283d110032801c200501d41402c3c1030340c0d82c200090124025000d600300214403428080c540021082c1c141d229400307180b13400e03a0300300c800c00b0300c0342c1c016a0240100d20703400300043c1d818004030780c00240c124000300b42c14805e0080c544102000320030840d91030380b4014040001076004101142d01070040028540c0404203152900b1602c200c8140c800141d00700c00013003001b01601984440d0040740070742d481c40640c0740380550754400c0329802200500825403070b400283c5824410f00080002910940020400b0122041d0700f04140e004001110003580091081008800120354a06001c05251000301100c103034400020300880b0b0040c011034050780c0c0b00d0000071750588a5404030341c7c0d141c0d0b2280705030695003050b04050165422105019100781c1038250364108500d00100c0550580e0b4130400e0001482d8035003002203005040e050402800e5000b80c3c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 252847841 1250 252846591 252846599
    0xb060711040b1f111615020307050709090c060c0c0302102d140f0306040506010504150f0323151c1b061106070e010306050604060905040e0f1b0406 65
    0x3000c140d0f840030002000524024012440203440c400906078132207401c1d401644200004070f50380c400c1208440603118001c041032401003040341140706818014040344103d0400043c0b103a5554040703504603000e000e00c8041c2c035403902d500711f03590001d81002800c0078080500030f0000d031500c50a042e402c0012428100c2c0342c022460b41030f10680404540e03e90f15542243c0140c200243c03c03140320b140744d80e0101c00c0c46182c00e0780191010060700010700618015556240081c03e0b0340d014904075405065001c038103480600c1d1003a0001d14074500108450006800c00c0c6078400c1a00028140c00c00000d0304900070011982c400301400040140d092a490b8031104603000c51a0b07135016900201907581c00340400180c42c0126441101c401d40d843c2d0700240030026080c61440500002048254000200e480c00221169000e00103e010380040c0d00a0340d071000e00001c000a00b944c01c04042c0d01180c8060310140903049411140c0c0b43c032003c080745c52500f0b81d001244204c2c01d04800403018049414010800220a40c0f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 252849091 1250 252847841 252847849
    0x220221030d11070b010504050907060e060904050103050606040f231017150f100521071707140108010e0a0603060609051e04080a0f03060909030c150b060711040b 71
    0xc80007251081c1c500014103c0501180142c0036024241c169014071460038642c41140d600d12144c8244002c00062451a2900781c0c2c400b02143c48400c002002480a540c51341040e9031500d0382980c0282c840d80c54a201030407030300307400e00940301c107041c450740c036560b810045407001c40f45070764014007042d000240c006000c101c6140129800c0d82d05106140100f440d0300e00c80c0918030700b010026003006c0c1c40d10040c6003007200c64a118040e01090321403d0f100c000e020b0010004607076080c41104041c1d90030740992030003c10700303294561154010b4030010086a00c01c035076176001ca0610403a81211f007070024003420014030010086000c3c1d42d8000300810000240c2c01c3e40d07600e4004c21180907402205010f80c4410611031003100d8840380ca003038100c0791003400b1418201681e440e24070780305040303544040c0480c013901d41c1c0c0114021f0b8480c0008061411061000380194680100402803a41003255a1507244440c06c03071100c4140b1584030342c0c200291185103000800e40710084c160a00e0303c021640943c0b940d500407a1911 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 252850341 1250 252849091 252849101
    0xa0308160909020406260105060f0c01140106020d1403091507020f03071217070e010f0c0c0807050a0e190207020a15080609060105070201021207050114040308220221030d 75
    0x12590388039078501045146d0111390400c1030401c6d82225040c500180915500d4030111a030904a4603403507680d40e0307500c01e5410b0140800410324200803401700e0000620640214411407151580d0b07940d8001c1c288110004c8c0340c80d010a86019801d0391019103a81d00c004d484130101d541098a1b0300403141d0708842c06132514030b0742d0b226003c116014410071440a03a140e40014003910b9202900c0806070062900003c000d008141c3c0c0c601d540c2c104200c0484100301140100f0040c0885900710040141e0715407140700b12a03603940c1900c900e07405510030420000321070b218018518010221103403042e40c07000480c0712182c069080b00000ba40d110340810070000d030580c400140e50600e03102d5034681501c0d600d4a00108141101c0091069050080c104001310050703a01161040c4548004010662a80410700305540145003030b5103425582c001c0b07501880203050700401014490500b20030200c09204510388803c9104000410081d04138800c0d0f02800004103010020100d88841001100d050507e00c0008005403a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 252851591 1250 252850341 252850349
    0x60f0301051e06130510110303060108041112060103020f0402090a0b13090f09050705040509030a120209040e0a0b060d0816030e09010902090a0b09060712020307120e040e0a03081609090204 83
    0xf40c128500700401e0a104003d074410035887d0a00c055000c0c038880c2155203910004240d60304010903880068100103600403101c5c0140e102900981e40d1005840384e8030b5581c4070a0000303a01c5104114158291440c2034021245410360140c0301c981400d1821042c2d040f244c2001c0c1c0400b4425040810104940c2c2103841404503500d11810007003840c0c0d603507003071507070078009550000c034016414a8100240320500000b160b494440c5807500710036003401940707104000d01481114507403280c100b44032803503880c0000502210090042032901e40d241c81d030404028490302e6485000700080c0c418480e85114a2409400c1140c0e5800f034101029199a00c00010b40c07517032004d802c000d0820754082940441810040d40d030f080602500c40c0c2e802d01c2e1459200008805004541004220201848400702e10620920a0301d007016070010185a0600e100c85002c1c007202d80705c500243c041c41c50082a0440f0b92800135184480307d803d52510003160300c510480d0100030010008080510507405000602c0881d1840140024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 252852841 1250 252851591 252851617
    0x415051c15290d0302061b040314070509130f1103010b03060414160f09240306050f07021b0105031005090c0c1c05040b0310030206070c080c060f0301051e06 69
    0x2004a00640d0382c20029481c2550003205201c42482c0005e40000f02990043c014141e080c0c0e00300c2c0d511140e000c0380d1045804c0142040d0b444100c0154004000030000180e030411258070303a09035900e6030440c5540300c6400c00034290381040318407400403070407060403144083c0028001040101103c00800d20340703038058a080b01c10780011202143c66a42c180501c007003d160195040c404107180003403222003e00300740100004255600c002c0f0290200c541b08a1889015058000484956a040100007008202d4800003440311403030024030b8952001c10840c0040701c1801440d449800000011181c0c0e4000801d0140080061080400d0035541d10103424032640034504050790b51400390840c01d0815092401000070104c8101100600d03d4004003a1416140d02040c2daa80b2965a650403100084090b84040d400140c0068140e041c0403081014070152213060044801040c010302c24440a4810b07410004610403060006000519040c48011620802d01854a81f844c044200203843e030741c0419140446 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 252854091 1250 252852841 252852881
    0xc05061602011a0d0b0a0912080910020a05070b090313080a020418050601031515030312110a090e0907030219140d0c0306020306031c030603020415051c15 68
    0x10340c0d0900504003252000808462103083c4440401c46540040c030000313040304006400a240c0c0d108030760140a0454009510007000070130104050800101655400070310b024803500b00040d5405ca00840c3c010380b036155200e80c901615521141140070020b42840c003180000c0020306803200d000204600039290640140510101610401c0121100c440e8141440184410140c001c20000f094113411079422072204403800c100d55120000400c0282140d9041488504022080c560710806c20f0191211180c003c10801181c9803c40c07049003c0c0101038000902050ba0511512103644401030b0001040400ca40c5699204d43c00507241003198200804501c400800801400b0072054110b15258030035100100110501e40390858103802900020b0180e540001c01308425403402c1042c1c1c1e0901148400304811090010001806400680720582c8602c0c2010241e5000e1038886042c0e8007212002401d1644142c100c03401c2800c0118545d0007941c10948070030505220a01900034580c905900c1414001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 252855341 1250 252854091 252854131
    0x1106180303031f090b0a05060a020c0910030605071409010c02040f0204120b010b031501052a07090f021921090b01150c1a0c0403080c15061008160c0506 67
    0x2180701076400b0910b139074181542803910381c948004100c281d4a040e54007a6580e180c2050030381c60200300c060b4183d0024106001c00c01c0c425181440305082e0703407007550140800e807102030741241c61100000000c3d41c0c02d1420002241c0d0740d030151686540701032029201042801001d03124000703d80055000301c0d101b1007400320b50001c1060a500044c050640f500c0101c1c1982040728007406507071705252000e4140030000401000f0f070080c1701d8004002c004140340455101d141480b031280c54003000d00c1210780362407c0c1100303032030740380e8141c000d5136483c244d488508100b008441030110781c141e81c0c2d1030f0807091102c85814100c00d00c10780c6010362445e050007220000e250f940740c81e034600038a44040d51848104041d4030101400210080500c0748070581c003140c03070402502c4038024100b052050742c0c00100100400100b560134200c020403c540c058030200e000403031075075580b000e0012754410305081e880020a4200002c1c1c01000b41c1e0f000801076491850b001745020200c0e80c50b189000340a48015002c00206000d0003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 252856591 1250 252855341 252855391
    0xd0c080c040c0503070c021c150c0e0d02010806090c12041109071407062c1507140409020f09150d1a100c060b09040b1b0304110618030303 61
    0xd0003180305140c002c3c91403401840051540102ea84001d20030f41c0e0708809041c600b008d030b1804400e00782c3c200340c16800002c01b030b884800080a86048440c0410120902c242c0c1c40c3c50982441000c00d601a150903d00765074000400c806242e0080c14181184414850a40c4e05650780310348a10561043e1200200f1401c01d10400109a00061410007044105803040d180c3c0d0318284141c40d119a030080d00407807001700c2d01072415a60500041c00310140390008080300701c0a000080c286000100d900b040c4100c5072140c00044036030204964082e13125039010801080750b002d1030303802805240d030102c992034185102e840000fa03459091001c100e8034402c012880d07404004051044110b031600405842400301003044c0414448149460f540050255004014060190030340050740c079032000a040340350501e000c1c909040e50440039902e0451084000d820901030a90711350449019540049103032000714062020088103900124000c8a00f0310440041846600c04001541c05900d00c80340007181c0d00c01c14840c2d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 252857841 1250 252856591 252856601
    0x9110a090b0a091e03200a05040513080309120a030c0206060405010302100c0503040506030f09060702190f140a050309011d13090201050f0d020a030f020c060f060d0c080c04 76
    0x451408000700005080950010410701c12500c0d503213900b4440c00c0c080402546060f50950025003001404050024024400302c2d0042e14454110f440006017619403043c0310440d44101c0d1078140f640c106240303060200381100059507018202008880d00c220850800044540000c201a00884c0d114148040c0044c1c05202081d844030065030100829072542c2c000031802c220f80540082800483c01c410000d00c42d00303208460291034080c05959072400d041d40f01206007041200d01080340c0c010007001c604140d1021a5199408056110900790300c00c00d0785910100003440d04044403074044195555195580600010040314054400b95441e294502c00242000303c10307881c1a1070043c0c0c40d282d0110a561140e11000201c0f03504400041d051005100684052003a058a1031031801c02044c0c0d01c440350a150000d003802c0446e036500348003c8420a001c0ca050740101070740c4003181e1b04107d002584460500c140c0e0b41d8071810081050205140548075005040342e15040000542c00405111083c1c2c1028010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 252859091 1250 252857841 252857849
    0x221071508060f0108040b0a020f070804090605030a2109080609150702030c0a140a1b05010f03270201021c03060e010e04080d05040602040b0d090c080c0a06030b0a09110a09 76
    0xf41c48040c1d03400c0020320f8880700400c000c04110319800440c01c41c80d850307816614111181d64002d030b0b440c2510305001a040c4c005102e02e00c2682c7c2400e8001c2401d00703021030703084400c9502c0340a92a51401029240c4c400c4000380c0075010400c8000301000070071070030400c2014010310022001e03140c1c100f10900c0100740c008001b0403200c2594820448820001000940713a0301c015005088400c2820f00f08011a041161031000a40850040c264400b2414800303051281111001d0705c556800c003441e0f20055080c0c0d8480e000280c500c000c04140e00580012580100003118030502c1911417403141807826040184200b6020000290746141c14003540c19848070141c0500a0701058514519203680e0b4000284a01c134034207000c15072074801180c1000f1154050f074014007000464aa03c40400802500081c04080d80503510610a80d40010f40340402081100d051140a400781501c503003402c005070080d11120507183d401248004001030341003098844c00c640c034010003481d90759a00503044018100041508 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 252860341 1250 252859091 252859099
    0x3010b0102031c020c070f06020f0d0804030e0f0d02090915010801330b0301141e0306011412100204031b050a1206090c080c0a0801050402060304022107150806 70
    0x89450802c4018480f42803203010001d002580d60003c102003603003460310300d6011078808107100d10085038541d008a800800c01d51380c0c500321000d40f002410210f5180e58242c5001c1c000c111414044841400d043c9040090139074040e00e6150303100340a030301007400240c048494100340d801c071102c4c1e501e840640074100d50040000100a00056007414601c44c3c50f60420001c80c0045180e03150902c031031030040101034004100c680741454481da0740718500e2032006004500d061080a40d2201c0d0740c004405040c40e2030081c9006802410b03641e0811150300356006007005402d1b4001c11a0540d18000b010801c80003c00d0038400b98051307292455450600c417106459582c6d15420211188144a6501c45440c504d040383c42070a400c45e1043c5481c1001001445201405031400400220104448800180c40400c050041d164000c109039940085c50032540c09480003540100300300045005032034000300c01024098401c9c014005100000c1d003803480c2210b5a4050580c49001460140c12180c1010f081580000155 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 252861591 1250 252860341 252860347
    0x5100309080912070b0d06050907050c07060305220c030614040b070e010c0b0a0501050a0f030309051509090f01050a1d0604090620041a0f0403080a0507080d0b03010b010203 76
    0x1544200c181d0007426486806000240108489200104013107002000e0201c80700360b03100300019814020705100d000d91402003402201160030603100b0000c40c1c120490003005003603041e090031811006088003400b00704620001e00035854011156408540c4050310400d0900c1b042c3d8038510700003068402002a030442c100c104010040411300c0d0380e003520b80c03084140c58640700e603090110059440100a000c05081105046e080140d050140d6104074185c40303007291491049581c503280d00700d11040d075000050004d840c0c2d0030308110500700544d0500d0f00000f0b501009080c000c8080100f10380c132200302d41c0e00007450311300b600410060920140400c05041001010410041c0e8511008542c000260020f40200d80d00c007026004c2c840c1c280d00c01004801260401d049482c4140c650394110303006030064031072804428004081c201003800440702544800c86565092519586aa5040c0c0c0c000441c11000c4c0042046101c0c0007814100003002244420714000400303403024002d00d401c40f00041c0c10700f419503200f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 252862841 1250 252861591 252861593
    0xc1f091205070c030b0f1b03150910030b072307020108060d030c05030a05280c03050307050c030301090c0f030c020c06090d02090c031918140f060403020705100309 72
    0x44080c0044110440c20480e81e512032034540341103019096403016000440320301c02c0c4a1a10a002140ba018005141028000c480b441c0c41c8100350b0301c421758050342400d01000c00d07580f250130708070013aa41c8441e00d218848411652a00e40f104800c00c115001000200c042005410324020400d011204945c0f85003058100040c50b400a04140d070b000d041c40d0321880d061000842050f00c1900e25078081a400300c280da494400c0d80c6400f4007985c00005604c9003e5200362000d2042c0c0701d00320002031059100780d0b03c0105140325038400755000d0b4005400841004820060401160003c00055000f0400c3c440300046400e807a0b94010000b1208001c04020103040c034070340c80002540080c3d0000d0342030044454070b5642c140c1c9000030300d0002e10150001d41065000c0100100204a030001e144034a04000403400c0600c40800385d0307021100d45803a1500a60b0701c0b60540008600c2030501420016a20070895074054200480030b03207048411079045005a1000d0000c1c011410a0100c41d402c0000c1818140412606 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 252864091 1250 252862841 252862853
    0x3031b0a0c030818010606180902130b07052a010e1e04050606092206050a080616091d01030309270c05070219050a05011d010e03120c1f09 61
    0x141e0030016040000c082c000c540c6105040301c0540681104400070012140e640703a019200b40b0403103500038013a0045200c0099400454001c8450000103500321080f100d040c01c02424060300042019206403103540051500308041c41700d02400c00200b881e450700f4080050300014000e1090320a014003944404124a40c00e055147e06a40410320880e004980c1c1c0e80c998021889900540c4080c541c0a6030403441080c50f00d10940c4058a07a001c1120240803058031481408024841c1d80300b800c900342c0c05070f40000e8036200444c0800c40c0c011740624240114070303a5404051110401e540c548580d040100340104105904041503000400301c40a850504104424000c40d0b5100d1010210026645510109545503c100200c4212701e600410344401d4056100a011002640740103150080041000c08a01d0350b009207a4041d02d5103001041f8000750511200450300c1c030b245088419054421240c0d071880424072000034120580542000b41407044903104600f605481a406c04541e1a1801e056280484c81d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 252865341 1250 252864091 252864107
    0xd0b06010305190c05040e1f0b0a05040f03030302181207120c08070611010e0109020604061d060d090b10060c080c250501020c0a060e0d0206070209040503031b0a 71
    0x1024200041c1c0c60359002c40c1c410301900f030a10b00f0314a4502c0d080d411422160440094010f8980d01c0f82481507945d50380b1078130081c1c0c80ca02c1d604a54a4000303030700304000081700c10000b02141c10892610300e05041d99640c0109000000b40c0003280402e802088041c01c1c4001d85a07080074a0208031600e8008208125040751286020f00411188003500b001102c1840700440344140100102402c6034806940c80d440104020960701410460394200b6502c0c0c460800d05020b801952a0004c10951500d8a070a005441c4c80b00710201141d0204894190f88500740d0301d001c060702c40c00040703150210f000d6581e46032600c040140100102001840c9810602000e41d008001c12400c5601c00e403129581c1d500840854030303240f0a0000296a21045030842000361440c1090404450b0203808a440900b4041c04003c0160701d07600803032001401c06060012545459a103519416001030841840c0200a401040140d0801c680c15506540004207024204841d00c0180643c06584d4040b039050441420000b4181c0d9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 252866591 1250 252865341 252865351
    0x3041a0420010e060409050105131b050c0a0203010c030c0905090408030406110408010905030415083102030a0c05091806060415120515060f060d09050c0a080303150d0b 74
    0x568142480c05050340180185200520f000b813840744c455079607800200c083d1800b402050300840078030903010302916190051018016070b03840b18a40c1421010b074100d07508d800800c0f542025110b00e415a8025031030070b100b0440d071040c203550084cc081051000c00b03000b607030587e407005014841c580208000f00380308005594000741c1c4040040b55507500025040e01c507020b00c0d08400040d503e40840071041040000003002140d400030203404013980329140686400004403102030444803001c100307002c4100c101041032542ca91449654811807200d40220389840c40300102140ea540320450180014944201c04550201030440c07898042640a900c80d615030b04003500c4540583c0c1c944c1d12011900e40c200301410050451182050300540d0030381465581c601405010602c00500400801d1007070038a00c0c200b00341300341d001d403026251041c1c40f0141e038001c000002040ea0035000b061001d5a03150740d585141c1004010403c01140c485c00e28960042c40001100040d0b072007282c1954004000542a00803a41c0c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 252867841 1250 252866591 252866633
    0x3203040807120306030201080a1b0e1f020c120102030106020d03110415020a020906031c11150106050a0201050105012c03011b020f1509030403140705060f03041a04 72
    0x66111031411080d40e0162100040481d039800781940345050380341d130020045a000340d0f50340f00591503600200301240c1c0c501c00f00c0752000c0e140d4900c4800041c001c42000d004440003038503c80000c1c0c1c1a910241207680201c0310350005800c2840c92070034524001c03605403000d14608008524552500c44003a6607000d155000905150f280e0b14012404d00070034094030b00500003441c20359440c1d59074070780081d00c0703404502d0300301c0c41525001d020034150300700060728641580c2d00500d440d60124035039900b5103080707203250344100384c500c40c044500e080b02e00040c103124020481c64076142c2c0c8440d24140041d082d160b05800c22410043d41006446005a017810b0882059403062200c822400380c103004640940411140c61079012800300d041d0310100e5002135410000140b540950340e00a060005856a82e10141d4082c107180e84141310902c041350502504915080103035007110281952200410899000510f03440c90461001c010001030282810034071300000240132048002d4942680d940511010220402c810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 252869091 1250 252867841 252867847
    0x1120317010806011211030709051f06021e0715050415050309030306010302070305090312040503010e01140c160c080d080a0c090b030c040509010e09010b1e04050411040e010b0132 79
    0x144800e442d003040c1409005002e4401d500c0d02c95400c40c0c0901010303034180f0300343c2113000e070400212500d18bc01c80c4250750143c2d000d82400300f40c0c02e88451103000610030601c2640100d6500203640710b1984407844060a00b5101c550b00c40d0b2a140141d4503601074080d01070140982081044414000031040305c0c5d01030000d003130041c1c440780ca0381401c50b682c0c060b1820702901440350610301d4242c801100081d0040310000ca000740428022912074070300341d03140064110300065030100407030310041302900030b05640070141e0320340301c64000980c451080c420035a070b02000007038100072000031025500507030255114929013001c1c030010189450003401103c540c401d801c8100c0012000c1001e02102c1c0c0101e0300180340c0280704030582c1d40c54a02480d11203500743ca1109080d86405442111420001008000c1002c43e10015005103460300910001d4407008104403030180c0740f01500022a6161f01c650107020200000010350790b500742e400500030031032042025000340c0070038040003031035003d0a183c2007078441c0800c0c079261 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 252870341 1250 252869091 252869093
    0x231003050d0f11030a0909060f0303090905090a0203030301062705010f11010e0a031107050103060501121e050405060907060203040b0f0f0706061509051e01030203040317011203170108060112 84
    0x5042c00c0d032011501d643d01000176000d804580c4841c40741c0c1580c811050401440d99241030f40d4074849403074400140400c410140801100703805510155001e4208019601044202e50020f42158000d80040010402405d000c000c902606100406a0303c000c92600a12a00303003400030b0405100304040608211401c02c0000b140ba80c20740116960300d2010f41169841d007002d1601034880b40b03840b400c2414902c80c120002405610a020304412180d042e1500d107911a05000d80d080542410600c42000311242c000c00c95074507640b489824032440c01140582002e05040f06403a0030054168410000c65006100034000183ca110450f401c280110701102c3c0e581c2401400041c050107800d00141c29940b170705000041682c40f0160301030800350f4a580d10b140b442d451b201000002010142409640d4006608068440d4046c0e4025604a4000d040801130042800d4020441c02404d0700202030130070ad600400070425400556860104683d00100d01d40c9604040c45142d0f200030520982c10310907001280c10b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 252871591 1250 252870341 252870347
    0xf0609050f010c090306141510180f140307030206090d030201110a051308070b0a0e130609021804020304050303060d02060f0301030812070309020d0b1801231003050d0f 74
    0x100c50950500083c0b04022190501501108041c40141c03003142c285405400c8400c1180034084c07041c50383c01c1207002180700900c00d2260342c0e0071250004041c0030440b1004002c02010f2032151000b000201e021010f0203081001407070040406d002c0c124042d40c0800ea0230300050340c8903002d4031151142507400b5440c0d10f04908040780905001246c021a441c000117814400590000042c079505c2d4001c00a4a2400e64818060303030b4a0310b143c4514240e0b14020b026218219116400c0e490902c4e1004001b02e00603043c2c45183c4c000c8410590100d2011940007074510891900c2d40800740304080308a4045003140b82076180e4640301c0c480100031501c500b404200603070456494a060b41d1400000f00e41d025100e603100d107841075055000f5040140220030500024580a00c640510052264050714200038030041742e850b003440c40c3c3e02800c0162052114090110085c20034464803001203076106440444000c5048846180c402c0580540c0b84501004001d1010aa0000c0c0c40825080d0340c3ca0180c89160940b4021 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 252872841 1250 252871591 252871603
    0x201020c1306180c200a1506051309030f05070206030a0c050403051b0f0f240d1a0901050103060510080601140d0902010824010302030c0c07030f0b0c04030f060905 72
    0x1e1010b10850007901d11016001d501c1003d40c11001d071620703c18003840100b08012100c0170a01122264050902d0704009815150901c114500c5c03914082682600c4100042c0344514201c1400040e980c1e5600f0682030560090816201002d5800c0c0359160108580118010748402000d54181e00d841d0f0308003102291180084400450300842500c4a000d03080c00c0c0c070301c5a4090038040c2441500201e8103412103192204a005070644000d1120a14801300052450f0300c0464000200c11100144100324104000e4058100410303299044000584804070801681d0107040e0841c82c10940390110500160300c81c0000603854200e03505003c200c958602c40102c0b001c811015201c2007981d404512262500301d9030300907041440c400d8030780e041a0340d2404032a41d090204181010901030511001c051254000c1d4011038010b4440000329291280d001d088a1400202d607004a40e031f606010035102c240705903010280c3d0000b0304207130040d103000d245840d09660ba0803000c00c007601e1190303200d0344001000010026 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 252874091 1250 252872841 252872849
    0xa030503040308030103050d03050705090904020406030b070504260307150204030c0f0602061305071403100603110a0801090c03060c0e10050a020111034b1b070201020c1306 76
    0x1169a00c0d6181d151605044d0428841254544103500c075042600b80203012700d034815449641e5403401c08000504201c0c0910002c2e0041c0e03000780d0b0742d04001c8003040309000c12500c5040390344c50f0b069480340b03409070031003062800c980011040000d030904035814400210464071080d801c003468041110041032010024800c503400207160180030707940000c1d0b00106855144c2151895000d50711565162201c461003403028103401040c43e04094428000300c0c24060102c24862009004c5580c0c9400c40b290724412190203400944184152580034030142c903110703031840c0150112400034030030030b48191307220f621003065404000c004030f81f9021511fa4061003034070f1804078208010031020451407040c40250640c5e20803000303680103500340300f0500caa00424100701e9001d04c40519460405034503401030800c484004404061104072035901c0404c40d040d0000c107504c810825040c0040540c10032941b40084c01054100048480350180017810151780c0108a054001600f65646068001c02407003007070003032031503803c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 252875341 1250 252874091 252874093
    0x702120312070906030e030313120201061703030901060503210d0b0415090f02070b010e0c13030303050105090703051e071b05011e02251104050f041b12060b0a0305 72
    0x10070004070b26440007084007220384503101044548680e030042901d07880101c814608140005522600007050503420403956080e42c030001030095115154203c0707603801100e016909038804424020000c2c820f120f004010801180100b10120f03851036802c0c250031204404024038440400c644140b4401e6406c01480d4030001042084564040e4200d40c440002901030315100e54139000400d910a00c85208540c442c07038100303c107995141c0c41d20032142243c0c10014054400300c5000d00c1480404040004c111011b1340c801c0e1004206581000c0500100d0400180f111080504160901241800d03c00c0c2c2c0c0e60b2864070340300311101036503615802691740c10a11540c854810442c01c07100b5050007010342c44801194507a8001409804c0c802804405902804140300d6030000012005900c0180d07803c03200d517540f07101d81508008011300703000040807108116103417082c6258940400003004000195100240c540d0841010160708251800a4000f2002002010203035289414000c580e55100d40000465000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 252876591 1250 252875341 252875377
    0x30f06050d17211303080106030e030f091305040f1103011e0e2e060b09060307080a0e06040b01051206040507061b06060602070f06031404150b09040b070e03060c07021203 75
    0x9000c4c001c1e180034031401075000454540001c500c10f8802d00409528540031002582440b18140d2800099400b00d04120351103410b10030740500d04400d13406004d100b14096043e0f402c002c840c500780010f02c006c3e030444640c40f030f9140416580d119826402c4028407030303d00c17200001d5aa400402003d103002040c1c4000c484021180501124081c0c4010030740300100c18113070080c0400c81d80c032507207103140303014544000d036208105000165001d44116001c1e684907801d03250104407001042501410910f0a0380c0c1500c0070706a5600520003030030943c0320802c69404e0b6800520151800c6e44605488104601800f003c10a0b0380381c0c012640c8948450200f00707140c0203041081000e6880034040d40c0d509162003891000075164900140c203070300030301c10b100c20801100341507070032580c4c0d0340c0d1842900d0100301c0d036050845540340b102030000c1d11510503042c03060b4454003010b200307401c18003030103810321039621400c0c1e104e0742c0b0100401900c105040140c41d000366040d240030f00825a091941800c40c06103d40304901c2c02520 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 252877697 1106 252876591 252876601
    0xf0b0415110307060c0f0801060e0307030231061e0608070309060204030602070b060406210f0201020c09070806130506030a110f03030a030f06050d1721 67
    0x700040c0c80c5441c0c4165a0002200c801021000001d2040701c2004105604980300c0381c00340c031250400381034880082002030f640e81c1d4603000c0240290301c0030507000816034441c11b203002030880c12075001160f041840340400080246104800c1e0f40c007072041a240203000f030f44a034041a904c07180d4400301c20740d0710414250041c0400c2c10084501660030440040440c6051020b400c46a00c500e12440040c08c1c0f141c100801c0d0b4101b0b801c6800191030b5801a0b43c03d8000142c440510203601c00c3c05c03400340210790300043c1e0800382401003068202d0490403c000f201c1d0b03400749400344160401c90325401e906486c6950304048030360803100540c043c0d125000240200b02c450207a288032084c0200a038062500c0740740403d003950040c18030b400c003092300c40c944810401203e0140202510064500182d008201d45030f680c01d82511a03031031140510002903402d100c041c1d0354049032117041c4000d01a070141c104 = true := by decide +kernel

theorem cover : BRFrame.Cov 252697841 252877697 := by
  have h0 := BRFrame.cov_init 252697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 252697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 252697841 ≤ n) (h2 : n < 252877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
