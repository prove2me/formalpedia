-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1684
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:12:42.243806+00:00
-- url     : https://prove2.me/submissions/9c583485-687a-4d6b-bb67-c49d0e384eab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 302697841 ≤ n < 302877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 302699091 1250 302697841 302697847
    0x10e120106080c0d0203150604020912030c07051c11010c0b01030323390a0507090c0203070b040209060112020a050c1507210b0901090911030a0302210f 67
    0x18440158811025100410116440b14542d0800c00c5085014007400070362580c4210002a02d6007024110781340c1048016002500b4104000c00003000c200c2402801c01c507aa00114141800540401c00d8100610307081d80ca003c003040a0040d4000032010103803002c0c0c00301c0300c7e547c0d01c04002e0348280100035515800c01a10915540c41c0d1400400c0d00010044202c0100194052401303a41c0318401250f040c2034004040c44140c0690054094040d90440100404102100110f81c0203410501003088000d1181029080c1c0505144800007142c1026a40c030301154000c3c00000005600d1008450300950122148620340e9076180040360561135030120240e426001050000741250440003404460101030140c42014031104c0e001500740300c00300c400300009407082c0c41c4611a0201c552041c1007041c050040030030868500808178000002c2a400042215a600c0c40e040a000c3c2401d1242c0d81c0000031800f4096040d480d8400940c1c40d00000000c4a6003042d031045640810519401c46a1091814a031940c07 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 302700341 1250 302699091 302699119
    0x108040803070203161a1b0324060a051e030103020a03021210090308060a05040212010e070c050109050304050109080f150c040302030f06180706080a0b0a050418110f060f09010e 78
    0x4020716254044041d150811310106044001c4000c47e002900104141f440c2140d551000300d0b40411803800c14000102e101c034000d130790303d526001c00134604901c240d02c07655074440e0b4070242510420119000c50004050a04c0140300507504c1200e072404603601102c56440c00c1c0360074a07003142080c110118240e032152400b2000f904043d0404180380c400c20044800b00c0e201c0d0394420a2005902c5250704210080e5a5500140107410819000c031b90003550a18012190003031030342c1d4950848020f0360040d074840e031010070100724645e4001800f4000c5c000c0e174006045a101c2207040207030788111083c2c000481555050000c0c8106950030305982c000e540050440d445003003400200c9445480a40300b814200c0c0416141c1c8141c25000604042112400c0e80d84130400c2c0d0351441020020051404102c1d0b01c04204a0002141d1384c40d13000c0c9503002412911104040400c03490400480980b002c085400382d1100b05501c411642c1d4801507400da441001c40d92a90b8104140040ba080341d90040d00c03642c4140d140400003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 302701591 1250 302700341 302700353
    0x230d110d050a05150d0618020330070807030c1b0b030411040219052a0c13050106020a02120a0b0c07060510050607150e0d03151202010804080307020316 67
    0x750064140074003c01c01d58460304052800c00c034141c0b61940c0c0003118540b001000900c15032041000b048098103490f420768490340000d0070040050800c1e0698441040040200103420100c13013107035030910810500c0c180c03450391566040d0081c49000350501000d030710343c6c0c07050201982400c0103e00c180d072104000162100b03c0d02003e0b0700103850954018400301048005400c15100316031074041c0110600c541c00c1840413044560307510000c000040d03082c41c00c100f05001d8a4020b411284801e190020300703401001c00050180401001a003040079a0402004000680d000b0501a007015016521030740441c1c0075a00c403a18018212400421002010041000040811b8003610003648604002c2c0203d803940c40c82d112003e5043d0040550002040003070710000b4034403049030460803481c05008901d14800c102064140058003c3e06000311f0703100c0012200c0c11188113544c101030031000e0745039070306401c0c55000288100001000248806800400700d8103080c000c0040c0c078409010140c40c0001a0f21500d00300c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 302702841 1250 302701591 302701601
    0x24030f01031b0303080c2b20030c070f170a031407020714010311040e0a0501030b0a0b1509010e0a08030d060801060e0a180f061a0306070f0807030902060f0408060106230d110d 77
    0x8c140c103215001d103843c00342c0000904590040b455044203504140007a2a00850036000e41e000700d840c1d102524030102d02105c400017a21105c011a20002010b41080460206d00f4100410000854100d84000d1054001d40c103080e1000c503000f807034009035602401c4801000d6215a410000e088002d000030400300c41565080340b4141c0f44958134420385921341da0940c100f81c842100c000c41e848524000b0303200182d222100601601c10052600c1c101407049080401e0b504400e9404c401c03c01d0304000303410030079131141c2e0145500402c0b03144020001c0510304041d48800035006130100400e071361910319140340701c0c45641c03007408000d804c44200022100f0780c0c64444011300c103205010401440410040300140b038040f038010f20a50054803403020680d104042150744a00007000b100a05070358507590b4000d41c4680d000f502d40d00040314030080e82d0b1400c01d2a45881c2001c145e0000c420008042c80c030b114000d4800664141e000f40385174010351120040080318ac09840c0d60412a00700381c0d404110707528856420307042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 302704091 1250 302702841 302702861
    0xe090f010608011a0a120f0201030b04050f090c0d170706110301060320040503030a0e030708030c0105040c0515040e040305090d1110030501060e24030f01031b0303080c2b 75
    0x1c1542070b5104113003440180c650522030081d840d18201581c4c4c011958403502c200e01c0354414940042c03507000040004040360000c0c3c600a500d03000f0700f010481c0103141000894181542143e91900d50303405540d6040b8180000c0100b4404d80c000881c5640412240d07803c882c230102c2d074030a01991a503840701801001001c2201c010484640072908215404001c001200c0642e000130300658580f00c0744010666203101d000c044107406215804000500d40d005201070441c60401c0320000c2164141400c4c01e8616218681140d0f105140c0580c1d900c0d110185203044038219a042c5410105070f03a100d0406841501544002c01d0b0040940070401041010174141e84100e48412103800c01c00206411048044440900509022038000e41c50b034005031030610303064103043e5069826600b04501021214485800c29120483d4010b02040140200b0110070403080c41a603007a1804001c507446d517280144540d030094000c5030380c00b40005101701c00c9841090a144c1910500d68440c0e03540c09a50398240041070301c806 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 302705341 1250 302704091 302704121
    0x201051b0c07050f1f080709120c050d11040f02070212031908090a06050f0906240415090c0e030709022104030c02100206150306040c090b180408040302040c050a090e090f01060801 79
    0x440801c04010841e80c44c4c4025401103102d0038414242001d1180d0782d10b8942080c2da188075003700095a0b5a6680103d41843d4074560b005a01d5078424170512062491081180c07043d90001c0c084050000307240c5002000f004070174034085c0c07555162844c646041844104000d0155070078981004400c080442200340074207004000c031565559040703c0480400e01c0030012252184020128090a1030181c000c0b8102c4101018520900c0c2e541e0101c010481d0859410100800c2c40055851650f180c02d00000c4018911394806600c0c14840c0e4040807840c00c03100d03c0d511003540e80d6102190905209480407625141c0c05011320074444d840e1a000703980c49030300f01c03804010f8071070b10301d00e41089040224a07140510350050f0880b600c00e04002e50100901850b01d060341d000b4180d0313102c09400c0c0a8209420b0302640c05100d1055640e419070042c0025280e000d0301a6040c00b03820852201e403154071205d01c400710b4038640c6100c1403e0310790300026414400520b450034895804c001c40840d2607081980070003048881c0e00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 302706591 1250 302705341 302705357
    0xe030403030f030c140a0203131404061d04020415050603090f061602030304020907031b03020a03113105040c0e04061509030b06010c080a0201051b0c07050f1f0807 72
    0x440c281c1e04485a02c04c00200d0700d071940501d12060001606034410a801542c0c2000c2c546950b01c2013151071684480310134803520466400e2403c152240b13070060681441c0744080700c0d00388405880700700c002906c024040d5645001c0749500407910b581c864040c00e4024425036407800c041480a80c1c0300c550380d0782e15040d4011030010500d19180b01c0c0186070010b40b503402460840e65030b6000c00400400003018502459112450b1001c0740c0760045100045842540f001612501c1daa80000c040b1402100c000700b29000402a01c0900d8014848000403142c0c100313900c821f42c19035800a000d11103040d520dc0780e0460304202824100c00d41081c04806255403c3c2e50030000c003544c42d40d8034041c441c001e516101c00703d0355030442840410010b4654550050040c10001c06080c111380d00c4915a030301c06841c12005075500e209010b040c40c960104000c60482c40341e422030030b102070f800c0c6440d16540c0c548a0b10740304041c4803195140c19142c1d44424040700c080140174550040b0350700805001507400301e8072040028442 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 302707841 1250 302706591 302706617
    0x303050a1119060b0604030c12050624040c0e03010501140312191b05060c030a0510050604150306050402070f0b0109050c0315120706121d2e0e03040303 67
    0x2060444a05006405040c1e50020f46485008083e800c0b030741600310204010100200f0b010405240091900c2c410790340300c02c1294108a03051003000784c206110014111101000500750040407460644102d600080b441100841900c2c0081030748511a0194203103030000490074a20042d06004000c240d06aa40a901070181c50441c3e03c0342c15140d1300300703d0049901c0e2010340d204001daa0b40e0306101c5042072441041540359546000400c0310201a02c110000070098184600d0140e5034101c9444c6501d81003080c1088005080ca01450184c02c021010408140050603c283c001d907001b4000a4011551042e0340d0070703e802c0510803510152165826540005110b5001e88151303803142420440b4070f400c0da00c4e03280c00703000c12812810b00150300001c0b1a01011210505000c98801050903458045a80040b034103100150313503400701c0f04040e0260034031180b81c820802140c83c07000c40721101841e040010a02d11019802c03010103010156a500e0201e2110b041070b0008010000c2e24081c2c0c0300c0310242a01d0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 302709091 1250 302707841 302707843
    0x201020c03040b0c0a1a060a1e05130609060305030712051303060f0f0e0c0a080c09150d0c030303020304021504082e090c180c0212071703010303050a11 67
    0xc0ca440d054041c0e000304010400d041225019220300c14204042d10341c1400583c851458030340c60018403c1c50300d29641d090000614011104000074409101821403141c0580b01e04124907207144191809590704400e44001151664400006016100000c00c082c54403420003580d02e4000c1c880c100c601c1000a40e005039120b00460036502e24608400c0d20ba450281036687e5031010340160b003002e0007020b84444100d07a581d8424080c14444100714002080443c804808120841d0201d6006448030340020500d0042c9449131a41150b008605031104105080c0b02c0d4007140318440303010030107403e06290040101c2050390680042d80900d0086a19465000e13064411070014481d070310420f1841e0740007241015075250b0101c047d00201030070f50070000d04c02038192004011388207c2e5134100c44501000c00b00b440b26031808a5074000c1c2d014182401c01c820309080001075a200390b0f448281085502c0801c1400422040b0f004a510210401c1d007400d0b22560350b0315015140c1c1c2c00c00000b030000300707400d68040882d58030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 302710341 1250 302709091 302709097
    0xa0b1e0301420504020a080a050601030501050303070f17070804090f050c0a110c06030a02130909020303040509090a02100f0e03010905030d020f0903010203091507080610111615020d020102 83
    0x102c0e07551240d07071052614241c03101d0380311249551010078185800003a482d9a644003030584851240c0b26000140750060000d021120010b10641c141840c0500500280c2c80010580ba00207600000003240040503003000c1620410100c0410910400081c54100b00700e0398101500445032008024046002030031903003400e60380d04a815492449040c46841c1c03030b2502c02c1d1270445075084c01d401991107212154001c10b140794001c0318403a031041d40010f4002c82e0342c850584040020001e41d14100b002402641c00692030b403056209581c411140c01b804244100d80900c0703c0c034461070b401400b500c407401c01c07502c02030b00750305045080c0000306a004901301e0f1681018007a4903002644036024501d00320f6424100d1009400081a5180c4098244980320880d01e09100460040f00d454000b40314403c0c50103000782c1c0d01c00000740f10200300301e0400180007040d01c603100380756041d001a04280000c1940701d152146000782404e86c2940301c0c01c808900080d8100920501240c5152950903504200e420b51004c3e42070784 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 302711591 1250 302710341 302710391
    0x50406060519020d080f0c270f06090a0902090628080f070c060203070309060e01090b010501050c062205010c0e010207080102070816030c050a030f09120503120a0b1e0301 75
    0x71400000200d80b0350030241d00c254401c1c0038075411070400034442c4041d505501141ca46c0d2400400c034484075060751511700e227880d900c0d82044850700e02e01000030300803450f8403166200360000e83e0703004500d01c03440e035403a1004d94828074000012508c515001403854003003d00e0420b21180800c01c2c20b408100c1664075145540c2c03103a032481e22542c42c4000c2c2590307520000c0d03000030031081c2010f60390004030700041c905e8040e0450f10b01d00740c0d001042505141c00c04014041c3d060340a28103201e001c00880f00458000b04419a014010400f010b61140c150410003e07071300350040c0001d00fa17528040840070010b13007004c200b03003020800b80d08071072807181c440180600701c0c424000c002e40007100500c840c00082c2c1e924004003007a14801d25040324220460ba4a1518000141c076080f0085207040c40400c141d503900c8104400201488000218040020380f1020707240d11400703403005181c0100c100014000200c6030844081040003a0203400c100c00081c03040c07a242d071401005c1c1d611950034032540020300351071110810108 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 302712841 1250 302711591 302711597
    0x4081905120712060b073c060203090a020d080d0e030313060b030c0613060f23031b0412031202040303080606220906170a05030409090c050406060519020d 68
    0x680b80c0c1e80307040c1d40780d902c9403410250141d00c40d580824842880030141403c1d0303104003041030a0622607540f0b104a50744d100b45c00504c840240007010a000455450841c0c0682c210301c0041c1c1d240c403032202031810207070280f00c0039400091070300310f100400c03000d24000e0031044000b1008024403003010740303540d45a07c001c1d500b4a240b80504c1900a0214a141d8000350b00114020101d030148066103010035001e4204e0b02c440024604142001c204290300290302e2052400c05180090f0b46c01501242e10750701c5240586400c840c1800840000c107036010340000c038201802c88a00040d00d45646489200c4c0d0007140100c11000104210444200404d071802650700b0b0342d61548071903038156602d4003070007030907008110815416131400c00c003419080e44401e4030101a151915010542605040ca40701c0086804044050720f94003045078000415808400d030f4003030ba1494000410307a203442e4244140f241459803c0143d0140c504100080c50f00d030484001c018410841249421081300c0e940280d854403d00d52800001c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 302714091 1250 302712841 302712877
    0x90a060311040209040912050c0f0303070503072016050307121a071403010e01060e100e04020c070305030c0a110a08070e060402040305010e0604050f120706020d0b060304081905 78
    0x42c42c054002e08000c2601900018140381c8680722001115a03003101000414400100d04650380310911883d100216603400640c55401d04410041507071000902c2071081003196802c2552410408000041c90310b50401110099048401d0743e009a8805d845858400d00c10194005030001915801851880d00715050600080c0c07014120205050000d007090100040000d24414900e6100c0c0514040c4c1480051085598188a400f6140c1c07821031507071074441d000000401d803520f5807006024401e10029a030140e105c00704095010b10b028219040200030780000314525502d03880016840d84014001c2000a080e480d0120501c0303c7c1e103100780101c403203d41044405116844401d072119070070150140006150941c3d0b91540c6003150855400c00b0225040b20f0188030034013000300140c0d041020795a001d004100481c4035614200d101c2d08100910f0950085081c28410340d295019605162000e818665245800d1500c1e80342948848040341400d4801c080c001400c500c03540039192400851010310003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 302715341 1250 302714091 302714123
    0xa0606090506010f1d0604030f080903060703051306090c090603031d060c06010b0f160f02090f060a0e0402040e0f06010f0905100b0d1b170a0506100c141b090a0603 72
    0x1303640c1403030311704890f008481084000001303100300b0704018040b40221284c0d511a08950205424000c0c050303c540201800c001c1840340d21881000380558041e840080090786880074501b4040c1c2c0c00580c2d000407a10303480c0140000a16400600c4c018105605c2040e40c150485001d040000901490322501002d0b401000140580000c0c6030050203ca030840f003805041a040d500740d40401c0e20780c01e400300e8000000e44039040c11801c19101250308205101c04140080c5803003804680f044082c1c2c407403001107801e0360000c10250346441d400203006185500c25100c20714120511599290001e1003000100040b4440000386000310348201801181403034150141c9524108a0410581220b00c1c03040100d80d48800000d10f058908071444411040c40d00e903801d6040104204190700000144407181750390402041003560f644030400e00901c8030050601220a400714201840038041e00b018480051160344d00704404d210340070401d5244038004840086865680c2d004807016660103210091090b41a010112 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 302716591 1250 302715341 302715377
    0x10b030c0a090305030f0d0f2702010512040c0305191a092a0114031012080d0e03040302040501140102070302130e0a11030105010f1802070c05030a0606090506010f 72
    0x400229902e00e00362140c9910707619014110750211000030940766000a040c00ba003491070140c1d105008809400b0000c080881d000745032140180c0c41e141e01c002032080505811680a03c2c15510500c0301c0c03461550452134207203442010940203000555207845001105c241c2c890f030242401d5a1300e5849802000c0c04020100c0310741c010785010b09a41d141b80941c0d803024001201141c403460568920136007080c864182040050260003d0000d1007041d40010403c00ca00440400303800c0c401c55500c008006d02c404024200a1034900404804503143e600304452401c519000001900942e802140c01308803999032a00e080044000002070680941c00994003000540760403403400710401c401d220007191030150100f810b0f00340441c488084410500c400681081801c1c2449818003420111031440d15450030042807801003a01d9070600c00c0f2554002890b401041400c1c3c4a00c0700800028080f00c040328000d20f8040c000d4240c034090a42000c3c50800002ca26610451088090060750780f6240b0201031200127071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 302717841 1250 302716591 302716597
    0xa080405010c021809010b19060518010c05030a0e010f030219080403020f070b0d0b030321150406080a1a010f05040f06080d02030403261b01090501020c0c01020f06010b030c 76
    0x183c0e130211051403581c90380c2d080c0182c0a0702c9000503c1c00052048150410001003546004100c021040045010700000b9006000c4850a8110a000302150105030700103d45406d42e40304000c020740000f05810130202c1c0c00c00700405200b542601c41c054a6192260308804a004034003400340d6903007800c5200c24406024519441c0c22a0191066a00018001602c1490903016038050000e0450024580f00940d011b441400c1020700200c0181d481c1c2041d1001c801003580009440c0d0f13070489115000308094041c5101071200100340030348103000084e0b07034410b219240e8802c220250341d80c00c66186250450150705409a050f02c8800c0480c402d0142001c080c44001c000420131404c4040c0c1d00c840100ba8030000300442805034070b06500642e80c440c1036140c03403002c9259205182007600408a814000601e805003500c1c803d484400030004507182c1d00340080c1c0581b280c240060301c2c40d4800544903901400104840240302c80c02c2e001c03144100d68084000d40c0c0c4400c03d2040c140507103000d0010400500d100c1c001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 302719091 1250 302717841 302717843
    0x414190b1009050a0806040309051c050d030207020f0d02092404050112020a091a040c021f05010f0e06030d1803080f280c06020d0f060803040609080a080405010c 71
    0x20005041030194041181541c400070350a01040da5464108500e1502009410103469918080c100c141407698001e040103105004441c42244402c65200d80d500c080d03403c09d0503158104045843c40e0a00c0c080c050000d41c82928142e000d0446656041e545041203500c14509030b45c040c0070300d416036031144940d80c41e460f05546800c001d13985001600c1d02c103580e9070003a540a0b1051401e508590794413481000003202c6180d110041c018240516200903605504102c071480c0f43c159404100300c0a004c80803801d200c0a1040e02074501c4401c1001c0410708119802241600c0540c1406000c041e01e42004081d051821220f5560640c03207500f15001d850300c2041ca4481c05800704504500032516540e6004450b0805102a0314120303002c00e070141c82040d0078082c1c826a055250300121032100c0030200504c0765001e4200642041d8001606203101541030340690a400080b5904005064403101c9468030399000d4415940001d5404d600812456404110001c40a51000c0014a0130f490140103480782c600480c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 302720341 1250 302719091 302719141
    0x2030702090402130f09060e0d0c05060c03061f020705010917070920040e060310090b0406051f0b07051203010f090509030904091203060b0a0f14070c1508060414 71
    0x14140c070400003e802124111b1f4441e0602203000896100308030f2514000366500010403100d0b03045000410004101d407500318401e502c42070790f01d950307200c0454020706240512540c201128124215005e602103221019204240d03103151f002d5035030790460711340032410b142000705942241d142004147d88a6008400c4503002040303429441408003c81401c40c0c10541c041340f000c1d4038500400c03400d85014005080c0030b000340035081000d04d4070354a60a0b04480c2c024401883c6543e0782e800302e0042c00300c030f40118081050003588195050b41b00d01f0030102c1030700071a408072401e100f1100c80f01c03000c0b40341a0a4034183c2c0c00c1c40d660003068900e000e00d0300f405058054901d607400d02082140f0b44090f100c030f0040000f03450148281410a00b40d0302001401c55250390b1100f04400d005000a008c2c065000c900c0240140c1c04d468444145d00c11140004514854040c000f44600300c0a1000960104031202c1481c00c8071071a02e40243c141e0300c1d001400240d03044650219130400710140017445051003190800b505919080c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 302721591 1250 302720341 302720351
    0x10e0609012301031503124107140601060f0810050102120f0403080d0504120906050f180303070b010815090a12030f060e01050a05120703020d03140f0a0806010203070209040213 78
    0x3494035401c0d118440c86d40e40000c0d0700e800c448d65440c000110450500030445200c8c0d110301100b0008001c1140c400030700190403100004524040c0070420401e051158400380035100b5550b904c1001600140350602031801048000c0300141c0d0001802d510710701200c40c1a0050714500b144140000000e611100b808166141c0c11300c03010000c900300381d02030001d00790160350009281c04c0030300b0002c4440c40000115010080d040307006008266010041c2d5100800242c5140d4644d101c02c074110000c506065082a01448040f4903841800281c0d00c0381d50480e81d02c2010b031007078825024411100700f401121800742c3c560003c0c081600040081d0009440c1707010b5403600107200c03aa00b6076610f094800550181c9203951342d440c0144a0341c44c00e035410314010001254a4182aa04c210500d91100c0951102910803207014240105050040104400112000340c1e00340e50b892803000124800e8000700400400540000d0002d00c0b039500000c100c502d00ca4006001c02210798071a030800148062260038524015114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 302722841 1250 302721591 302721593
    0x5031b01020406090503031606181502090406150203090607030e03061515090a0e060312030a0204030c050111210f040b0304021c0c0b0906070209010e0609012301031503 74
    0x128641108216120000750382d81d0300d092002130042d1403d4121500c00d400400c6201c0c0a08046604020300c90b40c0040e01180e140007103505142d00e04008080501001c4070b4000450b00d80c0c005500078142000d04540400c03919440c0d04c1540c42c003540da4514000580e20400c200a0a46420f070090706065204e40782c20599003500c0000f003424042d00791030080710310025080404240c5840780300c1c0301d00c8640c0350758410308203100200015442403051149403800038541d00860107940f03040c0070740c01d030044550084942c0c80c1080000100250302510082d035180e90840c3c4080b9103503204245e4080040d220324001d00c25042e4241c880c200d6500e10704255010040200402254a20400d014200078000c20220a45920b41401801042c3d280301c503000492050803c44840000e0440c0d84440540d20fa00300a503807640780100c0441c84070302c0740b01c40180d4410105000014a01015100c941c403621003906d9080b1142d80c5c0d48464481e06094000406404241000d0394440c1e5200354081e100003004031072500ca2150307403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 302724091 1250 302722841 302722867
    0x60901140307090b2b051203090a030c020301020c031303050c0414150d05060106020a0b0a06150807020c09040c06020d14180a0312030b03121e071b06030b030c030f06070c0503 77
    0x540c3d0551300c0b04405001700014403c2c1800020000c4401d00d16041c07951038800c64042e225100c0b0b8500a0504c03004124500541d2000d5050b80c0c81118000304407550740345901c020100306502403100b140c0d18440c0e18400c0c801c80c145401489008007000c0d603481c080b502d84d256001c160300110510182c0006902e039400002c54010044c82e0700030038071074016040070f0000b8200f10340490300060110030607508020381040101041a0003244a21003441c1487e65910b590408a0400c10100c1c00d0702c1d844414681031200340961203c201c0d0890700750313030200c400c045820300082c7c03450300504180b00e6402074244120120354944103040741080034018207140c0c546860713548040240b40f64014841c000390b51016940d000c0e040c100a01c66824131410300d45801c12a00040c808081546502080101000818090200a80d45142490409031000c4003540325440b841d006000342030283c00d00e0722030711590854145070305001c66411500b0784004080c140c0703642c450700709a44880e40310900316024403081040b5545450 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 302725341 1250 302724091 302724139
    0xa06082503060221190b01110c0114120a06060314070801171f091703040f11011103120703060b131a1908010501020709050127020904060905060901140307090b 70
    0x20030136400d43c0385c07500030340004812104468541418422000458400c00e43c00080c0081c25003002d00e0250781030680303131620000d10b00643d00c1c03182140120800348800a0880e8003c03405603201a40d0410109104000c9002e15100a4400c00c1c00715a5190040c0201c8240303e08160b99180c145040352060b500b0200301c441c42c0940f42403540c0300603a8409000c1c007000b10401800b0000f0046140c100c0c11810b25440701a04d03401e038617400800c00d1462091214681e4020980201030140100035642c940b2503002e011400c1c00400c84074070000a1400c200451030100d080145c8040c420345441c61b098050800780d4440c40000141901030b02c81c0424401902e008000704014811641a59180c1c0b4955140c8400603241c0b85032a000303503603041d080c03c1c01842082e18a01552011303090340c94044180c4501641c12100900c58425010742160a095001c030b003560b055007001d40500015983e4800d40d03a41c540c04140d421b481411802d0345074000e0a0100080843d64014020460f801400c0d1a0084c0400400f904c4c544 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 302726591 1250 302725341 302725351
    0x5090f03190305070c060215070c110a03050a0507080304180f091e03021005160e0d02101706030a240b0402040f0306150614130e0a06082503060221 65
    0xa42e00007044c0d01048840f0003440d00a1030a400106a01012580d800c41c24180c02003040c010000710b44101414421003141c480380d10030016000039000758582c280035440d01d0841c00b094130a8410b4003030011711204004210707012142c060002c1481c0744640031001010f020030314140d20742c01d0703180c45111010800c1200307102c0c000703500d500c0300d610300d1120392501034103003212007054420061a090410102805030002040000e06a00e0401120300411000032680101450044c2d04450b10f49210070450f50401c5010305000c2c0501105540c598450040540e035040858000b41404c0b08084003e1610940d050a00348508001c200421036000c00408507040f600145e1103004084a00c44042050001e207200d0760350a200403495011049052a5003c0e20403d00c10440904204002580601c000f1012440101801c0d61320104001c5d030070906072400c042c02d40350040c4002e5010714002c02c004107884d00c41006c54801e24829000780940303192250350007504540385008103401000d00912600111070342080c851 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 302727841 1250 302726591 302726597
    0x32d021c200a120203070305030a0929220c0e06010c0501091109012309090109060f0e0d0519050703030b060a02061b0a051b03130b120a06050105090f031903 69
    0x3150706061140c503c400c084101c000f550030810007000404d6115045944c031100c003600220742543e0b1460548403010704409e81c80080b0424075010700600422150300350048040c42c00050882d04544041c0324422034000c0b000b80081c480f203200f0058030b845115400c0d4490014140110000f8890711a10b003941d41901c01120342580300103805030395241142e0010701524010500750700d90441000d144c00311803076040f9120b01ca00f00e00e80c0081c03c031b40d009422840a0076488642070007000341c00c1481030058814400b0000c2903020b1a01a480c1d040d11440949258400010800c80c140083e9403068030700c1c5e40505001c3d4101511811900c0c516140c00f0002c0c1103000d607941c0245070b9450010f6048026a18905000c1e5411a0402c1a00d88580e40705007503402c0b400c0800c00e406c140c0d50403c038001c2c0c950310072032030700541c8072a071003000196040c400b40191500d401d117030404481c541d03202c072800c07402c80b02140261804505e0038000a040c1d8246120750a201aa0240c01c8400072103c8130540d0910300a125411400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 302729091 1250 302727841 302727853
    0x8046f27050a0318150309390506030c07141908090a060f05040308090406050301091a060d02010804080a030f0f09110d02030d1107050d032d021c20 65
    0x425900030f84408040c00b03c407503904d4805040202c2014100c0f401102e0300308040c0c440d94414140b100c002480070898003442c400580410346010007000ca245610616603013421015000500d034141101141d00c41d28400841620b00505039541e083c1c0c0c8194400320468a20030707a000c0f40461031001ca41850b015014030b00f000e440c0c040318801c0004e60310058001c0010400280001070a4036044801d8409803503200070855210442540403800912541c5d106503819800c01d42c04005000d00008900203000400d54143e1b4583d5907402802544110307040b0080c0001c0d042d00004010175032040190002404030314000c50044c9640316904290345d2400801070a05d41c2c0e4003d01410401103011102e80d14000756030b0705120a0380d40d00000c0d11404c0f800403000c06e00440310308008080301c2c28031000d806001c5c0100310200c2c488207828010000f00c0035228544928071000403100c03080c001c0f2503d04281441e180d005040c26400c03500907080040e08032844405110b40d03850031000a000a0079011100f030340003001015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 302730341 1250 302729091 302729093
    0x423030a05190c12052b0b0109060809060606031302090924011d0c04090e01090b09010e0d110a060501141f08046f27050a 54
    0x480c0b003818008500034080c00448040018000c001c40b1410440c160034480e844640e00035030102803d03203078102c6c0d103038821807413501d0320300380c19a6807050b00500320a9075041031150321b40c18240ca400b08152143d15466000c00e0011710240b070240011a40b0416840a1604920740303540442e5001d030040c6c50480007500400444441c04141844180400081602c0941e20f945004600328010074043c604501c03084940c2d00081c0c0d18a09102268000c000d08d01040103810046400d85009046044080340c0507036003140418040c01050081102d1600c0250140000740151801514001000b4034060842d020304414500814101e120b064024560000d02070442da140c1c0c02080110101c080c100f900e5500e00d101904041648422429803056107c0c0002207200750b007220881c0318425403c811216603140c1c255980d804139280c45815a6101d190f0b11040c20f03140d50f40d11085600450300f040084034551144c0d40c48014540d80c11a020580ca13511441d05598070300c211503c160300505006031401e9000c06e0707400c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 302731591 1250 302730341 302730367
    0x1e08041d0906090109020f1002072c01060c02090721181b0f031103030409050a020912031c020d021204080a090602070e07080a0e161703120423030a05 66
    0xe60003807100c0c008002501d406d600050703080c10f001804074066074204002c03190b128000c00c040406000c0341002d0310f84001e9070142607110a0313803809442d0f62100313849000040460281c060700c13205070b03130042c0307104810791342e102e811100e4864116060312404410070500e2400b41082c45007020101c440600c0700070044640c140007603603280c0b003031280068a60481d01049803007d08440c8105036540200d803094186c44940000e841c0d4080ca03085005000d240c00c040c000700c1c0c4400c0d030040041d118142c4141440407071004603e912030244a5000a0750890101d04130b9520100d0fa00400c04444042c43c0103040c0407103460762025940041304c0c100e900f00070014001800580025052009141d0381c030040c90607504089a905842c180941482c1c18450030f0740201d03c4211080d04002c2e03c2d0520310048800c002c905200c4d1a030b020559210708030745905205402d5041403004003c40344e030421800405c04440e112690741d4500104402c42e03900c0c0008000d0384001445100744000c00c24a030155070343c1d540742c064a0310f141c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 302732841 1250 302731591 302731603
    0x806010f0e0d242703110321040b06040501030309120222060f0b19030c0302070203120d06060e030307080901140a080a0b09040203060c0a11030309100b010c1e08041d09 74
    0x100c3d00559400c04880d20800006180440c585d6040ca8982e4403d41c150304210301d10301800203001c00394209a8010401100300111003403240c0d00440000e17000791983c03000c1c030046031403c1c04041d00182400b2400d100218042c03044144603071014055a01c0000640020503010380206221215079880340810813002922650a001401e5004d00035460b002d4150050904484120048000d068881d00b510f41e11901a60680304815005000d55101103103000b4020503c1d800700c41c4c0e9a24840c0f85c9240824645d10030144518543c5d000b4009500d0b04940d83c43c0c0020a801003000c40d810802c0042e4170138072243740350014218141150b02c403000740342440000350003035801070240a400341c500300040102580c1c0000300d582d00011080340c481d544903140b8900301c40b03902214201d04068400041407105801c4006880e07031006448038402c100d404550001142d0100c03c0c9075000d024010483e2050150240c850811104d0a12454284e8903007562074401c80081c08502d800b03108054030607010048001414402 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 302734091 1250 302732841 302732861
    0x180f080c04062106050712020a0e13090c0323030a020106030507061b031d03070e090c0d0312111b1c020d140304050f01090507150806010f0e0d24 64
    0x400c66403640105800340703449414800113800c65807070700c0108090038000c046005000d00020000d650b0313540c80c40000341c43c4480248006014401e00300880075007400620964000903889034104c40e03490310b0340e1102c4032001556042c525070510240c01d07070002038200b00010130310030b1504c0d0001f140746841d60170310605280486d44903200303102100032600402c0c1c44a516a0500644c0740c1020356600310201c03540c0c9880b1100c20321941d058031071401d010070f4020031040c4043c03144501c1d504450010003020148540c5207080754006011998081c10a00c40c812160018605070444108142c102290421034015807105440080090740000281104000005070780c5840400d01c0d00051019801d0480010700c1003403100000c485000000c00802c0c1080303c03e1000f5a45d03501c05100030b000004031410132603250040c4c1d210308410582802240d070788041c0210540c500c580c2058444201281c2d144900ba00c03c4c3c06050b01060b8010381c40900b83c000100311070000f20520b192054480900101d41444204445403040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 302735341 1250 302734091 302734109
    0x50d0c030f030207140f0318030102071211030702151207030b01051e0d020a110d080106050315012d030b040b0f01110304270b0f0d03180f080c0406 65
    0x4604000329030401502500c05205250040e504d8080e803c000342456801203800100c0d00540c140101562000030140c0107910301a114031040c01e803114101403c038828001c008000f500205d0341400344c1400307190158a05104041520b14001d020750006005100d00051016900400300c1e140c003c1c15400e6074420790040c05400e00300900100000003031311a0040c8902d004240410401a0220300c8803641a601250301c02241551514281d400c00381030011400200b1038184143c100342207007d48651040d038122034103902e40340d103180c90702c2156070303640b00e40900c9180c103001401401c2405031443c1140400c0044c034040b2460442112420010160344080e00d60a200341e00b052100c040070740c1c40884440d0703041c1d4242000045620b0403490f0500f540100d5000b9202562680e03940c01d10103030303180001c401001c440a000c0203519405e8041092915451071119005038400302c03400000381c05216910345240030f544c25800000d5542d00032070442403039500040e4580e08a010340c9051400e1502580020f000554 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 302736591 1250 302735341 302735357
    0x12703031d010801050f0a03080d02040519230d05061807060f0207091d030c15010e0f0a0b0102120c01020912030c0a081c0207060e0615030318040b1903050d 69
    0xc1c0001c265000c10702138248a804580352a142c0c540e1850541c00003036501100e55611001100e061900075089440b03203a002c3c1040e241c01000c80c1305049c5032042aa1081900e08240e901c4800740050f6003000000711540101c1d503501c03010302013a420001e06120300e80c0080c0c13074041e11041c218454180301140e0b21201c203102c0f56a40c0f900d4920340104654081d0b860620300040d040318030b20301d100e6a0078680001030110303001c0002c000c20768501c0440d0244110441854124a6903030f50901c44d404034404480031200c1440d03501c08144918003d800c0391a28200501c11100b2550395001d03015099445442800b000341e600054031111410b000b250400c1300c00350100074500341161582100c0e01d0340d5a125006000700d40008030b41e00d1852089a122114139007010741107495070607500d40070004003124004c6140910400c80003801f042101c480a680101d805800785041c20007516107812041c034041c0d285507000742c4440c2c601200351900e07910035440059102c00052424030350304009040c80000341c07149003045164 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 302737841 1250 302736591 302736647
    0x70c09060812071a042f060d0c0e0316030b090d170406060e1602150121080f03090102070309140928110c010c03060f1401270303 57
    0x8105041c00c1002d01d2012a80c0d2031162402c03400000c3c03040041c003103041428040c030091249010b590502031945004c0e0103201b25a08108032401036420203030562100041011b0032941e110740d005100303c9202800c2c0504c00006440000f42020b07200a043c00c0318000100c40ac0061213858420640c0014191020707180320325003208000d04407480e038800b01a20141c040003243c02c100c43c560048005007225041c111aa0502d070100c0300004003204103103801072041c10744001c030725082400c40504035030000c2c419101155501c41e0301d04200c50040b505075103ea10920a541054400c0340003140b00340e8209000683d24511403402030424900c80e000107040203006079141c083d07501c52200a58102906c1c0400207044000741241c4002d1a1000902c01902c0e8246900340c0d61000000b0701402c580c01c0104000d1110b46800f800c00c030101d409900c01d4072903900000b502002440440c40b00b681402006140c00e1003d41109a01032070b04851820b0303c039090b00c04041e001c05c2451b500c15040203500c025903540302c0c03000340c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 302739091 1250 302737841 302737843
    0x3060316031e0c030c03050319110706080903040f030f0303060608150405040f05030d060e060607020306010b130302060a05040e06010c0206030712020d1401080d0924090b040308070c090608 83
    0x30550001d0310b5218480761002446110003140e8025540410a07002c007a40701d18125440750040f60400c003011003807a2683c45200c0c05070100321460a0090010160b0303d10301030303003100c10403000360910350640001c00010442c543c3c0c03a1040c0300694002c0c403d1015104143c83c00804a0b955a4002000c2084a0042c4200e0a038010f00c0070070b094808940100c0c0342d460300e050280700740c405808014014800056030000d6800d03a5085501283c5a08058000c3d513a1200280946840341d40c00007503043c3c10440050002c005c0074000390448014040704031940d01c4e229408141c1a600c0301d060100070600c046810071540c0d096803d1b00b64822004c0c41e10303c6501b540c2e80d01107540d82c04094102001c0c007008010b200c0d820f0820303a050390260308001006110001c0e10f00100b42c5034400c02c2c0162061030240b0b40c8500038480c0a040040c0c01c655008800d142880700741201c801418201c825280104500c0201c00682d2100000c054005180600411583c907041450412003200e201d603ca0800035080000802c88914 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 302740341 1250 302739091 302739113
    0x601061107150519030504060b04050c1213020a0308030406060906050609060a030f020315090114090f0403090509010303030b091b0d1e050114030f010204081c030e10020306031603 79
    0x1d640508400c00140b81c0030259841e000e0300c40000340c039150308544160380550540055008601a9008220f04440340051000303440f8102c2d545030007038004000170300601800040e125804a12400640b98010701940001c40d2001c045d030050303802000100901080c000c89110303400c0140400b26041041e20320344004a00c660068001c803601c50704001c585450118000e821030b0f0b030700c0d103807000b001c565a2518002a88144014020482c0200c01000000c26a40e079504070080045000034a02e40f00e0745d50b182c86150390104000c2003101000101d40c400034035503c84d015514061131081d2404990a150001880714440c40185800000c07a158001082c90303603109000c8075505905220042400700c1c0d040144c0a10340f04544c01445031030b1410000056141c400f200c004012882141070303801a0004401d401d090b40030324051030590307070004510f10180c40d1086214094206040c14049041c065a60140d402c0c400804629003070507400208011252606203ca41010481c0000d03050009041da1035140281e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 302741591 1250 302740341 302740349
    0x807030c17030c010606091d06090c0901170703050103030e091308090f0a0b0d06050603150904110306040f020109061d06090102010e060709090b100c0f03050d0c0e030601061107 78
    0x449850749400c68420240129004034220b8002484040d644501c020200c180e9403041950700706c0c41a0310a800c40359108030041c000c4400500003541da440701800200700b0750207004614103200f800f0340032704010100c0c001c803613104940c039490001d45503145040c090300c00064025800d2140300c00000300081d1001006006d94510341103040a610344504a011511194000c2d650303540c0f242041c1c1c0002078400c4240010045000310f240d00b4444150798009004243c002500d00d4143c10008480300429070030100902540a07014181c503001094060000c2030420310107440130b0340e261350130050720829541c01c0440c40d40100185d01c0e04000c0c1101000d2060301c0c1011040c0700f60321401c000a91008030b80c5c0b00750041c003030450006056992a08006030060030004491154142890425800b200c151804205c02603149003c2c1d1076240504400e81d41d600120b42d003031001207040c400240413002c5410307207900c958601c0303040ba82c55200c560580642018900001640031000308064000d0b42c1406c0d04010844500315 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 302742841 1250 302741591 302741609
    0x1305061e031b041d01021c0e0a060b0409060207120e0f130510030b01170f0a0b04120c06050109020d0f050405120a090914042108011202030c040e030903070807030c 72
    0x140501c6000a0203401c3e481d4100d400d244044c1c1d6503144014041d40100442d040c40030095000c0f0002d0b00d040410760741b00020014203500b04165050124089420010910500500025000c0311039910a000ca80080740207451032450b00251004441d005007411644041c2107030f0001038602d98070001020391150b034540001c407a8075035001c0790066580c080410090b59200f9410749296031540d2121040442c50300210015115018480740c00c002c010030302801c0356400241030100303a0345507124000c001404400b1441081204220400072440e94440c1c14081d141491003d030380c800000708000c051702d004d00310045509241800380b01c00034034005030701000c2d8800020341c82d45486409209545074051603100800d0581030110340e003d0171440c0e407020f80c0300310312440c8010358140030071588c03105c8240c070040c0080c007041c0c01c00300611060b400301d25001b54841c03006003141c14504600340030405070341c0c03611038480d0036070b1000c00c0d810401d10b004e00048000e880810000c00c201440d5403500310451005206a441c0c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 302744091 1250 302742841 302742883
    0x6130c1205100914070b07030207061d03070602010509010b0105030f0f060d080c0d1101020a02060703110408010204080105061f05040915030f14060709060504231305061e03 76
    0x4020007404100320600c049801004100030f1810440c01c12840707500341030f0090080841c0411214640e00c1a2045c503501540244949401e203101a10115032410000024031501030480900c1da0302000328002420071a800841c8900b000c2040078256503030005003a0500c4014409c1003021100142d000c1d0703205007a02d903d50308a0725400040744130b040c091a800b928111001490075100f01e40003035181c480352010340d40ca582e101d01c2c00190038201d00500510340010303084400440d000500c00d030440c410380c01c411013510f480c0c2940c4000850881e8000e9016802c0d594540d81003000c82c0c6082d03100d5100b501058007030744da0041c0341420001d000317200d140210f442c140d54516803103086071401c1d02c4e540042d5510549c0300400300074608180c5001c41508091140c02d00c00d002c0000c242c1c40c400d1202038200e60709078680c0e078100707801e00b41003090a41c03520144400340201d0038000910380e55454010b80f4a0310804000080c40d040100c2841340c00390141074188101c080e02c0c00300560030340380041d41141a0001100ca509 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 302745341 1250 302744091 302744093
    0xa0b07030b0d08040312050f070b150607060e010605010f0804060207060603020904150c1e080414010513110406030201090e0603070f15020f061501050c0f0d090806130c12 75
    0x4018256041c1d0366030440c00c071044220801504000804c02d0b82c0c001d00e4840014070313512500b02c6e041d12503000b40c48011032042c00014005041c01400725000911051299802800305000c41d8070b540140c1001e0303c0c01615002d821062003020f02c6190003a100030310f007503244d0441300c4001802c461300160000b80141d50020f5401d0a01c20158850005164010314003d04da040a0802e451000200d03080d00e000103103030010b00c0900314001c1d420398a60f0440a01944903040b881402035a50340e0b001001500d81c001d00d014294a00402845400d204504280d1035000701d0860b420801c05210441582d2070080307282000c00d1003d070783c00c15210b004640d00b00e000ca00d029550303080400d041c42030680c45010444500007000c110b82503c12218101b0002503800c45260a81501d80303184e032400d0a450020845030319020031031341035210310002c08110034000c04a841100f00d1480c16890310100501c0e900001d00203c1c0148241e28080c07042980148020702c1d0000f8108281d262942c019180e4400c0ca590b42080081c884 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 302746591 1250 302745341 302745347
    0x30203040e0c130306061508100501230301080d080109110f1602040c2a02060d0203090a0f110a082b0e060409050117071a090d050f1c030209030a0b07 66
    0x14011050f0041c11040340395880c94540003074031503409100c50050b8a0740076407443d54412180c2903c9071000c9600a000ca62a00e40151411407000d00e20484502c150403164006804600c000c60003010b00c036000703150402c1c0f000c000400c0307080306803c03c040c1d20703044c413140c0003441116005a035000c5104503102a668900d81700c505114001203100290400c0c10245907011140e00304500c40000220326a00341545625410700500c01070f02144003d41c0304006000d2006904c18607406585d000003000216007000c440ad840d031540c01052a1002c40760150080341050080c10801003801c0108240c0000b0180b501413401003904405005121414402c1c3c01340110743c11074441e4032010042034001e0540c55880c0c1d1607545000141c172090154141082100440040d1404005806e40440e1141c100d466440880504500300aa001c1c2d101c0340e0f400003041180301c01050052140301c1150303d5282c000e001c0c039030300c2d450748403054035424100d43c0070703d0720520400d06036131000f00b00c3c043c8180d44500021425a103c075016 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 302747841 1250 302746591 302746597
    0x30705120705010f0e1909060506070803040f08091e1003050702060f0601091706091204030503030711100606030f2706050a060e070507051006031a0901060b0c01060f050d030203040e0c 81
    0xc951b000c401c15400660b0301c2c003185100002e41382002e00520003c1d84803424440540b1030580010440d200400005020070300041e6043c10181c80b079681a840c0480b03041c00240781108003000d40740c2d40300007016aa1542d10b01072043d03c0c0020680c0c01c042c8494a4a00070280d2161f40080c03e00c0c0c03d4080120026a890f0311583e40c0a01034803006001c404484a4a43c0190741d4010031a0541810f109010703171440c0c1710b41d85805032000c07268400001c51450350345e070344104c8002c42d0720650180c040c41800e041066000e594040d00c009807805680018083c03036180582c405480c06002e43c030000070040c40501010703c030b0000c8485146034200c030012a00d9298491104000d1480e503202e2184100b114041c0800282e00100070302071580994110b8030183d016604040803070b1b0041c440108000c0101c44000f16500e040d00600768003400f04400055000d0381da0700d00c40c48650001c213407100315940d82c100c01e00c4955000c80036400a04025244800d6072511903501075580d1055000c0c0744104060f038000507903003002000c11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 302749091 1250 302747841 302747867
    0x904090804081608030c0304170c0607110f09190c021e0f06010608090357030705250b04030b0f0906090a0308091218030705120705010f 60
    0x1800340e071182d444507100d0700d5055211181e211110700d50000581c0038000826a80900010405180b4207841c0102803241d0450440203550f80340100240e0600b20394400010b401e034140680142c00419600d0400c00821413040110f0a03c5135806200740158800580309000180401c4000020f50034504007042c0e2400b08040c0c0c42d02c44559010001034418400885c2581c541c0c02c040c01100d040340d0300d500c8146c510407011586001154824048081c10381d024140c0518003412041c65100d290303011000103807000050b95804000c0c020008260070310b110802030403444038507841001d182014119620a5140e04c80b80d115600f42c0840b8201e00c2d954030010049100041c032450700c4260741c03039903a4175086000841c12616401da503e03040c4c002504810303010844078401c1c012038001e0072404175580c0d815120388030042d045000910030003c5c200c480c40450390003050071012000078104c0342a0300301c080610384641078005a0158000405030580c9010020f601c0094400c24205070041c000381110848070b950384400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 302750341 1250 302749091 302749103
    0xa051201080f010507090806060d0c0e09060712140c09031501031203200712050405060a0302090316031a190203040b04170c0307060509120c070f0e01050d030302090409 74
    0x1501e241c0054240c007001448002400a03642d48102914001001c2c440c018498100c40c00080007403a00c42113a05041e48251013034020107481c2c410601d2108000c6902942039400031040c0b00816401851940445110b07903800e006150402c06901c440d500082c100c60312840001c142420b50b42e40521820648035201149140139695030b08040030541845407036000070030f1819034000b108001c480450141d0140245100c2c1c0380034400d95403500112403040c41c101c00c02406000101e9696110f000604c078600540d41c000d600c03030710300500705802d1050b1905500710070074026000b0000241ca146a581441e01100b003070768804c0e42c43e980f400d4024071800d1040c24005100100300000c022424081c0d40c0038900a094142c1c00b9a02030398a1013261003501040b03092a1b00070f0180b000054a1a0071030356008507800b00b134907010401d410700a80c1a401010040590307401004c028003d0010345c1101100614042c00c8900c02c5500d000b0100d0a23061404402404043d00000c10b035105403a01d4001d0443c0560200c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 302751591 1250 302750341 302750377
    0xf030405150c030c100501080309010813030c051f0516090b07030e03071205060901090803130203150a05011503090c1406130902040504061211121009030806010f020d0804080a05 78
    0x2194840d00c0e840400044140b45d1310706000812410750000c152a080e401c1a11000043e880304007010b04020300907030007203003080082202c02001443c02c4c00548144400140088120651800080281da000928903160b201c0070501c038030025640000322608030780c0e16509840d9100c9560800311010700201c505039426210b00c000c0000d0340301c00c408a4608440c040c80036aa03880d128444031600f40d032245500580b0215060022800c3c2110320341070415141e2005084072010402c90110f20503c2c54100c80c0407a00c1c039a140b004128211221503010341030b140500d1b0821140420340d451011500d00c038060500202c26144031703c1140d031218001c0301c0c0203405189901c0b01d06581c3d4000f0002952042c000d8038080e1b800c210000450841030a100d1801035400020140b0015408041c8201d40c0031000710380200b032141d00d1500c40704c0c08091156503d030314001d940303c940304d1030311900140a132929200c2c0841158800c00028100c180d00280b400d0b001580700d100c90f50744a1442c50216005c0c007a955021b03058107040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 302752841 1250 302751591 302751607
    0xb01051e090a081b012c19091103180a0f0b0a060b13150309020901030f052a040c1407060509120a030506090a050f04080a170f04140f030405150c03 65
    0x60003c44013a0302c01d9a42c000720782e02c4800e06a40d4103804002c0d00701030642001d004a02d5140890344010716443e01941034640342c0e03407107040344195056107480c45441680002031290021550302e0800d44c802c01a4006c04040020759580304040404c0f0001610440c0f0481c0850711556058000e2802852051540f94a03142c0c0c070012900102e0041c460050109040344a50004600078091401c009130001d141501e260b103180c40b06046254060710403201c40c00703007100c82c203040c00922200040c1c2c9080f00030303200340c16000312040c0300480300382d0102442444070595616014208103800c8600d159805103010400d03884010f8640e1621104141d80c40c0350450110710341985a600d64840d41c81400100c1c1c0d008416100c60307141c007085500580300c14a00031202400100410314101c0200b03100d16440c03401c00c071001c8801003074500080064031541e4444004200741b00c18400d801d94007400d007488100180c184408080031382ea40d644110b01c1014000c003034003102038220030201820303164011421303003e80750f0354544 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 302754091 1250 302752841 302752873
    0x3140c09010f081303030f0b041815050f040809041506030e070b04060905011b020d11010e0909190809040501080607020724140c010c050903010b01051e090a08 70
    0xc2008500061950750b00d4a212485000c1850150076030384081080701c45180c40c2107000e05032013001180030701d459203910300d8662140e00c9005218a007001c0c60518880041c41d048008042d40d8883c4070302031741080300b0b1241c000c4000511903002503024098641e101840340114014105000592070200d001c03440c00a00950142c11140b11000c3ca0001d885e143da4036a040105240a18010b080004480304420f00c83c2d54083c4000d0381c501140580009114078644d40012840c25000408590544664121450650308880542c0c0a0a011503041c8000e03d00401c0180e0b89003030443d489840208000d029000703100054088480e01d0318090401d0000d5a11445540d41d80c3d102900c0c40001440781c1100020f0041d080c0d216030107520041001c01102e002c00c800c00325806041c5504080010a0411007194240401d1240100e8031200d601c1e0710b074640800c40c0801d42148c2c2d901d06003e0500208205004090030302e603590303000ca06400007525441d0107041c000b042e213149144c2c00148940c85040244428040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 302755341 1250 302754091 302754097
    0x31504090218060a1a0d232d040f1104020c0f0106080c030d050d0b0a12030906020601050a0305060a0e0f0a030305062416110a030b0105040f110a0f03140c 68
    0x60251209016a0359170000c0b44000f500f010040d0440d41e0091040000d04040c40d001440755005664080c40800d11034120200c44800179510010403a401c4142000840380d034801480002001204100407460070343c0f82d2040302c104000c0010940f102d400704000c07550707589506882c102d40c0d01c4000c4800c881e0100c2070141c024009070103040000d1113000100003140c54000751325000d02c2215507031141403000c90405480a0800b406e00268400d041190200f0040c0c1145000c2183c0ca00039521542402d02d498000b03420544107811290107400d4404080c00403c070005034143e0070048821000500f0100540c01e5800c10004c18541940343c080e14040e042855416000540203550440e400d80d40410b4204032681d09080070415400c41d0041441140f031146200b00d01441c1240c081d00b05982507011b0040001d203000840e402c100c40d041b0981005219508203032141c80200d2600e001c0c00c101c0e003000c00803c0170841c021011000104000940d482085070320039086003003142034a00104026003048001e56941e50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 302756591 1250 302755341 302755351
    0x2100606090e0109021c2c031201081c0e03030d1e050105010c0201090e0402030a0b07052505031c0e03040605070506092107020a031209230105031504090218 69
    0x540c1c0400081204c4410b407007118240040302c9000184003030503800802c0603140407070380d4010780340c1051208001e0014003900e0b14100804140075680d10080300111512401d41a00111881d07403003a0790001e595404410104107038420750030010034207105007001070701d148503040c0a03054040c140300b103d80400880010407071846402c01c2c428001a038a036001101d2808c080e0b40044d00203840300c0801c000c00c111041040340c0190010341900c1032108151208501c85005807550800104006008070301d4103598004d000348a8065030090100750300342e0b12001d81d2070040c94000404442c0b0410b038a0000c454580c401c00380000541700381c9403640d85c1d686e00904640c00c1a10181e603103001d00800210600800704500c0841100c01c1c41d245100709000d00a1050b40e040407000302e030845003100380403002c12040384110303111511507a03404a41070b061003e0000401c0124003550714440c42241e4a030340c96a040710030350f030703010888110018844c944000002c0141c8610172010790080403001c40d8403818440c02c0e400354494 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 302757841 1250 302756591 302756609
    0x108060427030e0a1a07080d02160c0f080c03100518010f0501031e05150703090b0f090d0c03020d12090f0b060a051005030606030a0b031f0c0302030f070f0210060609 73
    0x105980b070b40e81c6240d01c585001c40740601503041201b1000a2554005002c0c0b00c505082c0040c2840d08294035003c0200d55514260344d0003009410800510f00c1d030304120030160500c030b4007030415a1000c0e800310b07030b486034025103d900e155219000647d0255008424241c1c1084000007070101a80707002c03250b80186005e010545810701d46188100b0020300c480d240d640d000ea442001440c0150641c8142d1200100281c00b2404050b01c40a10750702042045080341d000760344c080c1e003640a41c10700b100c440f0310300308212000509106c415851440802d80100d406010070809081960210030002d0400b0014486010020666800258070405125110301c40c03611514003a00c4102c115078565040050034905d9081c0180000c6003007000400b5410643d018680003180c0d40000300d040b641c0080000c2c1800c04000074500607882001e5084002c0c66540548280c600361800c0440c61414a0b10590040150041410080c0f04058820014491081041c80c0d221001281c0130400c20b070715118002c2c0454958810307280b030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 302759091 1250 302757841 302757859
    0x25060f060905070e01080603010b132f18030c0a030501020904050907050307060c0807050706080a0f0c0801060c030c05190309052b0c08100b0909010b0108060427030e 73
    0x4401040c41110f002c0c0f1466190420000704007001190503500041143c1e4255407510440d035595129413840b803c60f103030052400702d420000c00d80211052078040704138120b81c80d618405590001005011280342c0b41314003840071049690040481c0c904001c0b41050f0b030700320114070b00000601a040d405040c083c1c1c4110f0b0140415250092540e94071082401501e174144c000c24010800c3e28002d1161070700310361281d00041e09051158560500f4880d60b40d02400c0464004420440003450340d04c04c00f02081d241c00d070b08110245444100410b8503005007d003005100729080c0003010b0500554180d80113980c060111203416030304604011510401003811404a0501c0c036021500e0f14100e11b4004c1d035001d00d030340c883c5c5c0040e031070803000d0850b8100300700240c44450080c00003007802c00040c0110700340310410380070214400e4082001d100f405c0800401900c10f603450700040c0d00d9941e9200d148540c00c28400c48020420095031002c00d0b0f900b03990260350360303c1d01a0402815081582005508440780f00c1100c070350346 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 302760341 1250 302759091 302759099
    0x804050f09070f031508030a0c0c0e0c03040b040305270109170303270607020109030806060720011101052a04080a0303020a171005030601090605031225060f06 70
    0x110882098806001140c005060202004d209a1040d44c1c51400900c01d651044d540b001d1240c1903910801145c40051164003085041c0402d002d105001000d404040c0701c1140b81c503001714019400b0151008060400d4034000c10185846a000c3e60014030510070031403030b0304901c0001d603000042004c0246020a43c00040000d0121100302e914122001c0079019615544d20281d000b12641c0341098040b01400c141403400b01c0a04017000444d100d00f016400004041c07503103084c06841100010312452041c0c200b0480b61001603d0315050400311000a000d0040c220040700051b2103400c0d086056408546c81c01c020441240342003451840d10903215000c11042c8980220103031524440d502903001c2940c0b05521100c00070f84250700901c01a0124a00a850007410312061000c3e51000c1d50341e40802c40710041d00b40030915041c03003094010000a02c0802c04240351102181d16600c0c000c0b00050941d10205202c9001c1000b4115908018110345103080010002d1a00900030705215032100c01841c60500041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 302761591 1250 302760341 302760349
    0x909010f0f0213140a121208060a2304020f0c0105010e091606110102130801020316260a0603050a0b070f0f090b1b0607020307050c0d080405090406020708070804050f 73
    0x58482080c3c03c0d1141c9500742081e00d80c02c0c42009500c45103030001034000b0000390743e02e28070840d8200d042c414408807040c03d05211004214010207007a0620440399044d0800c20503050b8429542c0102441d60207a0110b501000020001d01900c111068942400074808400e180d042d40018140c400e02041a84603459070b042d0350b640c03201c4030305080c503810f0a00300e000d01410b0302138090300f61641d9009001502e8890320211031011036005500207800c5a401005100c080c403075001900c0003c450300c0c42d00b000d5650350880074848425004508102c3c20780303003030041004002e5540100002d50342040490340d4601d002d01c0e000d0b0740800201c400700000b8401c20b00104202e486445100309414070382c5d40702400c00e4200501004503501c6200000701c03c02503c0c0000b800c984060010130300c50a4281c0107141c440b103250501e20705003c60040910702c03c01b0b114030080f000444c540e0a9800b03448068605550340e075643e06d41100244030744400a0148800403a584040004480c02802aa030095a00070700c00301a2100344 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 302762841 1250 302761591 302761597
    0x40317030c120405160611060f09030319180804170303090d050a030b12030d06061e050a170c0304060f290307051201020c1203150105180909010f0f02 66
    0x30580700340d010072200da0007140761812503400c28010000d4580d2a92004503503962042a60b12490100e940000308044504c820f215440d4071103148159101c041c0782034111580ca0b403100804004000003101c08041d41000181c0c0700260500e94400c1084100034182000081a00988078845200c001500180074040700802642e0140c800c1200034042401a458103071803c3e0080d0303200364109a0395600030b80480d80c03400c040041e030707a05d12005185d9880400075250151b40590304600d0611003207500d101c109822032304440040032030780e01e00703561244202c0b07104455116903000801e004000c0e000034810515944001580220f100301010041000e601c001c030b8017542d04100603a040390722190701410140e00b0554061002c91002820356150781d4071000002c0c030881750600c0c1e1124a0b035020914134014101007116440d0303400180d0b00350307085180c890420106000000c14140c10440041214010101d607420144030020300181440920300e4640c9441e0f000380458000c0070405810444400c02e0311902c3e10031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 302764091 1250 302762841 302762851
    0x405060312270904060e010b040603211106070e01170f0402010e0406050301060b0306130b030304030303020a020c040203010b0a0e040605011704020a08150403030e030f03010918060e0304031703 85
    0x8070302c1c20b000750a001400404034524503040284a080420080b03a030711100f59500c158458000006d401d000c8826480c211440e070315407140180d150074070500108149181c2c0ea844040c0041c1240708480e00038100300e40021600304054198800c200501a54a03005003102994401c282d898003440d03201403411400e104410b84100c8003201800b40030034095441000c0000c030134800a480800c940d541d40d0042402c40d0301070342c40107650940200a004680c40c005c0d4008926003d2544180101b800100000fa1a4840d600c001030915a0000303000012500900c1040032403c0020300442d104c1d0381d9644064820340c8184d61820000794940d0075003c00346440d12580741a108103030f654011600c00748501e481a00c0025006907400301259800103290402002829404e94140c0c04d0254030341860b140180c1a100c0500c0c1d8032005410901246420004050540c0e04450325190041021070040d805469290590040078103c941451506001c1e643d00200500859110b0704108070350342502585a604d9000a0759 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 302765341 1250 302764091 302764123
    0x617060d0312020306030c032a030d0e27100510020d02030f0a020a060908091309021503071107060216050108040f0206030405071701050609130308180c0a031104050603 74
    0x240d40b04801c880e503020310340c01318010f001c0f21900e441c100e0000c1d1030007040180c00a980391892410190358050009041421101600100b1042c0b2112102814510700149103a02555000c00000c800d44c07180c41e022803520302c28448200e01d500704030f0580500d198035405083e010781541c441d1510054070000782e040c290b9444c4c0e4003850034018426881419980400040411481200041e4011842031300c503521820b0702c10240345568980407802e10049925001760703190a149842c0107500580c40d0341c000344c15001407111131540c0e25903407264141c8145841c081c00c04402e218442012510a0700083c0d65007008030014401c0c0b60a0780c0c0c6000444e0000c00469004010080e0050140c00506080014640003803090058035000d90700c0f0080407003084003141e1003404603134443d010301865080810949820001d03205d00c0c607611248945000e0107031040600356401803510f6810b04400c000d02400701803e401001801c092420395241030505002d4003121a09205d94a04030100b0090700e00040c681c690020b20075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 302766591 1250 302765341 302765357
    0x4050c100e0904030f05121915080d0c0c03080a0305070912050a1709030d03020409060504050705090f01120f0501170f060c0d1104090212010509190e010f060617060d03 74
    0x1513000c95840800030701c40001c0c4101800881c07030301001c4144181c4665402004403444d50021804082620b1354400c500ea000d0300c1e44841840f4408000c22401104c04107070600001da41c24910f01f01000441543c0090100100070031607605150340750300118054206607032031110381070b00c940306c0144405100900904a60040d0048000985400103110b884910320340d000c0e062007009030105c1d060019010440e0700084d80003805000c04480d5100d003401a101c00c0e83c04000e14074120300094203501ca40781c0014031030445500d0fa00c0c1c0c268868010042d0005810400340014649080c1c00d0018000c2802002400690858648000340e00005c60140d464540001042152510440c041040c0c0c4110341d4035851782c0d107030745042100910307500c0200700914039801c0040ea0f892202c002c8000400040e04054815580201440341c141d030141800306407800060030014202c116001c0981c01055036245c11031402e42090000200940c0015420b40034150711042c0b000150b0b65002007000d144000e41004010590320 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 302767841 1250 302766591 302766593
    0x13090209100c0c0e1306050708190b1f0504030507141c050c0303040b030103120207030213230c09090106020102070804060c020d060f0222030506130f080304050c100e0904 75
    0x448400c442c042c05656590715998907514011843c120480e01c4088031045c074180f40c002c000507803107481d60064051400380a00e0801400c081c62506200100b15840340d200c1205040315510700000c03020984200b100e00302034030701da94400b40c800d8015201c280c0b014020740c40005581a0743c15440320988900505050440c141da8011082c0750351010b405561a00c542e60b810001b50314208004c0001c0c0180c2081651290700d14500080340c00411084070341190460401000183c07280c1804101246501d140410f10003066591421003c0300ca2250140d13085600c01813120040303034003000b0001401d05603403e40031a131329000141e00740d215021005256002c1081b00300030305442400c610000510083c80c0341c01b2041d00e501c070402920302409804024aa0000c0c0240030900b25000c0901d0440040340350301e03034481c030315141c241c1c4542c00100500d5604042d0402d10301001b030304076100380e0300c01d60205845480342820b05009030340d940684501030040c1d256000c4106914050b060340201c0321402484103000d80d640b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 302769091 1250 302767841 302767847
    0x601061706090c0c21071101021b010f02100906020c010c0503130f02060d05090c03010e070509041407030f12080f0f04030f1b030c0b010902071205090a09020f1309020910 75
    0x2000c4000c04e409080081417122034001c01c050000850403801d1070701c8424034200380364a0981c000c6010b05544c08801c81ca00f84040207409280075201c00d0034282085074140c2c10903800c3c91050444150b80501c0e008416040200f16409014403440ca44001c0001d00d4019400b507500b072100365007448252440800500020f01e00880e603890351032000d400b0f20b080800c111014400c0c0c035000d44a80483d5007250744034402c2800c0034418040c0900b00400189001803a00000c19450b010150001d02440200f03407512032100c1003005810025607009019000ca000982813120b050210013841d040002e41d170902144102d802c0000e8603018038075694607042152900d9400740d66109803401c00701d042c07149244640c410040a14090200c281c0240ca4110b00d038420780c5030005104105070802c08009105100c94000702e0144908225000d045e400e02c1d83ea00c0d04803034009030243c80e4030350003510300c0b5000092802e40f03003540002400401004080030b6410f079441d10072080076070050540e200d8120718004c450710b0741548 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 302770341 1250 302769091 302769097
    0xb0307090e010204030f1103060c16030c1406070f0201150506180d082101050306070c0201080903070c0b1c0902060a03020d0204080607090e07090e041103150106020601061706090c 79
    0x4107400c001490166a41c0c1d8041c031600034030070182c0320006480046402030405100c0079901507940400c2070325004114203c42140744804502400704440386a107001040000b540580e0040c140208458080c908160000e0615194141210042d42403109042c8000980340e0207106444004010301c0c01c00c103c0c980140020100d90940381d0b401078141e020300c80031804050080280c144a804000180e030001e0001c540e0007072049e0700403030181e4005c400f0040d1540c0c0c480e010312601642440d2144040c0c9903a9032503841c1d40036100d00502512032580d4000f803c1002c041c01040320340ca0305c20703814035900e00202c05501101c81001000e5007043d010000000000c0c40b03903005280c071612807c001410302d40ca07800d0301480d1450440709030380807940105d400c0c01044d0003103030b25560101c0c991407c2e0030014103102102408240c040c07c01480025100e0700310003699403e10a10329074000702c40342540190780d1100000c0d50352800784140700100b110070707902840b86080d8010041c4a208081d144c00c845481d0030110490f40e078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 302771591 1250 302770341 302770361
    0x1e060307120b0a032913020907020a0b0c0d0e0d0801090c031d0a0309051f080406090f0f0b0604060803030f09010e060108160e0106020c1002010e1f0f0b030709 70
    0x80c2c0d6a400b4201e09544980c0c591000d103002c1c0a01c02d142c050b942200c04105003080c0044489014004100b000c40c101c0305064104096059070b10620986500c038050349001c9074840000c14040c890f00812080c407905101900300c1d01040c2c0800c0c00702c0000d816803031340c41e50341030004000041c40060040c40408600d0300100b40b407900e1450009440121349084c0031a0420b094400c000b075402c41c240680504d507100003200081d09040f52103c41461011650040c001e180c0a108030034801d100c0300240c2071011680c4035402441d0026400d03048540741c0d2030040c4005039044d000300d41c500c1c1000041042e44c1842c1c814201640c81d00401903107140c907603a00c0c41c40151b100402d10f61a03036403950b9a2020b2050107022150080000380010224960f5a4034900880602e0350800f4401c0718046004100c0341d94009250900c2d8003041e68480c00c0c18854002c100c2c00740c0341c041c40041c1d076441401080c49a43e16400d2a9949078013400104002c4000010003060a80c4c036542112640b540c400c40041c070180b0020340c131098180c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 302772841 1250 302771591 302771627
    0xa0204200a0302040e0f061003050405100e0a02030d02060c0403020f0303040801111e070b01050405131709120d0903170d140601021b01050a050f0c07030807021e060307 74
    0x1010010314060455101c08012000a50082020061140040c200302d40002d80d1000d0441d003460620301051406450251100070180c845000c138090040c2032088040c0e111101e40140800e180040507641e64013a0302508a002e0301c0b0780341ca004c00740b43c03000c1340d0b143c050b0701440c0c005442c0c285560200a04000a50700b000c3c0c0c540410080010385100921500000ba000364165030345400301803403200c0940110b07484800507c1c108004410029403443c2c00741e0b056a5080300d0000e40350300d554140e4034941c62200002021012903800c251324a861090291484420440301010801055210240c81c1c1950b40d500102181640000748002955040c2c103a6502e055801d41c0c6003005441c45840c02a034601d0410010752090307031070501583c0d5038140160700b002da040800011404503402c0000344588944200c0f001089804500c800740c911507030f021a4009011482280c070303900d88a0a01c03801580c04118100e00c21390400500c4000c8012101d101810008001c244a05540d203945055422446a9803103d1403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 302774091 1250 302772841 302772881
    0xa08180a050303120106080f01081507031e0b030d2d05070b0a0b0a0915090203060d05030705070e130c06050918100320030a1b0b0a0c0606050108090a0204 68
    0x6182c070200054180140440f00c0c40a055142890280402c180648030681000c4030000500080300000b8002c07500350031300354a410155941090440051032814016802e0024074040400c0100072504a071440c03801c11416288161814603090318000588031100318501c0c000c8039020f030308806210005602039500d0030007610340003056a41881b066004c5405000084e0350311100115420200014009000c0d01082004104200c2074150090140f1344070782e0041940001c0062100d031034210340e5104140d03221040380c1d141c0c0121316040e45c076aa0103000b1003d002c2004400035000840ac0c1001c08030083d000141104c185062500440c0d02c2e90040d0314140c2c010401d8a07141c0803c954940d01d0794402e080c80c0304212507540c00d62a181f2040842c20f94204c20104411100003059540130078030740403099000f01240843c13000c0204c07280c640032203940106059000800c1c28020244c0104000e00c1c2d040c41514100403960f10f07040150b40b80388003644c1e4030b01c05604c022860001410aa4410628141c43d6100d2040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 302775341 1250 302774091 302774099
    0x1b030e100e060c030723031e0405030a060f0e070e0c07030c1203020307080723070f0501060b130519050d110405090c0a050901211703131101020a08180a 67
    0x21042d48036810b40b00c8240e10005d514400d1158410460b035261190f4a803611074000c404909950382c4c01007038403101d90a0000f05041080e142018102c40003094040e0075501461800d04002d8000c021401c500303a5981d08020019469503400f260f8102502e0501e0a5040c2c01d03150f0008485054020242c00c03414071001100d088080b5941801d41c62041203e5680917942e813811580081c0320090103400074051181200c50820804050345000500a500514043d200c640505001094070922170b070107045540b80410200c0c0b0f8821000040007003280000e003490401f5620810f0041c0c2e000b02007402d080c0d0004851003401145484600350b0b11083c0981805400240d82c00005070441e80103a5030400d19a0200c92004464103051803080000e0900311140c01c842d41c076288160017241034241450712500b28081c0903a041041d0a004805c107159401d40054403441c040034a00000502500280c94058040d125039039958800591000f01a50140c2c0c03a9040c0600448000801c480c0080841d40c0180b006038041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 302776591 1250 302775341 302775349
    0x1401051e1e0304290a2c06060108011d0708040f020a06030606090b04030b010909050a051b04050903090a0501030b18040b0a1d0c0906040e060a0c1b030e100e 69
    0x200100a0314041e9079a040074508041c82250202c5865209185000000381c0380410480c41070388030348011404140c600d004806101444168204000224440c10600c000b400000502d54807d483c03c0c0c03664031181e40c80c7c094242d01502c5900303103203105400104c00101400d02c104403c90b001485080d5032600c900a43c0d0018441011681200700003d9035502d0070001c0d0303640099030200402080761168a02810342e200c44101ea5014003502d509152102440c204001c4104080030b485034110003a1400f0201400c00c543c1c1c038070036002d8043e11403400c00b40800c40b003036400300496108000040c010000c4914080055014000259060f680030441c00d400103a001580601184520b2103440c02c800315240c6075890100711280b58000d805a4007400d5005a2003e4000508881044044810700c0700c0c0c0d91a1000903015218040c11000c0a00a0500340a07500d180c9400144402120740c0b10486132541030081d041441a80d440d000e0005555008600e10b01d0a218000040200462400001c200b903424045 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 302777841 1250 302776591 302776627
    0x1060e161d0909150c0406090b0a0513240305071e02030f0a1e0201020c03030103030305060a0909030c03031a18090102090901030309030c0801050c09041805060c131401051e 76
    0x514003504a003403014078008000c000160f001e401c3c2c214507406c16042c0388000308035803000c1c01500064500040c4003082c141c001c0c1c1c01d0369520110441ca0116241d140e81d0440d992100c000100862400130b488500443c501a00134248242c0c0302e5070302c500780c40d283d00404c41000d41400c4a41015808100700c0c101000807884002d00f1034110a80390841246034410a05007408210a100e40441e481030040c102c00c008003008580c1100e41500e404500c80d11a00e0010b164001a9400200c00070700d0308400c08101600310400980c06030181e101040380503400c3d504004505001e900d040e82c400b00d890702c0760b600240070356035031a0808094400181080307000c2c00440c0003100207030000ea01144100504204000d1403040c0000a0100740009001c40d0801c2c440341225402070310051031055440d04004900d580d072100760300003001e03000012540107040c1000041d813070398000d070f014490a9000c1c02c1d01043c40e29601510500403041a9140d615200c08811006240340030420b81403d907040402005c40c25451180705 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 302779091 1250 302777841 302777851
    0x61404050a0920011106070f0f02010e06010303082208090402071509031e30090210031b05040503030304020405180a06020426070501030f0213080c010201060e161d09 73
    0x800021043e000002404003202c0441405d91603000d40100203107d94091070242c48643c0ba41080b003042000c11001364050030542c12500060310400d40000141603100144600402080c000c0304004841c1002c1040c80c402e5498001c0c00a950400c2135240904096005100e0b15014401c641e034200414156001900c90700c81007038000500303049030145000340d819201c65035a441418040700c020101c0580c3c00c000c0f007440c0d014043d1440220148801280160001c0956950051a00005032031140001e070040100804000700d68500a202c0700e001405030b0100da081d03d000400440c1076940b20360810014000c0100040c23260060b07501d4003035811100300250600184241000360301c56003003c84031042c0400c0304048500c1c0c0c6070020000071001501042040681c0c000b860302147c410741244005000e4401c01c1c0701d080d011321030300d000080c600d00045441c3c0c3c040042640240141560340d100000c2d40c010949501340700c040c09105007003443c3e00074245a540b0321000305410028550301d600154080c0c030200c0f4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 302780341 1250 302779091 302779133
    0x3060906091b0207030c0b0904021c1a0f03060408090d050604060b0f0a030f121404030501020c12031b03060d02041107051501060215090c0415030507050103061404050a09 75
    0x4580c582200c100302e214200e00e803188000c1c01c0720f5145407200c0c1da5943d180e101d8180d5916000410320b0298603550110742480b600c04548420700140000b50100500128145c000b02d407407100804907151904500c800c0100390010002c2850792102d450300d80160340410446580b04400202d04c60005e0802e11450740310318007603c40002c0074488501401000c2440d0f2142520400407031209000088110b00c05000c01038100040c10880c030304540c001d503140c0d50030b90720301418480301040000411205400401c03400b15110155022400c4a000d40707001804240d55001d4031240c00c460380341c203484c01c3c2e01c0990b50180c802460b4040354040c580101e411500010076220b00ca64000480809100c400c0021111840303154400620b19850032100079100c0075106150034040c0e601d100070861441023080910110311006108006600349007180707030340c0c075002c0744800c44aa00940c2c100084941c002e00c540e404035078014402c40900d4000000b000018140108807001c03040c1c1d90822000411240000313542041c1081c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 302781591 1250 302780341 302780351
    0x70c030b0f0f060607080a02012403031215060c0f02210d0c0b060103090c0503030d0203010f09020309030a0507060f05040501021809130b06121b090c0703020601150306090609 77
    0x4a1080781d000002080040c080a00c50300b40515911004110781410b40c000850b40d860341841c11040b805000003180203100c030102c0b052800002c4165000c0441100e00c03d40f14101d420b40c1e1201c92105558060ba00d10f144404024020001107006d854241031841c41400342800205403980081e0180d2910b865940c003090400c2e01c0d04d07120360003c00200900c580b41e401d0003814031400f0f42e1050724000d0002c20250406484849035001c001c1c1800011005e0f005c02800e6a84480005001344001c5d04244070f02c565010f00d00c240060140b0b0f0074400c6a00901000340078600d46900c80c40140c0d800d60194034100d4800d907035404407400b142a00d225150103548110005a507a03484e55a0000c0030501c1e05000324410640b950500c0340d54505446c0081c2384682c0302c3c607070100c0c42d51802c0014581800b031507070112a43c040c1c29544410302c0e002449601c0c00913003ca815072425240c00007000090b004070100280580d0001700188060015198031040c480118540480d1f19520384000c4003c1e140568803040741e098440b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 302782841 1250 302781591 302781601
    0x507080417010504110301020c0c120a0b0c07020108011a120714030406061e060e0909030403120e09071106040b0603100e060402040c030b09160c0602070506090c03030307090501050c03070c030b 85
    0x903e1641780c5114080700290705045ca501c69040c1c542d41582c8445229016070004040b90060a016800340c994006c190307a00f56180c00701d480b06070ba50103034404900180510f0008036010440b202980c4182030000802d9090410001d10102d8210001e8051014091104540b981081080e4019480350317100d403402107921403412626042e02c0f0801c0d01030b42c2503942e10030001d00c02c003a0b01031030902c003014085406500700d0300c0f2260f41c54151322590f0409000943e00d462014509030f00704200c00190a4180d405203010360303c42c48204c5684483d0341042070107070045000b044c0070442d14180700303410060090a580040e00c000c2200012141006003105158005004100545c5454421030707084203540c0c1030606c60b1180203030005142c070300002c0c44560301a6503203070402e42c01031041002c90440ea1b806802150fa44c403c03410408d54541044401c03140718800c1600f0314a071400d011007a02c2c0611082c2d01c0b84420320f03047c400191820f4000708000301880c0301c107000c1500458800000c0d140110300a031a001b4181c204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 302784091 1250 302782841 302782853
    0x50423010327111302070b01030b0901110a03090302120a1701150212070312090b09190818150d0510080a0809010f120e0c0f0406050d030507080417010504 68
    0x38100440c800d01480000400d65202c000740420903644824402c0c201200440003900e04080c0c0f050301103d00e0301c00b03e162410003c2c9a4046810b8a028003403c60f919a51111410b081e2903803404803040841080c0441d58074980290410304c010743c821300584101540c030b04104500c641200201100213a156200a850141c00c09072850141c05018007001c8100d440b400013a40d50100d500391062014000a203017405d0501c0303204080d200381040b003000c0c450b008007800c081480f09420364460b50940120382070b1b00c00d000300074a5000b1005138400b03582820210540c446c2060007441170900b68024104000702c0c8102030131800148042d00402c0d074001014100064428500842e5801c6125140d2101020002007114482030f120883e0342445c102c5544812100d040b5000f03080da01d400d13204103007070030419011840c003c00d00300d5044c0302c25550820340041e003c0800c401c4d51131a1140ca50400306114105d404688100c00500141e070040c1c100034a080d0f0b40302e801401040e040403401e0000d966035000c0c4030412034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 302785341 1250 302784091 302784101
    0x70f17092e030b1c031107030305250b0408090d050a0b0406140912090a030501020d06080129100201110c0c090a091a090c0a030c090b0406150804030504230103 70
    0x4442c42d0412060035880c000c0b6504101c4110165240e240c0504100209480f5017142c8180484030420f03240722542c0e83c0790103050341d08182e0702e0060201301d03070303401c1402414001e540c100810707000100c090309034986440b070b10443d600200401c1d4210307140080605c00b040080010301619845243c140f00d0354503060400104442480fa00915101008428080107610000f8100710700040c14491a54074a4044001a441c400c4c69100903c13039400460105811241035114208442c1100c00a00c100c140d02c201c00c42c121120135803070201c4034415100d41c0d0300c182001940d0442582d8940000110084103002402e40d0f60040c412400c1503030b02c5002c1850141c10401d5805803c1040301e10144a40d50a40c0d850340201c088a80f90300000c01e01241c0018110a0104018030482d0f0002c0d06514130a0303120305010100141b94000c8442403418100360f55030034203040c811001207580c011b0a8050008580d1821109800003610071303030411006003c0032130041004500c2414065000c1c52001100c0c01000014059603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 302786591 1250 302785341 302785429
    0x31204090c0813031b020a03080a0305060a0501051c14040f05190f060506011202030702030d1a010c1707020405100501080a06061e18090b0a0803070f1709 68
    0x80200340030f001d1000e01d40d401d095040e540c141813040400c040318500141d003030342d0740328041c1d80214140000414018102c0c014030b4100c40990f010300807980c0309028407140c0d508030300c94180080e40400c100c0141065800403079074810800e59021600c4000c1048200c50440300361030584c0c00440032203590342005020001c014903140400c10440c0d60041c0f603103030b102d510640d00c41c01506031911800000c40581c17003007030304107542c032142003045441c3c2c2809a0000e5598000b40103042c1003a260159000805035031210405000038141e5600e160840a962540e40d20000002010725441c0d0512582005944a0140601c54010145803480040c41d0400041c21008080c103414076980ca4080c00f444401d40c0300768600b40a090606441482c2209004111580740801001c2e400c000d284207404188144103421150b1285400c035000405907449400017074903482150b0009041a021090310800540312211828002440314403a9050004000110303040c60038100e0008280f1860368504668111502e641c01c1c540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 302787841 1250 302786591 302786597
    0x1605031c02150403020c03061612020702121b040b09040b15010519031401140d0204020315030106031103061e1b160b0604050a0903081906150c0201080c0313060911031204090c 77
    0x99640c80140c10305108075082142c3d22f400240c018255103801c0018222011a00111041d41080c0c8883d1088051a030007410310a90804d42815800d18281000c030740502d410090903441070301c8076840f52400c1c02c4050000d5050001c24000c40b00704087d420001d0041003101d031008210940b008812841d2010b05800c90101160025840111034440b4049604502c0c1d040d5401613482d03e801e9040c0203250240818190b1560034544003000304401130540b0700710000148c084410507116018122401709003038400c0f11031000010b000440c0d2a130300395054084910303031104280c5080310400c46441f408048080a44825140c0f8051014a060512840d603114100c158100000840d03903600400300c500140280b013402001480d031142241c101d80c446401411861100c130500407003e000076011480001c0c1c140e0120712003500181c29911001c08a9116214010340c55208000c80d2b5140310041038100001ea40d01d50b09a0710342c1400d07880400a0001c41800341c4040c540f03803441c1030444000e5849090180c020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 302789091 1250 302787841 302787871
    0x1080f06062b08090409060b10030507050a08040c0302150306011206050d0204020327100c020a0308270706030f0e0114040213090506070503091605031c02150403020c0306 75
    0x4a02007900c049020503900716a0242000380760038850300e0f9000d60880c480d4060700c0c10311040100001640011b919000c10303100340c5006803041406034103c0d281110351002046080118403030042c030522032107038068421507000311035a88036008501741c4100051098000c000c00014071590f0342c0c001d155082c103105a2a41808003c1c284004190a0060814001d000e02d8010012510b00d102c810074200e052040040040c01c5c3c00c3e016032680d5500d8062509000781946440150a00640702042601a40340c040c4c0350dc51254491a120340c48018507800b020a045441483d000040c6605020343c400410704d594010820281d50130411085400c0d46d42d4003485617140c4818200c00c0311030324001c0399000d501111708022911417003180e0009804820802030240c0661030401101c1038011740594041c50000c3c041b40c40c2c20840f40c030b8454000c601402180d9165000024483e80740340a19184080c03042148141d8075401c030004072441c0700c12401d940803401b50b041613907020ba40f07023030401915034001d150000c500c078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 302790341 1250 302789091 302789119
    0x41506020715091505120a0603080f07110a09050720101e0c17180a12050904110919060c020f0103020c031c0e010c020309090403021501080f0606 64
    0x5a500014461607502e07090b0114401482c2c0d008280703c0c00140507081800b040e11441d030200602c19413043c03034100210003058002c60100e81803846800282d076840070040345094a0301501b000700c1d4204070360480d0070780024800b02050343c40d000c0683e4014903d0500100d61801c2400c00a080c12821030001c00342564a0890900c100c400000c00030385d03c800b00d0301c0c0054042102c418500c5250140008084003905100580204940c046850780c001000581c50040782e4903102001110200c160717001c118598400030103040440c44c125012002c44545041091030890600d01240c1a030341600700d07001c1d0454000c101003043d820408003451244110042e2512042e0a26201412455031114040d00030141d956240742c599000b54102c90051000c10200ea84904400c2082c601c203071210f10310b036481c040c103040d00300032810014001d01d010b00390550048c6051032600c1c0c00340a00158018000d030114442c0c201c6240d44120b00700c1140340078040020207003032003611340d07107600740b400c0c0010300454000c6c0052241342c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 302791591 1250 302790341 302790343
    0x80c0c07031101050c0609101505130b1c0f110102010e0601210b180f07060c020103021c02030906040c150804060f0e12070b0609012711071104150602 66
    0x41502d07401181c1c01030035003019004a525000e254488015442848203000c3c0100d00090281000700c0d2020f0140702c42d038100c0d8100200789005110b8aa0000d00c8043d070440c0c68071040c0c0060403800e1026002c100ea2101b81c0201003042c26800078145c076400c101d101c1603402e00c8000042001a117500b8002440105c0d08059802e41d07844052107210380c2c0c2e03144084460754603281e515500021a800450551490a0100000ae83c0c00e10b0b0500b00c40d02d92051003540c103441d400c003051050454140b5202c0c8021074a20360015406540a0000d00d400401d0345a861a840700f250b10103503000300155002040585054078040340350700c41c0ca4102c501100794120b50b03510b405622042a561095002d50003041c203485132001d074009000c0c001003109050089411068501110f80060004640500300040842d141c0c40180910504207018818210105954400c182940781004101401c1c3c3d43c0c0300095059503e000d030092513000003d0494102040440142540c40d050084180040a6241c1412035900d810381c06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 302792841 1250 302791591 302791603
    0xb03010f021806070f3305040c090c03110a0801031b03020604230d080310060327030203070c14150c0d1817070303020708030f040302043801080c0c 65
    0x20b61144100050303643c1000b80100141035140d500200310102a001a03801d030710038040000ba4101c04000e258a82041400a405243d000ea6001122046032604013028800a8010b220794001450388034140b455a000f205402040c42c0003060780c0d61100341d4110301c5e040a071030030b40a025100030501c0304010b0005d41c0d03c003400c0f2412602d803123810381c0080744910000b00f048881042e00c02d0f8810942c0000005202e04840114030a0100d040c2e04a0600e459010a0b001c80b058410701c07042c00140c6e4280006500e40181344452024040d00449090250503940d916030481c154100d520909924140303104641400c07864030315100600c024081c10b003131965024503a202000034200341081000c60110321012003181490000d000c07100c011401d054100480d407580c82e205071000b02c0051045000c0001e543c08040140d801c00107660030050320f401d14507001c01001d440c0010041040391040380c40d011003801e0402d546403440b101f5240c9031807000019000900140e00061400ea02500d08001b03080200e4004241 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 302794091 1250 302792841 302792887
    0x501050a2412020a0306031101020a0f0b070926010b04050103110108150d0302010203040b150d080309070e0702010903020f0721060e120d0b010c3f030b03010f02 71
    0x207503404006000c081121002d41151104880b5440010030502007941604064140e80c0a5403c0020790380800004a0703030380310310b06405460703006c5210085002686100c01190814018900641e800da02c07003040700e0045045080310a50003070b01880900c1d54590a0043c4110b0141c210390412003585540c544400c40050702c1c42190400441c2400541d00181143d0f2803250306002078840b80030207043d460301900070b61081c0c13010340c1c0c00142c00c0300080010000501c1c1a0010700c020308000e00300c803001d950321285904041c0c61080369009560000c40e42410801e072940c031444036540003046100d0582070107410001d4540c14043c2e01d400280c0e0901c1410341c140075110714070480b40c80c03004e41010349050020050500c9510340d1840c2c0260703a00c21515a4250000e4210802c1002c010403146026100554141405440040c00e804000c1584c1089002c18070004041e091340e0341e443d0342d000c4010400c04640b0071109402c0c90100e0741e2601000d80a0400748507040104001c10b03400c61800750070402c909000304102c44 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 302795341 1250 302794091 302794139
    0x608040804050f010c20091003020f060307020c0d210201060b030c0f13031110170f04051501090c091a12040215030c0a08060102151611060103080a02010501050a 71
    0x1003d00b000307900c540521043d403508020007008903810011a17034410040880309502c5020410041841c803000c03c14800d049960051646002a40d0f64003031040f02d8100409032000d5000b2826039641d192101084421002d10074080b1401c024914100b40f16003003000c07d407a204580c50440148070035000398040380c0c1c004824003d4591a04200d41c0946994401c11260109140004200004018035000f150455200845442a40042d51a0125101c080c40300306408000003010108012500c00088150003034000c0d8181e48821607050858007040c00d00782d0012060641d201c824580c0c2c141d00040d004090704903030311141035245c000c1c00d000b11103010306221031003200c40c054041821581c1c2c20704101d00412040003126205d24144100700420f42050000d4070200702001c0000e5804e40c800701e003c1400d129001071a130690b031501813211990300188101c203814800111000c0c0d104d20400c0004c00c0c0254440c404041d903c0c0d4004000a00b55101a44900d000d0102401c0034401c1206091050418820900c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 302796591 1250 302795341 302795359
    0x30b09070e0919020c1f060803030c090603060a090c08160c020f19050901141c08121b07200339060c0109110f13091407120c060804080405 61
    0xb45420024410044021450302c145607991604004014541016401b240810410a41c2d5001c1c201e4032407004a414103a140d030308120104880c600100510b4001d000503006010041e101c1e90700b00c04403510725940001044903c0c0420004405912184c02e9070a00342c034060451140d40d90205441142110180d0704c64141d4004480c120309c1000e07481d50090030f00801e000910f581d101544400340203100c40450003000f149040c001100500d0709880941940803080a1402d4200a0300190b00c5d031018003407000b00301d08400c0510300003007a040640f02290040248200626030700e2140000e01c0805028a4082c1d00f010b01c584c1180740300c4182d1044e002c480700d204410741080d01001d81c841c00e99401034141d80880045090f010100303055002c20762041c480d0803801500050041003100f40509840119806040280403405070602074001c0d1892620900956280301c0502c100141008185c0e0080a031a03090446640309001828009400502050a000003a401c02d5240c0d8030b0244203d0082d14001c075820 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 302797841 1250 302796591 302796631
    0xc092401141303080705060a0510031203060504020d060503010b03012013030f0606140901140d0f020d080304030f0c05070e06180a06080d140d0504020111010c030b09070e09 76
    0xa20446800c64880ea0b48554226220f14042c030494006000554251007a80c0008405d401c4900c00c2c20300442001002c007218600d5940d482e0b501c2000c0c0011903003051348850f4002041d480324005803007014059440807a0803401c20040c1402c45400315400b034801d81c1040410200107040c103142c0c0c09951110144583c0c2c03088401c981c212500394640c8010004440060000c00388802944910f0179034846640102005842202b040040c000a004280d40c0641e464402c5209180c034034551000244200b035130030f501c800030390000741c03200000650a69410030300204000415511451180c00015142400c1c5042c19080d12580c0c0ea540e141d00840c8800070910b00400e0090b903034052118a415002c1443c2c0d501071900c200c1d800b000c2c010902ca0011644074810160464602034900b68040304151403c04c0c1c2800715a0700e0280140c00c1c007030000d2341404041c9e24071081e5482e00303010b21002c1040c10f0f100401c440004205020703030514000c0c1540108071000740380107026a120381c1c50700c1e005000a03804c41c41415034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 302799091 1250 302797841 302797877
    0x2090f06070804331806030e1e030901080609040c03021302120702070f05030309010c110d08070606060f08060321090a0f0f0504020c030d050a0f06080c092401 70
    0x142e8101070300c030000044001d445010000020440100130200821050000490079245119031401000c000400e0610501c2a58800d40c060015004404203d800603041d8410b2400e00d40e04184480015402c005440c4030b25581012500780c126000b075901001a01e05070b110b4240e101c002e400300030311400c84480d82040d0720506406481d0341c901000e08040e400d0414140c0a9a0707001c181c8109404600c0ca00c900140500c1c000c0203940d0720b00c4e4103844502480740c6550b0754030300585800c840190b0220f030250311035000c03a20070805031071001e1084000045190400c007002d05210030440440040041e85410020b203924041848041a84840d001d10428845a460580c141c024442c0081d0400e5200303800140c0200c00101150441e98010703d00215942c941080c4400d900c1054480701c0c8030350007040040307107042d240e41c88103074800c0c4811000100c1110400624090f074103035510901c2c0381d6000490b0070304240f0300f0790b46082d0050000042c0c4e001c12001c100700d11860409602819060295910081f040c20803 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 302800341 1250 302799091 302799097
    0x515010e0c091f050d06050108070f0804050f03070c0801050a05060a0b09130219120c080402150c07030303020a200601091509060b2a0c13020705100f0f02090f060708 73
    0x102684aa0f100d02c602d580000c140c0d4008041c3c440c80303141400e400142a50140d00f08a01682080d9038001c08480395842c00d8071800c101a008840d03e210303804802e0074086c0c0c14005080464499a901881e40d032900d07180c2402e41d0703405001c0c1d022442c54002840941d54880400c0400c4440c00d044950f2191020000982e11080300d030801e4174564000100900880c3d443d65604450240c01d866890240702440c0002040303d003044c0030392020402d20310126015140200c5803a003588800c24202d4901908000b00608003c0250720407004a50046030310024a0b80240021095050310030351250b6160581c200c803a079034401031007044c9416a40701c04003d18248515000c101800040c0c900348000c503035030641081254030003903100040c1c011b9405070304031140c240c03503d849030380d04003800402904800c80308002c0d2565110000e6074001e5400c104c0c1c1000a0824040044250707030130240020f02070b006501c18410b41d08080e0303a007902d007441001203401c3c680e103401d440c041c41c1e44280d44281d1034400519105000f44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 302801591 1250 302800341 302800369
    0x9062a01230405032b1401030f0b09190c05040e15010e0901020d020441220911010e120712050a0f05070f210210021011070515010e0c09 60
    0x1078007501c010070b92071038065411145030b52178103000c00800c5240e0038540161042800300400861049841c2004a0351004d110341c4c014400500342c914110303154010b000c1903005140100ca100b511200c1c1000300d441c203441800c04110540f00608200c45850441c8043c0710814007604d20420300c0c0e40041840c0071001d60580d100c01c244080110354032030711041003407219440f40d0711044030f0341c0b089030ba07100c0b03945544580c880800c003088601c88000040f10042060200491030301c20701060340c1024500e00b4104c1401940034060044034041440c1c1204c42c0010013a40100019500503103030394070f101604070070001d43c50741141c841010240240e182441d0150400440343c0c805469101c41d240400d09001e800305080d01110000c5030081c0a82c0d03070711400307092a81c40c0305541881d40c1e8003550b8000054201484865490b42c0e81d881643c1c0b105624402c910110340c1d031004200005080450700004104003040340301d2042a0040900351590702d00b031003c0200f02001049400013002c080f958900390303101d204082d0080 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 302802841 1250 302801591 302801617
    0x7020d050708030d02180f030a030e030c21100c12180b0f070f0c0b0103230f0d030f020c07060c082802010b010806010806011409062a0123040503 64
    0x294031000e1300d01000e500540440a040d00c039001106a0311b141242d9180450725014000d843c01e15445d80701910901000d141c1d0941600800c4550b40460f030f1750300761030ba000c0f41d5450300700c8010308d21140c051440c000c84444090796161130074240e620000d40001c9501c1040103003032000f02e0704d82d800c00000040c2039503924008109413405821b03c5048492044040d11030b10306a80c6005451039140e0f4201c69861140340041d1a030207800300103002240c42d482d0250026003401284130b24145641030b0240ca0702400329002d9102d50404482844030030780c0740c001c0c207a481b82808020341c24444120080350701c80d8540c0c41800e0078040078200e41003c0103091350a940e40b43ca0109281c07580c81010464408081c006042940d005500c1c2c6070358001958000d00ca0b80e4051f05040e03452a91aa6402d401940da84203005180e40a102c2c09224508403640c80c90014030101c0c00c0075060800c140c1d640340d090846000c80f682c00902690400b4036002c160b50a0b1211615052170500000c505904d032403c0682c150b21401a0b41402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 302804091 1250 302802841 302802847
    0x8061818100f0b120d05030406020a020f070305030306040f06081b120a03031e20090a0306020f0904050c07031205060a080f070305120f04090c030209032a0a0b07020d05070803 77
    0x1042c2d00d5a0f101c860041025038100c07113485070800d64180c41c0d1240500602c040364051011801107039099018003902546401200c0004216541103868060654800c0729158000001c024441c105405000c90803016103009204fc1401d04c044641c840207540c1c0500300034030080c0098282541c40c50310301031601c1b00400c141d0b021003126080050181c10103800d00c40b030001a22110300c03a10005807060740450754001003071807400c1600c1c06e12142c041e48114441a4410030201300800451064401002c0a6408200c0b00b40c0c4d912204080c402692002020a0380f0386805008620200740c110300701c5000340c840c1c03840000c0d29a8070440003030080d1100d0740000e011407003142000c900d0400002410411b8a00941c12030b031155230300d00d00040441c80341c2480042e040200380800c20211069412068802c10242000b5080115000200b41741044052024400c4c540c0d41d000008004a412075a684a003800d88000d20320074288896072090380704200340240541d00c2c1401c0c400c03d110050000401604a400c26243c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 302805341 1250 302804091 302804111
    0x1030213030c060305150102030d090311030406020f06160903030f0c0b0106020a02010215101206060803220b030c2b0515040e010c02060f09030d060603020a0806181810 74
    0xe0006090040002017440c08010540c4580c0d6682e20b4840031205900451500d0721105125000c3c00300380f84202c0600203240360b03903442c011060010f003002c1c0000354001d0610300c0103066050328141010b46031202d2a0101068042150b51101d9248242d17034060070400d0f20300c5070703110301141e00389080765000d4032040c091000868007a40c08149040540d000740d0880300d00107280c804005c040041070b0341070002116807400030040080c14182010b01d03980a1100002d58541ea5400b060550f84201d8414a51000d801610700405201202c4200900b0031000c0703007070951800d2801804d10748166842000200c652106082035038075480c5c000f43c070400d0860410310175824940e0f0747d070807015914040b81d4071490510610042c00041441031460f0010564010708250f190500c0311407103108081c041141c240002c100f00605078285004104c0100802c0ea00140d407415808030042c400c6802401c0c4e0f6100e1210b04486800c902107181019800901c501809090910140d807802d1a040d0307500e024280707460401070703800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 302806591 1250 302805341 302805353
    0x3070203030708070b0a05061c05010f0504050d0f090b0a0318140304061106060303120c0c060708040c0e090a02060d241e06050f090d080304240b030c0f0103021303 72
    0x1c503c09105d012407040c40c1c0c460502c81c40c181c6604843c0d0783d4119035150703a03000c0c810324640c500a81c040d015000000300c0b002404505c9060b42c100702c406441c41d80c810510100501d620182104002c40a0320b02000b415060000e0025248100b2504d802050b440b81c0c5070300e905e201a0009407070f0043e1302010500200c00040410b50b01e03a041841071602080320460300700322008020a000b0f12650009001e1442c0c404c2c0e400c1036504207880035000b00c942041c10700a40607030301000c0103042d001d9075050302c410040346840d1402694810198114041544074030091200b031650000305801d6482c1d0484075580c40c2d0744400c42030703402003000d5801034400b062410503003a1341e881000068000d07100130001811981c417182400c14020002c51185200240301002004048594800601301c200e038000d20507010ba011700e48800440c0c0d042980d06681c800c010f0940701d408440b8581c4200d100c41350b1030ba41032003000f0002e40001d03110105c0c13145890090200c6e4007001c020b80c0c4260704a42c0d60007030700000780700301d01c0e1281851 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 302807841 1250 302806591 302806597
    0x30908090904030e030c030111031618060206091e060f04060f0c03021309060503070b071106030109050601020706030c051b010e011b09080a150902040b04020d0b03070f060206071103070203030708 86
    0x26030700a0107200b424020b10305040c00b07000509e040700c0d50400d1071625001304c211407c149442d814810011003481482c1c2118802f4030070740013400194020000303408d04004403414048262150804041003400d455660740001c00c00c0c1c3e078402c180d00005020742d84c0b1414403902600d050250a102c2130329181d0000075550701030707002d09041200030600c608165214000c080444d00b8034020294903901c00c070320400248041074018821944604004140c0411180200381190402e8010042e840c0d1035070100410340d42d04014030001800c1e240380c14004c480c0869800f400c540325007941d00d1000c81940d08024000002500030790035a0346000001c20800c85003403d50308060614001140000302e810100207062000007a12440c00d0381c00c01d64807070f06550005501d038020070036010100d070002d840394081645503485201900c0c80440510022030000f10010405081c40c6c0680c0080c9054404200148541a400610a0781c0481c01c0d00b080c11688003070560007851402940d200a500d0311001800404000d500809 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 302809091 1250 302807841 302807867
    0x140112030e0d0209131707171b070e06011701051003020c42060306130203010f0518010e03070f0609030c1407060314162709020306150c0d03090809090403 68
    0xc0040c04452034071011b0a501c00e460b0301070701444039403e07440268840340d4018404800900c02c480003032058610b416040034407550103803108000032003c1041c1960040d0243e01040c00d04e402100166040c5000509000742c03914204007003550100d0214140d14040000054940c401d54400010783c846480d810030000e4208000f076000c030201d1030350454046c08104134600038034008010b043e9581d101c100c40d0381c582000c02800c0e40c2c50340d201c1405820704480e51049901a405d520990fa486a2101032100d0a4510014560300d03144c1c001c0117504003052074800b0002045500400208900c13406040890711501c0c81180075205101c0010407500410000629100b291a01c2c0c43c00c0c84460340e8a0402400004101c85008108400d00c0320001024402d90b40d4142c0c2c0c01c80089800c030002c0005600e5a966040d582042c0c0b042c9a0020500016150a1903800601c0c5440c0720024038044000003400c2d01c5111001c002c0c0103140e11581c4e4603040103550003c0e2a625000a40140c10f60320785414000c1c49840354801d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 302810341 1250 302809091 302809103
    0x50a2909010c0e0a0f0612020f03090c100c0209130609080c0a020405070f020a020d080d0608010207060f11160c1502010203040c05010809070608060a09090312140112030e0d020913 79
    0x7600f1450b007006a07101046030b03150b403c0c0207100c43c0b178140e0070b40d50740745001303501282d0603400c00c1001450051000954000c0d00c03074030003c02d040344100d0240484901040343d81001e018501180d01d0050340c0d04201164408820003942d510207440d41340c8a406030460300701c02490300c0d00100c0c401c00d41100000745c07000c040f802180e0034030998583c84819076092b9071105a600058010102507000360404501850a00344244100c41c40d080c0751040300022100550007030f02ca6a500082e8480034042c40c0c2c0100600341341036410410552500c050160410701c103a070f44400002e0642c104c1c910500c545082d0190041038070302d10041d600a001c59000b0300075482280e040303c50702c0700280013260b254803070400d080c41025000010301d19507081503020b80d25008010b0800b0360202d40b003440800e070380595018a840461207501d801130103071108c42e064000d030382040c1921403424030b102004001510140903854110703505800c101d26281190b10228a801d05080070180d0421070000c140206d50610301c40d4030341001e001d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 302811591 1250 302810341 302810357
    0x309120d080c031b090a050a0b0702040614030304170304030506040b0f070207030203060606090f03150f010e06010504120203031b061602030310030b060a090603110907020a050a2909010c 82
    0x102c1c000d1503500065a9002003101241040302c026006100280300000005010000e00e81e91600045c901c1242138000b121910008075110b011401e290050b04098241c800710760b50300d10700d80008a603880c00745100b81c194103035883c01e100d952100c080c01101d0180d030b0080c0a41d07000b132030a401e219003101c2c0155003101e410b48524000640c541d2000c1240401c1d00d50050181c800c03515007908100c9a60084c0c2d03002da03400000344004c00d2555a0400030403141e50001c0d2006a924904110b0303080308240140d0100300c2c1c07010380c0810070800703030381c458121003c0d640303018840500350085001080c69402800c480f00317500f0020150b05072007000001034a501c500c10004828000c1300d41c84900320b89034007042c0d039428601c0c4440f08051000845000040d6400b502c06040c942c50a6681c41001c804d403001d690084d244030311022034454a03800d00340f807040e40c408000d0000388050142da5a41544c1d0f03440c0308001400700c8000c400c000003101c035400200240f40c1461000955075041c04008580200b03035525108020801c070b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 302812841 1250 302811591 302811601
    0x3020901110f0a030302130506030411030c01170c1b030a1e03060605040e0c1c05011e05010f0806040b0406030b0f0a06030f0b090309102111040b07050309120d08 71
    0x20b00c400310101940081c100d100074994041d4040d401a2002c06100349085202066580b01c14000d94032941c0101002401c404251050500340007480c3c80541c10000540c06a058181404003900d4000c04003845a5580b01f005485a8207400d05071186c0d100640000540e035514560b1204401e64a07450346d4484480800c44c2d10030503000c403507071880f6480208000784402c01540e001c50302c1e030aa004140c0304407180ba101d058065038942032813440361543c7c01503a8000620828450112150445d40840c00000c842e40c11300c800604010000054402002800e00c00140d040d11035070001030803c503014000b0f0103110344900e0b100c030130032001321658445c00390b20707400080740e58506010720000c4a410145800f00c403140e544030300d07001010080050125200070882031006403078145e020a241c411503982c1191408480714071030140103450603c03115032400c15000c0c140210110303046a049a9102c5200350b900c803c640303055400c41c05129141580400d030500c0140c1c080002085680e42e004043c0e171206895607803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 302814091 1250 302812841 302812843
    0x41e021203090a0803040503120d06030204240503070e0a02070303060506030106120509120906070309030b10140108190c020c04020c0d0206130f02010e0409121d0a2d150302090111 79
    0x2452254548c10b61001c00300482c401403080080c003030505910000f00d80c051302c940110341600d10411005d101d04005020210b0040d1040100720050308044000d0719041e4604112030290302405481a02d283c1d42c00690b031030070903000e50f10040046c480684443c0e1250f0355500050075034441801c023000d0b00ca082900080f415280071481140e12007400c0300701c4d400c1c030303510344240a816000168110284041000c0120105064101e800d2180c0e100007004904c5509120282d0502000b003146d9a060183c100700740301e103100304000c00f02d14003000e60300001110742204004920742245140110382141c4000b4481e010400f000c034200300907130382d10307000ca84494482042928441006400281011142038110001984500098190b41d4001000440e000180351902c010100702030140ca00410a10300c50102002d00c9101d407109550000c4a41102d00381c9082c09190a00c600130703015900c4607940004410b001140007000e07401400b4618922202185441d0010b4000d50041c01c0250100d950624a00d04901d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 302815341 1250 302814091 302814097
    0x30606080906010b13090527150a020d0b13090b1308040303030506060f130302011d0307090506120a05010603021f1b1113061a0306010206041e021203090a0803 70
    0x1032001d0003404103a03c0c040c00c540707041c1c200c03000f0705d54031030388000000506000a02410b802151851015803145001140070340c0f41401201e0340c0c00c04e5810100c400810740101c0b184040d88007a4400c4007503501c14903003000c3e1000b40001e9094903804521210400144e17a0030b030b07108020140c0303c2c07401da50030740d05c810308184451113641900429250041000340000b0748a600300c250001130241289007050302c2079880408c5500240c03150f500798248039104005541c0c1c4010700caa20032440d05400014801940003003911000c1c0d6000f400c54590f22540401c1300f070f4540081c0950b102001c8030a403003190003e4030381240a880e89200c00c0c0d100c0e07420020641985c2000c070768803145014041e05c0710408011084121707170903810744640903070b18455942c5254010f500c4100311442c078085901000100a0b060040001500d02c00f03209a00e007000050042001c9070741c0000d80f56811a80040b44442e5041c540c084c002c1c1c1d40c42101900a422082101c0542c03030030040000038014095085400511940e01d0b40e03641541c1c0c1c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 302816591 1250 302815341 302815351
    0xf120203100b041524050918040203030405120d0905030c370b041802130e101802030703140402010e0d05010e013806070305180d110103060608 63
    0x5040078645540c003103034651045500c40400307032020911a50101c0009109446a4010306241000040500060450203141507654405060981c281851500441c01030f10b0f0441c403440350380500340c01250941d5000c1098400620b8001d100c2da03030003101e402810b911845500310384404240001d00c040b0785454046504540168081e0060030004146000003211840c000040a074881e6110400c41d40c0068070810309002d05010f02005544034900718002040e8410100480d040310700c18040d2558040b0202c8403041200d0003001c503000e45032640d503000e00f00880560f1060718880100040e20183c41250b40140d4898070103500c080001c0441480c0300440300d10200c0300240002d180c416009000c2c40c200c1c10400c015070182c0000a056151144424210b401190000400030803100e81021481860403200e425a803803040c2c042014810403010554034020004028107010011a0400c0c1c2c03000d818401860903200100000301034503442c14014041150268081d0000e81490000704849005001c414011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 302817841 1250 302816591 302816593
    0x1306051207030f11240a0e09010b2a0d030504060c0c050c0103020a050d0608070302090903040312050706020c0a0b150a0e0612240702150603060402211005010f120203 73
    0xb0f00c1d5a68801c04200c4161105030700c1400144180f50048246000c10407040c446004280e4407aa0316102a045408100040d8441c07a03084006020251100c81030b11503000c91100780700222045007101030400c106510465000d842504082414254190440d42c042d81c040c0500b0070550041344804c8641e00107001d00a000d0740d0200301400c0c1194465402041502c02600e00b89051011000e80d40c001c0d00d006a105082c15400200188294640100303200d41110002d0000e515051450b600c803203e1f50001e9880009002000c1201024040d407a01100c141003040025100000280e2506011004058a8810000c103400410600d40e041403130703d550540e1103940342d43c0b8042d518a410006100d00e80c040703e504500070700003170000b0315007032002e5000352440115111005280901c4002d262000c10400444946071034002d100e1981c4020a0781030b08150181d40745250340d015428502c007210480380303105006103d0449542c03c84840d0303500c100e041c2d41003400441c81c0203a42e070404c042107200c1c091000e949 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 302819091 1250 302817841 302817863
    0x1e03030708271f0210060803030a2301030f03120f0e06060103060b2d03161409012a080a020322080d0503041403070303050604051e24130605120703 65
    0x2000c3d809140120002c1076204503604508a400768030300742c60700b80e03000030819440881803180c180d02500440f28000080300342d0100100711002603111845042c0b201a002038800c000540a042c0704500440030080d095130f09001400d4a5547c400040c8421a1020420701450000c201950302ca4003609003200c5e840c0301c1e55414a11146111015142c08000c0009a854028102800155510b014600c0351103000b034141002030580c1c80140110f40d0306548000a00e004001c0c8440300da0300030851007280200c0c1d081501c2c2c0c40c0d502c01558a0100001c0c040540880f0001c02e2034013075158004020602105800305005645c0c03800c402031042c43c00d05000f0801c3d503811401c00c0c1c5110a00c2480075542c02030103060040c00300c0036003c42083c213651240300143c00080e01e400400c401400c040c0942904507007280c2e81d03084402180e01c6125070785203024124070111020485e00028200d280102c4800210005182070490425150710348020406031107028007900b5504440f0104080100c4ca00342181d4000087d404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 302820341 1250 302819091 302819119
    0x16050f0f030d0e010e0f010507020717060109091e2003010e0303070c1e0308010e010e13081c15030204060b0f0f0d020c03120a291e0303070827 63
    0x381c8940b443d101c1640d96130700c1c001c0c400c41c00f04200081485808000024282c1091000203003010083e070040d10800f0b50385000d01c03140b1540002c0701d9044556103540000c240443d0710300150110729201178680741d42403000e2040c05000d503180b200e01c0701141761301061400603e4042030500385e82c20514a000241c04c28400030f03240030701517403500c1001c3c0d01c61030301d444c0380c0e80f01d42020300b10000307101e50b094000980a40041c002e49802000720b0b40034160400801100340b03080d1040c0521804c00700c00003401c0300008030f074854190b00d0140c8045040310307490206025403847c84020710125071041c401030b442103017001800125040104100c404041d9444c1c0da2034903045e82030044010f02d921a900300501280c0c20050461402400d2024100004603022015072a00304841c121007130b00c0030800c108a5202c4111402c4414401d600d0420210340c0c0305440c1ca05a4040d03e90020b110002d20441d000d4041c000001c0c10310801805070700070a480c15003810002d40d41c00303941d010103a081c00c0300e0003155080b1500034000a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 302821591 1250 302820341 302820367
    0x1b0715081303181d0114060901180803180301050604090c1401050f0a050c07080f0c0909013c050601120f06080f0c011710050d061116050f0f03 63
    0x301458000e0505100e800010f2464550003000c95020a0b11690034803c4d44d00c4007048032003602d0042481800e0f185510b29041c000680300c0c0f058002d032505000d06905900000480407108000400540c1c0541340c48580d2442c3c0345030304c000858640c501c04e5203071100168561802d8410f1a50762a0011502c0003282d081c00040f0410a02e65104c9505000b020700080c010065528003e02e003180142e5213040d20b480e074568600345040b005801021068000340f40700d5403030b444001907442020104854103402da0f03c0e14103043e40100000c24070100a04000c000a50b140f4550401000c850441101c00c4c0303a00c40456004d140c1203402c2a11071500159140585503048880c3d0b800c00441408070780130024000e0b80e1590028581902c207000c0003082c1d00401442403c56030000c5a107203500a01994200d02881d04013201031035091039001d25442190f608100105110b6154449003c0f00220b001c1e00360b46000e54a4505840801d9980403a11840f0b00c54100e0307200d19001c22200152014180118105041d9030720707036 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 302822841 1250 302821591 302821621
    0xa0315031a0a020c01050114010e0904200a090c03020a1106010e060409031707090623031f120b040209011202031209030f12030906060d080a0c11061b071508 69
    0x4840c4143d024000160b10307440a20410b0f00a10b520781c1582e00208c044030002d00319140203419607102d82000020040420b07607210f2050041d5250324102c01a461b1800c000400c00d481035000381106600d019800c45600b509640141025201601c46042e5160044400341d55100c00f4051421510313884000714409052035000810805c1c0701703040a02e10400c0700343c50b140740c0c042c00302c50540014007151420003d4a4110703541200c9030760285068401c1c81649030702800307140720240201c0c820480203043c6060720603c8036800390241c81c03d00b00240741a1024103141c42c102101b520203a101d6154880002204803070401c40e28952a400350280401e64001d55401186411000b4419018003402c0c12000001d5010311411610701940c0b0b85032a1070f81080ca07c00da03d803100090100d40642800103900021424000590f1404c022742d1809102844281c41e1665107040c0c0c1d40d04454000e48040361140c10b58030320840344042c0302c144030200c0d060b4507550348a1540c84030781011040045084607011541c1441007500d5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 302824091 1250 302822841 302822851
    0x406080d1d0103020c060a0615020703051b030307080f0c0c09150d080c0703080c1005101a090901090c0215100513060509040f030e0a0501171f0b0a0315031a 69
    0x10043c05e10140450700b03403d224040b2020131070542d45d180180b02c1c1024007001e400620700c00d03200408802d825652003a50302e29001c6407000d5103001a00c400301059404104492440f0b50110b08071780c454140c1c1040c640990410707203004001c2c0c02400d10000d00c03424016202c910603110b41c0e034400400c0741341c03806000050041c12010b0707401d04810400d03802408030802c848002540700e0388445907140240c0c50400d0608061004035200d060901d0180846c806903030480000b5031343e003402e0001e03c2c41c240085c0440548109804030b600159501c0000800000691001d00500300300c3e00ae0ba1050180402050528101123401a030300c8843c402c0103000310b00302040d039221218401580002c800c0c2d1600d0003c2e49104080300c00326542040340b5064400c15511000780e0480000558080c610242001d0003c0c095210f00c03100381021014040005070520b4004240288052102c092004104c2d1110311000d1103034041a0600d003c24200700749a0440d01b20711400d402265000f01c000c1103d00d122003280d029901c1e01800b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 302825341 1250 302824091 302824097
    0x2160605090a0b032802121b04030203120c0d0f1b021903060b1e0102030913090b0a050a0b060c120a050d2c032107020307080403110406080d1d01 64
    0x40041030641104000f0340c0100032055000ca115841905c0d1452440c42c00101214090300602007090600074074400c02d50000d68041c4401c28102d81c2d03001401c500d000ba075001a60510070040c02e010f104400310010000c1c1c42c455025075903000c1003c501a00d4046184184c200041c10149213282e4a10305100d10700c00c410b00c0103101c00c0e00500c0c052421525941e05c0c0e003090f5803042d654a80560140b609115900c13001ca011a071502d8001000700010b1b44901952503101e00a00740500b4980072002640d01141109a000d107030355003142000412040248400c030361103240d0314034016050019140000a855441910381c006282c60303054031440780c480750444901141406414491300c1e03602001c0340034818060300703e5a04441c0115030018200200d030a25006005e4541042100350310140014070f808034000101c865400c1c87c0e4489241c03c07491803040c1d0310301512103507010401104000d07182d00300303400348441101c0c1408507540b121030190311462140100d00111380307001450005852413890419200324141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 302826591 1250 302825341 302825359
    0x40506030a1106121503010e070f030312020f030708060901360b10020f120708030f06130f09050d09080a1103010f0f0c080c16020909120a020a050c010216060509 71
    0x1900c4454038850a030391440724103c03007110145e4241003d209030483d40620800500341503207080764003041c642c55808003030308003c0000d500c100d1400c420303011943c1c6542094243c56a910746801d0041c640801a130300a803040c000d0b10000101030f1103290380000d094052019100e1082d035a1030741e90b41c18070304d80c84840c0380550b25800c0c40c0c80380e5607864100c60301c40d102c29000b5001e0304003d504858100014880c5441098506001e0400403540c0d000c02e0b6a4820650800141103803945000100c0f030f61031440c01c2c00b10b01800d10380c80c1c82c501101a0400d651551060702203036404078081c0829645442c050280c01600d5004a4402c00480c443c5d0071491004600940002050b4040d00c44100c25240b0305801905020788601a8040655000140d9580700030346d1606941032651030311010159000b40803001c3c2c8601e204901240040c3c00502000ca941c122804030f0666407042e005001e525030b4144c9c407042d15507000303e05012010b540045084c4001c1d08506038010710b01c90608800341d42a801c40ca07c1a600b0041c4a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 302827841 1250 302826591 302826607
    0x909030a1d1c0f0b01080d050901030c0e03061906120f0f11060f030414060c0f1809090106050a08010b010915021504031e020a020f060318120a0e040506030a1106 71
    0x40c800b40899014106060009816050015404d00180d000300700a03808110710150f4164810f0030303200c1c4000b0900e4085034600e0101c408681b103104001c80d581d0303d801a203003405207007003c5c3c507820001d2045502c014400c2d0f0741e0f140c0c5000c440345000c00010740702001903152400040d01001d81031900740e204c1d400c030886d250807410100d40107801410030a803070710038004140014000e8108803c03642d090100020040c1c1d15181c2001d4005004a0070004407007071020680c901c441c1d2460a480c0788074078015200c003020b07141031035506010701881d124242c0203c141d08800300e50000d0600078008545410b03140c1d030a00f0780c6071820b008220201d01c10420f0031030141900f5201c15550714500d80340110302075565107c4195801104000c0b080050300058159800b1214400c016200c1c08070340140c5030011103151351240c2c0e40c400c0074951251507102402c0d25014003980700b104928104090b058030802d695030000188606c106020444601352040b40c0c0c1984412031400c001041c004045c501c61501a150798100b8501d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 302829091 1250 302827841 302827879
    0x9051008010903051809060a060302180d0f1110050306090703060504050702280203060f07180305030304110f090402040906020c01020c0601051309030807080a180b060909030a1d 78
    0x302ca9402c400103100000c1ca000200d001042c1155800002c9a0f0f0814905150700020941c140d68483c0c0c006250b00820819000c0b4584c20f04504401d102610361401100186000c203540002014111500c4200700080919410b00d841c1c0010861031985409146445160800802d840020600c1c010561a90008150303a1240d020b203e01492840e0001d08910702088481074402f00300030000310a50194405080160b54001612500316260400814494460308011a85c1c1c1403a11040300c150011070b1000010400c00000643c0319a001c0d0640c801c905c03040c00c0c100402070b55502480ca5110615801190246c5041d921042d1a01d10803000140350400f81d00c442400e80e00b00c20f804040d103800c8030004000781d040140c0308044020b5203440c01c21800e0714582e0060002c0e1809801d03081000300c244000f5a584003558000c010300c03104a01d01182402c2d0320328049000c0760003214490300038060322006c902c0784140001034520030180f40e1105581e418280f501511a840c0d45110f150b41700c00e007a0807074884000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 302830341 1250 302829091 302829101
    0x60903030203041202060618090c0a060503070306080601031203020d090c08010209040e0d08160e130606030c18060c1109040503090909031908090a0b010f08120f03010905100801 78
    0x4826240541c8a141030700b06010f20300c0b00000315906640200c2d003081500c1d80d410402450002d240b0b007410409071505400d203032504203080c1c017440c0c200c03400107000b0072065006400f4500c00c00340c1d9a4184902d0f41c40c1c102c181d031221020701c070080c000401d00415028107400303900a481030644446000807210b042d5144e801d5112171550002c645658005240000c509040c01295000059400140726004a1840c010100600109842081001300e8150a03d1a00c2a0710500d030300c5000400c403c001d0012210008001d000910803880482e1070714000604440c01400460344080e500504203a09a20741041039a400c071908108032610001e544500c04c80341e0391500d203140198042e10003143c5499042003400700b0000090010252130f4002d2200f1814402555181250100980707801249900c0e0000010300d04080c01c1401025185c0d00f00000c1102240c082d00b1400b150f0a000468a4007140324150140d10f1080310b02011810303104100600026040390011034001d86980c291001099550300c4403400c5031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 302831591 1250 302830341 302830343
    0x305060c0a0e0a0b0d0c030b0618010903080c0c090133031d030705010513121b020907081f0e010504050606130303020a03300e0102090319021003020c0a0312090609 72
    0x280400d505c00700400520918040300403504041181c0101d03000025454040c11080d0720750303000d07078001d50b02c01c90744a81d0003440116804124a41c650440b044040d850b915541a201c0c02154a00c0002a5002041c281844805240400100003030101e041c01c8041c070100f001e02105240c4ca4802a04d42c10981942a124075550803001d16140c24507403410f0390a407036020302940c990f4540480c0d49000701c1d001015a1451640074105440c4041c07205441905003c1083e4010b5070150141080002190708840c0692040e141202258614010040002e00d0703030110b03018a40500008600502c10360410398007282c7c1050f0000c110170308003c0c101440d2a504826030b0030440c016045440c0710000c05820020361015010501d80b408184042140e8203221004a0700000c2d416544a2007000e105080030340c1210034041c005025070b0030584c000200d16949590070034040340601e0150510340e2a4910900c2075030b80754160440a8100c4911039182201c40c206d008140f40c0b20f45030359a2070800003c4092050030221 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 302832841 1250 302831591 302831609
    0x41503062408370803100e130b0619030c090c0e01051c09120504051206130807150c080a0c02060903041e0e0106030b12070305060c0a0e0a 61
    0x80303007601040340480800965440304420307000c2c00b10382c00118140b14440c500a00c148450b042c02070110030301510001d00c00312070380d06400d1008184a240c1c0000c512481b000700c003141000b40c1d40e9141207900c0108558084204541144000000b040e07044034640040000300041441811640500702c00040d0341c0c0304695803031541e803081041590398000c0d030914081a0810300d64481f041c0002901c14803900308144010f415058030141c03841001d070f0029594942003070141d20440401c2001030601e61160003034621030020300010340c8080e400017030003903ca207400c1d00390280c00c3c0d000c598070082d26030800001202c80f411113101000e103c20003480f5404105040ba42c8140090400349020301c200c3d03180464240840d04560100110303102c5c0041141e04540d08407444404000b0a0400f5520742030b880e030000110000707160300028032254150052008004101d444454070750380d9000299940c0b0042c44020302c035422440028a01d07444080240c105074841d4100180740a906100195040000e90012151 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 302834091 1250 302832841 302832851
    0x21204091d031b07120206190c05070b0c01200a080405100e010b090903070b01060f02030702040608070509010b04240c02040c0801090c03140402060f16080c120a0f030b04150306 78
    0x43d01c5020815a03004000c4216102074800c9980c0100e10b1512130303003080700c19010150001005452181c8045e40041d5040000d4a40464a6901061a6500904107001030b1740c00c04c0f100851001f41c1e0000803c08200041045140c19422201564202c3c4014000c0ea400e000f01d0614500d07030348a50086040c01040040005040042042088802c68010b41100d000303600500c00003000684117540503040d00d040341004120400800c204915602c15100029007181c1000c3c0006180d03400041c2910070380c0c50449140120341c1e2070b40d01c2240c03240031314896242030700b10040c420fa04001e0903c04064610703440e0710b41404032810f507401060580c2d01d4040c410000030900c80c0100100000c51140030300b8501185800d121241c00010007044407400500080d211300c1c0c0002c3d6405101d500c810840d0f80342d600c410f00982c40f080e014104940c050700031025100450140c1c08141340b0002d0001c04407502c2074403548801940e540502c50440003020a00c0045e500541d40348201a24007804000f1400194820000418 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 302835341 1250 302834091 302834137
    0x70209040f06140f07030e030408011103100801020702010210020d060905090a3522080303042612100b1614010603020a12080904020301030f020907021204091d03 71
    0x864030064040d16443d50600140404220a40c1000e504022a45000f040005e002e20a10f410341c410340d8003105039986041e0300e006100340001301a51090018101469007180c1e940000e500341e2041c0741c0d00070300513001484a003803105002e41c0a80180d5000c0c0344002103854450782180210344e03007030704c4007486c99000b2a064010007101405001c0b200040000c900d54400c1c0a003025443d00407680c900d001008404140925104080c00c4903600098220300c00001c05135450300f91b01d4072a80155001e4034158103982c1c078002003a0082e561a4590044029040c0c50042401c0c222084200c0c044d007461b80d4904080c0c5d0014591119801900b91001d072110800c481d011146481c1813090148030b07070480c003641862810805681d0760001c0380200d0380d20f044504500200341c9880d071000c2c031a000b03039280e0161022002009200314001c418030380ca4820ba9403075100d0348413080140d070380e460062400881c00804000070300c6084030300d422102074800c20070103e03c80109180141800c60308003c4985c0c03822894030000b01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 302836591 1250 302835341 302835353
    0x18051005090f041a0111121206120a0302100c110f0c190f06030504020a03050106030b010302090705091509010203070206030a2a0203090d030e06190e041a1302070209040f 75
    0x600c0358401110100016080113405400c00d4034141d1a40d4188003103001c0c20300b042c0030240040c1c010119004182560340b0408550b18031a060b0076a4800d00581d0f48000c13404c1032060008a009150350540c000306040102c080c1341c00007812114440324200f00d000d00392401101800c1181022003a090009421514860800c0c0500d05d80360507a9a0b4030b48090703400801010001d5040340c0291740fa58580030615039142d001040f03404465a000501d40d41c0307811800402e0241305052a0706a0780300319182082a160101c088529000d00c0c944c1c554000b6140b03c070708201110140080c4440c00e01801601d04000c00c1d0340009405030402c42e50403086684405140301903668904070032034070070161180381d00113004200009599000303800205001e000810900704c00c0c54069209100d407600003c0a4503a1962503000005a880ea100040c8006c19600105600c85203003a0160381c003031442e02a018543c610700c0a0410600c040c41d0310f5401140e582c00c01402e80540c0742c00981c0ca108500682d8804100301140c07a101c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 302837841 1250 302836591 302836609
    0x20d060e070323270a150e1e010e0d0c0203010c0201111e0d05011203080f0108150c0c0321060a030317060301110c0c012303071805100509 61
    0x1e90201440c201d101c862003074115200d0403160104150300c1400b80e0700d19005101800003091a503d012035403610007500c048000400341d810620036444a10a204ca41d410078040da040e240c4040210b170449101082110389528008c00140321510000c0740350480d0180c2c490504450001d0000090001c03401e200650609000381c54403131701d0501c020000c00342259003000050246015500aa02c5034030340c500c0300c0528000035694a00000d500400195075a9400002c0700043c420086020510580000309410102c607107480c1215008405060840413140005000d043d00800902d004a01840300040c0c0410820203040c3c244c994074907010401514542d180d403034980c028441c0c1c1c4640c03000c04007400043d038040f5280d00404000004038030140c54002c0003901404482503c22050303040400d444903030240014180f14072900c280c8911821140c60b440c500444004040360280281d03003003011604261041c084220b4400d01c0304441d81c28145c0b110002905010343d0794541c0300203100071071052071915098180c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 302839091 1250 302837841 302837851
    0x120d0c02070b0f12041401050c0306130b060405130e1c141603120e0a0804050a08010b030a0201110a080f0d06060302210c0403020607050a031116030b04080409020d060e 74
    0x102c0c03810001d41000f41034880c45200031a5255640a00c0880c0821801e0154107160300c181000a10440c40c04280d0344519800413541244204880c0b01c515284d0601441082d50350b40340600342a01d42801e1000340321440c1008021242c2c04c41d0784005403452860144504144688204090b00181480c0c4070000c02d103402000022003c48001c10840868844043c1021030b1070b589801c2c034030408000c00007050010000c108803401d02d4092628142c04100200307000f04117444084891020294540088608884143c0001074069001354202d2015601861640ca40e4001440856204001c0b035031b107918854201080040215101141c0e040c1002c01c5c5020383c4c40034240c1890114103003003000011480d101b10544042d00c00e250074002040229031044201c40107960041c066030381e9601c507841d0240d9552582102900011b000a50545402d200426901c402802111000e2240c50850f202c09000440c083e20403a4810300c10800040d4060190000e0180c120000100094042c03404c081c1c10403000000704 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 302840341 1250 302839091 302839109
    0x10801051e060f010504080d020d030e0102070f0602090616031107050f03060a1d0a1a060d0b010b0c0106051c0210110a03030b0402090a17010c03060b0708030603120d0c0207 76
    0x80c000d8801d52008101d038480c5084030301c08100040600165481d1085812500b0769000b00390042601e81e4001030034110f901401d1340c04112078041200300c0c900302e01518400400c182c40c810484400704403150081d1190340300080450703103000f110410b0041b80300c00c0301c0c07000c070040b90080002800348441171001e00700030b000c1620400c0d00510070800081d00c0310002000105850380d103d00ca2010464400f1008202d08200030454142c12040d04140d101c0003040b01c1a030302081c201400042c21401c2100c1c9404140d03a202100e0070050742441b03d170518035008101050002e651741c1c100080d65030b4a08070310b8901ca031603c0503c04507500300c40c01401803034108607003034105000c04464070202c4400e000580d805290b40500d00050114000e01c0080d020388640316226521100034040800d0480c000c2490341e509503d54030007000070b41c10020041d000e0303421900c585948003c040c801d00000c280030760000c580c0074500406840b04240c1c00040000d9541200f204004025681e03e19012282e40400c191005000015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 302841591 1250 302840341 302840371
    0x11409040b01032406080f010501090b0303190228050d0305040209150d050303010e0108070614090409020f0904060b100e0a26060a1512030c060510091401080105 71
    0x40c0341c842485806100041501d2820b64a03a14000c3d00d54003d010310351091003040c440d065031460f10903511030b44014050b07650b5203803000025078030103248070303192030860b0103400f035402c0c026030910321060036070008032480070741c05500c004040e4141e0140088a601c119003103000008000f904043d8541110381c41150181031406c4240005070f81d0f651025948000c1080b007021480450030041070380c075080c41c80002c1440c8030200020984908415400341070710800b4040b1034071290f9803c1c007101d24448400f41e94030025001c0005148904080c4c000c1e1041f140082c2041c5d526101a0000c0349840c80100c80a9078042e6580030b07203050a160011046040904a01d8038504090341d800004210210910070008400c10041e144020781e0103000280140c2041c0c01d05840f03803440c0401400d005480080801c0ca4401e22545012440d0000c003540d00b1082030301076481d200d1421060360303110f000341400341040010781800c2c1b00005942a041c047c2d008a40011300c00300d0915458524001d0035950b000d0402c2c1d0003ca000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 302842841 1250 302841591 302841593
    0x12050a020a1115010e06030c0d0503031e070e15040806090106030c09090c0509070c0803090312010b0307020d0809070503030409020d06050105071203091505010e180607021f0b040903020601140904 86
    0x3c0c0b114941591580b000300c1e182510b6001c0042d01d405000f18407650054401c14054007404000310103540700f165524203207020450f02e40080d0a450000301d6142000c61406d000381202e60070581e030404200304041191515040c0c50348805450542d04444405c81a03440d404213008002480148900402c0400c0c4140510301c2035658101c8044200d00900b0b004e040c0a0b00084c0d2108d2040e1070080d00703650000c0001d0b41c3c80c180803c40ca40c030b80d80130b064400c54150000c00005648820b040c05c4034420600360340940507042c413800084911140103007852000d44195800414aa0360510040000303000c3c0c440016540c4041c104080c05854059006e107060120031b00009010948032801c142c682022454001501d18862034222011409100c6407409145000d00101c1c3c540c40c20071581707000d003c80c0c040c205407105000d0342d0305a5800c42140c0f1038005030402034102c0003516401281342d4502250103404a4105505400f090498810690640c0141d01201c0100b0000310300940e02c3c403085a0649018900f8505 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 302844091 1250 302842841 302842873
    0x30f05070c110301060504020703051b0601180203070e03060106050409150303090b0f0d0501090e010b0f030705150c0d03050121030504050918060a1e060e0c030712050a020a11 77
    0xd102401c8054182007442c0c02d560294400c0e000340200030000c64076400346060061882d089446e11140300c46000740d1104901c00001545030403501c41490b0710f282c0115400300003000c0d4001400308c0d0180b2501044d000d010f543d040c011540030340740c140e81d07481e149d40c500549042940d100c2d40580da8400d54000b01400820380c0b1184060640e01403600317a950341d94055400b2070141c4107020280814500d00740020840d003c468104d0303003010721120002d01421072141c040148901d0740322101a455400b440041110b41049400d10310040407000a80c0e040050b5903800a00340781c1e42040c80b10006e5a50030061000000d80300b41c000c80070700008046a0303507202c035640280042c41107000340d41c4600810340c00201c000d03040c4c1c0074482000c1c0c4010b05172800b50a201c403000001e000c0c50341101070f40702c2d11181013807500b40c02440b62404455a5021350041a255107022080c5a03001400710400c00c0580b8585164103406401054000c0c50300e400010382d10180180000d11403400e4043d5948540c00c040b441c1004810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 302845341 1250 302844091 302844107
    0x30f0503090307080f0706093f050109020f010215041506030203011b020609031306030f06030807030809010f11120a09020619020706090321030e0f210301050d060207020102012901030f0507 83
    0x4d034034500c58640c1a441301c002c61980404d5140709d00101c008104002008410b400032003580e131095403170300c1099043c03d00690b00c0d140c14451551840d0f0004000502103010605408031166014a00181987d12070300841e09540d103021100201c08502420740c00950b90402125038440040400303141400102c509440c1d80e030000f4400c402c10580c44403c0c0101d24196544800d009651164045954150070b00c2c1c040c044d28012200c1e507449510741000800085c60030f00031251807540c281400c92501c000407540e00418400505445d40d607035500c3c0305807001602e43e44004c1c80050803c0180d00d12034070000a000740b407c0d2054219a0406c00140780403c0011001c014501851302d18207058003950425290440041400c824203d1041c8100340741444024004140003030040070440e030b6940c24100c54822100c1d207110a114168000c98200200c50110300c035a4090404076205100100302a05488440c03c02a0b41c0800010023000e00c881c413003542ea41c0c00d032140d5158241c00000134030240c034010781d029109203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 302846591 1250 302845341 302845379
    0x41a0a052d210f0d05031e15040908030f0705090105030133091802180d0309090c050a030c09030b06060705030d050f220507030f0503090307080f070609 67
    0x324000d02402407590b90034221940c0c00c1d008032480844140480030301a0f5450024850078000d0081110b801c90f40791203042100e100300c8000644800f100030b643e0304c0001072038000b0700c820302c4604a401c4c124200e40c0d40e40150501c2a000c0d6160540b24140703141038a4039224064000001e00908004207001070740c1010036241103d0845201160406112040c1c40081d101540205a01d030103548000607860782015550050710311818018041e03407801d40b00c0700c081344500e105008000380c0780c8400f81084c0c0352084007003145501c00e242055a15a0724120081641d03040003015001c40ea002c41c2e00c0c00d0381c41d41032003a407803030011510703000591070310303540701c4800e40038000c1c1c10f1500070701d0f000607403009200040049640e41c81400b0410007040c903054544061404056800081c417020308502c03101000c1d000c2000014881e0000040e00f00145960b8414048032034010703045500b80410b0080e4405035405110000c010b00000c07014000084c0000912030803d0f0454200206100d201c410a014441c1c500360004542 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 302847841 1250 302846591 302846659
    0xc06020903030702042c1609150803040e0a050a0203040b0109050705090a350705040216061e0b120303150102030c0a0f021306050f0f0a05041a0a05 65
    0x56440e48010a04512079801c01940080c14004119880080004504442286095241503209402e13404d1601c603000b0504001030f0000640041c0712172481680551100c5214004107600c140d0760b24401380c2141c1080e4410b0701201030740c1003003101e076061500803142d011030f0507030045140d45400e07980c1c008020410700a02d1185c0381d4440008004602500c1100d104060040c0801201c0350b885000210490700103104103640014909800740c007910018407100c6040c40b035400744c1040ca0030001404029004521090f200c000c410303a644010170164401c03141848a0081a00420440440340c1000d441e0108403040c0030b003014899100c42c8110200c2900d41114650525000c4043d9800040f071940c0601d0000d9941d500400e18440d04100c84c0d10b1247c1802c0d403080e1074501511030440403410448405100d101d0700818a16a00e036024600640001c82c00000104007a00c0305840714085021203100988414102e401d08009036503a1508040307000c010704080341e8481c00f0002c00d21403150a10702c181100108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 302849091 1250 302847841 302847847
    0xb0709060c121809021902150a09030e09070503180705031506040f23070318030507140304140f030f0a020913060c050d0b09010807052e03020901020d0804030c0602 72
    0x2c0c0b8031030a2003e484980420201d680991607110000096004c045d2411058101d400362203035090000c83d04c0c41007460907a6500c512a80c401080c04060080c20b0000c608001a90340712042940d102c02c480760090300c83d030b6512600c0b481e28143e0644a8070b4003030041151540300d00c004014035a40002d00108400f4920540c025540b1140c0c00318014041e41d0b1040d1522074141826910600c00b0ba0741500c8580c6000c0d1800d07a0079880c3e88909404950348072218516210b0b120003208003290003070006010a41c03240c014540c00c411a00030003400e681141d007107000845072a01e1400020724152900384440d15044014010840c100805103946090f180002070280e6000800901a6031000364928240341d0844428050010801c00040c044e034401c49a440f03c2c80d15213070056009080c00d0003400e0617100c002c1c00802c40d96040c0000c21008000301100310314080c5400141b01c2030001d9076000501c800c103c44e1000360712200000000390401c08084090000c0000000c01c00000c04e62110744812519007040340140c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 302850341 1250 302849091 302849123
    0x2031c05090402121006032a0c0c0e0601020f121b07080706020d1b0f06020f070f080306121204050607152c030901050f03100f030b040b0709060c 64
    0x40a001d140d00c080e40c414030214010300501c00c1400d034141300790700070a419000741da21180d0640880350b80d6800801510440c400b200104012449041d440b4061820940030001c0b840c0e55145c200d500507000b18480a0401040c01b4455804010350540c0c14495406403148041e917000603151409039594941034280101000c1408560520005002d010b412040d10f0403a9141e400107942d540507042c0c100d00040c80303408501c501103072441042c01810b61150301c0d06104030741c1e0b44503000139410490311101007031000c0100d1030004031001c0a01a6851190329259200c0c94003408015144210000c4022650402d0a00103810a04402168107813202180c583da11b40080c1c0c00c01400c404a4007042031446c518200c003814403542e2000040c0c2800a024242040748111204000d0b05d9024464000e03000c0b401c00d0003881954480036010f540d02103c01c1000d59a159074030090344a40b0109641f003501e0740581031007400b0510101e18505940b018070b038102203c2e200e1602c4001040d0382d41810024240c4020112400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 302851591 1250 302850341 302850347
    0x11151803190f1112060f01060219020907030b040f02040303030b13020313031209140606040c030c05040e041b1805090a0f0609060f05070203091207030308061311070804170a02031c 79
    0xc1e04d05108412201e69280000140504030028001c1c00c0143c03141c07000d682aa505c000d40c0c2e11b492158050400318031130b10b801005401409004160700c1d0710035151485e031480307036a0600c050402580a6580802c01003581403d100080c1004800c042c80a4010401c0095544072241034041d0640e01d403034120055095546120010310302880010b145041245191080c4200000c034203001d82000c480402401c0700b001c005404452010b201800072580500040140d49454502d0342d0388140034080341060020394000150001d002900600d01190a455180d80314100071310415034021b103144001c0518007200d4451503c00744440000400d03c5465001c1c1000700040b0750811146004020801d118505081e04065100c0d08a8101617025400d64035140410f0000040c006048a801d0344510303002d40c40300024090391801542d46c0018040d00c130440c01c4000e500401c002d2814600610629844a003001092403130b004100c0848405980046103581c0903a4001c0b440c11140100340c1c03611200016501c00035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 302852841 1250 302851591 302851609
    0x90e091e240114010f0905100c05010e0114010905010308041203120908030a0c020111070221070311090f060907050901020106030209012301020a050a11151803190f11 73
    0x30709070040100c0c03006602a003510034107a0380c0788007480300c0341d585000045449001040407000090341e018020032030ba04140806101b4024180307403240322000d05803102800d403010b810340c10966070b40d01c00c13030103482d94070214800d0b000d0003c0c080c0070701942d4034688034500640260300880c8908641d18040e0410507014035650220b440d12400300388109041400e003500550800c491200601303041c4140c600d0440d1041c450b149084140c941d689051400640038810450401d245140021f1044420790085140421146c40254803419503000b644c81900280f090b00703d0302030f1505030030740c14110620010703503180400954000514603000da02c0f5468140100d014002507480039420001e00c0c000440da4509910034020100d4203070317621130401409080126600d0b000c0d404007034441d4111301008400500e0b100d203c000000e000800341640c130100c003240c40b10b0340c1d48008400982c0a0107600085e0f0181010b10600f0440782c030601940700904034540312045280c0706c0d60b000402140a120702e405072541c0d03c8880c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 302854091 1250 302852841 302852863
    0x6050310150201060501020d031404080705150a0e010605100c03080a020904141f0e18010f0507050705070b03010f0504020f0c0a050604030314070f050c0c041b090e091e 74
    0x80e62401a11901c40a0b000f01070f5400340070b00500942c1c00502d006800782c0030b1039000b0040e404d03800d00305945686800e515034203e2101191540509040038004840301d44c0c640740907010004001900c41440340c0c83c0f80c210346e1b1a0344054002d0300c800d000c0603000c83d0031480302004a40c06040c120314581d14180c80c040203100312a0402e5102d46401e14240c01d000d02d400c0c0c0c1504c544402c490b40c00204003c0d505c400c0b4005098414045da00441c0e00001d0054284035010080101e010350010070b081e200c0506000c1518422142000065408a0b0f14014004100040d000400100010710702d554142040103800f5803071401030b00d000301d4001503d8100d001c50740d400c842c40c4241000554003802c0035403810340e17110101690150002030401d42c0c62a0b02810905030240903c00c40d07284c050b0b95440348003040e56190070500ea8042a0301138900841620346a82c06401c940c000802466544141c0141c4060310f12000e41c0c00c400001c941040070880f5048000845031442c19030604900351000d4034900d045c3c80c1100c0060 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 302855341 1250 302854091 302854109
    0x60c03090803040605040509011a1c150b0a03150f090e0c040c111204060f0809011803020f1009051908070c08010207120f0206060f060918150a060906050310 69
    0x240001d00d04e5030002c0a00142c400440d00250707166620850000040d00030940b8000d0300340c00b0011a01070240c11602d4211000c0c1d207010100340c0090b0481081d080401c41c0e80100d43c450400981604071503450304c5117203120640846458622410183d50498520341801107483d516640e0301c019001c6e0004020301c03010302070010310900030640f40840c010030700e00c80300c0d80380b2845101e0143c011008052000560301540c907299a05140010304201c1100ccd03017030000d070464403107541c0c40e0450500380d0f109c0c1c1d03010018180203400401d0a400700404940ca002050305c0c0140145240c1242c1c040000e1001c05e504c0540b03045920804901d504504001c1d40350b115085d00109244e0600d07200081c54081074002c0c1c2000c078025807551a1910030b000c1c054824080310404600142c03c294001070943c0303441e40d03918007442806054a82040089000315503085456524410511020030803c035800d4500e0111902890094a103107680300d103848005001000d082c029101407100110004500c0b20b03400446200800c1c11304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 302856591 1250 302855341 302855347
    0x30c0e06040b04150e1b0c07030201090b0304050604080f041d18010b0102071e0b0c010f0510180915020d05061e0303030f22030c050111090d03050903011401060f1116060c03090803 79
    0x2a44c1f0035507540c1907101c1240410400c010009141010301d0a4a1050741c106001d0512660341d0303a180e034503582c4100243e9010002c107204c0403408a41003036000321311004082c81c4881c941040d0100e459004840140904260f05042c40b5071400d076030201d44441200c11081c82084410441c2c41d10407200500c1d03400004403580d002c1400c207a014015005000841483d10040207903840c0d00c04101031150550007406000001c0440004c9840e4043c0e0044141c00c3c0540100d40304900180c0809050b684038507100700c0505d48500c1804034529100011a0441c02c410345030400305801140820f031039000c014104a01072441c0c8000404882c03000d140781031405880010003040e0109032502034030054000c0001e030f600e580b91291008036081d0f400308640703071171000601c2e01210b044169021130f11517121408154065498212413684120350200c10350280c4441d480300c151b500304484005243e0f081003400511140c1c0800c90340c6481a00890002e029a0014940290381880500702560100c5060780101c503188400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 302857841 1250 302856591 302856607
    0x306020309030714030706060f0b07030f14030c0c070518040f0f12050d05100f09020c030d090c0509070804020a140f0307090203101208180a030c0e06040b04150e1b 72
    0x2000030306c00c051107000c04004040e185d541a11103d09075008414001c0700421141002c603000c0d495090a000c10b500d0240180c000034500c5440d550816a100b0080e60070200d512550301c401030000601410080d1341d2409004924218028903080141002c1d00900400c040c003401d1080b00383c0000d82c1e035a04403105c0b07002c120100e07800401d154407114146280d41d14040101316004485007181086650300715100c40d115061000d510029404034070a50b0f864401040741041c020303a00e02034a0304250003403992102d29450300c17091003d901001031801040109030410080140e9880c0110f0302681c1407005d04002402c4018003040e4141c4442d0001603040c444d14100050040b01a001036210f128102e01003030307801e0fa4403110101300702240c03480208108414016204021403480390041081001440e485078a5500c3e101d1180c0b80e481072304405404a01da100b00302c0181001d015841126000380c1e000c00442010440011000d2000d004080344941c0b0309002ca9400659440b1004620000780c810315512007030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 302859091 1250 302857841 302857843
    0x3071728050609100b010314010501030c090911091c1515081501060f090302090c0903031e0a031116020d05011113030b010602030304170703170405010203061e0303040306020309030714 81
    0x138140ea1a40d24100300e000443c651084c01595428005011500b42d40d0342801c005401034500b0084105c200004c078000002c52032901d005002403043c940d80441d0b5144200700a000b00303a0001a000324000c54110b0120700000c60b664500a8580c903035080024210405e1240000516943c0d4400a0b031031140500c80308481c01c3c142c00d07050407100e00c2d031240c100007a141c65041da54144d0310710010f5405019030303000070040600c0100900410314001c0649180400d4540d00f04207845043c40c003a0400b40010511150540c1c01d4814100d0002d91b101010303041850211b0602042d4900c40c40081c05401040281c40030000c09410801c800c441d02c2d580144c8440c2090440800142148415252110101c0000486c64000300449003d560024240c581002e01b81480d29060391000381d00724200300c0150300c00e852030041010070b0307809a4410000903a0740c2c01c102007044003449aa12100f040d4080c000401a09a07a00100311011641c1c04080541c580d0b89149056056001c3c004024103010040382001c180640 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 302860341 1250 302859091 302859103
    0xf0f030403080a1406150c01090206070b0907051c080a0c020a1401080a020a0207060f0e0a0605030114100504090902060904090f14030903070506030a092003071728050609 75
    0x380040c0204103010304c0402c542c0100c101075030880d0300b0100c0106488022120480102100c241420000c03c21040c1680422016400818150b442c0300c1003400380400c1d500240072080c010903045070a083c2e504800d04c00588a2240003034001c0041c84002003008a1358000c80b050f0158a0300106181e08040d9108140440301da08640040d00064802c00000e86941d85442520140c101170381c0140440b0b03060100540d00503603001172400c1031041445030027032641d42e180c1c040c40c083e280c2d0b90340392030310380d40341020038a508c283c5401898131442204640c0307098203900c0710549044549541000c00c00380840e0001c64a40e1003401c0019401608000384030007401010baaa41d0042c031321482071240f04815100788030f62a0300a145802e5456008000208101c0c076101010f140c01641d0010f0001d08100c1a5407094900c401c000308200702c0140d20008140c0a1405024000c0244a50b1003044002d803080d690383d549034004d62214404010540d6aa028158404215180b01e594808100c403002e041040f070031079442c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 302861591 1250 302860341 302860351
    0x3080a111c09090b0a0e0c031b0d02040e090f10020d0e010e010b010f09080a080904020c0a05150c0406050d0903020109150227100c020301270b100b030109020f0f03040308 75
    0x58144003002140e41808038910044070781046d03d501007034940b1800c0d0302080d40098016400013465041c0c103011400884010484050000401a6218074003030010034035050013040f1540039000f1a040202902011803188841c1e08030204c01070341e68a140f250403009142c00b03c000c91981d0700e452602c2d0013484056000203002e05098982155821600108a401c40c40e5400340c81d05c40d40014007884000341003403005c0c1400001c000d03c05070400d01500300462a09031180f40944480d4403038004001010101408146c100341142034a84ca09400c050024107540b043c00c883c5c42030182d4419481080c140b007940000c8166520010134040c0c00e00c00010790f8040c1d002101100c08881c982524083c0b007001d179164440c0120300103000c0c05052018001d05480c2401c000b4801d0703805549541d0180d00601c2d5010021200c8003a42c111105050741c0c60078106450900240b0300407020031201401e01940311400103070b90456190450160b07a52080d9161040307180140c1949210002011003803104062f0070040881c420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 302862841 1250 302861591 302861609
    0x60315011803150e0c21030f0d051b1305010810030c18060504060f14180c04031b2702120c251709060403020a060507030f020703080a111c09 62
    0x13061948501a154007185284d154001c08044e0411540c2c076550302c4071000b00c102401600d0a00646552082c0640c0c0410398071142a039a807010408060700520b810b076150340313507154060b08005546103541d103540401c0c0200e030b040c0301703082000034000c41d07035920f840004c0e541c0f04854504441d0343c0c882c05824002c21240c802c3c516400d064004c1442e00340340c81070500b04c8406031402c182041c42d120f202040082030794201504036445030410400c51200f02400350040d481c003064150303100c2c514201041c41445c500c04e90707422440d07422030800807000d00020008042c0d11101845852a07601010300c40240700c1c00c200d8003488500c1d0300c1045401050603020b040e080b012005d20300c080100c00b6003600440c111440000b0009048610300450422045010303101c806030280119140075165000984402569401100015000503004041541c05410003100c1c0c0440e0004009041c29592155042c0c01913012110820520944100048104101c0e1041c42c0e1a94400075014a9641000406081a5000b40121 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 302864091 1250 302862841 302862851
    0x1b090d141c0512010e06010302090a2405040f091d060f0f06060a120e15041506080d020303010302060d02090909070603150501050403020d0609021801032006031501180315 75
    0x3000d40290b003250315482c52451440001d80c2883e441d4507450601800640c105035082c8444142034031101d0104000e40719554900c286003d8948a841c00380c00700380098002c0240503c01000f0384400c811982d000e13200f050f1804103407480c4842400c54001c116000030342441c40340d40c0521080b9000070102c1c5000303140c406c185a000303640d5401480b0780d40c42400162000941c1164081490b2095a4041900c1070102e030103981c044810300490580401b019642501c450043e49400300400d40700d0304c510401002c0080c050916581e540401940380e010520010740620400a482681c0c41c5a95040b541c40704c20081c15080241401003a80da41ca480038000d05001c640707050308000007a84107140110032100e05a644a10b09815542403007080d10001000711100754580d40c010b401a503d0398001d194500010b00540c1c1198910300380420268041401502e0780306900f4800400d40d128007084a600030020207580041c1c1550f0801203070100c000a110030800560740710040100b00c0042500e11141d00003480601c4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 302865341 1250 302864091 302864143
    0x111e151608040f060c0809040e16030b01080c0a06020a0312060302060a020318010203131403010609020313052a0409170a020c040b0901050f01140f07080c060a051b090d14 75
    0x14085907003c03006c0d0000d078090180c3d144a15164201825221b0603a003035070307041c003602c4a0603001c1d035040c0e03081101c000c4404801400142c03010804655150021207820392110304d04030307020391900700048001c0c0400c640c2c44601d03401e2842c0e0790000401150301510841d681c10030004020f442e038103c14141c844081c21614200303c55031000081d18040d4102154031003409213070148001d620b194041c00349401d035403140e500160203902840a14403680c2e00100d400d2108085192941c1403600c0303456440c4075400c840740400c0f4070340380c03c420b203819441c07040c0c1300011240c05034102101c91010303608100b40c02c018000f0701d0f11456030340070a003000007c10a89041c0b111010150800003011424019070750414000b11000c00958400d042c0099104901040a46802e0207100e6040c070304e6028503000e898902002030840c04500c81044080e61005500d502000a030a0003603034545034007074441002d880c2e501c0110751540640d40d0344031403196142d405081c92007159907044440751203e003252a91100c504003c04820b07 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 302866591 1250 302865341 302865347
    0x9050f12100b0d05010507030618051608071116090e010e060402101704120914030a02040e07080102040f05100c050a02040c140a03050103111e151608040f06 69
    0xc0d00c00290034040d210301004550950014451104403940c03203e081803502020610178071800303026408503640070407003508000100c2e0106800c41e203447d085c6803428003040044220340d105100c20000a103020112074841c89401c55030100005044001401103007440413004280d2000c0030112085180c090000c0000207002c032b82203400f6020036007034035080100003500503e0b001400400c19481c504200c0d034a00384441202081c41c0c4d040702c04031800d8400c401c0b045029500001680000c1c241242404404041100826240c01607060001d0040d41c84809a4400c844203100c56001703800c1d054001c42d15242d480d0b990600a8100303102d2540035144203100c80009a118a8892044940003070050090001c10303400e2000030041c014864040100350452649003034041e00081520f843c140e580410b50354190b0030085642506001c095101c0d02070400c1d1a20200c2c900e0b018405007810403a1403444080341c0500207440c074880c83c4440c0c9072010b521214502009039100190003981d8600c0307261078805071202c1d029 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 302867841 1250 302866591 302866609
    0x9070f020105090304051c2103020a02120301061b020105190503180a0209010b0f07061d16060f03020f0409050112030e030703110609010c05100c02010b0a0b070b07090305030a09050f 80
    0x90b003144030301080400c00e42e1f4480080c0441d40c030071120031851682d085980207044031006a000d0019400103858440140e04101e00342c000c840f0414002d255515061024026006001158110320084044d820a40e800740007a1880c24041410001503814040d2006015900c100c03404041d41350760006001c03400d00001084840305078040e00e030403510b90900da01c1e01c01c5508200040c1030100c1c0c00300102c00c00251a409070f50300c007004005070123020400e5100303114100901041001d9900540d05001c2042d544d0100d05445404064100107035074240c0c24040039143d205a030001e1040b00d003420000074000385070a07a010801c40c029903a80b060b02101008050702d40129100c081c010140300c02c14187d840c81c0140080c83d08250506100080301a65942c1c681040d617500c40c189801035592520400c40c07a020300680810ba0f0301241c822602c0e906203060004076000b8407101138120320f070300d40c00030b241680070703c1c2001c02075500030044a45662904d800217054540c9409818001c00d5049810286420a940f803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 302869091 1250 302867841 302867849
    0x6210c090b1c02040e070e120c0613030506101e0501021e19140c0d12050901140f030411042307030207023a0b0610090509070f020105090304 62
    0x20159118580310656100380c024281d10058491400306aa000c000b241c4010b10007801112400401ca2a110f03c029003a80404400345000d040000c5402c03a40c12404148803043c000111032481e25441440092040703c16190030081107840740300113019510420f81d003420125110112203491080000c042890b41158912401d400742e4011804111074000040c00c090820b4000c1d0221030390042516001c0c0300f0170a006070191208201440d03070b24408802031003100301e07691095138070502900d110783da0f50020802c08ca00c600308012020841d19000ea20603034bc90b00c1c400e191061401d48404083d40d4802a6500548048036100c4003a825100c450a01d80242902410311418131a80c1c40c5072880c025415840040c01d4a00301542080744600590b1441d01240801005401000b4003892940103e50319115030303401240c943e98041c04210024400c5007005520440603102003030100a91007082c0c41c1d1030404d81203107501c8501c0c50200203085610020042e10282603038000e00c011780301c80c0e94658583c8a5801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 302870341 1250 302869091 302869097
    0x604081b0a0807030209060d0803160306060207031502030a140c091333050303180418080d020705010b130b01030506060c07140f040606090e1f150c0c06210c 69
    0x7410009403401b48000380e4004406003071104140210381d12924140d008548480020005041001f070407030b4148100320140620740002d05005045407205195203408400b0382c1900340c0c000000808134009604400b0a00c490503804660b282041c1d0000c00040d0400007625008066400000d0900d14560180c0d8150501e10500d101401454418102000d0b0003030542911048003448001350648040008001c2102c0c0c1d141e2030000c002c40b600400003691400b0340445403560b540301580300450344910454044440705240144e890002e8074046000d0039040e680103a0100e10f03804400d49007030f040e40121314424400d13030b020006c03035803200c08004440c040d080391080705521034042400141880008815400d00c01043c400007280480001b40c15910160407090015140100c01c1001d103130800c031402d41041c078941900d401c03050718004039040c600f410f01c9200100c9045031040103800e4014460649074903000002660943d0b1181e0000c1c164030320107207012124a4511482c2d41060096218503204104d480d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 302871591 1250 302870341 302870353
    0x308042912010b090315010807060323070c140d030207211b030c050601090c09060e1309061401030b090706020318010c03120509070e010b1c11090604081b0a08 70
    0x24601c0540380c104107413403500340c8950f05003090100391000041d802032100e50000c00e100c0d81416801010382c0c00c2c2e000301001d82c84042401506a8540303100040d48820f041c903004a0200c250f040480e0f1f102c4920320483c215004a249801c2c03c1e660580041c094140a4a02e02000d100c080758a5a107018042035510000b90003041401d60580490300c01d035082c00d01a00d00f80740c0c441d185407962810043d0a034400d081e03596596082c00807960300700d00e00c00020030403818035002805c969000b203040040640700a41c00710b40d54005d100100304495200035a56003090100c000d056071680341083c0340301f10a40708181c0038491114001400e134400412205841c001190440b00042070740010341c0e5100c06000c048091228500300c09a4030b100d10700c15284100440f1004000003450207040071951132041e0010041e49504224200c0034a040f0908080040c4c0f1503c3c0c009405120410720718568018601c03020b034440000180041d0034a800034014101e07203d50307603210428004036020005420858402e150715604a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 302872841 1250 302871591 302871599
    0xc0201080619080c04060e0127111305030c040618050402010903120905010305150105071104060510020c0f040212010603110d09030f020d03051e040507030804291201 73
    0x2419400d82040c0050440140403606500d10b0526103030907041031005512101d580001d80c503190080c640104042c1548920035410000c84c505c5400b554040004200c288040d031030b950000c0c03035000442d81c02c82c41608a4a0300200c01c2c0941d06030740c00d03101d1f0034400d1041c550014035a203854800c0c0301c22102021100410080e507061610050030005009038140440100000080360311b1850b02c282d0144669100d03007110b4100710026040710009005190142006644042d8590f0001c049400c6a03070086220440c0400f010b0004014013642e42005800c80d20f10441020840e4000070100034548080340c0180702190729205002c220b0180ca0321407103500b002e07200104826070207603200307140d80c0031160529840c003c548140d550640325002011070001d6400400a07054a60601c20550360042d640b07824031042c1407048141c405900e1507000b0009400700340020404105081200340001d6511440c0b15484d1956000407801d90340f496280c051002c40c0851041655070006411605000c07003071484040c281c0d00b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 302874091 1250 302872841 302872847
    0xe010b070f08040b0412140a0f02040e120d060e01080f121804050c1b06241f0207150f09060e1207030c06020d081308031e071805030d0c0201 62
    0xa581d801d80e6031820401c400f14251000200800143c410130b178083c00d003a0b40525000000340480400300e0040d80000102d200000c1c1d00c2c8000e21803482e011140415400404181d082c20035001c1010002032100005800000322100d400c540100d4035903003c4070303600f03a903140d4405441e156102c015000c180c200d50a19619048103e000d0300c0460a503c0f00452002d400c40d0101e012141c094500920a22020031f0070b001d607503050715442030301c8100350f0050030399410204c40045030360000c40508c41c0c009410700402e9a80d40c642524518034142c8a5500c1c401c49582d1040281d21406103004141c409010418065140f88c0113446440c1c0100c845d03990101120f02e00501100c40000b40c814440c0d0021201014405040c0f0030050710307001e94040c03041040082c2c645840603240c8510b001690007848501e03010800010210280c01e40080d41000d061a07990341c5240b10213110030059203075501a10540300900c00c0e802e0380035804018044e000c145221841d5101e00416554003071741c02d0030f04000b8050240040040d44 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 302875341 1250 302874091 302874113
    0xd020a0510110f13031502091302030601020a0807080903060c040803030c090f101d0406180b0d050a06060815151306050d11040605060306090406180227010e010b07 72
    0x118240c500300425036074a40c0d45030380300b800c0750a44c03035040b035800b40240100d07424017424216081c5d0045280c104d001d800b080f020b451021003c040c003030b408000140c031742e402800b01941c8654004805581c2d1403043c81c00d4456a0408003015020b88504000070303908628034421102500d08183c01036055070350f6401c410086038049440d003608803003410b6940407a6242e074002131807030303421949510707500e0348000515958401503030f071403584181d080c41d204000da00c00300000380c00c03002030100c03000c1007041010005c0f03120340b460f24000400c01c0c840e00d413260050000e95401302098809180c00c1e15240ca420b8270851440c800107440401e0001c076042201002ca16106141102d02d814108000c5019aa660001191180711141c19551203582461f1701002e441c05200b014080c2c2000c8600c2410b60030698081042040005e0008000517640d042c242c0740035061903c03402c00650300900c583c00a8030500b101c50201812400503080c224040720001c599400c4840b9500e0507514600145070410f4182d417600f24080e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 302876591 1250 302875341 302875361
    0xa0608150406270b100c0b101805092103010303080105030d050316090b1b0606030f070303080c04081902090907050913150e2508032b0f0b030d020a0510 67
    0x1941e4130300d444815100d81e031043c24070280c1ca881e5060b03404010300340202e0405004120406c0700c0140d01007400b1a8500c03090460312964002400500c81d41c50401691402009030342800204280d03032044000c82c15030301c00440c140d034403c0c0e80c0d006082c1d90710703014190358103440e41d03480f4003048050000440d16204507038590700e510000c0ca420552640e590425652075401024201c0541150300307a4000b6034001040350b80c1d08000b0a80051008044003003026071034175a540030040800c405500442c01c05402c400c252009409054142c5001080e50041d0020340800c1c100d04a00450402c00000c440364008105003084a001800440c00c55a411140da1451103c0d00402c81b1200c030b419008402200c0d49114240500780a9001071010342001c2010b801504060f50108100c41140401400000c80203c1075410000e81c108220640320149022034460001d6281d80c3c21416191500d01c0342c3c0303000580c111a044100c1582901e01070030301044101d846045a10b805452513221916255654646900c100703861 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 302877697 1106 302876591 302876669
    0x90304170c030a081c060f060e01031407080a11030f09060108030c0d0806040e01020313170a210204051210050106110d030e03090a0608150406 63
    0x50703614110000c113000c0d030106440550708008413507420b0302e40c0c8040b01407141d2610703400550020821440744000040841541030320b254024403440d10000080d0402c960301e80d41d44030301a6200040589113021103070b40d4000c0c03a4001c03d600c1d8003550158200c0010403905013401c104035494600107800000e0240c0080100741020080010400b0400001d41002e550390343d40d000004004010400804040d03500000411420901c086e00b0382c840240300303102c05c0841d410084504813150040300280804117080c80840c5420202507052000c207034456500251400d0317200c001051740b40700c6151200d502c590088102d041201507070300400e03024040e240380c0501002c4828102950303a034600c002e60418140d0364110500034800600c00c680080402420040c2d19940d10742c00200071841c01c41c3d15a207420340c42040c0c2021f074a41401154201c03210309050004140c611007920300104484201d03042e00c = true := by decide +kernel

theorem cover : BRFrame.Cov 302697841 302877697 := by
  have h0 := BRFrame.cov_init 302697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 302697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 302697841 ≤ n) (h2 : n < 302877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
