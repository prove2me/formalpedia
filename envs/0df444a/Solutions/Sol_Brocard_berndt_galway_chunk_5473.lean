-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:58:46.288304+00:00
-- url     : https://prove2.me/submissions/0775b34f-2b14-4556-b166-6ea13673b9f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 984172661 ≤ n < 984352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 984173911 1250 984172661 984172667
    0xf09060313052b050306010f0809012702030c0405061528030507110a030503070f0309170319020a08060402070519111806060a18030503131703090108040210 69
    0x1582182c108040714580104071034020803c4010310203401c0c080c10960f040011450040c0c040300d0003940180d6070784c80500d134440d00484098501404444241d52220b9140c0703141a0110011605000c401c4034517041e280b0284101890042104400c0340554180b104007d96a560b0341030706281c0c0f00083c92001da4a0864001c0a50007401080401c10340c0f10780a0540e4081a0b03060f848070340b18801d00e84951007071080004990760f4803201e008009000400400010f50070a2243c1640c944c032000c2400d0200302e00350255200b0100d10b1000e40c000d590800d010080090314400c1c80c3c90b1101d4003204103030841c40c20410a000602601000348210300441e000900386081000400003900030b05507840c520a80d1001910701001a9000c00703180b50322034040080000c0c03440640c0c00300140a884014202490030002d14020f442c0c0c000841e000700c07040510880001301049040c4020805090052101d8810500f007440e070a01d03110110101c0301c021383c000d11000c0c0491740c00840303141d040307601192445034801d0707003000031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 984175161 1250 984173911 984173941
    0x5090c070b040609111818100911030105010b040803040e04140a0506061201020c0a022808010203060103060909050a02120111040e061c080f210112050709020f090603 73
    0x380711400750002c100a001065100c480614428150b0207141807050040220f501c0c10410030807070b41580440460100e881d400c1c000082190a1740503101c41c129240d034210211a00c0343c1054542d400c03500005442ca240c00c0c40b0b07450140a50f00e00c02800c1c2401d01243c030790350f40124021203160100d58030104c0c0074070101600300c1c07444422000444488100500d0007076200c80081ea9124011150440141d401401c1070003980c80082c5040000d10910500380c0802440602d491400c10480422060681030413011043c10006001c06000160b500d00b4404001011160254480c0c0c40d180c0c0790951040001e400480c400000c281c04460700c80c0c00480c0031498900402c1480108007503071000040c0080e5003005040c000d803052000b04c60034000010a85007000c005c020441c0700800504d000c0007190179206c42d1101401c0300d4042209400002c002a00464102c0c1000707030404800456035042940801201708804000f80040721002d44c02d0564900000656001e920601c501c1103c4c01300000d248810503e41e2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 984176411 1250 984175161 984175163
    0x109091e1103090a0339030207051518030f0d1d060f03270a030c20010816051606022a1b01020c1003020c010c0e0a05090c07 55
    0x4000425521850308600c041405110005909024011100049403002d0324490308609014103910391050781d00311800350b454881504405e410b20071914018030490900008080510706030403902c1603908000e480e00515a004901c60100108034580160140090319100d1a079681c400c0d0002815800003400d014a5441c2e0b040301d0b210b003856407801d032907010040d5048032140d503041c0d00c000408003081c03015502c902c03180031454030750030408241c529060500c0d01500c91078030210800a00700680155082042000b81600012282054001804403110008040f8907a2080070004040100000b07444050007d1400c0c905014110840110602480c21210140d1215001d0b80b039041c0e4a00c0c20f00300a400500a500d00038405940c40701001c20620210a490341c4480018800c111602c013102000c3d28488004504502901324240700c1c640b0f131039046038400c244c1074034003584a2818460760f80c00c40d260301c5070290030050045104032058a03a8403a58042d6401075900802e141e40704003003250103114480c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 984177661 1250 984176411 984176429
    0x12080d0c0210151a090d020f0a1a1b060402150c0709021903060b03010b070b04110315041221050406181118040201080a05060f042a0801030f060b0109 66
    0x8038100c010901d5000600a681005000004c100c0c400910b202e4680141c041e10341d0042d140122040161916140c0c0c01e01c1101d0080c4049100c545851519000822419007000414004104070b0341c4100c2c410302d14030400d512140201850701c2c040d000a2401420340203100500400000d41c2012410140060130190190000566030350752110b8003178461f441400b07566030009141ca18086500300c0498112412203030701180c560b081c03105c151140d000001c03002e4412285124060f5100a482d1014440694804425020180d05140c00d0038444400303041000404104444290901d01052140000e03407200514070a00150315175861805c84000c244680f03008090350700140c038180410107200d683c3c0000090644142c210341407411910b040200c0d040e03400034081b41121000960a4080d070340000e6002100030402d002050026010800310340f104520041c100703440800008061940c45c500f50324901140c42d00152561540e11003041c103120342440200301a440b0200071580b40c1c41100010040c000d421 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 984178911 1250 984177661 984177671
    0x30f02090301020a1701050102030c1b04020904060e07030608060105240c1c090b030c040915092306030a03020307030809010b0a06110606040606052b06081612080d0c0210 75
    0x201004c5d081e101c0300c603070055114178071030b0010805500c00f00943d0441c0d02c01c20000c0c16099510041460906110086186c00c0340d0300380a100c08982d9075000340300050a02526128084c00e00d03a80080580e14143c02c030004550016004001c1c5454159401a1131240c00e41c6000200c104441c00030058071683c0c2e80907003148660085402c0305801100c00b02c001204a0b01c5603090a41d48043c2c0c1c240e64002280da20410441c2800104201031242d000f517000c0100f840000340071181c440700c00f04111005164800315184401d0000d0324054050803005410120880061411980356500250f0f00c0c82440d0000b001c100001011912100f400d40003080c01c43c90051001030320603107401001700000b8070b86140d0075407403050b00c02140d00e070300780341c4600000c1c6c2d04aa517405141103030803607040d00c013100700010203207508805060291030884a803040001400310360300506400c50b80040d100c042c10a89410002001d8040114400001c404608465040111a101043c0c1e1b40001342d041e03044c0140189100301c900d00701 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 984180161 1250 984178911 984178927
    0x91501090e01151803170904020d1104080c010305063d03270f140705040911190605031b040e040b060406060509010c1407150f02060109090203030a030f0209030102 72
    0x70b001070762490103480e550000c00003900250f0200c9240d8602c17000c1c141c2200c40b120b014007068000d006210309800600054501000f10140174116102c00e45d001101e4030700420180b0a104080c400170744107010074a818052401c26000040001c108820340700c0428a85400d1107480e0340940e2603400030032803000d03c6003015840d203081c0030b805002203004407880f22800c44940300121000f140d00c40c4450740c214554284694007039450843c2d41c0711709041440c41d0b11900300d0000b1580c0c0c0303078014074009a2142645006c410002814056007034a18900040c081340000e00a0080780e0380300c420349134008081c4a142148540c907289541c418810382e00801100c0009900b08010b00c8910400e00c1d002d407030217070b5040110780d960741421103550250301d428500299010a0010101e10501d5084090740000740c1a40c0125a0f00c00ca96440c01c000c04254402040000078551055501444071500408807060140b090885a6002039101e114020803030080c10790f80d02240c0c50051880c1d058401a640250085503100a2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 984181411 1250 984180161 984180179
    0x50615060c0c0f2403040c0e0106021b041b0e041b0c0f02041107030323161116080d0207090b0612280209130c0206060d050a020607030512070905091501090e01 70
    0x10451b0103880c80581294001141259046000c0c100c0d61658090044a0440c0c0e0b03078090745035542d5000d90350041c0c03901c500c44d002d0203016259401400981c2c544414401903242030006130341d034041c4c4071014201000300c850340c62a00400c040800c154420703524045000d41c0c2c80090700510b40c03800200720740c080200c2d0341e004258055100403034400e041c0c80d200100c8400b92550b106c00600886500a5243d07034000d800410380d01410050080c2c03a25007040d03405c600c2640454a01d40400c80c0d01051141c1d000103010010319406000c0000900000182480904500408980c1c01d00c201407c82d03030b840075810b00060b5641c0300c0d8050041e83c0346611800c020303800010074412019401061090303124202e042c0354020004100c1c854003010711580d8001d000326a03030f040100184550020000e881d00e000c0c01f54520010780d281c10040c100a0302c0394a03a951900d8050b0402d0400c4030000700000b06001d06100c0500c034966071800f9060303115454420040030039003c01d0048603d012241e02010050302d01c08008283c00c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 984182661 1250 984181411 984181417
    0x3020306040b040e071a1c0b100809060105130e0d020102040503070f030f08091f09170d0c1e060906020c01141b0306060f07050615060c0c0f24 63
    0x449091004a1080b0100030480300c6842c0c00400d65404244200120080321076a0f40c1640104200301d404c001d551640c81201040d040404d041081d550001c0c900b1500d403c0b5800c402c40400e91030403403c6c61410b5105180c0d602c02c107001c0c0a2041c500418502d00b02c44030b9400a603ca07040000503500010a9680c01901039013203402910700c680261900460400c038050034400499800070340d465014581911000c88507031003542c4c556080692040d401c415000f42d1211512404501d0340d502c030201340380c0700c081c0c0036140f200a41c0c014076400030035103808a96400003210b0302a81e048440089858402104040151500440104804d040c040c401050241b9a400340002c0202c0070000c1c8100b035540040c500c0107000440700580014210b207110016109070401860f84228081d0415143c103600c00218200e0390802102154a64428001c0000d40503144010840c00941a07440c01c2c2000172650b4620b4031400503883c05809aa04580b48440c150b4829680048156030f041c105007404541c0003900100364 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 984183911 1250 984182661 984182671
    0x6041d0d0c0303231902132405090d030e01020c18040c06050903030d0c03062720040501080402030a02040e0f06010f050d0807060e0f0f0613050606010f02010e030a030203 75
    0x1340340108030145009041c0c0790b03402100b5922440000c0f82d40d804032520a600c2041502500d0a60030712680c0e40d62804401d159000d4410001d003440e0110b00400300042281c1c071003d81008120742400002041c0e00e54801219045516052010400c181140100d191003e61118240e01a0011078a00342d20000d1003400ea000e240200900c00b003958403104107450900c82d110140d0f807d43d008002c084005240d0354001c45900c0042d260100d40260b5900c020700f6903203a018402d03004041c0b022481c0b01e01404601c614020107c2d04001c8008078041210380082c0d82c0079521441d030512800000103002c5641c1403141c4160b065004100700441440b8881103a900d2000c050400b0071486840b001142c0c01845a1107107084070030042502e0f070307040358545e5854525001030600b00d03019a1261403400e800074040c881c40b40030309040c40082c12440046090685000800b0b4000300304261450011404280d011821683c842001c0c00e083c0501c40b441d0f42c00700c1c01040580c0000c42d40f408007042402c500da505400440c020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 984185161 1250 984183911 984183917
    0x190e0310020a1d0406050307060807091a0a020d080c0313080d14040b011712090102030c07030803091b150304031809051b131a07080301030b01210b06041d0d0c03 71
    0x21120340f1003404101d854074050560701d90703c0100100000d51151144642c4800303030f80350070745003155140c441400e0701c80e40382c4040500c180d0104e04101c04642c10480c4484201061428000506201d50740d2000c42c800034240082c9000c66080d8441801070340c0085410319800715400300301581b0894240c105c2c4400540b400c03100da0381041c00004440451241d03070b4014295000151803400c8102c0c01200d0541e1195003540e05500017400102402c1d4020702c0310800460090101d282d03a031504c0886641481c025019440041601c49140131003030f100c01d0000c05281482300100c564036222402c0640328403000e5031115642e41e90520010850f8541c50704040c5c00340110b10320001e00b66201c0180814203000f008004040324040090400803030240541c0700c0b07403c1d891962142e02d000d14940b0ba080d032540c400d81040d202034054000420601c80b5889425041c0f50703401110131120201c079603c0e03141c2440041d10480c400c03074403080c480c07075078045540142964031070700b40c201c605d2004022005440d034010b4103415808 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 984186411 1250 984185161 984185207
    0x604230102120d05071106190612050a06090512031302041409150601140d02031b090d0303021806040303030c0806042c0a140601090e03190e0310020a 66
    0x55400000c034a02c2d04100000300500b800c071419140c01c01482c00400220411840007101d00b0054400c2c407244d801502c6940005c4484402004200191030b403075803001d0b207140d42c3d809058001c2040422120103540d0b200380086000080341c14071919011a20301c20f980e080c4800000c0c41004088605001109031084e2028000d24211340003d840e4400101d40c00d04480d0001810b50800a103128002e0703178802414100a0704e81c240030b003410000741d040007460314009503001040c401c800d1020f0498904001604820034680144140820032003243e80000506251f00801c4a07554211980c0296070a414040c00140e192507482c1401405040c00640503c08228900e011035100c0c10180100300c070700c0c0310b4118003620340c05403204d800703e040090000c8201140102c1007140000344103058141c0518000c09c000b0302d910750400b0120380454008001c0201c1e640d02c01c0003901802e6014060032402240c0c070741018245000d100c00801e041860700444c01c0c6000780b0001d092100e4a030400c0007000c1d1402c00c5802c1a079 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 984187661 1250 984186411 984186479
    0x1812040b0f09061306300c030f020c0304050a080c031507030905010f140f060a140d02040f05011505031005040f0f09200a05090115110105011532180604 67
    0x80700210000040c4c02c403c51b1a104009001c40c660007000c0312030003034600042c01d08608a500c504a811079040c008580e0000941000700e4600b03c400b0b07001610002014191103030140000075540c1540441c0b05400e03500c8a0009400350340a684100441d6070041c00034400c101c49940f0840c003c100207040b100c02c0c1190308021444150490110520400015001070129401c0160341d100c609c89074800c03154086107007400900162207500454103496400500844c0d554148001944010341e40300700203041140c103008005803000707801a00000c4500c10345001528804203002003010f000050b00703105c9001c0c1003030320403000c0003080c4c8241207030a20018801001e005170710041000740c405034441c1030740c04503484006005058540d240b4a00300035032401c040300b034425032440d02c0c3d081d10303000d901084081181203030824200d13400940c040c4038030600c421010520b02607105d01d8014040c0301a0060a002e80110300c0420401035201d00140c0b03610f00400d441c5e1290ba84001421089482c015842c20303800040250003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 984188911 1250 984187661 984187697
    0x3150717180706030b030304090915060b27010c060e060105010206090a15050c0909010b0715290102160807081b0928020408061812040b0f09061306 65
    0xc81507000c80252414900e0715800300c01500c01c140d80d05500d40020000000c0d000c0d55403241c92916849010b0a141d000c6210110b9000c440c1d007071384103175940c25040041c02205d503880c4400c516841000e1403481500814803004980d440d42c800e038020045490041918810000003070110b0495000345d08490056458004546d10f402961200034004407584a50303107103c0409401c00d95100030b401624504000c404400a0f0110100381d010351120380c000a030301028841911625661003040000c240038000304403000030618110742c02c010f41100c040240340c1405030f1090001d11601140c040b440c0300c8039611080c5260f120396103480b6110321482031403400c0031380c880500c242d210b654400406411880d52102c05110740d91030300000c20b003017013a031680362400030110900c00f41001e0b18543d00180241c0c6090354440410000400b561002940141184101c1c0401c8408590945040b01c55580d2120000002070516025407400c06078060004030300001d10a402c500107038126005503580041603c00b4540700 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 984190161 1250 984188911 984188941
    0x50d0b010905030d0e040213060807020709050c030f060301090605100e10060509060315040f05041b03050c060c0c0a030302030309160e01060309080c100605150f160203150717 77
    0x200b41c00d6000982e910031303094003c12038480006000f400140c41c10601d8024a103861809812136008100d405041c0201c06a0412000000d800405000c0016084c07041e42003a00b40002841d401c5d222040c140040c182da02d00303422021a456101d8402e0009040401701340010201f14055004122030000000342400c0350031504008680045d00c540346010b1405c07060000ca82c0c0024034100d0349141080c081c00042d2074507c12003040d04c000040000b0300781482c0ca00a80c1c001c01100340203942c0501500c050011600100f884580c00c80d044a03956524040d01c151641000d00c50075001c5e602c1190f01c074002050580209c02144030b201283e060713800d40103034150040303042030031070046032040c202260041c0a00d82c0694084c01d00c1a00514000d810003180c00710f40ba107414a000ca01140c1c11391900010860750800341743c8080b5005407002c5035402c003141108510414040c004605101325081020742d030079500c1c180f004e07042007041900f03401494500390b94050f2034500314808403145541c540c00001c40f880301b003100c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 984191411 1250 984190161 984190169
    0x3070f021609091b0311041a09010501030c090302031203041a090c0607060f0f0b01110307050613020607020a06021c080c0d09140a030306030b07090f180b04020a050d0b0109 76
    0x800d56007000840402031202c400e0445144482e01d00c1550071413404034114009501c1904d15202c0807a08100740000e42da03c000c0c82070030700c503001c00001c4003030b9441c03030652811b4410a10b000111200c0b0705004071100403555001039014020f2103104003102201400862099004072038402021508407940e005d02c500880740b17842e458100e1102d80c421854a40002c00c440c41c052140418545080a0342208840260105d11340171595108105055600590010001d08020014504112150303c80f1502c5450050034a50340d40c00340da070890115075400090b51880d81c0c011b041c40c1c001c40e40b5400081d40e43c1d0356075008000044003d040d90380c0c80505c00c101c01c0f40314203000f1030b9450170074202c6007402c0c0240c05c1414007203035882c0110709105012541000080401da00a40c0c000c107406256040290101c5005003800007000200c40c5d0501c1100740c1525060211420384182c00d656a00011883e0014428070b00080c2d84640005503901e46258408040c10410441030005c0003101e03c0b940040d15402c0035842 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 984192661 1250 984191411 984191443
    0x603011512060e0c120c12010606020c04021e041503050c0a12021c05072f0706140d0204030c180504030e010f14130f06080103241e0203070f02 63
    0x100c9400000c5154020070540c483c07403c1100c00380e551000000e0700c0086000d500d10f2282d807215480d000c580c504042e60052a000070002002464148800251503e010201c214000d980010715011210540003007083c00d502e06502480c1caa0381c50b14003080440c0743d000d00321300019050402080100c000c0e8130444100207a00e881d213089024039004904040d42000d42c40303d0030b50b28400815030003040030380605c41c03142403a03617101c0070740c0c00200c018440d01604190801c1480c24407000c940e072219000140c1e04003514a907007411190100711042030500345c4240f01152010300c0c000b080000410811100c0041650014064480c0c90055190114102c60040342e000e00001e080007074456055000300b201f410100120302d4680d47c0c000306c4150500d15907020b1080160035050499082044919030311041707021f010640b038444495459030f00d40100c0c0300c41403180600d1241003000384200300842d039440f44841c1400c0d00011306214800841a0000350412a003003c04581c0c04046000321900c003007000c13150001a82 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 984193911 1250 984192661 984192689
    0x631051509240a02070f143c1c030c030c02030715020c03040801240e040c030b071713110307051809010b1206010618050607030311041203020606030115 67
    0x409000d8406a000c3c0c100741d521035003007003a000400c08a03a030343e95006007c3e880298080d4480d0030000d203041c00113060a64408429480c00480000581d0f0040c0000001e006485c0303020764240703030103082100041d8556105c9000e68040c000054064100c01d18181c01d58a003040140e80b0f1060a0742c40384100d00c0e0040104501044400c81c040884c0d005d4541d011518040341c2c140303070716081600c0c00c48016155280c07242a011446100165020015201070042c0703401e900001d08140d542e100c50400180002040d401845001401c6c80e071264561000c1c070044403000c00d0b064146500c05a60404070707070740305455180307c1c000001003d0500164401c2107850140804c000010850021004020701402810055480300c885441d40d54445030703804160345001c4042c2c492541340c90809013a00c0d092150f4202288d21083c1c00f0803295440c1c40588082c150541404180a050110818450f10690704554204048680c140e41072541c002006445408240c0080040465078080c99500200511540315002403407 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 984195161 1250 984193911 984193963
    0xc0703060c090e01031e14070902030f1012060216200406150e04180b010e0f06100f030e0a0c181109030a03050d0b1c060c030e0631051509 61
    0x20000710300d080c900480d204041f04070003003109410700c1141d520141d00e0360f801000303010300220011300c4150440d03040000140442c4c544104c1482181402501900c0c103580410010ba16621601342480e8065015030b0700003003d000d0452212030b03601c00380c2c8a2401071b4604030707000c501d2813a50241844160415140c100d0782021200411000d0040ca090342007180c0c2c00103202100250303450092601034a03410025150f07614040d143c040c0d400c0802031645100c2c0101403c2004440d42060322460344910614004c2940c1403801031980c6401841d12004000c11000800041c141d800c51142c0010340d81c41403400e2120341e00b0386e03000322000d000e4044850b9244c0c00c9041c1c039100190042c00101801c070084400800c40c4000080000c10211090101201e291a05c02c0000c00308000b034400d010b104410b50030100701c44050341e14000d54079040184580052903940d444001040180046001101c006000e242303402e80961908980312000c6c22803500309100c000010a81440000c03030500e8022802c10381400b500b11031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 984196411 1250 984195161 984195203
    0x10080117210913020d09031b03120905030910080916050a0519090e0312010902120615040b0304050106030515070804060f1d070e0606070507090902060c0703060c090e0103 75
    0x503501580f00e000050340e80c0c28101e01e800134020041e1401000030b40803106040c090000074050f10545010074141559030002500403220200142c601000040c0108040c5850341c40c5201b02c03c802548041882641084d29611101041c42405030704156007140300d00b00342c05450180c043c01000c0c1d00c81a80d00c0c050007030b81410b10109010300d6030345106054150740e40d04030300c080f5451040f4010203134000140c0445202c04e0603c02c5070041001400851400c40c0d0074070b600380030b00005440d0300d10030403610082030700d80f8030543c0c141c0e8080c09081403d250f9a051a180071802001075100c105c406005814940301c2c22480e16004500c1040300340c5440c1119031751230303581344020a801001014929601e00e88856510705060440026002d00002003c0641c1844100400658010801440380808200380000aa00880c41d001150b26581002c21101542e01c000744050045883c4d0b0748051003403140c00010300400303401c14100300310301d9120b03501125181d91103113880d99001d00000d400000070890300c04500e10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 984197661 1250 984196411 984196417
    0x90e030403060c2604231914010c050408010b011e03021e070f03020709021602190914010f120210200d091a120615091008011721 57
    0xa9146026803002d0800202c01082400f00c07a01301d51564610300412007006241d164466800000049581401489a840c60303551071074100451001c02c80f040f801010480305c454224503c004410090040240b0f01358024100c0d0070a04c2001034130342c200410100c881d405205401e0002c001011015480605080168040d600240300403000340711401415481054250141655511400f0008841d1495003402881d000a41d040102d20700d20412404081a800d44882040d455041d40c10901448004074641c5000105074040f10725141007407030741895a822142c103030741a174650344c461207155502c42e000d0503060a070f04070f402500941c240a560240c1d6001e000d07030f10490a600e0b100080629441c103513203400d101085c283c1c2c10100700c40007402e011501c45c450801c2c001000c0a0030b40e40c00c1c812210080072842002501d41d5000e00e9800e01c408900c8555142216031880300503180d4503540b5500d050050403003a0901c120411408003071b010500d401e0002c01c583d00303c142d0781141000c001686c2800c6070203d074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 984198911 1250 984197661 984197681
    0x40b010b0c03090901090b131427030304050a0b07180b071118101403070b1605010c0903030f0305090d0e0f0901030f1a0709270f05040c090e03040306 66
    0x44410300041c443e958400440c640601303d4504041803e4108009004016403a2507011314824103011480102c0000110419800320541902c100d01c2980c10202c07140386660300084404502000080100780b1600282d002d081504c50b5640f41040e643c7e48001b101c0c6503103070200d0504840401c5a04022100140c3c4c080c020903401414450031a80700391000598040c902d401c40301c0c1c4640c210b4200007a400c10400b084000308a1804003411202070840044c0d2130b404d80380184180d200008c00e282c104500d4202c00b41c2450b0754080002c100340d17400c00c03902810b00c96092008800050195419203480c921178015180608090002042c004c0c0e62075030300b078510007541c91609400002c0349040c6009513a0300c00c0428000d40c080c450700d500c0d400d15420314211034ac1d041d04404c00d0b040141000d2000c1140c0c4602d4050446003000500600200500341c3c800580b0490503140008604000c0e00511060382c1d584410b010341d00c2605d000c07903030664903101d034825a4042c510541e41c50f001480108041160b42d08200048 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 984200161 1250 984198911 984198913
    0x3030b060910080a0e0d1e090512060a06060327022d03010e010903051b100906050f06030c061804150324060f051306030b010b070c0e040b010b0c 64
    0x2080400030a009800402070140001d11000904c210038400c2e120384110080e0800281101d40701c01d49015000900c05281d440d5a90860380c46a544103124034030303000c043c000080804814075042c59000e59644419140c120301c29140c624000780c000d00a10807411068028100d01004012101c0003501421039400c080c1e81145c07410300e0001d51850860b0741c8600b40091007203070b171402420100038142115800102c031800b6a140c80102000b0a400c8820348005401c0e20400b007001032007d806041c108411400792466050420b420102082505d800292140c5803841104000f5542c10742015680d24080e440c0740e810410402160342454541d40c41c40c0e4844001a002280303410034000070380241e0407a58804c2c0d070110300c1c000c62017054901103203ca4030001c4032007a080c0025800c02005801101d0540304c3c0034802c290190101d5840c0034142c0240d0700550f001445004c140d82c0d1803101452641c070844007200c200054010108410544d07800c480d0090340c00c00c440040303c5c1e00b0f100e10a07030981d2120486000d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 984201411 1250 984200161 984200167
    0x6150504020c03070b06030a0f0f03090305010f0516090b18040e0f0a02150f0a0e0117090c01090b0708160f0602040f140603090a1211070f26060403030b06 68
    0x58645000034a0b100c1486070066076600781c80e080803000f612010305854400e2300408009404140354540500c9090741003803110362201001d107000d41d50080d0980c8024095403e0511503510090540e20807885401410110702e4003103d020800c441c10131103070150648101c020301c0599003400f52000f84001810014000050041d03215411350300d003050b000002c0d002503211600e0703001107003003038924007100300050350b00301d07081c0215030359007211a0040ca1614800c01c036904101c2841da80c030402048200641048400006041480310503403186034803108503000c01e908440020700c116005003100c074604e41007098503080c540380e4060315003981110302d400d491018582010a0100daa9440108020031810ba10750020764501802ca00c603c0750300b8101e06100d041c0c1070081010001c0c01162074407107941d2143c884550501c82c1c6c2000d54510036600280401845560f002040d590754410004095542d0700c60800c5c440084108031205240700b0003000403864000401103000a0b000e6040703459034030750080070641 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 984202661 1250 984201411 984201419
    0x35150a0b090f040c05120d030203101d0105040501060509061b07182f090409080409020705010509120a20071d10060806060703112407030e190615 64
    0x39009942d91014101c424090008000c07480380e0340e074001c080580700d001200c9a0005c0d02d6455142c0580380354180364000001413040e101e24000640500702c031a5000400550b29881807040f500309018040c05140b40c0000440d4440c000c40541d580c640d401005c2924000c0001410907025400503400d01e078510550340c01003020000d2484644110619220000b450f8002c0d00030041c80f0040031280c0b00708542c0b540d81c00d520607055881100c551403000d030750104206160740b402401d903110b281d0200185501c0031a0440c02c200064100d140141000c8041301c02412711030045580304d10a00c41d00c00045804030b0000350601c00e241c0114080174810b42d00341d81600d40e99203078180080410880111041c4848800c0000b141d00e04000c0a000d80000d00d0100724a2501342c020401a1103091005014840c4160b24551009030400c80302d00423588580101824404280580c03001c094140c450308003180c20140140711602000500800340d0a000800940d50b01c0703551200d00040c0210700d40e44245803c244000302d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 984203911 1250 984202661 984202669
    0x409051e1b07140c091806010e040f0303180c090b010909050f222325120203030403140c12030901080414010209041d160f06110f060135150a0b 63
    0xa0b02c03c0d410a003001101c400c6840c50741f400c0100580201c0e401c000d000e41800085000e404a0440b520b915040001e1503185d04006942141c4c0c0001c00186400c0c02e803d4041001469a0801071243c202a03c482c03c01a8440e4221020b841c0111601c09a40c202c91000421503d81c40950221000d2111404030f80c442d01d5844582d002c200d038115043d10a9944c0d0f0282141c4d80042010009440b02111300f4804c410270700d80d102c4003100c038602c01c1550410400c2e06840555806004841c021a800b800d194410b0100b242207640b582d0702c2c481c03c18842d105103020120044004001c54024400503510f40c1c18550702ea54600c03c40340c3c0982c24040310356600380f0445000d0f07100c52107008a49843c00d00316a042d21072222186244ca107115100811404900340c1c2000350340008816041a40c80c50304050702e6441c40d000352a80790951050b1000020301c0b91400004900e000804032040c0400d56115a0f281c807000090106025030280b41004500e600c0308440303805200010b140c46400440c403204c04200d6040b410002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 984205161 1250 984203911 984203929
    0x7050f042712090603021602010f0e06030f0907050a150804060e0303040515070504080c0d0807050706051e0a020a0b06040204270c030507050706020705030409051e1b07140c 76
    0x200c40e1144020b0854000d550015030300c1c2c0003449603207419031500e078291003504107010b170f2070100a05201d11003d034040a140180e04a1100d40c5020702540c1e140c3c40e1105400101050941f82d00026000f94440400d46023000c500450668050b070001c804000756a4104440418006005481c456910140c1d180394100910045000f80d014900800d0303910300a00400800f201c024004c04288001004104080f89010840427480142120300014112060400b0689481881002099405034005c040303659038000707010709001e0031521042c40d2483d480700319100092042e40e80c540c0241c0e00c41c2c0c504800245800750b555a019901600241c14195203c0300c000c15034011806004208059080d990030124440c843d01001b000545414041424080340c003030464800d81c01d021b44a1500000c070f1f00b003444010030031107009000000e801c2013149070103405d0507499180c001202d109595800c1c0803505840d98103d10b42c0302c1c0b0481c20140d038a02840347d61200d130342e1041b840c2d06040c640286d01810420b0b6948942c9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 984206411 1250 984205161 984205163
    0x12030c0a09170a0201080604051005042c0f06010f0303080c0c0a0210020d08160e060a03060510210e0309130e0a060b1302070302060c3a060807050f0427 67
    0x9003c882d0711480094034441c0c0040c011402285013004100465215080c000200d4109031400506006100c440d201f0603280d0100c0740802141e20340087c3c00070340b400586035030b5101f480b8050714a0760341c940c00580c1e5421110311010b000140b0481c049115000080000e04c442c5160b0300c2114104406980840c0e011200040d9a00141cbc009a18402d203260300580704039803181862200c0d20000080e42c81c080d045184080a0901400012803408500c44c080e0380420702600d801061914a40205940141403850107284550700304901a05170806c41a180280c03950300085501541c1024240f00034403c114441c2016144190348515440041e00810b01c003d8001a00544000c41c0f404000c40512102c030800340200e960140c8100301ca2004203a020420a1708101e414074000e0b03590404414452030b1001d0038680103200c821058607081500d5400b9600d4601060b88031060107100e41e11100e10b6114002c1d07104854120580b00101d802614040e0306c0183c0d180c05507131005207441c42e041a440910000340c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 984207661 1250 984206411 984206413
    0x10f05120708090106060903080412150906061a0703080f0a0f0501080a0302150f06010305040204060801180c0501020708070b1b070f0302012c04200d090605010812030c0a0917 77
    0x3e0150b01da03028094800902000e040c11505289107940c1d1800600c243e11400403654155021082049140c100b46204002c414400340182032160403c00c004140e140b00745424040f0b44402c110a048188064815964041d00d032000b40340d0f10b4690392072981e200106040e140d0303540c4202ca0200311031079200340c034040c2159400626a994903840c0181c501201c15148091100042c010050020700715206542c0c0a0820b28002c903075070300c951003c54050070303481c0c0110001d94205610410100003480e08400440e0040f8440000155941d00682c0c48510601480344075030000d6106101c0950a0380c02882c901806003c4084011445500e4905040d40ca0b0032242051440170420001d40d07030b200d2a0781c6d1031400d03014a07545260780549200398840f5802c04240d8041d507110911a00c0380408602ea07101d9451040c1e80543c0d072601360842060003005201c0c022a582c500e01800843c010302c000030403100c1e681110142c91701c0e503210350401040340e42244007107000300240c410f80802d00c41140c000035140038020380 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 984208911 1250 984207661 984207677
    0x40e07050a05010c170a0c0819080a15051e10080108010c03020a12090606230901090204050603070813080a090602150c1801050f0315031515010f051207 67
    0x40812031581000c0c1c2c09203042100b5804580d0128103200ea10344442500742c8a1aa41e40300c801c901a6420030803548058040400401d40c0043e50103484d600700c0c010380306503485088586d900a00d41d012103601d0020046036069262051286081002c0090446203081c00e50301010403242c07001a20706414000f07403c1c002010180104100c400034060b291480385035080940c10910108401490302d030b00c001e680944141c480b24518284121513004001504100c804880a9015010400c4041403054201802110740e0700002500099038401e86050700c0780105075034507545a41078116040c1d030015110005100403030503070200280070000101a654001d840700ca400c1450f1030f03c06420581c00c5a07110000300c10750403c0203250346810040f40c41c20868412404411009500102c850340117684424405460020920244043d071600d0f0b030304421000c6040301c000d01c2e0081d1103040321000540d408038140c00960039035401980181c00d0681842e01d070345026030a0200c0440900c0c8895015250100890880 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 984210161 1250 984208911 984208919
    0x1418130c03120906120c0c020f011e091d090a1106040807030605041110020a0215040801051503120406050313060b10031a22020904060506070b011d0f070309030e040e07 74
    0xb101c0300240180d90007100b0400f01e000342002074184607d0050023446401c40e642460507682c0240c1d180c15500c0c44000841000c06080f400140c04400300e4043d02d840c1c80710100701d03800220105040039200f12a0315015200303045140d0707101c510b0000900c400d20361191041c4004610a0020858040103501404000c05d0074185428081c601d0240910f10303600503000c00402084054001801ca1091941a03030b5400d4a5100720503200e03118007071074002c030a0550a24090025811300c2d000e03042c031624003c406480341400c001091101340d100d42c1c4a0700000c500188002500e8288504020801074003541707011403980703400d40000345001c41200410010079660f1b0180340b158a007a10b140c580e0b100c002c1c2c807099001480342a50880e001981c6840701a45900098404083d40300c6030096802000c01412041e12031030b130340c548001100824041da0880f25040c0001241400c0baa2415500030090410341c0b134003503119030401318040c0200190940610030512620f0762207885071f210304085c81e51020007401200d828 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 984211411 1250 984210161 984210167
    0x15040606091a0306130503130e09101b0507110603180c0a12060222030309061803020109030332071403070b061c0b101418130c03120906 60
    0x81c2c8881c1010404140c0c100541514001100c039080610440c503c0950401d900d40305103588540c07541c492085541110008101ca5060074081c050b058040554090240131501d0404582240c076184015110b50380b00c20b208c00c0c1c01800100f03440360044c602619403000f0400071841c15031080e0361182c0840c840c024480388818003030056445e004011510002501d02e409603000724000e640d000a03100305c0d0b0000d50049815030040948410303a562540c5412041da80f0b003130142400003c1d10640c00400d114003414441d005000303600760b0a491707050b100c1d645140d045071000c941300f82c034404140420032139900406090842d11585c2001146084a0640e074400703041c509155000310421040c1c0f43c0d03610501138540069801d50f082a84100e0554142e210b000c2c0b448005203261303c1f1107402a024800d500c0502c41c0c120309209042e4140d41c0c800e02c502c1304c5140c1540501c1840740201d8051603400525002080e000c0032045040c240407400741051140c0541c8a4550f1510700301003000079400708441000030048190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 984212661 1250 984211411 984211421
    0x62806060f110705030705060d06080714031c0c0f0303140103080904060504020403020d120207031704060e0609010906110102091801032d15020c01020703020c150a201504060609 78
    0xb0b0107001c2951030315000c290341d49424042c0364444ca40114956407200c4441c0d10100c02441200100c6116542c2d8681d01e660484824041034068051400440c0580c940716003030004890300d5655110001602c0d0320740c2840d505044000b02e04254803030700364000e000b5100c1c001074081d5001e0b004041e0b452140000300303c1101c0c1950301250096005000400159451201c0610445e4214003910380030b844a80003242040801d42008200410b50420251501c00c054094030a8900a4841e01c111380e160004003d11809031481350380c006903a07030209100b020701c94011b0f04000388a11001609021242c40001c503464440040072403801c04401c01001401a48420804840d882403d0490140d000001d014003111001c2d001400002c944200d194410440f54100c0e0032404d2000c00840d02c44041b46402501d0f22025102d482c8180041d01c0b42c01c0c1c40202010490340c2494075a00c880e002c80422000c0d90b0080e42c002440c80c500c0d401620340c884004421184114803d130702c03c14000681500703206610741290 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 984213911 1250 984212661 984212687
    0x9061c0b0a0e070b030408130b0f040302100507350a111006080a0305071a011d011a0a030b15070302061f0b040506030a09061e0b04050405062806060f 66
    0xf5020040c2003091605100c100d98100d40c0003c2550755903840e0144039698402e05074020084484001200104501200c010f0415244203d42d94030000084840803075190040250280854507084004c01e0f00262901060010183c4081090200b19080340d5070740140c0c02080c0c03034a021541c1c61124000d400740c02e014070847d000c5201010411182002c001540d00e04008400a051200000c1d83c2000c0c071a00e5441240965003842c82e201c029030310742804403040560100c40c5100200e403540041421a4401c040440104158260505080c0c40b06411000352170052219170300094450f003a007122241250080c17044334042d400610050034403e080416082002e0007907800100c1c100d20501107140c07610101c4084803000c4a000d5202d40b0b0f4151410001e140340c5c400105064904014281407100a83c1d901402942c00103041001e04403c1051006550003102c0003045c039002540003404c0d402e102e240011a441141191000e04010a601d013411903c003904031402260442c0c00e01005550300081400f030761 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 984215161 1250 984213911 984213913
    0x215150a08060a09151503080a020102040b070c1401080c09060d06080d0302120709080d27030c050a050901080c120307080301122a05040507230702010e150909061c0b0a0e 75
    0x1100103a0f032178025681b0039000040000c00005016841603100350143c0d0b0250140a01c445d40d200040e103055200c200d49031084040303a130440100d0418560003440014840e0315070301c448900e800e50b50b070b00b0003a0381d03409641007100350f40d92824080f404850401c0301c0300145038036440060362415840c44081d078141e0000c20880030001c6904080c4100c920108541014405905054a0190b1070348007005504e25103410000308c03e07801c94000401d01400c0c3d42484111038082d41c400c80fa0584500500107090000d005220240d400710a4412403814003c0000c40444a2601520706200300e0f035442d840c1580c0280c0c001114550100020800e120501241c2c449400546812180e0b001034494000086c1079540314042c0300d2691200042c007001d0141c03e00300c07421540341e80c030038132042d400501d4081c0030f40150400342d00045100c0350381c81d52820985a20409054403039601400c11200004000c10082c008040c96000810480f4070001070b901c401c8105d035010b104e207595004a240c01352018013160340c280050700513 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 984216411 1250 984215161 984215171
    0x251a010e010819020a03121e050406051b03250b0a0e0a03030e0c182706130c0b0a0f0f08150f0d0812090c010215150a08060a0915 57
    0x80c1c40b0005442d490300708000e8228419180c0d070f0f000144482e1203da0010700780501180e101c1e0000c0d64400c004c0040c041000c10f0060021204800807a00fa00803400303550082541001503280030a14440c0c60f0311a004807408a0b0300c0e00e051401c0004207440050241008808000c41000c10803801e80306070f56110400240c00c105030920400c2156948a4150016041c50394403250041e4455084c02007025921028215040028460102c2508190102d80c134903d21020084c84a166558110052000c01d406600070003690704c039000c0280c1059035903441150440220f8000080c00c0e013120016040c40100703610761135000c0c03e210602402c441c0340554a141005032520030401c810112440e5945940010b841c00400b007507668020a4284030031000c0038080c804003040c40c040b0b091189149500c142c2858003901c82e1034a2240041ea81d950310001000580301051000888401c407074651000c1540000b401c207800c1e280d032415464280901591803644c4243c0b103440920074402101d0307030031019035480501000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 984217661 1250 984216411 984216419
    0x1e041d0903160206030702280201020f03120c13050a0b19110d030b01030f02040e071e0215062205010906050607151104030b010f0f15080606251a010e01 67
    0xc0c00030b001d030000a116490200100c2c42d4284200880b80001c050b84035500e0709000e0700352120f048020240000c900620030388426005c000404401d40380219000002e81c80b140d1904032440b091a00300e18000107101030382e0780e0001390a80c0c0e1089030000400c1ea8030a941d80e10f0b031a8011105c28040d04611040c00d00c0903a02288001c40800620100f04011a103000200c0042d8540120054456201008400d030700202d03001c582003050440f454014142d03510346401d10401410180e016a03080c0b094080035800001010800e428461074032507001c2c0d00108025075a42480404005410140c81a441030a98450062180c02001d2142c0e0000c0e040c101c4600c0c2c03e060059076020340c100400c0d560710841030b0700c1d00680510450458140d41c05140c0c8224005101e68480780d515080b02098421416403196450000131001c1c44d408001800406942c0c5003121a901c030b0080c000d6642c4484400f25030482c00601401ca41883d0300c01c0e02c0000c40c071912005d001800880000940d4540c107030010030090f4a6100108 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 984218911 1250 984217661 984217687
    0xf07021c0903140c0a0308160b01090b0405061009060813050a050606040f0b0f06250308041703041218170c0307270b060f0a02030904140106141e041d0903 68
    0xc4c04803940091f0082e900c0e40360082000f1000c3c4081380041619400da000466011800d0b0000d100003401980c2c100007680c2e0300070401c040c0d0880b68560201084650805015403403040a032254091402680008020b80b03558886140c10565041903135139421803018882549421302035410507032441442880001e44072000a50b1f00f580300070b100c5100c1c0c100024003032040c25500711840f04422a22045600700f1204c1d040242a212040b14122210296005554000107800c02568025600b111219403a89440e01c02a40c82c2d40e4440c45000b03420851031000a95080400e0041d1950781c203200180202504070414145410f045800052104060940305c081644072004040000d18040c100070400358a0341000c036420b4440d82c1c0407a0401c100c0052a00c0c0841d4001000300540c14050f942006180c030040a01c1c160880c0c28012100040d1240c804042c0c850141d1000c1e020103140200c18003004c6501005100c42c561140e4009081c0c981c0301e070403002e10010715560311030f4048021740145181826061642c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 984220161 1250 984218911 984218929
    0x1507080f0601030b270903092d030a0b0702010612080403020607170c0f1005040302030a120e01021306120506060306060a020705040614240d0207050a06050a0e010e0102120f07021c0903140c 83
    0x6422940d0f003840400d52039200b11950070104180140036103084a8060500021134070043710a88007541c00c0c440002130724500305884003440b40c0c12032511420309003075500300141640403403410344d80541c13039241c510100144000207042c0c00307028800401c0e03080c1a000113241000b00070000f009602e4030300010000442d4010040f154222020300e000102446c1c1c901c9490014011414421807641c8041202080c0040f41d125a07425169a61501d00580d14010074503c01d81e0720468210b9048181030012400500745440500b62034440e50050b00c104986420220f01101c0c65070b072181e070009010203a19a254203006800001001044c840d4049242c10289000007502c501300418808070b174000380d49014000d0a10100c511294440010700450038580c0d45100039142c47c032103203611546841c04a0848030014800c03103200ea0344c6620b4003112070340c98400d941c0d01594024024000c0d030040741002c107002803c620329059102c000791100c09d4030074110f0401c5050030303c0030194440c1e40e034480e0741404032580c0c5110030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 984221411 1250 984220161 984220189
    0x32d06010e1e04110408010f0203100b07030f050f0d1103070314162d020a0303060b0705060c0310030b0f070f0c030804060f18060b031507080f0601030b27090309 71
    0x440c0c1e0f02007910f4003860354812607110540329423030155200b8428625800450052001c401c840c000307151540943d1203d4440c58400501054200c01e00c0344400340100d018001454034085680e084c03000145540702a030f00c8030505411007041c00003c0010b000e425128071801905250030004140c50070302c030b030f15804505105e80107040c4606e00d40541c1680f0107107001090030480407800e17098003402d8403001a607102400701044000c40d08002020816150400540c2d500a401a005225684454400c0400d952029010040851800c140400460690304900e402110310b58841d400c0351401030030040c1000941803088081101e001c0e0000c011070380c05413441c0d40154110034001b0f40d181c802882c00c4002d107210050705000030750503d11401800b1044e448007103840015400d80e000b254460700b00303080c0740c50101c402c0004500310031b02040c0300d441e82c0c81c41c840c4d0041042c1000950900c2000000d10135014140104403588a5150f91000d803c00d107055040c1c00c5282c40c0c000f1070524040600064111001ca50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 984222661 1250 984221411 984221419
    0xc0d18090b210316050d09050405100b1303080301181113031b231201050c03160912080405040f05090316060b060c0a0c1e0506032d06010e1e 62
    0x8102c40c034120341441102c20b081c0a5050b0304080300d080f860100d45411600703070160040340c154680054130307040ca80285440b811100b5043c1c0189070034200e9000b1641c01058240c21180080c21011001905050044d406040c00812250042c2c000d1801070054031180304110019030800e000d4010340000211030345040d29801846a405809020f81c5201d04240700d5014402c031156242c425005007010740251104c49a090700c07119145001c1c1c04e0850b0a03a501554a44a81034040001480901825000c0e00c1044668640111440e50b240d03441940d14008103010b403200c03800041c0070422407416200300c085680010005108502e48200456124002c0c2c240d00d907001002c0b91110001c11140b640704d2144810028000d43d25402e000f51f903599502e031a24402c4500005660012480000c41c01e0b910010940384400c0b07900141c100f6041c441580c1024281044041c2074040d041d00009000c8043d07070010034400c9031001c3c1031030030340001400400760100071340c021280000180c4101d0b210b002c3d10b41002c04252 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 984223911 1250 984222661 984222709
    0x101e0c0e030d050c070b0403020d03030c050d0c030c0f110a0f150f02090406090b09010b0f0c12070201020f16060309110d030e041803081506040b0c0c0a0f0803030414030c0d18090b 79
    0xa003041c1d030b240c480d588404074458036100380380304400d4240e0f0004b00c071007081c0da440741041495408141c424800d990504c80a66109044003400140c0c035205840009205001c1001010200000e18081c0d400039940a107007503070007003000c0c500d41c10035200310030081014060a0000d01c0c000d0000c00e095070010700807100301071000a40c002212600400301c648507030701c100443d11031490070403022509170000d82c0d0403801801050301d10400c0210014001412a41c6421547c482c0c0789000c20070f43c020407043e803045600005d88220400d240e40d800d40c00480c500d00a4943c1c4003410100401c00045030714140c011200140c03000b0401c0040b030382c040000d5030b01846416010080d402040005406070140340d210f403030300010025a040920002003284551401e064130340000540d1521503500348013a40c1d01442c4001ea00600019001c98000919003580443c1d4405072460045501c8890741070810356101200421811040c0e44100600140300000600c1080d1003000b1169442000482d445890031061802c03c0401b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 984225161 1250 984223911 984223931
    0x91b0105030415091b0f0f0b03070f0503151e0102160f0302060903070909080403050606030c01171312050c121306050307051309050108101e0c0e030d050c070b0403020d0303 76
    0x886001500d40c0c110409551707983d55400c40d01e000303141c0302e004896801e001c0383e8000032080c0b21a01528010803442e2501d500400c60000c0441b00ca07000107088143d0805c000001c1c1c2c145841d80e03990038828bc41100312811100000b0030000e803810110750040e01c00c4156028081100c05528000c1205480d4100c600c1a13440c00b150300040d2400303809410102205142c2001c040401c8402d40042003164403481c1034440583c3d54104041d01e0300c805507007583c0030541c0d1001c0034841001802000d9881024100b1450000f070598448400900402c4041d2000c554001420346410a00300090084410102419403a0480b00c20002440d04000c1c410300080c8003020000c150340070301900642c3c1500503104041042c0d56a0764501c003025050078460000d85004901410030091500e001d915010504440450685142d0b02c00d0f0304000c0c40c2c24594003040005000f021440ba0341c0900502d00c808070a6600d080c1c44030f400c41440303030400141d80d101900e803420800040006032100b203d10600e154050600142202076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 984226411 1250 984225161 984225173
    0xf0c03020a05070e1803070b040b06061215010306090e0c0919020c0d08010801020a0804080313051911010f0f0f0903020607030c030e1512060f030303091b010503041509 74
    0x20368440103002c0d0203000c0d004034080001d944202c2c460700318003401e6000c1c254202c426940360300c0f4440015015803901700028021804111580d50809405040340b440d01c11504420010150309440301c03444031800c0300700c0000e5503134140115409001ea0180c20000026840c280076aa03036140c90509008060900004281104081c1c00c44503802c920401590703255044e0804070f496900c02c0d00e814001c80c21220011400b02c10501c00c1d0f8514603a103844424140d2100c0d01e40c204c403a00001c10b0036079401d02514045000810900c0100e410100410300d078842031038140740003040400d11035601410803c2c0f421b1a2907800c1da2103a408050031005007030004a581c410402298038007050b401c0a900030400151041c1050f90055240c83c3d460f001c1d98030001402e552030104001c0c01c5e114201400405810301440d60420007601c115504000014500c00c009000e500c00300f411030300202d0345121541c01c040ca48200700070b0989075010310090240b901c545103240c00d0b0307034412640d004041c000c1101d9650700d6002040041d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 984227661 1250 984226411 984226423
    0xc0e0f061804090512430204020c12130801090308130606121505010501051606020d06090e07080c0301380a080d12060e06090c0904140105010806090103030f0c0302 72
    0x900402030350721081e809817064019601291b503c110010101c8036040c0e10041c400c5601c107802181c2ca09510407000283c3c1c21a0100f0407404060340e119508100111851400700316680b503500d143d54203030342c852482c06400704400c22194050202c59046c400400000395101880c1c650180702200e602d50f2504507414008018003164100980850310914014180080d0351a1005c0c0799660320422b0111b07a0326000110707003900903105a000d02c160302c2e408140009050b50080c0125908036640011200d0340c074180a401d0b6058581c1540481c0c02090082c030072900140a010100e28041c0c009001c840070405003032103a680c0522000a00356844000305402a801c00c60000c80403200078440100341e42c9400c5402d407502c0800b04c000f0045042e040380d52202c10382900071038048a1500c0c01e146084d070749100030302045a034018542d03c070102040101d80d0b490307541c9129148000c1a0005001c00943c100310000d490441c0c087c14592080035030b45c00420000c0d50200708001a0500c070301d40140c507103c0c05d11b4140d140903 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 984228911 1250 984227661 984227663
    0xf08101a0d1a04060902091305071701180f0308011d010b07050c100801090b0102071203050a0c0f0b01030308071b032a050c190315022505010c0e0f06180409 69
    0x5040382c0144030900426030070070407035a40210307604030894540e41c070504031310b6145c604014041c0d041032008001c0e4100b01019803084240c0d04c0c0010400c0001c8040501c0c90b040518011114200003000400c01c0c180d1020109000d0042c56140003000d0115202103606284144258071064500250071003c101d000e2092400c00c07140030f4410201704005260107012910240143c1303500c00d280000d005510341c40018801c0c1260a100302c243c490709a251411031740d40d0b201d01618418010541848400104504009008076000b00303080b8859504601d0000c0c03001c80058a04402c2090502c4410120484c180c203030400f055150030042d540e42402d800c00b4400c0f05c001c02095001030003944401090010120300051384032002c54074038800c4d0b19083c01404c0d4a01c49408064500c2c2d10144146902c400558010500b12030141d00343c4031900c02190b85100786101000c0111446d94540380307480c51281d007007102882104400c0325420750844850020840030301a404040c688004071810680250702e075a8000e0a40c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 984230161 1250 984228911 984228953
    0x151510050408060a050414071206090222140a0507050a0806130f0b040b010c0f0b0705130929030a060203150a060f020c01020d1403070314010f08101a0d 67
    0x140c41c10300d25034001007104840c02d50384403031403665107c599a408161031081d20804c1030182e01d44100780e22100001c09401f13030220703086a8020100e0070106414443c4442c2181008000325005107402815804040003a0403500861304044c140316400780c0210580301085d01070714010f130072079580000244494000707e400742845481c0c10f80806941d503035a000640d04400541d41884400352603001181d9280c036040c0064140d2449034031880024002c403450981001051400c1810031102032484410210305a0024031002d9a455000c5000d1310400f4604207410410f00140840800c402c0209407070f4690b50400411596000000800083c40000060f19a0034050072a08041340c90b10001b600122504001d2400752294070855000d80d0310000e11150450804c3e130b151504040300c0540d51989802c043c10090a1640301c642c2080c480300303800d1420303009140744091207030260f00e0202d9040c00d10031710a080300072490602c540d4040102800c1c1d4800d1032044161590300450b0028180002c60035508001c104007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 984231411 1250 984230161 984230173
    0x20c182707050306060a0e19020c0607410915071a01090204150e0d151e14060d0311150105120d020d0f020a0b0103050f151510050408 59
    0x148003000121034054a005504444c65503c490003000501c810750310034941521030120000741518840350803034101111182c0003500f4410810700f094180801202d82c200011251043c01200742216a5030726005070500c691260134101421b1050420b0f07000e030850b500600c0e03000404440c1515120810302d894000955080e13141c3c100741c90260b100a00f00341c003d590982c103c500115500780e65108a43c2140d1012408800603207050b002602c80d0010550300c2540015401c1d451004a0840440d185205035844c0e8006035280101030014881000070384001c00203880c0c0081040c4491003070751f00c203400c84412240201a400d55143c01c6800104603044c2010900480340034196508115103114180c4004550604da0f06003040c0a55542e07859000c40400140d001440e0aa01d560060060b482400c08074070680da180040f40e1205c0e508000203074001ca901e0750101012205070b900501440c81d203d0210b08000145040014034082c00c941d0110302148201d4891400d0000e56010b04100c03001001101d0903109 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 984232661 1250 984231411 984231481
    0x81602070e010e0115020708070504110f0c150c0a09170a02030307060b0a24030507140f03091207261b0f1507090b0d1128020c18 57
    0x102103d001c1c1701d441006020988041e00c900e001058a80070303280d800005001c1c580c035000c100005440113a9039509090300c1004003000c0c80c050540206402d44100c80200050b070a001c2c4e00c000c0c1c0c140c00814a01c2400c0c01400760203884c6900c100a4011103804421360004040300c0d0306200d08000e405d6500a51510000030b200007002050b030892410b6a80c1202d00005060f030300d00e000040320191154004004140c003146010060182e441a43c2004040c0f40403a440401c40d90561815404404e0b40480228044200308981108224070600b00c0203280d480380c20100c0940e41e00070500003421007000301c64826055250302e0300100040d00d0380f00305480001d4240d165200c8001e522200310440000c414040c1c10804a80240304c84207040c024074141da1007494480c685040300f40c02e50091035500c92000d07202c13100c274003104030044064842d8842c140711086001200a050300b0342c00260980d40000c0d5000720080c1011039540c3c42240e026a090154440d02995071840079400c0d2940d41040c2440300b68034228503070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 984233911 1250 984232661 984232679
    0x18020f0904020a1211190f020c030f0c130209031c0c0c09050f0702061501030b060f0703091e03050606120316080a090905090709180f0f0c06050307081602070e01 71
    0x10300f03601030b00c044c2008175042880d01c0c040b0710301c42e0000860741d00c0800301c00800d442c1d10032064441030508500c1555120380003000040c0c10400d1403800c86900351300c06a1840480d14001d01c0303c50303458001c0ca504614085d01d0741d000c03a440383c120786c050079400d52456031001d0801d0f004034100552690310a141d5034000c2c2d29000f2110013008280c2e20300d40141400c800141d0030f64000200f050040d40901080c0c14994035140046010b04501481640c101c0414003c4e80d91400c5580054030200e48240c403903843c100e08000319000c01d9881c884c000d800c1d1600014007000840d4020881c00d030000c4017a641d000c240049e01401030f25500c984902c010b252002c21010a0501010380c2c05010009003643d190250320f59680101070940c0c07030603100d110b03554011420400a1000e9507100450484800442e4000c1c400b03261900c2002e005003041c00d44003052041208401c000390b141d812005440203080c91411420041d60040140e40014081c1e00f41402450f80300320014001c0110078001e00c400364440b40550784500100d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 984235161 1250 984233911 984233927
    0xb0c10050109020319020a080f100305030f030f06010c0822030b070905030c040b010e120f0708010b01140309030a08100b0c0a0605060103200304031808011505030718020f0904020a 79
    0x3006401000110400c0c0c14094005c1f01c01040c41552080d2450310303810109800c1c081d0192180e42c8040c904d440000c002142840a0201c280488407140e03242e203801400c44d517030001e00401d22410070885c0e10250000620003416100500300c9094074450001030030507464800c090b10b400141000071003c04004829502c05c240d10240c41c0103405032aa201030401c1480240d42d1310240d80d40c081511614984031908140c200d0b000403100e943c04071040010892030681c01c240c1650050b03d0141d4440745846a030b5600204101440408080410b180d0314100014903220700a041c3c0000c10040214040741e035080d01c0103441c001030002c1c24a059946c522403960702d40e403031803500c60442e05035040000184e400c1d80240700c1d80d00c404046051407040c0d9106c0c01304509181d800200304409020b030510174540c2000b0300000c3c150140040000006070740495203040783c1c006100342e020a100382d00190f414445404001c0d01c10340e0600e801e04000d81c031424580c10008240c0074401980b504144081112031000b540a84a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 984236411 1250 984235161 984235171
    0xd0203060a052d011809051909030822031b020a050405070e0117040302060402060d0f110319110a03020d0e151006020601060f0e0117090d030b0d05070b0c100501090203 74
    0xb04a09090040c0150342c0c400350012017072903282141d00c04214802898004540c000f1801e912000300c0484611100300b181c071085401c0d0002480c00080000c40008209902070042c24200480d10300323030440d60020320120f0040f00190004a6001451045448400d071102c06080020000d002e80d00c2c20003c014511182c14008034001b60014605000310316600c40b03114040c0b40c05a001c0c01c00c1e80e03a59001d0060b160701021454244170358030f611003018607032240718800c5005140e1003400c0e071fa81450740109044002080404032810b2504800c0000f4084e04401c81c0d03000c1c600e60802586540d83c01545200a000d543d20741042801591800501268811031039031180d5001414051881e403102d40803030b40c0781c50174040d400c0400d1900c04c19202090040d40305ca00004814503014000030441c56080e503403000191024405988019a071203201350b050700a0b4005010240d07070080e00c003ea01d807559580ea81c035074030802e150608000751802c8502018031a07007031a55080c0009101c1941e40380340440c005d40c01150 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 984237661 1250 984236411 984236479
    0xd0213050f240f040c0c050304031a1e0711030c010203010801051b030903041202040209060a11071403060f091903020a02040b01050403020f10051b0c030c090601050d0203060a05 78
    0x4014180b04103030403a0202c901e101800c00703a8202001401e00c001081c04802240511080c0c840c00710005401f08028009940b240400315038030403d180d200d000180b000f601c0b88900d1070001c0340c090f4400200b0304a032a40003800b450118002c0080c200064154403400f218800254000400464403000c150420b07070180940c1c094450f0105444045003500380003d0b5640441a0000c00c030400500c410005000981d03030004000602d020054400038460743c0c840c0065201141003180c48020011041c031510000702618107031025070003941d90009840e41d03001010044030414080104039074400400940707074001d6070007510034542c1c0124240a9030311008100200d129509145039031500394840c2054408a03540600301701c1d440c020200400c1354118100841904110050208090308001800320f1155000020044d040035408801031504110303405083c640241d01107014098940d9114040700d4010703400c00001030f00c81d102c10000410011280d400070303910010000240250340c80482e070101c0e0703030b0300000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 984238911 1250 984237661 984237691
    0x71404020403080a030207110a06022d0312090f0106030f2609130905031b011805030324090c0a020118120e04060329011d0103020d0213050f 62
    0x100800060788640c0c0001022400148640105613000390041d115581c03042c1d078400f48070701d4010041211440d283d4020801a03008002d500144400c4481c0303e45085034000d80492249020494540c3d24451400034a203d001c0010025109440500c40b00c17400c0e01d0044003d126080e544d05051031900340030b82080c0c825950401006010480880841800c8800084481d0401e9018400c21101000c0c10040c0e4681c00d4448014400180c4280014206000c440c06421750413080318070310a0071101000c0c6880b40c0b01d010307001070401143d000030581e54405040d0745c5501901d0036541c030a020702c006008c1c1c9541c01c82020b1080c0004912007001420a110341a03000f00300c200c94070000c441402c0010f070400b42031180e40d41c845007502c51042403050f4002002401c0800c003644e0ba0303581d60f0f01e20075209214400442042c0761099a81c038500c403140340101155074034a4a12400c074940d10361205010711000b481561076070341010031516002d0442640100480041055190840310325503080da04031078403801c110005c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 984240161 1250 984238911 984238949
    0x90408040312031413080c0d030f0b03010902152d0306090a090f0210030b0d080901080702160b0d0b03011a0a050d030918020415030e07090203190b0f030f07 69
    0x181c4110045101e40e1003e00d400f176140d810b4244c004030700030b400548100d4030800c0700e00b00d034841c2049591500c6140b6039000846c0c04039140c1e01c20465613140408c5200344d044c04004001b40c1d480c4120400d940c20380109156484805110b2403070300f00d00301894030303804041a90810388503217103800103180314803026030782c20703896980318040a4104c640d1400f000b01a034108881c1301e0090b04107c03144580c609910300f8009440e1416000203107881c0c66402c4201c6020340001100d201a50740208900e0300095103000810030f0349600101074100c000240551014000f0118940c0f001c644c080d002041d01c520040d00800449149983d064800302000100c0e500403d84508000740900304000306440b101e400d659100f80d01c0d401d1007200064580d200c1480d07180d00d0b03001d01000c548030303218240395281c4507499103001440c02c0b0310914040c2050115881194203600c18400c102004102c001c14030740400c0400e2001a081c0c1c1c000340085c3c0800ca40c1060b86806218402d0a0003080b400001c091040c0c40041220225400c09 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 984241411 1250 984240161 984240167
    0x5062104050624030a0f08220305070806090d031a0402030712060e0106020309091308030903071b060e12070f150311030402010e0909030f0d290a061409090408040312 73
    0x440030840da09a4400a50300010614100201e8115403050400c60f05e400301c40f9113034108c041240c1d440380b503000c3c031740e00300070003c101d010048075008088803c0908400e14040c41d02c180c4528903524140c2c1407648070040006139000415a681c19183d004004645905003908024414040c0c5085480c565207414004140e80004035070b030a04175449907000714a056021001c1c840c104c00054034105040b06640c07824070024440f64061442a1141001183c075240241020950103c01c115010341c4d00c100b03191305003c010742c0207502003964402540d02c0c8150b81d040c8001c2c5490400180d00c14001c010016101080a120300220319010100f04e94ac18030402d082541d01255a00c000c0d50b0080c0440c0f1030f009020b07103500301485420740c03007050304080c2d034242484003e044140ba84060b40b604441555081d00d8548140c070f014040741d000312030000304440340d0011008241242d40c180114800d024a444e160110380c400c500458090100190805500b8107007443c1c0341d111a0800c0c01304540381d400c000c0b594025244 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 984242661 1250 984241411 984241471
    0x3040906090b0411180f03060901020909070e013906060510140304141f05062e11120f030402030c120c011209120e09180304050621040506 61
    0x221014590f4500309005d00c040f000600c0401c10580c110f1560a04811281d1302884040c1c45081408009661145040300300005c46600400510500500c100b02c240c8990b8000d00d42060329240717142c141c0c2d00280201e241d00303036080c200c41c0001d64400c100c4141d4041000c580c000004035803041e101006035008442054031000b0410b01b45203180182400003402180e10a01e10341c030f407400b80f44181c0d940100d902e105c0180c040d04020200007055120b40a101a50501d41b0900180d40744801c41450086884494007441c00041400d60f0100240015501410901070044d525600d0001d910550749029407292092580c0044070164402d02032414890494244104e5102c55146250007611054014500540b40e03d0508030303040c01e00603a87d1407001e0019503908042d4064180c02d4a900392040010400c20145540c024010a0840c0c40042c840b544107200001b0382e42550802c80c8c00703546941240d03d04442c404000401003091090308818442801808a60180141c0611004202c0340700da01c1c1d40c00e01180 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 984243911 1250 984242661 984242681
    0x30f060b030a09020a0b03040f05060105010e031c0e0604030c030512031b0d23040209010803090f0f03150c0a0f021f0906090215180d0b0c130803040906090b04 70
    0x3503001c00004031241e0740355008254240c4001d020b1032626468148205a980040320104c0c1c0310001c82030700100380f0808000460040109181081902c0d00c0788021a03207800180303400901c1007000b0883d03e40c05a009406480980310080e0400f41c0b11541c0303017440d07006842d503403106541074003940c07100c8112181c0f4070044900c5003095800c403461984040410000541c0720815980074507540e1984d106180c0c0901d034151258901c100d203031102506190040110414040e03210f8007480d0b00401208110740c407101100e048040c01166103411480d04580403d0821058002d101c103548410300811860300c9003100076201050300b0355940c2c0411114094207a0340c820301a5803030701d8002c1c80c2c5021154046015002100b6140c4145408070700307211554040780c00e000e000c1c2c0310020454001303d08204280c4005145a943c0c507012600081c2452007601d031812105405045892850000100c800d0303080039010742b4900810042c800c0301c0c1c0d5030750b48a0190b0001c10860040700e80181c100001070116107080d004500b075070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 984245161 1250 984243911 984243929
    0xb060d230c0a050307030e012903011413020d05030a03150f0617270d170c160320070509010b12070e03072103081b0a0e0a05030d0e01030f06 62
    0x480e00e00a0b080d0380542004002d031082540b180b0003c0618402801010b00070310444c3e8803000c0e00488982c014090300c1409a0b4907000768907043c3c084000088017410f2642154000000c44130700c8059001007082c1441e074900c00390191000107444080d40c1e03419403244070b0040f007100001e0f14982d102c1c1402c5150560b103208810008450b034541075650020101c280e40c000000304841402d1100c000824070710b5103020343c42d0445503000704c0500388240d5005403a8050b051814400c0b080945450441c4511501400040e0a940444504083c040501400d0350780f0381035412844c00c0c440c2c1021390501c107503030f114180250390240034004000514105010141c50041c3c1c813002111140b0340e15030070b08503061034121a98907803520a07a00300003505001d010300030207090860005500ea40440d07040242c41c0c180042d000004001d81c5082c4021011140c0003940e560005034a40100007010b090700050588016800859060103000c00c9800b080e50005a9910f42410230f0328184480c03001090312000300c4811740302d90303140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 984246411 1250 984245161 984245167
    0x24051308070b100305150f0702160e040c030c0f061e0e040e031603030b040b2e17090f0d090f0506030a0e06241c0f02040b060d230c 58
    0x1405109006078880500000003d1240e96900c07101c0c5060000520346824071145d0080c0004801e14004955018915000500b0b640180808500c0718402d14030804040031140404030341007050200c001001540c000c4400b01040b40c8400c5002424031485c441c100c00704001e0402c070078402a48000c2400e0044081e19284400421501407001412940a82080310700080000100483c91400d200c180c5034043e44e000141c4141030b1040c40308a80003641502c0c4500d40b0311102005041c049455843c40240c0c45c150f5070404100340740f0640383e10312618105c1d0207410140c420030481600005c2c2e81c0c43d03000b001108507041a18558000d5408200c00e0054042c05443c64009010b0350410100540d007041101600181c6c00506201c06400d08105036040c80c6418028622140617034001001411040412207034003914030503181512a4082c42d0100040040e84041c8161f001d5545940c00404a28001717000c10759600d081e0242c00c00200b15200c0c032410002000044140d1703403442c43c841d0078810351440c000c6a103 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 984247661 1250 984246411 984246413
    0x9030c190f020d060b090c0705061b0421150c0e0f1507050a050d080f16050d0903020a060507091a0309070302010305090f07030503040302010f08071d0105072405130807 74
    0x2101c0d11200c9801d84d20507071114100c14182d19a8921148600b445464440d00c1e03680601e030145c10080060000d0784202030341030548410b9242181114100c5804d0228200e000b4840e40760010f500c18800b00103050300c14a9101e076403190a0640003100401c0c90b40d682c48000083d240200300ca132468500026401551004015040c26140e000600b8810b01842c00c40d45035107403da03a4189480c0c00c50356100002041c80080c08609000c005040f604000c030780290700261024418014514011640e051441603141c640507000c0c14000c1c0208009290001801e00003481c00c00009000103406104410801000d15660900d0b5031001058030b0041022a02500407070349150011005800090000c601e2400707054400c0f81002000c11401c0d0046114401464a0f03038a07500014000c0d0220003480000c1c4180c003401c0004050780410140e41e5040095841465149004012205409000001441200d46030008400700c02e46902d0102c541d0b00c441c00c2031041da03986090401c0c60a07072108008200f010180700c494 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 984248911 1250 984247661 984247669
    0xa2702010509010306050d06063308190e0c1002190b0a42210312141503070e04030503090a0b0a09020901050f030a031808010509030c190f02 62
    0x202c0c52180c1450041900ea0311400094411042e0740700c08c172a00d5a41320010010304445131201c1d50b40300071500d000c030080d4003400101601ca00090510108012034080000c0e500c8140000161441d140080f04200415503d8515661044010080b9102c2d0f0386002514103018030009d0f1103400281c441403c0040103805541e40149103c01501c0040c0040d06ca00203500502100701003004010300d0605940f003032071301101510150b0407030b50036020201c421705135040c4503120003108003070120490360f0300a80140c1c20320701f4101c42080d80b018503544060b05001510890200402e0564080c01e040301015016043c2c070f40406964290521405604400b02c80024011030700805c040d550041d200030644241c00310640d1480202a000c40316014a40d584507503a5040d41860401c1602401d0280c80b80781008100720b0010fa0b40e03c0074000005c2c1004a0301c603659080b110041c0054001708604402030141c0d00300140d056403240c0080003d14520b100342840c402010300c101d4804c40089400044c508600101e0b50240 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 984250161 1250 984248911 984248917
    0x60f0112030e06091503012306030f040320010c080c0a170c041224110f090301021201080c0907030c0f050904020c0a14070501021b0d031b030302030a27020105 70
    0x207550302403c240840c840c90f40b45e422a030b101191036008100c3d030320f40c1410101c4400d5588da0050390950001c41c810000241c60341750880340c110b15090300d03034910380e91103250481e00c40d2101c00b03001c801302d8040b010588148005400521203034000c2c0d15448059036540b582031500e0700420640400091903074039040030760300c1034949094001100320019031910b5151a80911f1000d8419001c54850755940c540007480e0280344405040c90303140c0d100612607424074010340c2145d13004114040161300000200c50780a81e90950485603001006025056517607980c80c55181c4444196003400d00038034214000428441c441e1003418503111068442003000030701c0c03e20031a1075412010304540c20903420054100c510200300b240c458054818a141000d805456031000d04000090f8000ca065501124295094130b51200041c107070758030187c0d8000f0110303141d82003c4801c04107084030400841c0d40c1e9515030051560cd42c004500c85c07503152000744070310400011100c0d40c940403100d0b003408c0c404404480c00700562181000f = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 984251411 1250 984250161 984250187
    0x61905041101200f0d03050702300c0a0809010f08040f030c03030608030c0a030f0302040806040f0f02060d0b010f2a060b04020418050f0621011409030c060f011203 72
    0x3000703119054410f0000d1074044520b41d0036903581e002140c031003540c50745401001d0f44051544068080c803218840550002404028205165001208030800040884050340c400000400c225145071129040003501d50340701b000810b0010300c82001400c8a1030041011501841e07000131504628001900c0c121a0500001c3c0c00b2010551544000255148100040c1c540e06413442c0140c04076201c1803802402d2940da10f50580207050061108101d191004220300b40d006030004074680d0151001d2400f1881c00d034048500035400000401d40710200d491581c80f290b0100000c0e01c43e803031451000141079914428014402c14070b607640d0b4905c452000001c40c03140340060f208000c00704032010060f0003c1c01b139130055000040709498201d4815040031040c050341350014040503c80f0224101503010414450941d5a01c5000210621407221205000d5000c4e8100880046460030503081450b001b50303d980c04111134541034450440400d2a44000814650480f144400052040b0b681d1750b5051355071803a0180317 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 984252661 1250 984251411 984251447
    0x2710030b010210020a020f060a050910091b080607030501120b01051e041a0301060f06090b0703050c010204030308060f040b1c06061203090e090303070e012f061905041101 75
    0x1511041c400c1c0c1d80c0042d0403408021b802034002c520301c10b1030240c43e008004005d025454240310a2010f0160040349074209002da0710701c00300ea46145820b0219240c56034954110354016120b03c0010164000318159019050584e8184803590742c4180400301d40259900103451070100130010055031804049031a00441c20003c1100420341d03000000d000c403000c8040350003800b0b0b50503503d014685001e00c00e10000c1c1c9800102032400d5824207000034600c0b034080c01a841c0d01a000a014030625000c0c805560250500b04029076840c1c2c0c403413900a007040f80546020780910103040e03070150145090b00402c0c50580001d0104404102000c0d0b10600c410b400d00c406076403083d0340e000c0108885d01d103d1144240f280c02500c440420300d00e03001585050305001452102c0c0c54005105105038554070144030300c642d00c42441c2100e9942004440021030b0400c07500c81040442d040080111030a4011440911880840401c0e035172211640b11501c0070303110304480040c03c15402c060315244d55805101c030110b200403485 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 984253911 1250 984252661 984252673
    0xe100915050322031d060705070b2109010218041a06090609130912020604050a1217071101051e01090f060b07050102090a0f0b122203052710030b0102 66
    0x315071020100043d06003940010442d4a80104414920a05450001054a8691403d0001e480d010348414503030103200c200c0c0d2000200301e200b60b04d05002e142200d13a44004980094104021101d00079404030070102ca60b0601407524803810302e044d00c980340ca802040c0304002e580074120010003e50358442c5450a9001c0303400d21803014140c030350740c1010b00340c040d0703400c0000344031000c07410140e440d042039040c820110361000041000245010828049480e801000d41d240140c440205030f0300c0352812041240d4400307000b010400e040c0c0d0b102e400f14a008214030000c000c0b54841e05140009801c400800c900c2100c1307510b00400840e00c03194400704142111500000d030039900c1e41c11045460b400f00c8821f461583d004169203003680780c100d06040003040d14500040003240350003d0501140510008802103480e9580045c102c082085001e5a201d140e20b1a040301c0c0c0911441c01401980111190380724285c0c04c0600c0300108003070740a0100703a0301c400408017400004604021005009514150b80c1180186 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 984255161 1250 984253911 984253951
    0x903020d030e160b0702040f0b100e0103090b0f040c090507021905013902030301050f10030b030f031e0424030204030816030e0f1018150e1009150503 66
    0xb030300d40302c00500b041044441c3c0e030f44c05c580104030940c0d41c540e8445103030910341b030843c5119586420040360f180740c050074140344014444005070014040c0d46c00140c902d4820104010707512100b0003525101c0c0f4030411101300f00a031942c100100b10344007104d03c41d0142e0300108030402d0030700c3e0400e82c00c120341e8418800031039015041010b00d21040401007040402d0150f038201070880307001c5c0301d000c0141c8061602c011410340d850304000030103007003159804c140100281c81004403c54429040101844005811243c07e41d030003540841d501da003c003200c210902c1001c0c05000c0a40e0090040343d040315400c4000140150880c0c14030240d1845940c010410726500308030000010781c3e1007018044602008103c2c0074510110308003c1c05800340e84146030f1044490740700d007010a960321940c8440003903d2707207014504824410205c50028000d60010300b084500394110036078043c1d010040d400740050980d0002585100403000f659074481038080c610745224940e4600c0900ca00c164081d551014107002c0401c0b4072100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 984256411 1250 984255161 984255193
    0x15150301020d0f020406110a030e04050a02090d2406240207080d030204091b3e01020310151d150d09120c0804120807051b010905040903020d030e 64
    0x500d040f5500220f4011508101240d00100d1940c48a401d0f003010700400407203035030001c0094150310300f000e104940d2440450407003503003903050700ca81d6031001d07012256800003424019040441d43e00b00350100c40c940380104044403140d01400d012038164444140c655a45100080044850090311104521034001c0c0010160010030026402d0645d985005a4540c145031018060711140c01c0e0017000d081c41a60a001030540c0f11144480c0c280f003440c500c8070140e115031001034010b0820451151004d05040140a42d13803c10341c000c60140c1c030005240c03000541d60310b451106030040200c039900402c40105016041840711000a410072130000e10755110002e6100e5002c030a500302c081ca00e410165100f100b0070401c02414152880089142454800201580c0e16a03086200e5800f81d0700710750105103a440104108901a911341b298807009480d0703424417001d58181c50341e107008490740c0040c0200c24000b400c0c3c2003a00c81d40a10540650190103030780c940c441d00740e014118001091380a440341c1900540b45d10700f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 984257661 1250 984256411 984256421
    0x50625022107020a18050c03070c0615050d0606210b0705031e0a020706050603070b07200406080a030201140c0301090b03070e1e060f0603010608040c031707060e15150301020d 77
    0x881d00303a44c0500005d504d01070011510003d02c401e8400d0000c1061040894019415001c2d49600c001c0201c4c05c118400940b803d090415030149401c0300044011a0401400b5048441a0f40040300e0b0f80803044120b6010303c407890401d03000030740b603100711102091189101e003004550102d02241c0b861000815011000388c8e1520807034a00c444554007048220800c00c03540a05174004e0f50403001004c05500704042030466104100005203c0c1b00d00d0f6400c1c204002248190f444180d80c02801007103c103554401e00c1e621002f04400440065190440540d024006141044d0103511500c258608507800c5c40e4401c002014103101d4541d252080704000605030b81c1000405200d0340c1e0308240190181c0305028181140c006c00703021140305851a4003e2130144d00d80d5002c1d281102c00030b1619210a856500b0030361000c2c400c0f9040608403200c04400489610320202c000c000183c440c2d50104051140015242d80f920300301c19404da16a641140803440002d4100700801884800800040c5071101d21031308182150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 984258911 1250 984257661 984257669
    0xc030f020316080c210f030909010f120f0f14010f061a071b0b1303031205090607050d0e1c1e02060703020a0309020607050625022107020a 61
    0x20004044010440c1001c0c4100031031054101c1802d114036041240007600d4240e1105414065654031551040d03240c1c01013000303a0304036030303040a90790503414100c00603440760310200086006043c00e4000248a8426500d88011507650854001e010b078003c3d0b481103078050010710140d910360030706441075020030602c42a65050101103000000d11500c41540d110039100d8960100080e4180d6407684107845903060226034020382d0008402d1101803503007112540c0355606411590071a40042441145a11201d55502c00e4078000d840c1c0140043c0346038080411f0354022031f0070395060b8108202086660380079001402e500340280c0004508050303411042498072048041c4884043c800300d590f841c120b504000381041515034901040580415840041d569800c041c01d200304042e40000c0c400c0800707109a001000c00350f8010051030f550b501e6814000e544100c00e0f5890485162181046100c44100402d2160308280070b40280c200300c007510a42c1869810740307200355034600404000050050f0b4519001034050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 984260161 1250 984258911 984258923
    0x170f010605130915081002041a0a0903050d110c09041e020303090d060218010f0c0f1b03060e06090d170411040501121e0c0e0709090507020f12030c04050d06090c03 72
    0x12514000c00c5c2840e22107400306402d400c40c8104010700001042d0407500c05043c0d401112282d9802d40030704211803107a178551001d4110f008031002401a1944030080c0070b00c0c0000041180c0b640c80564080203014281a43d0060604058010401518881040e0b080c0c81c50b0008080d00d0401c0040d00c0402e003c41d40503c0c04540302d03030b400070700300d4512140700011041605080c0b03052222642e20080151140b01c003100d02512081d0802480ca0400c0402001c0315881071392004072034001503036450031002510000203002c59a008540000342c00c84800111a0002c02c0150780742c4035240100600200c000c500603100b40c565520f03c0d0240071003520355004090091a405001089144a60414503c4040321001c401100d11483e003648010400c0540b45005403880c804101c015502c03448025100d4403915170000c4059400d14040220142d00860950000340d4080241c605044800280281c1ea103c2241c002804240512040c04079003807988140c101548111400944003866440d200000c466a910884003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 984261411 1250 984260161 984260201
    0x1812030b10020f010f020307090314012c060f0c040603021c0c092d0303030b03010b040911011b0812040c0b16060b0d03090308180d05060601170f0106051309 69
    0x19400d4240303c0c40003034a495000071821f504144030010880d9806200203402e26000341801c000f02d03002980040c00c4010214014001e45403010703064a61340a034009901c400d4052031000540d2807081182c00e078800d0003c2d1541c9803a0900b4107a0590007500042410f0481c4000303442c3d50b44500040740304118043e81c2645074094158640510b003a043c21505004da007481c0503080b0050180a0316040000540341e050401150034105100824018000c0c1642194040d090810000034410721600403c030791542030ba2008800340c4406044250191604001001a01c0c1003100c6003204041044d41900a8821812680c1c029540ca030744c0c0100d07070006a0043d40c41840407480c20200402c03031103440c080d082c007a00ca5500e01c121548000e0004078543c400a0427171140000d1108004046d00c4528546030401014054a1001410f00c0340e43d03040c0407124035000c24205120007a00f80c0b10145218820462400c00b6180390b0301f441801c44aa0b041700140c0da214040a000100d0103480d180581d060065001d40044d00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 984262661 1250 984261411 984261433
    0x200d150b0403080d0903141306091208120c07020a1508060f09072d03050f06181807090507030e0c150f0715050705120105041812030b1002 61
    0x2055001540c415845030404010800c0080c06102c203469040140ba54000f0b50340043d41416200e40f8051050b1824801c0c0000340b004250300024100d40990310141e07a103004042d129500702e150180b10380130151150030b062115480020310790340d44035805009140c0c1c050420a807a40418421150b030b400c443d1394161407048006105a000e03850a81c4000300b1240610008400404134143d0100a04228100044001e6400300a4210305a03401200e289098008150f014200c005000740004e841c0311400c01e882002040103460714082807103c96054601208a03a200d80c070000400c2c403091100880c0a0180080001d036102c05482158030070000c40e10045400040124a20305024078110b2903445080420160301004a02d802a0354910a1200783c1607680d005a040408410440680e20b48059051000f0010356950040141218910350441e039180c0b40d885030304100683c0ca201c000c041c4032209088000b4003088100c5c0000800b0220341c10005501030000000c501400c01c0040d4900250b444103c600c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 984263911 1250 984262661 984262691
    0x3020703060e16090209030c100207050310090209010605030a09050a240c1d0d02090a02131d0f071b080307170c04270c031a1c06200d 59
    0x2800c984610260011550b00c1c034640e55540f68500500d00c1640d400301e075449846c1c1f800c00c440082d002c0000e154107810324195400958030019400356070301174010003280c40e414225034042c410042d54001c2040301544c0c2014011603c07500300400c1082c210303840b668000c2c041501409001c0016000f0301d104d00314034803205510700c800080184505003480c0341c004c0100d03005a10288911401d81c000440b290518020000a440404100d402035448045182486098026940100040001c03241131001e41a170316884c4c0d148440d00b14002d41043d500382e00c0018403c004410101c6d07402402130425002c02e00300300841e150095003103842150541c00001c10304c40709a8128003504440041069010681c0c03505540d204c0c0180501d200c1c803001c2c00801a0882e41c11445980ba80d8280d8160800400412a600c2c00043c003034882102c44140001315000c080f155403c01400800000b1f007070940300e00400c083ca41d258401402c0d085801c0c40541c10400c41c8440056114000f0a00c078002d05101094240d1782d81005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 984265161 1250 984263911 984263921
    0x50417030d05180703140304080609010516020318011b050102030a0b041a15090a150e1c0b060904080c071d06030604150203040309050406090e010c080705340302070306 74
    0x8200344140c405640001880021070800781c0ea0701544d10400c1d0606c1d030740036618601498104c0701c410700441d800c101d6401c42c154016441100d01c5466000e0741488034105985a01c00d0280b0010755866150400030306501a100e104038190700a4200c20b0010b8803a29000d08903041a00c40301e030300c00d032203003c000d00901e0715000d4100c1603c0007001005a01b0b68840c00605008450030019154202c08140b10244d9035541035600014860030303c900344150492240200b030ba04c608800d2901c00c0c030300038400500d052041842c54070b1a540c0944050711036280c5104008001e40d0040080700d4400b03003040f0700041d41c801400704800a00311114041d11401c0c0b00e10545d05a4980185041c0c000d5000e82c0070030002c280000f416002c8980c08803001a03417912181411070b404042c0b5008250003d0904030002014451580a0f000b441c0100000b005640061036003203400a07000c0c0d4450300010700620544a25007a41c0105a40a00798501c0126480c48100010040e0804804090700035070070180041003440301d18081c6c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 984266411 1250 984265161 984265171
    0x5010503101208070209010e0714040b030601030906060b0412020a0503010b0f010c1b2418050f01030605090709030b01080304050d03110c0d0b0a1524050417030d05 72
    0x446411450000c01c0c82610300418840e180302501c0040728078003070080381e5040340c00b07003900500015044d43e1141c2410f40c005030280c41341e0380081c260300c444151504800c07003a0b50603608140c140516640311034004501800601c90181c0d0540e5a5500000c0c8000032100100001c2c40c0303001010700001e00500400c0000d07000340d8011802a41000c49040a998605240c031a500e40c0908148001c0d09050410148400c45e608052040b0381c80000081000c801024510902103000880c6214030b441e0358400700c0c1da540c84100681d1141441070741c203008601c0d090102e0940100189070010b000c0350780c6c1c40061402841585c00b5404204508002d00c14400c4d450081c502501b11000198540307440d040100d01440382140c00502007140c40e10f420141d0341c800384406034025a00608521003040a420b0a460f0884181c03010088146420f0b1410781e55007021405100300c843e40e100d038042040c0001c00000e2000401038503001001000c1001182030301c004107442d0703a03048030320006548454035501c0c058111240500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 984267661 1250 984266411 984266417
    0xd05101a150f030f041b0603020418020c0c0105090402070b0f0105030d021209091012060b01080a180605090c1002030c1002121807080d0210200304200d03180501 71
    0x4201c07a8010502821250040704809180e2a550f0300d60810040c0306e1103299100450f9480120000355055050f00a8030507200100812442600c4c190001412032181d0440760034550030040010100e9802800034119158000d072005d0300d449039640d60102c1c0103604580403c541c4142c3c600600c510b0508010030308803101c55000400f1880080904540c280c0500990184140081c4001508140304101800001d1015106001002d8004c1c644070b006007a610030614005010000000e07803e01941c01000e040d00b4204070003440b52071b1a42c5802e000382400030041e03001d5205940507104e140d190002d1040c2c6d0307000c095002d9916a00d010143e03d09000c20000e90400f52801071145041d110380c084003560704469042605030004031030b4003801d030512903664020900da000d02010045029004690b51213320075440081142560f070801c4000d00c0304440200e42d03042c20090000030f00040820781d101440400345900c2003815900c4000290000340140707011400582207460103214410381440400143c00242 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 984268911 1250 984267661 984267667
    0x6010c0201050d0e06040c0e0c0f0901021f0c03240e0408041509080d021501090209030a02061b0708010c021507020f06100303110d020d0507080708030f06090108060f060d05101a15 79
    0x9403274506540234002d031280d8924400900326156a0080003081c41c20084c1e9403000144115040c0300c0001000b07103107011001300e418641c5401d00c00e031a2045401c0d10900050400e402d2a00b000d0250381680c50081080390f03000030802c00800c0b041c6903254080d0041381c207070f981e01503002d050115030340c10240424076030410341d800f54080f80d6850646a081c5410355548a0b001070b00d8130041d0000900d01800e0050207034100c003000031003a8002c40c0c01004608140020011109010740c0d80c5038850032510505140f43c0103800010032040c5036040a080950408003510441d011041d8036002c1505080c0d090700e0b10300c03400765a01000c004040d0001c03541c0c04242d0004010340500c0c15050006519907c5e014130400401100164000420a0010580301c9035074010840da03840e0303d04002d0358000104141e442510400501000080c540400115070344900f542000011240d10340101b400604406408100d966000746001c106a4030307414403568610200317451b0b81c43c40350444a4180880402c00f00f25510340300100b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 984270161 1250 984268911 984268921
    0x50303030a062c04080a0c062901021f23010b310506031b070804031403030106120b01260103020126041704030507060503090105180606010c0201050d0e06040c0e 71
    0xc3c00c001c0350300c0381c1c11010090fa00e846400080740c580c108804000c29a0b4a029021242c030052000c0c00340030364000c04038514031004c40303400590b982c0405040d02da03d9203031460303d03404508109400030105031070010000c81705551075007800424040242c0110000c2d00021401a0743c00b01c0e2043e060224200f0380703e075040742c45403000720b80c0714814170342c0185405110000003141d28201900f035091240c01c049031495848110700c1c03a0146c000d900c18031040da035500204207040c64401c804001c4074100c401c140c40c2c501c1c000d0011608130b000381c11149011b905200701c15075490510110145c0043e01040e441035000300035810f43c0b0002d000503000303403a02d070355960b00c0840f801208401041002d80050704030310089851a18480b41008610a9400050640c00768030400101c15800101450140740004001e024a54421441c007030000f2226685c01100c0e4811004a0000c4d4012000c03001128010b1600500c1c1c100c0700c6501500b40c5205601e400f4640d031040c000c0100f88094041c0e0400035245050303110484d4104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 984271411 1250 984270161 984270239
    0x150f03020d1425090f0e060a09050304050409030509041109010c020402071e080408070501021209190b03090c09090c03030a08130515010905070f09060c0c050303030a06 74
    0x1c044020801d0601024800c03005000304401181502984103001031403e00b0040c0e4207003440341d441507800c2c0b64202421201c080c1c54038000c031070b071842800d8028001541e8000058024001425061340c250108200100301c9031114000c2c2c1600901984445607900350b00020b00c400c940007004c2d611214002030002c400301e60f81c00040134640540480b00585c03103100c44d080094103480c600d41d0a07407040443c45054000c10070001c010340101ca00d21026103024544c1c400042ea140c00c0c01a444145401b410002c85420f850030526400d001c140d04850350b04000c2e200c81c4904425841540c2540c542e9100300e1078650300b032820101051303201d9500d20103000c2030580003000c01c0d0b43e070080c00311400600000200051101310381f07a00b040b07140354221085070125060074809810144d020f015640405052500040500e80039454070400725820b41d0b20115201d247ca0001c4804803821502201c0c0405601c900180700d030380400285028564441000030307014500007881d10002140c21a001c4410700c41303032203c840045 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 984272661 1250 984271411 984271429
    0x8120a020c041b0e061207080603060a1103010e04230708011a0a03140f100506041a2b02030a06150f0b091e0303070501060806180705040207170d150f0302 68
    0x1105051080c0b10b1801c40002801e42d0049a51b14500c92001104014155030b0100001c0d0061030700341c0c240d0715991110b1020314281c41c503040500664003410801042b50103003002d039076903010780525a00c191a0041d03041e0780fa0b400300034200c200c100d41e2120380d061080c1003082c0f203040b203085641c0108008101c040c4001c144031203418032000c1c00c0070b40c3c071030032840e8503580c20711401c0d0041c00c101d0203551010200030802d074000d01303060300d02900591601501c1241440303440462181d0b03150041451414500e541e1034591011b082c7e03044400c01712486805030300161800c0200e07002c11485100c1c049080104040920901c0e5020391002007821410201040086800c10440b10344810580701c046c0c002000161030b02000000446a03605440001048800d00c401940030701c080e02d00407001c2d83c000781c07030f040c00c06d40c3c8204401c2c0c0110003981003088108100d203003d50060404c2486020413400c1c0e0380303010b10f4070301c1035801c00802c0c0d42206031111001c0851001d0462400041c0c004001d201e82c6050a5070003046001c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 984273911 1250 984272661 984272711
    0x5190c151b03092610090f0b0424020d0f06030f08090d150504170309032b050108031e27310e010b011407030908120a020c04 55
    0x8104800700d4050502c02d10418002d8260781c400584004000e181c0f00c203682c402c00c0c440402600460b9004080000300d4040c1c29407842e00500000030118840d01d40c1500a40d02500844114400e04c120500200d2420540c0c801c900d03448030b00603100d035101e06145041c0c45111074103c64545c507020040c00003c0c5080654810783c4d8200c1d80781502c40c0c003a0400700d0007030035580c50301410901ca02c440c0600d0400c0700e50040d92045100d0700c0e51382a801002c0c1800c0100d400140d131800b91a400a02407500c0d04070808541c0740c1110702622035600a04860b06e101002c4400c01e800051040d00005000088a04030b030321240201c036040c4003520300e8001da00051420381d908442290482d440950b056100c29990130b48403800340307180c5580b01c81e001c19240b02000318240c5401801e140807410640d01820080042c8964483e444060312601d2144d0072564a07440e0b103900c400350440522600b01c00100d8104401c000100d82c0461001c0542ea46403481040603203000c01c400000c0348520f042c62007502ca640c824003d1500c0c25 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 984275161 1250 984273911 984273947
    0x801060831030e041e0b030c0d0609120203070506181f060911190e030a0812040b13030e01050c1e0303071b080406050d0905190c15 58
    0x54552036a5100e11900030010311601c0c1084403800c1c108040855000100d041c880e0b00c55038409040c1400b0302041e00d8144c01509101e9201c000c685051180d0f130f0f003200603240402070950340c0101e940310010b01c80e4050071200340c03800c0307a8580158080013000c1141c82101072580c001181041070076a58a0340d5038800034403000030700d046542d60140442c4208410100c1f005007515480354201c903800c84500401d83c9108034592107042a0752445100c045004580c0002c040f56023120f020301c580d03441955010703000c104d1680c1610a608503070000c12440c00c00b5141541c5c40200d014840d0815040c8513503603000103058640b100c00000360540000b40c100c0c10304e0143c00d1081c20081d88070000e83e680d85003004003a03128664400016030005581e100084003c5114102da5200c2442d01c5d466003481024150a8a100403c1c5100411040c41110b01600181c01c04034003180b4045100c42159441c5401d02c006000c40000101c18146c441c1f08010030f000000c0050702d501a81e400706c5501b0b40b80b00400e0070402030515040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 984276411 1250 984275161 984275177
    0x1c05010e0f0c1605101b0309150b1804060204060e060909041b1a0405151c020706060b04090e010c1107050114042117030103080d0e070503071d100501080106 69
    0x150310302243d003025441d50000c060310261501c00001c8800f4055030703c0c0e5540301141251180e01e0140c06449002c00c800d80266150b4a0025500c0c0300c02e000748100003080340d00c640000340319920b205806008070b105030b101e0780025885618100c0d0161000d000c1c010314510415040c4100125034503084800c40d48a60001101803010245001045451410740c11040150350030328900e080501e9034200030011a41c0c15200a010450185125006406501001c5592100b03400c054400c11400d9006006181d000d6140000c040e0f99039801c08042d9407065010b000c442d0b49542106501004c00c2c845c140191032141881c41c80e00802042e107a0b181c1005000b030302c5c1406011f514502040507031a05842c041d1482d1014010a0002d140d0640c41002c80d20b01e0855440002c1007030500b0804400003945d041b680d204030414100f414042d4480b0141c16001c9d8482094851b14000050680d4100b26041c001d2011440202c840c140405484000b00300052448001d000c900c0000c02290342d000041d1411216941341c0281 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 984277661 1250 984276411 984276427
    0x902041e090c081614211305030f0c12070308010e0f151011010e06160f020309040b06130f0501030e06061807020f0610060f0f21060801021c05010e0f0c 67
    0x2004006040300c410004004500003420803205845c880c600700d680c401c40f40306c40e540c2d036007030301c442018034800104903030424807001103000c00780e40140010500710004d0780d100b21054100680240c01920041c0d0000c0c0d01080104001240c1d01886074004043ca01c99058a140442c40c90702e8407040c101041d4012602c084800700c00c41e1146030080024061440240507403040381d00300c19a28042541d0106000180d0300810580c503004000814500729550040c504002e84107081100070b00403a01c40c50382001c0b0030064030003041e04204040002c6d01d00011144012814080010210342d03131080746043c507621103c1484120380d680100f00664481c2c0d2032061480342d442e448201e0404150709603607202031081c80c0501c1000c803d03000384902031399040d544910070f154801c442200c103204800041c2010440a040281e89940300e010005a0320208540c0403038505d9440b041e003030072079104000c100603500b040b04055602202d5402480e0051902070189105810925034136482000e01500f070032400c0400041141e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 984278911 1250 984277661 984277667
    0x501050307120504110f0105121b0c01051008190309140f0d0309211208091c030e011109090a09061d0604030e030d0509060d02040902041e090c0816 65
    0xb0403008156402440141410f16100c41d0403c2c004400c5840f8400b850b140300055440b890659400b14403441c1119500c1e20303040307c44641010380100f15010202d0400c46510090380c240a014000d0709404044940751340303031034116800e20581078060301080c0e03468910300c004039501001c01c00130b0300d0300d84980b001203d01500c009191100c90000c445c0c0c110a00002d6042490f41080120080710382e0802c0d459200300c04000030480085900c0001412198015032060550348500e0449030301c08600000c4501740000220750307604503122007003403a00003500c82c0c401c03070039200007030085494003030009401c1da05250184000514504005003601d045c03d82c1c0712840d000303001e010781141c20207040d1100050781414400f20643d40b00c840c100e9083d000300d016469402801c3c10005503291b0100ea1039039826090145200804c0400d510481c4a060040d4003400042401d90f980e100810041c4082260310494002541040801544c1c56100300700452509945451090300f2004441c0d00050444420700566031601060b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 984280161 1250 984278911 984278927
    0x9130305091c0b0a111e070f060e07030c090e060610170c04051804020a0b070201030608060108070312080907030f1406010906291225080f0604150501050307 69
    0x382c4001c1c0d10340400c0c8003d010340e21503058020f400c818801e00104075854200701140c072940042240c41c0060300401e07540f400111014000092054552500703d5030651038800030307900c611884214540106500300100a14200450b0041004041c10300c0059010110b00d034417040010403040c0180521000c44d40c1042c46039005201c2003410103104903482c200b1458400d1160040c0c00f4284c0111080c120300d001c041c0781602d10a201e01d80c010315240400c0c0c148140a220364101d650200d05140c1c07254804104003906001c81406408440000d142003850b60500c000d0308540c03d102c910500c11004103000d0b440501103403400640e500000a0143c0548a103003540003c40203040408890045500110380c15440360000070031542e00c1030510b0242c0c80806810a944000070140c409030340b0f000c0004200600d07100118650100c0c0844c01a1505000007040b40c05440211102c10002141c0702d08200d6001c0d0142201604918107460400440010351b441035800b0100780606410700801100242c0340910500c0e03c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 984281411 1250 984280161 984280189
    0xe030d0f020f06010905060f0301140403031a040905060f070f0905090403210501050420040e151008040203070906030b19062117030714070f02040e0c040b0913030509 73
    0x80b0f9403d9039560340c1d0800200020364645220f0350800108039020310b01401040114159070703e4030205074849580c154020001c04e0f03085646199032040075a1159241d2040c42540f90080d80545624504410042c2d60210018003d5080c00700c02850010720302c3e404404d45098641c107855035501500c03142030680d500580420040b40706903030048a10364840389a00000e04036a4261010f01c0b0b4213001200304030050714081c0861109880511003081914500c03001c0c960040340c0c01e180b5106400e01803010030540f0070251811004505503c1c01d0108500f401c10400e0020408080c1c20401c031030851b9100645080081c2c10950100d800381080c0c2c00c0e0340c0941d844a00140400d5007810380d080c0c0c800030803840d01b8101d40340a0300d00c01d0380c10800c0048070602d8401c6a201d18059900d228089000210002e06900801c0e01564035091001e012001611180f0500a0310b265000007013101c0c1c0510410401510200d4a03280d00032844903080c040c4954070032a1494807664581421234a030031020780810640702d00c03121 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 984282661 1250 984281411 984281413
    0x30c02041107120f050c10330f080a0b040f05010b0907180f12080d200d0b040c02030d020903160f0305120406050a081915150e030d0f020f 61
    0x5194010003081204600f01d440745a01c078840074008400d010b0710303603001c0e041d00d420081d042041e444c3c08500140d884401c1040454080321280605070429601c1c0744c048071b9152151110144c418440a82d04281c80310040c2007080050602411070fa440800000d0f01400041c40c1c41c0d0b80c0318072901080006e401000311150064107000306031900d8000200840306500765090340b0f8016000116102499401034819200010045042d0f01c0060b500c120440e4000e040c40b030501c584e5104451864609600c0381c0c0242e0301c95001068950034800b00d04401c031510440714902c52443c1c05a6a03501c030790003006030386e00c0401003000144c503101d03c000440d04041481e000d628901c0c2c1c5613000412190000300c610f2042c0c80c0240c0840b000940742c40080e11007032085001d40700109809204803400144074407903859000c00c0d6404507000c99682c0070340010507030701c51804245046007000c0040c003000700314004100e07038854545020480001103c020a40300d90002260804000960000051880c0200240c4080780340702c40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 984283911 1250 984282661 984282667
    0x702031c050702040905030d0b06180d0521090f03030702092205030318010606020609060115140c010f0b042703110a08090a050f100806031f05010f06050f0304030c020411 75
    0x2107801b5459510403803203142154988401c10b5424200b01c020f03600c1d001c4a1031200c0c0c91205080e010481125100d05037100d136482400d03075160300b100000c03803411880f450740f02210341c984101750100643c812071400e0b02c0380030ba4818440880503955528006400c1a1800280c20a0000c0802d44404d20340c440040074020344000410301200c00d56011180d8000e641f030078000c100c81d40e02c90078202c0c0c03640404d44201c0400e0380000d0041c0000400f00c03014400034600340c1004220142c0d1000c0c3d02c1583c0d0014141684165074640d4400c0261080707005440c02d503d4112020050042d0550350802d054906c15060420b0400303001d41d80c004c05019441c0381d440440240201e900c4540a483e11980b154040d0b0381d11402800321100006060901e0480400003060042100700040801c0c1c2003100c1e0001c2c0103020310b5251050300aa82d60303034801d40c0b111828460b14400045007540c14515206440c2e041503003c5001c00c0410030500112002040540341c110794180340c00f11142c20503000050181c129440d0b2000c0f807206c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 984285161 1250 984283911 984283913
    0xa050c0d05090c040c0207140a0303050703030c02010f0504110102100506010c1112012a0e06030c2a07061b0203070509040c03210809010902010912020d0c06031d01020702031c0507020409 82
    0x402c1c030704481c808e5200300100003030f007414051a88480e100050219100780800350002e4080c0e00140c20305817440c4000a02803008822100c2529001e03541030340c04080c40321580c0e0155906125407240906690000c0c443c50601000003003164040a4001d000d00000031011140781c0c1e81e1066440c0040c407014000c0c01408540c000021518419100325902284080690480b40c1d01a203a40111040000c1c145410741d83d940750a81007c0d4840c01100940b101c5c050000c0c80000e40341c2c00c04082120119000303114850401c00090040c044545c004142092005d910100595000445606540056407005d400b503d4030300d84281d00b00740c0317a00018800c1c0c10303651100300001000c901103100d4000c00c2d69118003a480b0301a02ea4201e54148802070b001440802c01401406010901409070b180301130817001d491401d540387c4030300d50f0080707400c50381c0080c0c0c0724680400300300b50803201c51043c030030030134002c5240440c5940040d6860000d07010a10602c0451f4060380b8900303000d070064034600d6030080c006000140d11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 984286411 1250 984285161 984285163
    0xe0112050a12081e160c060902030d0509030c040e100213080709020918190b01020a170a170c04031716150f0603080403020405060607200102060a050c0d05090c040c02 73
    0xf0845100818180100481118240c0c2503407a501481d510102c24680046682003281c84650300c81051f0381d003540f54240000141c40402800c1d40c40c42460741c500340ca0300c40c00c40c100f42c1800c0300ae1400c0b6109905115141900040110320100310781070351280140d50f403c2c00c01032140002d00d26407000c403040c0940b4400185980705a00200190881100c0d6000c0c61402d008500708a0002900c4034107c68020900000242c0c0c001d500840ca5a1030500403180383e92000d6507160203a4420240701180c020020a52404860304207900721051760400448030301619100e07004003030038000c80c0710160441c80c0f6000990105088441220002c5207105c01505580c000f500741903040c2c0c7d41c00310700c2542139444c102058000100c0b0344604020b40b540800b00c1c902c0c00d441c46d02000040c2001a21840d4007000c10070000b000a00c4100c90454840c2c454510306606c1c0150b103001909000340103060800c81d03800c040802c04200755210458030070b1043c0e4600003c1d0f84c0c03650503501d8940074030801201d802900d0981ca1100443d0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 984287661 1250 984286411 984286427
    0x70e06040c170a0f1107030c06060b07020603040b040f0b010b1b0c01090902090a17280201080a0c09080f0102040e010801020403050a08220f14010201060e0112050a12 73
    0x159400c1c04100000c5004582d20100124003010030500d240108080d21110b82024460902d1440c0124000d44444200c08241c0d0240404902254640c0440c404012030f5028107401030095040b51030030090b0030b8011802030b10008200604541d030007c001010003078081d0b11840303a20f41041c0b94245c00c0da112040c80426509c040c3c0d1034004860341d00b009000c1420002400f001d6007030180d5503142818a06284040130790081000254013522184011400c140303600300f2142c0340c00400c0001c1031140521822852048604003400506c908030041000141c1d822601c40307074024220410005420b800f45108441f803010319000b40035140038407009001041815006041526424804c000d8181d90300e0031441c1c202e00c65840000d000307410405600021420420203001409050700c1c0d4002044440e1910255006658020740a0100c00741014040b29103045808003404000f0b000030444581007040200c0300c044144201d0110305405849003042000902c840307043c02d0f6010710b00c0061010900070150400c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 984288911 1250 984287661 984287671
    0x81c050618010b0f0c0c04050403050a0f050405060316113715020903070801090506011503021e0f0702031b1816051602060313150c02030316030608070e 67
    0x103200003a6030003040c803405406038121080c0b0b2003040c4c500000d90340d01c500c1c2604003912020b0035015401c0b41198070b85076030241c180b00341d11983e111a07550003401d40c017030000041e01c560320b002c001007803001384181c0d00c420040340d412502c04d41c1c00c2110b0b84035400088441c10400760310b152090040c0d814012185803400a401c090395a417031810740345c06000d00d83c0c00f0b40b41106080050700c581d070083c40012600d03849500400b641d01c005400c0c3d80e141740d100c10000d820344401c03010880d03c0b42d0100b4010400c8060010490200440a242c103510300b28001d030080d100d0482801d5402d070300300340003c4e028800c031003280d085609669010f015030725180000e06250071176a0500c1d007114001d50706203510010b80c402d950720080c81913486030104001b098139500d088880d604940b00b8814203100510320705001da0707208000740d03224507450142d1454007501d5240103041c130780f03c0004000e8032038100f0358290703940c03174020003a40d60020395561410950b106049003100076001c143c0c0000d050b07000e400700210f00c0394245a0380906c54 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 984290161 1250 984288911 984288919
    0x3020d0225021201110315010201060503150403081303022a0d060603120c08071103100f0213060e0f0103110d09030c050f060103020d02100201060f0b04170609030313081c0506 77
    0x4a61850f900e909032180032954007520881000000c4400d0300d000c6081c44808018030001031040e0702c40c0d01082c60200c03000840d40c0d2030545003080000b0158051201e55000340003118032039541c03400c0c3d83d0295a528541c100c12080003004215083c41128200c0e0080e55003038000c00a02115010782010801400c550100390707103410306040a00d42c40f40c0280074101d03036194402100c030301d07019164881c04034680c003150006506004131403c2c41c500c072006004202d08807006002c01a55907143c01900c3e080d000c00c684c0140d050001020501c8899540d040540c843c124080c04c000c104000c0104161880d449480e070744007641894007001900381a4000600d504261041044641e1030703d0140c0343d683c1c0d490f0300744802507200c24091001c000608103081e2042b9440c82900020036056101d60003484c0c00c104540141c02c0600000c01d04021804a10b0b8080300d00e90007110141a1505103904019128440240020701016090b4030710300400011500700d503d04002c104502c0351140c0d08a400c1009090240d420a01c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 984291411 1250 984290161 984290179
    0x1211190c08010b0105030c0f090301050a0c0f0c03080117010b030f060709091118041508161707140d060e01320115120e03040f0608090d03020d022502 66
    0x107420014810381a01c50016180c1a06642d1007011601c4958400c1c140c5940164050043c880b0740d8409002d211300404000502181c050004040101098401c0304008108078404211402003500440605e0556104800c5142c040c004c204120380500541d0f10f01903014803517034044400341440031400714021240380c3e440078555507a4208007015901c0302c500c1e44402c10000c01401c0051035100300300007041407010300040344480340c2c40c4611400c8261940702008681003006441084101c4004c02c001500000c8a050311611103c03104a41d02c0e1028040d400c40c01c000714103100144da9414041a04590f40f203074040c40004000a5190301900c3d008103148260681c0c41d071145820038090503542c14900c14500c3c00d1007a40e00c0c10004d201d0180e000c4800c017040c0700c00e40c5480c5041c103c1d240108000f0b41c414000640e07483d440c04641c4058001140d01040400540c0d0040c4030206a01285640d012034040c5000741c0c49a1003480310304000e1040a50030340c05c0034415184052440703503080180d40312500032207a1080e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 984292661 1250 984291411 984291419
    0x30403080f010303170402010c21030b0d030522031421040303080f0612030d05040b0a09030915121817041503090503090d08270d1211190c 61
    0x106550300307003c01008203001c414080e249138041c400c0c15501c18014589504040700e17a407990b048422464104080072a440c141b00c2c110107416000e24103284d4400d913030198074003040381c078020300c14002c02c03281140c08410242022062002240100003454200c10116180003200e45915600d01307501c0070807141c0704105111000800700c550152004c903070301512151000d40d01c190124108a10007841942d101160503401e00d03800a0800150045141d1143c0008044c01c0038200107000e189c004000d0801d5a0070078000c0d0380041da00c80b00202c2100d2490140300ca41e03c2d0766620a81e0424464081821418504116404000c00b84154918464011030400c0210030303800003000042e1243d405400360515207000010300491203580302d111068040c2c030030391741810600030001d1200d003880343e015500d03a0000300d08004d50647e218039403107841c1c0da0303823500c0030101c01c0010100d00d1440405502030070039085200c0041a05004a9101418100c040281c9000c0d06081185444081e61200240c456060ba900045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 984293911 1250 984292661 984292681
    0xf090f031203100f081c050d06170312010e0c070b091c0905120a030207140102030909040309051203040f03020607020105090301110c0f1906090813030809040f140c03090a14010203040308 82
    0x104400c101c1000c1c645011b460304010b441e0b0340d02072902c40301c0140c1d491500040305c0030f00d2580881c642d103080014507500c0203141c4d4204030101d0181c002040030416401480180c00c000e0003100d010a9001d20780c40764503900d0200403420161100c000c92282241038070031000c0311740c1c0034140c842500c6084031000c4e00f034220b4507101540c50680006c0200542d0100ea002d000703102e100b40e911051010148116450305040002240429070203507000c03800704104c01c0f0148181d142240400740031600c5000250700301440d14070340c0e00d43c004a512003c1d0040c02c000410b030013903911420466401c05409030003448501500f4045080c44e5020018040740c90150003a0004428070115052a140c2102c0a610b0011811703a12400b00401c0125000c660781c500421000d01900c4102c19142c0041d0302840e6070903120704440c014042522104103042090b507103010307800c540451856101c603402181101200d03440c1d0752500300d000c0c038000f15124003900c5207807802003040c1405415002103100f03a200c2d940b05070468039480140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 984295161 1250 984293911 984293923
    0x6060f0801050f0a03171b030a12020706091b1401031a121c0f0e09070827010906090c0501030b0112111912050c0f090f031203100f08 59
    0x100000c0c0c1150010002464038211405046000921050503540e076661268580804140c18040795a4041610740c500b000d00310442c0100c80500b406075250102c0502c2c000d00e01003203400c0741d05000b41d004c9484014880341d6031152141c00da1108040402802c0814007405401951081d44040c0010380d030741c1c4646510a0240e01007290f001c20300301501410003c2008280c00c2c0d04031100c0e007280b080c0f0b01d10104424a0b500640300200c8980c40d402403500109000921000420300b865005100303441c01e02c4403003a44a0901c1d640059101c055901140c1c0ca15850b04c00d841b1590000c010725807d0508860601c40326a004200c114420103032083c910f55580010340588550018480c00308045a0603003064180e16005500c032021031384c160902d01250354001c88841c0d10300701c0024000860041c1c0c0403070102c6082c41000c0d00700302d09101150805000033003100342446681d580d240610111034114240f03482c1000b688604d0391001c494940c50327152201201713201000c540324560b4011000103000440040200308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 984296411 1250 984295161 984295187
    0xe0405060c040f0905040503133b0109020a23040612060302060a26070c14120405040e03040f030602340602210f0a15150c0302120705030d0606 63
    0x4030f8551914101c4404024000140b0944141c00100000d1550810351010803024200d00b0701c0302c6c3c1d074a5144650928070581402111003c14035180380c5600d41c00100c1d103259046501d2042c1c0540e0b15444110101c0314002002c1010348611003100c00b02075002c8a1502a0040e40d8495440c0040d548040c4905001d80e8601c2c44081d4022400300464100c2a2060b0441e5580c43e5809140560b031040300d04e007071014001d00f01c0d046000540741c0c02440c0200300c2078454180001045000805140060036041025840740d403254910903541d0b4031404940708400c0c030030b840003080442c40310b1204559074208500658031886142c00700d2060340801014183c0c25014a80080b81078010046608031985e9900d4025440030344030b0050721440c14015a42015440000740c410311200c8420f04460a1140c4e01c20140c900540c0b00d0035400061400030322902d4040c0e200c4030f90315015840c04019100b81424107070305050580e030401c18940000256042442000801842c0580700040200200d80d643d20040381c550720500a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 984297661 1250 984296411 984296429
    0x110f03041b031a01090e0f0d1209140706030c02030301060f0327030c060e0a0b0606030403181509050604060e09090106050d060b1507050a060509160e0405060c04 71
    0x1050118008008845806040500c03201020703880b500c0d500340ca50045010300360705030301581c0140103201d0717540035100158190314014445600d0003205182c80e00300020001c01005a03401c410040070107190450300710182c00600d500020f41504007101d880e50502e006480100341440d45440d175103480002181d048031030a60702d804030032400800031009044400c1039450345003803803140055200c020500e01e101a5100341c840240b40725052901c4c03c159180e00c6040103068001304061004102183d2425038040d004991a55803079452381303003c1d40d402c0e040104a2015010202e03000c0303040c1411160901110b0500e485003030000342d440042000034881c070300171000000e06561315100700b411b14443c00c5410030440e03c00070070507549a8001c02c0131245440b0b0280e42168841301c1900706800c001c802040d0b0701c0c0c0e625a2131442e098a0b9100e40d1f90350045c405000741202e0766032000852880c0700348140802c0c000d203101d00c444600c0d030f10101038114000036201500d241c050f0380c001c42d1010a01e23600300d80407161144 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 984298911 1250 984297661 984297667
    0xb0a06110c090708181f02032a0405062d0706201606110a120b0303070503030f0a0b0303040605070605091c03090614011e06030b01020a17220801110f 66
    0x20752250031407420b01c00051407080d0040140c406c10b200c00c0075814410f811800603240d140c41200300880c038002038100803900683ca0f001403903d4500c401140c5c16a00b0542d45c0c9991011600c4484e800c03a6410f0540084001d0b8003420400b402401100520906000d54014418500e07084007100c0100703032600d0b41c0c0d03020301c00c10000006c00b01410104042258040c510001d49046030800e0041181e20a01701c0e00e000a460140e00b0b540303210f051040d0114468150001c1d41004c1c110b941d519503034071015014420f16414600040d000e2a0300e0f801c5594010300c040c0c180c81e15150b035804090416041000216001401c01c4000b80601d00005a205244401c100600c0908280e0340400c0c1e000344282c010a13106540c41c0c4600d403110198040b0703041d0091116a10b00c040d0101c0e00449100904003d4211008042c1420500250b80e82d000595142183c1c010416903147c1042d0120350003288a4000d80000f0b1641d60aa041031120154442c0001c4030305460080c05404c0c0c441ca500202c0b84500121003003003071024 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 984300161 1250 984298911 984298921
    0xa021506100806011205010b0c01060f050d060b060f07030503060a0e070e100e04091a1f03060f0f0c0201060f140105040b0c01021c2c0303070e03010b0a06110c090708 73
    0x145120b5801c00d2060600307282607904210320380280d4009800148201ca00000c055507041c0d02407080c100108003620f100302d00c0720b09090004400b148400005028140c840f10351044a9581c0c00803580030030400b07100030303a0360441c5103006005500101d400910600c1e6140f40006d00d07032460302003148152034554922042c0d100b03040400c50301d603540d07002400811000750f04c90741098499110b940395480c05031010480b01224103180300c0396614000d10a0b240d40199080d00400c3c0e400108014094030307070011000c10b4900c1540a540c00a050810041000c1420304050704002d68040d8491020b5842c1810304c000140d48030b020610b1824401039140740012410003080061038150b01c013806030303000c81c3c90000d407409940b20090701440110703408444049945200044c0030380c0302004103d00f460502e840d01100f4100c10004181c503030000409003420f10032a03040070b40c404d41d4294052200500e0013403840c0e00d5191500c4006083c0c1e61503900c2c10042c0d02c282280f00d0600d152609c0e04600c140300750740e15a030045e595 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 984301411 1250 984300161 984300167
    0x60b0d1104080d020a14010b01050304031112070318050f030d0c020a05120d0924050306031509010f0f050c0306010c0302070803030411090a090c050f010516080a02150610 75
    0x32100c03001100e03a8052002241c103000c2800a18001501c039030013460b4020290409041212040c403900d003860b03161424060f03c03170740c018060f645e00c1609030810918084201c0c0c5900d0a21070070780d26040d00e41400064030000c158002c0c205600e0701900e032403000c06c0360751198144503900040325020b0340d060303209210303d40c801c52094074400341442c80504020240c07070341c40780855050f500302c0c000b80c031260300b0211990344800e62010103100100700300025480024907205d000180441066585010440000000341c400d441c01c02c544070000340702d074403900c01714035100c4111802800c40c042000d61150603d03880760034010b11801460f00440c040d440c2c503481e68403500010340e00002c11403822415030084402c0020200b406001451003540900c1420a5007100d1404001988130020000030045140480410214910042510680d00103030b03403011b070220038400140c815004402e030645100d14037012210801000f0005041e40720916001c640e0071092201440210b0341046132050b811220030740205100030700c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 984302661 1250 984301411 984301421
    0x306060d0c0b030106051908010b030708070203120106020313091103010b0c0f0a0614070224130606140301060f0819080d0e0f070501090b27060d1e060b0d 68
    0x110401c40d10300d00c16552865581140c009030f0112020820204150004031030281039100d41c03a80520b455055503040240da101d4600029280700c2c20000b450000442060080040300c803404081c16a01c1c0c86503a40f114020740c0c0b58080a990800e04a80300d100003100d10080c080c002900030722250310f5056078248441c0c8060b41d002944094200e04c100b404680001e5414000d0341c0225000340d001068180c0042c4482c400000094000c008541c4981014001c5540100ca80d0f601250403000030352060711041c1c0e0b0070ba425000b04030094242c070310704000029010340c032203590512458194003d20400c0d598607000da0090340386124411507a0400707c3c4101100750540c426200c41032050a140d03041000c045034002c1141c5824100d00076a9004c040312038a9071400b00700c01c000a020074a4819180b07410000003070785c030740100030344103405644500d0301180860041800406083e000317440d094a4010042a03170001e0405911691011507101d10b00c081c40d05030501078481542d20400e0041d140020228141c40109 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 984303911 1250 984302661 984302663
    0x110d44040312021c0c020405010b07120e1f0201060305010b0910032409050f070e091513050624010311090d020409120c0201021209010e1203040e0709030302100b0306060d 75
    0x401002503a11200700c13401416010040c16681d14440b000c80741c810b000403244107030004254a0020f10613440007807a00380d121091035001d0720302506010300e410302107207105810800344030b10802c06500c0c1d1071030700e64154040c0301228011002401101d0150040c0718441e201522000b6850050550a0000c5a00640e404103907650341c00b042022028803000e018102c1c0d0b040131003200d058101e0540c501e1420300411204000c0c2c509058122800e05081200e140d42e41111044580246003e03000542c80c1402c02e1014543d16800000342c409038980303040d030020307900f543c84035003254600c500c0c20b0003242e07520070701ca8002080c40d075003040303854035440c2c0301003082d4003c02c0c0d48101d07481507c2d00c0204000568094001c404080103469840300001188001790804e0341c09000c030030104209011a40c901c0c3e92020340c10009840a9410600c680d4003001003500f98403641e0000882c1303440c10b100b40482181d00c00f041d00e040320b02907403d840907241c041c00985c080c0c50482e001254568401c101050b40b03031610500c280111 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 984305161 1250 984303911 984303913
    0x20303180709020d06030b07141e0403080c03071403030907090b131401050a050d020d0305030702030d15051807080a1a120d0813050604110d4404031202 67
    0x140e0b519540e50081c1d034444800c40345119181d000800c02c105640f85060b41105e80780c10300703140c00d890382184408280143e441090950440014a8a290301940100c4019580000c0c84c80e98900314030081c580e03a03910503a400c03601d8143c80d0021811507a408000d80c6e000b8405040a40745087c0741032040400390204204140e446054485000c00c099020712551070710510f030044002c003030740c500420881e80c86602d61116005e402c44c5c08a40300141d5490303590189040c6e01d4204291252030741c5034102e10394010f0204440b400303881d250542c1448a0030203100400c854080b41c2c01c46441c409008070f407440c49021303a401404140344070042480c0002136009840e1281d510300c800580c000c4c0c00c00c000f0300f043c804602002019084500152030542d8070a051951041030460018220400d59540070340d80c060040020b0551040c9420f201045e07902c4031710003400140c10a01c101c0d5006842c0c20500700300750152800792441c0c041c141c144400c003000c2c03205014018060700710642c2010b04d152a5045104c400ca0110011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 984306411 1250 984305161 984305173
    0x6011b0204230f39070501020405091f17103206030115150f090f08010c02010e06010f030b040204020408060c0705071410030f090506090f060a06050102030318 70
    0x20701c2600c4840d200e07443d0305200c1c443c1c0d4201115804a80c9440500c1c41c01e1503001546880351102056074065102401c254069a581d00241405030090056401c060307401039446051040c00b80400704907144000d20800f50151040d81d4040d50443c07440c10340e43c0240c0d5034100390380303218007071140c0d5116070468481c403020300c0181a910038480c0401c040040007a05040d0012081c010242400d210f001c81d400d02521042050701d04165805904440c04107a180405c852084a42078091040d9500e038000c1c407000c00072a100d541c030345c29945c1c040c000007000000190311340f41d180190008000f4046048829101c04041310904586600d511240c00130401e9800035000c01c400241e121042000c2232240082441054a03032125162490408000e40d108480900620315600d15983d101c0b2810504042c0e541000100254040ba2072000740441c0c201c041c0850058030100710100901188010485a440c010b444042d41c0703424000c03040352902c0c0a1203005038403e000095040c01d03240100c0300803140207070850349 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 984307661 1250 984306411 984306461
    0x221e050607170a12180807150f0603120215061005070204020f07060c1404060e010518030a030302030711071805041a01122003060c090a030602030c040e06011b0204 72
    0x7201d50182c0c403c400012903884074060b8a6489218000d006405200080720010403605c80031003501401e00302031714010700c0e041c006c2c401190590042c41000c1c461101885000e90764105842e824000c2c0c1c01090140c0541c4580c2040c1c160301c1d0300d00600c600e900808a0058041d000310445582c1c200d007000300d8216508101c0c0e1082410b1342400f03841c1c3c1320b10449001c201080701410003460109100c0580e034070440d040c4400d00040340c200d0b510342c10800003071030040e4580700e15045280740c0d16410013825400d070141c0e0304840145580350700114801c1d6040d4551300c1121703007158a055540d80c11440352802c05004044090704506c003507044075400501940890300703950718a2000400315402a4054000c0e001c80e4131001c07040000a001b003551800b41000400e11601048002c00c0d2160300040150000100000e006100c650702d052490300a590021001c43d00c1c1d243c020503120680c0c1c01402101d03d020f0150000a141d588074845090521842c40130b110b00c40740d260b500380009080c12120070003400c0e1044008030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 984308911 1250 984307661 984307703
    0xc0f030405030406020106060813020d110d060506040b0a0302010507060207060608060903030a0b010302090d0b363702030c10050a030506040c02070b0c12221e050607 73
    0x5014502407005140d0720340c5043c0010707007140d0182c0c0c890010b10000f42e007007260000f007a0306600e08c0150180e0750390200d000396161111008828407082903210700002841401c0c030010782d003e1b520034041a202007040c0701040d01000701d00c0da404d10009000580c100040b10016082d60090403030b252051001165494540701e00505100742111098219440441001100c4504d4052003580c0710003800c00310b01d41030801c002b0903141c07600100d01030451805200860700c54420200c41c15805041041d031401a00d82e0402d01130701425151120742e81c103115908402ea28501c5490340401c40d81545410900300c102d1094601200e003041c1e52050341c0c540102c510100c2c3c80d031104031074884845007640c1c40b00c2d560601e814002c0e08481d4050f180c0380c0078600c2c006040010980026200c01600c015400c038a464030044400300d480d04120b40c465000802010a0004118998a031030325085600f244412380200d0f02c0c0d03e00700b065070301c4000001001001090080106045c450010042640500580d05c6d441004034449 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 984310161 1250 984308911 984308917
    0x110a17090a1d100b2506150602071d0721060b0405040f05040305040b0705010b031b121c050a02101d0d1103030a0b0d05070906060914180c0f 62
    0x40301d103000d00d031000340c440c05a10041e503030040d00075100d40012401c280a040384c030302801004521200401d49900d08420220b9858440d0302c0e40040148644220000040003c1d0001c1c40703650098801c3d89804034028030b02e54007500c826000c03003c007440c65540d228000c40314601508000060b40c500c0c107200442d41c103080d000ba603000d84403001d002c594651600091000711200030a0200c030f124540014000001e42c0107044070100c4104060300c0303495180604107a401000c9081d50203525211386003905071071000d800e4542440c1e0808950400708001952001d0f5182c6407000e044510090210300c40349070749401a0090001c1d201e00344119030802842100300b104a5401d0340221602c44080d80b440301001c1070800850050050701d15105101c0c1c05580812030b0749000240c4500318881e00c440344080c0c0c03074540d0340700700010765080000c45031180c0e607480110004254034014680001e201035000b05801e889544002030811016144c070700038200982c00501404c4005c2c10020101404104800803a01c0f2003000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 984311411 1250 984310161 984310169
    0xf08040e100902090d02041112040b0402041506140a200604020406060e010c151509091a0103020603040f05010e0a061416051b0a0605070f0e01110a17090a 68
    0x8408074142035803022011999076010004441c0100141c0900b6120000b060795241e605a82c045545881e080900c14a40100c06402902403550003c02040c40003100c013942c002c90003540d081110520083d14032049d1085401040f010031a900306000d15101c01c50020714842e0420320749000310b1028100d40c81c2440e02c501043d200154400400e2000350324040c404c100060003c0c1c188003a5541440c00043c014019000014050b404640207100380c84005030422a0100c0c0310f940c0d40c0301000e440f03000320b000510620324256000e400130030010f1041c5048000b03a034180d907002003c00d030640c4d80e195140440010005402c55441d500c035001c55512100070061800520302c603400104100c608240f1840f0103400c02011204d000b04940282e0300d445d030b080000c86010040702e110324034190355803403000340c41c041651100600d40b502d07000401c81590b90000d0003801d20620b5649a5031204103c000456011043d0a0014840c0c4c208243d0b8400140383da101a040c103440c08800581007044e103600107a4410380300c0d80 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 984312661 1250 984311411 984311429
    0x10b04060e100b0711280e090d03051e040302150c0412080901090515041d06010e01050a0c08030703020c390d050f01050f250309051e030c0d0302030f070c0f0804 71
    0x5101c500c01b003102e51140d010b4004503200c9400c500c0c0c0342c2c950035a40c5001c101c103c01032507174400215592044c400f000610700c0c401a00b408000e41010f280007903641c10261808000c2c10814004946138071700d51802c40342100d40701c48080fa8205425215500070b90701007040b1905108000d10001407940710661030400c131b586d0207107026031211718002042c005413025440303c4c84110028400c000c1c050383c11648401d41580286002c0349c44018080b806d886007011640042e12011011040192841d0b040d0018401c09007004283c402082c00d400d050b8803100607030300602c050408000b2a00d06442901180c0c040c1c0b65900030103507844240c194650506100409104585036511082000320018848103161f0b009a400d00710300d100104c08003018020b0594179400c82041503241c0c000d000a2040400000d00d120400c601b10794507003803c40d44590390300d500817000b81241c0c1c0075100004044501a100707580c460140c1c903000c0e0a042c0d0380c11004036800d0016010031104c00000311140d40104051a001e08042c01c0444c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 984313911 1250 984312661 984312709
    0x7021507051b010e01081b030402030a08030f27070e09011d010b090105030d0918020f03150f04060b030a0207020a0e0f091c021b03010b040905010b04060e100b0711 72
    0x240005103138809821543d4140030806090203908500810303442e21000c20016119165100c1c0c2c40001d04080c213000d4080c09003030b800300c2409490500d0f9040503004002c201d0031018502203860090580341c4001040401c1078210001c03c1042c1c41c0002000366010000400014001d02003400f0700c50400140e5046109685d0344203003246007030078558100d5001d480c0031001040d02d048070358070080c14800c09020360740c0610203150b0f840000d9003a40d01074400454010740280d48a2070104c41d030342c1d10800190b4a080c0708400c081c0e0411600c1c1080e1255009a540c410b0100c1e03c0d5640f6814588082e50003d2001c07030300241600c90001d070148070001400c0c0154016400d49003582807807440545851207282c08039941c03028a2801101c0b25400160a60b0286281c06941c009000341000090040010500036a001070404240074200441944002d0500e00125400c01501c1c1d101d8211b00d42e41541100e441d444000c50000a12210100502501181b031140440713060300c95410000c18010f00c107262070103001d14560 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 984315161 1250 984313911 984313963
    0x301060f03060b0303041511030909090a050105070503060f120309042406050a0f0e03070b040b0d050108160e2d0106080f04031e02070f06050405130e030702150705 72
    0x35010f080a4140300710b000f90704250a08840e8603c00510085440902802002244511505105980840000078064202071a0502006840f02c140383e40840b0036520f8040011415409403003a81d009e901c002e403075205821200d030305100e000e144010215520388414840100c0135640d6018004138145242e1030180491031500c001c030f44042d4907801802c2401414404900c180360300003020448507085203058240d804624002c01e040c00031682090798440c40004012032a24044401013089018048041240b6070340c461400740c5686801110407480d01400c10200500481149080e800156880b0101c2074464008140d003001608070003000307000d01001d00108405a089900380f64016089040030790249410382d0024840b40c09440d192500016241c1001100c80c402c0110901030000d5a105a0355030b61129800340a41d002032281074030941400107200d03903a05241c02184030340302e1820021403c107461982001603040c0603c400e200c038228140703c1c04011a00400c01c1d02c50100032060f028140c3c0c412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 984316411 1250 984315161 984315173
    0xf063b0a080a0803041e0213150608090d052503170108150f070c0f0f0c0503030c0703110f030d030c0807051809060609061912140a0b040b0301060f03 66
    0xd07404080346800105415001c50708100449521a0344260703002030b0000c25280d0421103840070b20011390803170070704400041c081c401035205244080740343d80c0d00c207000365881a08485c0c5150803509078002d41c001c9504020194010409010805920440348103d18800d000012118035170300c0c402e03800149100030382e0030805041400507026003110800703070002804012b1081441d0801400003181401e100c3c0c0041e1070184981d40034851103a100da0010905441401d0820116074194010396660340840c1000581380b500000302c80490030320300094040c0b80d10b10b481d4003609050040d80682c200240d0001100301c0d030f405008101151030584c6002800c01c004503c01800800000c12000c00d00400b00942c4100c500060420540110121031800590382d40d1004510f503800b6001407035401010200c0c0c01031190824024000500406a440300d2800c1c410030414010b581c0705220056403126628042188000035410245018102800100c2d40110410201e400c4803800d6001c503070f441c5904072040c410050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 984317661 1250 984316411 984316429
    0x1b03040e070503133509100c02030d0e03070e040501090501050a02091e0402041d0103030822061d0f070906050f030d180504090305040e100f063b 64
    0x91402c0d9085282407402e0046000b55444042c02c0144142041004101003400341c1091040d00d042450a94203450001100b68020851451058201c5094200103510445216107100c1c0c0041c018038819041c8401500c1c0304540885817034140c003810b40e000c1030726174022200034003561060780000381150181c20804e0840300c01070500c1e01c50354010004401581c2d0307a84a0700907241100286503140340382c180c0002e8000e2207a81e03c40015440140c108020881c400441e0034100d80c0662110340d0b1640d40e4241482c00030788501400c2a120150140080128039940e10001c00d500c6074039020001084040e4800349800c00d02003541a0f01d500919080c0900900e500400c2c000700002d503406444c1207180000030340c40d041c00aa134030003004150a1000e66800840285500a10003e0802c1211440d241001071043e4040c3c02521030781c04160000c40c0c004200600368000300c4200020743e007107480c1080b1045072461400c10350180d10501d000000c170b000039205040c0344007105070601c1c00155200d108042c000601 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 984318911 1250 984317661 984317671
    0x5061602210910030209030607030209130606140f2208011d1b010507061503061415060309150f090705091513020c0619050901180f081b03040e 63
    0x403034003050500d81c20a11015035010410459807110060301c1c2e041c08900078002e54a00c01c0e4144907000c140500607425600401c81d4603030540360415240d403d00c4420068400d144900c030009500c1c4210208030361001c40c0508824600100c41514100a51000c0c2140828446088032040e166203020440c90711f092241000c0038001c64440c0001860640752103456191005034050001c4074008900c00982c4a82c0444d048035070b0150703040205c20011a040d46603604140000c881b810714101194100300100d14640e031085031890b111104005030f8005100340742d000906502d02c07510901801e00c240803000780c400b0707100e24102003000e144c41c40c0c100a8240b4201583d44464041c900c08820310400e8194100350072405a41a110003151402c2550103c0091042d0500070102d801458180000001003e040b01d900720742104041c01540c84064140d8203d5020324281d200d0495a082460006041d00c0b40038031585002c3d0703c045041c1034151001501c90354891001040e240c000140a22808520819440d001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 984320161 1250 984318911 984318943
    0x30721090602060402120f07150e060903030d09080412080c1c120c141b060a27140307050312070207030309120c08250503011a091305061602 62
    0x40c0380340110294540101a00190003640c2054141c90b1240b000c03c00761801010a108503082680d448401807490800e4003070200018030b014030350074070610b002e10942d4a08400100510300e044c84403000b8200500c213514003110b4085e0103000001e00c440b000350303001d84194041c402c1256100704160b45107043c0700b12102c540c4488900d84546d103103400c0d4044c24200c0c061208103c001104100183c0540d294039500c042c0055811000418000011101140c102030110300e500722089520f802d0003075801d440340001061030f01e005841c4601d0851460480c2c04032058050248840004403490f602c0d4203551024409889960000520813410a000e015890348210140301918001e404c0d5030380200040f41c50702c20070354161100040300091000d00c2d80031400601e106021135501c5050f00c00d516501200000406020201300f000015560406000f9011000b4803810845444400c0d98204081d161019040087c00034020058400082c02000110f0255204180b00780613054014402460140280454102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 984321411 1250 984320161 984320177
    0x1504030c03021003020c24060102150705160c08061608011a0706020d050405010c090605120a021b0102180f0d05060a050a0e0a08030108010c08190c0908030721 70
    0x45128120000181d9a0440e410500d88101820850203409091103c40d40c40c003a40c1b903c1540400e074040f180c804001e6107003030b41c45a42d50f06401a621590070500407041c00e8201070000304038902c214010102c01c012110601e500300f00740c1c0c44c0c25540b4680390700411b034650301503020f001c1821000c0401e10b803185891300e0301020940c1007801c00790344402001c0800e100040003103008030401010b9015a100940c0c4558108001d01d01400c02c64040c0c20079880c240b010840c1c0c01408201140f00300300321180750203c01501c00c2c0f151159081d0200940c002c010306c0009220b85180d01403200d10038001414040701c0c888003d483c0314096000c0000b0b0009020305248190340b019119400203201290383ca500c002c1d060400a000d5980c1621140a044600d0081c0d11a0080c03804500812298030051070503201103100800480d800030ba001d0343e103304252503111042c01078104000c0c21050940046040b03d6440c98001407280d0380780c90580c9140c1107000d044848a00102404401801500318020000d5003442c140300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 984322661 1250 984321411 984321413
    0x1e0301030507121106030916050d050712020d0f0c050f010e03061915030c56030c3c090a0f0e150108070906210c030605150403 56
    0x6628035240c862800201c11042aa8040c1300300c1d0f00c94041c64840c00f41019070740e4a000409140c0ba601c0500140c00010700d140c1000c03038242080445a4015988040100002401c0c00c91020030171034482d02c1203070b100401a602900091040f000300b030400d0b02c5210104041410728040016910000c00158104030300c0d81d059000d1a13a000812503041144907090b42e81c4456000c20300030140040000d5191803281440000040156100d202011075500c4902c0800d00f80c000340408080b614804001e0303002c03460349200c1e80c0e0300880c61550314500ea121054078480000c56a0160100ba41080707030010321140c4003107050001000d03035040f60940311000a00300020b103015010b04004440c42580d5621850401241030300da40d80b21041c03054090a15001c1840e4202e64850b00d180c021581110110b0700c6803c0070120031555400742c40132600901e40b5031038041e031041c28120100da103e0910004980c80f0881d5018004940309540f01d4a025446c560750f02207990390818040c032130000040085900d2680f0104404c01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 984323911 1250 984322661 984322663
    0xf03051b0d1b120506010c2012030a0207180605090402120c1305040218071202130504060e01380c0102161202011a0f010f09030b1906060203030f1603110c031e03010305 74
    0x2d502238a01c42004203008a001f1a4008420b6040030000b40300007c0d0b48007005400103144ea08a4060b01802c0f903031880300c00d0a060950312a03115264009880001040042c82c00e50540e1030740e9080c110440d070b4085500000030b0101c4011100c0740c10350503680c406000a5040a02c3d800c41045401030f501e280340d00380744074010407440c02210490703d11607000c45c49480c1140d00030646002440020000c0c460b10b40c540c10a440d07060400c0c4124a10f200d1101502852010105212000400040200c0d03211500c000c40c464a280c0c491502114695420400b9100c041100b480c40d00079030f402414068a560030b110000380c2140c4410850a811401241200101d41da030040d440c45031450a107440040301035441029100100c1d070b5000107012a00d032504000351944144030100c3c0070222042d06000c2c040d03445806a0f02c074031041c1d4200803d51003210009210211220010b040502103190020304400a404060745030340120610b50500e030000962001a00300c10401c000c040350b010400d903459549195101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 984325161 1250 984323911 984323933
    0x910061401110616030b030c0603011503050112030c030318080a0c1101020102120103120c050d021b1e0409020a3201030c020604060c050d09030f0f03051b0d1b120506010c 75
    0x1301040644501c034900d8907850034000700c8140d2a0241c103158495848850a0280c02030107080c1070000b9240030000640d0745c0a131042d0204258064030740c00c000710640d0310700310091702410b0408036101c40c02d000007a00042c6c1c6034000705020300441c0d40304a5441e44520307001803800c54070348040e0b04683c01803003418031100768030040d141101e5003c001c8100c6220001c0b8142c894250202024000f401074070280146141c020403001c0346412400c80e0941158803040400038201c90f8813441154001c410790311400d050030725600130360313100340018840681d180d56010403010101d6142203400d100c16084190014040750b1f000c07074010310341c401d0030184032101054100a60b5100020400340000d5260540481114000d01c00c81d58242010002400104140e05001d01710407801c0080c400061500103044104a03c03038400d01c0d0060b01d055000e290500302a1108a045401003841c1c0c40703416070798010380102d0041050599244c100c4580303d20703540c1704560300c3c00000c60342c000b01410f06004085100c1e9001071000c0c000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 984326411 1250 984325161 984325201
    0xc050603150103090f08030112030e0301050c0405100306031502070b01081c0c060b04050c0702100809030d0b0103150608010e070201052211090f150d02100809100614011106 76
    0x8001a804c81c2401c1005070700c8004803028142480010003c10652601d02400705024025141c10309c4801e80e140c1410300301d90046501091184003440309018074600b00c18500040b480700d14000c244a03440f6101d82aa08181c0000c4454990740052650108002c0034002030040101c00040c20b006030404140000010380f542c1c240c4100524040c240e0100308042e4480e40c1d140402034010481441d00060b0740e1002e80c0150001e0348100c0c3c0b90700598002a00c10031a5510841c10f42003c1c6040c0300403052040d001d4140c80303441c81c1c1415103502c0d811400e502082550f00040001d50384540361075140c580c40b041c08020151484085905041c104001c03a100c281c1504000e503010b44924280208a0078507024404d0008065544540d4032402c6c8441500a0607066004040d0380b95409540c400c00f00800c07014200c8140d009400c105400c1c4c100407624018040ca44c0e2043c807040c04c3d00c0030100950000e00803581d0070f4000110100306e0515140441d40e1107001000351940c00d0000345246d0505c1240740505041c0f40c04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 984327661 1250 984326411 984326417
    0x9011d03030304080a120e060103060b0f0d12090810061a040e0705160206030f0a0e010e07150905101e0801050609040f0f090803042108040605060a030f06090c0506031501 75
    0x1817245003031071061101280c1845035000400400682000c00303a2280740070300c4280d0b185810101811240e180420601c4c020b01d200800001c1100d81380c4c1d90303d14014010159003c18400001c0c400581020306100d14a0510040e040029106003004002500e080070f04905c0d2420030820300c800e001d01c0da646600150007445074144a0b8451624004440c0105080794000750418008024480d00201d80b2071342c0c50051040c070400b8400d20708202c03801802c0350300403004244150302c41c81c000c0152044c01e52003641c1c80c103068030f0b00f98a4580c4640c0420f6054220000500002e41001803140205441c80d04041c0c0360142441e091001d5413415000400500402030000c2c411076440c140300d0380c810031a6100b00101c206215050044030b40d6820b0100a0b0f400c216410340c0c425000a4102c450480c0e0f90900314496041c58071440340340d4496071038501c01450700800e410b030001240380b004004500c0180c3c100b41c00340c1c4690b0000c00d0120700c03032501c90091001a4449030150405005212804008a4404800d94402c0c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 984328911 1250 984327661 984327667
    0x206010602070e2208130b0c070603050612060711010f060b030114042c1908070f0f1b090b030a39030b24062506050a0209011d0303030408 61
    0x302e4005444c20386207002031522201304260f401080071503c05000c0b20140f580a120219a40f81c0c1e160305c1d2803040c1e90000c5060b410500c030034401079000703610140d00020007030205220035444104441c44c000c0142e4046011800d80d5100c5c1040304824001c1c6004034000007820b000b160300d840c00d9282c181c00107018800200c4600744124440340c0b1140c0c4000314100309401c07012038100c0303412140c405422241d54154a18000c41d4607c910041c0c4000c1c0400c070040d4440b600700c1c500f00076034546241100444100329a480000000080803650707000302800c000400350301380c12072940340803509402c07103001c582c955009422284007000070510007c244104811000000582012000000a4180021061401d00c100039003404004d00c03060164051044000d80c10b0000c6074204000f502c01504581c40681364044c20410200300110074001c2d0202d0301481c0d81ea011034114005903110016101d04454a4420350343c04030b25081d1542c1c2c081040040b5503421013035248032070000000f0a8503440024000b030002c0c0000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 984330161 1250 984328911 984328921
    0x30c03271e0209180120040510020109080307110a05010e06070801050405160f02010f0e0c2704020f060d020d0b1005040f0306020c030c0708010e0606040506030c0f03120d14070206010602070e 84
    0xa40240d81b007141031400c102210002c070100c9030040d4016005542c0a98000f40303903c0c0d550b80c014401c2c0c4509a401074000c6085a231003450403030b001c010703d02c00d48000340105404200050424007841500d042040c004c2c2c01c2515000c0300040589105a2040348118102014005001c54640041c45280c0ba43e10f0242041030101138280d0240072950112030085d40b60114a0407020808912814465001c81d030001c5400c4c481c4150000362803070b10003c2c20201e08103402040041c0342068100249450150016003040d004901e03003000c07a002003080307690940d11968a0a114504104100302654050508500b031078141041c02400700d16074000200050750010340c10614050070415030b0142c5020104a540c41e5442c0d00c0100e001e08103030901d0a55030b21540d0041075841c68140580d40c07082601500602c2040103000801c4441000342c2000380d0103002d605142c00720010400e00620303004490341808a02c0103100300c400f11600c04002c014a086401110060019aa003c240a0300300c6100c1403403580c4540316 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 984331411 1250 984330161 984330163
    0x3020f181506130b0910020706050d090201171509180c0105090f032442041b0206060607020303161b060908100c0e01030c03271e020918 60
    0x80d050f591590715074802d4002641000070001000391000c2a51000e5500c0b00e004401c0e1fa481a1a00400010038402d20540c03440d000d00c0d030b0040740424014581941310840c032504032901c001d01511819251003d1110200c8a800c01070101074102c40c52070b501400320503090143c140c03a01c1040c0308640c1006070000b44154155070304000265904401000e0f00c2407254054103410003903d0b40031a440b034120780030340058210741d1042c4000481c00c4483c0b4903c109002d10b2040a5000044144120000707030299105d0043c82d125485091107504041220901d604100c034406031500f40000d003510312a000402542005071404029103090321f88040d1060700c055140d1820000d00c007400c88006042c0c0740082d00008907594002c3c550411030385494151000c140011000e042980c11100741075010403003800d4810b03610751003540040c1c6012117a01e80046e510391000700c091920b9aa1003501c9800000401c2c62070140700c00c10b45407440450000e02088820f146950124540c4100105514601e10000c40c4000c007944c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 984332661 1250 984331411 984331417
    0x2060c090f061803070f0303120c0215150307080c0d060504051212010906050603070c080f09060403061a0108130b04080706090302060118061a25030903020f181506 72
    0x40103007071644030f101003000180d1140c5844482d910911a12000054180c00d0300c82617020389805075140c88006802001203c0a0700c1070341e51000461086400c284403912012400c6030090350000f041400c9a09900304040c03130074103c0d82106066801c40301480b0282d9403081c13078491400354031801c0440c0c1d95469040031810714205e0a0f558203908000220511348601418910341a6151542e08009007910b07001880424007084070808085541c0c203280b40007007241800900191101d0401c017038603203810030300404d4840e0080d03030040300e040b41c48410402c1542019800c07188060000e01e0319903050301e03240c000728012002d55000540703108142004a4140807191040b985d41c0c0750008010301c0015113a25009569640902c901400640380181d40f982604a5000740000c64206c00341d20790700007030702010803c06d6501094501c904403c80426800d604403071858903203c0940692030b069400b17440c6006000044400581c45031144a6240400342100480e808054001c0c8407031600b0909091080007007950f0388 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 984333911 1250 984332661 984332689
    0xc12280f0215030907060c0f0b060a17060a0b121e0c09011e0e061e0a03060c0f12110d050a0f020409090311211e03240f0102060c09 58
    0x40e40710384803205030b4550700d000f140540082d000f182d02e041d075506411106041c40780f000500c5c18105d050350070041400414002e030496401001054001e96075601c102000020448005e8640c02100c1040080034191080b50350b805410307070b20240f9480340e03041c40e6926503d1841305003416000c84141d00144140807c1200006000601411055610f403d40c101960340b01b21202d00d0306522080000c190500401d50590140d40b02030103208401d8560182405115045003a06402135001d90000003c18400d0080255803001c54540c00740c4001104401051000041500d02c00c403401d01c5044210425410704807203407107030003c0300000d190711a410030901a020340c9400d490445e00105010a0b2002d45034080c0311030511984a0f0703201e0000c1140919160050700141490380c845022103503034841d541000600a140ba15882041c0c0300d442954240c0300c0d500306031665040c0042009802c202040c00000a00c40e6210484240d417048085200003940c582d001440444d002ea004030700003503180c0300c4065100b004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 984335161 1250 984333911 984333919
    0x15040b0406060b0f040503010e07030803011a0d230106090e0403050a03022a070e0108072c07020d1403090c012001050405030a08010b0705151003140c12280f02 70
    0x341c00020070304ca025041401000c1c4254a020050000c50000040314804c40313502c00511410750386040802014100d401045009414041000345914401032194186040b6440802e0001c3c0f40c88108418110754141c03c0303842400759280c0b05200c40c580b0b50010990099252800540d5801c110104501038000d800b160305401941d900b402c0403003000d009200240c44503400444800640e074410f0180d06120a1040042e9500102001c0c4140c494050000c0b0b0904039149030300040d02000c01d047c81d4800b808075040001a0801607083c40c1d00c0e5401840030f06010035600b007150441c10f05004554640704580c4081d414019940121550840540d505005e000c2e684402000306141508101d0340360350203240b0b0080040c01100001c58800310382d030296079007150008018502501600074a07401258050003400d0201c2406a001000a04090b4483e201c1e951420290005072054400d1012502d10481c68031007030303006421406401c10010000c13182415020ba14511140c6d41e50815180d246540e020180d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 984336411 1250 984335161 984335167
    0x1110607080106030c02010b130c02030906131406091309050708011d07270522060212090705221506020d0f0305040c0302010c020a17011d15040b0406060b 68
    0x59035811514860403581d550b242801030000040c4100e00305c07600c1d509003591001c40b4100e6440b00e805654840303400164580105da14000a2600280190f00072840c02200e0207240708090050148500507002c8071101550700e60f080c01c5e040c83c00144070000d010702c8448a60360301c158800910104002c3c1381e0092043c0710003000f0010700210f040065021050710400d0900c00c0100000d00c40440c04c0740501441003e40c030020345507495180000151601401024401c62a03942940c07682c00201403080040b4418040140d0b6404a09003103800c110005040602d150840301c07003008240c0b038000740d03141d80080340c104c1307522903010070f81e4003100504099110302052020f41e000441d4007500044d07507242c03030643c030f444014201d00b0251040b425201d040b24000c0c244035070310400700015400b8882c0b0318240740c070041c007640c10341d47c486180800f40441c9180304503150b0b44621700c070482c0c503c0031840b002035031040308041c20a00d0300300caa40c00d03952000035200404040c8090001814002694007800203040444200c5907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 984337661 1250 984336411 984336421
    0x2010c020609042d0b0a08150a0f1508100603050c21070e010612020712050f0702090f0a0e0303040218060102030c01050403020a02010f0e0d020f0a050d15050f01080318011106 77
    0x255500c0c13103a0920a1685c07400500314118641450480f0807103120100601c00801e007002c40008190700503240c459020f480b074107000035145040c000c05040d41e1030f80c41801a61842c00220a24002a2205840a0b03d2803c1400d01c0030500100f20142200419100460000303544240d1420000340c03e10001030038012543e010130308220a0001c42e048038070a40d2a01ca0095854031640102d108100d00240300320300000e07403800224082e00c081d011061120f9001ea050031500e402140721004121101480f654680c010816041950300c592040c0c1140380700254158a000d0340454007040240002000501da07500c001001688200100d4a001d0451002070050381401e207000b80d82c407000c101d000c03404980584500c40e07001d8400d4007405603240340145000000c14480c0c0038004980180d00c00d2a80202c1410740103d41034a5020002007024400c41d110074a401d070901d035210468001404050070360105400400208100006554600c03600c403ca9845a42000c00169040f411010b2100001d000d0842041 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 984338911 1250 984337661 984337721
    0xf050105060102010e031206091e0a15091104030206160f03090e06010314062e081501080108060a020f0415030f051f17012d0606080402010c02060904 66
    0x2400341c03800781c0080c40355415040b20700340c03680103006000885501d000c2c00691b007840c00400c0507400c420500c02481c0c0160424500101d4600c0480d001001c950302c4000f910709580890113000c004216940c42080a903840c10f107106454402e61001038825003003c1554084c3d000c0d141c612803502c80c1c4c080c800300300c0e0f4022841c0291100c0b480c0d201c1d43d10300001710400105a5400f0380107586048d41c230b1102d500e40554a4500300498505020784141c1d09030b45a030485c00c82417070401c4032840804000d841d018010b280c0f28156041c4007900b0b041e21810080d08100401c4071080010744650001194980581c0312800c9032204601409580c2c0302106119503a44581c07072598160340100042546141305000716610710480303200101d8248801a400c5000280400c91345001c00b405000000c0e8440003ca09080c0e0818000e800700c90050405280d140801d84c001045403542c42903c0042c403603400c224850307242075000038001b4990400060f00500740040d20604a90303860780301c20f400145d01000c10100c1c1c04014529 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 984340161 1250 984338911 984338921
    0x1f05100824150d03120e16081c021c05070203030d0203061908030d0f06050904050c09011d01031203021606020408070f050906210f06040b01060309050c0103020a0c0f0501 75
    0x201c4507075015401080c803182100c920300c20070020140000c0c1c1c0e5400181d504072582e6018098044144c0d954031865018250207100140745552200100c07103146050420440c24000c0c901c0c0380f14031041d03c5000750782d032068010a409900c0c44c0c08039204c90300110b081c10152045d02c50400025418080040c0c04030a054141d8080d5026480694090780650300c1c441e10601203103154081c02c01036a10601405481d407403140c00c84090340d145102e011078060f54980115110503c15a03003168070380c0002c0160b8005043c590b08103070042c0364030307107281e0240b048268211a40b4101800050000101070b44000425400794040703402c015400208101725680500308a002900035000d115041e0240903000900d0f06a0030380050b090300c10042c89210580c035a0001c000d246090380140c0c082400c902d10128180582c14802e0707040e0a02d0440140c40d89180ca45040d0002040c16040001030502d0004010003082d00081c4801c03d50900b0300340103a5844050344240c804168418000b0412200c001b98042048019004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 984341411 1250 984340161 984340213
    0xf0720030310050f0f040209040905011407020c060a0801060503040305120f04060b012303063705010906050a0309060b10020709060f12060c03021605030909091f051008 74
    0x10040c050f626001084014003120b00c00303903882000c03110704203d24034040d4011300712450002e20009a5202e030707039116820355400c10102c0502003c18010009041d406203c9910104c408882692801801c004050304c2000706010b92020484080000340400d8000c000f182d51700004001183c10600d480196085601c100f150111080340c10150a941d055010f0401d10603001d084000722008151040d40248058000410b56540101e1140c0200d01c40f049010440b601c048100c03103400c2070440d40b10342e61104044168402410030400c07080402115520500395001d030744d260f10b030111345241541480c001a00b0020100340c0c1c0089070440038007010b60000b07030368800c89505502c18400c4940e100b00200d5080ea01d445070b0240ca06025042c0303800191540c6c0b10040e2071686040060070098052400007000d40c42c00c500b01d40b150300010300b4110704d01e0300c0814180d1006483c0010242e00c99200c05030380c440c0304426450030f941e60f15280032800c00500c0d10710b42006085039004031010100700c1d03c00030340110443c0003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 984342661 1250 984341411 984341431
    0x4021e0a0e0405241611070b030606070609032c011b05101a0a090b030a15152304061406090102120f19110a02090603032206030c0206040b0f07200303 66
    0xc185c4d02c001e4025052401071681c8030002e085554a84012914594802032220364024402c20040300041e50740c1c442d969200c3d010340c0d10080414030300311441c0003140007101c40484048200400c030019a92000c420034500310070703014810082451340350a40c60428000400307501a418110201820000b0b4072062000203411070307021825903030380e81c030080848546a08081e0035400c00c40001002c1050050a20582280384000003088036180111040c502100d800256101d05030b201d00d10b4140b40b9040f59200b0310a0210740411029160200100201c03951401d0280141400318031005540e00070701c1221400c2981400362a0340b018030b074070102240d5100070002d507018040c0c124248141d40c4520361401801e14080c005241040c0c194003001b030600b000a10459040c070040019004000542d4003110501c40c0180c010300c1c1103820688050140c521290103602198400c00800001c102e42c2210303543c100c88094100c0c1c48680b0313280350440c0d90f0500b016006648100c40781580e828540008029440303401008 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 984343911 1250 984342661 984342691
    0xa02010309030338090906070f021c050d06082d010b060403061d1f021305030a030c0201020d0309030507080d0b060705060103030e0a081005180d020604021e0a0e040524 74
    0x2c01c4111502a075001b180c65015000260b25a4001c84e1464130b4290b00380103d44040111400b110b000020103c600800544040380c01c81c400541405842c000c1d1010b400601030581d0810850305440d070045449a144035081038440c5071800083d800a9049800504229074598903404e002e0040d010500880d6050b1240f40e08a404001d400700c1c0b9076980401c441343d03900d1003d039842a580c010350024122013024a8401e2000151a42e00704944100e141c82600d03001804000c50002904140c2584c00c030764140b50a1008940c00243d020085030603040c1e00c40401a00c901c1412100c8004002e480701c465007000c00011030034284000021954100d91099441c40034004601c410701c40d40001600c0346580c00d0780960980d488030000c0350041035101241c00074800e1800e844c031070780c01c1c170304803032107181e040075801010500065061003501c41c6025011405d00014030307100c9070082842c1d500d00e0700c2100c50a660302c4002c03404004007800348450010b594a034000f154003048143c00c1d403090080e520101840c200d2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 984345161 1250 984343911 984344021
    0xf2503111809130507120c0e040b0417040b0f0f0702060f070507050102010204050913052107150207020f120a08120a0c030b010203031501021c02032203050a020103090303 75
    0x18410b840f00c60b4401c01500741c0c54070b00581c168002d189905d08560402c200c200c00310744120600d030b500b031203680100d10003416130a1908119800c40032240c40c03ea00c02030100824407951503c0c0301101d81c21203a907022590f4400103200d6001c203900441c240294401d000046915001c91960090130465009500340d1348125178030740041e8200d100d00d102711354109a4120000d103014080c0840301046a00480c00d03a01c06050000b651001c5074400003030280d181801080a034180015001800d5546100fa20114a48243d1303800241414000300ba1851007044042c0c4209004502400070980055000b0030305074a625039070b5080b40c0040800c82d0004107107460201d410403042d01c40d006080640307406801940c51901c500c8022011161380c81c20301419403141d40c4800c4101d0303100e034041c1d43c030100d0700b68007540d240c182c4850340d0300d024581011001c1184000d01d80a00218001144800c056542401c00040c001840d180917409840c000190055511650440d0925034078094142c840880342d031410304040100c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 984346411 1250 984345161 984345181
    0x60f220302010212070f030e0f0a030501020a111501170718020d0e0c0f04020313021c020102192d0f0309031e0c0b09010c020d0c0e0f2503111809 64
    0x61020281500703207141e01b6100403a0040035042c0d07450f10040c0421a1451051021522854150388216800d81d400030302c00300c9060b4421043c0140e6403400c00a41502103402c0034050120394180183c040c41440310940c408120780c06c010f24401000000390400d000c410701c09040000303403c985004d21000e800c2c468450340302c10022440e54081341d0024030100460f4280c109100007500b00602402e1440c1100c4400d40169503881e0310700041400607110b5070701c1d00401c1d01c002820710058a1551100010011380b01c00000c036502c005d03000d03c5550a40104143c0116004008a00c2c0302120203000200e1500d0303600280350788a5001c0c0150f074044c035403038100c0741c1800240d81044180141c028120602185c030502031010030f10002c03d22400149031555103104280c0001d042c3c40e00e4010110390700f112030b02c1e0400c03011082403013043d8803030340c3c0750a4000146007221940401038841c02103600c0c850340201944000e00d00951004c0c00385010018901e440e0141c440c902c05400d544843c9130741c810020030000501c5003038 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 984347661 1250 984346411 984346417
    0x17010e0a0633091802070c081212280912080603030d1104031a09060105060f0301150c0b01140f030703030e091801151401020604020f060f220302010212 67
    0x2c4003021000c01c0c184403124007011040e00c5607640d01042411080080c030b042d206040c00d40300351443c0200580e601d03100d1520302d28221195000c610303e03410a0350b45408070403c00c02a074000128800d1002020340c2d40c90070300c014444000143e10b01c4625004203988003503000794011586a0702c01c0600c0801c042e5030300c0b0159a00d01c4c0482e8400c1d818bd00400c052000e50485401100300803905102c01401e1640b01d0fa105414900b9407010050441030020410039034807010000d041c01042c0540d0071524040d1100b2801c016484140031343c207141c0302076500c403142180c410b000003000140c0140220099586403a0901b01d02202505041c0c81031020740c2c002d2074039260109a04040301d9141d221000280701800511900244c010456420f407595030440d038401000c01c1c0588545c41202101e00d44059003080d510407034100017040e2580c11548980c04100050310f510340444443c00044031010b86881e4020b109010511401484c02c016900d9483c4441001d03228921910940707100740c00791038a0b860542400741080c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 984348911 1250 984347661 984347699
    0x30403080f18240c0304090e1c03060605040e2205010b030d0908100c090305030c0309010f0e03100f0b06272b1103031201171501031217010e0a06 64
    0x14040808149810740c2d40d000801000310b40e8802d482c00c00f1f948003910f0045503000146c81b040c540114034000340b586001000074014a115042c01c003e09410400000c040d40124001d254489060708046603504031164500c203a00198408403402c08000d030325045000c1c0014200c028060f101ea070445001080c021115441030303402d180b00070007140104580c8000074203003001c0c4110600074400c1d0040003040c42440202a085003000c000d50ba102220000107003d00070341a40c0710100a0360103001103503640c2c0411011111007125070702168428460102d0001011481d401d82d52082e400550b003012613204101400c84400b030400303103008442ea15014040d956041c2004c030214400ca80c480b48140420201c4a40056405508282541e20f80d00f808030349180d11003040180b1060b8080700400000074120000020410440c0c080c00080c40c1ca11000014440180801400a003044000c000d205100340500c1c400c1034810f007038201095940705101510b41e601034440a034030320708040000c00c20741d8a440b000c50f007c0b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 984350161 1250 984348911 984348949
    0x3030d09020f061602060d181208010e01120605062101140a0e030724060b031801020c190602090a060801090e0313031209090c0e0f12060117030403080f18 68
    0x8040b541d0b082006d503a00000c1c60f060050765690844075045150b40301d807c9214418500800d0481207400c01030820394059104688040c010b000600c80c8804804c00c2100c1344d45d100d100030425440301c20003d44d00c182c503520040350104403254408468881500302110601c15625405a1a1200d0b48400282c8000f0100782d07445034001c10410300003800348540014200410880000d4200c00580d2440c150b5046038000c0c4204a00442403000c4840800d40880da8460050001c5180181d001c5000751108060070140c80d40040d410500d03414801b4070307011121542001845061485d0301c5100c0640060000c2c05010040303464203904015400002040701d040a03007803d8410035680c559034600380003004a170840070422004034000602c8600c0c5005003281d000072038984c0e00c0c558043e41c003400004010804901d205201e40300300e000349018045015815a81c13a2034010202c51011201c15195218540c0000c0102c100028204480c0500d480900a0b00582c1c450164101e000c8a081000748080030302e500ea40c0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 984351411 1250 984350161 984350197
    0x11205101814070f02010c080610030e0f0a080a02070618050609030115031115040e0a09170406090e0a0b0109053309040516020a021e03030d09020f06 66
    0x850760240300400e001403a850208816140d90310180700d801c4169581004558440d941c0060250280101c42c10710341c0e07500e89043c003450302e04002580411000101c0050541c2c0f1008282070b01005d10444080442c1102120424811803030300d251142d1003124510018040c0032004281284100c032641014010300485203091802c10007085515401602016032542da00c0160042419440c12001c00039801801c0c060410a801070600c030401002142034114010f0030081404216103480006402c0640b00d680002c0c101c00300c3c6054201081c3c6501c01441c561804580040d05640c0000303110140d40219180141c1c5441d04500002038808200e011804265810001d1201381402c152039041c485802111038880070300c400394a00c071b5061181d481d1054401c0029452442d013090b004207500201c0d883c081c07084014001c07400a44901802800034071a000081c8041c4003198056441e10080c4030040660341d035a205000b0030001455490300c101d005820000c0c2c20403541c80c000e416600800340d1141c0100c9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 984352517 1106 984351411 984351419
    0x60e011401120507090c050f071209090605011b060b060406050d0c090305070308070821041103030f0406050f13080d0207050409030f120609020c01020901120510 71
    0x307420b60000c800307000034100140900440d940c01c440029029800e1034100d030720f40704200324143d10714400f0401205000000030f07041d014075415220206000d07a107001c0c00054070100c0c8100b90100b400c405010122415440c0541d003035500c6520000745051004002844c00e420542042e0300050303004c00d030840303154107070b10407031410411605200040910316900d180d9602841d000003800748602040c1d80040003025070a850700d04e80d03415a1484440c00382d620b1102440011641521000d4080591300805e00707000c000c031802c11a41c241c48510b4507050000944456122751104e605243d0300300000e030140030032141389a010b005038070054010800d240354001e1800030035070041403040303140c0048070000a402500c1b8800450381c03070501d90141c105040114009082a0748030110a500020350b03021541c40c198000c090070304090302e80c2c158445004c00c10008448003120310010401c9000b000780 = true := by decide +kernel

theorem cover : BRFrame.Cov 984172661 984352517 := by
  have h0 := BRFrame.cov_init 984172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 984172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 984172661 ≤ n) (h2 : n < 984352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
