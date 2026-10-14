-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3375
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:28:46.206319+00:00
-- url     : https://prove2.me/submissions/c0b4cf2f-8819-46b4-bcc1-cd2f9a7ee4e4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 606834532 ≤ n < 607014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 606835782 1250 606834532 606834581
    0x30f09031c050411060f0301061b1a091006060512090a0606080a11030316021c05010c11120a081b070f0f1b061b030e03030c1c08010812090103 63
    0x1001e07003420f4408990039001c2030b134501c81a141c800b0558104e2040c844070542543c1c83d241c0b0031240d03001e0910040000e00c4586042d40301040d501400070f50906a407190400b00b5050801080d440c1114900c2d0070039500345800d000384481981310040319550403130345160b00c6a545a01d103a031807c024621320005c0c030310b910384400001c1482c40400c18240302c5001c2d041c10802081d0b03140901d07440b40300364000791280004041d0783c0d0340189054038032201c009a01c04002000c2200d16514503084484030718840000ca00c10948070103244400704074404120080c0380c045801d100408130003424404028001c492080e641c01c00381541d81c841074003601e07901900800c00c80f00700c0c0c0b0780c1d04042d0111861504269081010712020400c001414140081215038a64031403c03421001040c202800c49844011420441c00e025484155602000134100d0503160f980580b000c3d010080062031701035070b001d0190003031212075001081982000320310100b807070003c1e0340c0440d40d511701c05004074001c01202c905140fa03031482001c000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 606837032 1250 606835782 606835837
    0x618090c14011b11120c0a0b0a17010308041a040e0c1c06061806030c0f110307060608341802040b03040303090b0a02090f0f0607080307020c0315010605030f0903 71
    0x42000716810f17288601280d020701e590588a07141d0b1007140707030050084502044602100d034020302c0810030505d0300b2068246840c0701c0384c051400aa1090340d01c0340002c80d0501495480002c1c907810031010105051500c3e1420203507c02c860382c02040d8544540c0c0c0410044002e0b40340521500d5200502002000082d456420142c0442e000102e0444030081008021031103a02034452180386250585403040640740000d42180e400c20a09070202c11400240031803c0010b40703502039400030301040000340061003901000d01200c0710003040f01c10340c0c0b6250304950141754a0f014034032034169200d9510309980380d030048400c04060b1040390b01c6040b0000001080100f40355040e0301195401d449030700c041100e0f40f25100408103900a03c01180d601c584101010070aa181030782420581d1003000d0840d174200f0b21540c5488566800c2255400e000d038110b0007541116280a010400c031090140c000058554140703100104113010041100081183c44004555018000c1040d6841e05500454200e0307131080d0300c03080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 606838282 1250 606837032 606837053
    0x140c0307110a0507320f03010b060406030f0b030106210c050d050609061f230603040807060b030102120c03040f12030606110102090d0807030306030b04060618090c14011b 75
    0x5400c3c01003507509000b401c00d42e030b070010881054074035100c500d1000700c5c800c2080b10801c02c50140036030641d80c0e100b031108103448541c050707c02000300341c41c002002c001d8202000c0503100c5a2110031711a0349441414010b1600c3c0c0f003000c0401d01c0e00440e41d5060704919240002e117070768203038101710b500200b01d90300d80013000800205540300b10840380984006441c2e0056001881001d00c0b2000540d04200700c7c00c0c4201ea013040c1c0540e00070307081682a0440b46603500e0209540758016101a0742550000a0002c14800c86015046040405030007c42ca81112860150700b2210041e100c13040808000000c40c080c488490030a20409400c070000003414110300300c019000b05814420340b40440c1c050258000203e2061003a1031031480d0140c80e0700c80304c2c061991800415800200304030f051503134482010001c50781c075103000c1e8443c034800c040010700e1070b04001e011800340c1191500304514030304008000e000281d500d50140111124454582070b070040800041e140039062201094400035591162070500001c0100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 606839532 1250 606838282 606838289
    0x10306051501020f070510090306020d05040203151b0705030912010c0f140a0503041e0609030311090d0809010c05010510030201140a0816030204120f050c0103140c0307110a0507 78
    0x1110110304400700680c2c5406240d281e0001e5034204a408020364140050f10880e40c0c8402d1421101403a1a96218012600220355480e04160354a0410003141402c10040080700050030380c040b95403510002203180c1040d0901d0010080e1004034240301082800c0064500d240c174000d10052020441d507a00c0e03402048410314500008a51030b102652650184c2c000551030102004064a007403401340d003c0d0b800c4e601c090011200404810303442c80c0204144074243d41e68610078880868144004e00b0010300795034540080c1c0c1c07080c14080200e41495038451113500344541d03110140c1a00d40d80081c0059aa5031100305000d0495400c0c0010020001c5c100008442502e200740c841d00c445100c4134656559500809400f00003041c40c0c200803070510f0f401a04045548441890058a0181c030b4141c001240d4041180480d0358100c0180510f040100a00c21029500421318040001c03840803000c031001090090301c3c0b05400c800c00000310340c0f5288074000ca80e90008413002280c0e2203c40c20324200340e8070341c0c00c0e20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 606840782 1250 606839532 606839551
    0x60b0711090a09051902060408160608070e01020a0201031d030403110418021005180d0602070c09020c12220f14010c030e012d0905030f0102130620010501030605 71
    0x70000301c218071240f1030b07185225000401130422a8010b1020350f000d0a2414099900c03203801d000c00540b01c07804010b00c0c82d6010011802d8041540b038207002078410346c40900440c0500018044a03001799900190400449409107004120112a4041103d0380041e004500d50540800900070091180401d08006c11034410744003040240008201450807564840c0000c3d40030003800319403802d051090029180c10b0000c0c02809a0080ca05c00014250181d0440100c038141e03004a02441408455a40800280864101980b0b0140182e004940b1800000382d5005d4824022411440d0038ac01940b000790046522441c1d2151aa01d407685020111514495003541d901d5820b40a511940702d40e28400031182d064403281680401c000040d2222809010980e04000c81c21003800d03c82d06280c03d041280c00300f9074841c240c2c40ca0600c0c0a041c2031105452240d0516030041048082c2000040e0305281180d00382c3c03400c241c1840c01911050212120384007441034a42c01d01e8004400d000c42988124000e49250 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 606842032 1250 606840782 606840799
    0x50901020c0604050d14100906140a0605010e12030c010c03090b1b030a0c030b031506040c08100311010507060e151e0c0a05070b0a0c02071d01090f060b0711 69
    0x1c010070400c0c0c8554003030b403500303c80c0e07a11a1030005074020903d420030104c030009452110554140038000c07900c1010064410640340c00742d04400121110610f44c2210207030105000c030031705040c000713824091802102e41c0100d240303005221701c58006005503090b0b41c00c110001c0c801500507e20041c090411520b05990b03000000c030100e030310a00c100b0401d07035520020741c0b81e0908550314000c401d4001c00b50740011005050b00e0301803240d4560780a1100149000001c40303145800e08044042c041228034101c450424007a0100a103e802d07800014068200c035807110800c40040803042c0100d8240c05502d2006001c141441e03031101c0c030b9078001b16002150000d20010308406551b070b403034200401c0d640090415040044c100201d810301250500420110b80607042852626406a880152124084070741407240340d56080b09911180d418001c640040c000d801928041d61402d02c071111780e8400c10b1040c003030300550b5904036503d41c1c440c1d908030308011300510342400e4460096080c08a28805804d0303059119000b507 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 606843282 1250 606842032 606842053
    0x4210b090d0e0609041e051609080307020906042003150604051309061d01200901020d0e0a0f0605090108160507020d0c2610061d040303090c0605090102 67
    0x1500d94984101035070390400c0501c0316020311183e40d00420185070043d03210442c3c200b040380108051340103110f14000002d0946410811101c40120b03a25010302085646142001112800008d4491103501216138a80648600c000074004000c42c00c2c035411084074010780d03d088400c0d0503015521038001c0caa5202c07901c0464104002c528403442c040d483e40702c0d040202c000c41c42c100e50760090040611540c0001a40722102183c001900c050000030708083e9114165218a0a00302c840b100c50000f0b180105030170803c0600010b0740711100004a40c040010022560030710fa40d425500d00000d21074151080349a503204c05009020b6404100c105010a0114000c2406a84400c0b000304444800e075540c0d0382055084d40c00c2148103040101c003a100d081ca103060104210211801e841d4003000554401004902d41140c41420842d40030b0034850282d15042041103410a8100c5401c500c460b036086140342c51f600c900c1c043c0c0042c00d007100040c2004040300404520f65030000010505424242c003147c009100c1e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 606844532 1250 606843282 606843301
    0x10b030a0f03080411060d150b0f070b09010b060d02070203010b180a0f0209100309051501031a07020a06331a0c07030b0702060103020906030f0a0b090304210b 70
    0x10020008000d084070020741d6011911550707156070018451a04a04140c1403a000a00035400ca4003608815580d00c0e80000003406522044400404950440900b4800d2280c00e10b600381c089c908010707040d054414001000c640d400e40c401440046d000f041513440c0c1d482007450000075003148030200d00035840c03e02083c20b20300d00146015154003a038690780a070350b51201d82e07040240031800700c8603a085400380711180c601c2d5520201c0d441480c1c0301d40ea00042c1310b003060605130b180038a0200f040010740b41040052001c80c0320a1103104100c80718400075280340e01c4d00380040b80b0380821400d002c1c2c1502c0c070703082c03d11030800c41d5010700c1c80d4003203000c40805c041c020850508080241c52440b501100115003080e101250000001403e580c4500c40141e444080d070f0707030f01c800745148811a070840050f00000e0040c0304500c1d09084050300900141c0040c0109240c0c6d60104d5a6003c8400000d0314002030f80d400259200d01c00c000f00d03400340009507400600c111040714035a40c10603087c0380031105041d182c000a030030b119 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 606845782 1250 606844532 606844543
    0xb031207171c1a0f04240803130b0f0906090f060c0606011e020a060c090f0f0609090204210204021606020c0c01080f010e1b031609061407080f0702100f02010b03 71
    0x340020400010540c4c098100801021418411351094145504001c0840891049000100440030295550b064007800410148080346c010094019052040448002d034402c00d44104d0b2205031000c50703070b0322009000a40480d9514200640c4804000380c404829000850348c203005400a80b02e03103031511904020750240c50007102035100143d0060a01d44080340c9150008669202581030000e402511441140b07074808141e004840e80380e031000c00820506a002240b08001e2009840850400303041a00000710703240b0600c200d00c07080c030b0000c0c95001559070310780c100d50800c814549441d1180281d450168043d40140d0407401c01805120b04480c055405000c00d41d10404040076041c03443d80c28a40006c80064000d0a5160920640f641e0000c0c0d4506241c0114021202107104208148a40100800c4100690015030420103920348410b102c10850044d0340c2030300d038800314031510b40d8440405d600c01401981b0300030f0f51103030601d6489110b0a80020004500304039035030090004088030000c1c990b82c1c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 606847032 1250 606845782 606845831
    0x30507061505091608150d0209040c0509040c060e0102120d02090a170705011206030c180f02160b16050306060d0905030708120c0408060721050c1308010b031207171c 73
    0x40d07000b80401c3c0c012720703042280301d9000c1c1c400c6883d43c4c021074032180401c000840c225802c44100c81008410705c80c482d000703ca41c9610f54003d1009003000241e01202907050b0084051001c241900880c170882e056441948000140407410104c0700c040f01442c1c0d5046e0360350054820070b8045200900020700c061124010801601d40000e08000854540070301010a40070740103010340c949035502001c01c40440315000401c02012105000707c140022030510343d0f054003001c0c1c140380201207922420030207141c000c002c1c1c95012401f00e074503d4440c040e0b00d41e050081c140030348005020b4040041c01c4000c0110382000b410061543c00b082000710f0782e402c0080019842117000742078041d8810800241141d2050441ca280d9070a00480302e04000324100580c2c05550003518580c0c50200c0c080b0b003440d60041c6c02152a001004000c0c002d00542c0c0840300403a880b114580300404180200141000c10b000c01a18103900031410380c2c000039a68441c14000c4007444d07140012440c43c00e41003810079040791000c051581ea80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 606848282 1250 606847032 606847039
    0x20d0c0302042405220302040f14070e030a06060914090f0a0809061209060103030807050703080f07020a05030301080105150d11040e07050d05012703050706150509160815 75
    0x403100b00c0010800002542d040708000041004418031400105c88071406500032001c0b0f41101e0030740c4100416034090341180b9814603d40302d00f4400703020240040350380001d03090a01d81c018490020100c2d003080003031107020703118501381000044e00c4503003070748104050b20b000103c85805031150018140c844808010f01c08070369208542c2500481c8281e401000c10729801040c8a00d000806030302070250b101c0071070300071100f600803400410500d81c01100c003030b40c81686854400c0c546400ea5402919204014220341000150705001641403802005410750643e00242207030b07265a580d40e50240079140840f1080d1640000741144110f034105444178007403156100c2d04a041d89810b50060000404001c10020310741c1c8074002e40003402c0d444801000740c0700c501440010030f02c0103a040c0e068001442440800c05020944070001000c01d5000f0141c50180f5400440840c0302100b550b01071200e0025a04400e40c04600f0fa000d0140c00010700400d10b600504644407a00c823a40e6403d1004c842d02440ca200982 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 606849532 1250 606848282 606848309
    0xf0501051e0c09130e100c030501151209050f07030507290306180a1401080610050d14121902011413080d090309230d03260a020d0c030204 61
    0x500c40842c0b8090702032004060305107811012100ba901041e20600c8107001a01d802100b99400d5440c101e00a43c820100d11782000d00c402e5150401c490030582580d109003040000c52201703582c80c04615084400500e4100d01101c025030b5100351081d46402a500c0102d455200c3c0d0140040c0c0c2145116401c0740540d800760071301003080416008818146c0c001050076078006540d000c0c00700940610f88890b40900c4918000141c40308464010003454241138200e41043c0d4480c1d410000e8800c000309207401694029100700b0a401c005140907280611507001d07031001402804040d026180a00001d40b0328460717444a00300168100d20b100ba401c07542c501050f280a403003c0e0340020014001009400704042c03050b0b004a01d0480791104031f50444080c10703802c40004099840411200803041100e1406805d90058422069040c030f0000b06041d285110050030b03c900005006419500c0c602c0d505140042036103c6481c51418040c00350003544264240030f96146004ca0300b1054511920030350341510349510b840d08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 606850782 1250 606849532 606849541
    0x90435042403361202061f030209011a120106020a0308151e150c0c03160807030f060f090b0610030e060f04082803050a0507051c0f02070f0501051e 65
    0x24503400501c00c030320f070140345800002000500c8010900019035400c2e800f0b45840c1c100349901062000072191f101d10b80d040001001d10140e43c44217101d034116075511414801c2868180c2014400780034412014031040180f000000d20a9004907a40705607034031950f03070aa566540c40d03180030440488880310b2030704803030051070119490109170001c140301c060041800241500804445000b544480304916080d04460085400c6003810000c042c40c110380501442540ea050010050743d4003454800500305d440c800c003840d800d02a00398081d41c041c1401090510aa103002c0c20580703030102c0240c403442d0003082d446c001d1001e140d100384102003481c4481000340400762510300240792624806042500c6100c020094900d00c04011440102c0f2440d80c10040d060b46a1254005412960000c00c403650309401c280c108004668090100c0708100702c103040c541644c1c0c000f5541c0000038480140070240103440050810b0620440d0700d850014244640005c0c8245c0c0e403100072880800750f0348020755178421260360106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 606852032 1250 606850782 606850841
    0x1090507030b150d141312020c0a38120a020415020606130e0a0b0a15030c030c0812070303020a090504020315030c0d03020604140c0315090c090435042403 68
    0x10010491f00380304840d15442c000c0c000440c40016540701c9501c0d5010100c0c000d400d10010090303094580013083c0e1007030101050349110030741481031090400d0001c40fa1000a141540e0039070540c0c000d003501052450310764600032000781d92180107130382c0f40c0d01c12000d403074914103030800394000d418007801ca0030040c10f4070305915903034150a42c001800c0c4071f0300c0607145c401000090045410b0f4400943c091148480400d1860508031500480c541084003640c005000001000082c1c1d0104c500c0c043d80351a0050b520f12006004580f130f581c03640c101950140c000428445010240010f0b2104540201c080d600030699280801074280c80380c0e4801809a088100003030b01262400c10104c40d124141070035120803006c0c00e0000f9040401c05042102814818410f12200e51070400120308085010f5070170312081c1c105522001104211004288001420740b058a800c40c049840015540406066501d85507610703100100d07120703000c10704801c41c6039003006229248035100b400307000100317100412403600c0003000e041c1e030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 606853282 1250 606852032 606852053
    0x2503050412030c0f06051602010902090610031b0e030f0106050f01050f0d02280f20101b03150b030103170c10051602030a02030301090507030b150d1413 67
    0x542c10b0000c50086000455059560304030810300c90780c4005a94940fa40031052240d91520501c000c581c07612840d840140ca8000105800c13400885a44a44c208401001c030007401305449140d0300710101074100705030907400800e0440e00100450958901c940503041e2a401c0f2880d5100d4298002240c4c00c0007a065400f03040103000d603040c101c01d064030f0308081c3c50182040c0d90100c03110600030000c14207102e0480c003080c004007100d0245450910340702400d0b444003c1140045003400d07000c0441c03081402240d8201000080000b9460780c90500001600b900d18028605892a07864082410921451460711605a5030000d8032001d0a802d0f0440e403e40d02d80340c1c04101c1400340035030350150801c45540c01d03000c03c110706074008101c40d90104d514075100455030030183c601c2c840081554424803500c4030954011041d64150380d07281d13000048641c0c070075808030090b10324a00081c3c0c10000d1115104048a4484000c00e8183c003082401e111440400c0c0c214406200200c921142d100c0b00040c10000103011042c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 606854532 1250 606853282 606853319
    0xc1403010207050a08030a050a14160203090d15110301050d1b05060418060906120b1012030503011706070c02040207031715040f0b0a06260c25030504 66
    0x40c100b01140d55100d1802c1903d031000d0711845004000c2051441090050b140d04c410102c0f030610114104462035001c24001030301d085083c11000421040c480d20800c2036500a0400800c43c01c03000956082141d40c1c120303001001e148090801f4000c0d00c03104d00e0702044034100c0c0c20184c810710b6000c186450300c0c0410b40100d40b08242c0a0080007000405a4070f00d0094000341122244c03003400b5000c400c2c841007c8500c2035014006c9030b4100b0400b009640283c6009040294004d1891519561020000190000d545d084030044000e075085610901d68003101450681c3c11207480b142c4681c5030068071300d948120807101f0100056a44000030010300341131300038250542c840d00704a46078517200440b82c28a8a0219003a40c10307940050307600745041c50036000f61300003600031800c1001010340540200d030303850009001d48014012035648428060610403100e0921801c034600700c0f103260500c1807440d0403d5109000e03a001c401040c02c4000c0c29459410001030700c0a501d912000d28151811a504144013042407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 606855782 1250 606854532 606854539
    0x80612071511010c1805010e0303040306020c0114070806060a030e010e0615031b0f04050c07081c0b010f020d0e0301020d09050604030f0504180515030f01051b070c14 73
    0x40000403100d0209140c41452500741c0c80700d90359100180e01e1182140d0b12004113a04108950031604440c002da01d80400a951003031a111043c1074415000c24914455035100501035440000c140803105019444090f102d150701050703c40726100c0300004c58131200140d911702d901450811180d009140258051000e8103207041c008515822852007150400004844d104860120078030203016030700d004c2c000c21450a81c1c040d400442c00e001000858242180b40c0c84a5015996074400308020303c940405940c40b0b44d600004003030350307244c00c1500c4455200a41d0841c0b885030342000540300c1d2642c012001c2020b01134842c1d00030b2403a50250a0200d481442080c00c0070b4140d54200b00031451007106000d04081c09014170700070f2100c2d05103480c0c02085145404942000c00c00140028040c1c019030324000c3c502e0002c600c0d4049511380314241040f0b071028441200036414483c18414500360705064000504c144a50314103454541c540009480d10740c801e48000400c50b07509a02c0c140524190303071441660b141d2000c1d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 606857032 1250 606855782 606855793
    0x60f06081302010e041a0310060e220b0103030c110a3813080706030203061305091203090d0320250f21031802010516050303181b01080612 61
    0x960100b0f088501c0e1b007120308140000d1890011880c00d0410183c06000004002000b41714613260060004440c050445503c0c0d18086221840e4111183e904c40100c0d074004a40c0060b030350356454050001c894022045510a10049106026140240a9000302d0f200050603e0140f0302c0240c91a0705142001d00243e94020309c9440340d07101e40c0e5824060071140602400c04020641003043c058a442c00c550312100c1094010810010545c8400c0c03440d07602c141012601151a8035545042401c04003451900101d04001004200e0000000210843c03200480e4500b08440c00320700c0050f80c1142d050050b4041140c00c1040084545228010f0b03948800554845454107201d965440f612881220740c0b06a82050128003040703003103080e201e0624a000c0310782c00c0c10021003514007a5a480c0c0d2061201c06070600502041e83c0005c205000360b1524100d80c028240c956a01e44036050b515a1000245107103220710034051006440c408145103103592040c16102e40720503030355807020810580e004185840840c050b0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 606858282 1250 606857032 606857057
    0xf0a05061f02100e0a0c0e07020c040f060e06010c032703061505011806020601030611160b09210d020a1103040e010e16140a0c0f060203010504060f0608130201 70
    0x11655a140c000702207074003a002c00501046418203a0301038000c0d150850300700c010300c5000a101c5035181e40480300e01b82510380940d510007000703904050701d000c8101d421508151007032400030860340c008004c0c3c4130824280e01d0b1030f4032580c00441782540104402000b1a01414200d100c2904540088140d52803280e200b44860341c0702d9540b8030070784040440d03118460327040d42410302540d078000010030380700b540c45a038040c0c080c0d00e00000295100701c188000741100340d903590040e4444081404840b41d40100700d54000a0800924242003101c00c129a600201d0182d0f00c40905040f404001890035200c6a010850508a100c10888000e41c00400d01d07a0a02c82c92206681700741a051014100170300d00700600441e03641c500f550740d4019840081a02c0365008080d4020700e01241c000300e412420040e85841c054031100e03803504c01c3d40c013501107610103849102d2803510801000b826400650681d42d09540c2408120703a9290b0134214500180141404602c0030720000c0e1250123085c8080f9510340c01450403060303d02ca0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 606859532 1250 606858282 606858319
    0x150f0f092327070905040c06020a111c02091003050d1d04020d32060105030c18150d0b0a05011403070f1e05030403020c060406020d050306061e0c0c090f0a0506 70
    0x46544001c1d45130791594200002c0c401c0700202d0741c1c0241058000740c1008102a80d0310407003800000c2105104030700c2c2c88100425485014120b801c0700360301070001c0109081588480300360038840c1c48101c401340300c1c02d01039004107442180c40304810002e1105003540300200d44100700c06500040090080690b03550f2070840d81c0d29100c4014070861400a900c0c07803856844207074041c11017000501e034905000307040080c482d0038003140f0105c8900c0c1c1181c2140c0303107031003c0e90000104003c0310f80d444410502c00214000208202c40d03803140680c00001c03a002ea089503a52401074400581511f01881e08281c1440000c02050081280d411020864031300606010b150110051807031280300503003c00030340d000c4104010150100301c0300d410b9100842c0c0ba0341c01c0524001e0020340c1c0d2017099001e8010800c2c040089207441d10344c002a50f030f01c1c07044500b0034031707050750548241c008a4010820800f10751040c100092418144400124068680c41d26040496540d155000015000140950303401045da10415003c0c002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 606860782 1250 606859532 606859543
    0xd300207031d0d0c05060702030f060901060501020714011707031112190e03041802090d140d0302040b0415020c0306101701050c0d150f0f092327 64
    0xd10948500c501910100a10301110700c003549040d00843e249070308440480c214800070003c40b2000c59000ba0703140c4043c40803909000c0800001c140320703c180d4051088960041d0000c0c01030352400e074200c42170b096680d12140803601d00e100005001c11011840c84180106290000b5444182800e0110345440f00086001c240e5001c1511041e580e09000140040e1002c07002c000c80d0f003920f800d1410301c180791000000c25120f00c0342d0302c914080300ba444806428491065019030b00c1d00c0754002c0a042102038181464100d03444d481280d03040071b02400c41945081e501910030749003500c40e8a0161814a8208940c030440321000221100a522580c865074100f40da08100c058401c102c003e40709810306140004040b210400c0100b82c00b601e034101810006808030040c02c0d60f45c0c501c1d5070f003c04204003241400c40030709200300ba040080710b088041c8000c03c004d4006030843c804c840324008104103103040804140b820440c254500b60b8031485103c00f155440c0c190449034031303030f64007500c0b070b20280c4880b180306151501 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 606862032 1250 606860782 606860797
    0x31704030801031a310b100302030c03030a0522150207050405060111030d09020a050d05010b100c031b05121201150513171606020f06090d3002 63
    0x40c01d441c0043c0104000f8045200d0000d038102d100b003806040465101c400100c441c2e500b100c5e615450b0f844049000c400b103584203010303a00050389440500307112a940d110030310740d800141d009119000d0186e610341400021220f0744c20f05550348506000c0004c030f4040300c195001000f509259101000440e40440c0c1d050f68410a07501c6400030800744d480c11040c00190741d070041429060105103112140c490001004907039242e050380ca0001808007681c80000c8070b44d00ca50300160740102144d054007040203415480070b44200340c1203e103802508200318080f982d0002104000f00042c00e00d4100e0742c0300781504200002498403400c20b68101340c9031500399030240c0d004150b150301c0803072404004001c19030a29004071524403262034694a03040119000d10707104040c9124028502d031141c41d81c01182102070200700d06090303030710b0060240c15542d460029500c48100320664154003c048c08100848800100d14200111070340310321082209040715100e82c0307410780c100f4000d00301800c1440048003a02e44000c0111 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 606863282 1250 606862032 606862037
    0x30206030f060f01080601090303120e0f060a0501050d0c03110f0405091605040225051908070b0a0b010914010201060e07020a030210020a140901020f16170102090d02010c03170403 79
    0x185814030820803a542e207003c0050600954005202c6a030741d00c00c2d440c605503030305800e00125944407001c208004014080c0403a0140c06020b01041e440940403034498010848246d081c0041e0b40c0391303410000b00c1e5100600c001d000c440ea8510030800102400d25001803110001c0035411401542c40104081d0f450448a05083c0d4002c9110b0041207110603200d8000350034240c07000c50801c80c0304e0100301c5445d9022948080c943e40c000c00c48400700001003084034010102c160701840c6501d51490110a543c001c030340d04a0700340050300005403003040f035442401110a0160358442c1c4241c60490000f92414030401800e0455480301e00118203692f2000d1400c1c0254290b0f402030944005031304008cc1050008050707220038600400120040d280d02403000b05014001d050110740e920341e2070b40141d241402903010b15940b4001c0010f4284402421856201125114000700f1030302a0032401842c00c034400d020425a101c41d0040040c405540324070001202e0520a0500d648034404125014031030182c1100c04400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 606864532 1250 606863282 606863311
    0x60e010b0307061404060c080c15100603140103021005090d14010c050304110616062903120d0902150d090606050d12080709050a0f0503150402062203020603 69
    0x80d01d050030811100140280c2c5440c44144601c403100700314901c00c510908041100c0489140c003400054000c076568a070404040b02c1482240c0d000003842c15500311030080010483c4140041d405000303000e00c5038441610101c0c50220f80c295420042000c1d010a000010084240102c0701d4980b42d4248242c0098014080d00b801c04640c048600d0030b541c0c0320401d04040081c00c1c820720000419004c1041600c0070101c031130302d03150700c01c0e08800d0071900e02c1c05e1800341500e4180306c0140c11416218214080760038450608580c0d00110b04d041c0369942041c80c1c42002d42c2001000302c0c03d51050154058048a4801040721013006441c00b1500600d0300032a4a812206a0b21400107041211901c2804010542994080300101140e214541010700a60700041448001c1c4005007240b8440c0c1d401e0006410010103070048151520b08680b4150080e002c1c8a0281c4160f140360032610f005095280d210b107500a0031035142568103081071000e44640e40b0308071030100d004000480180e95080c09507104144900380a403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 606865782 1250 606864532 606864551
    0x1c0807081819050601270c0203090405011d0601021606030f0f0207150e070e0f0403110708070f09060f05060a18090b13050105010503060409021906050c06090309030d0813060e01 78
    0x50401d0b1381a8402e40c19000f00d030030980040b0702d084d860303c1d00000c814040059200a00e0303200343d04603c51030000e69030041c0b91030004165010740300c8841d0003031802000410880c0e41c4000042e6a035881100c00701e02019251070040080e60b12a400c407490310131008a011401081c915220b40503604201411908071103500030b0003184000c2e92082951941c05900200b0b0300b1464100043c001120241141030440030315400902454000c502e10034400000e07004071000b407680e6030441a1201624000d1480a505064000520a42034003520341900c4d268001c801c17101c3e15000400c110b90b40311a200a080c00540301080407841041120500202a2000003091010151041100000700c010b40078908074502801403001e40d0b40034080e2a0700070740c159800107141c889400012460900d0302d204640c040c0d5024404500141d00c10054a80c04103201c0440d0a5a02ca82078450380380e0103124080f5826a00c0f0a400011840c812074241c1c0c3c00428440e4040d00d070100c0345c2c50301002e44e401406007801c203030346404030708 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 606867032 1250 606865782 606865793
    0x120c051b0c0a082503150c0c0c0807170606100c0c080f030301090605010302071220010218010201060e0415150503030703020d081006090b090103061d091c0807081819 73
    0x2462104e00d0b0b0549140e040d81d943c1101004440c400c02c880c03645d5001d2003d00b00380681b500106a83c0c002c0b10580c0c50326900c0050540c0c503241c41c00b07465416802e11103401180800041c845024110040040c81e0902036408200d910340040348056075a451800000140d0440501421040f888158040c69032507040a60080a85140b82d100030304141c41003181c040415140f1241c050405071610b0030341400070601c8030000c0924080c07140c0d110103502c0002d030207060442040030310304d11040a8000380b000c1940c0d0380040c10210803c5501801d003c41d03921f11032032446190341c000407200c403111360150500d0380c890b4042482e50300011030460150f4003d51a030410140c1108029500c11004041000e1180c10320600a00005846c840c841c1e00000206110301c0c1caa0082c4c001c14064260007502c10349013403140202c2c0b105e036617042c0e8858080c2e004418102c48500d00f00c2d00c81280c400625151000580c0700d15904980140000300b40301220104000564282d00d0b042c0b201848141040303140c01c5520b051070a08 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 606868282 1250 606867032 606867073
    0x30516050a030b07080c220509090106231807020f0105160c0206091f12150b0f1b10270201020a0206180d0c06120c051b0c0a08 56
    0x110300c2146010002c00c001202010800da1049203441c2010036510750840d040d0361070064498204218020341e00c5a0b544006030160241146c6045802500a440305400305088400070301960300700007804500d1009014148821086170030300501100240859003401a8424505458540058000450041441c0c0c2d003405529088011030300ca0912281d03100750003915000145600a000714408940c05031565125201c00220340c000d070600c9182000b07000030040064058210b1185480c0c501404036030f0302c001c10821401074440201c04507180800a80c51041940c00c08554404418440034984d000ea1900707002e2010310016403080458200c500280c0381d600e10610b100c9079462000402000d402503030340007a0100504d501503883c01d566918803031801d0b60b045070303100070b15802c5030314581c08404210411010100304c0390250380c1d00402c02c200710700580645120301003c4000440a104020041340f00d9004180070602c8981120100031101003c81c0351115103501515450f000b6212440b10454075656 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 606869532 1250 606868282 606868289
    0x2a0d110111010c080613021e030105030f07030503040302010503090c03010e010507020106120b010501050c100603050d091d180307021201060e0f09120f1c09031b0804030b040203031201030516 84
    0xe0080c070101e1900241290001070010307204900c586d440c2880d0290a1781214503104101360200c03180841c02d80348480c1540f0a00c6458064403c0c8030454200c1207001c600c001c1074940c05409540f4061650300112115000605605c3e0a4068030706022203699091003054500c104d06c4002140c6072615080103404c45840b1f5000d0046465400f03c00000074418000c401e041d19001d0800b651101d1100c02c1c090b1070710314500c03034406000e4646031001c000d00000081102030314015550703042c0d02c5a141c40010044080c0950900c0641c00c801000c58000d0560354a40040101803804580c180b80580c0c0014804a58800081103035035983c0f00d090008003080c0480365031101122a03908064285405180e1341c800c00c0781010328005a010424000100f000f008450004461040c450080410800d914009201843e0200d01003046054000031440c402c103480c03080c1d40c1d040040b0504192454448824810b401042280d16010030400e104440c154800141e020310b00807401040c5851204404107070100c001c0c1c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 606870782 1250 606869532 606869567
    0x7080a0608070506030c0d0e15010312112d03040b040e07020f1009030e100f0809071503050603150408030114010c0c03111201020a050d050c0c2a0d1101 67
    0x70010f1140e80ca8500440b07400c001e045d21101da85024500c8200010702400f19000b0705c502521110201d002120108607060380d0186500b134088000f170000a5a0a680f90f2000d109542c110041040f10740d2152081d643c4280381610b00b0003445420500d0050450303015401001d40343d030b0003103014070941920700c2c65540d103e485400100b995400784400950784400750b407014000c180d110b0f4558000c0501c2581000034400025000740c0c03d5800880c00a45040c2e900284c100001e0604000101032040c000b41c19412100103c1c60700b4684803c5c840101c01814008200c0f81d09072003120300350300f0000c01200b4441d1180e401070a01540780e50405010242d00c622101c5080e0411030703003c6400c00414103082c07041040340d0307010343d0840c3c6005602010424001c090391104800d9440402c0e940160b641003c001c003000702210504000a60311020090118050005188031551080300da1810140704200c2c14000da8030882043d01000041200255650000314400c996203c05900110150350300000894231160140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 606872032 1250 606870782 606870793
    0xb04141509130b04060b090118050f040c020715030606110a03080114040902040e01050901060f0815061201060602100f02160308060409150504030206010609030804050f0109090507080a0608 83
    0x100c80c205194050040458401c0012148000541800381d0102c000548050024080141d90b1501c40180d90050104540400d01044242d142d001c20002c0c0d5506403803000300328022880d469821710004100308004c1e80705510480c0c1003c40c0201d904000c5d100d40900310790b4086180c1d030409a0041041d0b1506204240c00c0d44040e602c0b20009402030190f40c15112140d1100103100b090000050280c03c40500294019140200c190304010045d04203520030200c8100922085039240e441401d001c98520a210300b40d0082404000078034030300d541d82c0d0703004400104018031122480d8482421030301c0b980d00c68400340e03011040c41880314400c2c0c0075030406007020007070841c2010031001e1802000c1c00c40900050410000e80001000c075580c9611450f41c02c0c0c0c0204d098040c2030b913503040500007400c0507502a80544111350000868500c2040b205003034990008005060a02d0501480400b0034800c40d018107000c0702e1031012074016040d10506118504036a600030450400381003140c01c55031a60000d103003a8011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 606873282 1250 606872032 606872059
    0x121219020f0a030e0f180f0106140904021602090a020d050601031e090813030b0103020f030a0203100e1c17061f0c02060d0c0503070e01180510180b0414 67
    0x401c16149031030701400c0804d140101070002076003883c507900c10258440c1c091810f80948020160f4524810480d880d8550440e90b08c41d030007074030305407000701c0b090b0111403080051506604040c0c019080c840417201d01c001c1061000c1d030000e1196441120030580d40399020034013030b0201d10607000e03080e0000000c0c241009080151054405110240042d45c0360041c2c032100d04c242000782da10111401c204a400b07442c00865204d03e0503540c03003502071205078826071840031b080001c0d290100d10036402e91750080c0181400d0303001c4806940a003540e07070000d58243c0105461540004ca01074424041d0700308a0b9242540c1403c010f9034446102000303040c2900440d28901207400003160200d40d240007801609101d0054002072000404a1040042c0c402c03015007019103c840254100014600070352040c1c94001c2109514001145d030300c0c0c00100d500c0303c4841c24400401c0141410b0320499614a003520309448a01d010b0240a4001c07519940007503601c400000b410020000031000020402c001254118814481c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 606874532 1250 606873282 606873313
    0x30216120305040510120c110c0f210a0614061011100b0402130b1e0309030301090b01020c04060f06170405100b01050418050103020109051c060b12121902 68
    0x81c0c4d025072401403800c8070030480c844d402401c0b1046802200304040c840c02648030300c01803950b0b81c0794686111a11510728540950b03d04a011143c242c00301800070f000311900c680a0600c08a02c0210041e001d008040c23040307012802a005a01001d01c446a030000300c2c2c02c00000f40400c0345c1c5c2120803042000b22521150031469804550f1290811284030080b6480c10b042c00003400a01c5645041c40703240b40c5480000450001ca0005000045495103035001940e050685803070341e91000704c5003550355030000c000511115460b60302803a031030081072044a40001c0c040d000700d8201c0e40583c0000e45840ca050404000c183e030300c503241000d86040c2d41c40d40380c114181542c072166a6800c180c0c00103811030f00c40b668603d09034845d00c2920010b05030502401c4144144001940c02084280410707170008096400c04243d90400501c60468846060420034948003691500401000003c40055100032100103100d00c1c1e000070448002130f040c00b403d01a5032148881c1d006002078004a0915013950400264a002c020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 606875782 1250 606874532 606874537
    0x90803030f0402190819141914150907061e090308070602070f05010603021014070605090f1614120c0f040221090105070801050d03050304050a06050106030e0708120906090a03050307030216120305 86
    0x254004a02030b0b01c07549c0030040c58104180c4918185000000c0420030005290000f91601160019111054002e29510180c08484810302415000c01c441c2501040000c070220010542e4500511006080503256503400c0d440f41c203400300c161400c0e91580c6050081d40381030100700c2c0c01000241410f44c8110f200c500310781c4141c09540e0300a00043d9444002907107040090180c2450801d1010981c5d120036400807080d60600c09a00415414454040301ca040c2800c25000703d1544c9a041e00040c88490000b508200c00b02c6107003080550007940070f01c140403030741100c100c0d81c49445c10485802c1d4881c1c41c00f41c10a40c21030350002c1079902044140f4004201d642c0b06c4e800028241600752030401c2c1e8070340c0c0360b0070800d10704841401c00070000c0e490140006881c55141e4401605203440c03205680403607035604240c0740da503c101d101d0808180020820300045150003c01082c0d915409040e2100701940e81c0c0302c803811504070308030540168029400355000d0802e44100303440903000d071300c1401c14111881e0301c1c02007960 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 606877032 1250 606875782 606875833
    0x80115033327050a0b10050a020d09050105030103080307030b0316030506131109040807020a06090e06010206190b04110703020106050a0b030f0a1821090803030f040219081914 77
    0x890352100415000c05258120000c17616000d40078211002c40f2290007062940004402001406110555150b6500c00c13262102240c01c16990681940d00355181c01d80750390f1000e006041031503962200800749440074442e8803046000c0b200701040e0b10703145003070480c1000d0300100300c141c04052180800b8001800005000c05908041d0307076141650782c5a00d882107480c807444401940c0900000000074095510162900c103680c0703510b0011205850311001680d4952b0700303841480c0311030b840e105a00360301c5003a544820340b814001400070410001c0310300c00f859940d100000550060f51900320601042c20700900103801440c004864500e50b21307003015111205e94014020381d01440c0c031400504054103840082202458000810700105202c030300c03090460b8080e12680d400480d1030b81c01e000540001c044103980c820249e450301705c1d920750b80b5a404c1040e4102840704038140ca01040340040380d940400c00c90f401000340048100300d59241c06044c103400000b07811601000f990302100c03070034582c840031180d200d444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 606878282 1250 606877032 606877109
    0x1207080f030712060b090a05040506030a1106040504050c130611030d1d0303090d0e180414030c061302010909110904090c091e060608070801150333 65
    0x740d03120010102c1c0c202c0c8511005402403420a4808141d21400d0300080c07000b041c086402c0c03025155100c00f848291031089a44640c540c001003000000f04501519200040000914086c50603890380001021160152060340c01c0d04000b040d122150000200d80b00060003241c00e2440d101c4414030040c954903c2900c025040540e11050842001c1e486c40d0600054607040005890312303850406a07050356000c500c2000c0300081c200c00124800c9083c2500000c2c011f4214213000f100f5551076850f0502445d1560f01048110710003008450154401071003a103025184a50b0302c80c10a082e14000100000d0080d0410901c43e40362005080c0d16495210403a404100c0503500170a801c0140d0401d1a600801680082d0b46203041c04485500c044c0c81d010020180701c540c5000300041c81d100d520031070703210707038200c2d4203078041070088005100f00301418916840024440c6000319210124000342c05000040211146030510000504080c5202e01c0598502600d242e11010b2903c00790340c01480310b01003440b40c60005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 606879532 1250 606878282 606878287
    0x70503070f1502070f0e1e1608090a120f0e06180103050a0b090703020a03061205070b0c010e070b03061f020613030306031a01030b18030a050c01091a01081207080f 72
    0xc2c4507000b8001c2000030030f80b1440142c5900d50300c8600b000030130012290b0001c60040c03051100a0280c503101882d000c1ca250102590513041038000503192100081c042d21520f100d402d003136000240444115408a000ca07684a071003015041201501401040310305034403c00c001d000c0d17000e100800401d51a491102480e01140c0c5440d900d680b0801048400c03011034200d08200b04100286405030000c0c29401410382c0c0401a461340c900b0001190848000e000b0482c2e00300c6c02c8200000054140034040000c01070000181c810b8150500524141c0300740e1105000a8000c402c00c821860005080c1ca50340c7c2582c0f40b034004142d04160000c1d100d01c8000c00c5c941034008241140c1041c540b00345e01c41c0c3c1c05907500c6070740d041060348880808444c000c000d20085030398102e010005010710444540482c04403e4030001103040154003e025140c9401c2040c011000e90758849044001c10301c1183c04918004041d460b980942d410400500e041c000c0d9001c003d80390160401800c00003c00003021030307004440d403c03035440c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 606880782 1250 606879532 606879569
    0x21306050304080711010c020d0308060307051c1b090204080a0201110f06220b10030c0611032a1506041a03150408090307060302040603180f060b04022a070503070f 72
    0xd1f0411504c08020b0340240c6c01986580130103410500c5180550400c804964041d59540200f090203842c0c200042d000031034003c00000010102d04c240300c450b0748009a824009611503680c041240c0066000003c1944503d2a4009558004600124408105001d814601c150102e11682c8020140c4811041c10314020b55052100c50003400340f000c2a1301c0b050b0701d9418205284078400e09100d030700003030b10489114880000c205008030761200d0348030780c0710002d1070a101800a54500a43c000f51b4001c01280100a812001200901014600003d0941001c40f00c1c00d00c0b0062100711160400c014080088070810300d020b641d030006c0c00f409004048010805581d0f11458241064020040019018403c0810100b40d0342d4158000d0401d035141583c1c01c2220403000508120840e5a810001e000c40e004070441c030010507810780180003c142c025202610b49a47c5625400710213030600c5140000e0500404411010f01d410702a610003410100d0080000c1c40c103003090360450074144c0c4240c669012443c88445c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 606882032 1250 606880782 606880787
    0x315090c13030c0f090905070b180904081c05060303160c120807140606220e1902120c090c070303060b040b040312111c03020405040e0102130605030408071101 70
    0x100d90441c1c041d40c440081954030b240400c00b511540c00b400d54070f40000300700070801c5e0209101d62851075030084001c0a020385841586200f0360301035410b440c0030700301c0c0001d00b045d26195800000e0286100d955400d503201450240389801c0802080d20f401468184424080c460381c1c0002607031148880440c1010b280c0441e443c010307807181650b600c0404034124806c12a01031001c4400504031980c02403040d580d828124031081a15254120307115030b4047c00f910300108026548940a003031050380080009501c038580040c60740b0300003000700390104030300803818094214180b6038041e0680070144c000a10700d0f0201130f80001c40d180c0000b00b02148505001c1294420f25100b5000f00340208907035201150703140d885030850b00c0f540d0310034002920741d0b56860383d00403e06807049040241101e0100b000e46000c08080ca400158060f4030500c1c03104142c0c003404041041da6481c41100c01c003640c90000103035100b0944581d000020f595a20180501c00e05100300300c04550105c044a00007030b4448003080040c082100107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 606883282 1250 606882032 606882037
    0x90c0f01121a1201060512060105011b0312061518030b0402060c0a0f2315191d0109020a05011d040203221407120c0306050c0403050d091a0315090c 65
    0x18107520040f40d0341c01001d891419444541602c6d4203844500700546802082ca41d5600c0a02c030b4140000c00c444444070b44082d0701110111100d1091400c40c40d16000341d08907a0698045400403511003481c09061801940c0007404142c0d150b540042d10700c10f0300d20f15107419a0b031020041000e4003601c0002030fa0160b0301c50500c0100380c1c0c0c5601c091104030102140c10421200e030030351600c00040154015100051031000a0f50303c0c200b03112600e0000c1159150a40a446102030961400e5455141c01c2200d130a0301c901180000c00c440e80100020f56110305004201d9040d40e01c2e8040c0f0305000c4205000d01c500001c04540c04010941964003603034a468205007520009030312400b091290503c400c07114200100c080204801034004400c54602c1a106c540c0c50040d030078004401004048642c10800004070340d074000c2d40c0c2c4041202021420565607032144d900701804102c590000426000301805200743c005d0740591701c0c0c2d080f1800a07041d480d1071160f40d40409050303c400e610410382240041d05502c4140704 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 606884532 1250 606883282 606883331
    0x3060e2205030a0512060604120201110c0411030a0c09080a0807050703170d05010503060613090218070207060908061501050306030a06020412210516051203010e090c0f0112 76
    0x4803607540c1c842c07000080c07042d00690010a581700010001c41d8442c90084240e60a5410540c0c030700c480d900035503006549002160102d03074214024111411100d5540744507502c0c2075907500342d40c1365072803a01d06151030440788032800f00e2080c014003281c10f100890002500c0e210040c1d21401240d80c4060038140740d40b824283c1d80c401004a280006d034441404201da0241c403090144650512150b6200d50030162205000c5039040e0f08410300841c1485814150303042070110b20700152851209500380c022441600c9022142c0740701682c84501e0401542d030f4081440c10090414401074951820540c90610311007449410903810444048042070b0a540c040c0400f03161581d11010841d500ca5480c00c0080001c14241019528030b0065021405004803000034514080c0d82a03650a150a4044240081400382e1401c2070f15244111059011415088001503001e841c4600d00382d031061030040310741890a07403040010781c005d0f10004c039107000c03e980011040c080940381e8000400c00200044440d44203035440342 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 606885782 1250 606884532 606884543
    0x8030c12010b0702030c040605011d0609030304080c09150a0608150909010b0111060c0904150909050a110d0213020a0203090301091401050609151c0b04111003060e22 73
    0x80c000103066400200078000e0030701c25000d490804102d4004c1008980d8148a01c40c0840c545600d0b01409000340f40d1404e09820004202908080020000c81d2850b00590002c41060340300341e101000d58a861041030340d20455844c405d001405c81c010101d10100c49510660091003007510101c2d1080c0210994480c807444007501203403e40c9048140c2d240a00041e10413540480c4c48120303101030101011610b81e02c1441d000c001e0a1414001005000c000c1007c180d480d084450340c9140840c01991074021002c2141c001c10003020176680c0c506000c3e03a07440e050100c5c1407040c00b211346100c006889080c80c1c14003440d070741c0700010f80310740309000164150712405641503403551812800c0410800d0a000c03112614448070000c00c000d035070b034805200a1401c00d8422522075259406100038070328120085c01c201c220000b52042403d00640c0d10b045082d101078400711441845418144000e040035180300413095036030300d024405203142ca41c50302004840585100307481c01d0b0806400b03220311410107092034102e41c4003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 606887032 1250 606885782 606885817
    0x4180b04050906010317042402030c030d0203151c02010e030138010801030f0b0601050d1802010201051518040c12031101150e0105100908072d0303090308030c 70
    0x800c2803600c5a500340011035264031181b40c1521000a100c003500c050700c03c180b410b10180d05201000c001024075509200c421480200469201814180040c140300c101d120009601c904000c0814001045659110307409515291030808c0c62202c04032944a04a4083c03c0035200c403813142001c42d02604411107189400d100b1200112034a4204024a003e143c042c40c00c031f070215890000046408600c28800030700900c404d041303403c010500d14a0502e800c10310506009261003404400b6400303948201e1204002114002d103050190750302800340c5070340001000c0303126080861020005424803030048d441a8000c00c004000741c1001075030308068000d4592824808148429481d00908000600341c1c01040755082101c1d22103110744032000d00017070307807003041c3c080016030b00f0803042c060b483c4529044a0100322105100280c6298180700c42e038058100050100c0640d0494a90b140e0382d401e01d108020084045041c1c02c002103507004c610502a20361042d0f0240d0340c1e4840b0685d03501240150003c40c041048030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 606888282 1250 606887032 606887041
    0x40b1305011a0a1706010b210a0608010b03010908030a0b01170a0b030706020c0d082d0a0306170703030804050f0f01060512010218090613060f031b080304180b0405 72
    0x14003200034000d220448070725680c40c0d1500b00131043c0c1000140d83d0540d83e880381d80180031221580b00a000118010348038801da04800c0c3c02e104130115400d0701e40742115a50f0f848244000d00007030240c0003407210140c0c000d01269089584400c3d641c400204088130b1103039100308102842c1e1044480008880b0410312400140c00d102da0010001c1c140518441d201c3e20541c0e20001d005030000c82c140c0c11003100180ba00c0001805a15190860340c4012120340300d880c3c6c2c100b0b00e00328603907202c410300003800120540170b9124011050050300312003050304440e1130b43c41800210000048000f9400c1d086e6070741441c05c01e000b40c45d645020340c0703441510343d000b0045000e5103c010b820180f05503c51000c8410448800c2640499031031110700705e11400c0b01480f0250200c41c0c6861140c28040400b581003a006002040c10910a000742d10840300c95401c4460b01c8801110104240b1840ca080a410051210035800c201490312160329501c0c80f882c0302e281050300f0302d07080c1e19142c1e0351550700c10304040b04090820f0005241 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 606889532 1250 606888282 606888311
    0xb040b03010e010e040305030f0714130801051008190303060b0c0d031b02060601080402030c030a03180f2d090608030918060a060c141f0b0303090108040b130501 71
    0x9001c2c0d2400c004064000080c1095061921030265070991621865601c0b20390404070080300062404050240c52407001100b00d0341c81008140c44c544840d801400607081445e094251403000e414503070818429813043c86000008900e240c0b41c1a1b0091400d0f0a682143ca13040d406009140d00135041c030300c40424090000113020510081c003000994040150b429140c4104940400707031005038006901030400107031254050300d03d040d00031340024121000c1c005c1c0000028500510490108c0010764000010300200d002100d002019085403000b0180060a25003015403000c00c1d001c07840d00740c002241c4025032800f560072005028150f40d00341400b0b459124584955658041054a40209008484100c112a4044520b0300419009000d81101c1d80f80410456009400e05000c1c0c4034003080c0d803060024800e041245103080d1449406108919401d4442e140444100304001c0d4040e420030001e000150382d0003e461603229a00103c1440382c0e88031900c81c00b40c02c590041c0d00910962800304d511000c0c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 606890782 1250 606889532 606889537
    0x60e06130c050402030705040905060307150527011e050f04030c0302010e0904022d0a08010e072403051e040b0118060b071421070201120e0705060d060b040b 69
    0x1401000c0d88500103542e041072004074401102c0407000640d0078401480404000d4100580004000b0211150203860365926000008941112808118000307140103d000b1075059880134422491190b1022199100018101102c2c421900380303100016011040510701071011344081c64001d900041d1569140c1c500406035032100e0105034041206a09a03c41a107000c00d1a1440743d0382c05090160010254600e41034650440e1224030250107100612020039100c810044004043c1000045420030211461070700300a0142c0100d102d80000660b100e546c944605020121010740d80b500060760707507814105501d040c008003110020042a1818482401049081d46d4165014030315414500d1072000c09040c1120200d10440410031001e011003400f2540300c1d420340401c42010004c1c0e484c0e040c950401d1220300c0101c90b415424492022841741c0c1907507440301d078404020003018010401080c4020081c7c0c0c0e5202a880f0705032094000090304030038400303940c00610003000c0300d265064540f81c5a01c02c04050341c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 606892032 1250 606890782 606890821
    0x1a0307030b040e0c0609030705150421110d0206091008011707120f0602160303060e0709050f090a0e07060c1a070507060b06041206090303140601021504060e06 70
    0xe4108014107125140c40d20404240200040007012125000030511205411905030580d260188080025407502d8480d8662401903512680e181d6446c140031000c210207040c4503022011001611414001804042a6a907058401c5804800400340e1340300050861040010f120303080b03007d110706005680e0f004285181a224012001d40744500500011692606640324072140417a100c0108404a00b85d070130003c51080c0980b60151500800c0041c100500d10044001c03400240e80d40010000a01c100f20016001203c41c80c10150280c0340c180000c020b94201020b462048250402040034002582d102c0c0841c0082e0000ba01d01c0076555031400b80c840011004103840ca48900403103401c07020f04644015100390116203a00e0304190300354640748024124070504039000402004041200100300d03590b045e03842e2180c9404124550704d480e005003038070740c0e8451032030300a007030001400400d071303004582408a42d80655109415685030b09009004d404080d00005142c018482032200d1403180f00084011f5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 606893282 1250 606892032 606892037
    0x203090109061404030b0a060b1b06060a0b030705091207080a11061306050a0c0b28090201082d150907020309010806040b0409050d0504050a0501050306030c191a0307 73
    0x2040e0741d00740c19200d01003000780d43c02c6884401c000c00d0000502c8951525006070110100003032658035034840142d182d000845070018002400c2443c4c6041000b000720950011040d6081a2258544034003103055000141030401808070218005696484e01e101d410000303d100343c200e450346503440600310784a0f400b0300c00c1038540201d45420010b02d4203024088640304800300986080c82c03440c3c807800b21807a0708440580010002c20781501804102c1d03150b90715000d059030600191802c01c055051071541e940203100fa4910b507040031803000250ba0030180803607110288010340c0c20b03402e44400640315034038070350048141c01200c07070300a0050080c410310b83c040380000c0c103841c0030045840311182070b41c0d01d019040d40b02d40010950400100715040503040710b5040070b4050008250042240c2d40d076801c01c41c2c50a203600000760080340401051620b08002c2d0014003007801c01c0f0349582000340110391114a80341101d4080d4542e01e441520b0b004480000d4402410040d07020552003803508280c00b0260b10540d840c400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 606894532 1250 606893282 606893297
    0x90f0c050a09020c03091c0506071e0e150901090f03050d020606030a0c060c21120609020a050f032706042d031d0406080705100327060902060a02030901 67
    0x410102e10302c202d07440e15041c2070040d0309222502040090480004100f8241c180c2d0803840c0d6000240100145406050552940c01d2945907929141d6401c03110b41000604001c043c025620042d103409030021204000b5080095980c0345020050712600d4256001690302220300300004113004000c80c0701c02e045d00c1b00b642a02d0150301c508040540d501c400c2440500301030195201049454022400c803101d281c41802140c2a41400c281c82c000134004825104000c12441c0842101c11105407240d0005403403603240440c2441643d0500814034040c0302880810000d0000105030007035600d01c1c1003441c0685440c004003803e90314004083c1c40345819202261000c0c0030706c48416002e087c00106520034204c1c2e140c07446c03c0d00c2450300c003207401c65649883d854201c9000c1c042a0200d40390390040c500a0700d4600000c00241d03242c403040c031207102e41c50307400a000c05141c40555248200d100d060b5007405005450412040442c500304030000b404e0001c1c0003940090006500c0c2e0081e03401201514085409884220 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 606895782 1250 606894532 606894539
    0x708010c11030d0c021c0e12060114010c0c08070f140d111909060807031b0f260a0f060b09041119050a090204080706050a02030418090f0c050a 63
    0x8801928484944034550800d100104010b40c0c0c59021448030314885c41100c480d10605c031174000009041114400000d0310080501c481402d104480c5200c004143e40280010740c5400c0c1d49080f0000a001c2d614108800d100ca65018019090990b8014000210035541c25a40c3c90740050304092081c03243c1c42c150050000c2d860b801e0710381825a12a103540080d50f03804d5600743e0f002080b4006081190b4640300400301980880c0050091295002130000070006044041c2181407540c10344010004202c0e511241c803206000d00802100301d0310866180f140b8440c2a02004034201c1015114a0706004c3d071482030f80006070911280c042100340f0036020352b00400042c05070006000d01183c0450700904865641001c00318542400c0070064080c414403624814010b480b0300014a120015038080b003092a000f14040c01100010300080d0b004080c98200145450443d10000c0c0d2607000e40c5c490310070420009109115403030641d4000c510780c9030f441540c03c1c5800c5074514080100601c0c40c001c8600410713002d680030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 606897032 1250 606895782 606895787
    0x1802041103070206130b0609130b18010b0d0c060503090708030c03070c06080402030d140706050a0b030c010813060504110d052a060304020d0f14010917040b0d2c0708010c 75
    0x700b80176900b00e509001e165641c0c0040c000070500203400c0003034034040c484425002c50a41c128150003013400c14107110503d40070b0f447c01402d503400c40010a00c2542e03098107210000d0040001002101d0140c01d019881380e8401d0354260404c2c60580c4a8406070000149101c124140030004004403442041409156501c4501c00c80711940101d030000d4044c0d1003000c01d40c6003503005030001c4d2900b407440b03100f842c03800700341d66209130035604156403403c04652200c0000c4c029140901029071003450a20701103900e4640316040385016500b001c00689515555400710382803003444403442014940180608004403190701d05142d030f400901003940101820500314041d1949180314000600324020302d52419510f4940803c41d9840b504001101d00d0903070b151004000035041070740340d6848205240001001001c80c10b140380ea421117041c5004556104120a02a8900244c1520b00380c011022002032400c0b203404141c0d0341098000c0c24022849515148008070b0b03d130014103601a00c202100a1006d9020303800705 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 606898282 1250 606897032 606897061
    0x70501080c04350f1005090a2613060e0102010e06010609030305130806130c0e04020904060905010e0f010e0c03011a010507030504031703010608130c091802041103070206 75
    0x440c4606880c001c2143c1c0710f00020300d030002588400c80b00792a05000d8482c520743c50080300342140122038102000110583e8114400c0d180d0155440014014101c202d5561311103ca8841c80310104503507181d65a12500d01c0c1d001e05840407081d05492003020f4540f100300180c544c1c036403203200a00560038030f03501560840c404500541240c005481d6000c0c500c0c1155800d0f204c980000c0750b62240030b12200c0b40024800700400c0000c0c060711040315004401071040c2401c3c0a41c0c4000d400000182074400240310041c0c482221080d031007500020001252603040c42d01e507000d0031000c1a901032601c692031050f19101c1c07043d480001441c814000312140c8003400d105160a846004454440400500c2c03048030813540240b009100503132080c503119191688035503031445d400e40c00d59145c6850841c048010720115800402c025001680c0c2c002000407148550f8894100181c10300803c81040d031616100116000070050080582b540100b05000c920705c0031414103200e4204070345d000c005202e410301090505a00303059 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 606899532 1250 606898282 606898289
    0x204062d0905060a03091203021e040b0909090a060903110d171f0b0408030d0506010513050609030703080d1b0807120c0e1f0e04060b041a0c060405070501080c04 71
    0x3a0841c03000d10340020000b682d00090380480c14903440e43c18075030001f0f5400c1c64621290655440060f10f0703805410305451843d6031b58808803003a680030881449402100810b4030701a800031110b104440d039400d00d0f40c80c10074072280801021242021445030030980c0083c070b070711a07440e507a104440e60062000011101c42c4200740590f42c03c2103030180450f00145c4850f2100310440c4c2c8607083c01440d640c0d10900303081c980d0300613400342019404c08540000c11480c07070f008036034101c44240380803418104204000c41d10083c0074481e280c401c0400003003d030481e4506124010045401c81079890700c40101203844009003d9511481c01100c1c6244a102c8115005d96081c41c0500c009685540d5400c03000c4d60b500b00240260b5015400b400710800240c54a566049910340051105800d030701c9881c8100640505503a41c00c0380d5044c070031418071805100c4010003105840488966083e0100320000040f81404148120300f0b00300401d018500401c01171090002d4514101da500f030b80d8884030b580e2405608001c5001c0e074003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 606900782 1250 606899532 606899537
    0xc0d020c0405132d051905120306060a0c11150702031c050a0f03090f050327060f030a090f141005040c050409020114030a1d0d0507030813060204062d 66
    0xd1155140c6202c01050004c8200b01c240c04c402c03034a45500c4151030043c4c2c13680301058194449201804005041c80303003144145d011801e075400c50501400045082c0101c0003d0400c021100705d1401c00d111074620004601d01016081c58100418500009401c1e0b21052084e8004c0c441d503400400b2811030703081354890301c203000c5d9030f0301c3d04180d100b00040310720031001a2007800701500c40200d40b010821401001e40810310500083d0769034648581109c0b40d042c01405134900b13501c584040e00415880345e8084a100c1079005806682d01c1d5610700444004002190000e0600f03040030194104002c050031006d000e0500003c12981854251038040c010b44004690003001030f02c640d1010425401c041d001900040e20504050160300c3c6584001d01164004039004100a9240c1017141e1428059804282c029888280501403070400340c81c01070403174400c02d90024104040f80d00020251900b28803045003580d480780d400c1d5030313407581c0b040001c004105101c020182603060824090362441903c034a158159440e8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 606902032 1250 606900782 606900803
    0xc1911010804060209130e06070f0206181204030c1d0709050f04021603030501090c0c170307110102070503040f06080f040308090a0206072307060e0f060c0d020c040513 74
    0x44032411000b40c001c4a010381c09100401456079441c0301c041080120100001da03c0785030420032860004054104d009000d01d4510304075885501044955101030345200a51070031000880141c03520f2003400245100707101c042004000c2004400300101140c58160312192140c2a0300e500c40000c0d4415204080426520380341040f03a801e11000900d1011001040182006040308603922003140c0d040003200080c1e65000180131110203885500007078001e61070100f060201b56a10b0341d442c22042c0703840b403524002c04000140c4040c802c000005c40c0400c0000299103521040c80d01503500d401034005c0c000c061610340303c0420041e02c00c0c14568400e44040c0c85003259600d03545c5040d00c5021018194914600482010784050303110740c030080c0741170347c419040181071010404800081c2048910405a81d8010500030014554001481615904200d5420790f10344140d2000a00b54419104001100d000341c210840746c16802040750502c3c00e40948040c49650384a00300564410190b9500a183e44080c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 606903282 1250 606902032 606902063
    0x304031e05060f04120c02010c0209060a1203021c0503091905012711060307080f150d0b070807030c0f05071b0f0317120412140f0c19 59
    0x1010209086100800558480103000e44840c2c0c1020400c55040c6904424042400204000c080300360400240720303d0a83c19014684e4002440d02085410180c4a48000303404100c80380e950041020040c070342c08165504444840c90045c0d20b600001204210704a90301c0442d2010714041c00c00c0700e210b9900d2201030038483c03602640382c08000e020142c06403031541d41e81f46654208180d1207400c0441c2e2103d21294aa004624501a02d800080c5464a0702849084c02808100340d001403045420a529500e100e82541e14a600c0319250104d00c024182c1c081401c01108081c071841440b00340c02480c503075072000c4581d0b56402d02038083d22560854030002601d441c000c020150b1013000a0164503104002000e0380c6550a5021f0306c4c07035070b000d030080b911600001000b00100034602d286041c07a00da51441c2c071800c1980c81780340010000e400400241210520345800c221281c0310301400c00e40382030b441000540700d04a00c0d904801d0360b0081c20b010141449011040c4150034401081e001516030304c2000c60100e050b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 606904532 1250 606903282 606903293
    0xf0718090c08030406050c0c151608070614040b1005060406050c0313080c0a060908030702042406030b0a06030509120f04031a04020405010b030f011502070e040503030621030403 78
    0x240c0c5902514003400d14000072a007000280028801051160f9503031ba102d02200706124203140720300d00a14850110301c0c002004040909054888048209440170440542401c01180c14840c0900003440c0524007070364441001d070300420550181e40580541c00541c2d4a001d030785100c0144e503014030350b4050390504c030410945200d04000c1640740805029281032806a43c8502c00d03844003a002004130b90001001c5c400681000f005d040014a034030724142403480e103008805034403881001c001074000ca80b2071000020114420b5890440c0c0300c40c10f004081d206a032248028010504945400d00c0380030400340009d00c440c440d007d000d0148010743e0140000c215100d00021b2a40d010741c240c0d00308468188000400710707814110841c000c140e03400039401a854030344104021268140c10555183d070003801400100b240704281030b41075400d400b4030184001d9a9010682c41d00c07038540e0200b035203940c9071002c200c01c001d0702001a60280c14103442030304401ea02c0c01c1d100302c40d40a9000501a40758800d0008001158 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 606905782 1250 606904532 606904541
    0x1b020a0b060102070b190305130804030807080405060714060903120129040303020c0108010b0c0c0d060e0102040b071101030209240d05070201020711010e18040512030708090f0718 79
    0x201c050048940050b5200b07202e801603042184154050148a201d802d034598040c01121f0f03111903032a141500020081e42c40d694140514040a0070300c0101007034810030000201c0481d00903080081500f0344031040e034030304142148200b5123698140d01071840480c603941400000c1d01c0300c280c3e00503c1036101d80e08050180d09418034107035110f030003035261048980740601c03140010005140a58060710640d401030002600228041e4407603151001d04200003840464003040100c1c41400885030510050010b051240184c03088541043c103952001400040b5408150001d004481c4620384080c6a5841e80c00103500701d02680b40b4241d0031200c002020274028070209502e00f81005440c50042c00d0000511101003140c02c212070500c0903070360028003d02802031000030152a0302d800d1800469114126000c50748035004042503940910304100810304004c1d080c440320722085444c0c1c041a45a18054000034000c0c441540c00e038405018075640c82c42c0701d58012a000342920843c00a803903020140710401c00060 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 606907032 1250 606905782 606905791
    0x705040302040e03191e0203190e01020109120e010909020906070803071205130219030312090326100b042301030f14010f060207050a030305090102070305100204091b020a0b 76
    0x4e010030400c0003408070124148035100350f8140c0d150503000c80175244070f4003010301c10b42c4058113542c000d003c480d440c411400c112a02c4482d0f107151081e0810000001030340074050150000f00130140c401a400c00d450741c4170300c0c0d40078a40001d0766240c4d890b942d10180d0b94204d101d0880620380001c0200200c0380401d82440017190013148614240002c0c0011040140031103a090b9181048600c3c0e03030034134400b50700c0c294040e54008140c0ba07100c64442031541c0c0c3c0c00740ca084220380d816900c0a2315250700c00240750103040c50321680e41089091448642040b0100d241d1890b0484040a1900c1c04100101e0f03203601e500c1c2903505583d10207008182818107842040081001820b5483c1019105c4509400c0350310350707018000319040d4102514000354107280e4507000c0105c69400800071544011401c11083d1b071640c1c00542101e8141c2040c6540303d0490004070300b4107140d074201400c1c0b48110152000c802b101c1b90300810031038900d04800c01000382955a01c2246e16210004580107074014000000421400454a40c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 606908282 1250 606907032 606907061
    0x20a090e01300609050d0806040213050907020c03120a090803070b07030209130c03140a0b0f0f150c0601031104090b0403080a0e33011802030c1201080f15070504030204 74
    0x5507090380c4a02c16950352600485d5260002410456042e80101c880c90f04554100c80030740c20101450076002d202c080c14810a0300c5400801c01050411380248900d442d500400b50075501c1500340303020b400300a0390282d1621400030740b41d403070300140f403000220542c0c104a42c040e017240816182c00d08118041e4201600056100d00340c0c95490004c41201d1090280b01d035010307240800d245082000c45413115a00401e00c407006c1707051079003203071040d503811952804156007220134800154585012642c039041c08180081100300c0014129400500003585074101c070310036850001100c42560a02040d41c40c1d00e0b2000b0103030000c1c1e00c01300c1e000070300407800c4036400300c84100c00045202c2d007001000e10346003030b05030810741c3c1c90007500300302c80041c5102d15080028502d0507944c04a5500d4108080c0b0240040c15064661540c0800491001e164100c200c03007400784461110045942c4400d100354a4211035110b85489200e103107611204000c6403002c03035200c1c11881d1034003428145180c003400b014100d03d0000444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 606909532 1250 606908282 606908369
    0x3080a0e2707020d0513061416030c0b010f030c0506070611130515040e1f030b0103150f1401090c0c020d03110f010218010c1a0406020a090e01 63
    0x3200c144074200d40203480c1c0403000040e6420603071806400d0031a01c012010400c2801c00550b00b10602c4040c03043c04481907403820512078000d101c0714480c2c81c060249842490001c0c80182c0c4249513114000380d188038003c019100160740e8801c8903944a81c1e691100400ba180c50308020040c524044020b8500e042c000c1401040750401c1d070414642a40c810f000003210b00c0301790042803002c0c0c02c00c1420a145102204050b038078003800e05075034880b4054010f0440006803583c1081c0034102c0c00c100701e081c0c0295809610300ca51035849190100c0c41d640b401d0021462a0f1a20240e20791005540c09400c61440d84c950980405908119401010f0300034500d0fa0720a000b00701c9415070050719020840c034001402656468440070074590701c282414546820071019038014003079010500000300d1101402402404c001440f81c2403403816010504448000e86082c1020904210520920b0340080c40700304030075605c1d8500d80b0384600e58000380740b20a00660b1210f0780f40d1000301107150f800b0901c0503011841d400340d080d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 606910782 1250 606909532 606909559
    0x1b03030c0115140105040b0d051b0c0d08070512010b0d06030506010b0c0f0a1515030f060c0306060c0c05060a091a0d0506090613051005300703080a0e 66
    0xa0a40d12038000066280c1c40e070440400c0649610100300b0102802443c22500d1b081c07800e180450180100a13075100d1041d5601c01055080d100800080d0090011119168403520080041616030620152060200e11284005030f030441c410b10844800010865070300c0703600c1c0d08212408e0301a402411000d411180c0e140c40100c04a4010010300c4d00070014a10140d907075025220015082031207240e812203d45c0c0c0600f0603d030005041d01c00c5006c140c1120200041e0b940f2000385c08108111150b803028107102c460090703d40500c00076801c241c40d0301c001c9413020312545940d410110b03010800004040c100040000c007d001c50311700180280394002143c68100300b00341e00e0700702006401d03191801c01c001041d0002040c0441c0c5a03103028140c1e1000e411220740e0494074201d000301d407982c404c440c40f1400f200c0d525030015200c6002c00300800080d000282280d8000c0c100290340071800900300c401c03070f040c1c003095920014400038006148000c0e04c0d230203440d00c0e040544418060b0f03807500244500343c0e440840c0a4441c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 606912032 1250 606910782 606910807
    0xb1006030603241d0a020a0f0e15060906030a0f270f0206131205061f030f0311061801180302030f130b030a0c1b021f05041a120708040201021b0303 65
    0x844000c0d50344d00203080390481e130b441006003810a96002030403038114100e00300520002140d00b2603000c85443c1d0451a840044400540b1910400014a500c80801b01c2031024901d900d50220440385200f40c1e041180001c07002a098a0050744101c00031004d0180d4910400175030310700034101a0b1803001d8011420030741c80813648024010250080c2c0d5520818003900d0381401010010541c0004c1c8141c036650f90040e064100701b4443c1d80e240005000d841c0e50070f0b80c2c0d00800d4806e40c190f5030f8480021050300d0560620800350740b00e41224444843d04d541c01c4ca12118100e0000c0d8007040d201c194181c00440c80c18520450385100c94000c4110220000d00090000a03a0031205d001907108074038404001480c0c0341864009000702d000806600c0d040c00000040c00c00527100c88044070038080401200003102e0300c100340211401d100f240c0203070b41c010f00c0098601d10041c40982c09000d921541240202040c0d40c0c46070111401c180499001c1e006030b205c02c001e0b0740403048551041610400150580703103400102410f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 606913282 1250 606912032 606912071
    0xc030c01260a021c0903140901111204080115050604050904020d12050a0305070c02090109050c090a030c05011710140a1e091b020a0b090c0d0b100603060324 69
    0x75440302903000130301c11031078012283d00c080b41c0c1200894100700990660b02c0040000b8110322400c0b100b84800501d600c140d1f8021302d03e21141c0c00081c0c0484140076908041c205c055001480381c50780c20340c2000034a5009403550400482592000360840c1d0401d0302e0002044004c010241c8141d811482c0608400e01144441c1030728410401c1c60384403281e540710425070050489030000e10714400c009400002e04010380c1d42e8142903046030200c1002056070b4a03454070f22180d62182c00c8001c1e50180000e24004104070fa440e500d0401c5079030980f01c042050303040b41200300c45408101d8240c92401000e410501155251101d07158403404082e26410b03d4540390300e011580c85090162441641040032810030000d825406008415230795101080240001c945001e50f40b06420600108101405da001802c02c0030200004c400592004241400400303041c2415a0613030020381d118503103052102c034045441d034068064a0200c0340c5c49083d44818060004419a110502a00341103900e070b202c1d80a508a09031700d000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 606914532 1250 606913282 606913291
    0xe13110a0314010f03030c0b0406181b0b1c112710020705010c14120301030317090601050a0b18150903010605120c22060b1801020c030c0126 62
    0x100021501d40ea03640c02c00c142c0d001644094018410550203200107503024000c03030400c5500ca16010b503292030368607010000d4902e140080c0150004010008140284220300395031a011140c0304136a41a12950500050320540aa407130008819120250b140300311a44040e82c1200c41041e6142802d910840b10f0411000c020441c8041c089040315050082c0f5003a43e094908028a00040080310300d400c0020b4003c00392410058075006205100c0343c1101024800094100f0344242115525a141d28002d0030140d200108401d89486150010f09058400900d07036041e60300c010421001d5a00e0251883c54079800006000b580b20364401c0700d0f071a541c444003030903069070b4040d480f031035161040d00d03082c182140d00643c0407511501c0d0301c603050030841d480810100114042500d07020103000c40340c040700108008040601000624001d00014806001406030200449101d03d640000d500314004981e81d28a034005694507410012030301002d980a083e209084002a0340d1030305c4c80c243c81001c0ca1884503030131903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 606915782 1250 606914532 606914537
    0x30f0501090b0703020c0114091f0b0d05030a0f080f010506220320060301050a0b090102031b0604020f0910090c090f0b0415080f011809021c0c0f060e13110a 69
    0x290280c0706e10320038020882c1800e203040400c010761070700508042d561440c40145182118000c203643e25400381540004403c0c141c09025003402ca07160b454020f40d20741c440d107030542c0090410007500900710b120320b20b494050482000c100c0c030300d82d081030204051603010b0038000c0241150400c0407030503d40350301c401000842c00703018041442c0d01e14903a100c00d02c100128103544521020030042c000c0303075100030803002911817240c0c5954466484e080140e01d11322038211443e44141c49a00c3da80c0d408000001c503203108a200b51010701602082600740100114140c4525910030300034203003803050381d0542d40503a508a0b01880c100521039030382c0002c41440b000e983c010700d01c0d203180041c05200617240c180201c4100e0f1410b1400c06524604510900481075041c002c000b0b232145200104590700425030000741d40d8980050841039030750b0040e00b216000d01e014110486071514410000900000c0c3ca50303441d000c5840640703480403200614020001801c00140406a0843d9503900c4444401040d1000e02008a950b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 606917032 1250 606915782 606915787
    0x1202040509091c2102070201180e04020a1202060318070f12050c0913030c020d021f1d0f2701030507230d03081b030a0902011d0a030f0501090b070302 66
    0x4500503d62805548a0014401608980c0412144400055008030303154180141c8451940c80104d810f4071803030410a411845210000c24041600020140075034800c668002043c3c1d90f4042001c0c60780d0194102952020782800001d414100380204504022280d1041ea0910380d00c5a9212050801c02d8201060111040c80750100304041048070320b880040450700364041d850014a00c10b4001c40c0940001c040114139030040e01107444028201c211035030300801c5130591692500c105103c0f103140004660000300450010250a010424034680190001d44151521207054040c8a00d450b5441c030030803500e1021044a07058800840603007070103548144092321082d460900e15003a012410071082e40072810360310031242165030b50019000c8c5240d260400030006c0e610055000300c44550b43c0300c2c9200001c1c00004004d403610082d40300e404114401d8854482407400d80092406400d0170343d195542000c2a0101400801c4114004010b01849a400800d1404039544c41442c210005d891010100c0d030007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 606918282 1250 606917032 606917053
    0xe03042c04032f101a030c060c030c2a041e1a030d0809070e01061e02160602160b0c0307030c150c17070215010506180a181805030901120204050909 65
    0x40c0500703007000d513103a0029214081c17108000780d00d4001010080303100d0080015180c48420302401a10360554a50054400501c1810a0036604140072428204104e61200001c00359190601c50b0b04c2189400d00800702e107034031390004194014060704280c0e0030084698030a9021554041000d41092102503441c0002424407440ba146025138031b4001c030345011524001448601c1e4401ca0120040c81d1000039954201c25800b0305078149280794020800240341c400010403d941c000607800025a4104a08080e05075100c02c8103484d4000c1212141d0240c1040203401c020030301c50040001d5260147c44030848039050900c8902c00c0328000c600320008179264804240d0300f41030b000c01c580e5110125001401da090300c0e60705211000c80b01409001c1c070544000c035100d195150f8042230b1610001000d064001c003103071119401c94500c1240b9500340000c81c03c3c0f103a08042c20000100b54040a9030240065003009040401521b00d000d088200c40712070b541c28080042c00d980d502042500628603c17002d09840c480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 606919532 1250 606918282 606918313
    0x40603230607020a030e0907170a060323030d0209040b090f0403020d0e030a0b19060b1e1306080a0b0a03060b03120a020d1b05010e03042c04032f 64
    0x1d00342d20954108001c0c50000c0390300700b5140c035008401140d04145a545e0b00742c040e24080340081c52589111108400c10603054420340c400000daa0050104003091000000c0b055801306c511104280307190000d00008070042c0c10340e005400040b00c000e102003080741c01304c404030b1201c0500300c5650160700346543c10b0005040d0103000c0304202075002e00c0c103d02d0000180d40841d9a45c004890010666102ea10018941c40840c008050f102952184284175407a40c842286a2540056210504905840100d80d4840c2d044008442c0940700206080d298545406020b450140300100f450901c03a407510320310754003590340759581c3c1c01541c0310740c000242ca4090307841450316004803200c0001ca12102004450003445e00014011401c22a51401c03403910102e13000c46960b080302c2c010004200d50300305031600d56003810200280c01540c0040c0418451b0100f6180c00450621900416410310314400d4040340200b440b50701000c00180c81c280c0c0040105220380600062180d0300c03072060300650450f400048088a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 606920782 1250 606919532 606919543
    0x1d0d0c0309050d0206191106130c050f090403110109060f061509032001030e0f06180303070801060c06020c0d0f0e031b01030504020118060203120a0516050904060323 73
    0x20042c2c2e100f50780b02c090351340420340138498400c40b0380c4207641c04007500000a200301260100d4845020550b0b500e800d152040303554900300b4210403a40b40101d1032011034142000401c0c0b135903c0a0040618180c0d8071075440642c3c2400440740480c0c0c05548800300d10002ca002030003041541d5007a000002206858920307041e912441070442041008181ca0007000820800da078000503403040c0c0d1542441d20035030400140d0003020250300740d0410340a4031091100c0030034013103000e03446840c1c510160707017420484129964580c4000c44a40012507ea60018840c052003107010740080b80c0b040c1001071900d0545d19001d460040740a4003000041c0100c121048100da005907400e2040300190000c01040c0000007004100a5091034680d040507a5140040d0540e071103010110802c040c540c3c0b42100964a9407402500c2e50b0155060a81f16218030b03001c103a102d405131250307078442c0190114220000c0801d04049841d0350101c04056482a21a1400720204450049140410341c12011203c280d24081e08810700700b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 606922032 1250 606920782 606920789
    0x705480d030233090a02010f0e0d0b01090e01110c100b06041205060105031009050604080706060b0705010204050306130f030810080d0908100506030d0c020a03060501081501090605060405041d0d0c0309 88
    0x58001170302240050b60041e82122544115040000000000c103010800b6100040c4020340003182c41c1000082851040c1d00c241014011400203018180c2e0029031250035104900300c02c1c02c10740c01920082c0c03801c2d801d6417142c1d0346681c2c01823201d440e05556003522480c4035102c080903078440d001403004009524007001079124213003100e00180805040ba0f00c483c1c4c0c032600c00802c06458110700040b5941040107a034040703800341403004000c41d110380081c102035000350840c1c010036004c1d00c40c04020600081201c507080907150303889014148600342e1654121141500908412000000d55001040c4a100bd01c003101413542710b41e864843d05450400c04a01e040781c1000015105458001841099100071030b6048a4018600f00002161201e10100300105616800035051900c1c0c14004180d22101041403070310101030201c0d44065036298011002100c0c19403049031307402001044104171a0a05400040c60b007200c1e0b10305001c10701c0c08052524203007024409501d0024505907000402c2603000358240015 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 606923282 1250 606922032 606922051
    0xb040f02120124110102090604150806040902150a0e04020d091a04050c060a050d02040e01050f180a09030c05010518060c09010c02040e030705480d030233 68
    0x191415031103840c04845900724000c041056804c0840d0038008250105e0b081160040c101c2907a841c1d440002104c071440d0030421200044460000c10340b627107840d001b41d10441c0d40040150324040c84a0160104a41c0007040b104c00b40300b5a86241030344c40d5204c1c4007511294910401c00b05051859103040e44080004100b190071202d124010710000c1580020801420343e41680c840e503442411040c140d840340036103e002104035000080c00320314000072070f50150480380203035248100d4920540070030060407016a0300c0c41c10040d9010006a600802d6080320745200c3c000d05000080a105486050039504120745401c2d00751003ca2404019a03000c1007990390100f002401f403400c2c911548002440d44040706c801901ca00c4d11203c0e000c078071100030720813610030079440011a100a00003078070103202d6007508180a40c94030b040c1040749207840c0044400880340c0100b01d05078024031111804024080c520003609400f14030541d4000e002c02c0e601080d45039540b130380451407958101e00003000c041200800400f503064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 606924532 1250 606923282 606923309
    0x8031005040e0601030b040c0b19030b221a0612150603160f090b0d0605120a052a150705160b0307030504111017010b040b120603010b040f021201 64
    0x2c4045010440e141541e6001c816004030380c0300e50412041c4050789800c40e0460f0400001e005141e40312000354803074040d000307441c103003d20810407081029945c0f8103e020300007001002d5810b0f1041d540c590044d03c91440505440701c001d40c800010400a4000e401201000200d80d002d01500721060040d1845807081203800342c1c51803900409040c2899106012801842082100c0c070284500a280c0e800c003034610440070703070386030003951184001521980c030407e030007034160a060040144010501640c0550032800030101d0022032030b040300880b0812210000f20382d21841200301a50350340c0f0707c1c918840b40c1c403030f0406407030f0b004500309541400d000d5001c03283c50400c00c90382000462050000c1c0c0f81d01090750b00340002c9681d03950809103d0b8080385245290b01000c203100c4292090b8008251040e0320040182c480590781e21182d0680b814400c901034500108014072181d28604003110a03258000c4000e000800d031a080c1e540442c003a035030748807404903d031500440e1182214040030a401d0051132071002020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 606925782 1250 606924532 606924551
    0x1e03060315020f04140f04050702060402190b0a12150807030611120a2a02030c0609070e0c160807060608062809030c02030f01020307080709060e010c060b0901030803100504 76
    0x400ca00c139502c039640c6003814090060721695900d110480d40f40e0000340050242e464070490094036201c0440d01244039840e008003500e6410201d84100c803d5404a0001902e40440301d0b5082c1c0d04200082001180581c03502c45c640c0c0c40c482190356100c0200340c070b040107082c441c5c11490220162110008c80b8207108a0500910a900c186003000a07008090342000040b41030940140942482c50b401c0315041c0c4041c0e4028140846500200402c030341d69000e401e9954079150002c41ca500d602c441c2c0304e00c481c4072882d04041840c0c8100c1c0c0c1c009080d121036070300364089285070a030b41d5040650016401074610700e641e07000030422050248211640403032460480300c0d070701c8210b64800e80c03542010000d9140b999550038444041501918181109540080488041d1038240500e07501039441108d6400c0001c04040100301c1d224001c10f004000e980140e11130070f240c10161070045903c0d042e880d01c02d0700c01036100e03600c0210320b03201c0f08403d0b8080d6010f010b04c1da40d245040e0b011017055110765801790f03008130725001555 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 606927032 1250 606925782 606925807
    0x1e010e0613150507110115080c0303040e1b223605090c0303070b10050d03170a14090a06050907030f080a0e061b12281e0306031502 58
    0x52000002c1c0b440050039031181a81102c40c14900c0c400c01c0c101750b00e802194800c1420120f00c1c201142c0c9160100d800c1e030214401416200e00880c82090090114200417602c0030707482d5060703185820708203400e0074104108030900d138051100464840c080017403052418020260590461803614444011010b4202d5081c0b40c165854941c1a041642099036180401d101c1e00c0c00380051180d01c80b0080859881e9155828007440d031020a42d00c0b64081d03114040005541c0c1084444004070300d815031500d0114105022043c001d0326002040140708a5980da44c1c441d01380c60242d44103000e01c01910040582d1001b5251000840fa00507015144c0c030740c03220908100050711418038160700c99005600c5504c840c000d440503102e0b5000c0b02e140960001022070340032505010004541038094140e400c136942005101c0ea5031144d880b401c1030000c100484280d02c9400100c1032036100280000c01d2401191120691071002200c107140d0341624002926981c0420034010b400c100d80e82c1c0c00c86607507130441c94010f104000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 606928282 1250 606927032 606927053
    0x303060819030516050f0f01050a0501080d050304151401061220041802070b18060109090f110f0a08160f0807052202030c120f040309050f031e010e0613 67
    0xb4a450781004d50392001089018450b414200311508200c5038100900d00c80c1c180070f480c003268030000c0946030130000110043c001510ba1011900c6c2e0700c6046c61519651581c240c051041803410a0494a59a02c1140c40c0c10f0a00f0f80341c000d012a54580d4100c41c01e882000c82601d030760f00982c01e4643c40c007031502c0740c00d0700d4a84100e07811128070100500000c40e00380c1c00c00c00640226100a03207840340710b85c1041542032568010002881000054441d00da0721200c0baa006c8071090300001d81611400ca842d40d00181d410031030b1842100c4000d00e1060144500300c002005070b00541c100000940061113001c0b9040310800340d01000d42500d100c201050b50400f100d02c7d580d00070760720504e441240b2110081008150b102c5030420b11220b18070742550307a0b143c1044500c00350781c0103060790881e04c03104400041c06003100395071840c050781d03040c0c5d80c040140346410200003c415844401c13581c18062400d02d500d0f044040380300880c44205240001c40e010700d441b500142007000041c040085003124141400014000064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 606929532 1250 606928282 606928297
    0x30606030b0a241416050706021207030c14100e0f07050d06150e01150e01050a0806040c0504090516020c03061b03220302060f100803040506070f08040303030608190305 74
    0x88a0190b4a803200d0482c0c015150740d60940d5503100000707031442e280244001d2030005c40c0c003600480b80a66900c8504036038410b50500481c05a85082c0321050000e4855041d240245000b0102d1100c03400d604501c140c245894a43e0004134a0b984111346583c06000340326000040d45801e024188207031501d00424040030a8240013071130f980e52804070602035003400344130034050540f145440041390384030300b110b030400190025040d0216030780d19612480c3e90311520488500350010394840c8200c0d103c400501001e441480b80341c00a0060901c008202681c00b0303c6414400c080038030801010441c1e00380702038281200250300328003d801000130001c011400b02da00e0602c0c6804a000c0607901d80d00c11991920900554011603960990520035506040d40020072902070b04038568000f000e5140c06c003042442006500c220071281e001404208802d01d4114040e200030f5008603051144117085644403290f95115420407008a40d540d042480302e500d0402c401480d0804075003d6840f180519100500280640351 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 606930782 1250 606929532 606929579
    0xc14040609300f0302010609060506070f02030c1e040c0e06030c03060406120f05070e1003020603450d09031209090204090b01031503020907080408070206030106030606030b0a 77
    0x141035110350340706035000d00079030000c0c01000b0066807031858540b01c10300c5190000d8005608200c400f1800c441035204d85001c48000a088620749078040d540d0480c62080c1100c2607030b050050320b20115850302c0307540c0c4c0c1200a02013110f55104483d245000c100449840245178001c001d1070450100e42602ca81088941110f0040d100640701d81d11280050060040354101e100401036041c0c9140401546403401000d03180702d1010f40312025100c0c110307250400003c5660525500080b0720170809820441d0041d5004615041540b02c81c1c420701c13070322110703241c5881e550180d01c0c0e40c880070b40122100c03205002d2101d050700e00040c20a9015440000341142c001c0d02028081c4040c1c10002400140562a240000c10f5654030664440d613544120800516903400c0c4140800d041003c21002c9104040060084e20390040215105880780c500803640b00e103008104560403681004000090f83d1450003542c0204602ea4001c05d04074100080102a55800310940340500442141844038808a8641c2e07003c070600d18 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 606932032 1250 606930782 606930809
    0xe060304080c0a0605090d030e030901050a0e0a0b12090c01301103011a0712080702071a0d0b010815040c0318060914070f0909060207150c14040609 65
    0x60400711580c1c030034488903101c01e20035121403c00f04440c030f030801441885410180d5150184402c4140d0a40c1c1d1165100d2031150402c06c4141241e40c000c0000e0041107d29251440c82400c0c1d042c00f1a080740307507a0f00004036644002c5800350150003130007202c0e0760003c2d00c81c0c050b0008288050020344408442c91b0322400700300c4208071408981c404645201a124500041071102d8059010080350175442801001486004c003081c0580701c1e1900c030120750f01c641d88120400b904070211801202c42d80c00c054526000c5000d81e03a80064401d170a030088004140d4811f081640d100d50f41e289140844105101d01c42c11f00c1110401c0014120307042031130290211090324086a580840f0340e0450041ca070b00c0640601244100c0c5100050160b66800400e00c54803550f0221080f000c5084a07036a640f07240c1c42580d82115610009015094040d041381d44c0c450b1244502500340915517440c0707001035008892940c01e140d030310b111450303120342d00514428110400900306072800741000f01c02081a05140603017401d21441 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 606933282 1250 606932032 606932041
    0x3020c0f06011d011e0b1809041a0a09231e031306030903020c04111b011a1804140c10030510151d15070804030311150f06220605150702010e0603 64
    0x47c00c0d00052900e40140300c420a842c042c0303050800034100b103001710020038101001954000462290542d02c82d00300c0356030000c1034032441d40145140041c512065240c0110581010503a9542d11541c2e8070380700c40c2c03001d944c48804022600003949080d5010038105030400307800b80007080e00441c40c0c440444050340d021802190031800d05880e03110383e1109802420003110122403584041d80316044440e811000300c8007801d0b01000300320213050302000030a0450300407001300700003441122684640d0520003069514989455002891403640d4445d1748003c42c1d11201001207404a110312840130f4042590310405099500030002c280d041010130401e1070400c03000e00762100b40d55840f00c0210080b4020101641e4031010302c0c1c6000c5a802500c021004034440d40010708512002142400c060748121160200300c4d9241f540102c0221b03409081e81d03811801c91000c1590003940141c0840e540010070b10086017142c68541446a249109031445206100a11410700182c1e400121500030003030845205840c1d848 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 606934532 1250 606933282 606933307
    0x3240a051e03030d0906140114130603050a03050414150f130302030a061b080603100c05190306080c01031b030c020312011203170405070603020c0f06011d011e0b 71
    0x100100340d682c1480007140c440c1c030b40d5406420114103188204001c1c8180113450540480180e028080c9400c8292400c00041d0941480e031001c3c0e0f0700c05c4103003d01050b029900e0302c070107003090300e014429400940002024400300c80030160501f4600025200e6500804070410042d00502802c8000d00c0240380c0081c007200707880b07085031030701015540080640f001c104507031070070078024031034008071104c8220380580807040c160044403031612840c0b002c0c001d040000c1403803000000418440a4040a00c034080c01800c0b1150314850145031031185a841c0041c41d42d050100092a00340c3c0540ea95040600301200302402d2920095510110746850070041a082c00410091b811401303000414891440290000921145c0420011007164081d0b01d07613055105221140501100040b00d001d4555400000e0403c40309200f03170300820003001d0101c181c8602c2c841c15410306080206c20713844820001d500034449400712030680070080c0148240c5c107050b80e850059042011210780a031064101094001c6000c2c4141d81 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 606935782 1250 606934532 606934579
    0xb1804150f2c01060509040f0204020304020a0e1501021c02031801110a06050a06050d031d281a0702010206390c070b0f07080904090609050303240a05 66
    0x4142c003101640c00c004040b10401288010001a1043d07007000e000240a0421b000001d001d03030713040001c05048412507000c1c08065072011b001240c00400f419000031300e0318030f2a00c81074003400c00c00d0b82c4080f800036107000092915890008040100214a10911445400004550b022031040206030a904607080040c0ca4006401c034880200703014894004013002541c0d80040e02ca094041000c101068035074090206084543c00c0045c0030034110101001100d0305e0802c80d211880004041c041301c1e9140e051004505004080540c40e00c550000080c04800c1c00000621030f00c4000454150411105400007541d43c00041d01d01c044292100d80400604002c50302403051740105071480144803290000c540800740c1c4001076105e200d0040f40800701d00e0302d403400101c69444405d010400e0400c1c010303444030400c5030300902060341c2c002d540303110744030000d8170303d00403105054064ac000d0764813442c0840c03030042840c2c081c050841c1041c101444002c215030f10342100c00c0030380f02c4c15912190b10005442c003400125 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 606937032 1250 606935782 606935801
    0x40906020408120d0c0903030f031a030106060c02010e042309100218121c0509030a0501110405120a020105070308060d0606080c040f11031f12060b1804150f 69
    0x900450f00e440a036841c049005002401d264001005100c012a108071a00d41c075031f00005000641840d40d2440481c444c0d00000746104803422203c01503201c941c0081e003119003171342c4a580410707003c1c40240155a0862010340a040d0207035001d03c00c5695040c00c0c004032203060001d400058079000003140040e6004c21841046040e41507046540d2140307100070000c10a01221211b10038144003c002035404004150705202100c1d5240070000050003030380c1a038141c2c200145094040c0310b000c61450206000340100e01c00c01010b680d520f0358803802c00d01030014030b500314030070b49102d580054031210042c0d038044222000c068040c5070803441a10703004005007a0b03201d080e1014044a0402c400031408071408900507185100454003040b100140c10039550030380d9000c0300d150400040620020710a280100106c226004041c4104407820b47c0300c01007404180c0f8240c8007600c0e4036a48442108d041e04203c401c0300202c2080800340215481c00340e03100e040205c1c0880c26104202e44810215000c52416000140304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 606938282 1250 606937032 606937049
    0x3340503031b15190501080a0f140c031501140316031b0b07030f020c03070503210408060a09060b0402190c0809060a0201052e0b0f0d060306020a0908030f090409060204 74
    0x3d030034902102d42200d038030391820210052501c000024080390015000d04040c0d80050210240003468030f070b2040c540d62202e08c4c194540164654004140e0301401003920078500d841d00c0003119414020350004003a1820559030003a80301024001341000a454564200c0340e000800103a03103103151054840503c1140e004041001011803d6020950402d02e0741401c0b085690071148401d001c40101039489006100e83c5400d500095854041098a42c28510303885462100061400daa201011480c0200c201e40c1d40240c65528403000c07080065a000d4411400800c171401c0d4104400c008840c800314510700d16802c28801030728507480410210000703403044403c00030000741c0c44200040002c0e01030f010486001c503000d401015501403010350110615059038000714040640e074140040740140341c4c00b41c81341e00c80e00c4505000842c00c05007180070307a04c0a1441880d0140c0c0354490480040c10281c4d1640100c9040d400c1030180c201d0b844c0030f80c0b080d106440c41c02c985c04031f120602030800c0300003842a600f00050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 606939532 1250 606938282 606938323
    0x31c0201090812040203060f1003081608040f030506070f05041701110a030b090a020406050313030219082208060a0b0105130909120906050a08090c03340503031b 71
    0x8819180e07800c3c0c901c079600035801e44111b55640d9040c5982444100c4051b0030b5441e081d54144041020980a00360881045203505803503122501c2e12000d64000c0c1d4840000c00030060028000c205013800001e03000003142c2441d0f4a850510301000d0150b00503409440c030b20104600c9010007080094021629158810000c40e55130040e03000001c0c05006401a801d0203500034002140d002d003640e02c204d4044a0080d9111070451700c03100c56124500c1e8603d10309400b140f10f0b20b9440866400402c07061490f583c8100f00603542d4040d080c4243c040000c64203810b070210300e810740c0c0402851102049407640b202401c030000541000010040c2c43c1e901a00c3e803a01081c0d000034501203170b421000c0d07100104440c080c0e44a203403228a1b1000443c3d08084500480000600030b21034181c0041c003e02801d90000c182c0c005407080d000c500004030b0300d4900c0c0d00703400c001e0382c0c014107441e03444464201c168080b00d60740000d000e941c3c107414407000c06d40e03c0c410000f01010141440150061000d01486160703441d80701104c04c0103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 606940782 1250 606939532 606939547
    0x10308091005070f0209040206120f01030209061c020f0d0803010b1e07120c11040c1716083405070203100203061e061b03030108071202031c02010908 66
    0x12219005094094025055148518007a074042c4041e40c06a40d032050200c82c103c007440d4240403006801a1080760000000d1101c01260304086a0700c5108403407000420f00c0940c503500400c0580d05010741924064600d205000c07a0700b903840320701814866019640b02c00c1c82071140011444406181d840941041e80100000c1104c0304410002d1803c2429201c80369442406850302d03100c14400d03000d0080ca910010750442c8070880c0160105003d241c000e411080c2002080e20125064600c10385110001814104041003101c4440f110180c1100303542090448403104c02c6409070030494003800203c0a00081c0c603100320350035210300e24060000c1032081030340904200d20001518a40000b00100d11a00580160800008162003170f648900c800406440c0d0240c0c2090302ca161018008040d0398016004022000c51940030011940c01040440015566989014000c905180c1e0b140c022001c240d4480c1c409501595001694006048404901d0101c0c0310074102d059006011ba544c2c018000040401e0300b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 606942032 1250 606940782 606940793
    0x171c0210061403060703020c0d0f03091e021504050d140a020a170708010c09090e070510050c0705030102070503030c0a0e031f05070809120702010513090603020a061d040504050c04050103 82
    0x4010405094080301c070307680c4074070030103500707a0140300f20060165010064507034271184500c118140680d000e0500180c010b0a0340c488580c0b4282c2400300c81e682c4030110343c004085040c1081c0c84d100011508580714182800d040028031902c548040191821041411020094405011006103164010000ea55140e07603040080440402480800703084d024400e00000d9258040c0609076900c041c655616802c07034141128107004149190501401d44111070b0081703050348130120300410071146e0b62202c54a9072030046105141440301d400803030217a4018070090340080c400009498200032510110f41c3c407001500c004907690504101055858410030341c4c6007054518062203080c0d9506140b1052020795a500b1302611034410980d600d0300254448000e0350007003000e02c4080c00c0054070500d0110b20300002d134450002c492055800c40c82e1721640d0340d0070800441c43c2010091004102600707142c040e84011200301710314010015002030003113483c2c8000504116052041060750752006100f04080e585a0511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 606943282 1250 606942032 606942059
    0x702062a060a090f0201050a11060906151c0f02060d020301091a0f0312030c1605030c0f0601061d22050621060a0b01090b1b07171c021006 61
    0xc0d03411502503000460301e40c100343d0068101c41d68024800311140d90300c0d54011502a80f1148000e000c009518500310322032102401054003845240b0300820160800108580d0510004c41c8031610888540c1c1c94a103401f81e44220722807601e500051030359083c2245002082d498420705480800b21803000002180c1a80603030300a001720305880308444200035003001400030b04034107840d1456160380300f200710030203d035808030055901010780608a400c1c24009200038030040c1803140700b211240c00100703001c04001020005405545201c00060800c0d5241500c09440c0c3c00e074465205100c0c604004000015441c2e1800c461140308405240c120440c6030f45404400922060721000d1040ca80c00809a1520180c0303403480c0c04600b42c1c0c1c0c0242c91ba9407a8802010002e00242ca840c1d41801240203002880220070800b915461038441940713015410310142d014200b4049401880b075041d28141c489403007403400150b214031900054440b40002da80e66106074a06a55052001c031100c0c100300c404202402440030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 606944532 1250 606943282 606943357
    0x150c0d06050306010e010e160507110616080d0f0c0f0309021f030237030917040f06090803040b0a030b130608010e010e0f0309270109141803030c070206 67
    0x2500303d48070f140c8c2c2c1c1c5100c0804442c002c00014010304c00c80e800b11f21411400c02039200d005011524160041c017107101145180e0100b034440c05004194994a1545802180780c109001882000250b2554001401ca204000711280415a070381d1421021500c8210015070500440400d030718200e83d4460000300a5031003000b08002c0c03d0341025511003d90703c2448804ca1040300405003840d40300c5202c0080b4010100c034603040e1100074100408210220170003000700b0107041b0500a0f040094103102c00030301390210952084060f50710401040003e80700c44c01c150740e80c0000360b24000c41c2c440c0041e0002050300309c1e00220f100700300e441c0500021715500158804003290710214002d0010003119408280c884503071580420312508104040200340c900b941e02a61401010f0f001c3e140c16040c074003c89484400240c01400b825079640e0765401e40300040c00515a848a036440c903844c02c501c860704006849003c0600248140c1101103130500031551401f00b510100c0680c044104101c080c00007416521190364217 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 606945782 1250 606944532 606944549
    0x2040e090c090130080406050909010e0402010203031605221404090f06110403150903140c2e140402042a0e0402070506070e01020609150c0d06050306010e01 69
    0x1d00762185400d003601d01c1030482c0c00c5500422010711401c2c04402c0305101039080380e501c61026040840016000c04081d1002d000350b079564584030401502402514034041c0c200e03803044000c807000c100050ba800002c0780e80c403440920380d8224000c1804403d460300d00983e484d00c01800c114615107a0f0080e0401350440031210480d500041905070801440101c1307148000140c01c520a814080010031a0383c3c00060002114000e07551030b00e540c0c1d449082d450f028944105608584900e010340a06501100454074002e109001078070f4442c0c4604404d50704e00062203040340c0c20511583c0300d00015003242082c01501c4440200348001d6515500002c2202d0080b54102d20130761400e501c0040d2480c0c0b542c5090381c6051701070180350704415098010356210f203209240c00e6005808000e20b9000030014407905008154544905400c2d40a031400a4242072000702455081d07800007000290018131300345020341000032802d00d070f540d44070305c02490b90151440341c10030b513018410b440000510410f4408a0b038100ca2002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 606947032 1250 606945782 606945793
    0x50a0b160e0102100207110904201e190f080703230312060a180504110105160201030504140106080d080108010b1f110d0e0306060405360102040e09 65
    0x28019151150381d4006240180e200200d0300311107100c59401400024043c1c02e40081e00300504c80051000702c03003144c00321101c2040000f00c600203110b19001c0441c80200301c80d080611100031504100817003449040714072880141d0400c2d155144030900003000351400038800c1c48200e8842480076510240341c80308880c04403841031101030400284090301c0c141400000510310f8096610034003010228090f25241e4040e030385840000e14903401514543c12038110340300100303940c41d00b824000a503100c5075010a05001040203038007840c2c4a620001c5104507030909000503a03444070305001a0600d400062449958a0b1041c003042020b00060b02c24060442a502c001e02d503038031468814242d919900007e41c00c8500c20245080c0c503004c02e032201444030640d281081106008900d82864511144a2100030400c00e03280d0a0f01418240000c644c030000c1541c0c2842241441c084415080c1c0c1040e05000e410740213600200b0220961501078101031644400964445d6140d4010380c105410940c3c002d419840b50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 606948282 1250 606947032 606947071
    0x190e073b0402210114190b04171516080718051e0d11030d05040b0712021f0c03230c0906190207050901080a030e011d0402040e0a05060607050715050403050a0b 70
    0x5200c5020951f4088864681450724103900d110f840e401c1040e01e00101c0c02101c04200c540f80600003450f214031014011500d86007100e000151840c0d1020301034008210310381840d4242016445803040407154296066031a411441042d00c912001403181d240e07021107014402d000f4005504e02d2000c100000b101500c2d00c1104101c01642d280c8207a1050000500303080c400d0300c011600c0c074142c107100041c00c0e00507610665020003111589860005401922a40c1e0346010907480e5407603c80d00700066604410200501b2444545141c0c00d00020502c140c8142d0008521210761911002c5d142c0d990b6040700d0400704058511006074070b4486500a90f4040c101d04070000510f2040005c044880b40c0d0582ca520101001c001c1c01100c040391b4044042c8200005000982000d4466200620081c00168221903141c14050060b00c195076002d08001d110f10b005208a00100c0c002054440485101854158120141c02c4040c1c48034010740e4405413640c052003001100b80445696034038407a12542410a001128 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 606949532 1250 606948282 606948319
    0x2a0301022a030301140d020111030307120605030a0519060207020904050f060a0b06030708060a0803070c05090a06050a0b16020907050a030b060a0e190e073b0402210114 74
    0x10034407400301800b44100c0303e900141000c4403810a0706c0d0061514214156500c2c0051740b40d50302c02d030b03010300000b020100f500301d00c0001407046601803c0b00b18003070490170b03950b0380368241e41d40e07130041d95a00d0072480c01d1858002c02042e0f0341100c034101e601408010309450030341081e0b500d40c407c1c481950040d00800c0002070040c80180b087d004103da008001904544900c43e0486103808010421900a0504440441c145004101612006125596158940c0d0624050050f0b1b10006048601b42c00d003050001d0043d903a84411490540380340f0041c80d0f446100c000260011740c0700340d1304081d420600f12000e1065135a8002c0042c40c8a4203252014020420800140212445000c18200019401d07614920107803402040752021500d541c0d503864562911420304800017074041d602c0001103692001c030041440030003c640d00074000030111984081d40c0031000b1200c00242080f1461190341d0000d4081c0c0c1d4554560503640c080500054440025a120380f2003c002d00c40d207175151441610300da55914030143d07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 606950782 1250 606949532 606949537
    0x80108030319021318061a09032e020a0c0320120a030f06061806140409180c1e0b18010e030a0b0c1e0307022a0301022a03 54
    0x15841148040b008944001450081d00000e10180c4013032800f9400003483c0c1800d1020202d89400c8034000a00c55245c140800c03640e5000b01c0c20058002e909004804a5603801310710f00f0005c2c601c5000640941d0940300410365000030740211041000c1c400704402d0305050744140c1c0c0480041c426100c0f080c881c0c070240c0030004e2151b02d91811080950055174200100050740003e40f400c5480b500b408038124611310200010303124260029800541541e8411480007040e5440300010b240a062450710040b00030240100d51044d402034014403a00d03550404042240c00380c00c40d841d21b8104c0d01400009440307251848071080e10001d040c0c0300401070390001c00d01da83c10500315010b201908092810f0400c00f00015036000010807149039041c042c01402c4c1d408600c0140c43e061152048000c003540d1500b1070940a00440030701003000d0f5001505108015903180c00144c10850748210051102c01c288244400f101c0a82c44024981d4044d4008601031102c4144038201d51403111640c0c0d104800c011f400b002d180e9890 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 606952032 1250 606950782 606950791
    0xf03120b1f05130803070204060b0310030f0f200102060a0b0102100b0105190c061415150409020414040b0907020a0b150a0305060604050f010f231507030801080303 72
    0x201400744544512001e11003407000c620b0502c0e90500070748041c500d03075040c1030354001c240c0b84d0800503040c0c01f1071925128000181613450f03a81c60460030190004e500c2c2d41002d010040114402030150821b000c01c100701c9d03116103680281d0001c14070b18000014440600110201400b500c261800305001240900401480020603801002050509011000a402603400c45418000104092000b05402e0030b40d00422408644035808210110701d001011100c6200741841403488110601103120002510600d10441c1201c40c0720441d20034015113400391185610079200c543c0f0009000600910740880d250400c1012038040241c030340c01400340b03c1d440e130b000c03502000181c00c01d103455000900e41c140c226030001d05040633034a00a440034003052401690f43c1041c0c50940c1b002041104074945800340680c03044504500c03240b207514064181c281031066000c0c0d040b41d00d14001903803030f41d2101d10542c0748100c1001040c04e420510350b9103100305142e1028109500258801c2c002060501c0000f04a0b03015 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 606953282 1250 606952032 606952039
    0x40c08150f0904030e0103381f2606060708091206101403161203030f11030a0e010603020f0111010207050703080910140a050c010b040609020c0106050f102003070f03120b 75
    0x15440308c0751a150401072654020b50300804444a8800c0f04010040c0042d80302401d80341d282d080c0c0f60040880d0f06181c400012094403140002c2002003940715034086d1380c451a0b10022540d00c491050f400201ca00c040186411041c1c0b0812080000d501d00b41480312088540d40c90755002a803285909047e100c442c0c1009a08408900c60820440c000b69182501c2c0c4640c000d1400041d42030780b03903007210280ca0b0780408403007000c0e9003c0180b200100030b0348609880310104500070840e4900e50f80c0842cdd5112851003203181071100c4006907201524081d0110784140e94400c0c20360b0240c50f12450000d2881d000610454061107041540c40d41c3c041c0510200085801c410346520708007002004101d40a40c810007a1910307654a0303903100403036515140290000360540c1400581c0b2185000402802c44071140d00907442035a00b882c07006400d03140c0680b0720401000a15080d0161404403c440755801b00e00c01c01808075120009146c0140038009410081440c400c0e51489245801c8601403002c1d98011004c2e03550 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 606954532 1250 606953282 606953351
    0x4111b0c0a03120c0f0b06090105010c030c11240d0b0102060915040602221404021608090301140c0703020705040c020d08040c09020a090302030705040c08150f0904030e0103 76
    0x705141525a51491903186003403d15168130342c2da85544400340100444111001006022862403c0c02140c0c0c090b100070300c0c0000c0e032101c19480041a0590102001d0040c0d0000304c0d182c40180c9944218036401066012100e1550301040c1009503036074460f00d00d1b82c000c01e00d4074038085100c0d8804287e56016801b050003c002c46028160000310b070300405041240d1181c0d007041072060b002d0b0a0100002400400c3c440030441614104084001611494041d4407803441080803124440c2110000c042241d000034040f6229600c980210780141840d1455492042044041003241001003004000c458480e50030348a0303895494050000b501c042701048405604011542c81d0018841c441140c0e21900440030141d83c5030307603140b80c0022640442c0500000541c458030500940c14104041740080600383d0342009502d0705c01c203000741401c1000d01807003245035a08011818541d580384665214420003050102ca9040620f0043c02c8601c1c540c0049010038281040d610b6248002c0c4111032012850850441 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 606955782 1250 606954532 606954539
    0x60503040b0a0e100f0b310e15040c06030f060b0313020d0b190e0c0d02060d0f050a0603110a060f200604050d021605010e010c060b04111b0c0a 63
    0x14054224400b281e9594071649112007501c8025020741c085945804000240080c207100521844010701310070a003060f00b00e40c020b074100c100c4940c01500381694601000035582041c240660510202c4200c40c006501030700c9c02d100c140b0040e0403020044400700e4404100b41e00f1a0745500d403e85020344110034140c44c0500020b420900380d01c01a2840910080c0700b0044810141c2d01c00010fa80103a501e414200e402c40314103a1940c40718800c0118800d4130400810b50586c03020005001c00d000d085000b405041d022582503c0401d03181c11041e210010500248054030300350308060007c00b00e034401929030800c1c801c0b142c1d516003420303920001a500d00d540e9030030300041407000c146d4180c0300303815400810700303501c4d20200c403004014825103008500c12006030140e2403144000a14002c06c007905001c520300c0300300080002c0d0380c01215845100740207003420b102050980c104040100514680f1035089030800a04c0c040c12200103004201c03030f4103114120f20003501060503203507481181d003c0443c1c00084050092 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 606957032 1250 606955782 606955801
    0x60a0b12030a090f150c02040f090b01090501060f0309020901060f091a19030212151917070e0c030f04060e190308100b030411030a14010203040210051216030e0f0303010807060503040b 81
    0x30920270601c03900c0441d00f19130f03690703a805120000740e215a8409550390010302010764480440c9028071161301d0184120f40494000454408061091340c0030301551142e88107005025441503401084140f42c8041c0e480c0060a0300c800d030390700034501c5084c08a410140c5102182c001d100381c0b002002c0d1807542170201d039110a120a00d408a0300c0095500418041c075030319003401c03113030600405050583c4682a00c0100740740900e00d04031994100304850000d450800a002024200303403644080714440c1501d0300e44680c10035a000309414800e94819000349006852464410b126a420161080d520070200395909440c9a071441503e00642e045c4000400100c1c1c0424400076581c00903000090a8850031842070303468201041c400b81c004031103030350040208019454000f122000000307240c10b26618200d00c5401d03500390444014102d0400861022414840fa80b19074003000d1102d003074008588400b0030f0b8407145690707a0000d01c40c2103110b110f0140f011641505c00c0e415030f03025a502030000c60300e60700c2d2a01354 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 606958282 1250 606957032 606957041
    0x6090403140403050705041a2409040c21060f0317090306040308011e05010c030521270c01020d051e13170f060a0b12030a090f150c0204 60
    0x90302081003040381900416010760003007004500c203c00800d0041c0ca07100034031041e00c504c005010502aa440c1e4503400741d07180d0629101001540b1a00d000c0c09400b600d182000c50300680703030b0071781d007191400c85280e5050343c11403035400c501c04c000085902a942100480b105403203040c09035019003030f00e07004104002400050301042e4044070380b9882d0305111203800801e00c5d15100300c03030640014031640010030102c11030311424600c800d20040380c25102d50410001908801030003400404000d030001d0829070100c503002d030b0700000d0b604c0300141c2c00071030a111020b4600602808552201248607110382c04081c200041c400c590441c041c3c015140f0340241c00d2007607400703420017003916008407005030402d694504079400424080c2c8245150f102c4c4c01d401c1141d000710501c9581c1000310240e0008084441d45000042c02039072203001e2540102d881d02000c800711308800c03a400c589407024800420380c4e92107150441c00034810388070105032103001d499681c11000e41d079a140c2c00410021a0f1207200c00005401c2ca81c11 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 606959532 1250 606958282 606958291
    0xb031b060d0f020319020a2120090f0f0a030b1806010603091103010b0d0602030c090913111f1202040302060a08070909020f0409090512030a1b08010e0609 68
    0x6990912000109400684891542010202e0350020130401a2500302503040c2c62800d40540460803c110300c00060481d40610001c0c19072865605004c00020400d6003003542c0807030054500c10310841c0c04500e00c444c0d0350803000502d40704144102840304603060180106e003202ca0010b0803259080e00c0c58a41240034280030b04084012804c4640d0350300c01c000100000c078024074455800256a00340d0b41040140d50100c081c10a00c281d0404030400c445555944030610300c2074005000699a40701d211140b00240b01d0640803d802c1007540c010881c2c410425250b00000c14010100300e8929141031040080c282c000b400c1c0c41080e03000d00c000700c607040d41c810403990401140001d001454907450343c0008640c1c3d000014410000f82c100400c22080903440341d102030082624150540c101041c40d8900204c0380500e0003521150f503600d08012007400410440d80c66840740400030313940d0781d09080c4400e2001d4070303001101c01c201582041030036002c14803404a4a04841014900301c0160f10b501c1c3c00c01050500140 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 606960782 1250 606959532 606959539
    0x3090409020402120c090a0b030601050702120106150314090601030b1f17031c0b0d1502090405040c0911090907180302120f37080705032b0b031b 64
    0x10081c1301c1e4003c010045030044098840180d200c446a031700700143c0108503080400000e4051044c803d103a604031382a02c1c1201d5048514011500d90f41c403885004001c10b03480319032045055582041c009816501002000500ea1607102c60342da103040445031780b40020f1100a01900303109000542003080343e4201840640d6013008021030981d650041c105c0e5400900c03d42d052504001504c4448005841d0a090a4492110306001c0250440000344400d01020300c06480c103920030f040ca920380c540645c1210b108942c014070412581c113103820b1021034540c0034014016454038103010b0110b0f0302800000c0d0761007040010940d0046558040003111a065090703441d200c0c02450305004030040c0d0b40d0002c1150361640260040110420703080400d854008080e01112090a0801e01e0558014402403619a075a5400e02d070a2101d103410301c2d00102500c03410354090854000485e03080c10381c540d611300c1801912992041848001c81c3d90343d00d001160b04030101983c1c15449070754800c82040600089800084008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 606962032 1250 606960782 606960787
    0xb04060c17041203110c01080412030908220812030c190e0d06020a170c030721090309052128020a120209090f06010e0a0f021215030a030203090409020402 68
    0x5007140f80c80d01c450320038101c0119000d600748809580007005841028a000d01c0c1502c141d06040c1c541451003c034000c1301104064507600320741e00380410305c0f08031481e08000800040e9141000c02e0904213010b028001d40c421409075000b50b034445804941564010146090254685201c04802c066449154502c2c072090004a007940780c1aa5243c00c3d07140751043c021400540c1e96560410011301c00c0001405040b48405200103001b2008461000c2c2d90744410a0b040484044d07c1c40f8150a240b007074400440380100d4280341c542810540c0c400003010441c2c0d400c0da0304100d52600b0540704110f4940e40c00c40c4010395400551500c01f4076103596000c0001e0900b08411032041080d503004980c001c0150307003040c4241d200c508821000c504190350307a1741c2e001c107812000d0305074100582c001e9901d501042c4909281941d1820215000340d01039404a060440180350443d0b80d41d0b1140811040d04600b29001d80b00c0c10344000014185007004035020310120780c141d01a40c900340801c800c000050841c0b02c01aa00607600f07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 606963282 1250 606962032 606962039
    0x80c0f0a0b2106030307082d0d09050c06030105060a030f020d090f050f120d05091f0e07060311121305161503090308010b0703020f061f0b04060c1704 66
    0x10000702100c00042c012680d07015100c1c00040940200948058080e41c8104000ea0201d0400c40a440c01c1c0a5a240f0741031054144401c03103442c0c1c001e054044100389000007801426a03c0e01e80c089040709105400ba5800c5524500400a45000034414a9001b810800c80d02030503c1c401d5101e0303411151480001070900b00101070308012690308410803100602c80c0c5240d00e06110042089104000c208001800d6041c0340100240d0a400743c41c004288140c0c4880205001400c24007801e00901c901d000d504ae6058420304e1090041c1048450522060003412800300700d5034403d00a01d40d201a028492502d4860321000440000e1130007089850240100c081840010f2401d00c0704400002d4144070345008142072062140c241100380b0300c0c3e4403e1520b084100701c0040e070069480360455540003102070301c44d0410b0805904205601d242a0440d0180d0030400901c1040c1c115003ca4003008240c410400d15103c0d2181d03590b9108600440c80440c9050b80d200d400074409001c5d6a40420510300d015050558 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 606964532 1250 606963282 606963299
    0x103021b03040909050c0312040506030405030c03210f060105030118021e0301061b0209040b0405010e060106020616180b0307090905010e07120c080c131e031704080c0f0a 75
    0x3d8205040d50340d04c941e4042c0074464200b24101c06581c3c11030151444101009490019105601c038490103860302100013414000140251003e03a20500152503440052940d0243c2040000140d0040d421411000c60301088d80c001100d441503006850b1685036900b0220b070a41b010070645c20300c010343ea4003008a003043c400510004950700001248560716035061001c06000e0001d05040d001020b00b40700148400f5076600340540744c00a030490703040d059913111810b1080c0540f80c00058034015205800c000035078541d0001d0398602c901c000c1a1809100d41d01c81e00111003442c1103014001429001c002c0510001420b240156001195070a005070815958826002914400d900500700b03021464100441141c22451501c503d482c403040800800d40f850744007604400b070182c460700081602040728400c000040f900180902102c4020680ca0000702c000342d0f03c002001e001c2113a6629107648000e840811540c203603026600681d0150450035440c00a00480311944ac0003143c1c00010020002860308 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 606965782 1250 606964532 606964537
    0x40b0d020a180c050703090603050402060d18050f0c0f040b180c1305060a120507050c010f06030228142407030e100203090415050a060c1209030c050103021b03 70
    0x107001802c030099400d0108440101c0da82c0211072400d04c1002c0003004002540075031408181e90003428009080d8440780040390780e40c05000c0f5071401140c5404020b4402d51161a01005124812030884800c5800072800781d0f00d8420310500260080c1011600383c000740344ca508400d240140c0035000c030b40c003207050340180c400802083e41c840e800a00700140c0070141219035a1104050030043d42d4041c0b510800c40d60052491105403c030000140e642c40103e1019446241110f1810f2540002440107603644000040206201e1100f01e2091400a20318203038019108006201c58503141c042d803001d14900750118640780f4020a00175070045c040c2c00c00c0b00c0e50300c0781219443d00070705485107040e498041c10310303000c0d050700040107480d889040c007010080328443e400000c55848050503200488c03802c58010f41c0302c00102160700050343c041213030380c0c0110302203920100141c0c80c1c601a0488806014500d081031791025803a00000d02a494403050901581d4082c2d002440203410001e00400c1031000c0c000842c2c10f58 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 606967032 1250 606965782 606965789
    0x20a0b040f0b0d111215060423040e01110d0b150901111018031710060c0c0902030702030a120e0a0605040312060807090e0c0a090c110d230711040b0d020a 68
    0x917801003440650020840101c00d00c00041e10381c20320b00380c2805080030200c40c0943c490400c00303155050039412510703141c01103514081004c000380f00b03035071002502c400305400040d901d809140c505007280d035180c035000410405900031600440d20303080c4040c0044500807072811821480c2c0c0f281900710240c144980c0708450010099003140da0b030404061400074082c650a00701d28012400a005001c5100b800c24000700403541d0609201548040c0381c600407a03150182e521842140d8800702c10004129000700003480b0f85001565140c41002d109003040d41110030178110500550301003010310740064505d034041600b00b4041c4c1080340840b003900c032502d82034a04942045013a900a59030030007806401e801103910181200019040900d81c807004103c80c00038034815400f61640301e203800d0781d0700340c060500002d502c00082e040c0e456141500101a218400744420090f401d003d140c4e1203414804410280e58a0a50080003c0e0a1110850401001d400514201a446965090354400684c2d403a551607008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 606968282 1250 606967032 606967057
    0x6150403060b0114070b0a0c02100609060e090d021f0e10060504051302030c151e1c05010302090f06191205060906010b07080a140304050109020a0b040f0b0d11 70
    0x3030080110004000c02c84c0c03a05070700c010000038415600054081c0c02c000d648103102c0c400c0081c2c080e40402e1304901e408400502e0204942c079140e00820441d8540d041078058804540c0d40e0402c580b0f0780b07019107540b5440c2a5031036005800207214240c03004111070201c0426040c884010840c1e0783c001d04842e00740412001440469aa103000411042c209401190751141c145074804503d4a01500420f4660104110003403088031614141e00307054588a06440c40000400347c0c03540b00c0c5414050460203513003c07100c11703407035011013841030428961580a5281669405094240251110481544010310140450340d00c415401c003800c2e0b808d81c1c05145c5070000c00108005414541c602e0034640c1c20f1490241c04101c460300007800500190320320070100c410459000740303020340d181136203d41202d210318902c520120000e030000900c8148441500040209030007204c0214080303030783e007500d180c070b5201e18450f00343ea00d03900d044c040180c4a580d0005d00b400484211022400608603280c5004542c400e8115026 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 606969532 1250 606968282 606968291
    0x6150703031104051314010b03060f131401030f1a07050a0309060b060307020c1203160b040302031e0301030303051e01121b03080316030c0c0206030402010c050a0b1602010501030206040e0615040306 87
    0x14034206c003446004280791205036140d820540c02246043c14201041809040041010407400920754020104215900782c40d0066503182d1801c10000400080e080e02c1089a0324210900620b007012114000d4035a51141840d15400140a402921002078141c503025a90b1580705003031f8407514000e40c40f0f100d403035014010050841003002081c2640d1583c01502da0b0091149a8802e514840c00481c01d03508444403ca503903445103022485c52003603d0130740c0040b508001140410102c04e1025506030381c030a4605120a0b0382d1580c0740310303419010054407201c0c2032500004101400090424200040c0260044140250601d4103403510b14140e034030843d6200400401c101c03080d504c48010810058642c41c0610412007a8140241864903161010344a101d000003c00d007168020024004000c5c0c1c000c003550030014282c100010b0703000007125032040601e4941540b01d281d41c8107200c4c840c162031780180021b0506041418010410a00800745034000d20703100c0d04001c049800101801c02540302c0c48011a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 606970782 1250 606969532 606969551
    0x50c1b01150b09030d21020f04060f03020a020616170906040c0501180302010e0d0b0906070e0d051e0f030f1c05010e06040b0a051306030b061507030311040513 70
    0xa200c124290b0080000b040188541c2c512580c002c9a28000120503282400802e440812521081114030310011201ca1001600c1017825585001400c04c480058403004103030a482d104c02d409034401c00500f2801600175800140c0e00e03260202d6140d030311101c0d500d010b21881e846da002400d1500d0b01960f003007515510100030001041621080312014140a1a20000c01e800c40c440a00f00320680c0e000c002e040c004102090390f01500d47c200b03003280c05074114412050a042203a501038494109854801c000b4150498406c2d4034104a46081003482d4080014103680c00a1103801da0b420920010b0b248141c00fa400c10008055010006081040c08015409a8406026955007400a083c070080d190704c13810100104821075202c80c040e50b010340140c6002c02c0a48001c00014040b03101c58111582c050b000398880c0403042e00503407051007640c1c4034044140c0191122820000c81c1300c0c502140c105064410842840040d1090700003002039a4901c4503a0305058a400006030303104c4011130781c0b6004665410040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 606972032 1250 606970782 606970811
    0x30a210e010b0906010c03020706050f070f0317090111071106040906060807080702070b18192d0e06280303110d030b03031b0a0c031211061504050c1b01 67
    0x19030000e4007400c016603241b515543c06034840100d807242c0c1d000d100c40441c15030341c10300c50101120502544104444668207641c0360240809a02a080861420200c400185901070500c140314a00030101883c50400c1c1b80d6a4030300c50350031030070207945400950512002505240034001e41001d01001c0d00e4071140c82c904003000030b00c800030017400f0204651040030300304030048040c41150340744818901c034070f00003c1494001c14070300741d44600b04074030300c2c001082c001a0100683d02c05001070140d0186501000300e4800000c540610329008010202c400c9901149203803404009a40c5501c2102031900c494050440f8a441414041e60041c2c02041141591509400d400e02c80101d01ea03110303003000c1012026a0022036a01d020304603919080c040e500c4a04034044108101c40f003007143d4030070300d40e0144548034900841c0040c0380c944500c0c0031072003180e01c000b1b20701d2001c241c1520a500d0200d9909004801c24200409400c0280ca1302c100c0d1101009400101c0ca40b418200c0d04900c019800440c80c090041c409 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 606973282 1250 606972032 606972049
    0xa170f1203130f08070b07090501020d05130501030510031e020a0603150605030a1e090516030b1b1b0105010e0108030403020a0e0a150f0801060b040305030a210e010b 73
    0x654030841001044400c0c0ba00040b01000550400d030080b441c1001807400b9401c501c02c809000d0604840042082007582e0700c030242e01d00780d50b42a404e580120400120940d0f00340181d4180444d105903004051001c0c0d4444d0703102c0ca51001c8184210404180e583d1143c411400b6080352100d5040305104001c1d05501340055910000e285034903040110401052074034905400c0d0340142d000300000040420024603203500f000b80510302c0030a44811030758884034860b00a100f030440444260081942180c041c80b0b0003011403007129048035030095a5074885030980c242d40701006100071020381c140240307244440c54201030980a5850000000d595040800c042c82c0744605904c13007a9243d204000520050315004040d004a4200e03420f0040e05032103081500340035205044a00710f0080b4a1000080c0100e0034030503110441e980d0300001c020140d00ca84040200744120700010380070380d00400c14500e641d84140d5044500c0954001100d0b5031403011094041a92000229240180c0d102c3d041c1101c240b0f000c048 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 606974532 1250 606973282 606973303
    0x40b16060b0a08060601031d19060605030f0604052509020a0c060923030c030f0702030703080f0409050109020322061119020c030307230c100f0e04110f090a170f 71
    0x1032034103580c040e05d003a16035070070302c0042c40005400b09d0440c25080003103030340140014240003800d60b00c0d4040d45c0c2c01102e07078071901110140e4561080c2e490386c00a00050046000985103001c40c0d5410050a1410780c0000e54003500c44981000407102292021401e544160740000d44038101e81214010403404055810008040c5514503800804c100c801c11900042111001c00f5a0301606271180c0310360002a081950b2540080c01c80b00c030004410010b00300000c02401641c04580c401c1001d0b0341c842907080124041205c0d17a0700f03080c40303103a000074220180380401d00c0001c0c400c400c0403c04045115803000282c00500c0403600c004510f003844041c494043c0202c0d0605001600114206110303600d541d542581510300705805a504418040c80700c9105114206482101410080e80c0701d81900c0010502a003614000e000526210ba41001a161900403440e9070322503401c0403401c0c9501009000402e0b40724078612540420060b1000401118110f038080104410001401c81d0b8454080741c2820022600c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 606975782 1250 606974532 606974561
    0xf191e0612060f1a091008070210060311092a0913110711060c010903081005010f09060f09180b040c11060c0f220f0803040b16060b0a0806060103 64
    0x104103000c50010340071002c080ba1644407410001500140071001d00d4070500141e6504400700380c0e071180700f00c7c0e0010a001e004140a03400ca502031600b0500907011104103020040403c0401e4002ca8103500c1c103401c65a030020340c160091070b901c1100002043d58030f807905905240322600400c814001d0325003020398944800e075100c400c0c05951855811142c241c031a02c0e00041101040100c5105e0310f0720703281d09641c1b00d00c1d400300c0200001c032818103002d040c1d81004c8802c0c110810500c100800c055115044500c0c401d001d50f1200e0f80c0c0301d418240d090722107840d0000417408015080000182c560b0700244000701c1508035040000b165030351001440240d80303950300b03150148404003e00480e803883c0058440d0340081c02102c0151607a000c1d4500f442c0502c1003104200920a50340740c240401320002d4800b038111880c985010484e6650344142c10344078003a40c03203101c00f200c1c424041d00000030001d0030310000103407058000180d20141540041c0500500b0f400c8820030b41d10910400245503018800c100303003880f221 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 606977032 1250 606975782 606975791
    0x90a060e0103060c020a020303031521060a09110d350a050702011701091e0b061602030709020406050c010608030414040903030906110a031401050f191e0612 69
    0x64204200e280c18400100036980da0112560300b40d100b844140e07845a80102030703d035681043c119601d601c10040781e007148951440d0302150f2013000741c1d10204806400380c102034110742e69030380c100798000d110b62113007603501c003d554a101000d03035111701084900700d02c51884488500354103607035464804075100813080c3e5551841d00100284501c0020388507801c2403480c156a9885103403004032004841e542e52180300d01031100c00801e05001c20f4001d078241d4030200c0100b0007203034414501581652000160030360400d5082081100c10703a00000003080c00c60026044407442907548010380c1c2203a10561041000610201d00c5c094460000c2c040d07036009210100c002c50915007441e682041660544c01c0c45c9108a40d0390382c2003020507000b6009000425080f1004020080c80320316a050741e50320012411001a207424042d09010041c2100c11b8180c84000d8105160708203c0e03014000c4441c3d0b00b042038031101d0042c10300020b044007002190f89034800110f000a00c0345143c0140a00981ca107001e0804005041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 606978282 1250 606977032 606977039
    0x121c0f050709030b090f01050c0c0d2102090d1709010908030c0d0819060f080c04060e0a051f090614060a020d0f0306090204151e120903050903160302090a06 69
    0x19003907090f01e821400b03c6010380c851030021441e0401901d40345c2c485500b0038080004801649000e041c607040e4400c10340750039582d4030504940e1491440e44803a5580956060110710021590203412501c101601c1d140b41d00120f51201c0c980100c0311600d00c41c5040c0001088520755034010398020040403000011424220b141c1c03c00c0b0703101d4814032200c4042004140004120103049400c1d1069014403030410090719884051007188000c0c140107000e014420110303680c6035410144100d0040351408150a85282c481c50001005440003520401d000700c0000c00d4244041c4400c810700c00103191010001540519010403242a04e007140304081c8203210510600302600d40100b00d405c12a400351604892403023401c242034000344084d40001600900c00308010518028804c00441d0340b90803a21200c448001c89102c41d880000c0b00350851001841c02110781c1840d0132250408030300719200e4100241800c2180c0c000ca40341000e841c0c002d10600d800d1507410015402c00c0c4c00003035000760700d0500c04d04c40d5030b0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 606979532 1250 606978282 606978287
    0x3080406090204062d1a041205160b0d050a090323040b0c01050a1802060406030b010306030f0f2a05130f05191401150c05121c0f0507 59
    0x400800141090752540d454004541c0c4a500c580c01400a510780b015181403544a40e800100f1030701311a070002041407101081401c0c413030303024a050b01c260b540c10524003800c3c28025aa100c1d41000c080307c2d107209a11049003002032951848001c1c0c141e0000080e01c0da100540560b06550000c1c2852000038600b1000d500400d50148141d409c5920041c010382d809440041d20002a214950005641c84808206200811010340005014103c1c40e01c080c002020020307042888400751640087d841202004108041c0e4041c0e00040e4060505050000b1403559030780360110401003410302190008c070301540b43c008000104000c1013018402c0404a000080c443c030011111038890b0080a100710140c04040d12541d405806c10103050920f21350a00590400c20580d00001610551084020707007003640c00047c80010036503140c100e881100010b88040050041984c0c5201e03441070039030719400b40094030413070f007440800101800d058090410500c2c182102c2044112651007085030142c508007014000301a0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 606980782 1250 606979532 606979547
    0x501110a08010e060d20030c06090904150e0102040f031208090d030209040e0f010b030f0a050c0d060f060f0611010e0307032703030c0614060a0b1b160807050a0303 72
    0xa4020081640f42d13290180001d420341c51220707000701444404e96912004100c000401c41d061001502152a02c5043c0d8040004900a6a48154000e81c0000000e00410f1011a0a5402801c51200001c1c1c40000203021800d9038040d8000c1c9400407101c1c0010410001e03520341c072403020241071402d4015801c10640c5503860703050800c0041d04158012a2010a13540d13681d1110000d90380040490310948071503072840d806801590000d511900416003280045207012844900f4030b0340c088043c202488030750040028007003541d1015500c0c141e031110051000c048a1142e08040c0540700c85103020149442001410f0b8040c00611a4441e41012869803403040008155103d842d0b05042210030034800ca0702c031075228041c50301c0d04044030100303000000174550088622800030b80150000e21001d83c10f20388042c100c80e42aa5419002001d00404100c00b00d29040a4406281c0318101d600750140512955460100c444454500e0f40c4c0852004200e002820801440209400c0e250001894a5900c002e01000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 606982032 1250 606980782 606980789
    0x51b0c1c0e130510050a0801050919050604032334020d060c0c0c06030f2913021b0601051309030f0c1a04060504060507020619020d0b0411070501110a0801 68
    0xa83c480300450700c3c08221450741400750402500000810340d031401c035180608400e5130141c050340201041d55140c0c81c1d00c0e07006000030f15042002400c583d00c07290780c221243d0021104080c1b016141840100880020f0360041c00310001d043e8290000201c1540542c103200703a0b00410480800c0d002510000585810b5190a40355801131400101c00c01d100380241c4034a001041e005180040048001ca00d4641680c80f0b4110303a10044010003583d04c1c59040c2c07041202104e800c4890304e204800e4251184d03e001040c0d000180c081c0c40c0b01604005481c2d40340c0501d05083c2c140d9800326004000180200d0400000da03070001031034600c040c00781c2e5800781c50150009125400a5040107043c2a2045c01e104410020b1114448030352103410380b51402e41418802000300b82e4044401a00b450081040341d4400102da60094014854200c800c00d080383e0740358003d501c40401c80030407544506100016076100d204003c0d03010181e81e511a07441e0280e14181d42100d0300b5074042d1a03440401e0015190b51588428000e040d0f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 606983282 1250 606982032 606982069
    0xd11041104230619020307050105011406040b0307021c0f080901060303090e090f060403120b12030a0c0203100603030806031e1b03011e0605030c010903050c04051b0c1c0e 75
    0x180210204805108882c04c0441c486184141c4229480c0c0c0000205100c1c0e000d400204901d989481602106602c040c000c5603002009010900c5004903030401103810400f40c0c011200c002c58003400a0458030b007585200000f080c040e50809040c3e07900505866480504030780200306003811503038090407207541401440784c40c081e290006007501c503081200d1104a40c08800703c80e030301e00e818034009110680c030fa040a0811410040b0200840c03c0400716032031301d40b5102029604141c01d82c04221011190b42d08180c2c3d243c41180460900e01d4039520410002e14001d41d00d00c00c4a03e8404280351501c6101c0c4100c0590307030030180700c1d131540c0721000c91001c090b001c581c40c1035440e140315400007034050321854903100310030520f501c00400b10442940c0072000b150340940541c4d0150364068015070315004a48406445904441440790007450107501080c2d000c4c0102100c071841441c030b00007440103a04050260b40495000300000d8110141c00105e152588107589007014a44214002180c034040350307607107174161 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 606984532 1250 606983282 606983339
    0xc03060801050c041205070b030907060f020f0a020405100306181205120609040204090503161b0501020307060e1c171b120405120d0902040c03060605071704050d11041104 75
    0x4102c800e001c404003c108c280b503002d03160306095002a888440f10301c10b0501003008100c0d801201400461521002c0031041c0203012a008079800b404041c0c0002010400540515400070002035081d1291440c401c4143c070213030194450f1894100317036541015490070f00380007090000003c1294600d2205602030402d40305415542c0b80c9102080141000080040281c000441e07a60b0f000403180d03041180345401504c10424004040746600a251002e0040310700580040281c035001c50900d42104c010401c1807000c0300c007441c080e0f11403140d0103c0c680c00e072480007401001c05503841c2101d41c3c0065420200d401d440f4440b81a0124007219140300d510700c010070801d42c00c030004003404018409164981144413220b90340e0101c1c000400020704080c4012072141e49003825840f0418400d03c504001d490b45900d41e80c0c50000503484403443e0510a40d02d42c24405801c2101007026250030700d904c816940304d64198840c1c0040c02c020001074548811815142031700070300041014101109001c2034948800c1103e40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 606985782 1250 606984532 606984569
    0x30c02010b040c080f07090602210d02030702160f0f031b35030901050301051c05030d0209130509030d020d1401120b07090302031b1c060c03060801050c04 68
    0x34050007850800c81d502c140b0307181010094a4100280701d11418822005400a0707880b0203090f206002503005940060340002104107080654041c00f05c9c04c1e411b80c1e8086424800c4088400d0160b81c4102c3e100b00041e040b58000ca903031030080c0180301020b0001400340104040c00d221001d8084402844080c162810050303030a817411101880c4400078080304042061074007211040c26680c00798403100d810020b00c2c07540107410107000c00300940e011900141e440515603440c100402004c00a11a040d0205406548140300020070810085c035140c245e41c200580c458000d1400c01c507803242907140c41400b0609120401014480c0401190000c520034a0010707128154080041d00038448411105504510b01d000455501090b078001380d421031180c00d5181440e80c0d8200d044403010072030720000350140e111046108841d0416030b0f20500120018052200b0b2036803c1a003403080d001908402e4990342d503501110700d140d540c18014200503111020091003203040112a8150500c80d9110b4101d8030058000882e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 606987032 1250 606985782 606985787
    0x9030414012a030e010e0306090717030c010f290904020103020d0e030408100c02071404020315040c0c1203020a0801050f04140f010603050610020319030f0906140711060403030c 78
    0x110151200340394241c0d0b4044146005010b50220390840d902080d034115a0004900d00040c2c3d0610a0300c14602410590b40391542e05c0714601c0b0519540d5030140001d001480c182c0340d09104005903401d0062000c03d010000802ca01c40700b421001c0121a141034010741c4171101e4580c00d620070b4000e54280390060f074450b00d0302c4440e40142030006045010f40800100040d000400044a4012409088040004030701e9035009030f80d0b034a02481511000381529044984d030345001c0d809180c3c0148500031000e402c00c4540e00143c22106031010100203d00e0308a201d405002011240101609083c02c04525112040d58007030645901407141505c6080c01d03400800302038403185c000c20383c020111031450040341486903103140d03003140901078030340020f240c100090b1482c500000a0b00c200e02d0250043c5140014180300d6414641c5048000b03018507440e040d08001e5823040344140e4040601443e00019111908000b210003071102410740e40c200220049008414540414290b030010341c14140000c038000c854030709 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 606988282 1250 606987032 606987077
    0xf04141b0d0908040f0b0412141606120c030c02101503020d080403050d14030f040501060e130308010504110a1b0804030b070e040c09050d021804060b090903041401 72
    0x2030151800c0800001c104500f407400350003561405d1440508a64803143c008181e0700030781c42109040c01c00000810045665070442181440070354058648001003000326010070100f0ba400280013902e405141d28000754648100d0350a84000d2038248101780081c00000d5a8000303900113000100d590718422170003002c2242002000790f5002c1c08a8040a46504101c004c035005444251454000c208181d03480d01e04c9103010340c203c1001d142041c0c0c1581c540035062180c02c1002172044030700b90742e00d0b8000301c0c0d110012000180320310030301c440c56280320b40c0515000b0800b41c01a4002801f079400c25100c0508408002d085c0d03114180580f81610100d410100002006101640094001c0d08009008428490034005117441210f694503103003052000d0748107010445ea0000301c404006031002c04140600e2402c001308010b0240002e0004c1140d4038a00404d11078000d0507074040300e00309d90341d1007003000a082010301700e81e04c1210743c4055818181342c0782c0f490428400d0004002d040081ca600041c03031040c440000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 606989532 1250 606988282 606988297
    0x10b09150310050906010302130608031b210c070e0412031122050a151403090106051507050c0a3f060504020a1a0904020a020312070c020f04141b 64
    0x303003e80d0a0003840c143d1198401e00003a0f008031500d2040e4a001107250241c141200c00410080d49072961040c144070005000021840f40340c0103600710f61041c0000020b0491613040c030503454940ea0304d500d4a4091030b0080383c0d4003100c0d4641c489020400072420202c00c5541c22402030402044030340541030000c0344c80c451030820910800c080300808111541014807482521004c0d1602c9000c2a142c02c0543c040d0305001d9070880000d01c00e00c0003441400c409401450f0800306100001c41c44507202c03800039035000408190340b03e03880f0000c11007000b0321a0400c003000c0c100d0030503101c3c1c240c220300b81140c5c603080c0c411200084100000030401148486070b0074200440480081c1000c0c00c00080b9441c28102800d000e680592095084030f01c0030a540c612101010015040c1c00040c41c60001924103120283d045110820309601041c024100b581140c0b038001449010955210700c7d1201082c41040100040d03660281d020381d02d40a0540050780d00480e01c1900890480314504541d507015019000b00d1003143c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 606990782 1250 606989532 606989563
    0x1b05030606070f1e0c0f050607121e080a0c050a0f051e0307080a061505040504150f0e01030c1d010e04051606110606040216021c0b01120212010b091503 67
    0xc4c99501d602e0030b04c681e90348180c0d109011a4610039590b24041e080d44c2801c0c090103a2080701000784c08005103150300d92651141080c10030007458490301c495440e41291549540011510500810a4054062003600d0044450b82082c60401024000042008012885110070720900203880d034800c0c90711040c03030203014034200b0040303603a880c0054006104a505880800c416420f080010a201c0101102d4030b1344c01045a403100c0c1010f1402042001401c1d10544411600c20b04e84004500341e8820b1944c80040d050f000070b40f0f0040d51451526100b41c0e1040d6000c2c0c92009266043e18840000d0319010504581401003040c3c620340ba14146917041c500380c0107032440d5007000b216001400c3c6420408500740d6881440a40701150741d2881071100380d11440700b0b01c00c076454800c0001e400501e4000140360500042c050500100601590744d200031070320a802400030001c070322546804500d0000c8082010382c409a00074019902c8230004540051006018400426500800580759442c2040f10000001a00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 606992032 1250 606990782 606990803
    0x509180102030c0d0c0e011e0e09010b040f0f1212030f0f0c090e061809030d09150609150509060d061812050c070b0f070510050a1b05030606070f 64
    0xa40850000e80c4130b1a0340300401410b191040541c2c50007602d1020703e90760103031200505446160320707548002c80c105005009014104064213160307101d2001da54003174a1200301d056a04d40c2403444514100e1603a0f48010890340c45818140000b00701070300200c20303640d4002d0620706800052003055000d003011041820070b441c64260458810701040d0000200100a6216214101d4566001442402084801c640c114410041c001c6d40107016080050f80201100706807400c02c401c0004603015a00303c11415120b40d104945010904078484c0709000c014400f08004000c1e064003481002c204091602c1024490a4041e00103402925407840446280758060801c1244c2c40d0030151140222528800541d0708182c008115020305000710102d54034035141400034984940b500d15540c03100c3d401560014448081400140f0005204202084680e41e12140100e40e928107030118000301c48904031450800f01c612039a1040c1290402d0460303810000c25210a55100c9450804821120803401c0081640420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 606993282 1250 606992032 606992041
    0x1051e03040c030b09010b0603150a0e01060207031509120c0c0504020408070e010902072001020a060905030307350402040908161103280614070504091401080601050918010203 77
    0xc0c0302c0c210180ca11074601e440303035a1a104541422203a0b03c400194000c0c40c1000414800f9101c03041c111003540300100300c5021310341c4801d8807488042c020b0317009402681c0801c00600400400328000b00d41c507149040100b100200607154429000105811482888100c84109003070003891003500001c1e140152080d5685c41d40c074440e4540e501c509100c2c20100c141004004695210b0034000c944403103400031042d02046501c08001c00000c001180014150702c034030f81d0600300140035402550344080c0900040c43d140c1c9031141d4054003486400e201440080540c000007507901008001d01900044a20840701032950f8034400b1400400d10402c000d0040c3c07501294019880c1c05110340c03900031600c03646103105088001c1007450b80d42c1da24650050240b680401000d011414400b07180c1c0900c070302603200407907a4010f00898412140781580d000b00000d02c002030600900b00240144080d107048000320244540c50305040700d855070818018036206008100c00310311f690185c1c3d80c044c03d002c4503000003150343e81030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 606994532 1250 606993282 606993293
    0xc030d0c0615081903030e06060f1009051c20130c050408120a021213032012010c090e0f0604050903042c0f1e090a060504080306090f070e01051e0304 66
    0x518113030840c0082d00301119000d208201007501c42c090213010b00380d00d0250f00700108102001c4030400c0c010040000b465400605d0b503580070031109002200c0c040424401d0840d05146010b40500c20408142d4400b030940c803401922120482c11404001c40000100c000388580115490302c900c2e442510140b150504404510710004020f0807400603907021540710f00015082001c1a0089201c0c41c2000600c8400400201e42d41d07101d290385c4c81d40754044111011042400186000c80d12400c0720314180e54411540310306c16004085800034005035025400307549010300345c0c9000c0b0000105001d0080e0303241c4003c590303010303410400d40700640145005000f2610a40d10200c160014034104403030000d804e5004515826046d0000a0182c00c1c0c840c8041840c03400304d844e4030030700724000c0d29482951288000310b00c0400d000d403148500840c4035203141c1e641d038103181d01007081422002d0f020201c00d0400e0400d0040142d000342c81c1004d030040038240140c0745d0021170581030b9016a000e50f000d184843c000f040004204 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 606995782 1250 606994532 606994573
    0x70c15020c16181e1406030105330604050a0e0f0709060203032a041d090106121103030d1a01021204150c0804051f020c030d0c061508 59
    0x580c184112400e80c0c2c80c1c00380040703014119101c0c07000e83d46030b01c00c00c80c803420380c4503086030208010045100314072814841c0c0c00421a862052007004401002050000030302d0280500354005014981080c603407110038910b4007081440b07103010042c1c180003544464150300c81c1c00a0707038001c10340100440780700382e0340b098a80c3e00d00c1e42c00c880c0310022051210000702603c1c003408404050703e0b103d900035411540e40428425100c6800140011101c0c040c240d644910540100200003500000400c10314010b038400078210744800c003070040c58a59041c80e2090025580b2400380c40c41a5800150001f2600321715404641580704451070821100d09009014440d80c124036140c000092007070b402c80d20341401d520045a1580030714003c0c00072004e0428010b400c5140f040b5101310415025840e0305d85403a0ba03810004c0c0d40304a046c9001440248100c6510303040a4040c800320156a0701a070150055000c045e80040030350b0440507008159030751310700304000400b01c1006040c000d02008006c9600391210882480a242c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 606997032 1250 606995782 606995797
    0x3050f0a0b071407080306030a02130606020705120c101206030b060f03120301060302070305040503240109090c03020405090c04060b1e0c0d0f0c050607031406040c021005070c1502 79
    0xc441004109110710070040c89100f0314101503428281021682d0307210031035002034040b03503151081c04101d00140ea09c1648401d810300301030000003800c03843d0190203820305034103911140c0b2409403058201500c4001050152001604503043c0c6408048180305681c0d100c001401c900046182580c00304c108106150799500070350b0115000c00303014000008242c0d8a040b0000d1681d882c09003031004101e003600a4000e018102e00c42c0c00c149040c2602d590101346403803c4500303000c3c10701c51030409d19000c09410210150161111030814498030f8020f032121801d901491000074003031603648000031100074041c001100c04000080c014028595a010f104603107421503451400003000300000c240c03800d203c0e2070896200701c81404c060081c102e003010080d41c440c3e000503c06418031400c050b800d40001d40900002d88101f40607180040c00702c041c24051601e078070005020368041c2c0e1400092488050700080c2e0142110514403020680341d0b96034000b150f14801e5200000e20700780d42500400c8000b0141e8001c0d0005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 606998282 1250 606997032 606997043
    0x90903090e10050f330c0604050c1f0203091309021806031612080a03150608010f0b07021e060c01020d0506040506031507050a200a0c0503061b1303050f0a 68
    0x244c0498100840c485105c62000d4401340c903210010078442c1210848035040c80ba4210140c24000422072060800d201150110381c2500840b414801901d001c04d051060342d5098201080c861900140c003a65030700c21580e04134030850ba0182e11160001d5650800d1113140d501621301e9a4003c0c810070000c50320902624118401e0045461610111001000010880d00a1240444203010030f44a074011740d8008954241059250100905013a0340c01940364002d080980d9102d015600d407140d4251810b102d03400000b0040401c02081707016035103210060f020002e04c2c40c000880007851000043d90381c0b041303904402455002281ca620300c1ea0035507024900c00c250544003072189a450404254558a0002911219800e40000f1880292113a80540001042410040e40f0803009042d440602a12070300d890200d0f40c00f5900c0003082020541030f11004040a0f00244000d060001000f07410365a0075a051256800116084021040c0466078134000c640200c01c0e2401c01060b00156515140c3c4004203450 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 606999532 1250 606998282 606998299
    0x3041103120c030306180c0f030c130f18090803063307111507080f0403020d12030c0f02030d0207050a08040b041a0a05090d050114100f050306010f090903090e1005 72
    0x1030303291b1058000344158404034082d81380c05920030804c222600041d101050b01c40c1c0a108505581c40341d40601c50103000002c6c0c21010061a104800300c0034500c0c0b100710b01c400d0707042807500c0000811007411b49070002001c58100c2000c1c0481072030300e401c00354050302c0d00c5a035014107001c00740000d00c100c0c01030440d54001d80da194182240001801140c019140f0640781407802088000003290405018000545029141c91300d0a65a40c00007001412203140c144c581c0c1032800e24240e071064151103034500c640f10f2810005440080c040000c0e48038010015210700da10380026982c0104030003442031000705940b000c00c076601c1d42d07240c160444050300240203004c05c0408070004c041c848031451040c0c4444460541d2050728101184003031145804090008072165902d60b698500301d400d1a082951146140c41125240032b440c001d507131000000c00d90301580c0a070304100d0040c494502e2195401007901c0e0065400314000520340b03000c0300d001e1a90303404440c085103060f013880790050540104c101100c10403590000b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 607000782 1250 606999532 606999559
    0x20d060218010c11010e13090809130506010c0b10030c0b040602070b070f03030f110a1e0e010203071419050a151406131e02030105121203041103120c030306 69
    0x4402854a1401600603c4e13108802912588155611340703c01c440900100080d86441800200381d5002420031201c1d8900410780200500b007000204045a84080003480785040100000c1c2200c2100840509002c035500002400e95580e5403440004507484185904103d0391201e0701030498100380202c200500a03c43c000400074007a1043e6200a0b82041100000504690307043d4001c01003d100e20480544605a010401c4000d41c050000c1c0b8005403505442c0001c02842e200000046401200034081c00e40c80314a6207990000c1500d48076540404084d05420818480910f00b001e00020070300740c3e121003010700c2c040000200f0380307203d40d80c42006c04900b848800c1c41803400b039807a0070070000790418040000400d40c2c40c2c00384210268041ca88400503200c0201c03100c035002544003080004800350000010003803420124041c03001040054060030205442c000030203d0391001070b0028001c40034014020f034195409000b00344641507500407580e07481550303002c5561a07400854480b40320b081c6030321001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 607002032 1250 607000782 607000787
    0x31412060307050a0f09090320030d0f180303020c03070c180509011e090309030204050a0e0709090203030703051803070e0a0e06100902071b030615241407020d06021801 74
    0x11005d46804158502649041c035024030010001d02c1c03015001c00a074410b07440c88020401c4c042c90503c400c5d100266981d6401c07003c100c416624040b001e0034402d4505109a0300080039010904102d03540f41c90301507503501c502d612541c958001c200300900005182007002460504a0710a43d44d500c1c0e1707950060006a07100c1446274200c8150010004400713a481902c0104003c9681c0316548062013400c11445040e125004282101e40480705403001c580d030768001103130340c102c01c0002d0b200a00c0390210622204203180d0100380c5900414100809119011400800e03900b10b03010b00f80d1034210080c0845903440d95a41c800b440c002000e8440c80d004a14000556901c403c01042180c07058000c9040d094000d803601d01c070a0001e600505003680c001011848500c003822150880e03c009502524010030381e14913001d01c032940ba1050754040c40401d44140701803019070310700d0002c20f07280e00c10034244540c86040c00e01400c0b03c03512600780020761142001900108100b40e0340c0c0900f0f0381c02945194100c1d1240e680005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 607003282 1250 607002032 607002049
    0x7020706180f061110051503010b060c12160803071d040b09012603030903070302070b12060910051804030f0f020601180e120301080c0603060d02010c03141206030705 73
    0x2100409004150b0030701403d801483c120302d40311508400c890011021803140000ca60050314103640007119403035060341a180c01d0081c030b44020000ca508601e401300300c0071955520000d02c05042682080428000380d1410b0440c800701764076411564403692441c20001c01000b1101d40c00401c00e442402c5d1403c0050ba0a0500c14484c81440142c1000d1150342064044203820010502c041c0d0341034014203000640e01c1c0300b400a14001c0d4100c0000b17648504041c50041e081007440c1d080005103d406110b904401d01e0711200c0a9045001a80ea072800c2d901d41d580216108145904002d803c42c19840d56402c20324240c0d00660700c100d00a940d00003c0140501089030395030101c4001c0d500581c403410061240c42442c0700c00009201c0c43d0080080c02c9404100042e04050700300480c200c040c00040010003040c9024000c0707980d418001c6415178510314000d000030f603905840b09d0019040082c0300a08400b01070150040c0e44c851042d11400c00e44590080c0a50403174901d0844806010f4098541c2c006041d0400006 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 607004532 1250 607003282 607003289
    0x20313090218091f08150714031b090a06050c0d05032701090c060c06050601020307020d0303050a06170d17040b01121704061d0f010e010c15050702070618 68
    0x2002c2a005180c0d0200310b0a210040c100003201c2c00c203038081260b10444680000d0007441c1c10400f80984030b600519200015900030207807020b0022980b000c000380000042180d03400030140004096490078904001e910780510040242c00c607098400105d00d031500800a070032414a0b0b2411207a818508040813542c40c002900c0c044034000c04016014041c240b4541d503141c61286c1440000340c1c07031a161b203c0200d011f5443e03200c1e50110310000384017030610a41d4061294810350a000851600302c0a90114404410100002d01010350381c80200e16420481d800010043c04150526840141040b54403a11341401501b0748000c80c2050001c48407999440000e248070310380190207614141c1c603120390000c2c0b00154640032031f000c100b0071200c022081c440101801c0a480c056840d0440b01c03110000500000010890080c40b4001a035004030850317a001d400a20384400c2841d140c5002d80c56850018425280282d00402c254108400c100d81168005150000c40d111603480107e400c1d0704c03500c034410800c01da01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 607005782 1250 607004532 607004557
    0x5010824180a0512190206060d061a031c030608060f010b071403030a0b0103060608041709010306081504020a0608100b070311031201150f090e060f0d030203130902 72
    0x3000159011000010781c81c0031034240701502e507100c07815500c190400030440c2920342881004a0020b01c0e0804011802045209900041010742007010001d4000107800000030820760321030107403030405210103891049080c8081d085580d05825003400501c514441d00c07c050000346420000240c90400080e054003810369528101503903400d252481c1095070100205403810800b03001c021180440400045128100941e000a140c4105800040590340c0a41c03000c010041040140300c04110b4544a03c400b070324805242559580f400300068001d05400e511203000e6000303150090408200304800607200d54821204a0030380c2c0e480c0d8500b911a0402900d0038142d18008000502c82100000c0090001600a0404000600440702182d156500c1061701ca444240c0c0324004000340f40e015070324050340005508161050391103464000740034016910404000c04680404903034280c5614881d8032000380090401030313900207113081c080d41d42e038426416080d00703042c0500300040c18501803007a248502d1054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 607007032 1250 607005782 607005853
    0x9060412030c051803010902090106030506180f07180b0a050309151905040f0204061202031506131a04090b010e07091d07031d1e0102040602060c1b030a03050108 71
    0x1440035030012690600342601036580300714120141c1d990b089c0e5140244140d90f030110b224031b485424492100080740024404403c40c00a0140001100d55120f40c09402480e000300650422450400c0e4098a5440f983c04494001030f0800810b610600035403160031084c04881601c288401603650300c42c0100c9000000803c42d070b09a1112034001d80000da0450b000d484120128902c40d000201200c0242e8490408144041310722001c5080901c0301000150403c01c1426017480c04001246002c02540321082d0026560012940401301107008403100399400b51081140c1606441d004010700340a002d109065690b220000d25010b00c2a000c5005441d40b64820003003030720881c80840441c130b00290000e0306041d107030500b07480211a25843e001d0382a030044014240780d0000300002c801710038001c1101001c0d03401040148040d0f5000103101340c2101000074003070780e03503a2005101075443d00c001e4074011140c0800103030349035842c5c4d1507005070703050750900d0301515510155070800e4901409209401141d10b50301 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 607008282 1250 607007032 607007047
    0x601020d21020301090905010506042702120d090f0b210705090d031d0109050d0b040807080a0e0a0501020d17071b0803010f0503190f0804030b09060412030c05 70
    0x14914035035000800c40024101d407a920401c881643c01c01d80280c0740302c035621814103050110901495030050000e40301000305059243d9051501403c808003610a80c8480f505003086465000c20366038106002000e6900d0b088124400418845151103071301087d04a40d240400c0301c000c2c500407036200f584080700006904000300c060281030f4000400080502c482400508030075120b83d0001e140c9684260b988418403030765a0035010502041540907030410550004c03e00181d250a05001c1d07070369400c815006c40d0f40c0e445241c5000c4512912a0045c08a0030220304500c000c1d8004260041c5404125002d0325040d4852004903511544040710800141d10f0811038462608003986041d0001240d18003411200c4548088888241e054202144c00145c00401008031080039100c060103070200b1001340c442c19190100414144c3c04110b0040e00000c44000368408000c0040205c4004641c41305c0480c0003403601000c000d4580c002120280d4040003181a8115070340d100b0b215a400a4441d5180d80e410040c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 607009532 1250 607008282 607008287
    0x50a0204090608070b0d0c090305060a050a0e01060302030a0f0c1205100b060c0a030e01141b070f0e0109020d090c030633061101020d14090c03030a0909020306240711090601020d 78
    0x47c460f10000901c0002500403003c11401d00a061043d2600c040100e0780d424400c107080c084a0851b070886607140d00d029414001030f640490380310070454200d4010300311182c50b0b080c2070b0380c0b9884a40c4208440c1e83c8100e5144108040824590325060240e801000340c18007010601070284104d240150b03164211404110000303028800320840d45a042c94036031400c0301aa50300b54000d034480d02203501541e400c0d011000728040100f00340e4005d05000742c2d104401e04c2c40e08080b60303008078040c0101d140b5180c01003484041094980e120a40c00c0b6001a00680501c0d030300e0411600a104002850b03041e44c040325401010b120001003020003007140b180b11925183e2500c0403c6401c240c1003120415155020030a04100d0610350107000d11407520700c14601000e082050a00e49041d9452464a010b0f81080c0140400030b80c20080d0070040303132041d01001d40d0386e80d6140300040300701e148102002140800c09040030300b0547e0b100060302c2d180344180101e01a035400c0c00100285502e00b1101d00d401a070140302c901c15041d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 607010782 1250 607009532 607009541
    0x609030b07090806090a0b130c0b030916090b10030e0304050d050f730309180b060f0a05210609011403100c02030904050a0204090608070b0d 62
    0x641c1d40c9000d80c03110392210340c05030600c0810b0700c4000240e440500094248800740b080380d500081142c084111401d185e80c0d07401910b13021407064031071380c0102000140905106201d100c15840100010000f950307112103c00c0d0042070f00340a49801602d4500107185402d00900c651180398801500460406242804100200c0c5101034211020b0185600e5050180400c2101481c4500c03100300c0c80c41c2078a5060451940003a0b040e480c584101407070880a030104403070074841c040c8000b500c07000d103104a208071f0303120f181940d204001c9031300709a02c810140f09156010a5200644002c40382074011051820500000d88028580146d40044200b000b10000d1114000410440f42d50781451030501515601003094201c2c07461002c00240684401c0104074500900081d02401d01682c05000f08100c60b800300f0f569003400021150080d640f003507500505030007081a5012104002c000340418505195003030080e4000c0d2180e4807845040c1980490110300103d0303580259142e1141042c14580200c045070b0141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 607012032 1250 607010782 607010791
    0x1140d15140109020a11030a080109050c0f180a0906050603010b0a090305030c1c080708040b07050d0e0304090e06010b18060d0606030e0c0f03030405091806040f030f090609030b 78
    0x180c1e40c0042181100310140214000c00700c600300161503444031880900715200b20603039040c090300308000712440e85805c8030b1f402c0e05581540200007207a0759022075842c13035803280c4c0031010030060000c511a200e191006070000322003001a5882c1d10803070f6440200c50161603031801f459601000900040c0301e00000c040260901000030710b010b15100f035803915000c3c255840348581c2d103090b8012906402408814210700810030409103007000361854200c2000b0b02603030002c0c1005010140b200c0100302c12610841c1694403941c0000c404110610006043d80e030380340e00510403220400c0c14490b8040142c400403868078122802030078100c0c600510b050398800c20030020702c5020340c00841806805180e0b110b41c4500c402902e00b80c0c0700041c000c00c00140b414070302400120300a00c01d10361201000b40b60349012060300d0403034905890040b072030b41712621300c1030610840701d82c982c441d032044404101c1400801d902a0200c24007a40300c3c0201e240741c410040f5001d1560307009881c00b043d40258108001140d0031f291541c007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 607013282 1250 607012032 607012073
    0x8030d1a0a030f0b0c18040c0e060417060a020c030a11070b16020906030c0310090c081209090a11041202030a0c1e0608060907051303080d1401140d 65
    0xd84100c24002122a0019041900c00811040c00f010800400600180e0001945d0071228107101c1180c081500b1810b21400041c0215151a0348070b0420340100600c0c080e0032001000c41d5100d5498220500201c2d4241d031a03e8901d201d520085500030142c0d1013102ca24480c80d2380514500390112506440709000011484590301c51400d00103010031041c0054803c00c6c900c0741004260040500421803240f5010784200e100750840b800b0040c0d556000100c100b01e10300c0d0740d0800328004032181012005040319500680042c00b400c0b0000060081c00f000502468404941c10065a2a07000c00c1801f110300070050160403074020042441070b04801e811000381c080c0700600302c941100d080e0f1b503140051445980807842c102240b121141681070300381030100c050000c0785044c402c240340c40b40009807040c9001d85203109005001a14014107402900b50704c2c0555008040f60b5039421800c0c01f910020300145402048804020707001240705100f56002800202000f0300c000250301580e02c4103950240c650301e03588007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 607014388 1106 607013282 607013321
    0x150a09182004090b1605071106090d080a09050a06180e0a230601030c0806030a06151518050108010b03180a140a02040b0a08030d 57
    0x2216030000001d10900c031000c076100091800d100e281c65005400e004118003800240315500d4022480d10042004c00407043c81c085580707004041009060000341214052103140c184054030040d030f401040b070204034402d552070407180e5004003288804209050030411052408400280007014a403d00b41c3e020308904164102c07811a031f008001c0c1f9118410086440d804040e80024103403608070000f0b00380500c0d240d0825460b040101d8849000900b40700d60146400e101d01200c07805441c01800401180c1c84ca5a1004051304240075806062190343e040043c81c420445444201c080d101e88585124050703201d0f940040080d150411814004014010411440e100007140c1e480356100e140c64521350101703800b441c2084002d0750041c2c284244030142d1110060b01047c1c2d140d050b8800c039020460008428188580b20384144104400c54106100d05944130035180c102c0c00150b052142d0210303 = true := by decide +kernel

theorem cover : BRFrame.Cov 606834532 607014388 := by
  have h0 := BRFrame.cov_init 606834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 606834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 606834532 ≤ n) (h2 : n < 607014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
