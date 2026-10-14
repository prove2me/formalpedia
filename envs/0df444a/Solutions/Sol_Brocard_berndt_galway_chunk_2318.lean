-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2318
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:44.619565+00:00
-- url     : https://prove2.me/submissions/7784307a-5faf-428b-af4f-75069ec19627

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416726618 ≤ n < 416906474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416727868 1250 416726618 416726621
    0xc120306060c0318031c02060103080a050408060a06060906080c07030804050c030a1103010b0102150c0c1509010c080604020301050607080903031905130b120a2a03022203020d03080406 81
    0x1c00c03004190680359076042c013415180f18420080c10540c000c2c8070300025028850401148641c2100a60b00101441da01e5a1742e403800c2548140100400c000d4113200c00542e00d4000c01009000e00b50702c0d400815a00d04081c4000c0159000307034040404c204a0000388003a01c542c2d04111203007590145054003003541c42e4144546441000b040c060f1b018071130302410005101ca102c4a5480e2200210000d01802c14110700490303442e180300c94009890b101e0746c4081f5078001c0041c0018180050904280c80c11881e400c400c2c003e0b0048101d132400c1c07090b51144205080903502408071548458121000c41c115414040407034594090060001d0034007200043d592010355040044d1021040311280c07007c5115508000141b45402c0000c3c0001583c603442070215260582c00e0581e00c035085102c24000e0503540b809002c401800c030002c0c050050b440e4408000c80c6580201c00b988941000320b40340503a0303c080c070000170300c1207402015014500801821041c4016907c41c0840c0c0070f0103403d80307003076106c5403201c0c28000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416729118 1250 416727868 416727877
    0x30a0603080408030406140901020304050108130c120209101a070501020405030304090212010b030f0601030f241e0b0a08071704110103050c07051c0909050103060f0605060c12030606 80
    0x3010004040ba0005440d00000028001d4a440340e4070450b4107100c1d440012003034081c1402482c00f5810501c03050050b0351240e1000b1781d1005100440400500442c5c0b01c1484e803a41c0e50704a02c1004010302140000e504150b010203400a000400d00000c2620388445190407585c0301c50010704000300010784406101003501a14060200101642e079142e0307175594028000d500c801131002c003d25141d00005003c4005405a921a102c0c1e00c01c80c169698521004600600b01c0d0b0311440010f170b66410041d030740c0d550f4000c445024107040d802324111580c103001554501c19174108100500003003140b41805040d04400658111003030a060151054480707050680300f4601c403074400805203491001300f00501540005481c0c0c04442070724200010380f21004640d03a64824414041c00741c2d403142c508c0c0104848500700c04c41c110b109900d40b00c00043e480d4510340054840c02e80c000e40d039540e00c900c0c010002d08014803404c8001d0504942081c603000300020083d4940000e144890707040880440003c0240d150700046a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416730368 1250 416729118 416729123
    0x31b070f1403041a03041109010f03061e09060504200105070210030e0616120504030e0919111e1201061b230d030b0a0b0903010b120a0b0a02120c030a0603 68
    0x104e030084504040708410b40c01c01c941c196001006088462032508003201d565050307a4180d03002030502801d54035803401500c1c4011070740d02186807074400380d03100d009540b18058095100f0b0a011501c1e04150616212490044004540064a0880c840000d0b82c000007194010f0313034150344100c030304540c5420940041c00c298074485120701494080024810790050807401402c040c3e00c83d85810480c6031688400c0711012580100440c5109010305264070702070ba100c5920400f4081e801e00f08110264100e000e64440c020809480b250128000184481140c421120804072010060411041c136401c0069801d040c4101c105206a103250549040440000c103150b9507000644041c040b44121400c8001d41400f280b580c0f581d00541c100b80d09000d11030f0041070020480244540c07803260600740e4020b1303194450450b10364150751b00c01d162950768881c0030010750b40c0b4865201800d9124210300304141a0740e40140b60000c410310410480900004050205400c201d01c0c4199945079522440c0345002801c040c1c101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416731618 1250 416730368 416730389
    0x315010c211701060801050d030e0a08070603060302130b090402010809150c04060e150a030b13051303020d1b060e0307150506030c0a14040c051608031b070f140304 72
    0x108820039401509402d00702000e400c000c0c086a0340c1c1c1d40100e9068600f80a81944081801a0000400d01ca41c40b5000350850040c130340030905036a5040d00380b0380540c40c2c1c4001c0c0400d8656008206518140e41a10030380c0742003000610004580c580001e5450000a00007814040c02c3e0020035000b401c10440104003664811b456a03450401404030102d58120b80300750000282d510281c1d111505140f5400090800102c00c1c0c103051005065069010300740582c00389070030080d20b1030400d098030701c00d01840740141941f01807900200d2850a0003402d01450000007018030009407c0445866090b86400c06250703040840043c2698034112214254440d4180190a040346458402850b030300b19032080d8095941101120844a00e41c03050040712042ea1003001a5000d862900000c2070500c0e40088800d0401460510305d412402c16101000e20880b04060740c00d400c000c0108800c58081c0e5408014654180d2000c070b050107881c0e6074004070323107144800007400300c81d40080d4002c15000c02c01c00d82d0b0241699414 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416732868 1250 416731618 416731673
    0xa060509030304021e0a050907050f0f0702010e0d08030a0c030f050708090606010f1437080703020f0304020d05100e010504051204180b0a0b07030206040201030509030315010c 77
    0x40d1160740750010344060f03214416190011801c00000302c1030894000000d000002d803945803600f004601c080040449040c09030401514511611107402003188480007001e20380c490310140001401c3e03080c0f00e00040d000c1c10f8047e0308140403410850603a42e00180341e500200d039200c0341c035504a018107991350b00b20380703018146428403a410b0f13000b0184c94403e020b10b9048400796592013004480c0c6003005440c1201080000001480c3e8071580310061411b401c00070121107035020290032101014224441c840556940a003200c001c0c26880602030303402c07560703924055013402c481080d1261036210113007000f407299100100020401074103001038610310180d60b1080000140200c031030390182030115000c8605000b080c84402940c1031200a66045e01c8004061000e00c01c851314040c1e0080100b0790403503a1060800d000041c20220b03160081100074420303405071a690500784001f4003a5080500001c600750001e0041006440c00300001c04c01c45003003440c10501c0616642890b0054980c0240410f124954103038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416734118 1250 416732868 416732881
    0x2d0306051503010216200a060f080a02090112150302041b021009030206011509030f23010b010807031802040f140708040b0103082802010606020d02070311120a0605 72
    0x92149109030300401c0006400e03460744080508034442c203404031220030040507417580030171400c41c102030462034030100c0d034801d68000d0b4002520400050b4400030000e850810f4480e00c80c0d510000c1660800320b884803e50600f811440041c0c141e44111100c59007a96840800c0b41c102c11852464070002d58000e0410884400760110350b14503900c41030216405442205500081d800e20f511558452503055405401b440c0d00302502c1c0d01038541c1d88040041080040c810200101d492051804441d5214841c239040d0145650720a244800310f070004249583d02d080c05100c116608104031544c400110300c0d000580c100c0c0300803094005928900c02940081c906050101040c8484d880401c0c0d0440c812090f1020313039034520b001c0b62000412a401850290b8807001000011420005440041c1801503408421000107002c0081d00c2c2c1c80480d15001030b034648104208207501032200780e1440c3d4442c400707000c4041c19a02d8011442d251022448d0240c401c0035000d148481741805020000e0f58040c0c0c0a002506100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416735368 1250 416734118 416734121
    0x190e030c090c0d0e010e250e06220204050406060e090a0f090515060405060d1703040f021e0f0307061e02030f190e0904020d030309050c0d0807050f03030c03012d0306 73
    0x106c1110743c0b40710f1001d04c26441880010116904180e480c009603605003083c00d010941500680440d0b0401d10122000001410b000903c001c2c644003000010380344e82c0303400308100c1901d99a03400441800040090741915131100c03a2440e5001a0804000c0b4008501d95000c3c401445d1020380a0100e002d044081000034003102c0c007403400b442048900340895158541004041400a40d0052910200c46141c0b5401403064000e154068004c800d50255081150089a0810354840c10015040c1c8100c80c54086403410420018000c20700b94020714440d8200344010300114003260320030070007840148041011601c20000c4950204440c41d4003516449000780910410401210303890200d01004220901030a001f4445031040c1d800901040c3c0ba803805482c113130018035800c40300340d600380200c0000c40d00c161035038007151804030300c248040769550940f41412400e006410140d00c140b0307002001400000200784d02a03a0650b045142009031800820714442c220b5404038050f203030000c4901500100b4000103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416736618 1250 416735368 416735381
    0x20f0312010f09051e060102010603021203031008010e0c0f19030507060f030c0e010f03141302030609030c1c05130909030e0405010302010807050705070305070803190e030c090c0d0e01 81
    0x4200100c0e003043c0d203c0300144260f0b8801c407040225155003d05800001a0403158560454010300000274150348079004190012207003c40c42c406130384008240440c1c1109100c60f44010881140208248900b4201103030300d60140407681d900c151201c0c420a400396540600a1104e201d65108c0e1084160f620305d4860340710b09607407281c400072a1195164800310741c020701072030200980682d0351403501000c010055038844e0740007500d001056035442d0fa5040f00d1240c100194024a0701d04480554910b0070704c101460204d0003403200038143c20500280c000000c00040e441c0401030f03840601c3c50b030162142c904072200d00494004600036900b0810000740207001d40c3c03100c0f00c424080da07110703601d4544400520090f0f410a1100a0000f020540001e80d440d1150018046c0075100740107444100f035890310703a81e141045a4215421703a800014181d420428140d10001c2e604501c0d0400041d0084500c000a071036490340500d4038006d440080000d03641e104034404175100d10500e400200101c024244015000340070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416737868 1250 416736618 416736629
    0x3060a0603020315010f0b0a020c0409050309030d0c05071a1333090e130606030b0114030f0c060d020d05090708070617060f1804030e040c1d010c03020f031201 70
    0x50300c100e110061003c05138942c180c0301000d0291690a181021100e5180d1100880104500a1540f0318456558070b0160080302800385004507100c2d00c900c0d04240c00c240303c0c00c05800034411041080b0700011000709520089800c0d1800500c410420626802003903c200540d6410545201380040366101040c500842480d903411525021049803025506040407000149404600054800c100d03002401d42140c1c1c0c010004611403110080550f40c0d441550781640040b01c13400c220740018425500d4006442031400d104a00402e400c2403040b03882034459808203058ce025202c00621810000b9070342d01105e000c0240660100010315042c004240c890100340112403041c00303580b1000550511407080c584003004070290703140590302c6000400202c540702c05051504681036100c2901081c86201c60755125074041d480d8840e480c214032080008641c54001da0700d043c02000441c50146c3d649401070810003e07401c0c240201400068181a4940b4050340b109000b544000079030030070202645045507040383d2 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416739118 1250 416737868 416737873
    0x1401020301090b0939070b090d02071d10120501021209011b0c0c03120c050d080403080f0402360109091106071e060b031b0a05061803060a06030203 65
    0x707032104200081604103556141002c0c00c4980c5c50714030301d041c61401040d86000c60058a40351001801c480906400c001d009403141c0710464100310300c4010503c000c4401041d1880541000703030400c4220750305154920031840c18140c01800081160902034001e602500180b000c2842075240c501c0c1c243d01035030004044c2540c101041022494004050190309052100e0360301c00c1c518052011001c803141d21030014180d80040c6091700000114900d0b181e0003200c1455a0764901150425040552500c0004809542001644002c10002c654840d185070340241c0038050700c01094950740002043c0c03000350040309540d4112010b4510344480c0340902d0002810351140351081c941c0c0d030349070306000b21070800c080585044610280403030189003c1c0000c1500621486400c40d01390340d000c07440450050748c400102c40c6181c0d10310040031a442c042210341d42410b40c8400c0b42d0701945802c00440c220b10401d12445005003c0880c104010003c20501d4081e40040902214120b00d403420382603001d0702ca14401603001e030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416740368 1250 416739118 416739131
    0x90f270b04320615090303070210090509011502120d090c09020d0f02130e06060c0105040c06030e06070e01051c02031014060301060503060f010903020d0f030e01030e0705061303140102030109 84
    0xa042584040d40f080e80700401d9220030341407481520b241a4880c00407aa8980410001d4030010b0341c0351075811030040020303030320715000c00e04101c1404440c0d007041c0c000ea040c14488002c510040d9600041184250181c144400d4440060800346c10207001c004100510030b266107040403a2111281e0701510000d064000144100c0003e101e22104a11448041d5240700f10003050a00149844141954000328003518141ca401082c0c0141400c4480c04ea9040300d07144245c00040001e80c0e031600503402d44d5212040a81001d082400d030140c000c500340c000352418060003003401c0c11401201c8003070b245440c440180c01e540d24500150982181d1400f4000c50307926610090111041d401c04800b5241615181d80342d8901d10b4a481d8100011541c1030408103040240850380400180c40384039100c0c655901c60295a0003c0c0c4a514003c0c06c003501e41c654960400d89800ca034a00050b03000a4210700b00c60040ea1000e81e00c009600a9040c9001203030400784c03240c000c02800a41c441415402035048601445040000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416741618 1250 416740368 416740451
    0x72306090d08010b1201090b01110706080a0515090403080414030a020a0c0e0c0307050c1603080c06150d031115190b031605060c0106031b0501090f270b04 68
    0x2140902000d17100090410700c01441051040d0780401e0411805043c40690803003409140c031310b02a01034100340b0016080f0800d1011111680c081c40d60080c08a4541030621042c0701c0101c0c100000007080601040f04a5000c00d00b80030b110300c088004180240e05995540520b194040d540b01c90707410003202c04155624000401d880034030401401040a04842c4d442c680701e240c8201c410350491640b4501c9800b801c103143e07408809044074035008611a154007511041c500202c00d04240c030040003520038807651171038000780790344210070003c01d00e41c5810710301c514440362440249041243c10702c040204224200340102040d440c4003038010f407012410f0600c000c2c0500030515444402204040080300f1420f074051045180c42c1025000d9112440c0c00020104d5480e200c2e000407050348106040c00c1c0e000e43c0300c00e00030303544e2000300703d80640300b0719250121032850400c0182080c0000000ea090340040049040451000c80d00146010000100f05200340503900c50b00e40c3d682c2c4000c010b14118a80380a107113580 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416742868 1250 416741618 416741639
    0x5070f081b16051c260904140703050f0105090a09030903020315010315020423010e0a030309140603060607062403061a041e1a09100302090912072306090d0801 70
    0xd06074400811480c00c504003084258046541c4400c03110440c05100340c6e5100c0c0c8540c4911705074246090805d041c10700b000f0201504880002c0c0800d02000c500e20010300c21a1a006000340d0401c04205000035100c1560030b0849d050f05035a04025410700604140b84484601d0380c019030305803409803503981164400c0900290407407146120704c04d0100d4104813900c04684001c032400700720340c906040400c840c180c0d54000800303408a40d00110702207a00340006100000070002c1e5145072a04c25280c40d4958204100003400501176800b00401042d120715020000085c2c40c0b11181d200c0394100c41d0103040707a4891130004058801c101e00c0b415140c0340074000354441c0c40c1ca03010300c540c09801c040318030503510b11035a4101d0140c22074001d00c1525254541c850407640d06d4403c1710512520310740c40b0000480f1700758030400c00d200d04090003408040e0700c41202070b61044108411101e805038071070040540701100d05411170290910107035096141c000c0c602040461040130a2591007504159035600050f030720784d070b420310 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416744118 1250 416742868 416742919
    0x606060a09170a210c12120507080118020a02030405090a060b0706050915010605070209071e1d0609090f0402180a0b010e0102060108072112020a03090605070f081b1605 74
    0x2171100569800405c00c1c130210310006403201d1501021901d06156003509940c001e4490400050901004007e440e43c000d035001405a14154194900100c500d402983c81c0030300c0c01081d21802d18003001c60300c0d8040c5035000200414241e50000e468002c1e606000e4000e01c3d00300c940d0b0041c0d000d02039030b8407013000a60310554162000b6803141030400c00107409110040000510749002d0180c4180042e1001c2c041c0c0740c80c0d01c00e20a141d40c0760020040511030b0180001030200030076004410038020323400180d84944000742d225050960382d19060360380c0d00000e150402c501982d500303140070f100d09206440c00550001c281106080c0c81c0d0382c0411200900480c3d82e04824072170002503400c02e281c1802070060b490303aa50300701d00d42c08006c2e9140f07200903101c088a0042c401c200a01680c4440102410542c01003200380007481d43d42015410000d05450380d14184104400c000d11100d80046c6d03c4d68682a00180c820105200c00b08482c0c140c00c004081e0301c2e5000c0036000744c510a01c0e0007040b5074401c565400c44138 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416745368 1250 416744118 416744183
    0xf0d1a1e010614030a0f060f0816050f0d1509030509030f0606011d150d2f0d05040503120c030603010b09042607080a08270606060a09170a 61
    0x2e01d0041841c5640c0c800941020b04065001c46e1901070242198a0a0045201505210510082c110310b80b620f024230303110394081742000076000090104607036070744d04003120401101559480c004502920308640401014228020301034a000402403e1503801406400b2036042a81101c1c040200b90a0f1103541d04c01c100c440e00d00044030096061000d105110742a00c182001904681d11800d0106240c100c640100c0c1c1c00b11400e81c1d841d120580c2034122002c590540d821203030810040d40490600342d50030340c4a60250300c4800750315a008034007008001c204444840300902140d00c500c0c24800c7c00194070380c1c030a42d4014407943c24510104040d06e000034141d4040c5a0181080052008802c1110b031454050603070315042840c180040c2c40801c189600601300009140d03030b0b1505524250301e011341088105d8078030320780000305034088021340c03240010407a4100104070360444d21400346150403078801080f07800424128103201404540035800044844010388601a9040410801d00c11900c102c804480d00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416746618 1250 416745368 416745377
    0x90712020a0207180b0907030e0a0609080d060609360c11010e07060c110103140406051b0702030a15020405060403030203190314070c0807021e1311090f0d1a1e0106 72
    0x4901c01f240a030b0310468030045410113440002c0c003544c54031070440d00161015100900d000400c80e128811074440d070f0001d08110b00b40f030710310141001c04031500602c0d01e0358024410700c04001d2011414040b42d03050212002c90300802d0010507518840200b000c071980c02ca1240940c206080315001d0b020205d200d6040d03031003646d02d0040ca8103598694486061000000340e0505a0700d903071a00689a59080c4c0d00e204901918010a1030300b13107000d82c0360004011501d1110341100602c200c0d001030303030042040000c0c0758000c042e0103d40301a81c15414005d102c0d81d07200710b0703000f0b40024001041640110140141840c01000b00100308003489058098403580100b1485000280c0c0c0020b168600030001c00c1c40322406001101c1c02c121032580071800f2010314205d003500d04444039005190600e024021a100b49403e04828402c0903403040c21b8401c0340c0643c0c05007510809501551300c04945800703400f5114650015140d82841190100c059042c0c0f40076910100a4501c00c10340030500fa40030500141202e002d03a49 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416747868 1250 416746618 416746621
    0x50d030b13110c072402070b1207090b0a170105060301080715020c0406030b01150e0a050d030c060f020a020607050703020a02090a0905060405060610031a090712020a0207180b09 78
    0x600000d0511060b104560303203040c002040030560400540015244848489042c01d1190030605c41460400d490707041198000301080c00280f60120596110b07640010070100540c8070502c040e40c0c0c0c0031243d0085c950600c0d0108040c001e45030b014400ca2884140101c078604d580c3d132100103200443c442401500500e03440305004100c0110708907104e076140724180c41500d0f10b0740c03960400642502c0b560350003583c0700744504c40184101c01c4c40c0707c034100f0445660f003045a411a5203201140100318175100380c61140f10000402d0342414040e014007861268400300800020b03902c8036141c002034204d0328190700180708010000d0280d500070350482d140c141c0c143c0c008008005c0254200b01007070f00010f116669483c0c4605100d00060340c00c1000e680070f244600042e0403146002d20a01180c8080c0d00e0840041500305441481540e100101c40c0003040026284400c00c0e65070f5980076520700c00d95103804500d580c400601800007550229410f006e23aa0441e0602e0440b98100c2c03119000d603a98420106c0c0e000e01c03043e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416749118 1250 416747868 416747899
    0xe0d050f040807120c0801050709030b090f01020708040e0c070308160c0813180207080306040c03090c14010912080315031e03070b09030c0601060c020303070204050c07050d030b 78
    0x902404001000c0c0c5049803a058640078114280841a840000004000b900500c00c201d1081da2000160004030f001304801d2500c41001401080203100281042c40c031040815081d11043c0061070300d001c1d50724005e56441070107150001e0603901c11300c11080c203607a5260204231081c0e1144110750819800d50303920142621032850380400b100e0154402814070008000e8a0002800b01d00030340f149446280c4000341c5185030103054140d44506407240f0b05048e204011120000b030320b20003582c1c0c002c5825100020309100c1d0010039030007444004006881081d411400242801c6c4210381c00d0341c0c204013a80e414548955614103540346081c4280010300b405028000a04d01e0449030601d001d0b6804024111140e8059402a0550440c4400300c0c00e07140c2e0b0400160305052080c001e1001e50041504002180b070615500798081d160702043c0500010040c800d1a280d095507020020366405c0b54004004020070704207414504035030352003e68102d0301402445480c140356400392185242c0c0030409000700303101c0302c07661 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416750368 1250 416749118 416749127
    0x2105010e03090117100e04051006082a06210114041a041a0613080105090d051c020705060c0301090e0a020f13090b010602012a14030901140f10090e0d 66
    0x44c8140c44101681c0c1780081e4010118102d00d000d54000c1010704011080c0000b0581507030941c5c0c01101a50b07000c08441b40465481e02001155041c1c00030051114a218000091181c401c0301f4550203d00c01c801c42c40e24201c021850594100d40f02164004c00684130740d000e220645041d881f40c00d02008055060403120304103601f12640d140680c07003444000400a030005a101e400440120238090700300d903814010514240300d02500107604100610129110807001040c6100784440f8420490301d11001c2407a80c105501911809075025003610090b1920101086c200d40003403041c698404d091034501d611a00c0c0115070041f40a4001d01100c08107100302040c0010301902448420b491581d400c45078001c40c035482081800380285a0000c1814001c3c0005007140b80c9603d890000090020529060f40b550082c1b800400101d586000545a07552604664014500030340000704e0004240108009102a00c0e80684150200d0343c0c680c1c029900d4a2042c0201e540e20301d0150b5003980940800520300303004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416751618 1250 416750368 416750371
    0x60501020d0305070c11220c0e01180b1c060b030712050f060909150f0907050105030106090e040201050d09050606130b0108040b04020f0d140114091c092105010e03090117 75
    0x3070903440302040a500384007c0c80c410a4581003d4a80d125800c2e480c41b940300030180200a024604440001c00b00700250414814910608404e140c2c000341d00c01c601c07800001c001006c81d0305504100019541d482000001c1d078022a5210005840300d8890381000c3c13002d1180340e00424044202081030340e990418403004580241440b00305100d103003100802d2402424043d03103d04034030400420700e41071441900c0d02e85641c94000e603040c01814001803044e01d41c805940b8040310743e00f50701c5080c00c1c3c45138001602c03d84604003261040d14201318100f03050150004d14140645801d81c1c60701070300004003800b48202c1e250b5000e540d00245a041c04100440c1001506540181c0020b00c1c143d50240c480b8006008035421300c0c3c04580748588040c121405080038400d1041c0324503940d800c41c1407071401c1040f00345c0364240d84c3e0b401120411050300c1003002911071901c4202908407016940580049004824041e00301100201d855608004142d0117900300402a00d03180c1c281a119823020000c54170b040402d0010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416752868 1250 416751618 416751653
    0x1501060f0c1b091413050307030c030e0d030509030f031e0f040509070c0506340311040b04210b22120e090a1b0f020708010c03060501020d0305070c 65
    0x150a00400e030b150395600301c400102020400003c680707011001c40c00d600c81c0024500e110441c2c4450f0a4004604c0120071200c54035410304e49101106410300d42683e28110760426a900156049401ca0805400c10f0042040305011411958400e07601480321b65248181407040780030800007000300412025400140902c402a886914103040e00d800100f00800d60840d6294005801e050181c814044203000c9141c111800c0100345401c9403000c8224000c0c8108050f00e030741d1081c0307aa1010b01c22a44a648110212803181c80d40a5450340c2c1d4288280392900a4014022900044010007182150f40c0c80b4a078070003035101d01c0480bd550384004040044401e449061140000001001c030001040a91030504000303454603911420558501404900300d001081c002c01c0a2400e544096609130042590581101078036018a0342c04420008a00744003103540412810741c20611004110340d0503400000c01e0300c10a03801c6924a0000030700c110b080c0c0710165241400700704075200038004074075205000c520050 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416754118 1250 416752868 416752883
    0x90a0818130c0816180605071a1005150403110603040c08060f070801170c0f0301020705120a08070f0801090c11150f06012109050c0307171501060f0c 66
    0x108080070405440c48403442800049030601040311152010500c1603c51005140c8a200c0c0c0b078010266110000c1d203070040905203c4007280342003c20040f000c0040c0c0f038414600c00088141840c2c140c03600818480d00803903100704082c04410085140110a0f1400c49401840e5421800c00c00300600c034884d800034105545072440079102094103c01007000c01d004140900310030b0464944080010010003040c1c0010034110390800c0800c243c1040045c1d0705450400480f510040c0004810000b4028891450004d1450040444514000c1628005040640000e0311441d2050ba602c02e400c4406001100c040008914000018444a09117510401c0701e86100d05299a903120988502440d0035000740034030401c50b104608002c003088c003004031a80c10100a003400100c03140c14200d41d840e540c0361802c0e4003211030343e94015401804410018854a500d000d03040d2098952241e9421802c0510107a85044e1403007031400800c9042c80c0309500074100c0b66103544614151040f0001141c4a001d41001a500207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416755368 1250 416754118 416754139
    0x904020c0a0b062707090503070b0a0e010509010509040f060504090302010e0618060705031f080303040317060a0302060c2e05010608010e010501200d180b040b03040f050f06040807050105090a0818 86
    0x30b0b01c08000c0719010f08030b2b202d0b00c00e8440100034402800303044006044c6040000500c40c844441e600b0005441100700c04940104121007035002d0740c0010081e5920480c0d102d42402074100c01d05070103601c0100c2c1c0107091001d03a0200c1e41e40250030403514098000c20200da88c4024005072015100310095a0009042c00a81160600042071f0b0301072088290030a11441e0000014001055000300240c800c1d28203100103042c0900d0401c0024840100d24880139018160001c0c2c2c0741c00c0007109210403070103410701502540300f41240c1e00558881a2080407400004e0749848004a080c0f0300070f98681d4121010507502030080da00340703001190710016610b0713800c00c851000c030181350452038240130449901d0b00655841000c0c01e00c03d03101c0e03041c2c01c000da4014040040c0802c03080c4040c04207441200d80c0711303801c0040402360b181e052a2041c50b0600307404000031240210b0f0148010040f03507074018008a40900006d0080780c49002c1001d86aa11841004040d10301c1003201010800d44c04a04911070b00c001080000b40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416756618 1250 416755368 416755379
    0x8130206040f0509090106081e07030c080d090905060d02040905100606121103010f1509090501030308040b010e250c0c09060303080c0f0711060904020c0a0b06270709 73
    0x30381d00940c20a10015041040034041810528140c83e8030413401002413000d245003500498071500e580407108003010380c8040e03007903039400100106802540d00c00c0c40c204a240d81e07030101c1d40e103405c2d800c0141000071b10419400a2200c02600945024400007403840d000c0040c19402c000c01004c03202401c56a90240c401945080c05061190500921254403210b01d02c210600512088bd00300482654440b50306000511400c11038603c00f10548031500c034641036502c007110050703c02c8607541d40144901400c080022007010360110000307004601ca00a89807440c0d803606000600d00e00c0c1141e07070f4541060315400c580740002c01000d030389200c440386d0309140f4100081038941880500040e0483d000ca039807200c50070001c0603400400c50b54811250a201400c0c196254113070400d41c070030028050008880c11185840355900c400445562038070003403045584998200b195602e843c8444415100040310400241403070070300155003c03e4418600c40d05605904186806100e4440131b0883c0c000c0203140c0401150 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416757868 1250 416756618 416756629
    0x91503040f020102010e28080403080d09060f0605102106030308060a060206060603040b041a15010809031c020d09050f0f0c0102070b0a0305190c050d110408060601081302 75
    0x14034058848421040182c1c0006400d540c1e003801d01c0c0040b41c0c0310000641e54001c80d9910a18100b0202e0352020524030303a800c005071035010f560406400042c00084c50140340080d40c5c08810160b11558062100c4480704404c00120707540740c45002d1308040a01621081c0d20b210310024060000d60385010003604410381015401c440b4680c0044011880500a0007054505280342e039009052600c0140101d16052010902030700000e0b2008104585080200d0200244643ea00728003a0b80248580002e1814031a0000f184040070070481c00309000e40042000c416011044030420303550800224150202100c1c202c000754408000b500d40641d48000c0309001842c180a50006010440d00820f0400c90025842d0b00b403a140340102c0f0b0555000031010000301001d0402e40c3d0040146041c001080d44c0d4000301d01007004080c58100c94000e05c7c0c200c824400640001c06460001e90350b0004124841c0710118503c80c1d0305c220300452546900010005602d58803491401d0b51110804030502160b00345980400e2 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416759118 1250 416757868 416757871
    0x70e040b03011e0204030219080c01140c01050c0703030e0d020c0f060d0f0b131a04020a020a0c030309060e0a0305070b130b0c010b090c0a09090b06040506030f0115050f03010605091503 81
    0xf29550000380400035440c2540b183c20741144800740d041030031071800000d5603685520401071418031426015101e0b04080810980308615007840084c13100e4945030350500042c2c0d0103a10210046450082814948240000d89028048103a0001c0030040800300c2000201031241800661110040140c074000c4141c50282122060040c00003289688080080080e00040c48000780d03d03107480d0032407c41d4401c00f500043d00c5038003c02d480060781e81c0b040907000c078207000320054041c0260003283c800200301680301d110501180e242da5580c10b00b51031032404112210102c2c0c84050000c0d0305c010400c0c4113102a000043ca50401d0350504409021ba45a58540a94006003c000b00390303559070589920600305120300d241d000e402c00c121f42d440d00640e0f8801600340201ca01034000345664421b814481d6848080458014000090640791a4605120304440b80c14090242c8080d000b07185952024550003003041e01c1342030349440402821030b820702c0c008580a1b000003803a66405130300000400c02200c02c1c8030085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416760368 1250 416759118 416759171
    0x100306020d090c1208030402040b040b1c03020d0215040b0903161a13150b0301230105030d0c020a090c0306170a060605010503061818030c0d0e09070e040b0301 70
    0x129281c18142003099191050f0f9000f00350007135802800c5400600900b0840b6070144c1d0441c0c000581081c1080490b0091100c8c55602e034102c29074141c1c81c0350031240c40700710030080c600c02d034200c41c00e500c10304108903210b0900944079802403d2017400316000410110741e071075001d400d1804507810021649080701200c1c046200a03903d4040007440c9030880001c000c0340784e0380007000300003c081141950b502ca9101003005c90419041e155961550204c80d54290045005810b01112465100300e0002c3c0f00c9820000038440c203071280c40354888600c111801a0040c50003160024421302805103440c05240242c0341c04000c42e400c1507500e00020400c21400d8491903170b040c140e4001801c0310b251610703100c4110341441d04107a0601c02d0a10030080e171030b80c4010341e040d4404a20350b1009040c1d21900348914210008600d0301c4503900001c1491400b4002c005206c01a601c070b281c0c0c400003000c2940b0140245201e081d10200b0004050301a0023515040c9500100c0f5021005400000c105081c54446140030306040c202 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416761618 1250 416760368 416760371
    0x130b03010f0f14120a1502090307080c090c0a03060b13031505041101050d060e0108030a0f050a12090317100603060b2830140f060108100306020d 64
    0x61000c0c81c0800380c0305001d08502800395441c0703402e0824460400307000341d2500f40700e40b280403260142002c09110300000306074058041070303082c1c2034865180043e401420a841c043e1244820010b0314500010f558002e9040c00350032082c1c240c0714004602d40f140d01114410081c16201c1d14006003800100c4010f02a45103503075038085009045103421a07141440c4003440310440c0c180000c1c40040395400800032000c01c000d085c0301c1d6076180e000c41903001a1280307070300080d010381f2450000186004084001d01e1071100e260340d0f0803040b80c8c0c0090166490700904040100184280c03e00625615280c2c0c0180c10490190419071038622414840300292501122800c0e00c40c954039404000c040d4250180701c014080391000f00303042001d0741520030b00348042101090b00a9040800c403121680c00ba81414500c24403c1103001d070305680035031000d503003020708903040544141750030048081b02c4d0201e000700380110410b41d400c0601e03480d54001140d800d000609110b102a49210000001440700d100800c0b010203806030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416762868 1250 416761618 416761621
    0x30c05180d1a091e060402010e091504021c060501080103030e06030c040e0712150b0d200415140f0a03240f050a0e1b0d18080d1d0705010302030408130b03 68
    0x340404c000b41442841d00d40c0c4100140030060380c00c1145207140748000d40b5070301483d5654204080c0c200d0f400b03141c40f5030003900c00292101c8070541d4a00080142c100c8907010701c80180d035400116000e000910001d80047e4a0650458051402c00b0086800031440701d40c0d242803a4031680990f078040402d95018001c40e100d04189003602ca070300d0141d00c0400c0d240c9880040b1051030134441014904c240e01c040f00300c1c00d80e1404404103045808407540001d1034590035841e11075403105840840500700d0b041500220f50800580181d1050031000c50f502d0b0890954104d090402054064028007110f07411607561b100c030040100884d14894040400800e41e4482c1c0350f06140c5044144000b400c0140c00c81c200c203141705810003d8665440281e941c1500841074201c1d959101500b145000b06046086801140c600390400f03401e1010400143c51030140e0500e00b000030700100b02d041c0450030440c00c140c20345608500001c2040d58040d50140d54418054110f0620b0000c03545580c84108071036400c6003204440100 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416764118 1250 416762868 416762893
    0x1f18111e1201090c0c0219080f060108011404082d180108060f0d121e0915020a0b0115030204080105010902071407080a0206070311010c0f030c05180d1a09 68
    0x80781c010280d007030b410440d44184090080c0301004400c8041c2c015031600d90b800c000c417054540ba000c01403905105640307000d42c214040740d44600f801e05c2040d1541d03003807034030500402c1421170005d030040da8030131141440c004020f8140f080d10100500e040401ca41c1c0f0f2075485808410b400c00600110342040d803e4503142d900c0200242c0555006007455000f400b075010380c09159254174209903085a00900380d11504e6602e8001281c540002c3e0480120a17120440007210140e08030341c1500030303584c101e100d01c10128080c1d07004a9484842d20000307401c10350754000400c00c801d242e0311181c031801222f1070003525081e01c0b07078281e50a60380280d00c500c4403203600082031420f100030080c0d03c8078071481450152122610340b2100310782d0346640403001b0307201d01c400092900400d4016161958640d0744200240700b5004940f20103003002c118a054400440e08203510f641d030032441070040783c0d483c3d003400b52441e80c104031000500c0312140e45890103c80e8443d0b000301084103030300c0340030302c803071103141ca507002001100d0045 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416765368 1250 416764118 416764147
    0x5030d1a090406050c0c01020a03060512030a270504061e0506030f01150e030604050703150908190e150a03060906050f0405070e12061f18111e 63
    0x30000d85504492000080c0e80d441030369150b08035030841000710301c2c2c1d00d42540011407840741c0ba0b05194190720004c0c1140c43c89801d034001c0400c517102195a884014494030410303840344200080540026031500241508034241d544035004110604003038500300783c50b000490111440c0313402200d801d10081c01050381030b165030001c0c90302401082c0da12900710f007030042a08900300010b000310780c407480c44c685000d41d844d40b090041100c440c0c0c000301203d04078100f6050894940074103010a90b0341c1101543d60801155990240425196000b5446850f0100300c0d0300304243c00c0b0802480400304140301800015940c0c2e902002503202e1008290203554180c90344e00038044409a0b8000420303141801000c10480e035400d41c909140300c200395408191a590f81030100e0303201c644a10b8580d0301152489140e1810507000840c0c41c41100c55401c0400f041620460154220750030b8460701441140c001e40b00000c2c40c07400d030055802d805004c031206040071160b0000503141d000081c40300241a50110b450352100908 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416766618 1250 416765368 416765381
    0x30309010c0f021002090d02040501030b063c030f070b0301062a0602090a090608030a0215060913170d050a0c0306030b07030b060d06030501020318010c0e220905030d 73
    0x12424402281c070840c010103501c0d044d140c0e00f8041c20395808030301a840c1c0d03280c03401c1503512207034004e004000543e10380ca0680c50000c410341d944d5000d4199442100c0c4001001100d03102c000c2c000c0180b804030001d4210540088441440f85544c06000750410700080c1c0380208881409080000760440d160f41c10301c400101036030300c04c41c0045503048070a40603004c8514030f0400a100035400203005a42c0d450080041602040c0b568004140c1c2440e0901c0020841c0000c0007074070340750341b43d0f07800d40e425010340c0300f105000f001b0195025a0f00c854181c002c180c180040e01000380c0c1e0f0520a15007015000c16100015605401c512031038000c46482d0801c0003d112403038420b40d03c3d0070391603090800c843e5095071201020381d00d000300900141030755140c030b00440e0303a107100503140d41c0c03415804180071091700e030301c0c0c0b0a020390810349079190350007080711180c3e8402030306020300b05001603d07540340415110284100b01ea2800110054114511808100c440c90b40305405810700050103180156680d22601e020101210311 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416767868 1250 416766618 416766641
    0x5031f0b210f0402130b030102070218010612060e070f1205100f05011814010507020904060b0a080d020d030506040603050a0b0415113103030c060c090308122703030901 74
    0x30031004020051780c600a0003040c1600801c0001080b21680c1e0100340284913a500196002450305104036175801c00c01c441c1c41c1658081c0d56800399001255400c40c0c180c4e000c6002e4000d141c0070302c0c4001200e05200302042003d042440c42d002001c5060081d1071021200c055400c1105030705402d905004070701c02c3c0141d84000700404e180c00644c41d0011a40d00e02c1194050050f01040c000700b110b40056a80f20b60150742a490b0000c146003c2801c0518201300144204280d4900600c0d036100d0021701030307501164910a507003071a00a0700000c450310310201c0080000814490b807169075684040003240d410131a040759144901c220384164149424240025075000446566207402c0c107034806240c1030f2013416039015024004c200030f10003a000542207085001d0070001511114400000820f0560001c124001c05004410410010f801c0e02021945031246000150541c0c2c0c00b000140141c003520241c09500420080711503140081c83c50020006400b800f401a0b0700b0790001c024811102c400380703c0d500c076001e03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416769118 1250 416767868 416767891
    0x30f01120201020606090c0f0c0106090507110304151803230105060d0f050a0506090d090906050d0b041704091e0905210d230703090305031f0b21 64
    0x40c5960000b507403854002c0c6464000c40704d03a80401d4100304100d040c1d034084503142c14840d0f1103d0075100d03c0c500130300051062050701d60a10000c1004680943ea0343c540001c9110051440c00d03003055545507401c034a00c24100704105000301c11001a16a540e002c0024621494100d24402100d00341d0404041d440e0602c80c40c2645002d0500c6803039036a1000481c0b01c00da00110040503440035040030382c24041d8400c00940300740140401c0001c131446c0402d804040000e2074071001c2c032091f11004807008070303002801a2508010b02176540e0b00400d02048005500500c2454410900e40c192100711143e90050750110111684680e44261001d141e85e0803100700303202803a005c04c40e240ca01d4440e69921040c1e40c68041c0140300709102c5889c401c02e441f0440b04030a10701c6005000d903040400106880098100005007031303150b801c0c0410038aa10a0251094550b09a035a1300c0c2507484803100e0b8551000c1700410f015075083e0f280c0c4001503114450014010b1085e907140c1d4002d00711070441c85221f41d04c000420341607855 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416770368 1250 416769118 416769149
    0x12050105030d0c1406041b0e0709090b040b150a091a0901030510030c140405010602010c08010b090f041505030606030a12121d0d0e040c05040b030604021e030f01 71
    0x3518002490344a190039403800003030f0f14041d030420700c4c048450005400c0c03007400f4910130441801010300380000d00c00059244038501c3c641d00e07002942d000100399409070001e10210b00802081c0e80c00d0300302220308080100000f840c1018840003401014071b540e00404210404204c20080c1500512154002c02c0014a26407040c2c4043c507001d4000e2060000650601d55610080b5414042d245240b40240d5880744e03d0303413040341c0ca03400d8120003d00e00b001c00d6446181000d00124280d03106000f03c0d0103202981d1114400c590812850b00380a8205079101c0380c001c400d00070300311520390340c600640780c1500040404402c0e043c10304040c0b509180d8001d001c40e000340e006007900700c00202c5640b086c8071910030514008000c0c07515514184041d040c0c2c0e4020485403400707d0050b42c9010780100d224101d0344416194414107000c01b50900c81074038019207140000c120305000401c680c00400c07000b19482140103200514054290202c00144058140340c020203d10101c20840031869056109025226620112800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416771618 1250 416770368 416770379
    0x1f0e04060b0306060703030b15180a0806070c050f0304060306090c1107031e0210260105030a0303111917060103050f010915180e060c090a0e0709030c030b07120501 72
    0x1103100243c80c0d030340140c01c00a40d030410326109a0085813010340003454000c003030401148212858220281c41d0014140e0f800c226106490503203289412a403112002c1c080a83c4c0e1410306813007512035a001640d4502402e2102c0200362000d00081000d800d1507180002c01380c4c18000014110761192442e01c00b84404960003842180d03001400e901100d0b44100c501c0001300d01039803800c40c90000680d00035003104202c40c45c160f0b441d404c4240340000b440d0511104d040503003001940814841c080c41050f0705900294800c0e03001c81c0c400d400c40c107179801409003000d1074540c84401882c800e1301c07804102d40c0021340705501886541c0812010741e03005142440c052210f4144a500c86025030018030501130010703600e00316801c0c070902c41e01c40c060040482c8184020580f4904070907001404400110500390700400d800110250f0030705c0240c40c211388028206020560402c95224492800900a00d080c00451440040007518000400000e580714480c0041c4c18244200003400050425445211003420722005118 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416772868 1250 416771618 416771639
    0x60314012310030f0203010b03180a0b180304030b0103050601050306070503101214010f0b190e040f020316092003131104020d090c0f0b0309031e04051f0e0406 70
    0x3941d60080300c003400c041c00c001100f54002c0590b0790300080302500100002500f4040f0b0000f851040038884046e9804040c440c00480d00c0d80d070080b0004242d12007880c08202132010301c41102e10006002000c803441d1685a13200c2020882d0242c1c07045449030310040040c030140c01c040c41059000f43e0700307040c85421401c014108007040503080c06000c1d80d40c2030000c100014080c0c006500504540441c2c0204141101d0740b41c040d02800901031501d006404c61241c21a40003110070301a401c554000c41002c089072a00d5480300b11110120078243d07807500c00d92040500c1c0c1c0f00d82910080082040d03900000780e0031003041c06502081ca140020301e0b000c00040c030030450b907400e1805240f4140d40d0311440900300040d588000500a0003504502e824061030071551100300b1920140340e2042c0c0b0442c0030f0700e00c6107540d1062600380610044490044c1a00709000b80990001c07038504c01004003902802583c00d0039117800c00308115900001000e449048001c0c0541884d0b508a10502c0d000c0d081500c0a1111a003010200e51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416774118 1250 416772868 416772929
    0x11b0906050a0302190e1c02010207030b0604021201090507081513051801060909050c03011104090b1c0f0611032406040306060308031605070210030e0c0a06031401 72
    0xd050000028030540064400da040303510b034581400c05c4034569044154020100c0d1002407500d4003519040451400100001403400002c40d4140e00600c400c0d403d5070fa642c5c00c0700c4405441c2c140c02030f4003071207001c0c1500c030300007181d0b4060100120001901d250200c0000c1207000042d010301a0000049038a10303030340e126080407402d611030101d40840e84d9190700b4a0303045140e00c00444400359510302000800c55042e00d400000d103440c0642c1c1191085100d400170035088a110440910440c4800c2201b005124425080b0000c130502c0180341c030f450104442c0f866005040c844d90b0841d00d6a13400b2219104110b03140c4a09078910705001911400c510b000654481c03010885801400c201c9450040300c1c825039940c1c01118065070340480180032845c2e1f01d00e00602aa041a129030a6800d40b1005e5107003200c0c4120141c404d19500100390b06206c1c5091301c000d85c014496034a0000c1c2c01d0191034a540c0c12134850400440040c0f1080d9400509015006400b41c45110103801a4041c120780741d5100e0f00c030030740002d8800d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416775368 1250 416774118 416774129
    0x7020105030a05100503121b030c0d0f14030a2408061302030708120c100b010e090405240a0605041a040c170a0b04111309020906090306090601030302011b09 69
    0x140c1500d035a0744080c000704c40e544c00a0341c10312400b14a1116551400040c5c0b00b5050701107405000c503103101b2502e0307407240540e42884e0b0840c0e0002c040041700740e20520681041343d0090610b40c24492801c034508406504c1210440803c90302c480613070b01c1540ba40070900b520709150f0308a07108007c0c01d00505a86612014150052400070501c8550035540e040c00300c4002022458111501303082c040c510001660081c200c87d102900880311944034010306801000803101c0d05a44001c0390703001c6041004036886010380241c0f824031500940a649444210041c19203520340c0d4071b144c0c218a011000b07041031700d042d40c100f03c0c080e60420186050300a004001e100072580304840114600a00c00802c940e2103007401c000c10f0031020603000b401480512a4400288100203440501041480c00f94200d02485103480c1d41c03202440b005002c2110f414103502521580721b0041c9160b150800e40e00019117020002d840da05d145130420303401001015024400c55a80070601c4141c8442d188901310050300243c0103201c1c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416776618 1250 416775368 416775371
    0x15050306010e1e06030103060e0c0a0b0307030c03060905070e0a2108090409020603070e030c09040f0b0a020f0408010501050a14150306030c0402070b040302060901020c0705041e0e160b07020105030a 87
    0xc403005040c1100071850303403c0c00030b001d00e42c403581c2d241001d0b80506020b40c5145143c1c0540300312082e0b907081122919090b030700002c0d00c1a00d103850385c440c1180180080d2858600b056541c400104407500c2c1c500409000d0700450752180484440c0740308115aa402d44d511992910341401680103d58050019401d10315800951203904c5041c0d40010502414111800940c0b00358000100110550400401e8154503810360031903001e05403800030310414000c2682c014116503002c14a02d0001280381e005680d0003e20401c0c0907060500c0c4181c5407455030007582040c219030351508010b10140c202072a003840200341205400740c4002e41540840c4881c04605a94000c040000001548944040210690126000d4401c540e40e40b4182441d2100f03403815181100140950b40214542c09014020380e01c0c402d1096001d8080d00d40341404100c000c004600c0488d452140005210103841c68500c075030203048800390080c080341c40b0050003045000c0e00580000135888414048140544d070f01c43c090300da1201101e40b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416777868 1250 416776618 416776639
    0xf0207060c020d08160605010b07111306031506030311030f092812020f011d010320031503070909170d0213090b01021005090a0f032715050306010e 65
    0x41030060045200c080c210700e03400640340c20458103e174544140c45000718020003c6036220001f9045603c05c1400251460301700c60040c00944c0381135001c500c40800c1c50480003c0c010303a41ea82c2c9440703031150504240009a5291000c2091640102d218222070207079802440c54440c030803820a8460140500d058010b03c0c0e040d94492035096a8000c0c0300998007511505035031990364500e44843d405803414100d000d4042c01082da01c9950007160036000755a035004103010010f8030702d4011801802d40c104090301e02c1da143c00380100b81800c280c00542c061500c04160441000544040c10701d00909175210003031035450300075040086a800c0811030a40992289441d5448000c014080f019004009820703c00c4805031303400096140490b440041c03000d0003a0265151784050755007250481d402194030311300c10b81140700e444001810080c200019144241064a200c03100400c5021303940540d440725010182809400b800042c00d03d080c4002e5048070f0346480f6103503150a07400201b03404000500d003401f550f1760f4103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416779118 1250 416777868 416777873
    0x901090203040c1a0d060603050601091a0f0705032a03070b06010909020c060a0f06080604020d02040212070819110d2c070f0803030105060301031202010b0405130506070f0207060c 79
    0x403c200000c040001550303c9409085400e9a07031584241d03401c01c0090319040c00054842d000740074a91240c48161100c20b0501d24001040300700580040242c0e10010042200400e03c0c1c001c000034101c40c9026031f004684860101008803040c80106812215640780304a0b4003028040000032500c0c41e59002041c551240c5a150068605150b0303a00f1a42c084e60020030301903a01100052100d01c034001a5009009295141480004031400d600822801e600040006005418414001842e05101410052400c0c2840f600ca840404060700c3d00d00000f4806801d10030820000c42d82e80903014031490041180080342c000140ea50300c10400303511030281d103461008090301201042c100d100c0c0c490401400c818009101060f03142c8450340600200c0010050300410704203000010f6038140d800140c41f4510316401c50321010008170041c00040704644d203c01801d4040e444500420f030054809000c0c00f1a21480c038130b00036007003071030081098080100a64150480c10f50000c4c3d050111141030400c0c00c0118101e0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416780368 1250 416779118 416779133
    0x3120f0c0b0f041b08101a060f0714190b18030a0512150307060513090c090923150102011b0807350604140115021506090109020304 58
    0x641001e0200224441001090420a100648258811040762060801c480d00402c00c0624074002c0061035804800d116008041c5980501c0d070300d41c601c00000c850007008000240040c3d0080451080c0d10b8800328a650030841da084a010b04500b10102502446844686501702419104805410665140d0206030781e0b900b661910801c2c0e40003a8143d0750340b0441160060010352120134030301000c0f041d07540081e20b5400d200c0c0c00d1100b240e41c010701800300d1078a05001194681c0050074141586580701c0c4000848002030312404d030400310343c0d03114030311510b01c2c0c111103400303d031031504128902100c444030075907154421269080d840f105107a5445600706910300104e0051489041d00c0302e90050b0041a584910b800040725803040060390380e036000c1c01e4070f2031940e03034924010340c80480c100240900d034064400d8482c030b4040d580010083d10004429015441100300b0070720a9010420b050102c803150304083d6814402d100e42180c000801591908001011031803c01051003001e03011036001c808a030030820354 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416781618 1250 416780368 416780387
    0x408030f070e03011b020c01050423010207231c0b0601110309091e060a060e04200304151a0a090b0d0c0305030a1e1e03020903071202040b030703120f 66
    0x43d0003007141310f19121848591021000110340903100340342d4a08020342c415004c441c01c0e036881d41c145407200a001442c0800303460300c072210b440c1540034030980031403843c0b05040c0fa04201441010711140032944082030100c10840440240d0309004085000000708909084140c0c21800a10707000050003103101c0d4581c254044d4080c0584d1040c40d806c14049809000f05900300507804200d84120b264a81e0010007004041c14416940402c901000c4c003030b40c41c40c299124500450307044540f14416080c200c00450668421541180c0d601900b0350904030340c91581c481c8201a0288100c46c0450755011000a04000200e2055021154564a5a010903151400c01d001101d0344070180241541d102e14200d41c803504400a5400002e00325210040e0402e002c2d541c2418680071a22807102803458408624500340100c1c050b1400d06800304203a1186840402201004003120001c00b410300c0c40c0c43c410002502c5c3c158404a200380c0c4807040500229403000209100e0b800c007424030740b842e00c40f6000c068440454 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416782868 1250 416781618 416781647
    0x5010203090f13180c080613060c1b080d0f0c0219060608010c09060e3a0506090304050a050303090f0613080102030115080901090b010524070302010c0807080408030f07 74
    0x1844080000b0300e8a15a41e008018498101c0100b2141c86e40070450340ca540c00c999010b041200c01a42901003003150780424420701607440c01c0c8209400e00e1401c10074414070740008843c2c410300000c4101606075030f485000700d544002c5030140121a0b203c80d0003591203040400d004c4070700c1510920030003005030944c005801003586000a2102c8210b2a03000f07810b0f40b01c54410f040c007140d541104280b8618180c00000466550701011174103144e01c2c4404018545a4000043e001c404840c0940000c140100b045501c5544645c0c02980c6d51428801800811485540024001d80c0700380000002942c1d4203c1043d85204160340c1c0f01d44604441000c0c0d010101c499010b2412948004001700301d0449120381c0441808840d100d4540039114000350a080704c19201010b03000b9401c070341c01841240b8211160142c2c3c29504e0f1008200d0300040d207420003056001080440140c2c4d510401403c400c0c1e00080c4050f440845401c1c190304524150300c0e4021544001403035047c42c5000900002d407024001c0004580401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416784118 1250 416782868 416782871
    0x90504090c0602070b0f03152737180c0f0620070608270a14070602030301050d0804030615030215091e0d080a0906090b0405010203090f13 61
    0x10807800c294161480302e002d41c01c018000c1c010042404101e08084410360120710610a25554541ca0b8200c231000081c85190342c800d41120294a68510b50001c1135000c040341c0030300701716606100c1000209250804546460031484a40380c0c80403802c08007580005003814100031400c0561440b02440c0b01c80d100c1c000528405042901095090030400240d094400617200c4a11042c0c1c00840c0340020b00c6e1009924506900403503043c0030180c8034038201078104c0e80092108040031410100e0b07007040c00080d82001039550104240800b03000006200e081d0303a40032400a801a2400d00100035140d100c140103032030182c3c034070712401350411411008440046400c4002004400c941c081d550441c03448038030050748501240101000d0400503202140d180e403a000b483c039a2a00113600300c161782440503c003440d900665074100030000c20709401c001d05c1d500600b9985c247e012801c1400103046428590480800c000b411f201c24005a6000022200181822100d81c5500b0f5000000102d6017140e04607115100d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416785368 1250 416784118 416784131
    0x13b090304030212030a09062c060d020d02071209050108040b0c2502031005070c0204050c0c0a081c050c070b04111c050609060417070302010e06101e030b0703020a090504 75
    0x542c4d010003d84844c180710794030681c0d4035070b4405085803e01da00008090241c03402803c4d03840404410050982d1a201c043c280034141a080306a9a0403030300040854100c00d90005041c0041000000c410320311101c0710b0402d0000700d420940002e000b0340c00184010301e50180d10010400c4c0e80c402e403080d5141c3c003074810040361011940c504129449107114130201e00078429035440d0520f000b002c0c01402d120761200c5e80e400c40a9440350f02000080e200140019004001c02c0000502081090001c82c00c1c1a004040b1143c1c0c8001d400c15014003102524a080c064130f252609006104500782c04945003079422111107007a545aa007480c150404541d034080d035010700404c4140302e4100300000a41d00c02402101505c4c001d41d2070000ca10746414003114002c201d24102403c0000f088250b02c060300e03409000740b000007064202c040907240760083c2514000100c034404607041100d82d440303070441500b090b800071291051601c0e41c2e803100042c1c2030261250081c107401080340e002851041c0d5074440180030080c01413008 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416786618 1250 416785368 416785399
    0x602070615060f020615060d0b0619080108060403050301150e030f060109060b0309030a14160813050d0302280215030106171308070201170906013b0903040302 70
    0x80032514400e400220b90310440c00e180e903500104100f80f00742d001c01d031b585580c94400001c000b1141c0c80303049003040055a03005c0490482e10340e90060105100384511f4401d0400103607402511030340050b8003140c0640d02010030440000c5e44942640c0c112800880052790071030745000300391600d50319500455014402e0881250303008030001178043c1251240542000000e494450f0595070b4401201d50f03903903543c000c10a80040c180b1402031004039031010700850707003441416884c04074050342c5244141d41441c0041620401c008483c4081402400708440400621480d42d602944401803403002821210b05c80d450016040c640380c0c0c56540c1240d0047c03a6000081d0302511100c1c040d0402c2c0030b03002c0000c04038420204130030380a110250013562680c241009009040d0745d05c4c03d0700c0d4440b500803810020640049d90401c400101010b000d04400341c00b8007082d60401c0ca008030007ca0700f45043d4048004140c0607480006c0101c03da00c40040d555200060340d65036004400d20314441e81d071009401038a0600c030740c0807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416787868 1250 416786618 416786651
    0x702070b0a1707031803120e03042d0b0414040c05210405100906091e08270916030e0c0f12120307050c0d1817010608010c0905090c030c0f0706020706 66
    0x8034607a147c00410000c030403114210742c0c0e4000c44c020301c1e245240da94004e1403c0005030a0001c00303210551181454142c0720303002d2001359005540420342850b14141600000d1919008801c400e401601d00702d410808061700414005042c441031000c06020350010409000e824045203803045980001800354a480c2c4c54840004c0121039000c0d20700f4500d1049946c00544005001d18400d504170400300c3c14150910150341c081e00c20350b0244081d494240c01000d940c2d80317805c00700920912544403030720041100e1600160684d024403029003120340088496144641e81e6210031104040140c0d04880c3e89108822a40d2a18a000d038507522404004002c00146981c400d000384851102101580c220980e00b040940d452465840700c00303e4410742d600d05106409100c11500b0b00d02c00640d002091150f41c401180c0d0031120710118410008116840520079824a9400c10350485121503441e031440c5001040342e0001d000b0061061205800041d006052204680541d005541c118ac003c000070b5160100c0480d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416789118 1250 416787868 416787887
    0x10203010609031a0411130b04050408040e150604090b0402251a090a03030203070c0c030b010602070803090f0405091f06030309080109030c1b0f08060702070b0a1707031803 76
    0x11003039600b240f01e10340c0b88002000c01c4c5000d260311241c0241d01c004244100300303a401d46000310000d103070b80d5441c04154a0303486000300303409a0f0144044543c4c95080101c90012070500514090703160590001540175920303404129011191182400520201f03c03c000070064400c500d2401e40d0700040d0300ea403403482d0307440c03105c5180340610410304180c6560030382c0442030051030100c07a9904c4035001b04d6060350100c1e01a40040d903100b0141d01c4e0803465036006a640c2c442e4100c0c1a001a00c100071140d005100054041162038043c04808005604045103000050401c200500205014a441d01c011401c644010820540240f04242903d0020000941000010150741c8419400143d406400050039101032041e090901d8041d0780f001070071a13541c0c54a042c80300d0080401c280340d00721124005491082d1040200141a0247c09070000d4101140000d1502039103401414a10300c04008518107640c204a80c1c2158900c0c520220056070748610701a00108513803a41150010302c120b9100c810160f01c80740742c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416790368 1250 416789118 416789123
    0x1005090118080d090c0509070201140117030f0a0306150309030905090421090902070f26030a11040b1c2d0209190806040b0a050403050a1b020301020301060903 70
    0x801840301c000410031200600804058015082000b03d000c0c50368150f00308012060150b0390305040581d965000c5091010700300c0d041c00050355610401e004801c03040d01c510340100b4007101401b405d6590800003c1d01d074410b420300040e00301d40010700c4841142c02500324078001c10101c624590400c40050000c0c01500080301c048000602c1c148012485181c008400c0303004d40c0e081151343c2d810306801d019202d01452040001c00505c100241d000031301141a00040400710310030300840c0180d078250316010720b0380c1e00ca01081d5a684800701a1002c005549d11040c0e90340301c0f42e095000706180070201c40c040f00c2c6208540113070030079060005690305c200c015440d42d029100d01140c8100b11320450840c0b40c0f200b81a11031104040054600c601c100031040d1900900714026005110302a0310300354448081c0c220020b944005141d4202000b04020700c8203100403076900c8032010302d0038009490b099800030914814005820103025022071a071018a040156505050798090021940e95071507000c060100310092004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416791618 1250 416790368 416790371
    0xa0e070908010c021f02090d0602030112051203010509070807210e15010b043501060602060c0f07030305042303031501030b0607020f0114070309060807021605010f1110050901 77
    0x2c40c43c0d50b440080c2e03040c0b07218101c0f01c1105010507502d0b600b0000c2c0d48400c4d078203580310642c0c600b0007010880c42e100941c000d0034816120350030201d451403c0c5040c807c1e41004102802e5081c0300400031070f124800d500d6031140041c5410042503840c0c100c2982c011003c4100300040440922248040590540c000e81a0f6443d14003141d030051510107010701e10304d609006024650300309000030010b4001ca02004280700311080f40740405080c3c6c9000741c110a001d030303200c0c00e24643e44a207010030940b601840110741104034140402d242001d40540520240b09417400101099a9107000070700b40703d220400c0310210f03400010f18051700b1a0b0b410800f80e490b041642c0320340311038150103449000c541c080c0c40f5034121001d003e01418202007a50b003c01c01926801d842c150305100d048030410413080440ca0051200c0c5200b6201c081345241880c0300200405401006e1109541c02031405000d014115908001210400d00e0111004480504104d80c15411850f204095101d24455203051182c00e030821807103064040d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416792868 1250 416791618 416791631
    0x613060501150f11100f0204090509030403030903020904060209030307050606040605010c0b180f03130303030b010e060d0b1c051507030903090e040503040b0a050702120d020d0e0a0e07090801 84
    0x84400c0050010a40320011421000e40030715500d0007810480c0f22440070000b40c5003040c00705105c0c0401e81d010960404291540003500b40134064880c86015085068a8011800c0074115030b0b02400a0f05070340006881070011100282c10040540c0407182403d20250650f0f845c1c8001d031a00e0b036910034043e40c0c1c2501c030b0343c00e0400100b21540b29081100310f0036000441d10b50140c580c2d00009030881d00407025100f09014914803082c41210400041401c98184503500810a165003002000c8441000da01da040101c804964121540c230070058076100059010300188080c10a0000394010131428a00018042081c0f0307100c05001001c590100d0b208220703017000d5040d6441c44001c8080311022a001008580032007014482031001880090380b02c0d04c5101140e01c0c21340c4810f0b4038001a003100383ea00001400c0020880118144050103041d4075155000400a078411900040d44501e000b8a4220410805030321b20f580c25502c0c040104000c1c00310455000d82400d000034001e281d041c15006440b85582001d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416794118 1250 416792868 416792879
    0x1d090f0120071109100806070309020a05010302030a140108100e01180f0510050406270b15060415051b03040302091305030c0715020d020304080316080c0613060501 72
    0x3800720300906404100311403150a05a05500c2e04404003d446a0803503558558550b01c40400040c0626040d41074048164601030f210303071600400401007810903042c030310300c01d0050f00e5604803401946d90900b0f0158603585e908001c00010019040e0000080340e0801c0000b031051008130300200c11411b402c00038026035400c01c0e1028240d0340d5a20114144210034610310740440c002800c400c401d280304d1002d484003140d00c000980700707803141a1400d680b4240c0d1204a1450681c10881c1991240050030748000b55030003685034494403480c014281032046030810000602651780100300c0d8040c20804080035003020b0181001000364015010601501d552031851402500c2f000050724110b0ba4020701d8008945d13201903142c00c5034401000200c515100506c10740c51400c40502c04c1c540900240582c50b400e100e80d5490080ca001110070a21741035400400050100300c2020084070901169046400704001207843e00810034400d2078842140c0d40a14000c3c0701c1c0a28005400001407806440c00381710598131003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416795368 1250 416794118 416794121
    0x4081603020d0204020a050f0708091e100305090c120606010305010e1504201206150c03030a0209031603061a061602040902040b0d0c0513060e011e1d090f01 69
    0x901010b5800114030b00018010301e003a800400c064031062500c5414554140310451050308020000c94084c0008030b8081007506225818441005200414110b20090440443d400c20320075a070240c109074551001404503074042011510800c8042d05a405c4130030414000354980a094403680c0c00681800d00004816200000e9103001d40c81340400910f84400301c0081000800030060f20301440484001c1d01000d8440500103400640540c5031816420f01d41001044030561001e80e80c928440400c3c0060100c0321030002c1680d521002001c03005176030301e40c8000040d01d0844600054541c00074108004030400603140c1044031103101c95486140203000c2d81082101c43c3c003691200c12010300842d0701a00152030141c000e0a000b41c001b03000018000c004c0c0d00450000100780300151b64990b5081d0040141d801c0ca003034240c807800c0d642d0078204102c0f8207091030304001d18010f01c28281800080712a602ca00c4030000801c0000f09940c2c2c0004044400d90280342c2c074003010071650780090340a1f00c0303070410030040f06 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416796618 1250 416795368 416795413
    0x1d01060c02150a0201060e01090c03050106020f07090e0f06070906020c100806040b040906020a02010e0609010204080604030c06110301180e070b0a0311041205280302071208091003020408 82
    0x924005089401480030b2090f80c000c440780c0e004540d01c034400014502140c80101d8045c1c5403484000c00c0c60170308100080c082d1f07901a40b09004641c00304007500700350200440d600e0207403500907d0202c5c501c49040807103841c10342d5600803d155030142c01c0500441c2034014980e00c04480d240d4080d00c180b00169420048220058245103004c00e0003180004d005140940c803060020500600001d0030015a8442104036080002042c02503955443d00e18031082c0f00b0040d0750b074031035a04002035241600348882e003a29a00040e10080520960b01004001c0041c030390466210aa6101c3c3c2c1542c40351381d60304c00000340b05003913071f00001030919104541d2041900802c60409903500d4000551400308400400c500400c5802da50081c0c1c08424400810141e040c0341556503c64010401007a00740c2c030082c010150040044159055004d8210303100c2c00003500441d0381e41c100d802d00c00e401040c002c07090800c0c500728443c0c043c440e640000301e0710414003600d405074080c005403102c810456030540070405000640085 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416797868 1250 416796618 416796623
    0x90b0106050a0503160c050a0303020c072102040207050a0615030209130c060e03150901020d1410140a120506091006050d020409080405100306050f0a27151d01060c 72
    0x10000554014029079120178406981c3c80d10421102950b2039050074402902012070002e41c0010b540c0183c88002c1000c0c0c0c0140020f0040d840c030140d200516003410058046009002f5500850440c040c48028000c1c00744441d003100342401590811340a45501d41041d0004030b00c80c4c141c42003c86e141000421481c1c8443c4c1d404024203290605141b002e035154014011140d40c144143c5000204030038503500d405000344842030001d82c0340c3d00120510300c1641c0c0005400c555501c151410450403440b1010000221840c0b04584200d030b94164010603824149504600d211450362040881080780020300341d0320640210090320007281080145000380c411718070034290700800206900000d403510754481e0300490f1248031890700d030a945c1d80c04030301301009410160f0082030b921074042049041c8001840c00307503601214031504039401c2030030441080d4900385005002015001e6034070641a041d40c0320745204040d20007080c2029a030388400030395055104a0811003032440000015030340e40590202123607503a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416799118 1250 416797868 416797877
    0x307140a031a0601090605160f2909061602031c1112040303050c0a02120d0e0f060a0e060601090b0c070b18040f0c050a26010909020301201b100e01090b0106050a 71
    0x3c03503111190380101102060750b00d0418207081120314840e0001c03101d0001d181030100c50ad9890320300134550a00c1c800602000d604141e405056000303503808400c692241ca000c44900081c60305511440c001000101100c0d903402400241c5001c0310a4003103441031040d03200381d41c00d01c0141d8446680101d203000700341596015030300c11070382444540da40c04040e100015500f00c00052410465071407501d402d406800008003600402c003070100540c400c2c0944813800400000520043c02c20700c000900da01994030843c082e160300401c814100c1302040c040c1ca801454482d094540795081e1000c180079103810800c0051190b85000c02d1208501c0c50740c0141e428440c40c0c0c0c0c0305c2c107041040101003030b01d441000c12805c1d01c2c5480307200400c0e80e6440003045d01c41e0181c2034036000003602902e07501c18542103900a0f00e00411001d0520300c02848030386c4080c00c86009041040140a405050318980344c03800305a03c1308a1141420540428022201540648811340c02040b54184690344c82d1000e580900c5501820070004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416800368 1250 416799118 416799157
    0x10f060305120d111303140601031a0c160501050106033b030c06010b0d0507020318120c09040b0901050c0408030901031a0303070c081b0307140a031a0601090605 71
    0x10400c40542084042c0d9003012822407991300c08100b040d070250105100e0f0040c0c0c1c400500a1000c40c01d081922000c40c0b000402035541940c0381d10103401c074501c04081c6071321b0014001601c041805416134201d50002580ba0700c024a2501d0030a019080c240540030010b49001300c0c2507505501040840302c209644803144500844c038210f41c100b042204c0d040010b85100410440789040d104000c0b03580200405181d203501c0c0d134012027180055600181c6071601b1903000380700480b6100b01250b500c580d441c4040b18050700807800740c1707a07042c1068409402c041e401502c50b0304004c18881a0804a8812801100200705681c0c1d040205c50990085022306200f40d1b105105040c595406a404102003030114a1040706030040e44000034a960b00c04241110305800c130136000c10544100b000042c070145001102d1105901d003d00100341e8640c02c03440784030698000140c50189a885031888a8041d54004101100c1c01130030300000541102d003907604500184001c800000e105204106841c00b00c03000c0707181030106 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416801618 1250 416800368 416800393
    0x10e0d080a150f0f09050711060f180f1f05010f030305090604030209070e030d110a150b10050a1106042001030b100201200a320706020705010f060305 66
    0xc001000d01c0b1040715258a001040b050482038541c0020700c046043ca0780e016090002400c10f889000c2c0c50300040c0322680c03031120b0480a000c100660f00824000301a141c5541d4403100759005260400e80643c03d00031445480301c2c120011480f00b0008504003d14400c1310b9042408204480c001d1007180800003c2d90030070b00010b4400c100900c01400024402c40c1000e4032600068040e94003952807401040141196504d14241031219080740c07031141c01d2000300d080e0259031240c1c0300c401c07003038000b428003008070503a07003c06c01560320805280c82d02400d111002600c1310401341096010ba26000c01103142c01c0000c80164000040c681e01c21070780701c0d80d0060302c090040311074080780c08c00381000d134141a180c0300300240c2502d5541c014403440a0550000c80c00c0b00070f0401c82c5405c42c03011254802128400c000b82003c0310f030051002d900d01614811a00d1184c00f42c01401440800e03000c0304e02084410016000f0706000854024040c041d00410007005003070641e4994008075044c07840002c026421907072200c0b00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416802868 1250 416801618 416801621
    0x8100e0f04060204080d0c031b20030708070b03060a24032d0b1c020d030818240a0504020a06120617030c07210b15040c030608010e0d080a 61
    0x8000348900d101508045e00c96172a01d041105642051001038a40d0300304406041d880041034131510b640000010074050b0075280c000b8401c0020303184c5d5500c6000b640c00c1c0307002ca072410410f1400508034081685da400e0749403000402d00c0d60040e00c0c0c2610812030b075040845c0001c02150500c0c03400c2c4c51004220f200c080d204d0000e9000e002c0c1c000f48500144400020300c2405000c0c40c5200c4403600d4540800540c058074402007141c00a5044281051408108a180e00580310905024200d5416060541c2507a9904034501500d00700b00783e03190464000d040e84070601d03600c050710024545a940d418038034181d0f038ae607142000302c40b401c80c0c01035403100c00c0300030070403c45000b29400d5510703120031080416030035184d0b21260441034122450a031036a00000f6465100d0b40248443c0c0050030030900d500119034960142100500d5000c01d02030150f421210110310a002290490b43c8109000343c000d04c107110040038003a005081521aa0840e17509050a440c0c90240c046569450000d99440e140903a4941b07299410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416804118 1250 416802868 416802871
    0x6180108061f0308180111031213050f150f010608060f0111071e031209121101031b0807030b010503010f0303110708030f03100504020301120807020d080310050108100e0f 75
    0x64400b41c0718020010803000e800030180141003420552612860000040000c3c42056160805400500c0541c1902d5841c4825503000100300c1c281e803480c030741c590401b0381c00c040d140380d5401e040b84a651070a0603130110050985200301a80601d01c0c4540ea40e1b480d01743c0d540542150b100303510501459443c074042d0300400c3c01ca00d0525856044402c400d84648213848108081401c902070581401e80c10030800455228129541e455454201c02140ca0090942c04818031518000c00c95100d100c41454140d210741d005e0050721024809880c0d03a02801c8402038464502a140350340020304051410203654000c50417641211000c50817580b42d5491034808417005c8030b6001000706113000303001c400105040d080028010307455040800581e01e080c4102120f0340c0d9010b039400540650300600040002d00c00320030107020310355040b014903655401c4a20000300c002018000c001d148200c0030090001d84209406210b09881c0300383c03502d1009407141108180d04110600c1a850206650000504540c103141e0160703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416805368 1250 416804118 416804161
    0x11030f2221170a120915230c120c0c0a0803010b040e07030606050a11070f060f020d0f020d14070f08030a0b04050c03071412090312070e0d0803060d0204020f030618010806 75
    0x440300406c2d001c8000c02c0c3c46045090315a40001c0c07650150b9000404c0625680045601d004d41b40b820a9940180d616004020850f0204200218840210003c184104d001d1282e100309040d65075a100c60150581d40c005001e0112043c81e8070700082e09181c040c0c8107a1040e82c06540b5040c2c00c00190010484080c1da02090104c6130340201c100c0041c840400c100000054076031034561201811901200030328081e01c0512110400c82c0307681c1d070007818a0f0041080070701110075280c14203016071803d40d901040e200312900201101c029002078024408000007444c042c0807030482c00c0c010368010401300030503900c0585500508082c20008030703403c0c60041081100481c03044035011305050810360014290803048841500c25003001402c3c02014002a6020740d101c0043c0c105203000001d5640030420381c19017010000e101c101d00002040f866540c02105842c1c96900900c25940ca10000380340c00d800d9001558914044d105a19840f04031002110440c1e050314180f00080141d565803c01014420402381600c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416806618 1250 416805368 416805383
    0x40f11030a0501020c0d0201390e1306050a0824090c061227030714010b030307031806080f070c030309020a0303020c0111030f2221170a1209 62
    0x803000200300f80040c10001c49000c2c0504851094000b000e0b0965001e00c40740e000c071801c1c0d1074409801485441d40012681c10101c0307869032840941c1e1058501c0040110929445040c3c000303050a04442f54001c5c606495040d0f0780309502554a03644070307a9400c01402e4004100c051607210599000c2c83c1007045030320005940803a800c00700660f01103a40303507200c001440c51528035803041143d004004149480103007041c0851962900caa40c482e15281e01500000500c030b50701e0140c101c0704450094200f00c1a42c44010141c0c5c2d500d407a10b10740681501101e16104220f003000103800504580903413901889400c44005072132a84c0d6814100312900041600120309040c3d81e0021803000d62511085030340070f10300c6038009100400222001400e044243c0c05c20700f285610401c200d00703460341c140098450b4500e0307600d410a04041030041102c0020040c4e00001c52040941206140300503004070342e5444a4085c00703015152036005800044144581c1d0021404224200e0b200304550240ea03100e008124003038243c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416807868 1250 416806618 416806633
    0x405060c0a08030705120f01060c0204021803060a0c1b050717030d021908060d1e0f1a18070e06060a12110a1205010510110a1a1905040f1103 62
    0x807031a00343c2d0026107110b000a1008644144c040c20740b00d1804c0e81040c2e1510340e48841d589040d000400c0d8180e100002801250085040880942c40c107844511840000303040d07801c50b141c601048002004804528400508040c01d00b8105001906907090f6950704a40649415420506010051145402c400700c0e5071108022001c40780c800c500c05050580e54020a625050301c2000005100084c090041c5109114004001001a05102c1091103840316104400882c1402d414400c010f107101b4072014007034602c2114400c8640800c00c10540c030940881c1420030a00e10400149959003c2a0248242911131030010401c10314050028155a114514042c55111024500304060324803018102036010300200b00310860640040c031610a0042c90b10b8100702e592b26005c000340801040c0049c8070240140030b106101c0030300341030100005c4990450f40c94642e01000d00c50401d000141160444401d1010700e0062050908030b0081e0b81c051038010300301c01138081d010748510864100204856506102e5080c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416809118 1250 416807868 416807873
    0x40c0b0706061802031e060a030f060605030f0a0c21060e0706090605120a0c26060108060d2301021b030405130e030a0f030626070b030c0405060c0a 65
    0x9000381051440349001260b414500561280c00307201c803105400586005104020100c04104070501e014100240b00720003130340320000400d9020749940c1003d4030074584040207409002d0550002c0e030849409070229000803000c21941501c2c3c168140c07005040100a00d000c100328804003d120480c07016000903031004481660340d00f0115150b024232000282c000d200d04020f281d80002c4024010f00080c00c02c103181010800c482000a030000701094021569140120007051003101082c0b0b05482c00c81007103500480580e600b0b80b00344012580340303001582280c00070300e181c14070100c42000e2a40c032854081c0030045001070b85903102400c00381c80b40c0070742d4280f0580f00042c440080c4000c101c2c0301a005503545a060605114148440481c004d20844c1002c44c3d40e006104000100d4904600d0740c034220320610141401100586401e9001e541c069000400024400186034660464025910b0844904031f64503c801905808210303003041c6c009200b4072082240f810400000c0c0840070896040c0d40a0b461617a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416810368 1250 416809118 416809139
    0x190e1305061503151e070203030603071a04260705040c12091b1d0a180201120e1f0f0506011e1403011e0f05130b060714100b09060d0b040c 61
    0x45918030248113200009121041c01d0056160b0011b2062024500c0c5140500210b90356074103d100f01102542140d0304031102610240548015008070b03401030103d144044c00752080119805800806c0e40215640050f0500c1d00d4031881d01c1c0611640c407060650280004800d0041040c6501038400b40c80c50f5040d14000c81e441c2041c1e8020b0058032404c4c0114a038892008602c162000300b071a400146850348450074500e607090070340d251a509180610880c019403000740007a0040045082c8140709800101d00312680c5d0140052016817503510400c501b0b901070043d4021307280283d0b0040e02250660185900d02c258206210700c40e26a11700301040241048400818558030076071000d000340c81c0c5140302d02501842c2c125200010000b25200b40071071400e00c0c001640072014164204901076885030351032205c2d1641016160b103150800108816904c0c1c48450b030340c8965128800b00340700c51509461843c0d921300500020700500d07010b04001000c1500c1d40d07030074801045c054411369841522220004006008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416811618 1250 416810368 416810371
    0xf1401021b061806010f0e130501090308150f1f140301080f0c060c030f03070c0204020334021f090c0f030201090e2e05190e130506150315 61
    0x1400003031100b4a0f02010155188901040e400c00d1500000b00401a241d102c04030750041d01d002100707244850700c811302c10003c46001841c2c018400e50034120514281500540d60354400c3c80b1281c0a010a101900704103d1807035403114403030354005944e0080403000c1c1100b0360310400d140d14604000720810300c440c802c00d03045d41091780080010b60100042400117a42072040d8a21180300b51350075410001e52020041c0c81e40107034100300d18611030100c00540300510400d000088a071300a0411540da041846050305032002c420402c010440c3c400b00030035400c80b20480c0307081b8001e8559014040440c058038040d10001d204800c01b50140d03885040c4400820243c1c03d2120003850110720000c1224603510002d0401101039014030462400c90b03080140306a98814070386004800e416284c191025240c40c00955604160080e68000222110002050303903c6404d10043e00c4464460000c0c2d5034992484001132001c4031001041c9804c040d000c114104480e01031031034084001000d4400290b07807459808a00c200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416812868 1250 416811618 416811667
    0xf020714010b04050421140c061005011404060c080c0d090305010b090112020909011506020102070201020c030106140603090a0b040f1b030c0b0706061a070c09090f140102 75
    0x29240584034554400d20602c0004a0251028803007803900e0b45508282c1c40c03850680c405101c005580c0089000e05c80c2c9483d41c0e082d040c4d00313a001d44805424030b1032035a03103408565a0307000300c40030352012400d980100c819602d240c4c4041640c51803d810804115011100c010044034071090034812000e10f00740603c06406481c02581e122a6041c1c80d6003001800c2d200d01c104450f02600d10035005106c0303507004d5a424110140c05403031443c0252601d00d08180100b10f40c0030a8482900d46810109030240d040d0010020607000364212461115407104040c22248130b41305000c01c41d40c6107800007a0383d042030b1001d103138400840010354240f070301c19031101c2c0200034048070708449801e8400003040070816810960320462801c2e040e001c0507181559650025402c030360080c480b010b580030403d1010008160444e034050708a504a96510884040c182d5146803c440d5044a0811a0302400306804150380708080c02c180d04058480700c642c0031138613036001c2d61110700c118200300d540801ca40c09071151043c03480d611615 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416814118 1250 416812868 416812883
    0x901020f0d021612020306010302011d03010c09081014161403091e0c010c080d09050a11010801240507032616050703141803060a05011e030f0b04060f0207 68
    0xc1d400f014500c01c11050700030250544d140c02d0b0308005620001401d505586d03080c06c0460700d0407a40f0282c03900c0800c1d10440720364150b003800440c0050795486100c8604481030081203445c030720304140700321080c0c0d5880404181d903c0181c030000391000e1032168002071115983d040045d00f4018416060040d0b6008441d89011580b100c003100f003000e80c1d02c403a2500c918124801410700744ca503540008041c00600c0b0005401e1031004100011003101d83d5210440003a40a412200b50354030724a0480c04c8a00780310390032808106400c1c00000d03c47c1510030b8024490415070900a54000c520100ba1802d070810310f000e601300318000d203040054880c80c040c078000c0c6503040201d680c1d0506c2c0025500d94068040403130001000304c240030050029401c0300c2c49504c800c1442c4121500c40000c54150707401010b2450f00b0031b6051040c1c4044c080c0c1e0f2440340d40030606862054081503901d4a02c10444031a828240c031000b4000f0fa40044c3c0580415400714000d42c2189c803070100030030003001f01d5441c5003c0c1d03041280261000d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416815368 1250 416814118 416814133
    0x411070c0e0f01050d020f04051015080105030f01150e09120d15210b04020d060908031602010606140a02100e1e01051302060a030207020402070b070e0a0510050901020f0d02 76
    0xc42e0340003034203004141c100c1d1103010040d01c4c1d0b03021403581442010b4140c01359031190701095100603643d484902600d2448020b1030f1482020340010038001d001c1c8a0030b4004d003c1d640303a010b03450728180a102028004220b503020500d1910404d14011000100b8540d21400382641781800c100080004040c420b0880001055015149440720414005a4021082402502d09400d00c8041548204860540080580010b9512030010988410703045800910440c45e001040042001c2c04001e14040c140101e80300c0c00702c8000103010303400c0b149240031780c4010401d5505002d0039426031600038946818580b040d54200c43c056250482a14110301c4014195001030f44d1440c075001030380703070440f808050a1000380404d0030124149070352002c03402406409400d0020300c429585000750104c8100c0369002e0011555081da0342480b07083d520301558100005903907443c0c6080545410034400042e900014240c0010302040c40c0166040c0c3d1080255034190b0044a4001d048004140903c1c40d80a40a0b00900403c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416816618 1250 416815368 416815381
    0x215091e0108090d080109020708090306040501050f1b1206030a02042d291804200108090c0105090a0302090c070501180c03021003020d020309010c080a0c0507020411070c0e 76
    0x1910300501e002070f9a0302481e500c240300c170fa0040c840750440e1141d01005a594091b42071840c018464507030130715010b2254206000410005500c10303072040d40403114283c00c030344808000c01000410001c140d884494103206411842800440c0b103034000000a04445d81d80c00d05501140c02e1b0780244018032030740c06d0300b4220006980303041042699000f16940c010042608105404810f01c124001c9650744004040035490094441e2070081d40120ba800495149074505031514a480303003030f04043c0ea48071a100000f16121940030300003a03402144040b016080b82203980c4011030300d540081992550010031288004096160b4440543c02100707180503050365034180341007903401d5400c04906d003061240d07401c00304c0010a45000b00d0000b039a50455406242d40c910200c00c8004c0e001e1203401c55840d03480001400b000d004150b000340d0700c2020940b548419651020700c0341c002c0b1070041c1a07980c0410304c104596401072800d42c0c04182640d402e0500c0c5824480c15071240e14010b2801d82105459a2a05040c80318 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416817868 1250 416816618 416816627
    0x11160b0a0c110a0f0f0b09010f06060512040212280606060e06040b07030207090e0d021011040905040503070b0f0106020c0303090117060a030203100b040b090903070215091e01 77
    0x41038101c07810b08402504a8102940da0f49030a510040d00860004d1208410000c6041d200b03100306400c219104140d0412000c0e10380200407507201516081e107840000903200d400ba0301030764022013040c2200c070300540d01c640902001410740b503600031450050802104080e2504485011010945070380710300c982c00a0f1038080d0440b41150002c505001d081c003004100d45c0e66030000c84007658226040151500302500d0103030301d000c1198104290081c00e084040030203c600080c98210f2204950071a403901e81c8012210080710741c1350381d03520780503841040180b0001c40740341c0066810602c550201c0f8035203038050b11403a98040c000d950707001d1046040e500420040b5410800401c02c0a411000f031031a03e00407000103401c0c168101d40da070b10700d40c0b981c2e0005261940d50300414402160040c0c00d490405200001100043c02101500c9202d00d00c0c0c072080c60001e0801d0703900b092188410300f00841c45c1c00103130380030800c03501d5610900c9003940c030303080003d0744848e142c4901d509016041114240100f0601800161 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416819118 1250 416817868 416817881
    0xa03080a0c031115010308071a070e1806100f090806070e030d08090c0f310f05101a0403060614040b03061009180f050303010503072711160b0a 63
    0x421940407034082c18844004441245c11070358000e10032a9a08540e10340860701c0b14020b402010076050540c1006080c58010044508a11003120b21170242d4140c0e10004000040540301c442d0400341001106080030701410041d60000404e0410400c00d0790b43c0c0803d0f5244c510212207020028245550402c040d041c01c004400c0b03c80000c1c00e043c14289030405040741e0381c04080310000d04c01d00c1c07102245081a250202d00713407424440c0c1442c40d100c1c0500c2c10018020b0079a1031034491112450310590b0310115101d84075107400f40644429841c0030510f800c819001045d064440c40d04114020000000020b0b000c1c403400c401050340000d0041c81e80b0000c000c01c812200b032040014060f8016004101c3ca03070030404003039000d45045480c002840d23881071480d65041405180000c0111000d03451407004e10000201071412520214101d42c1d0064032281e0b01c004c8123091800718180203440c00c4400903504000d810582500a185042905280b42a080c10380c2084410b0000c1d82e0340a104000c0c041002140d00420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 416820368 1250 416819118 416819147
    0x605010315080a0602090a082b090e060409031b06090506060a2904051201050405060903040f03060b010507061a1306270207021011061605030c090a03080a0c03 70
    0x744441407400440503240c2c60701d1400108040c0c0d0000e0310307100c01da4464405074054101d24003110345855456a00f00011075913604410540031030a0000742e0310754032410004080c0d0340b00c0040102e01e03840c0c081c28080641180d000440030300404120795002409012807201d101405480c011500d505141406820004054032460054202e00d100b40001e40340350700c1c00b920031842c80e03101600f483d90700c2240d10001c0c007490708003603448440301d0307a0401600c0701500030328025405902600c5c92038942d0002c0c0b554030305c164420b2110040d51b01008001051b0780340d020b016403403c18142249803150607600c039011514182c40f490301c50108500001c04a0401d4201c44c05101d60049081120504094003003882900e04144500c0302c02d02c0300c010003c0300000390103a441640d405018060780d0442e80c000a0000300020b969040c45200f010002808000ad45001c00f01070481c50722001c0c5183c84811180485d5030003040040d030440f403620000400500090700405aa40081e96003035541412442c00420b00c10311048074 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 416821618 1250 416820368 416820401
    0x507021501080c0603060f030a0605010b07060506030705010f0c03032a0e0306060619050d0f0209100c0809040b0d02090a32161403010806150d0c0501052b06050103 72
    0x3540080e2140c0b405c0740e8000c40b085402041503404040003c0c034110540c0070081c544c030b003032000004030300c48108040c001181c4200d0b02407016907510001d2540d40e202038811140010204040c061500d802a40034030f02d80f501038500850b0401183d00f0103c00a000c2d0b14400c000c011182035900c030503507800100c200e10800300310054005424190f000910701c2c05621034118604c0010301d1608003140c05074040700c0f44005040c20612440320241c8401e0001e41010740d0300b80c044c4c00d48102c1203500034400d05107182803940c00030b40300d0300b070070404020b03c80207100400c80c0e550446996002440075a03913407400c6c10721400301d0a9001c2815140310410719034140b0005401d41c64a05c0b220708206a0204684107964061b03a589250700004542c54801c072030801104e4a007000d001c01c00400030070900307008a0b84900c5080720341c41c4100c1428041003801840d0b16944005080d08040c5d64092155600c2040281403a071206602c41d104038207512100b28129000068803202d003559980104641d581501a580550844810307 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 416822868 1250 416821618 416821633
    0x3080a0c030e0a08130f1d0f220204020403060e010e072c090102131805070e060a20030d050f010e010303092c04051f0203060f091504050702150108 65
    0x40030b90703499444500405070f40001c182c0f13034480000c00c00301744028210301100070b15260307840c80040e0441c0349005290114021500c0010b0889007103071142405107910030781507108049800303041c00d0b0754050060704990060702007100102040c101c0c0107902e1007500078000010160740d0b020401e4505461a072080710110380303114054070224122402d8030045031a19030314181030399411010a009200c2d900c0f001c1d84080714000c0c0800c4402ca0a44007108007400c41c20100030640350501d05440a00c0c0480e11184d20000401103031806034452990b0b090160001585500d40c8150390b1415420b54002081403211240e46804000100c800c4480b520f00404c0a600b07411015419500c0c000c0100256001d1400304480e5070b03c40301c45410603003c0307061000b40c0b04500f600b031a04081c60714644848010202c00d000200356555100c01040a10807280a410020000001c8002c00e4050000c5200000c2c01a1101c080794600c02d0b003240c4443c01014070950090340509802a0f452038680f1480006802c120703000c0e40f2404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 416824118 1250 416822868 416822891
    0x30705010807020a02120a020604150201050601051e070201200a0c0e07090509090312010609050910050a05210f010207031e1407140f06060102010b030606060909100902030403080a0c03 81
    0x141c8080c0c95170140e80e01081c9919080201d882c0c41003042009401490004001460074145050340300142e8403680244000c0c0ca42c040119070b1802203c3d81c0690882d144240000010100f02c01491000c8c8181081c1241c6044881044402102d00440200a800021f458401c000803030300011b000d4000c0c0414100700341030042000b015010f40b40140781c001d01c05040800c40920341002622000004888a41c80568441030010000b071598410207005880d00c1011a8000c0e007214000300542e00013130b10200e1504d142c1820000030240f0783c440b03501d032041b00c68020174080740140941050a8004000541d035500603150080507944280c24404100500c03404902e08564400c244241555501107074036240c0d1240d0034101d40801c20810a084035100e0aa010101082c0114815100d114240c000300520b6000c1c40c141034864108541859102c0010080d840c1c051404030b46a580084c119085e81c0107c6807100d5621040f40c0c0141c42c01d4011500c02c10401c461030019001d101e00038019441c00744031741c48110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 416825368 1250 416824118 416824123
    0x5040f0b1b0f0307030e03030304031202030c040803040306051b04030809040b060c2506021212040302120a030f150506070308041e21031806090c0509070e03070501080702 75
    0x500482044820000d4078444140d070300c81010041e507107114107642c07a03425282d42142e660352013a102200403481e03025040c4032030f2a0105c2560700c184e8150b11018105801145c00c0e500035880141010003801c4c0c2484045000d0342d0806c003074005544503c41c00030702c03401d0003050380085600e1500340050303100c4100b0050000804c480d058508000301520081003100c00c0e68002003250054008840003881112501d03001c1c004d0718001000c1c201201000e9403500f50721003c089803030380e2081461124074401007004a00301d0a110341d40e59405030080c03043e246100e0781d450340a80d40781d02184800c1c002903158481c4181c0f040e99071140c0d4202000b074004698031285804045041402180b10243c144401180024280008003024a05680d1203041100d000112450590078221158031540420341d03030704403440580b90091140c81d42c41d9501c0e5480780d0301e08500c0c2e61503502078201010b04484102c6151000113107600c030003285c68012803503030301c505c44204407030001d0502c0c113452903001c641000380c580c0c288403855801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 416826618 1250 416825368 416825399
    0x30c080412110d050309160f0b0315040e0606101107140d050a12090609030b04031b020a09200a02060606070302030c01060608090d0c11010c0f05121b0105151e0306010906150504 78
    0x56803101c54507681d422010112184c282040bd903003203810507540001009012032054842c2204541e46081e0003440c0204486c42d0001c2c00d0484079a902c80e500a010401111071074040000b8000d1072000c140810350340d42070070300701441d80403a00500c00141e0b15002d6074026448802420062904523031640ca07544031011000400342c4064140300c0740c18200204ac0e40d141c6007140138960040e0500398070036a00c601d5200102100c60003403d000780c800200843e80c5004c0c004440304940b0b82d81c010309454866500300419a408114100d00303500c02000741c0f421111003130080400134541600c03581030314a00380095508280009091000300a401e003440303000220380c01d0829211010078a400136400c2c10a01c1d01160700207856074060150b2013010308103145864103400404000180a83d10500014280100c03401c0c0c40069440403140a050303034014030070742404a40d955a40385560b520560021011010a00304042a0424995592103500c10700c1140c0c20303010b854174482d409107482881d192400040b840c50341c91 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 416827868 1250 416826618 416826629
    0xc05071e06050d1803020f010c050903120c031606050103030f0f121a030a080d150311010807050702090f092503060f09170304020907030c080412110d050309160f 71
    0x400c3c034400715405580903104803040703c0d000481500050a01950b20100314091080d10360070150b40000e8a8170440a80cbe06022014006211f4041018a42291504202c90303150340c0c4c1c4001d01110740c03108081d10201d540ea5004103000110355041d0304008000348c00c032100200078003607103640e01041d0641c0100d0101e60103000520000c3c00f5000e02d502404280c3c440c2417410750500c50f0318211010300001600811611010490400c0409030104070b1230340c0740c0b03400c2c4406022465440440d8215500903101c196021072585840c5140c40155800501c038035034182c2d00440304172400c008020801804028000c001c03a0841d1800b11a072a031402130b1400b001841c00000d20541d01d900462640225a8111f000126030041035413030012411a00c202c4160011078042c4e1103200c900000c5145503002e4410418003843c40c0ea617a01441e030b03494441c2c00c00903100c480c10710200000080c100710761070001d212071a0b12107000e90b01c480d42c9007000740315140703042581510060340b0300c01e250301000f00b080f08100d02c104542 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 416829118 1250 416827868 416827877
    0x1050c0a1d120304030818030706020d0503041703090a02040b0301020313140a06020412030f03060e13050f0f1b09100510120516120504020f0f0307150c05071e06 71
    0x108003201182c01d5005184807048184400710300841007001ba01d025043d0480a02d01600d51004200c081590f1080c8520900000d43c2060401c2a2524458002594400e004001c15003020a10310a100040d0303000b200c841d00c070364000d0709006046240c107006903222243e08500035415824122a132110301142d1190050081c0c0243c41014010503050041c146c3c071680190085407529543d41c980c00d5415035540c003c60015404d603a40d02020742c068030550382940c1420100340065a201c8c1c815012825851382d00b03032210300c6041207004210718200701303015030040544040e045201141401c4207441c07000300388007031044603100100034082a042d0041000c44204a504a509113200403041c0d034250880140d484000b03091070200011008828900720341b6140b20740e00c2d100c6001c0344541d083d044500588000f03601c00c142d0720341c0c62482d00c0c0c900441c014081c0000c05441402e07540b8802d0203113000c001a01c03800840e13034407950b81c01881010300400004220b001e14000c0c0c000c524051510144100740954814031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 416830368 1250 416829118 416829167
    0x2060609011a070326091002040609091113060302091e150a1b0b0f01080d0905100e04050a0e0d0807020a1b12141c0212030916031401050c0a 62
    0x6201d40c4840c1917002c440311031007910301e102031000300e040340d0100c500004511400700c001d401c0e04c201380300300e4003103510b680d80e607415490410580c08050568625803500c08401804210316400c3d250000c00010251a180107940d289a00f0504c01812218000443d241c07441401145098840c504584542000304420568620310b9084c00d541c1c40241c1e9112044121100b1020820006001c02c118010104200d014803a80e90300c0005c0c1c0e0351910714400b1280000c844800820143c100707020401940c0f2104c1c2440d022030511840031908643d4103c4111110799120821050708034414040304140301c3c000d281c00c030f010b8a01420069a0b92030785140003428a95610001d01d0345521084260703001d086000300007185080300d820029010300d11401040014003139098002603510610031140040c07a990f030081c20001c160003400d00d0070754100801e41403450048400388030078400304011180c00346210320010740d0207041c500d5005003101d000030003540224104128039071405d82c000c08080200740c02c100a14800303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 416831618 1250 416830368 416830373
    0xf090f080d060e160e0402030106021b011e02160e0702070608060406050d08130501021903110f0a0f0c0f120b070c050303070f0e3a1b050102060609011a07 68
    0xb00400e80c02140354201038400d2102d5814007001910441a00c2e60304c8111903201e030410001248070a12034000980d100704002980992a4242d0009490301410070804880c2910450800810200ba60310b0058020341a12040c1076030040115015115613488540c082c9800c0d00c01031f55800050041c403080c000420002080ca40d11a0824009003101a0401030750411500d0010101c1d0041e455420016a9400740030501e54030020b046c0f03c001020409200c0000b010382c0301542c0c100750561103002c19004040d0480c1da0351b4420843c005145110f55088808002c1504205490107000d800844280e800c1000c100044002076105e420183d40000c50b80b1100d49510009441035002500000c155001c0401000740d0300e078120206c40000521916101030500300441008041c1549050000b00f1401045d95154030b00d40201103083c6d01600740403a20040c10007134940e21400341e4401142081c0c0c090b0804180402c4d40c0c1030101a1b040b150668000c02994189070300022011011001901c118001248000a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 416832868 1250 416831618 416831621
    0x70c050a030f03080f071d0409020a062f060105060d091b0f060c02100f0c140105041101020a12030e0106050a0f060306050603070905010c0819020708010f090f080d 72
    0x2098000c00150203140d4901c1e001900000c426001d03000b00d10100300050002e0041e1041c03038032400141c1d0b030f20380c92858101894618030060024868005569101c2130005032200c0c000c04003e85000e855412080c80440540d1140385c0304036486400071148500c15114903080092402d040d41e9045508a841f0000c00706500c0041c8050400a000c1c01116005180b4a180380303100c04080d0342c03a200402100c141c44640568044c645800025000784d40704c401c403da01d910584a450300c0210510349110b0907913480d01c2d10040300494801d280d10702e96550081c00100b002a030807460b0064070a0020b0710b000b041c29110880503001c3c0c0380340c2005050310340f0182031400c2c0c829400b95010300301c002c01140b09140c4400c58440c000c11030b4000d4074080b80c5410b10204444c5000c0003908c2c4100820381d0740381025420a0b00466000c44c01d050100c8107110140030034041034003075561144010341e159000b05001803804411900b0f44500c0c02019645a2621008030b002c500784d07407215000b1640190700c0381d90341c0303800005d00c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 416834118 1250 416832868 416832893
    0x70e01121401050a090e0a060e0705100807080a0b09061504050d05010e0105090a26070f061406010f090608090a02150c0d1403191409010e060a020c0c0607 68
    0x142840c50160080051401d401216041e5a419220981455110b003640811641841400c21850303000c5540e1000160164120980f13001085040d03810082d9110b011507100c802600d0800081071000040014442d40030708003660121a035001400041d0500c400b2030a042401740c21305014200c3e64031807000c82030b04541194010503029215004820241c00c1141c002c205800210352103500f4130021510300040046e488a00311f070003010700104503400328480744400c0c04903070b0285402403040c4244e5010408201032141307094040c0101080004982070008405180100900d0512100e078290000c1158000f04840c03da505604116505403591801989400c080c1c800003540f042c00d244203e4603180c544c5018201040c041011500040f45504003500e00080d8401d4880c00750009100281c1601d0681e003e000c102030120a00050048148108000800046a80d08400c0c1c1d1a05000e00f0700c20020400141d01802c0503501314208440c0303404071a215020b11541a206600100c0c001091091f500642c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 416835368 1250 416834118 416834147
    0x102190e031e0a03020f0303222d05010f05190b041b031b11030f090616080c070e040203032b060e060405010510120c0e04051905130b070e01 62
    0x5101556411015558900c160f01c210014001c0c01d80c021415000002074a0090340906803840407403e0207418080307080c24061090f01d206180b010115412100e401d00140024001c003040d04401d88142412401e45240c8001145114904000c00070b11240704058030801c0d55108d2030100d080c6c4110000500a000962880740e030b1489038103540030149070198080002c01d4450b400100e103841600c42d090320360200d421300d1080c581d003040220f0307014110f1100061807882e5004007400c1c01c0058041d40008100004101140c0e001c400143e00b6040c007000b013200000415130038405000364a050703170109842e03010341c66000700011941034050040c1e94442002c1288410b081030b0800c00310b651403035030220b030a000343c0d070b01401207150a001243e1420500c680700303040c0c070454a821001c103075444058070082030aa072070101009061081107078903503200d0050602804009406403203620b11015000b04030303240a001d80c03d41d482d03d0201240000c0700241c545034014100d083c100c0e90400340e600187c43c101c03010603c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 416836618 1250 416835368 416835403
    0x50603150111241017070519080604061d07050a090908070b0a1a1002030a14090409050303090705040e0a030e221509111b160807170102190e03 63
    0x10b0072004014400f829114032454000164129039500e40c602c43c803040508403500d6500200418411400c0040186d9000c50041e0300403460240d40d0004c26042000c1594100c0780a603c81c0c51036444500c0441c1c0c000c118000400c060100c55141c030001420a0120f032013141c040035150385800080c0540e0b0304c103603540e95801010300016881c21140540061007241d04e48000300b500c900400c07415041040c44c0e4008802c1c5500154075040507007505442d079190354003034056080b200b0402e102c0345072101e000e041c070118030680c011500c0e420300480b0903044c621030740c00442c01186400c81c2c0c8211040d001801e00f43c0c0541500b0071818030020751003c1403a204d0450800c0010350001c1c0000500f4500c2da60054a041400da100d002c0c1142d16800c0c008141e56000d18204180e92042c45070203040c48112401001d491041412509454140490a036880140d0341c082800c50f001900c04100d000001d59620f1401e0440f00021450b0002e61505c0283c0040320350822410465400c0c205c1c1c0b080d40b0700b08180da20b8880769010307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 416837868 1250 416836618 416836663
    0x18051c05161701050a0c050d020d1e020a170c1e0d06030b0a05090c091b070209010312110d0507061d010e030c24010303230c070f050603150111 63
    0x2020140c4401c555100b140e190b28060000c0c820401d940f1420480340b0003541c03800d140000030076800d0060b40092500581d200c0d96800c01549070220780aa035a0003814150000d43c60303c5000c8406401e02d0403c5580203040003603c0100114a0f41d00401c4070f482c003074507040320300040e00c1c0d80c200c540c020302031020340701e030800c2c6811808400d11032135000c81485544c86180c28003d07682d0f200e08803503d03211821100c41d08642c009012400c2c1c540c01e030f001d500b8480300c00a0081c1c00c040290f000102d0f080c0003131b4020360b00c1c0e4107101080700000303500040700c0c10320040c0303640105005c00801d0f100402510650501504041d9035009501c0c4443d8840c00c03a28030504840000c0c815040619100c540702e6004080b201024802c60742121054481001802ca01545000140c000c603840d6841c03d9644a03c0c100d854201d000103203054400510140000e050014012002882007500700311540301006440e80107184129401d000300403101068540000c9840d40a203003055903086018085458100f54880ca0584003da411 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 416839118 1250 416837868 416837879
    0x9020a1103041206111602041a03190203010c111002090409060e0f0705010e06030408030a1b0e0a05060309250503100f0501050409120509031005070f18051c0516 71
    0x700e806420f6030003070740704000840398600f050840b4400c0c9034040040315036050442c030142c505540f00841495151249440c8070038207100190070481507030181a01044012848005d504091068140c80581e40c101442400d501143e0340740d440042d0202c042c012900015500c9580d141d0f504400d1380c0681c0700320b092141603000303132109840e031103071580903607441c0b00780c10000450f58450703482d0b544240d8002d00302c549551200e444010a5500040c44800c0c050785590340228036264103484030308411103e81e81c42c14400c0325482002403202c6a0350065100d81c0c2d0510a02031030302000301e0310824000c9d009803a28140c0c2010141c01520315a154481c55042c0035140d180c00385001070b9000000d440020310010403041ea20390080004035002c2c0038010702949448045100f00c903001d50010028807000a04071026003241072001001e94608580c0310001544000d5034141d403981002c0e0510b80d10340003800d00c1003414205400300700c1c1c000000905e41b01d0a03a400c0440e1042c030009101210210301c190011503c11030316031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 416840368 1250 416839118 416839139
    0xb04030309060b1c02060c0c1809010501091b1d040f0e010b0a0303140d0608060a02091914150d18030f090501020a020d050118061a091009020a110304 66
    0x1c1040d0740450910310b404003070780380050b0044031094101069000581140c1c00380069034000410300c048038030030241e10303850547d518200100c603084145401c11171071034128521400d682c41a4004201c8508001d00341007003040c22842045201c500f0f18244520a103800921461440c210861030b40051038010f000c8004803198010a4504203d400280410f81c1142d0602c80e02c0c0c41144005000a040003002c4103030411040000d003800182c0080c0814011b856200b0142441010f84101300c0155001034007900c1820500340380044d1548228001031424034100000c50301352258071340544201c1400d03144507490b086000c144c0d0340461380b100040101c461446442c1030381117000b03a4203801107031914906000c050312030543e1000782c59041c1c0c05406006e0f0b090b820301c40d1f0140e41840403140c654a50800a04140b4035000000c7c0c61800380401144004040c08546600303100d4150b6280a192821f0402a40d02d900c0b816034803c489030f0030390041ea03e01038490100d0f031101d000341540100e03002c00240050f1240c100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 416841618 1250 416840368 416840381
    0x1202130912090806010e0c0903120c0a1e020a0b0901030207050a0b0402091b0d1d06070e0112020705070506160c060908070603021c0b01030e0111070b090a03080a020d06030b040303 79
    0x840c1c40b03420182d03440350485543c40300248684a50020103000045603c2506400b41144130000703811038008006030761502200d500035100e40541507000300c5100b004e01184c071034036490414003402400041540c50b0041079141129002d40c0c0300f0840005681140d0303034030a604603402c068200050f56440f004078582801e070423105840683c461409540420418070441101d4070f40070000c07014507841c003142440c1c2030000d0018200182841454403d03480300014051101d40d1041b0525904d21601c548418009400000141748a9140ca841840400b0025038006111701c00c1d10000c554540c1c540028082040c0d95801c0d140340209085045c0b500040d030b0703a40201c81c002c251038419090394202504c0e48012000ca0150f030f643c000b06240c00107070410110400b5404103440c2d04041c0745c0400c086194950399800c0d107219000e00100c000000944000340644100780d55003101c3d8400241100403603079100140807407805010408100e500241e40e48118081d648100300455006240001074a400d042c089d004008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 416842868 1250 416841618 416841653
    0x6120105090a020309061302010203071a0703050c1309050408090414010e0717040206070609170903100b030a1704050a03060e0c120706033912021312021309 69
    0x1c50404508100e54500a503485110103c008019680c0c402110018101d41d1507416410750208001c03a40104240000c203482c0c10b0050340140c0040d0030301e207030000d040301e8008100200e1581c0a0002e01c214840c0703a440c1c20101c0da01e070b89011805403150b092500e241e2054581035640545006514000d940400c2e030034604035902c40e288410f559840100c2a44c5044203c029840201488800100140303850005484803034019400020030503200c1d5211070f0301103100108101c03000408290b0840c00c0c41c1c10400e000c1e242c04043d00900c05055a0b00120341c1e01d02001200030050b40c50b50f40b0f2186000000f600341d030000c1400810707040c0f01c580d49052020040c048008480740d2400340d000950701c0340c180030800b111000c54240003401940e20f40f04003140140610804118103014501c0114044494421590001035180c00604d80c0002802c03000b13000b800a8080c08024a40180a02d0b0304102c0201c01c104110303101024142e60b0880c0c0e41c030010301040c1900c041680b0941c41c00ca030802c01c1c0301310504a500d1010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 416844118 1250 416842868 416842879
    0x5040201080a050402061215040c020c19030b0705030601021006030308060a12031d0d0b090d08100609140105070515010816140d061413031724010e06120105 69
    0x440300d00d0701070103039041144c020350003c90030412200c244d0070a80081d50f000140011128407e00140b00140580306880d40010050b40080344800701480e00040c809110440d002ca004807540c0307581e840f010030140082540041c80b00200000384143d00034000c645002507505804c00c4800d889280240107038000b503c1090250084a10106528a0b07130f4098240b000e80540310f03c03402201c03180d09010344401c012107058000030700840e4880001c2c038080590303014812607005425074080709640200004801841d8880d0f8105101c0c08005031508a0101c60540303103030214038100c00207503074010382d02403107030f450001c0080c81030406182c03006112601c590705a41200c0c09443c0c01004141c070194140c11b46006041c420810300750382002da4980340170261081441480007040321100c415a81403003500886002031840c24a041e0074017015405042011b1060303440100c0101030030700003140801c19801c80090206821110690b542a80c05541700b41e4550100512660742d07080000d0280d0b419110078407a0a0040713 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 416845368 1250 416844118 416844121
    0x406050709122a030317070302040512011d06061e03121917071b1b150908071401080405100513020906060f0913060b030703021b0718020904060b040602010504020108 73
    0x465014280500304c0344c1560714500b1280a111440a80d0b01002c0c140c2002c0c950301b004006801e8a0381c03046041202c0e007800001a041c0d00d0742c1d20702d03d04021401c1e42821290803003030412030b5a950700c10a05501c9a1003035148900e07000c940010926040740e1110009103200c1c04258054000340032894407009001c10f6403008801300c51086548402c20b011f0b240035021489000100140b5404c082c0c640003544c0c01040802c03009401807522610502c0d090308003480744e81d0398010944d9150342020507076000344010001000d00514008040c0100480c0e40704c541d0400400c0d202040c14030204012010701808402400c01c100e0500c542c90342c444414503141240a080e44500103120717860100141c5000443c409880352a10761900c0030491001d200c0790440704540e544100100d051042000036510404007502d005030307603400ba1407504840c80762400c5140c1e02c0340d004410038004c603002048094003442e07005901588a013001000540a000c441d00301ca502d440003c10001070081d4150001c5001c1d500070307250030056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 416846618 1250 416845368 416845433
    0x6020d030905031e1b250305060703020a0e03060f160806090103061d01230f04050d0e120a0f0b0f090d08070302090d0f02010206130308040605070912 66
    0x40c1c9035201070242440e08107201e2000d5504501202c03555400700c1c200f0035441d124480e181483c82c000d115a46105551201141e0741ca01c0768070005440c00f0400c3c1e03d440030b211514523500d8580c2c44034014904002c254010072082289800342605001c0b206006003a0f43e41032070300751440e81691000711003001c2043d81c014071741d00302140194900c50042d42d010b003200290340ccc25a04c0b082c0140942034040c4c4070000c24610070900100702807044a0b040c05031802d480b949400407440750038842902030862400c1e4130888080c0800540001001c1c0380e50016410314200c40c0461500040e4000c84500d011015030049950f00307000c10101402c5816100c0c407540c8034450903141e0b51000560a8811280b601195200c03e4230150494041d075802c45d8040341500d070140c0b03044404800308440c0c3c00c60541c2240d05a001e05000021036805100a41d4030011210303801c1e41d52091500c00424540c00070300090300d01550b91020075280740c13040403000043c0ca454440044d000c0614600440880c0c0d4102035103901074032180c2c21001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 416847868 1250 416846618 416846621
    0x30506040b0a060c08160b01080303040c05040605010f080604021314100c03050724060810051501090519150c0606060f0503040605100810060303030605090103020603010b030c0d1506020d03 83
    0xf5105166a1340300074081a42e82c031141d40c0d000d080f081c042d088410074808001030000c00c1050107400258061900c03414030303180412a8040302e410951140c6d061500610099a006039454007003049860070422584801c80031600034030818146c4090702c001180007103181460440c3c0441c14040c140c5484600700c21010f411036041d101d000e0001d001807820010754021880c03000c05203034031040210000c120805000c00c548202d50080e0f0140c00d90790040400d01c0d0010040e4407403030350711021031598810301e0b0202c200000c3c90305801d4082c880c450250790048071840c0d50001007401c0980a43e641c001403002524101828824a0f014216421410080b000c10f449219203404040c0307082d02e84566013180c540d0740d5041e001d403200420309246543c51100014a81508025175024010343c04070014009042d4140102568043e0304a41c0c025440b00c0700400041e00c078141141d044030442d200c483d4480e02c2d10a000b43c0c03a482503e041411356401d108882c14030048001e000001c441d5036400311064040104000d50 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 416849118 1250 416847868 416847889
    0xe0a05031c0e0d0c030201080705090405070f020d020f07060c0c0504060b04150507050c0d0501090c0306051b0915131a0a030c020a050607141b0102120601021c050f0f0307030506040b 80
    0x1c0c108645001304200650142024541180340c900780681031490031000300c1c0071220200c0d00c80d80003480c0302c082003840f01e0301404444100c55081c8098042ca03045488050707a43d40040c070801e010400068194400e00c080c0c0070510004e000018000d0005940d252445082e42c3c001d80551060201003403c504c4580d1700a000312491103034080c020380b0295038042d040064010309500207980340d5480380d00f4134000400181e84000518810200010b090420340c8000c40d04400003031035140040001c02c80d6205581d00c14a0700c041101c0390851940e6500040b070b0300144400784607440006050039540d0120180c80c4900c0c0545000503041c0d608100764150312b4030482e40e95000d0328001e49107810210100ba175280c801c4400e014002c0e0140380302c0b45840d00102c10b03098030f4001180042800d035808180c440a40b0003a00243c0d070418024802000c0c0980d402984a4404d400c0403100d00a03c0000907005028589507821399614030101901c0c1500c910b810303400680503100444005100e44e25080c0d60302c108d80741586050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 416850368 1250 416849118 416849123
    0x1050a0b090f0106140c030a080405070609030b2a07050a0b06040506130c030e100f0605030a05100b1507081e0f0f073f090b03070e0a05031c0e0d 64
    0x40b119900c1d080c000c0e910200002c1c04a050110200028004003000300f0003450301d2005da66407003540f1f28150074030a0410030745400107010056507120800c0803c4940b40d1503500900760100c501c5038200e07074038541c5220369014103200d6046076000c160344052080100782c282059000700300300700c50380e62400104000c6400c203c60859014078070041c1c0403004105030303100428200490400040d46043c0c0303149035181080700a15a9200e680700c0d2400d0001001500502d8010300058006040300d02e86aa103941e11011107100003a2526554a162300b50740c5d807010303000394901a032030009035680e4078030381006c50081d03028030b402178040c0c0100d18442c0808041070f0701710b07a5000c019000d500c0c1040703080c07866580c2d90b40c400042a80e0780116400e401c0c0c2c0f01d80040080050140d00a0780f030502c611141d9505903032421700c01310344009101d15582c0400034200208200c0c0c0d0302181c58580940041d840b94009140e006180d00502d80500c40c4603044803044040e40e080d071810704da2a499035250141e041d0100040b90301e400c40c00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 416851618 1250 416850368 416850391
    0xc020c060a121103010f21030806092d090610060909022109010203060a0e06060d05070c0611130f1a0a091203050a030b0616260c01050a0b09 62
    0x10446050b1003444002c1c2c0410810030080340f4a00e00c0800c80000703820a8000744114940200300300404080101000f00103190924000d28200d425207010341010030050400d03000300c001c040000e41a04e604006890f10100450469100e40b0341c085003201000000c03103055040344948004a401c40c506000e82000b02c64480d92103112072414400e10030082d4201c2c1e10182c02202c42ca030221a1810039a811041c0720304102000141c69140480400108110751b92008148000c202e0134009170361264000c4850140c0e01200120702030711426002c0780c14480c0050041c00540c9400552003540200c04001c003034407005401ca8081e540d03107234100020f00190750300c18446009444600d5030400b08447c4084c1400c004141820702000344e0300c918904020340d094101f00d00044001490340440740e0540318007600030300c060303503210f04046021040704400c0c607500801400d00082004a8000d00b0301415103070032074800e201522911a0110b51710b19020380400d46280c140036060200307100d0641400101c0038801c501c580319 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 416852868 1250 416851618 416851627
    0xa0f060914150a0f1107110907080705030624030a06060f09050a090c050f040e0402211e0f010608070f080d050f0901021c050304060f1a010513030204050103050601090c020c06 77
    0x300001c1509914070307000c080e05d8422160168445001400d0b50502400392410510030b0081000000c800051070001402042002c0c003071000d82c81020f83e6440304081d20b440b24040585c21075405030450071142018a0000001044910b5040e03130010001c40300c0c26100c3d412026400c4406880301c0059018107a002030b0b00038410840b0800907000480440e046041c010710303180080e40540b016503c5a00000c26440026080c40118104950000900120040c0301e01903031491000c0d40c1d807100c0c0c1c4015000911001c078280c5d9030f07240b64180600b114201c4058001c1003e036030b880000d25250b882521503542c1141c000030001803103090104500500c40c8050f590075144c0700180300c1c44452a00090412070451140d0b8140c003c107601c005018001d100700b1500c559480746070601c1e143c010703900180c200b149030508080c840f030b00d8a100400010b42b405001d01306152203c1008201c2003115810750b2010b0f5001d802c0c00b00010900c0404101075058503640c42080c4130440c03502e00141d03514080403c40e160007640810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 416854118 1250 416852868 416852881
    0xc091005090d0f1e0c031406010308090607050114150102061b1e0c0601091b0f050d020d15090621021e040914160503011503060207050a0f06091415 65
    0x204900c1d034040c4610b100c0f12040244c5044920440302d001c60440b500746000c00709005102800051659460b040802003c0345d42c11aa164000c500903041c4040c0184000b0030410304103d400e401144982011040c03d240b585050a00c0074a409a0324a007140940540c00c0410a00300785e221400b248008050107442c642800e005044000c65010760a010079090103000d10384c5907070001d2001d540240440301d0003151110a161070810340006d910012020b100e00701c244a0b841326004001d441d00800303071400040e103030641000101c020b08405010441070714405500400d076107285600c500c0c1031710045982511b030003407103110031b80d030314411918003075403050713070201d0701c40103031000c2090300004020140c008280e461441ea607066030214030101e00c400580007090174868011111103a50010b1100310000e10540b1915209042d80750114000a4403042d000281a800e0210030004413140d65070000390b46010043c5410814010200e074081262401a46100c54031400301c00640e074001010140c591a8468031080c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 416855368 1250 416854118 416854133
    0x190e040c020a11060c03040e0a0614060c0615030115080105010824043306050319080409050a060806010e01030b010b03151009080f0c1002010e06011203090506030c091005090d 77
    0x4581071704588004c020100d548142440d245006410b02d080101c0e640c0d041c40090b10000e84003420480c02201d0600820007600c0300090300503001381150342514691030042c00402c2c0500101215820ba0300082d090010301e00005610245c12203141100f0f5a075001304140340500c0720a00c0622241d0050020720119020881041d00011549e003c11800001d8542e4400307202010744d1100b0714500442e036201f0041020381000d00402e01c82003003100e2455600400d0341c2e04d80704940224000c840c0450f949200240380c4000d181d10941c041c00605084404541e51808a240d0780341007400100d840040308400000c180138001d05032030250401207004c4412004c190140510400078400441c20840d0721500010082e40c00c4c09014152600307a00a8040800100144114020440c41c18003c582c5000a01d41048401141881c1900c0d40488409200566814100c0b101040d40e041141d01c00b800005204802103034400818146074160f5a002ea981e00021098465026080041b034028552034490303070000b1284c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 416856618 1250 416855368 416855377
    0x10c111c030b09010308091011030406030e030c0f0706121109010806010e0a090b010219021522060302040510020d0806150d050906090601150c031202190e040c020a1106 74
    0x11441c000544030384200029403805420303841a01c5840000a0440040c14802d0001520b480c490a00400c0106034070252944c91040340308030700c10540d403007010386a02c540600403500c00103600c1040318840c000da04050b0340c4803886071298401003150f01d520041c034503c090040c5885c042c150b8102d142001901d0005450350500144654104100280020781641d2a0322001010744290f80d00001c80004980c006072504000800030181491802da00758010780d034050044001591081110340c48450301007841c0300091420054020000342d07890701041050303150340035200300d4400b1a1130400e021051441a078585040c4040407000590703a030000790050411414071003550142c002090301d80080d620a0b40e0459100740c481a200f90084c070f0a010034207508102d003074094403a44d1010550f1914101d0003420244002c3d90013018046140400903800e070702c59041d151400300100d840d40006540307241c003c1101e0200ea4081d48201d103002100008103200048c2d440301581e00c440c042910007607100402c00c140c1c00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 416857868 1250 416856618 416856673
    0x5010507032109060c121107170c030304031e03051006050c030705010203010b03062e1412041211011a040b0613091a090f070e1f050c010c11 62
    0x4804480504502c214802c41e0000341c003030600003d000c42c0f01c075002801e581a6046c1c0706405410a01641c01301c803c40e1044400c40d69005280f01210362004200c110203008038101680c81d40070120802003410340002901229080d800800c111510510300d040e001c40d88207458010303d4041c050001d1000e503014000030300c1c42a0030542100c5c20035000b50307181400d80c3c0c0241c10429010340044240462400c14040515203226122040c1500800c900d48402445918180000c01c0003016880702050000e4041101e448400c070704905526803400d4200781c0c490040807400300000914050b450b9100010622915426000540040d0380400211701000003502407103240b1a404001080440c8040080c2254080100203144000c0740e0300c20b003503503101e0302100b00c1c1031003501070410303801000300c03c0c110942c00c070b2350100c25800c0405114406102103450301070780851503030344c540c0800d220440c1540c0090207030240c8400180207100d013180071401101c09003607103a11000315601685107001e0340603801d001c6000a94 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 416859118 1250 416857868 416857907
    0x80702010c050f01060b0904200a0f2001021c0209030c1201060905090d090602010204050a0b1308010e0f07091505090a0e0106060c2a170307120f180501050703 70
    0x34914580c0f42c00c44185510a05400c080001d8020041c103060003a81c1c0b030341000c04a0440300641d4061a039110740300d403031000d0040090070046001c0940c00369a01072800d00b40080d40d20070700301c0d1106e5902d000b503100700030341040080218040304902d1b00034002c03501d50440c05005090f244a00d481070004000c096406620715540b10340012410000302c1c410315202c0d0410100402e850184890081c0141c102901300c40c0859004200c14001d6031120a10315041b560782400c00303a540c1000c808014142e2445800a00540d4240404034551f0300c0002004400789100310150390099588421541c02c5820700b101a0a101030081e00801c450f2602000e26540301130f0441d00480d0094020202c00c0c216160b1340c1010307010071040801d85c014071407960181250300480000d07418420325040d03001006401584208440132018068000040105105a50106134041d00c43e0840e901510b00c064000300d2100301540005604c1c0381a42d112075082c055000c215039042c2c41d40c92416040c0e8a0460341c000d80340f01c007a8104d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 416860368 1250 416859118 416859133
    0x1e0b030d0309081b010506090a020f0901080712050c0d0e150406050709030c151724040b060d06050907090612020306041d0714030a0218280f0b0607080702010c05 71
    0x5a034089030b04065104c0c1500006803443c2070350401c00d001c20050300109000e0310602c607142c01ba508081c11940540360900f0100d00c86d03510a030040b2448600a001c41041782c1c00c19080c05041500c41010b04014000030406011120165036181d507521100108241210150701c0800c01045c0c00f030b0312094210b0002e192546d403071030312501c03040c41940ca140e001c04c0d500403119080d02d20f00c0c3d81c03140100055689200c11944d040c00c10410f09501010b03625800c41e00010100303074041440d0b446600c01e107001030001c5d2035192501c02100d2844000c0519216080c020b45e104000240b09501c224a0401a54500e4890705804280034000000070340004020f9030704140c0d91041400c03130500030b08400003980c0618008107070302070030180401222a031034040786019074000c05844006030796402c48448007211504410b6800c0d80c8030590386a0302d1156035140c800c03075420040b084501c7c0c0f17010f03004080d000e2a40b01c000e2042192003414000c246c800c2410207464107506204074030040d88282d01e64402c05000b0740c200c60b1503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 416861618 1250 416860368 416860387
    0x6010308180d03020606040f0e1b01200a120c05190f0204050405060403030f0c0512100915080f0a0807021e092a03010b032a04091e0b030d030908 64
    0x30800100d003c0d005640b0860405c952403a260046004100e0300850a01c0065207148401e41d4803104907403503400c134014015800505903c1601d039007443e0b141c50039010300c810450a81490b1240c492000c162030f203240681e00e11243e540a8200c2d03900d05907010b030040100c1000109590b00d05124494211196089001807401591313560140070300aa008a000d041181441d24006c1c0407030705181000700c01681009440c0c1c21968000d015914905503421781c184480d41c5140c04102180100d0304090441c1d80f8040b0b42c604445e240440c80703000e55450034201c0d900440d91000c4165070340c0341c2c44401461880200204c000604000d40e65072010004c10000c524802403010000340880302c102c0350290006c01928441a051321040305030440076403021052469541881e810124034440140043d0030580c00d503c83c2120032250403041400d41c8100d0030310300e45440d103c0b070921020300f601c8043c09040510700030529818220600c112600c040e40240140300041c0070b450143d02504504005680000e400e12074240d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 416862868 1250 416861618 416861629
    0x150a0f020c06030f07110109080307050301140a06090b220803070b070201021204061805070b0309010c0c050a021225060e03030a2312130201080112080901031a030109030801180e0601030818 83
    0x40c3c045458070754880d810880c44c100385404c2c0280040c07089209434000c00110750040e00340810380d2841140c0c560307140f9140146800c522540d40021012504081c000190a4008400703003a055115a261030100c1d1034543c0c04078242c1c0500c0545c064039a40c0c0d01d01160015580341e00030108589100d50480c82112580c40382401d080e1a6400f072600802c0000400151210a211341510150035040c0f00070403201d191a020742e00c03180c411009000f1924112002a00201000600d1061110b0150751f80a80d450480e0380742035465500c545070108446d00c0300400a8174011041d5058815199260660070350401010095540010b01c1550308180c10001c459803501e15652580c8110200c14041c1600c1640d4400142604016440f004402c210109a6400120b5210031544542d900b4a40480d600e514981c1c0c50351400110603841398503619102c0c40600300b54000585034101c43d200481c0d498965818224a4103a401c40b1240d5070040d0440b00041c40020030b0742c0b01412401a007094803800d03900340a0f010a5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 416864118 1250 416862868 416862871
    0xc1306090507031d2d0a14010b030106090501031208070302042112090501090308130e0906250203071506050301020412060c050712030506150a0f020c06030f071101090803 75
    0x9000a860b502d4039646000d0000c100d444035046080140340c40d04400041d590648000c5000b1609024440c108030005d0320b04000f1001000d410030003c40b041010000210300900e10184558065400c0440c001b820300d0907845064101c9402c40040c1c0100e400d420001c643c0c00800174455018144c0c2440013040032801020000310b001d03107028a000c0c1a105904064001074880052071007000744105090085980c0400c0d0b410459901c256000d4580100703140c2000901010b4002c0c1c0b509181c0e03c0100300c00702100150141c0036425a0040b1204158480300032144000b468440c0005a4001c01100c3e002540240011000e942007a100250003501c880009081e6401640700250180019110340203111041c4500040c1100c6410024a86181e950703a0000312000a15480d00b819940d00004916440d40941c11034800007203241130f0790f0b5007442c00c0060504021090001c005214403818481103080200460740100008000351445980c1d200c0c0c200c0782c0b21312220700300c9034654841d40b042c00018503140146 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 416865368 1250 416864118 416864131
    0x2010201150b0d113118050a0e010b0f01050c010902030d020109050d030902011b02190b040f080c09010522060b0306090c07020108071808071514030103050c13060905 73
    0x240c0d0301c40056180a0039100e5490444e084140c08002c80503845807014000c09401402500113801c501500c0300c00c50059581344d000a00804640b100040c510009511a920811310348800300035442e040070010303080360824136500d6040741c500861a0034a41c090400390a0000110f800403d95100700d40c00f07c2c2c1061460300303000c400750f91514000003c200e01445000451000341c40e04009152854000030005211880800c2010503406110025500d0399034440f40940d00851013802800c0e074401c0c06c40600da1141c401c00a01c4da05055010402c400041850b06010000a204824990814041044824694201c041104c0c40c1c90203000341e116845c01214010907040140e503840b4600700c818000c00550003051000707034000421010340180e03002003445800075001c0ca0300130042071000d4884a8150015007052a640c0b268100005a014005080c601b503c4080d40c2c4589a001c81751011888900082c0002001a005403141c00c41a09011044070640c400c000400300e449551040744108840301654403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 416866618 1250 416865368 416865389
    0x5032823040501061e030b07030b0d05100b060a09030b0628030201020d090608040b0601090f0905060f0603091002070203030d060e062d010302130305010e030304140d17040201020115 80
    0x100002d109082c42a400180130265400714803d08044040c480740c0c2603400001c6c00a42a1404904400c1c401d50180300440005092050746580345d06105a6130500001c1c0c505070f00d4100205a00304c0e00b08076003542c0c035290454844988550031030395441c03403003980146100e400100001080e46541010802181080022001e440b140f80c2140002401d10030740010041c144141d80e40200070542e80000020360054001d80c540c0010740780c410040303400c00102da00c0540e8110600d800400c030360b041940b185008100c03c41d544c0340c0e8540c0d0078090011170b00045420020300c2c0c001041c1018a02042d40050040920007003d6034640403180c0710010458000b600140741c8260b88800f003000034180415000904d020303810034400c00c5c26980a4010512100103003103410590049010210f8428032030b400d90155a11034000e01020204010541d540d400440b802d5860798040345021048030004906401096030580d0b903040150794280326a6040749001d04128110b658170400340d240980d44400d07034800340506101 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 416867868 1250 416866618 416866621
    0xa050913022101081903110708060118060f05010918020f16061410050f0604080303091501170303070e010c020d060b030c0f0d0f14030307030b0a0605032823 69
    0x1c51000e0b00340c140c1250081d43d000148025140440c41c0c0c070940810340c546440c6181c800000385141c104081980481c04500c500800490144854101c40e070303004000350340420000d640d401c8110036022003031180e80c0c042410b14a040c0460a9a95102c002e9403055900152030202881c0c0303e6800e580c0b00c2d0f4840318800010301c40d1613040101038050422450340c0700c0c4c0c018550f07050481c40420f6400c15482114400d429944c0c118a540d1100350645004003c40015039459142c030300040c4e03407200d002000c00610500960300108010320600000709624007010300450455480120035a00c00c1c0da110f9116062210f44600e5400581d070381c103c403008441c8500c4002c0740a0307040d9002e0503d01160f01003940c1c880c0c100c03070045c5501a1940c00001c600580c1000c060405940d041c01c1a4a5401081054006070f00001081001140d0142c000340c10803d415100a80c1c51030356460f089a03a80000d0724014800b600141c51368007403000b55003002c0c0480b0151030300040c03962121088207584c0c0c18001e80359000c41c0a10b20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 416869118 1250 416867868 416867917
    0xb12090319020c1002151602010b04020706140c04060f030209060412052121071701080a02150307080604200d06050414101203020a0204061d0106020c03030a05091302 73
    0x82031500100d258001050303000c1318a44480d844006c0103043d01002c104400401c0c02c228801d400074030b001e1078050b004655070704160070010003602c02c021031100d8403201e2401150058401c04101c4003164220b03502c4001500d0385031411006503015014040e48600d05100c0403c45101e01d00241d9042d40c4a0002402d0b90060aa09035102c4d00325285109512102406140040c1c00c0988945803402c0d40c0358002c40d00f540c3c0e480019551032069202204580480780700208400c000080c4e080c9001d07000312110344242c1444c04403292544000c03100040052050800301e1100c1c107054000c10ba070f112003980b100c007080d640d000118030283c01c800110300500da21240c040016003050302c2800038003403032104a206a0f14014600c007a028282c1d114180f448a00390390007100f450702c20b00442c0790483c0e0080080c40625504c0412940c800312031042d400c4520a43d600000c2c1403800010014060680a0051410b01d40d5005003680c150300040c4440d6080b1206801d10350f0a0403052000380800301c0003140000b83c00c200b00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 416870368 1250 416869118 416869129
    0x605120603010612081e040f06030501080303071b0f2406081501060f030e0106030f021008041e08040801060b0714030a020a0803060301140c030604150b12090319020c 73
    0x5040c031402a4500501400058030b88080003400c19000313860143d540c3c010803078019400a884040d1080d61320040340100b038510b0034218400c12100d44c2d980911060b603e03486d9450306c0340301c16643d640c08030301300821008400c105100000809409400240c990381c010341c90b1001d01001000005101c078107202c5400344811040d00c0303044003402c030f0400141040101c000c0400d88088042c05040180101d410b04004614469084038182d5a0300100074802c1654902d015400c0f2a94080124810031040448000d114030840e50341b440740d9004254046c1d4100028a444800d42c0c00000607503101c0070420010813484400d000b180010117030005860740d2540c0604000440c082c0c50388d502c004981040085008075540040c4c41c407062a08000020b60303a80325540024010312020040390600b20200d0100504d13a80040d0243d846150195820b02411580a03030102c40c04599025101030320000380700c0d041080490445042d032024148040301d1805c13101120706a241c500700c20000005a210600110050800 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 416871618 1250 416870368 416870371
    0x2030c07080f0d050c19051513020f01120b1f1b050606150405030a030e010e060f03041419050c03100606021011040b070308090601060f0804060b0118060512 69
    0x350702912001e4008100c807078a44200407100d000b001408200c03007601c807500340030042c1d80061513101c03400004190325290f52a04d441514803e07940c000c0c00c0c00190404445007409100b0303907000b031205a0701c1c20311100640e013103c0305143c500400da941f140714a5507038a0b103101e516000c02c1d85107d40a1106001d002c002e100040c0e00c4542c80384000e0003103038500001c000080158201600b01d541d803822482c0ea11142c580d40c041e560085034144154480348c1d0074160040b040e4050401c0c01ea0b68503040c018030f042480814425140d1060500904100080200e40d038011400c0030f8040c1c28060b5401ca0301440da21103200c1101044c103866a401c00103070f102a51034100840181c00410745003c1c0051460560041d454151082d00d081e41191102c000f0b0034241c00e41012039010301b500e1951503448112508001f040420100c5112200c1d00c1004004900c2ea0300842c0000c103211030a6651146036038075640c810f8050000d070b0002c40c0c14050017610710528a1141d01d003150140c440c56030351549814403103e0b55580d8020 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 416872868 1250 416871618 416871629
    0x9100f0308070209011401020a0611070c090c0801050f0105090103050c0702040c02070e07080402090408030403020a0c06090602011d1f0e100b03010f0515060a05040b0309070303020d02071d0c091002030c07 90
    0x81b0103a440c041d60b60041a00c1ea019600100002044a0403501000603403190700401094500c55020210304500f0f16481400303006800d0369460342076a220000d114200a007210f086000c15003c4c014480158807940005600c500c84c0a440c50500c500350b4003085c103480310390802101580103000c5c10b018540f0489043d035400b0040d8540f08000c0d040c15004a4119880904054035281d130000c0000c041c94000c00151071401e91194000c0741180e42c4090042005900d400b80500550921040c0c000220540b0080c81a40c0c2e0440042d0014040290507401c555500e505e81134451500d5240d80348a012041c022528400742c0e82a01103200c0652400309030854a04c0f0740da03d00710721f1420043c4040900d690480d0500e4a43c140c9607965600501d05096515014650040c103d40703078008200b160004010407080c0460744641c00300c40c158200007030166102d0907075014105105412000c0c0c544402004100c0b00c2d0480079444d180d07854980d43c080410f42c541c00c3c0491540c0980d0001990626441c01001040002c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 416874118 1250 416872868 416872889
    0x21c021507020901141804060501180603082a011103060a05030a0302061501050705011107030212030c0f0d0b210d020d082409040b0406050c03060f09100f030807020901 74
    0x5000b5030000f04000d0060050000c0500e50200482c56130301d40c0c26190842c01a480c2c10242a4034007803501c00301801090007a40c8092100d00b02c0041e240b2440e0055406995001d52682d042500004040032421150074030516800b011081c02c400361007007071003a00000f90010200039a03031316182d002c1c001d5094169104602030b50185455001203507020a00e20b4112540e5071300d40c920160002c1c0100c60074011058003034110352a000080395200c0c2200c0007441c4c410b2094098942446450400300514041110aa10300e10f10800402a070300440900402d8400e10240700000c09661240100c0c1c10780e625038000e020351650041c2001d8000c0c3d82000101c0028a061009110503500704200504d81c0201030240c0016030500403000c5000b4120b441310341d01b170b9a0080d249091500d0281054041c80742e041d202035405524100201e00852007010440b445420060800f0f00d110000c48203000100300d00805591140d10440c5c0c0104039070382e03541e94400c021406402e429440300454010014054070603030000070200f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 416875368 1250 416874118 416874127
    0x70503120a05090d03030b060a0507060e07030b0403050306240d0608070b0406051309050712051f03020d050708010c1214010f121104111b060601140a0903021c0215 72
    0x181e02c14125616180143c8801e2044c916034503054020b00f0a02901d03603800b4002040b00310703105500030080c5c11010301580051001c600150581c3e45c07250001d000261901c4001d400203404607004100643e040000a4062040141003420705020300c4450440004407081c001400c0c0f20400342401940c001d400c1e510f010f04050341ca81300743c241491046110780c0d0309000b0080740b0f15034150b514030f42601c000d09840005100c00d01e04900000d10310f0350842c00c1030200b2445c100100340c1e407420119060180e403071042984401d07541141c0030803062a0071488201c1e031910a00d40301140300d103002e00403d6040c081d80d894940503010116491401d45100c1e040c0700780742030407090040029101c1008054102c03102039800c0b418542441c1030840c2400c0480d26195003203030900c811203926003820300040020300c001004000302c42d12404040c0c1d40303648054800f02c0c0000c00391018500c00756004001060529011300304401d0b29652030380450070070442000c007072280494080e6030909500340020458641703601440010b10b40f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 416876618 1250 416875368 416875387
    0xd030606050a0e0613030305040e0a0b0604030b090115060206010510110c010e01050f0307180e13110102010603020a0b120903032503060905040f140c0303070210090e010807050312 79
    0x180d02070b0180c40380030000c1c01030200c1c6260300c50500301d890719085080303c1480c4d1626410b01400300e034400d1251a403005036040003d02d0484851140070741c01d40d002814680740503d035465542c0c15140190000322255138407010b030740c0c514811442040040940d50040c12080d80340c14100405c04101d4802481400160740b42c800c1e030b501740031506030448030703090070588000c0c411040106c1d600d002e690160582100000284211160000840e400d920780118030348203029110b2442c0c500d4801e0035584c10340035600c01d00c41c243c00900340704610100214103200004109a0365000550a07683c20303070142e104084002803030154900c416408a6001012000442c5907051000750420b4071800c03400351001c4200781a4400c17030b40520981000c001001da022042c0514141401c00700750340d26003490100d500401500b001402510086059092200c0040155041822a40900545000301c2c0d04003c10090f924802040040e00c966405020300b00c3c0400a15450b814502030510f000442d6040c40074a217020b1114809 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 416877868 1250 416876618 416876627
    0xb0102010b0f0120030408030a1206170307020409060209030712020901080d0c081804090501020901020c012a021f08090f060c03040303020c100f0b010212040e04080c0a020913050d030606 82
    0x944401c04070404981c8681c507800d040d8044e47d0011240c600002684090035a0b0101a17900c03120002c020030000c20340d0b00e80c0c410410701c18030a0060000e030024403411001d403405502c0380b071020b8002c0002600d080d510500003030600303003513411a00000300c2c4d070b49481c2c0541c140b220219016042480c014000b840798000301903c010441c3e40d004240c0d6400040c258201200c42000c0d03007007920054020b0040400da803803d07901030740100b0006401032203284401030440d882030015130f6046185032881d40c4200903a1380c4181d4003100d4003100b66002841c840300080800d0090300c10391540000e5603652803507810400815400c0a151503036128840d846582401881c0072400112a00a940750800607516400c400d00d42d4113000d601c0019422070303840c113042c2081d4410550070902104d0001d0382982c820038548201400680a640109082212100002400100c000340107243c0608154101c4000450719400501403040c111100049180940b42c0303d0104a01008503a00c0c13040241014081380e82869001031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 416879118 1250 416877868 416877887
    0x1a090417030705040503010603030804060c0305010f050111070302100e090c0405090f09190803011701023103240e0d020c041d011b0908150f0402060c100b0102010b0f01 74
    0x286080c0340040850700c040c0c01401100c004000180091140e16640d04028098003c02c40d4140d034028100016100324501c68851207041ea00054040607966040800449190540d1801d000140c841e0410100c056514540303220725420581d540d120303400c52408244a0100806824401c002c1000d11080c000d0350b5440d03d989900500007800e0f90700d00d6a80000c01403410f401a24010121203417000400d0a002d000801141603402c072207100c1202540d81040c82e8201d01c21070b159804403000e05c854000703004020785005007155012014000382961071761034005007803510500301040140340c50501145c10b656400b43c45401e5001102a0181598842d006506c0300500d5a40700d204d5aa20066454601004400100303080009402000f022100325a005143c080e84104480441e41102000455080c00100c00144c007419040d40c100e99250102011504500a042281c0c0150709200646030f1040800803000322031040c12020030000d00c190000380c2110700c040345960007180402c401e080180d81140c81d90 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 416880368 1250 416879118 416879153
    0x20309010c0f0b041a100e01030f06140c0702010305010923220c050a050a030503070b06010e041103041a01081216051c08070c0b010b090109030804091a0904 69
    0x401c03900c49146040301401e100071100801c0b091242040c88140254240e00350b540c00101d004070942c64843c4000e01001c100e940c030a0b8005600041d0050000a42c5031180511300b03485030001040c0301c0c403010800311221404171500e044840e00401c5607802d40d070f4580107090041c01c817841c0800a01c424960005c4801c115010315a40c140d18110200b405900c01e080c2c18421703030303c1d440005942c1d0150381c0742007031120700c5d00d03c90300340f1035100224007040d035251400c203103411203900100441c90030002e0b0b59000c13108e040c020b010605100101500600c251600c0c080c1081018003a5610350340c070319051501d2549500003050048124145100503c860040000c0c1d00e00c0c0300300880001615001891010340c144040c08800420b00d009243e44403c40050361000200d01081315160103010b030359140001c50b0942a203a20181207101401d0040154495400041003e140e0626004041c1c5449807035801c400c2c1e0156002c9020729549000d01001c8258200960654000480342d1909a0820340c982c211070079030b4000007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 416881618 1250 416880368 416880377
    0x70f021215090129040b0f1509090c030f1816030b071d0307060507020f13090209090a020d030f050d15050a05030f06010506030c12090136030e0118091d0a0302030901 73
    0x104101583c505249501c1108014542a05010b5007608648260031809c411400b4050079804105044031001c1624852000344401c2c0003241c0d03400c01d500390314201d003960b8070216000b00316200c00744070f80140c0203802075401200c0c4124107040a000c024100319511003540f80e030448240104210796404640c410440f8940e03c1c0c015200d020b980009044181d03040e80095100411400007080b130f040b581c00042d40a802100e50721010b5681400301901d8a13501c0c10000c3d4050959404040020700500366032030b042e144d80c5855070030720401740c240c0e104645d0840c2c03089c40718120a4800b040541380c04068180a04004d9028185285030b142d90f0a0740d480c01805a83d125100120004542d60380040646003a05a071326000b00681c200303164070701e000344006565840c9a01508607200004102d1111218814681c44043c41d0b0131121600d0403107900643d1004281040002c03030303140750f507400e0200c00c1c1030240854200008a043e01c040b200c2c4040301030504c04103060b030400d56440d00401d4010050303231608882805d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 416882868 1250 416881618 416881631
    0x5060307020f0a050f070609060c29040f1101170c18031b13021c0903020c06040e1f060207140a03020603010b12010902040b070f02121509012904 64
    0x140e003031001c95401c000c2c1d640f06090711182031100004219601c2e5484005039000652078000c1110200035501400001c41c14802820002410022801d8400d07094441e040e541340e8407420212110400594080c0e440840c0004100700784141030541b081144c4003401c0070702d0748586007580b40e0303190117000f4240c460000e00860106080003604407885800d4000a080d00c140407603180b0403041041c5041e402d10f001d034a00805a00481c03e9910854600510158820005440000f0301e10040d10141c00c044003107008400c2130b00345c0d689900c0702400140070421041e0005250540c08421a419a0400c51600412108080100381c1c0c02003105011b50740308040403601003900e40003007a0441015400250030000c00400012132140740005014000110313810110640d90701c0da004030503030066004682e9548802c104800000301ca89142c048050301c00b42800b42e49a000060709810181008c90848901d8000304c20010303c0308082c0f1840c44030b02501c41c00360400042c0158440e49050b22100068001d50342e0f101c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 416884118 1250 416882868 416882881
    0x50d0212010912050c0c030601140d0507030209091b15030f04110a03150c0903080d02090d1e0308070807020d0804020102030d0507031b0518060f07050d020c011106070207050603 78
    0x41000b808240c00a0b803105404410303070801085503101c030418290b1401050441110307403030049841412203001e0600ca445108030780040261071071120750111054072403804008010789a0019451017125191b000e8147d0f4604058030500c08400c080c0d070700d8898041146072092040c03000c8141c0b070700940c5010355002d59039541d00e000903066081e0040a507001c1c003c200000f040020b0000c106030281709029040c400c3d010401c03130980716000540001014a07806000c01c00b1003141950143c448081c00908124504440b52140250b0ba0012050242c244462241042c1032540080440390060003910f801e5020745091031740203442c2c40380f41c800c0000300000c3c4030216081d68030070010795490f000c4032501004282001c400140081a9601065038040c0010713030f6040d034040c042c40a0b101c654030b203a041651010303180410040190b104c03200703c61000074103028550200b1010071490754540000d4005001a03245440050128644403118000d02d0b03100c0e20400c14180d0380480c2d0041201c200340d80491701d0ba26080f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 416885368 1250 416884118 416884121
    0xf14040b07110a1d010609050105120a020307120905161e03080a0c080c1b190b03041b09090b0604020a02100e1c0c1a072003130e090106090204050d021201 68
    0x1030384041d00c006103200c8014012402c500c604c034101c0d02103403502006182d8440c01900d030303405403072005460046a140021551907298000b558080300c0d920307040c941107204001490448000b548140c2e1558445080860714448407030500001d13107203620800c91211409038400314003400c0340c04002c0c2401c0b000304102e1005c83c002d8043c40f503590f5000200648900078000015070b03400c0141c40d2020314440c5164940c1ca41d0038a124500880150800c0d00010541491800c0c089507001801c122103d030030280b8050001c8002c840340002a18060901242104070350501e08003140020345040d01ca5403041050451840e00004c082ca06021170410118080050ba1030644c00d001c01c2d403104100425210b10946441d0782d109520700b0b0040d2160b2044448440349090b52401d80104440d01008107940e44003101030051a1030302007072a0044c24044914240504840d12014205a44940d411440e840103021146400703005200203030070701d482c0441c149807802c1d0020f41c0c2080d11200180c02541030f03540d500b84040c000e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 416886618 1250 416885368 416885389
    0x50c0a110d0b04150507030c05090f120d050307080703021309150504060b0705010f02030105180c04091104060e03011406151b0c01200303070302280f14040b0711 71
    0x100642056203003d0505090081c045200c05019605d0302c00020103c601900c00c0702002e10090381c2d42420003e000c0c00b03200103400300e00c140e07503481503003041011200da20400c0200c0e080c1044d6600c0039201d08003100064440f9402070424000d260060000d402c004400c520f4030000c5400c1964045107840c90070307030f4010754048650803254020741481c00118003110010010610144901c0007080f6500a0790240002c0307010a00949a10090507094034000416000e03220350081d140c0701c466482c150340c82a800049412200c5021000e041c049010000c55800481140c8040707801d5000b0302c0911680b211101c0340d0710006041e00e1240e50072000000041494200343c0b9511100d8030705044c985055006110360780d02ca215a12400078204030f031102d200100c4c2035110b04011003420011b50560712002d50681c0603400180000791850760454201d440403014012580c000c400030349440081e500100c10080101c5404502c00c01e04000c1000100042c0d515201100c648503002007220213207540d50400a04c00884c3e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 416887868 1250 416886618 416886623
    0x70516020409061e02070807030507230c0a05011d04020309030403020a030c090b1c0308131211010606050903030306100201060305070b04081006060516030e220b01050c0a110d 77
    0x81c000a6004002c1c03c0c0c3e100d03038044020030000008040d028500f00382030b44910704009100400501100780028000c00140401500c26955040c0700c0054200c60a0b4006681c1e42d00b103040e60014403501030030f040c110312101c050b040a20300150700f085004444041c032101112240e010b95800400200e118001348141d5001e951b005060f014020b50305e0802c0042c60501340100c5090610702502040740d03150510111105641c418451241541c40342c80c180c5102c4002412900f83c0000c1c00044000905100251a00032000d43c4907a5400e465000e040750850b10f4a8001d102484004c01c0392425695000003a03030380c04034045801010044500c401240906401d920040c042d1041c41000f180840c02140900142c0d12030f4406c41d110403012510002c1981c10610815020450800107203d1804e056129509074600a00b032508801c95050042200040200190340c40c00c548078881c1ca4004034180203c0ca0001001d10b0302c90b06280c000080543c0b0f0b6402040e008000000300d003c5144540c4810b078a0244064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 416889118 1250 416887868 416887871
    0x4020c06070f050d06170c01030b090708070c02061b150105181003080c031b030307050a23030106031a030a030509190e04110102060907032301020c01020a0c050609150705160204 78
    0x280c1d10304440c01b40f685480d4090400340180280611554403a214020803034100030100d104903141d83d08180c85805014082030b04100748502d0607405070729440003d05819406111007202c0048024a0a0400c02186032003c040e06030a00108480e540b0b80300003074481e0042e00f81c0e403070351515000b2640081d20007641c0014030b9200042441103003840c1c00310191600051010241c400981c0b000c1a460310303484215144400308005000c412a55480b0780207001e00f4504c01d00c0922103101d80c0305199406900268000c1000980300c15031034040700d0f0303981241c181c0c2000541c014110f882e0300c2e503030240180c0182d00c60240900481c0c8625040d04242c0e45039035005110f6062807924a003401c0c10320082d50760001c555240503100b05804510181c00000d61401102d4000300700700d18480b0505002d120000c5905c0744da5010390340074804890294028801005160301503281d500c00403d4515201d07080103c028034003a1250044003505c070b50025011010784e44440d0a00e0b023282c0d2401040700040d550024480003035000fa = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 416890368 1250 416889118 416889131
    0xb060705010603030201050108060a0c1e0c05010516030e120f21010602150127020a1403010b0714030f03130c12050703140a03120506010323011404020c06070f050d 72
    0x1601940f0540c16a05020700352602b5070b8450162206071048564501d0008820601156a1000c40c00314601c0e92a03e070f240c9100500b64644039a070035070714103444d449004406000d0405c5e0058040c0314100d81340c0180c8020701141294981c140303440e8026989041c091010001d4041110703015103403544003c00c03010518803c0c650312024000d58034045940303000e1451080400200c3c0c0c488803024508540070034084540140d02082d08103001035008146604180310b5003000341d101c502a400b0103580600b00300940e654a030751003814060b81c000103c10b08040d050300104504561000c00c0c5007140d9010b103002d450030003045014034194120030f0701548211018800703504613004000380801c0c1d91f411640030329110400e04070040829034a030301d12128010081421508600b004440c19080070b07a02240506001031045a60280b84420000070b030484010412031750300510615403650341074190074005403000c600380319880c1006a0703a600043d10080a200c2c0c8023200b04101c5200e901110301d41102030070140000b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 416891618 1250 416890368 416890373
    0x70905090103150b120a1502130602060603010b0402070c0614040909210207062c040c11010f150b0304051e030c190209010303080c0f3408030105040b060705010603 72
    0x142c007003840150b0343d040d080c045550395601d0300a10807110428548041c00c81481c00f9620000050820b40c0055003a0341c0a12401c040c500711f000d0703400018201034015040cd0320f001802c00d4211000c2d0030000e8030582c810b21802011802c9201c080c001d550302400d100c0c4940c48050b030b140c90710b40600d82c0075008150810800c1d01c02c01941d071502d003111201244400d01e25000d1400c05a88448140c05454000744180f02480b000c80c0e01108000c1020300213210f991040305200c1c0c0410169481d41d03041d400031030540300440c4001042441120b0401d8000726040141d0880b0600c0c07161521010300c070b004602e20303010012074280074081c8107010072401001c00011840110012494981d08803024000f002d014010201ca200101054080340296000b40750003016802e66401341d5a4075000741c44050f6400b01400500c0244c2005801892801b0030900201c642c607810210001d8a14040010042d017014103000c1000041c00c01c10607641510b40403a030100300405200d02048440c0900b200c0a00700d9030900d40000213 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 416892868 1250 416891618 416891633
    0x30304090903080603060405280b0108150f010b04030f020102010b0315010f0e010302060d150b030403031a030c0a0b03090102270f03060403050d090c0b1c060f1a03070905090103 78
    0x50341d9101e03444030481c540d80c01c4101503c80004480c0138000380c000e00c018060421b600d1541c041c40070407203040070959070555290340144d210240c0000000381c0c03004200b54021282130b41c1b041d40c0211145100c4240e0b41c10600d11030258099840001c2a1948007030307500702160b0003034000c22680302002c1c00300c0d07100102d910070f4110b8012080c42045000c034400c440204955030303088125416290050549450007255090b654010300501c50720742302c400100c000205103041c0800c0214010b41c0650390225090034030a0140c40603030860b0b00b400e07100707501422003141542c950440d80740403200700381c11042d100e551b00d003600da01a2140240868559089031a0452000f460500d101c52001c0b09440c0710781182305032010305a450b94283c9015000c075800344804c16030720003190480c1d1441c07031107041c007000c2041ea20b102004083e0010040d030b81000e47c4050b00c031101c20b502d620079031000740f41450919401501d880e0b0760420308100c50444100b031000000005005a0040301200014480904010760320342e56800c0151 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 416894118 1250 416892868 416892881
    0x9100f14040e1912020d0504170a020a080a02131a10020c04090309080d080c0304080307030908070b04021008130618170d1a0a060c0f0209130b060604060e06160203030409 75
    0x8030440e044244c00740074284005403011248400c0e8640d9850a801c042c0080325135420142a403480e840350104103c0140c4444020400400104006110354006441040054070301403120702025403070003c2402c1600300042c00740b26010b1064803090662030701294102e042210200407503412070700b04106842010745c0585014100e840a005039403000c00d407420b0403a41c01e041600c10452030300f010f0001c180462105c400940e00000302c0c0c100003490100070f0307a480701183c0043c002628983d401c00104030139403c1040c0030300d030030180d07501c1c1610552802c2c00c424040446001e4000d030200b9550081c1e0241400c2102a4040341500a00c0034000b030b808400c603180035a4010241d0070320450a1070340440c2500d01141104002001c010200c10550b070a01c4400c95400c2c0d04600240ca0f0302c3c0e0ba10403d1400b40c0c0780c814a03180109102a038080f51500c03181000304140358040d102d035005040c00c2004102c419448550343c8070702c5200700c0b140c540d00e64a01e800c2d1000b2000d0400e01030360602000500090000341540b011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 416895368 1250 416894118 416894123
    0xa0f0504110306102106030308010e13030f05070f1e05070902040f06050c0a140f0d0513150207080609150c0a0210050a06091103010509100f14040e19 66
    0xd00c031000800301c01044500054076000c4e00300c0c01100740d01152074000d120a064500765845000000360305444a281500d400e03a1040d0b000c03410520052010001e00785d03507294014440030404165095a5500824960041080c20200207010641008104444200c0030790076030004a11000b03035542e2007100d098801240310484151050b440c0c0014800307480d0003982c0450300b00360904031a05140c04070640b03166100c0b0000c0001c601401c0d14200019181035007501c141d4030454000d0206020398440c5620b003050034940f540a101040c0103800022030700389400300c1510704400c807400341d950a0b003030300703070305e8000c0f02c0d0070507001d500030081048202140000c802048209044415215489a021000346449652000001600a01c0c041e110021550700029000b0b00c0040c00020320703540d19840c940441c0e6003410a000c800800000403c0a403800050307444d003080b0100d400c0c00005140070041d84050320785225414450300c280b0111011030340c850348050114241c03071040d69500c01810304001103c40382d00804 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 416896618 1250 416895368 416895371
    0x402210106020f0a06050c0f03091605030c1309050a0b07020d0f14180102030d0f0905010c0306080d08070e0a080c0a06020d02030f030405070807061206050301050601050a0f0e0a0f0504 81
    0x1d24184002118195102c0c514003419809445450b001c02070711006010402001c82041507209240258000310300c0350314a10040c1544034401e0641034805203a035800740348a94003842401e1210f5a81c002a00c007001c840100c005000301031860142c3c100010340310301400300103ca0013003001d060380202d21100d60141c907949445500181a0301030b28610031a01d5001c2d550a02404070308070480b06041031090901381401100e04001291007118160781400a00c4005c1a0f1210085810003000340110060241d80d400c0911070745013498609a030321034080c1110070030404101c01190304207016009008501901910f030042c216200c0783c0b21540e0340310f88410140101d00c29040001c91520101c0c1c5466240040d078040c518001c001c9040c0451500060000d40da01c0c006c100c000a030403001084010700a0100e0307211880c100e40302d1082242202c0c0789070703c240e001c0d0341071404000c401c1c0e0b4400304648031884903061075980120050000c940411103619801d401c00348040c0c010030348450a01e074079411104210350 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 416897868 1250 416896618 416896621
    0x507021c0c0305010f1407050a110610141c0318030209010b03040b0a050c04170708010204090c1206030503090d030c1505060f0319020904030c0614060a0801050f06040203100302040221 81
    0x305c085030700d84400219850b10460205290340c0c407503002000c00d0322183c60040445004118003a040020035928000c403204002e004000300104210a290010030803900c100300c04c904020f07850b08208150b140101000404250032008004640005000d0754000d010b40101c1e68407507503c1c1d441c0390700c2a030b0295103401c0360100040d4004001d000d110301ca840681e020f44d04151030196030358104031420315100d200380215000401c0303c40302440a0710040945c80c0000c150351840b0764004c0d0610181d00582d1201a00b00102400410310000803543c2c1508103403074107203400311303141403c5504601c0c501c002821408038902194030460b41d42c1041d030082c0c000300c038207490806246041660316610b21070000c40000803182c00d440980b030701c0b8800c6544030b0300038100000032020301d80d2200b00311080e01c0d4504e0659160203003072183d1404e22142c8200500340e403100820017800c00c00789450380200000d004601c15900003000400080340310144500555010f0400d40d100c0101d580f20717a903071000715460280f00410701c40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 416899118 1250 416897868 416897891
    0x901090b0c0a090308130518010314240a0e030703090819050709020706270302060a050c0315060405060c0601090506030703030c03030509071d07021605010f0507021c0c030501 77
    0x219144030040c3c0d19012034291840e940d4a1641e00300c004140c400842040c80081c0170b854090741d0002111404c1d40400b000c3d810340c6042e00c10b0350302a40c90800705900c420f108045985143c1007050340440070003940300c0e655803001001c102521a50100401502022071401c0800d03400250300000c0d80c50040c00c2d26040800c401ca5049054040c070300141032a4070000e0200b19070002d0341c0c002c0403540d00600000c2028204512084000c62000110000b180c0714100d0712010b00da0306000032608110038003000c1c0598100082801890702014106030b40341811640e84050075600e03001200d004000c0504500c0d02c0301c2000e1002910342000344181e03080d250825001803c1c80c500800e58000740c3c0d6047d1600040d40c00315450482c02414020040001403148580c0840c602d02c00d00210340852042111120b01803a203e8002400c1c07400d07540180b44844039144003401141c1e0880c046148540c55441d00c03988440341e40c00002d0b2f05044e40d40c640d511401c002103007001800541c1c40c40409490089000703010010011 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416900368 1250 416899118 416899141
    0x12021605030c030c011d09010e010e0109050c030403031518020919030f0305073210090c1a041d010302100804080d0b03010b10110d1b0602030912030901090b 69
    0x45480c2d82e06411601072069103601400f05c000104082e4003640d07102030241ca000c2000e115007a0014903c04950300b00402c40032050f224170502400d8103c4090120b414003800340e0441d400007030710090601d902d030a4180210300754400c44100030010718200d4503c0600160040000354014400e031401a0700014442c00e0782c0d10f20489010440303038450800100c4444585040f12180c200b44021585500c11a1042e0160400440c100742108440d0b08a4251441c004681d41d181050108201000302c0c100000c260209011700708410480e00c4000b0100c20b4000d440d0301c2540288074030341000b00c803546170304103074024814000e04040c10b817071080d43c80c00840f44000d0300c00e40d24850102c40040c07610104002d5480101c080350400c03004120064004109400b0340c0c40022405040e50f0039000c00144c00c011040301c0d4030390802c003031200350105050001c1c00e1882d03c0b8014603480000c080160003180c0020104000c40d2041050142d1049049441a2203080005a06010f01000d01041d100c07810783e200490444e0325207 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416901618 1250 416900368 416900383
    0x1406030c0904171e0a030501211104020d0e0312040203160e06061b0a0302060a0f0204030f08090609090906071e0507021e1c0b130f0f020d1202160503 66
    0xd4503c078440b10720800c01e105030703448282c5800a03200c0210346002c00703a0882000d0703c2d01c4409a240418190705200710b811044480c08824000e09071000c0c01000811040c0444111034101501c015a23a002900340e40000341004e501c0703004d0244800210401d2005064158034015842101981c0c8502920240384169820b90300a0070840300ca1180880c5c0d00c0d240400080c04560308900c0001041c0441c0d82406d414010503030030960143e0050310030803203640518401d10158842c6802c046061038195244d400c44031040f00401418030500046442c1c0541c3e035042590b9a81000800c400c44030318142000700e8507100c096031520b01094480aa0303415108181d51520000882d0b40e82d26402e00000d6003c00c054008901348400c41030b050341c0c8012085480b8150300394004090100c42001007004c1d4540f4185a000041c001c42d084584850350200003003100b00b10b4480070350000c0d9002010304040c00015403118941d1802001c0c001c95804000c0305c15004201400150309599a5046140e5200d050584800d503 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416902868 1250 416901618 416901623
    0x305060a060f0c2003120f09040203040807061107140105011410092616060c1502090406030f02031c0503130804050d060207022d061c1406030c0904 65
    0x1811142400254414502c0200503040c500c1c10380d103641071079150364004041e0f080c081550207001580f50001d5040400601c14070005001085180031450100e80c1524010b0444e401d106680002c0030074240a01c10003580e0841c5c1d040380081050345444200d01e1602d90100d002104c0400c4207000c0007058410611507039040715600c0300120480c40d100703020080182c400ba05e0354014444004400300344039054845007103028a1107582070301850850105545000b007a00d003480b690fa000c106090140f1035112814020f50350f0700481c540d0488507581b07a0b07503002c2d004070030503280c000349410310002c18020601d00c2e030b14004d0b00903000e44080c1200c82400d0240004800d1202010410410100301d440d1039031094035202074060902c50741000d03140d40000710b1f01034585005039101030b0007041d100c041d0700d0030300030b210811030002001101e94420b40c140030074201d605008007403040c00e000c91052012030004503524070103958864200014001d62000c0c0c2c0c9024000e4813074901074881c0000142450825458103400b41e81c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416904118 1250 416902868 416902879
    0x90709090809040c030f0c091d190504050a120c0b01051e13021608030406060f080c0112091208250e0405090109080309010c0206060a0308070303050402210319030506 73
    0x3110b141480060683e100005040544c0c43d041628150100d2049043d0007440b43e0307404c80007a15051424880c1c42d0074104240341b421140d810b000c2200b0706054801e00403a401c05002c0382a03500d0f4200700341010307940800585220410282c6a0100303074004010310201e84503908910044c3d0300c1e4010f11540a00d03000c0b404151510b4400100400c1c80c0c44000c5c21750502d082e010142c03034564080c442031126000084c080f50444408802d03c4100b003151701440c00a400d4a1950954040c942a105655004028149030512084010341c4101920b03d4000d000c1680c0c204607403081c56440d100004103510001c0364501e246200e80c01d018031800d91040a080b40c01042e6a03a0080803920450030040100300c01380000700f040d980ca033403000000d0104809940b28400d02d8000181000c4c145001904061380240000e11401214005000003000007043d154166058036000655036118404680c410040038045458520a0b9040740c0110800100034003101c0e1000401c280b110500c40e0042c1e05554080d990283e110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416905368 1250 416904118 416904127
    0x170a06050c0405041d010c050a0f2111070201141c0e01021308030a08100e0c0c0f0601080307110603060906131e020d1404020a17010902060a080907090908 68
    0x81168200e180c00002100829141c159035000090807160b4400b0b81541c0201c0800030314404820a01c503000e80c071070b11030403c54a0002c0350b050003804910741c13003140c01c10712441d81c0d081642c1c0e95030f85483c808440440c41c0100700320034004c844058981c02c160000c80c00174280c0c03030ba0204040d54000540707521240000e0790014540e6102c281c003020b0b01a820900d0001d65082c480c04140c0304006014000401c4000081d41d030310221644010b00d03030300000b81041c0038a104038074104050420090455440142600340c0c0e038030707105031000544c00c06001103c0c441039171007448008109002c000c001894141c0c0710b0840c8100007071025040c0700c040c1c00100e900952103802d2400180083c10304442e60500813022000008540000c10802403141c4032800b861892181d0103e61802c1d030401507c1352420508644441c1d85281c541540090a469101c2c010015120541d920388502c8031409d4110480301d0b58010900764991258001c020080c0500720742c0303481640300d1110009184080e82c81034540e45a000300340c05191 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416906474 1106 416905368 416905373
    0x17070e0a0e010b2502030f24060a050d0314071b060206040210050c1203180105061002070b0f2a0f0102090d061a030d0216170a 56
    0x2008500043c0401000c800a0b2000700114000d4a04020300d0403060100c02d40407008000d4240c4a4403a940c039800c0804201140032100c030002c11501c00f231105d994801d210405a8446400690001d801d0016007021072000c40202d01078105016406624014003d040e803001c40285e41e401d03140040c007044011030026040050410f44000c00081c14280c0024407030154002912051001c0012280d40310038050180100203440c000ca0951649441424503154410704c06902402c1d500c0c120000c1d4070b40c5040d6021000c8408540d000307041c2070b400c02c61089140d60207509601e250740418040303500707400b041e03081f00124810b482d1011000301c111038140911b0404c804200450590040c00700c00500c1e210281800103840c0c00460100e1311035160244c0f4440c000d0505001c50309400340360031502d01175400040c1c403401c0c88007001c19508030603031750b644001601d41041044500380c1c000030000f101 = true := by decide +kernel

theorem cover : BRFrame.Cov 416726618 416906474 := by
  have h0 := BRFrame.cov_init 416726618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416726618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416726618 ≤ n) (h2 : n < 416906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
