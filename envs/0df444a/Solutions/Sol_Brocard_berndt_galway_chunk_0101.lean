-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:51:04.848543+00:00
-- url     : https://prove2.me/submissions/7fa2c190-2891-4b5f-977e-f13dc680128c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 17985618 ≤ n < 18165474 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 17986868 1250 17985618 17985623
    0x1080705010918050612120702190509011401140f0304020109050103060803040509130609030804062403020405150a08030408070b040608040b18011404050d020609070b090112020a05030103021507 86
    0x26020720b00c02094000741c0001c0d071300c040040c0051b0045400b0aa40b1858100c01a014402c0c422000c595042103107852800c80c0b240002c460300100e2580d0030080002c20f08001840b81c49210006040302e9401039020700c10001890225060813500e948001c1c20f250620351048170100d00007041c0c59400316140d07010b07225002c02e0303c0e1080000c50a10b0b0506040c081c0402002d0308c110203800303500c100100011114051051802d00c60b135030f01c114504141c6409000d031841000842000481c070907a4000600d10500c401007207940485022600380c990388541c1856420703015455401039980ca2010640303107000401002191242030443d420f0381d94070307181e00845028900845000076541c00214001c507505040e103e40001c000a1343d84000001044504e00b1560100750b404440c3d01c0d0502040b0600005101d00c80c04855180081d01451a001002d9501c40300c081c0558287c1040c00700d805111a442108114100e0400314400c643d2001c09107000740480e00244000c0388200b440c548040c00700300c1000b09a400d580e6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 17988118 1250 17986868 17986889
    0x414040201110d1209050708030a0507031202030f04060506010e1801081e0a060b0a0906030303061505120403050307200106090c0c050c010302090f0d0c14030a020f0d030e0d030206010807050109 85
    0xc21211320009040c09180c1500d103071181030f5001c00c0345081800281054000b50711842d943d0f03402c40c540039160b201162010418a0300c14800c02080360607031000607501c144c5c0002d00080782d546290068400c40005001141c2002c407034440c1d584d5580300080014182d8041030704070380c2030081d030800c3c116104040810060b1941c0001300d0705400500c65801454494000034a5460f0581d1100110001c4511550054000a4a44108105000e81c816080305050200e1074958a0841815040c02c1c41050180c001800c01c41c0020004480324441c60a403440c0c1d1510030f90800861001a52440c0a06940d006451485180550340c103400d50180701e880b401030b9803000c00317061900c50703c80054000b50806486950004800d80d903440459461800070b24006104004445d81d803800d10454001d24800101810302950040020401603942c00f500d0b00301c0102e00b2100c510300c5400740c1c0f8048a074250454040c903046014800840d04154010504905032082c0b10200d488140c0d4030070045a5000e914070800c800d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 17989368 1250 17988118 17988137
    0x613020a030206070c170109261606020d06080c190303021e0106090609090501050702070b0708030a06050607052802010504090e0c060a020304050901090b0306070809010b0414040201110d 82
    0x40c10300e44040c014090040311085c00c110ba59840a003d0281c000700d1700d0445964032401c0c1800c00800c1c1d02c8032003000c040721004a444080359044003c40d40b2581000f030380c0c8151120724030000c000450b0120340340c014560b035051040380e980300840f40c0d072441d80000042c030551000b0b00b00d4031441c0710580300304222074041d030080071003a031101d000308021400c1c20380400300340d5220304011400d0a034030b004a400512001c0800940f003012410300d20308590000d0511411904864000c003d20341c109010b450045130000d101c1070b40c0f40c03034a0608a0044c1016845280c0040021598000b44a40820810481a400002890241c08844c481c94422520240090101c0c009120503c000303082c80d0300203800038164904991040038600d000500369000032540c000180d0000500f4411820442c011030f0040c2400b92041c4800c1f48070348002629000010a003e0800000d040010144102508048542c01002d042000340c0d1015019401f002a81181c0981c04506100400e800380d0500099200c50441c6e550385140d000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 17990618 1250 17989368 17989373
    0x90702030a081005030d1101140105150901030207060c0503010806100506070b040f0212030a03060611070506031320040c0c021e060d061502010506060f0304030e15070b06030613020a03 81
    0x2207040141a9203101c000e03000001c1425101080781d02c6c111202038139007007002c0403202495400d4a0300000740407440411900100140d07141c030303101c1c1c405071040c10b0802a1200741c0600100d000b400b500c07401808050070044000c1c0f0290b0004020340c103a9001c00190351a66540280c150b1000d480b03480740940000c0208403800203e10b00c0d115150300706115a0a20801c2862600060100c8074200d0382101d00d6000091034072411501481450010222130a06038015281c0c041d40d26190880d92094030701518000000403e400c1001e40d1404816a0001740d07481c6031020801c60785240e81d0702c00c590b140100e14000c00b40c9481401168080e101e90350091481d4018419408030307036032191b02841515001705051150440d0031201d8000c0340301030038070342c490b082d109007001e070009081d660040e000d64021402000b121840c0106c2030112903005800d03080c80c0505c80b644001103010800204050344c100000814614100483c1612250091500324101d540a4940802c0070401c940d14450003548008041d200300300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 17991868 1250 17990618 17990627
    0x2030606070515060f010215040213150f0603050c0708072d0602070203010c0c080a050906040f0303030c02010b0603090a0b04020301020c07060206011502030a08060108060d02060a0302040311090702030a 89
    0x600510240c016400d0a0351a5207003460454205500441442c1000030030801d41408020306a84040902c000c00100300c2e1a00201176003e805800a4081c03c8212140032188120350801544e505542d500c01c00e0040c0d444c00c8400781040540a1040000c1c03c00c1c000c80c825100c44020b95a802e50407005075860100c140e640c0815081148080c84040d60000c01e0b0080f0701c610140307a00e40c1890250340c0140c1e54103840d10403d030848020205100030f000000740200040f07543d032070079a11141c0d00c906040317589001c5500065600d000d940d100200078250207601004140d4143c10250303030850190002d100c01004041000340e0b6000840300c080301a071003000380c0d9021079070501049410074005400180b170715603030f100f2860410015820020143e4084001000b0308000610028140455440a142021a1b00344000e02000d0003a00c0e16041004050101c0e6441c0e451007203490100b1b0380142090342e03849003d9000b80c060b41040c44103580b01000344040c071802c0d081c022801c42c466005607018516202a48900fa103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 17993118 1250 17991868 17991871
    0x90c0f080319020d050405190308030c122508040c121a070f0e060703031d010b0a080105040206030708060f03010606030e07170330040f170a0206070807020115120606050d050d030203 80
    0x1801107400c008c000010440d41001540105445040c0996981e14900c800c00e940402401c60307540c030410440b00006a1b13000442003680101c1e98a0003549640301da003405000c080d007981281010750140500c540820590071002861082150102c1c2c0d415a1841c0c02560410701c2c2080010108007110381420140c5480300003007015512074200011081260f00c0605852000c0310100d07013842e95103080f500d032a441c007076124000512254000740402d26183d4046540c0c2d000161619060191060100e09580d071035441100728010301400070005669114401005008071100180060007540404a035044c0748180b9442046200b100541c60078140d4130108180d1800b40d2071303001012045400704607505100c0b12215000e54054100b0080c0d0034a1070074000b846001a84c20711892080800c01c070181940c02151315603200740b081c1000c1009170f440340c2040c1d024000c00c15080035030390347c04e40300801c182000380e0204204500034402000100c1e00c880c144890307801c506d00c014100e603201d030222241d114440e40095 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 17994368 1250 17993118 17993149
    0x501090c0206011e0902070f0209061905130b06070302010b011b03020a0b06030a02060a0503040309050d21110304030606030b091f0b030c0409030302090f03120a03090c0f080319020d050405 83
    0x220700545d90305000022600218422145403002150701019842c0545640340c00407070880710245110b601d140c4200d020200d80c071996025407400c0200c0f100780807680c2d0103e00380c00800340c241c40d41d4058501d8001e00030039200300990f0201e401914007113240d280c403c4000e00c0d107030341c1500141001c1031191a1103449850041015525200302c880d01c000684540380988024030050304c561345c40342442e01c1d0142079101e55800c05030048a40740c4e124004500c1c81c001c003080d01d5928100740c444c3c600307444d0030445070f076102040c001e0540d101c0040c00000b017000580c094000c880c02000d540030161680302c030141e1590054166040038108200c0d107046082c05c00ea100c880003c0c1c00070704881d041c81030741e0081800e90300050001c1d0080380c0d020804110074100752400141c100800c8001e440c03070100042c940081402303001c84013404c05507654042c608208208440d44007900e010344d10203806aa6640520741c2e41e0340b04940800c03801c141d0661904005000061040b083c10858907a1424681804144881c0000c99100b8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 17995618 1250 17994368 17994419
    0x304110d03080103030f0309110f030703060203010f0f0902030702070303140702090a05180d0203160201050909040c03290601080a1e0b01090503060c03010308091519030501090c020601 81
    0x6454155119525000c05901c6078036050429031450501900c03134031102480300203260801d001400020a17145800ca449441165403d20b120b09800109241810b15080200a07510000000c514680e9002201c0102d82080d03045203292a102da05590607808150f4610015920103e400c0c40002d0058010301c5481c00d003168020b05282c420f80000701700700030540b07a46400907a40c1c030503c05500c04442c182d040401c00b00f03000f45494007078820300035039911904500e002003103041c0c0d82e2102160300c1281165103005d00200102031600341810001d403500418402211700d0442071b000c4842401840341c0502071180710304860520303036513200300640381180b0091031702e091280d881d02007412164001c0301001900c0444a00040c2c8150410000f50449080d44c006a11a138000700400c448060305500303c0307040d41e5120f0701160300c84a042010030302130304030300f0605051580c000c2095082c0a030008000602060256024006d9990b42c4d0000001c03604420507610050b0004401070101c804440c80c00042036048410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 17996868 1250 17995618 17995643
    0x1021206120a0605040605042a0b0c0f0709050105010e010801030503070b130b0a0b03060a1e0f020c071512060608040f2108060405070201140a090206070c0b090406090605030c0103020304 82
    0x5039041204d008440c22507800340c0c2c800c280420300000710803044801c1350b440e03c0c01d200709100304140b0a4000c890300c2014450a400038401c6030002c03041c8603050b09604210708480c0341e41e03160782216020304801d01400e8002500c2410500e12584205001412260000040e62600200d601c688804400c01006e560300a4100c4030910000f50340c40d840c851050015800006032210603800301030410384050515011030b803c01c04c41c110001011419240302040c2d1020001d80c0b40300e254904006401226920b416500401800150041e1a1840c2c00c2d50103410f907480088074030454140b01c0803516180150320014004ca030019000441c8881c829820710300641d03054100140e0340001c55500c1d44070100c5c140015040c00d0500c00c184c00d0500403550041d10300e0000307020708105205001030824008103226045a1240180e01c15511484110f443d80b90f00849150b0300140ca8038103845041d4440903041e4010b0b0310340382d400910030b80c11f40700b11401d654008018113140650000114043e400251042c1c07070347c0740e4a60 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 17998118 1250 17996868 17996873
    0x60706020d15030506061203190c050705060f030108070902040b0a0825020705030105090a02010206040201050a170a0203010501110a030504090906060b04080109020307090501080d03050702031608190201021206120a 94
    0x4062070003c5208400601079490a80244045a13240200701e0b50241e00a0103880302d181404809281690058641010b10a81904000d07103043c5050384820b40029001920001d400c60102c000c41c183e483c0d0408545440303503603103ca03100302d00c074600c901d44800c4c0c001e01c5080e042d984103603046904007280740d50040d0f02038a2050301208120441e80d0603409039010321000c002c02c2c00c0c00e00866512200140c090100e4080c03030b4002039140c40000f4402810480c000130088012070052701d0031100c49001c40e000c4440c61900c1d0800340025402030154901051014102c90310340d1a00090f010129541a0307940d40c181840c0030041c0c40603021f0b0f07590488009890705800b056040003000540700420b003901c00802c1c20740150040c142480030a80221064a040c0341c01400101400112030500314440e00d00000c00b80d4521a00702d0440c040c8035400c5a143d096842080103214400015017112048078a030400407210b8642c040c0d0803031291010044c4072030f400400085840c6001c440d00151a00340c901034580d152101c2e07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 17999368 1250 17998118 17998151
    0x1f020702040c050c0709090503090405180615090c1908090a05030f0301090608060106050301050d08040e0f04060c18050d021512010e0f0408070210090b13080c060405060706020d 78
    0x4440e800b00081c0c001c80c104041503420030540c00106549941044014843d440701d50b03ca100d109240c0b801a0303112000b00742c605450130f0340300c00e948402500340e6219040c8000010106620304556520030703100c1c1c20100d210312003010102c4070400500c00800304045401d6809075034400c0000e20f01d4046003c6d83c120344022400910050201c49034440c40c0f19540d41c108200c0104540c4203030071000665100000510101d508803007140c0c1524400c643c40c80e0080068542036410744241d41009205c556514180f040c00e030f1403c008240a14800c500c2880b041e020f403241110303801d40d03443c022540500503d9081180b81001c0401880c207900207840710047ca0281241e045040e0300455a84030f41c2c20030f001c010004440c10700955900704541c0101111a4180342e00c0e6650b00d406080000391042410084802135603000340d040030000c00f07841c1c404548810600d400c890340c80f40c42d8450b0315010301500483d2441407501500316801e454008241508248154842c440250000d07540122059503030350b801e60425415 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18000618 1250 17999368 17999381
    0x20f030703050609060c0403031b020609100201020d0b01020c1e1302041e0501180b0d1b0e031501050901030312020c0106090e16050f191205030909090f1f02070204 72
    0x200b004066034104201d076580307031000c020020940d441041c4000d000180e40320340412090000081e20031b200f003030700c1d00004103c3d103d0fa40d03078141d0244048100342d15050b01900605590751004800b00107c031044001603813103100003c0c1550b440400c3c0c00c2e000050060114490390003103400350642c2c40c4034a040c000c003822030b40150040035070341403100310b640d900d13000d1240240003402c0c003032900281c0c40d410031100000c80843e9002d1081d050001003848100b4103001d90044200401d800c1c400501c40c0100321025080c0c40303606002c40c1c06802104000c44404540c0500941229405002e03481c00f80e28540b022107408071302540d903500c0030303808010001103c0c01c03d00650005c0d0410801c00102c4016008017141381074204500940300d1030148004015660340e1804541c4441030550758a0040f1500280808410465802c041458120312002034244007001024104450307054542c9000c503254080c00541d10084804185019404200740c03502d80c10f0b040c0315007010400c04a4002d800c00c1d03100c1d4006400d4420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18001868 1250 18000618 18000623
    0x4050a060302030d0329030f060411040f020306060d02090303120705030709080607090302101101050103080c0607020f1002090d02060c0115090b0105090904020102030418020304030905010503070503060d020f030703 94
    0x440e5403050003035103024411000421010308040000e0700240f1440c0c4101030716500b8203030600c00368105100d41902c4c01c0c481110f11054200c151801da1a203450501030000b01142c2c2240240c0c0303007418130710011160b4421603001d558002c2c1002d04103448120000c02135070107134080d80e425000c00d010f540e1541207002c4050740101e02e240c07192a124a025200144908000e51011032590701c04800c4c02203d60300241000309903a010740300008200040710f010b07100382380701214402c007a6180ca0000000e1140400140c0314161101e4250741b4581ca035a4022651040f002c803d0031425003200940080c042c030f0690090480003805800031401c0c484903000a0a65040010408030a0751150302d00e8002c001440702c04800303481c51300020001c18070940c00082c0240134820000d0300900440c0041400e583c02001982c008180c0c004d000031007000400f9560f40650020744040300840e0301c003000440c45600800980784101341640d9079600799501c1c1310801007000182e210076a001107844001c1e85094900f80401000b41d070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18003118 1250 18001868 18001871
    0x30f0d0b030d020105150616020904020a17010203040614010302010f12110a1d01030516050706110708040303030b010509090402300a0c08160e0a06091a03011503020906040f0b04050a 80
    0x10f41b00c07030501140c4140071155846664100304081400d0401c410701e0660b280c054074050000d645600c0030a810500c103070040b01d1a0070008d12480f4a80005400a5110340e00c906c0b02440380c1300b032508010442020a0000030301042c40d1420f00c001181c8181107207643d035460075038045a001740003008004650300420016002480c0100c0049103000c800c8179207040010280303410402850600e294499103840d829204003040000202c03a0705204294014460b000c1c102155290740704010310b0030b1107043e40503200c2200401d0400c088180c241d80902c0a80e10140000ba1020510b41c0d2581c2c20000b0010a0045120510007518100400146003021b038042d0406e604e8024040d070503982c01d02212440c4540c1c850101d0b9800002206500045600c0340c000310707100712109014545520100401818054225035000c6280c01070b80040d890702010100d040300402d40c020000390b2001d4420280e011002d0102a412002d01000b01c1c3c0e05082c60350100c000c40120141c00a01c036465040010182d0348144ca4402c0c0c1039 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18004368 1250 18003118 18003121
    0xf0717130302011701030b060f120d08191407030e0a0b0114120a050c060307020a080c03040303110105250504030219030b011e12030e030102030a0e070f0503030f0d0b030d020105 78
    0x5580245142030a034071454080d0103a50700d0366561f8a01101c0c020100c0c3e0245c40c403040c40d5000340d103600fa41414050802026185440c401a038000d100306811208018140101c80d55440c0101e80c84c4580d62280720401450075655030355041c1034024000b4040303540450700c2000700c01c40105401c8020940a05080c569410107052000c0800ca81c0c070200201e200d00d0b83e0404004100042d000040c80c5030180810b40d01c1c1c50300e81d80d0300741d01a400d02111240c06000f00ca0000303071711fa8212101200030300c00c2e41d2290700c425681e40500a4560708031181110036891840d0000840c03044d00d841c45100101000fa03600e0040c0c40c2c0b9840b5808504401c1c425262105980f04402003802040302d00c02000f40944101c2c001074904c8101074003203400310106441504010114880603106043c0f00e0800001c1741440030300250b540e41031000c01c1740c0c01842c20080002c51030140000200e501d8410948800489400a00a6040c40542d1081603055440303240719124150f900c8810602c0d94038148400c1440c4441a00001041e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18005618 1250 18004368 18004373
    0x5040302010e0106081b03030c0307030c02040501090c020a1502040506040816060807090e1b0315040e030a02070b09041d06150604030f03030207060b060d0b1302040b0f07171303 78
    0x2514481003142c85680d05160052180700d00008042003d014040b6404c803164074281c000ca401d40c40750a419003041d001c00240a000c2c0340e084004108814401d0f5400c1100b030780ea4105803412590307540340900041e0001f03403485000c03d0142214203070f029051540146010340d203500045069004c2d0b4001007858000781c20080c3c4102a01c43c0001c01085282030070581407800b880d00600001144c0585814222814089460099002c0c14410070000d044001552402e103914160f4200b11000350051040b81041c4244429003808425942d140001d90000c1500c1070034480e0340e00c1250080440c09402943d00c0c04901300e45003c450f50340c0c00801034a1b014150358200480d0f04210030045081540c000c0c1020041000050007941017041c20301e825250041e11391405107423000250549620a590200c1c000c9004400f082e9168805481c5410440740c0610200c0d101c2400000e0b8000c0d4031920720340361000d1060b91450904032006000c110720900140c00c032010b9140720f201c015040b48056890b0034031140400d104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18006868 1250 18005618 18005621
    0x10e060709060315260a0209040609050c01020d021b011e03050118090c0603090305070c08030910030e1c050714070e06010c020306010302100905090109090b06010c0f0b0c0d0c030504030201 83
    0xc0c40380401341c41ea84c21504001210441a04d000c4031402418a140c0d6500d41c1480140580511035078000c102580d542005c0c00d01802503e02c840f02511940140c080004980d80009800d4003a4000e54024108229280214804185000381e190741409020b900e20805203034250981204181c04d92000036595040040040320621508a00c6800c5440c08a441010800216544040351040e141c04144071a01d842d0484050080e800d000348224405140401c9d0fa15011003d00085181551400350049005c10100d094404641860030140c100d0f212040c514035003044ca005206016060540c50704219903140c60b9410402c0c1003030340454004850a01c010720401c0416508100c007480c02c2080c036080d54002940314041844024810f040e6905001da000c0d01407070085004000040c04e00d402513035180c2c3c10130701070011690304032028503160000549130740c0540b0039140d6468201851031440c0c0c075580c0e22180003400240c20441181014050f0140380d000a005001059445540c082500c0c10304e40380190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18008118 1250 18006868 18006881
    0x18090206040b03040b090a0b0f0403030216050c100306030f0209040311060c03010501020d111b0418030504050901050a08032b020714060702070602030f031009090b190b010804080903010e0607090603 87
    0x250250007046000e030201da23110103210b41081e0600c00900c80364a0710302e0180c0c003c1c411011400c41d01e0510f41e0064046c09004106070707049079070590b080c4202070160701048049442d14000100606150011540075003000c622803548035120b8140007041e0354002c520640341c0401100c442d1410100040140500e582c1805142c020710300d03d0906011106c8680303450b0741c0f1002d6440c01e10386400a181c2c2140b92076030f111380041e0308400840c0100404401c981c28001d010354094058103010f0040040002031328102852802d04442c0c007030003d10308008174504000d02001d0381c000091900760030352402101103482c0344001c14000c0e104005426101c3c9014121604040c401412041590003003030081140030b0700801241d07020b005038400944d481d507620052800380c8076103401401500e85000b1248003007018040f0b000f030281d4911135080e1b01c04120380100c0f0301618050340c074407400200001e01080000b000e140c0a0503a5100040002c513100560203003241c600902110301e00300040d008002004031036010311845 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18009368 1250 18008118 18008131
    0xc0503011409012711010e10020d030501080604050706110705091302240315010507050601090c2a02010c03030207060c09140307080a02061b0d02030706060e090718090206040b03040b 80
    0x2d0420f00e20f04c0c1d81d101c50301c000400d40900f0002ca0440f011226030b2090051140c2d5801c014140d0044520145000b940c8170750096014001c40e2a00e000403400f81070025042e4403030f41c0d201d802807051038200381048a43d00c910440c0c5200d94411500040303100c0d903031082414440e000b00c1403142071040c02801049264041c0200d0258041400030316510380c084c119044036808002486451500c07030b040c1d00103c1d000d109400d40a401e90003054000b00700e0741025003060040e5441a69443c10a8002400c440c000102b500344500458400e030760500c00650194240c894118001d04005040c44901c0e154101a903680030b504600240f40102c0500c83c060b90f00c01d60500c14403042e0006d1044600389084295101040f0f80040d01c1076001045540c42c2c00000d0468038441101442622002c140101e006541d80d040305100716021820a10085442440b40441c40e110703a640c00000e0511030b2618015000d0280b480c0111500e080d2521450009a150304009000403d1b4404005641e882c0c203040c41022002d016251 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18010618 1250 18009368 18009401
    0xd0b0103020901090302040b011709010c03200304030e0a0323010606030618020d0207020307080105070906030e0c0d030509040c0c02041d280209010b031807060203040603090c050301140901 83
    0x10b03160716680800140b082e203905440000c0c8540103200140c554070340c040282c00c0c0c03008508082201102064101100c054800d4070144951001b409410f1000313a8550170201c0920014030001d404a44104618058032202400e1803180316280d81742d4588003288901081e4007e05000641080c4060900c03410004110741c0c9410800c0d00d09104044580d1160040821981c41d004185e40d0a407170460780c111491346900400321688156203a03030150180c8130460701d00010130308008000441c9402400f90311048040795000d00b00042164041100040840b5000e9080101c103000740c106036141c1e80300301452207400f5141d201031068070748104419a9070500f00b40c681a00885101101d2050005003a403e103080c640d4001d1210300f0002c3d03006c26010404070084d5000d0402000000d01c80d512400031409000e0b081030f00e22038886104c40751981c4110a10034400164800c210402069229520000d0200e1041c1b01955880f6a10030000e425944102015082c0c480710750240001e0036824070550021a1108a0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18011868 1250 18010618 18010627
    0xc141218030301050307050405061305092407080601030504170c0f0c040e030909150d080403021309020109060e0607080c061f0308040501030509160305010507180510030c110d0201020d0b010302 85
    0x886e8882d4203900c40d0034003031500c8802086455940366641410b410000c50200300c14909010041c0d561034642034114020f520f001001101c035060040084d104954a850303601d01900c030140110005c24000340107a8240500c1d140716030204244400618049000a0040042c0d0f0100c40c096800c20001e200058400c51070501d0303940c001700001c02554a40036007168000c40035580c013180d01e0f03551401c071105680e11407444001e403801c01c46120060415203009940c01001c0c004440031003170483d000c0d100040c3c040354141c0401c103d000e101d4071081c803001e40d015015609101ea10703034802001c1c4d00840c607070300c107140c018074104405003070701c4540a031005180b5000e20202c43d16584810700a485a0b028503070415456200150521800704514030100c800485850b5016940e8249107008007400d56400c00010302040c1481c20682c0b440c80702da01a110300801c6650300103050308068004044c15a000f90034018001c1c503484071480f06018070800580c6c550000341e13850000309120400c031000614850306045c030500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18013118 1250 18011868 18011879
    0x40501030e0609060103060b0a170a0605070e0906040e031b0f0d08010b030604050601110f070509151e04060302120f01060902180411090301060303090306050c030405030a030c141218030301 83
    0x511300341142c1d00843e00254400804022070584034098000001d541c0340800203807405d201c001940b4440b40c0c01078078200101c0d1504041121444141e20400d44d000d24240081501031600c1c0e8041e14422080c1809c0f00c1c5047d10740a040412007003c1000075119802502c004015940c05200183c110340b003c0c6401e07902581087c0c41c04102d800080d0086001e15a10703400542c650340a82c5440080480c018111400c00b41da643d400d40c0e41e548a4003400c0c0c007603503200c000f080701140e03d801e0b048521380e001001400c405a60240544a404088060301da115440d8980000540c69040107072182140c2800542a800c0c500b551650035640c680d40190030140c03040040c2d0825034141c81d0798511a00d012100490f00c0c1148501520301e80c011000510391552804034004101600b0201e560f0490f442660288035641d80c80201d800f040c00100c5014007150030030000844010711941c031108000201e400c00340c01068034001c4500c105e0304a0a10001074080c590180841d100074198151055100d80008601d19030410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18014368 1250 18013118 18013123
    0x2030601030b0907030803010b0310050a06051c020d09150c05031e04020a08010f0902031002040308030f1308030f04020103150605040b180d0c0e0705160803070c140102040501030e0609 81
    0x148806007050074040b000c6400c4880c1401844011500644070545a507120450000c0951080e52051280c110b500382c0086d00d41003d2850b48115074558031281e007080e514960a1415800d981802c10007141d0801c50307002040303420b1003541115401a1503682d45200c260b65180700b01d40c1c1d080b690a091110034003c11034102101c240d2038001c2d43c0b154401107000d407240c1c804540280d40d25041001594200544100030944a5201a040c68000c90450780d0b29158064035108901c680d01014024040410001d00c1440d1031a06840c2c026826489001e180030302512450300603041542e0707c000c4240d070501888155070345070007250f03840360342925031026851030404040c286100e20b21845401d0030002c501c9841c9044a0100510392410261100c0c1c80d00101d45003051060b5410702885410602100200d0312107403160302a01c5160701c05a8403012030b00481d48840d800d542005041c5e40030400450580d03000510151060b2480301c5c00b623400942c540f401c1c10005829503e030944206d10a505c0a000c00002c203400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18015618 1250 18014368 18014371
    0xf0608060d080901050d0501030b060a240c020105070507060503060f031c08060102070518060316060f051303060c030e0c030c0f090a060308030403111b03030a0f02100e011b0c020306 80
    0x480155940e610050045e0351078007400041c80c007220f1a12000106200c0202a8140300c0c82d030840e441c6c1da0311502d81858864840329207800410700c0c0c461240000d6054000c444815025005040080c1428072640c0c2c0c041c501640b9403c90130010760040148110707800d1800b0803030340c0030303e080b03004e00000041e803680e2008001c6080810000c0022040100394140d000b0b03c540c0c0064480076001050500d080507040194101c10346105019100e000b40289040c0b8042c441a801d5a999a0f102010a980058211001d40066100e0240c0958980c4008005580c0c0c1c414110020b0341d41c1c90225908010400f0103040045940585009030040e03aa121180d5071a48403451070806c0486019039640c56031030019005000640008010050003c00e1100781600030b00180c4144c8001d4007110100750201084204074400800c3c6160150700501c00106100d00801740045e511840e407040765104c0903107030b0040e001d541d0b18035110001030b51b40d880200a07003842e420741442007805070f00f460918900300703501080c2d44203070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18016868 1250 18015618 18015623
    0xb0703170408040f0305010b0f03010212070c020103140702010c020c0102070803041205010603061d0106060212090d110a060504030c0f05060301030b070302090d060c020d020a15020a0909060e010f0608060d 90
    0x400107080000a405403000703015a820307000441a1a1300c1c21718020015804200d1140c0c2c06004140441d16050080700c480c482c002e0401045522040001c5d100c18440013800c9041c9a11685041500c070b65010040d440740c180e0b07500104441d4085000a400c0c100c00c0c2c925141113410004062005007400400c960894a00092030044044c850400600400380364000511560500785401c0d2500001c0e240e103900222100001c00166079140802e030317907450045c0d4000081c0c40090040d664685003800e0481520740c040c103c403d100301140f0b00041c451421302d03081840400c070041800c2c0140061000110b000d072801c0c0e40c6545c0e22a0410000070080d000500c001401250351500054035507101e0340503106d07074000181c4141c00030001c5190141c0901201418080144603210284244510004002c5040d40c0c02569007041c5556043e941030295110408410900c507c0160004101d001403052038000c162080c07600300b0b55410007400c4581c5500c04c0d405070701000401802d101e0180d03203201e405150b0701e6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18018118 1250 18016868 18016907
    0x150905030f0a1103040303020706120b01020606060306010302160b0a0f0b21070306020a03270b04032007080f0705030a150209011b0606030c0603090b01051215090c030105010b0703 79
    0x2552050200d0b8141d8090741282c00f6030001150001c20550000792070802c0c0c40320741d120089042d1812800104540d241d2284c140107070302c51400300e03441d4104131004640080e410326026281071280e200b03c00060082890842c2e60613489010071100c80d000784109906911040341c10302001c0705d2400015a01107100c004c0d248699450546a80817500070003000c8000d541c88a000d6450301400302010317005210120031403198500d03101400c001c0c1e101c1800c8585041780c0c40040b140d83c85d152a02c1c11210198810b88070001040da003800f59140f80000c0054070024414000141a240c60202d50a4140070745035010f68081c2e4006105000014018000b01c83d000048071001130710390b8031010049035088000ea00c58001412000c1822081c0710b0075821020617207000d03032160196544c0d200c608404403070030140c0240a141c0103500501035444c11340340c0b01c1d104e10455000c0301e4085060300d4208012000503210140301d42e211003006946420280645801004c5a01c1d007681840c0d80c68401811040b9004907200c01d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18019368 1250 18018118 18018127
    0x10020d02120f070b0703020d150320060c0a0b04210206040605040501020d0509150123040b13021210060807120b0d060c030905100207050a0209040807060203040c03150905030f 77
    0xc41480b06489031180c201d0000600307400c002d20081d0003541b0006c2c13803051142c1000f0751303100c165801103082001c903030f44041041ea51a8001c03a003444d6041c101c1f1401c0ea03010b082007100c031507880c10400602d44054043c2541909a041ca0300d0240407e1a940749003030903400c10344903544a50758011607503542c80340d0400d0000c00d95584519006009100f640103540c181490001880303070160b00003640700c4001d4603407180701c10140d803682c41b600c1e060204400140c040c032070380810300d42c143d04194020700c1001038041c0c4002c00e0340e03030070707030325090681e00300c8c0382d10b480002600d008101d4000740c5080a0700081ca0a0305101c1c146003072280005000c505803060b0002c8003900c9130740005441d03d42c03400d2100c1c1250031150801081c0a5600001c02034201c01e00300340c61a1060440c4002c402c00648201c4105541c8100180403418407a030a10000c008010800c0c0d40d200001e1240c4404641240011440741f803041c000c40700074505602c3c000c15024200889034924038039140b01c09001640c00000c540314051101600f6448 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18020618 1250 18019368 18019387
    0x30a17011a0a02190308010611010605030d030e0705040f0207020a15020604060e0a050f100b010302090a060809190602030402010305010806060d020f19140102010b010f0503071202040e10030210020d0212 89
    0x601c1e984891400e1016061544e11091562091190b41030ba0320703a64412200e0600b080c132140c2a02d155000d11941034208010400802d4040c1d40700400d4100c41c8016102d220f42c1e94000101250b5000c40100d070010b400160034000c5181c919420002384c1000018108142c00c0d81c44000d40e0780303d00030801041a82c0d00c40900c02904c0e010458100000d034400104c3e400904081427241d143e403040030020b1000b80c1031050b207003c29802070003600c0308901e02422400520b0302c1c10f4012158808041c09482440c0284402c40c21350740740001003070303848600800c40503030349040c14800102151070581c840304641c0c00030070a2181c20740d2100d80003c2d8003a0112034403c0c80d41000c0c0c00180c50f18000840036010302e02581e000194440440101603200c403400d800800404000170700640b16880403540180000780104001880a8060490380b0400a55144018140798864490913000e00e01515102c00d00015580c04004500d48100c0b00300304512188085d0010140040020b580ca04146030b03039141000c07010480282 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18021868 1250 18020618 18020623
    0x406140918070e010305090a030c0b07050f04030309050a140108041103010204150e040c050906030703050c0403080a02031c180b041e0b04030e0604061707030617030a17011a0a02 78
    0x840c1141014266030307900300760001401c0301c00100d82e1180401d08100005811010200d030840019401da2244004010b40381d40744111100d004040d9014801d0521040740e0658004010340007035482034039509002d40c2000204103403003005901401410101c11003d28060340d010b50510f41081d03011040070b28460300080060302900403500310b02011a40112600c2c500703a4440e0862605030310584081008a01782e0408036158421089030a4100d2800c00100307080c9442070340a16488074201e0180c900b059283e6850040035031204c040c8034016400425180340d160300c4040b20100b5040c07c1c80f020400001d83e482e10203a2030414030000303000c0a6421001509010076024115166030007049601503107081e528181404003c140d81c00c0d400038541e070028110b6030408504840c02d850715a1140c00705050000c2c0c080f40008c41c020081000c05407900c60006154201e0448101814082405036845510001009000200880044119100000042100103075903010840030000d9600c0265540020540692 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18023118 1250 18021868 18021889
    0x10b0a03021b060a06090b0303180607030e0a03080406020c010804030f0c02011205040c031a06010e0d03020c040504050c0f04061203050f13080607080c030702060f070c061104060f020304061409 85
    0x21018043c40f030400480080a5101c1820740760701500410501020340241682c90207250842a0103210100901409203800c5d006030800c1440b03464110102498034021881035801c99104407070742c1401140a0103120340502c0400c0c070314442032800038418605510001e0040e204100103009112812400c03c0959118880340c0d81414071440d400c0c07009044c6480d0000c4003981a00c41641e103840720000c0c40e0215a082d65441d4003d00050b5904850443e0903800c01040c010360241c11015407040b40c0341140c590f190b82c0501d034403481c040c0001c0e0071802c68500c00e0000d0826001043c9100750325001003031065403c803411158013242c05141c60354682074440340f40c080b144125580080940d411100029030084001001403003441c0540c0c03040200c0c1c071090381c1130079240429500350015070010030000d816401181004d6074800c03107504d000c0e00100842e0300c1341011a04003c01411281800040511096800164102c0f0000c801c0c8015071a0620300400100382d0360681c0d185d9103481d0400105880c0c25510700c5003a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18024368 1250 18023118 18023167
    0xd0608010e030406030b0108040804051e09070f0305060609060d0f0b03030f03011e0305060a0b011812050610030b0a050a060302090702010504110406120807080c0f0a0515010b0a0302 80
    0x20441d0044109046699402c42d114020000e0b081c40d124410652003204d84500030b0b0380c02070701c960409040c40308000f1560342d031410030b09100e1101e8504445c555920440180140c61903101c0c2600301d0440f100c000c0940c1c2e8000d245d24000c0700c0800c59000144c0700c0f58100c824840217100c00203000003080c0e0380341c40a02485080941d1502c004141000c1444038100214121100490014904c7c2c0d171030020301c01c1900c61844007130050f03044140041d460400a8000d072034501c40524005000c1848403e80040ea80324907000100b5801065000f00100042000301a8001000d03115981601c1c3c0b03507907074401c80040000d03c9180d0721a12000400c074440d00702c2e0020390186a00411284192a042a0081c02040c00310f406076509100c1c2d4210f540c00b810a4800c03c2d00340e42000002c1c040c1400e0b01d441c1c0c0ca0540c2e10107441101c003480104410717030784004103200710555400640050400d0b4040303030814a10344800c40640d50748a403601d130b00400c20903101201300c0b5007010803400c0141c1c0f1240705400d0000c6109010041 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18025618 1250 18024368 18024371
    0xe01050705070807020a0503120301061106040309030f050c06030a0903090812071e12030203060118051315090f140a0b0f0d03030e060106030b28030f020307080109060c0e030c0108010b0d060801 85
    0x400011221180998140ea482d6074dd141c010910409189a89110503a0041c000c25600d00d01400401c810703a106082c99030041085030a100c050401044c003685c000c40311660a907070348500350130030543d01c10f8004008141c0b29004000120324104008110f10a00f50300921800700310304103a8840b42c0d140c5007800041e4000c00755401070341d201c0c007000d07000e5030040710b116000030021840484001c00c01000402a680050000049007548002d480024000c5100c10051100603080001d4110044c2c00350f102540702504000c258020821000380d60078201400c40315286042135503040164440c0c0c08a203404130780c12241c1544030007590400b0382c024208401004814000c0f50004110705825030072484031150305403400120708100300131a14051802d5070001d60742504060007000414120b01c0b04074400e90004003922031295036055003034211054284121043d985aa4034200c2e010340042c043c0c807240506601070b08049440c100000c109800500540030358803c04030b01d08001c800960b0080020301902d000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18026868 1250 18025618 18025633
    0x7020709020c10050c03100306110405060705070305120c0307020607021305040f0c06030c12020f040803040f0311060313120e03070609090f140c0901050706091103010e01050705070807020a0503 85
    0x20701d44609401c5202e030420fa0030030010940410707900044a00c5014150b05107100e140c11755640401401c3c00c2040c440708003005000c0810b8640d5a000240300e558800d82c01040613528615000b4101300c400d1800d80911034090110020000e004812075094550407100b07642e480a140c0300041d03e40003242a40c076000b0703103042c00308003c01c0b00f545c5400601d2800b454041500e180d4507103080b415134610481c00000a0500503c441411380c203500079044280c14152100c2c102a180c0c01401e140d9001544400c6140315002410802c0c8038400c4180c0303020f10b80c02d0314100d2070340c507148201e94111421504010b191001e0301c1061040c1600c18002051042c000800b074410085d50303000001e00c00a0385000700000d00780741c08108d6441072942d02c43d288405040d0004011155200a8156841e802040701e550500500b0021075001074507501c242c10100e44126074065921681d0414142164200480300c1a660f00d400c1c01d10030034642050a5500e000d5101984076602c84130382c80031030712000c506e030301080e0144903d12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18028118 1250 18026868 18026887
    0x7050414150d0c03060b0c03071b03051606030605030102091f030f020f090102060906090d110a06050a0515040e0c0f040b030f0616020703020d0237080f011a090702070902 75
    0x204840304043d0281c0c1c05001031340d00c60026200600c070b15020443d15034001c01c91030000600e500ca009650080401c1c41e00180c40d0780ba15400c1c10043c880b2548481d800c0701e1207003400480d401d072003000040d14040d0021418400c12001044030003840751001105c042c0c81c14484600240b19410601c20241074071410754a886100300d241d90340b80c010110f1203016004150014062407000540c15200b079644000819041c0c1c1d900005070741400030541e42c01030901803d0708441c00b140315401064011040b00900040510304044014486900c15810a05c52418000300840c4e00f403000403041468002252618403d204143c000f0f0001d20100ea4a560580500b401e000b500c03210100d51140f141d40c240d220340c00f801103c040d089840e0416170100a502c5892a41004054180110180808243c010700294001d40e041d20030800c55049428200301d441c8520400d00c8100014001d50310202c003688003d0041400201040b00002c85105640c1d0003549210700007406d2074404c2000c01e0003040004802c40da2486181c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18029368 1250 18028118 18028121
    0x90312030a180803060405071b050706080703090308010603050907050d0b0604050108030a0f051b0f0c01021c12020a02030910030603020a0b03010605070209100503030a09080d0807050414150d 84
    0x2203855201e0986403007920308403031552240b141c2007107600c0b002c002c0c03070369440c0d0040000511010b00000b00b0040d90f0050060303c2c09851040b00381b024001c10003041c95500d003060040c162140104210201400c0403940000285c11005182c199079041c14003040c02e0340e0f6102054a801d034294460750307001c0c106640302c0050000940103140140401d131410301240e0f0300c0c0d054140c3e0760304c600c010300f9001525464140c1101c07031048001d009045400040c1040703011071114520f1500d410f644102080e50040c1d0f0f24080c40b986c042050403a034070381c105003103080e1141c030b030743c000c0d00302c502e42495001c1c0d103500002c500480610030706c01c8903100b61004021040768401824000c0003040075000c200e01803141040041070014450080d83e04079401079070390500e0b00c034207035080c0000e0002c05443c0128010b9039800118850381d050020305003684007543c3c1c0040003450141010300c1c18441c8230070340051282c038800740500d5030b6000003210181c40c823049200b080e080044003c501c40002c1c01c91131841a46010030a444040e80303d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18030618 1250 18029368 18029371
    0xe0409081c0204140a24090306050c0d0c0305130f1a070c0501060b03040b0402040b03010603062301050a060e0108090708100209010e0307051c020f041506090e0f0403120209031203 79
    0x9641902d184103505024800a8403e9001c0c400203211032441ca00d2031b07281402d100310703403171801880e080701c1480d502d9036240c0550b10142d4a40003d0f00d0301140048101c14640304020403986940340601a41c100814091591501020301400152f0420107040920400c04510b0f0070920000244590134a0205001400f001407200300b102c89500b00180028010443c8003036900503504001d00002e5500c50f0350030400180748101803250195203e10b400001b103407117813180703590300086540b110444c49100c01e100c03104a001604110301c181180d00d018048103034410110000c1e0030080c2000c005e0f584138101c00c0c514004050b40800c1c414826400146010655a0058200c2031801c1c4c0b50000c68014000400d900c410f40c5d401020740025250400c0006a81480341c1805441c0c006003070802c0302014080810705a44811079148121440c840f000c1090b103030300c103007444001c0ca100a820708150078084050714407100060800350802c0004070300602d041c0c183d03034100c130f607501c40080c00c880340503d503034404c251a80c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18031868 1250 18030618 18030629
    0x110c0706020f0f030f090111010902040e030318070305100507200a0201030f140606181c021009060c0605060406170a030f0f05041206021308060a05160e0409081c0204 73
    0x500e2205080f0400000c252119001154403507818408203000446031800c403940c01c40039541d00c0e0b070407071030150311a03104401c81c41c00f6941c0030307542d0380c50011039066000004c00002d10803a84141d00c104003040c40440d02c10002c4241e25004151521074179401c5581e500e01100180c92003115500c03010130320307100140070051503100b0b803014442104075200b220115041141c40034400320700000001c1d01442c02034000c3c48150103019035030b0070424042c404a603003100245540d110b4811030350166409e621303011a045800300c40c0b900e08128242c0c10071600502d803035440f680c01441c040e160b8000c50384641d201e812110151904008800d0b001040e82016503a40241c42c00c1600441c0402c01c284140307501c00c000c110b004100030380ba0685411718146504403d9240140103645407a400c2c080900da082d402104040180791410040441c4e04101c0c0308801203d2024025140c40c0c81138040c2e02c0340d9503400040c865045841140c001490020700d04007003586209420000c0c00f249104450b440803d80b007640904140c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18033118 1250 18031868 18031873
    0x2060712020f19020906010f02011509050103050106081c0305040809040c0509040c03050c1e250b06030106030c0504020d06080f01020c16050303030103120507060903080a0b01090302060d110c0706020f 88
    0x3e50f45048004840050f02c0041d4100301d1a60010301154010001006040054070000800318080114101d01c144c0c0740d000000a551990010170a006090140700d01030710309031003d000c000d807001c5003a4000010a001801c01d040d01c405c00181800f855009071144450007410500c0b80020f2034000038030703d90088802e02d03c502d180402100c03041e403186c404c051092210b40b40315450860041c1e106081d62512103c8401e02e40d10401644079810181c1c3c0946010035034243c090718042c1c03083e1912032481040181068000d81c548502040414134010740642122010348005a03105048607440d4068203103a0050001445200305440c11081c0540c014143c1030740b0032060b601250049a05c06003552141c2c0301d09640760f80140010700109070152003400200040c0e05065107800300507075600c0c06803085150290049034018042000c1228140a0090050400d00c0c082c1103450955000425078001d502e41c203100e65035543d0100303802040c8442200c0141211008591985903141b070002d6481c001c0c66500303020390 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18034368 1250 18033118 18033133
    0x903030f050105060405010e0607060c0c03020601080303060d11010302192006060325080607080406060503010b010c080f04090203040606050307050306070903060b01050d050720240402060712020f 86
    0x500d894440c01e8103a5030300515141c905880c05c00111182d900701e2002c3e582c00b08003082a90001005846042041c41168890b03000e103a695050190071720070140c0c031028180d002081041020341d100210861107a030312480164000c000000120001c0c054490080f0880400c00400069503400c00200000f444203a41d0400c9004104652251110416991250540d201031b41144074403407003a0482000e40ca0b003452a2104903a1035002d9450290140e5514010070300c41c074180028401070307000c0c0300e01400c2c00790001e106480301c0c030740000c4c4000c0d03181001500c140c3e800b140e42c040300c041d25800c40d0700900107100103544905080c02c103240105a40e1060502c00e00c510708000400d410b003c1003003485049141c580e000c0c01071445d00c4107800b501104945a0422034100980c4d54142e1044c03160501592031513540d81000c420f0a042161169803485036138600e54000c80e802c4c018030076201c900031103e82c0041c0800f403490f2a14408128075000b101001000752150302c51100d4825800a244802d201412044032040b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18035618 1250 18034368 18034391
    0x30c010c0305070605040f020607060f0609050103030c02090403020c060418050f0408040911070f03020604050d0e100518060a0203120609011401030207030e030708071712160303090501050703090303 87
    0x444011030020080b950910010300801c0a13580820380c001c2c0500c4203041c1040360703640003452652012030110364107075850220744101031542c45260090451090100169411600d0142804e420040f00038807a0702001d0020301094402c0c485501c06030030140420303440c0d540b60b0560b074001e0000040c548081a2410340016101a8031441c214020781d00b2040441c40d1078109041c040c09441307840713505803107580200080700000b110f50942103000742c001d0b80584003d06041c6403050401007540d241001700450f0415604659031483c0b10390010302c3c0c6504001d981e5a92041e4040c1c07035031003040385081d80f00740c3c081048828650084000c02d02d60030030b1901c80c403281c0c3d50030003044110702081c020803020610448c015610381d4040d500814115000e401c184007803254110000340f806071190020621600285030410000301904a82c141c40c1220501070720740300401c04d180c9442405000c4c00362510340d02c146030031070605000e0703400070500f19005002072082d4501818050041c01c0c0b4004101c002070700d007002c985403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18036868 1250 18035618 18035627
    0x30403170a080106050d14151804170703020109020a03030206011a04060f030905030d0504060c1407021e0613080105070f110a0201050f0c061005090609010f030f0804030605090c030c01 81
    0x1c5580d03554a81030810707420100102c030243c02004100050f1b41d81c034800660207000d10401e0601c50b02590021180c0d82c10f00324180900c041c002c0700d5424100070000f0038070001510440303103c000342c0c0e0b0304524240c44003081d060483c007410450728040c1d0000c001c1e17400032003415400b0840c0c5041c0c40820300440150326881d8080c4a4a200e1031260b9000500015581111148203800105076140160304607402c8c50050a081e00032a201500c1c102e42160b03481c8000908140c004511304008080a1031a5080121903000b04104804000300000640c0e4920705844169a8503010345581010380881d01211a031204070244c02007100740d0348000401d40310040c0c15101449014012400a40000904113a0324075a005440c50b8001701d4000d0780c404bc0c180441d12a021f030802081d071050043d0140c05100516007400e1000103200901100e0003003035181c005202d0241c2c10840d2804495003ca000760040d141814000308070301680d0030007080e881c202014442c807200001540058500120207031240c1044071001503c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18038118 1250 18036868 18036877
    0x206040305040312030f1e05090102040f05040c03090f0305030a050c0405100f0203040503010c0e0a0e090706050a02120d09150203070e090c0405150301061805180a0f05010803040317 80
    0x3000500c0030407060000901030340d80b440351030044e81004150811104400b070141c2da801000110300f50030200300e201041815000f05604828448004c529250815010304c500d1200b50144e41c0c026900c1d10158512035220358031010241c1d070030002e2885401c81d00d10f0024400c2e0b0095402c00000d900781008120401100350480e000c540d8002e000b80800d102c00c0500342c405032102c540c0801540020b200000d134540303003800352403500b030055902e088456086104005501e00660000220005541d040049640e8001011011780f05d0509046803505030042040340f401c244400c1c0c42c4010400403c041580030b07a180c02050406206100d10065189129800812404112124030008440011505d59070a080c0210383d0082940b400980c03524ad10f0f9004114101c000c40118809514000010040700e07511a031000540840080440360b02803801c0c000646400c1d0901c8201c0c000700c0c0717003c00325003804101d500c42801210101004d001c40c0d81d4681f070103501c940013840141c039858a070542501144a2100468 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18039368 1250 18038118 18038123
    0x615030c09060b030f0604060b03070201090c0e0702070b1806130509070c020619120203040b0906010602070602061501050702041b02010c0509032805010e0309100e030c04050903070f081306020604 86
    0x11400c41d907401a0b28281440003034a0a0b400c503a80b19230115058080200079807007054070f6000800c2c90354851030032072540403450380400403080c1c1c1181404820340e4041460301c00c490a0000590711030400c6d0b2411480210041001d583c480340c002506d03200c4181690380703041101c000b200c169120756a4024207451415024000035481803041000c142400903030041c1c40301d688114034003800c030f07003160940c15804c9a0003560251000301a00b41046802034041201a000d402d0030705c06001c015140c40e40c040d648407005882a000001c4044030302107564454030603102080d40044c0113020001c2c01c041600100381c0d52807400c0005500b80002d0269980c055400c135020181302038020040304803c4c0d80d4a424003c207005070421320422180303484020440901509800e000800003179039580c5401820403444001d10b01110044c0b00104115001350394000c00c60441300c642c10340b00440c45598021607a42144038100c402001104445c404005101224001e0300403401050300c2e01c030407180c680000ba40d40c2c1c170b01210300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18040618 1250 18039368 18039389
    0x80109030e040203100504050903040e0105010504060807051b010219020601050a0b0d1109180609060d030512040c170618010501030c06030b03010609050108030c01060f05030307110d0615030c0906 86
    0x9005a051640c011513001703000c0e02c01c2c0c2450a480304c00180a6480c01c0c0d440d40c1550b400450140000c3e4129000d20340142000d081441c50f242c504000500126001420f03c001c0c4070300420030040f0070499280541c00c00e240f20001f107554040b5111203800d05018402000014440d405c0041550b00300150b02d201520107038503040742040f56400000000c0c1182c203040d803e10000500c4145480d48400715041d0484003900340d002c0382446c1400a00070101d00045c00984a80010208200469005803c03690130041c1d900d40211907503107900304080d0f0a0010b0340088c051903803840014a0740e11b00030074075a02800302d98070140c11000c031075103a007030030795a0078000648842140c0741c042042a0007035002002c460400780000c14550364500202c000c481c4240d001c90b00b10342002a4600100b2028131034500071b0001107220b8003429040c200800d07a070303004026000b0450302c1c41106440f050742e280380d45000c0055200009000c0320203038800d4825004890b100407603480d0b26100c4082542c04960083c7c50580307035240303035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18041868 1250 18040618 18040637
    0x60905130213060902030c03010315140414070305030408030409060b04031121060403030204081e06012603041e060201020a020a1e02130b010e18071404080118060608010903 76
    0x700b040e01d500d034090480146943d020000348400c1c050000e58818000381118507101e603d5800c041a000c0705801002c4545403501da07030b008150030084c4e911078202d03811160b401c0c3e4468401c5c40740c903d000180c3d0800741c000e12001c1000a11008004000c1c030943d02005010310481e5030341c982c00100d90203503000007001d50f080740c50742c0b9007181011400c00c0f10514203650711000840445001d1410003109550640000390002401c0c01604030810044200341c060007a00c1301c03440d0b50844403580b20101030050740b52214900d07101d5000300803180c42c1c40d490103440005490340c895594600301c1103032800001c05262030303840800010701c450040c42914034400d41500900041c80c01941c42c03407203484101c41c2540030000c0200000c0d01680342c0f0a40da2401115044002810303000e480009020b4a002c07401c1d69205800780c03e252580034015103205900700c016030511040103114004124424022074000075102d40c68070b2003980340500c80301c00482946029140411441c2c0e115000f107820396200d080054082141800c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18043118 1250 18041868 18041873
    0x307032003100213050f1c030f0e0910030506010f030b011208071b06030f02160803040203330f01050d021306090c08090106050901030510020a09150807020106090513 73
    0x440481103a0340080c1030b22100409040c820b82240c00c05083c4510003088440306021500b0501d61007200c14604a0310507603031525640400d45c11108204004003000701c904a01e4048900036104250790b814010205819841c1003011007960700c0c0e141c030050ba501c2c46501d00003d003100340610340760300b035070b0b0082c130480a181e09015070510040b40099040b244410308106040121315400d007105405074a50300c0308a401ea242060040c00c0d24000071403002906d10400a004000d81e000d600554a182d0009220792a652140002030030700009645100b403898800c511b003529150410070321240801030304d4031200d098848810002145600340110741d00200306080800162038020110b501e03501e030400000c21031584490119044e40c00403940000491071100502201c02001c1c040c52010708019903490300c5541c51500d03110340d65107210750590111a800030f0700300c101e64840d0005101a20b05002800806c00207118004e0810504880031380c0154038059001c1010180c5000e114017542c0c030304850f800e01c07009a8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18044368 1250 18043118 18043163
    0x708040b01170c04020406030b010906020c03070e180102130306050c09010813050109120201020a03141006050304060e0d050c010b03060403080c0f0909012601020f040b071119080c030703 82
    0x2c4602200b90711032200c0d140456907890000300081c01030303030f50046103405c5118000743c20382c10544c1081056400680d412102903d000031540212a80408651031a444e40e40314209500d0240e80d210710315500003e03199100700880d441c80c400701d0b44550010086581c034030001d64010302650030358900203198031000c81c0d00c0390980d091300b0100c54001c2c00000307940a415640c088200d42c00400c0d590160f5004a45c4844d61754041c4200b620410701518004c0c2e507807a22aa510070040807038003a00042c0800800410103000942c1c0c03007200d09406a00844e04802507848015005410a0144a0f115800c1800380f20a42c10049900c90140c1c0e4103450b14890b83d240c8140c0c2003e29001099102035070302007804520382d242d840c108064000c10408010440614441914480c0e9080d03c01c441307100e41c0e004000802c0821024401c031000c4600440d03074591102c196103005600c402644011070780c410300d00b580108040c00d00d00c03030081c2241e104804071506400d11b1000d06440f00790921000d461180c0f001c03032034a00c80d80366 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18045618 1250 18044368 18044399
    0x3010605030408120906190905060601052208010b09090d021b010c350f030613060905041103010b0a0803090d020103090b010611070605090d031202040f1403060708040b01 75
    0x482c01d040c02e0125800c030b091342840c000c6031011035550000c4107000520500100b8514400d83c0d0050500002d1450340740c1c5556102c0240242d4100700c40011000854854001c1c50f0390810007036211902d0b0750b50340c0c000f1603001e0610710040030b00c1901100b001c548070030000a030100802c1456005072040c0e4020319088181c845c4100803036410b0200c246c040d040050306180850b401c01f001c1c4a230b03119146007003040f0091346100200e50359143c202c0400c011003448842c0b5054a0303000404561400e401f00c201704810010700380030f51103045080d0800c802d000070403045002503021001d00350000c001c0b000f14030081102103841442031203070f960000c10520f4600d0810940e182c590314018140030805451b80d035182d4403600000da014034009581800c014104a41c10300201004002c01c4c5007450401c0c6100001683c240d000040080074081d0040c4803504008494040d5070081c0051111090300690ba40c1200c200910030200c018401d018000c005030b1000d00500c003003400395400001c40445030b03007090541d0307003003802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18046868 1250 18045618 18045623
    0xd0309110607030201020705160806150409060509030316081603022113060605010311030613060905010f050406120308060d060b040207060b0f030c130c05040b07111e06030106050304 80
    0x1103149800c0194980d40020701e038582c4650f00050b41c490050904501300004494882058101050304016603100024407a4108102803405800200c82c10005402446465001003206040078100070a910021028600c5111008614031442d03100e00400c94407418200c03162001d0940050425411a01c2a800341516088001c8001503209181d200312200803011501401d000a202040ba400c01109018410081c8000c0c201400b0003407240302299690300000381902e005140c10a00742030a44940e401c01002846060010010b55845080d580d0b01c242c61801607500903410f1000014103651a2040c150a883d0155500c0029480703540800030300240c0b0020580d54103032903240f000718660b42d503c010201503201c4d010015050002d64240991002c818103001c4c0300f500082c69210850720f40544884d01034004002c0000c080302d521205480d640980d0700450710416021600340100440b444000c980c01c4001c4464401800300b071404850243c1015803041d03000442400104543c5000d0f40c06181c0007071 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18048118 1250 18046868 18046883
    0xb01020a0f0605060a080c0d0308040f1a0907080c0d0303020f0d0f021b060f0601030f11040801050403030e121602010302070f050c0906032a010903020a06020c090606040303020d0309 80
    0x82054036101c1d510700e418081076446660b10001e000503032800410f070500800b00301015003198135156001070b080300d90940b006001e0140c050002000c1100e010b003403440c0305600002c030b0f07151941001c80d00301c140035080f00e100605108192002c00d030b40340c0008108003425001025500490501d9504034083e4002e80100000e8520a0084455560300741c054441d030340c20b00380401610350702048541c010321380b290450912180c00c11000d11807071703038a18501a41d00441c01e003008152216643c11210040855091960314401c011401103401c0701d06404c1680200c4c000d0b03405105c9464812301c010b03120840040200054a001c200f05000c1d0394841c02d6040c0805e0050400504081c0280c44808240042000032608c58005c07070440c1d0094036140e8130311501315030160020074103010701d036800e107008036a1398200085410040102001582c031511030381d0080d60340684061901955418065520304101d1b51b400d1249258200240e030b00d081100a58080340d4042e030042c948610f03808016801031040c070009a4505 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18049368 1250 18048118 18048133
    0x80904020f04080a110402030705031f0b0a12061d1602030f0f0904060b131403032511180a0c020a0203011b021209030c010809030903070603061d010605030a0b0102 72
    0x24000800500003c04442020342598526403400c84a104a000071711482a807040c406c0c001010760040589600a0070803541400705489400f00312101c01d19603102140400c0005982e65400d07600c010380c00701c00e413840e9074207100c110340f905141a02880301ca02d81c0f145480b2501c0009031481e0650080c603c81d0075940c01a42d1400740344881000072a071048404d07030803c850000b402c14450400c1d101e40c0000b03068180c0b10604010004082c101d41da401c92068420f0000000d0101030551340030b004950601000c02d50f4102415002103041d403401e0516901a10030a52881c0c00c548075003440000d0106030340380d030a52400f10ba0b90320300b03010000789861100300003103200d9000c0c0800141c40c2403203401142002c0b41503c8074412603030721000b4540780442085040e8020203000d151840e0720000762800c030851007400c210a159480f9104145940902900c0d107505102d108000990942c00d984501c0c2640d20160100a58084049000e03d1a810a102d1007000030400c000103605641e4170f50101c6c05000c41441601d00b030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18050618 1250 18049368 18049387
    0x317070309080601030f02010215090d11070513140a02040b0d05090f0703051b030106050604050904030c06020708030f06040504020109030b0903070203070311010306062d0c0b090607030b0402070b010308090402 92
    0x2e283e0244c00468001c1070384181c0106543c0c04001c294820710105000c0d1541e03140c031426030b54681025030f404400380301e41206c00c1950903d09010100291102030082025000c1c021080f802038412151030b42084689100132502003c45402103c05444505288034600142040008010800203041c2c001c180100d40400a036030b40240b1040000b5801038004044082804c0b01c0b21a158801030a810303c26032500e0001c0000c0d840b0724090f6800c6800c111141c0c00c5075134541c2000d8804800210300203180610016000702040301c00d0b4003450040d030200d084c0d200103607908000c0c001154000e90307010380450090042000080c02c09060180e10940d030900703807402d2021a074046032600301c6640003100c060b043c01c61090b0305543c1c1440b4110041c801441c001524680c0c00c607203210107018031001c0ca9078a081d084072011031640200c1003001c0325a4801a081030300d151010030682c0343d10b02640c0701c40010b4105201110380b0700e414000d4071201a04240c4503d09640303140c0c1e42c000c0d00d0703000550385600310350240074200c3c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18051868 1250 18050618 18050623
    0x4080a0f061b030e06090c030709020a140a020d030b0904020d0b04050106090216050c0d0309060e04021605060a14060a06030f0f02030f0106080f0408030f060406030c06030213050a031707030908 85
    0x9030a141e0f01c001c10070002c10600c81d03041c494003c2c182d840c00d034411204080310769400641b20741141e0b1680d400580d160001e1800b100e05420364080090320b2500050740c48000da50000300038680c12425030301008980084070400c010b1380001c2c1d1300070354444d9500c24101d012940304440349411608c680000100315035921103000c00d98020100103c0031f80c0c3d1203951401031220600c060b40c3c859104a034070442260741954050948119402001b04000402c11401e01e5905e80b64111103030600c40046030b44043d6081d103805035590f20700b2a203040b006820075016031040e41101502c68060603000780048441410402d00310001c04a152103070200c07940321400100710b000248010340c00740c02146903170011903041080c090040b110141c000c0c501512964100404500309400381c0760040030100607102162207110001e0064000c581000c1d0641c4c00d81d07980000c1e01764140c1e00400031f14811200610480703598004000e02c0412600c4017404481c020707036410f070107000050010a5074034843e08060358415211100d852 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18053118 1250 18051868 18051911
    0x30105070e120f030f0a0e150309160303022a04050115080708040b06010c140106090615030902090c070206040314010218030d09030210050705010f0504030e030304080a0f06 76
    0x404148001d14100441c01d20401e144401c100c82c0008040c007140d408203903643c81c460b9a524812082020651120580c403130307042d4811440c0f005245030351411a03100900607950007030341d02c09580d00c5100b6008107180441c280302400c503601500075107084015046620120303d410700e03004001c08080a210742c0e640c0d8a500c100c41c060582c00301c5100e440e550920010703050b0000a8807042c20300c03070080d040000103850016032a520140030b10f44505c4c00d144918103441b4046545030102155401c006010582419580c80301d03040f2505802e400d117035011083d07402d80440d50610300194200c03051000151025807071100501000b032024001600d0195603455210720450b0070301881000340d4001400c83c4a464200481100000f4103c1c040c1001081540c0301820058031448002d00459000c85585240c03401071040d6924241c00100920204406582d01402460200c40440205902100390710580c00c00200351001d82d0b0b50500101030421030341c0c841d05045050b100088070700765101c0200342c54882c1c8601101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18054368 1250 18053118 18053131
    0xc11010f0c0801060813020d021309050d02120403050312060604150e01020721030f120212010503060108010903050301060509210a02181003030c02040b030a0302070801050906070507021e030105 85
    0x1d0003525104000e28081c810303400b034001c019114003440312810540b0300326110140d0440b101c100849580c030100b078460035140c0c000240280b0340102281801004100510905815420b0742c24400c12440f48000500803400050021b500134030004020580c030403000fa4104000405190405540c0c0f04008000d600c0051990001246071000b1000d55804000c00300c0a021460786503d0403045400c0310405d104031004000e81040022500b16a0050050f0102040409083e0055549240c8407801c01050301c2c081c41160300038882d60f0000a401d5406210f400c078000d6050795804d1450f480e04c1812034040e042400069480340c0303110130304d1012300d40d0305181c2d0600c8010040504460720142c0100400306901d40540000a43c801c07082082040d500306011080da5450b09281e40207003100d0002c500203241068080d9058031070800c0c03140070b050700001c0c400112200040280b0042c0d4440382c81c4c6407100002c1c4d511002042c4240507107801490218018902190f2841000c400340380c40340002401e58030300303a0b0311 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18055618 1250 18054368 18054371
    0x100b03070806090304060906080412030207020f0603010b04060206090f0312040c05030d08010e0603011a040f06030606030b04140106060c020112140c030912190302071403030103081c0506010f030c11010f 89
    0x1b0003c0c02e800000d4040207142d51b00b00074105d1320b050f41b100c1c104021403100d44010194001001c01c00c40d80c0f070f07010354030003400c0142a1a849607112001c086841e4030a019a0015100d544001282a000040e1400002500340c02130340c24000c5440c5408284500500101c440242c05100030031152010418811441e8583c0d9980c84194904542c080c4101c1d80904003a000364103001c900a5201c070008100448040300740c40c006503000c0c9224698005008a410040c203041c01c042000061081c0c11060a006902800e00c1e15840d91408450f41c0c22101c1c50311504001c00c01e01003c100c00356002c1c620140c51240354901c0425040c000c240c0c0036007010001c840e0b100d01e002021060007512141045002918080301d10070703d19095846180c0510f409180940808040d0009030400403c44030303240b400c1d60f028800c004c40e078913940c5030300e401c0714a608900b0450500c00301c21001c2c0ca030f0140c500c0c0150743c0980c0040c2c6429001c8200310000300d000d0080c880d02001403018030414502c15007801d110b580081d00c5c84040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18056868 1250 18055618 18055627
    0x80102071101110a020315090a0203070801020c12030f040209041403070b1609030b010902030a020f030103050a0b0a02090f0114090d08030a050702210703030b0a060309050601050102010e100b030708060903 90
    0x9032844a01c120814616400300c501040146c90005030079003466001c40b0040b240c0d0750b4240403503181c2000220000d405010340301000440c030750150060b040c8c0a007040c0584100715500c1040d0161030000f210400b01c071710244400701d00541005100350303820034050085000c428001146d680d283d580144011504c5180d0030003007140c2d407070a010b10192800614a444100d540c81e549900040c0a010701507001801d034000302098545105504451061f501c000b0b1140d02c0e581d4034200280c0303034a505c000c00e03212501030100003120b92003e40f08542504070001c19121103203c110004407a203015003825500169010060448240e68156090001c83c0c491800e440da00d280a18211040d1100a80030005650104031201a007101c1c0c070b15240c0b04c403400c0c0300e4503544a11880c2402c50280c9140c0310515000320290102003503813a030540204007814068011900c8a903079600c0121708030344a0311400010360700503201a0703260200540024038254002401c980d20b00ba118480d10381172460aa4441896600006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18058118 1250 18056868 18056903
    0x40201030b04230c040807080709180c0b091201050a0204051203030f2802120103030201150608011419090207021002010e0a0206072103060518010302060702040b030708010207 77
    0x86541d4240160390070700080071004074036284141a412506a048242c00010341400110f005440042030a0400c0316200c0e96181c40e120b88402d01c0380501e4040724100901c42031244064000c029a860b400004d4508852510507031100300e8200c44070240e031128044288400c1c4110900940e4055000c03d00010303a55440e080400c012800c141070a05055003090040100c55500d03e59807613032110750550b82652201c2400f03000a40c0801036112144690710110700c10a2072010881103e046e40d01c02c2d00200030781c400703041c410000310040784101400946140018054078050313103807100480d10042c20b513581c1800c904260188684540c3c2001034802e40c08100942985030640740c0c2e41004803140020401021040074032516900e102001034040c100c00114001045409401001c80968486041074a4070503000010081d0426100302841961401081800c42d074003007400c1030403654010302061811101d0b5080c0005405052403165150140d00d10025112000b0300081c00464801c0589850b480c1581 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18059368 1250 18058118 18058121
    0x106020c09010b07140a0b070306050a05061306050903030403060f0f110406020a0308100312020715050f0711030a0503030406020904110406020c30010608060f06180403050708030108030304020103 86
    0x540c04144225001001002a29080c00803586285c0c1c2204164000030301c200c01581c50700f83c03006030080c0040744540800c8002d030b130315a100909842044803010300d8903030788004101c098002c0c800e8502c4002c50074003003042228000c80040100c00406402e503424190b03a520795504075030300c44080c4c2407038980302c3c2024107100807188201c04080710070000003030400d4100b290003580d800356008010140941c07140407482e595940e8404130011580000400c1c2c44481104000351941c0043c4145988840580c891f81c0303029003d0010f54100740c16500c1203509040c8651600303402d5242c4036480e81e070035000d0f00b1100703c0400d4060005501c100d00401025079038001c07400a200c1291520680d1043d41d400901c014400c166000c01d404c11004030860350401d0400c16451441c40f51004041004414034501b0f10340c070501134042d08a40d0850341c01c1015101190307109043c07881041d400b20751103603100f00c88040c00205c0d0b11440420680090013860300d141421080c0d80d5038070280c0c4c42a049604141c1c0080100411503a06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18060618 1250 18059368 18059383
    0x50a0b0109030b071206090c02030c120405030c0607060e010203070507051002090a03111504060c03110a110d03090506040b040302040c090e060607030203091302130e0603060406020c1606020105010602 88
    0x3841c00020040c82d54445044050740904014100b0003e000201d0702842290000409000c22940410004403584006035803540701c49000034090240010a0118100301401d80702143d00117409064908241020815107910601e0129040c1e81d6542442811220903c0514440d807901c1c0c13140f40e580c07030144c2001403400b20500200c1301c4507030040049001b9511800046030440340e001c031b0201d409120b01c100050346202884103200300d0710808a0002010350b40a00040b241c5030103500c0300840081c011001075103c1c86658009800441602e40225080c1800507210724554060b00d0303d54103898480c400a1221350060340711601043c800705050080d0315061203044811511820b1407080685481180c004554000b441d940c030a01d000300719041407500a108031611100e0081c40c1c44503465414464500a400c032102d540040c411900000c641d1a610440d03103401008010003d01303055403a90b84840c043c0d400050003520740c0c02500c00c121086105d43c0503400c090105500041000d6060080c0240b60401707 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18061868 1250 18060618 18060641
    0x906080108070f051e03060a0b0a0803030402090c0c030c07030b070305090d1e050409060b040305010b06070b0c071a090601091a01120b030a0f0803150d0515060310090501050a 77
    0x4000020802d86000f00390b45400c03503400f0390b50840c0c1d012451003030f07001c0c4003034264a4541500440b800c10442c075005910080580c0011920310415a807600389059480c00110b0703000b9080301544020403007050240001d0000503291900301c038605031401080c20f050551651049443c044a0014000d1003030b010b00030385500111a0b401031540140509000380501c041400034400c0c0a40684000e0f84507114a0032a009004100405c1c44004e41d21400030ba50b6601c83e101c01d6450394039103000203101c0c2c038240301110361003504a40c0c1080f072901d5800010000c0d62080c081200c40034003134004041c42c1745801110720300c0b42030703210003070700082d89086803010940e0040b41c00c0303e60500c001581c958281c0e801003014025903401d0080040c4250300100402e00e4400c610364060312404c01340e038048080100381c000541c42104c2d81c80107007c115502c0303810f014290701c40c0d020007403c0b90003410500321070440000c681c6911113030003402ca070070085a40190344215003800fa411340c0c29075107817001c200c1351305018090306030b2004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18063118 1250 18061868 18061873
    0x904050a0c0e12070801140a0c02011b030b0a031403070302010b0901050307091a0904081b01020901090e042103140c090105030106080702030c120703020105070311190201020c07060906080108 84
    0x412540300240b4480c6000100d610520b41c0020060219404210f290080d040c58802000720300300045c0002d4060710121000348405050001404c0201d106010340a481511804103800759104030400f580900b015108031030700141d0240002022400080c1000307030710045c0e000559030364011410001e0a40300d045c00140d0003a450040100810380300001c802003120702c0b10303000003107480e01003e4000c0300459801e07100d82c0c010a204180414418144004c00b032809110300210744040c05581142d081c0d0040c40da4041c0443c0d131401b0304106124130302c028564054800c103181000030762542d19210501c00308424a03000690740d0381c1d0704180080c54070320313164000819001486c2820340d1540020580c5c03105014030030403c16940c012840341e44c000c00581d07001244003400d0700e201c01d942480043c8117800c107880688c015800c090100b1409802442043e0000e020000381c01d00d803c600000501003000c05101000845d0740c20045c0c103180000500070300c0f02400c41541d40e07260301c1c3e142c0b0754024648101a08031035a1368 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18064368 1250 18063118 18063131
    0x5030718030302070911070204050103031701090b061b0102070c090b10050304050c060a020a0f12121a040203131a0117060705120408090d0b0609090118081e0403080904050a 76
    0x3d8000890340c04444030100301003002c50300c00c032414045000d641002504241404000700401d42c104d00c031031080482254030552140e0b030b03806101f01075400e804152078001c10200004d030700c2900d082c502c00d00202e60010000d07113450703c4c4d90340d814011841076000291659503410050f000349014412440c0c000e03503514050b406c46c00c00d51034254a43c103017008041d1003104001003000280e4001e00447c00c036140c0185600806800c141403400c0341800b032401010005042c00000300308180d03588541c4441c0103460301c87e102c09801600c1400025030010b0319110124603071050910000701c0003400341411001c60b0041c5080c65141016564007080982104109900180c041011503907211040c0c807074028a04d20805110f8881d810004160b100b18103101d0f8011584240e00010b02c15a0782d0480c0c0220025920b001c0c080e6500d039075090807103c40b001c0c030008149850282c40d0201c0e144401611a542090403500034441c1c06011402d5241d010b644100c60180d13000c1114074443c070b401d102e269400300b01c441c41030000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18065618 1250 18064368 18064373
    0x605040c050f0702120f0d020c10080402040c0e040f0e01050c030f0a090303020d020c01020702030708192301061d060607080d0207111216050312091002010f05070503071803 76
    0x95020b82c1000c0b203000e80e8041000c006658803d00280c51031a880000d070340c603210034021815200c044500503d40588607000f00c03030382142049100451703044880d075501026501d5507400c00c006407a125584004008845188118903a994410886406900d40000518006200b096401d4820081c480c4130452000d004001440c07200c188020b510642e060000280714006180c1a0000d01903810340d403007864408a0f4103007101d0300542c000e1074881d00031421540d68a42e61380c0c405d5960501025840d400d4150400c4420004a5100c4400e40901806805840000c1800c00c11401c54450703900c0502d1020030320083c140c084522942c0e407a00160300b076500600e403610300e4440c500304e48500003e032021a0b600080d640c1c03d0203a030120240794003c5c01006082e43c48516400c0e40d50b40c0ac1510005103c180050000150920740090482c20300c90368414003e040c0514031f41006950700103d6400c2055549074000c02203200500d200e500e2051605803515601c80c2004440200032807440442511081d218501c140301 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18066868 1250 18065618 18065627
    0x21605010206070c03020102041e030b060f2206030b2a0406020318030a02150a090501051206040905070b0c03040e070201021c020d1e050106080c0a0905150415030905010605040c 78
    0x180004203044c0904000d40624040307009108641c404041d04401440c03052020041c80c9111048900500c441401d54441030100041c409005407210307409000a907070000b84100c8140215034490140000040896694480480045040b507900900e40034840001356104041108102110b8504110324285420454085d59a100305441c50a07501d08031440c401036079174204450500964054268820b140c240a94070040781c02480c150008101a010040f404c0e5100700c2c1a030b4140701800c080e0f403045440b400e041c08002d01d0f02000a9034140a007504c00300380344100c81c0041c4058503446009598a0b40340080c51282140b001e84000704690041103c2c0000700440308000f540c0440d500c00040c3e94141c40d01d40240208050039603000c0440c0d000110608403001640058100d8082d900c2d004115900e02c0c41d01d451610901e004040826521142030003036040116641003031050300b104191030592648100350100c0f0503141c0c050b001076211b00120007040001e0140100a16068a00b4820101140350140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18068118 1250 18066868 18066871
    0x9030d051006020334050c01080601030c090e090c030d0c0605100e040605060310060b040906062303060312160201020c19050d060b060301060522060e040c0201090b070c03021605010206 81
    0x46400c402c888940060b244110301000d6034180401405d43d42c4c611619010f501c80200001450100e0100070009205502074094451540990350b240854079040003160035a80300003130591180c0f4419150390106980381001041c2e48d480c80d035141c01030012480c4c50040c0581d00c0080054415082076502048903131018141c00350400d5001d1804a1150b03208804640b6081072124064003c60a095000a47c03080c0c0400800507150480360901c0020745400055403921144011500d100b04441c100480c0c40c400c0e0400b6681101004066a0702d00c42e0500120300e036a0030452008400c0703610100d00e802192380402c0000000b0304113540e481e03070080c10964242d410700c61034840c0328007412040c2d80000c00c201480d484021804801081581c603542c4441006101c0d400000c442e110384074618103a145501041180c42080301c06643d00c440040301d01901b48005840c8c1c03d04c180080d592513054503c00103000c560b03468410140c42d51008501016410000c0c94064240140405850b40302018000c1d40d03030104095 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18069368 1250 18068118 18068137
    0x13330207030e0306010b0705060c090f010f0905060301090f05090c0901060309050f0106030503040609081204060c030c060609020d0b04060f0b03090a05100b1513031b0e09030d0510060203 82
    0x1611600d40d4241500c1c072065072188981d05006110001ca8615509070107030080c54060001c4072890355480450b03056070310402d150160701456180c426030613907116003071882101025107881c450131956100421340c150000c3e000102e0440e160621032102c00300b288140d6501a0181c1c004001c440414030104141b140b040c00303180209a103c607034000520400308040d01381e10007124000c1000c1943d90804c65200e41003070280400044000d0400a0601000034004811202c0f5220885c9041d180401c190742e10005014201c0c1486100101c2034085000ca1281c41d0040060b10740c00759036403821030028411a0722640105103d140740080510a1900402600c0181c94030400041e58a03100d500d8860b2810001d9880113003580700301a60b400000c02141c000c00802c84040c0c903400c43d01c890511241d070b842c0c0500b104424441c0002d100030000f240390030045010b00c00c5041055140c01c1e40341c6a9180e14080222140c50a80e400011002c030310382002c1c480e2139482111a11625211030030300c40000d40782d1160745e0f00b9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18070618 1250 18069368 18069371
    0x30e0907120e03040806040c03021203210a06090e010b0415032102030c0303090708060601050307050d09210914030105091002030613050117010c030605030a08070c0302091333 77
    0x16101e9030441001207501500ca00401c0b1b601c1450300d85420b0140c0701450004034080d400d074034132843c00003800000f43c0d030305d030070460101c4140004050354a112016005000ca4000c503143c0000168440c4039221364070031500e070b140002c80c0000c6003a0500c002d480c0009215404416194030400115081d005d00321503164120641c078801166030001203203107000c1d0300c0032b40102e03000000034002e280400084d008211901c22058520680e1044015222800200d420b2000300d070003000401071820f000c0d44010031040c450100310102222a50340f010801541c0310402d07010030b01c2041d05100a42030300100111280d4114024020391070b0590725a0f46540b039600d11030740101c0d000300218185a035484038210165003185820845903035900d03a400d00551100440021035442c1030002d200351803003806000c041d00c4026006080e024655540d0183c2a0705c5864159941502c0110100041c0d85024605016030701640c68040d0003c2d550608840c4051000f22a4420303420b41108881c07034400e60b0603d2a00c12600500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18071868 1250 18070618 18070631
    0x60a030e070b040b040303030507020115060810030501060602010213140f09190903030207061b09050105280905030f01020a2c09010602240c0d05071e020307030e090712 74
    0x9919141c0030140c0c0200c0e15240c000300e00030505045600141007264041d0750700303200701d46034001c0c160300300c618803004082040701d5100184185030058901e942c00100c0500340078202130f070300e4950354211151078201600603500042c800c905509200004c00181c44042c51102c0c5207820000040d50010104980c0ea005da48108001041126292952034900b0f0f4940c80501254810b8a4010000e41c0050802c480d014504006188100e048842c0d00c9140102501d481e048c2074104070040d07819030017600e54000e4100d200c0210300250003d400f03031241505159144c44640c0741c180380070981046104c4091300003582c4103200342c4a5135503000480400002c800150702c403015001c0300e482c00d44829031001b06900403c50100016010f0390001c0c089081c0e2003080000c04546000d000b610f03811400130b960103c5030781c00501c0600e0381040503601c41c0c0e0b08141c030b44c140645051800620906a00c06458508015800102c2c00209154205e140e40002c5201221070030034a25041c0c801510340c03900c114403010350681e12003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18073118 1250 18071868 18071891
    0x904060b010c0f0f03080705030f0402120109020303040909030206010602030703020c10030209092e061d0f0a06080907090c0c0f02040b061318020423010c020a03060203070305070e060a03 82
    0x2109508142e801410805a20601c1c1c00c00c80c4e22060551821030004501800040c0200d20580942e40960f80704c4c420121151610740801500c80c03220003030720381c0c2c5541e5840312900680d03040008100804821101195440b5a42000f0342400016480081550010070034900000e5000c01d20b442c1070394085880d103c0040d5152400c0b40240603041c0e1041e080f400550502c180c1c02400b24101d4604070700110580d0054001010300070341246640b1075500071500840c003510300c0c1066101c06c402528405041390300000f100c0c170001125101c45502c0350002c1070440003801300c1807000384983d80244c01118403d2188107003010b802060071480b241c0180881c056407800b4011981e40d0341290114100041c8540d0300c3e12085d071301d00406205a80b195500d22556101c941080148074000c1d901160550528460030000a5043d0321400300c04030380260400070500d07a4100180c3e00c22209402440c0100001a00c034502007002070101c030381c040c18400038481080f6482c48035581d20307400c0b90785281d2030303260110b0395101e0a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18074368 1250 18073118 18073127
    0x30d15030204020307020f10060b2b0204030c080c01080402011706030708071509080a020307120809040c051909030b13050c04090f0c09021c020702010509090406061703090904060b01 80
    0x340c00c02540603000205010700c282c0d0009104d004c05411000303640c0c0d1440200c541c40c080b40d06522442c550420244031b41e4146560710404158401c90481290810591002c04107049034095002259890500041804851803c1014030390400d003e003000800d0f07040580000c1c005d01743d002208030001c100540001c116440500529004040036004c070340002d52203021070300580027052500000149410000945ca640009414044903005030141540c80d0410000c2c4072400c2d6810b03800d40d04c01a04100a0203540c03518410381d10207958640c0d40c1c584688d48903001c100c0c04281072034480104035041c039041c00842c001c0e09949810a48410708269401c04034a081401d164008046036401450004c05000780b0000d41180e1045500c2030007060561519140d043e012070040c01301c0034450241806030a9203800b1554000c10034035005051040c00e007030400300050840f580c21201182ca00752911070401c92016050140c601032080300b400340d400c1644100114141200050000c0d10194441e038409181d42d014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18075618 1250 18074368 18074411
    0x190b01140d060c0207060f03090b0601080408070803070903031b03020c01050a09091d0f07080c060a03060503100902030c0109050303090415031703010806010e150d02030709020c010f110a02030d 85
    0x400c2c10302c1500e00380d10000c0e440c0e2801c0d10400011462051a102c0040d02c0b034031451407a03035448000100c141e280c0000468400c04002d00c1120005001c1040c040410050005075209007016580c1e0b403000c1c0d00310700c1c000303200201c00c201c44002c4a1405e04c107080040d401085042a504080c80d0441c0c455603007100484010b5410b81c01817110318034090822419200c4005080c040300f28440c04c0700ca49083d0300f16480c1d0390b9070042c450400039070030a0403c40c24034a8440700800d00d4070054036000c01c240e5204c2d000a030a002240d102c1544440c0d451036504110308060201a040002c2400c00c880d10300d240c01c000c25224450124158425982c41c1415078006a4004e800c80165400c0340c484500300304508000e84299000703000d11066403080400007d10b603c500c1200502ca001445c070001a405602c1c000d0041d00c4007101d030100d038180034290000c074081456102620041c01e030240041060100d2400403411900d000f803044007411010070048e400150000202d850b10403081c0c500080048000d20500c809801 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18076868 1250 18075618 18075623
    0x209031903050d020c031801020c03060f07021e01051506091302030a1506050c060f010b040603091a070504090510030b06090408070602070605150901050901150e060d0e190b01140d 79
    0x13012900d11042c1da000030144c20a010f0285241e04109615801641e4030000110f0342d80d4075a00030400518000c1c031500b640380e00006a801180c004d403a50032006180c20800d03e100c441503a45d01c80030484044c4100c0001c00e00d1140036240d20b841c110b80400800c40d000f2803988203848003500040032032614402e030380c002d44240441100101c0926226200180241c0c415840c02c0c44510410002c690329054406c0c0030360485004103040c0d0302c0c0600c0c5c0102a0007401c1c114000762802c03210507000c40584000646020300c6409140c0d074440d80d850070b0503803130000c660025006040d41d4030700d150188001409100e406030001000c07a204003040e40c407890514128410a41d004200e41d00214a4108119151b0082d83c000d032400910b44404142d1803091140f03402c02403048507030000f116001007148421940c0c00c0b1070308914525010100c41e1420000c641c1941c4007a00d05580a1b60b680040c1d01d00803401e1003045452802523500d411100c1c4107454030342002c101030141180c60104803403243d50036076480f95201c440c241d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18078118 1250 18076868 18076871
    0x70e0a0e040807030809010501050a03020d030315030506010801060e010e0606070c08010207080301030b01090207051b0d02030f0303070306051203040303050a0e041d010c0c0302070905100b0d02030106030606030209031903050d 99
    0x14051402e503000790008403003100410118400328414400c1806941d050701d90217840c12000600e15001c00448026982054044c19030395504148110240450040618014802480254174113031456084843c1c81d0b01c501107200c9454018040300b80079824040e0880c2d012200107840f44000e062079000e900381548002203640c13002994000f0405200055070480340034484030034460b0303038854409059200d003102c002c0042c0c103d602c219004040015454203005405000c0800044403507012078981640342501a845500200401c0921a8103006d01e0000c1c3c0b8042d22281c04d00c03040d000d90241d8074012800000c00303005003c9011002d5074800c0411140e810310041c0140303c0316200103120042d030490003200c56269401d1140411f125801540c44590007a4103500409007245080c80b00d078000c2802918049038100c216200080c0080b01e5800f50240ba00b0b030010059580d40360010183c11030f140f9034803103418180140070512440d50b0100f004d162240f010303001c240c0620100c0c50b00701c0b00da104501c0e10f0b03000f80b03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18079368 1250 18078118 18078121
    0xa1806030504150203010311150903010e0309030c041107062a121b27030b0405030423010c1101020a0204020406030f1508030a110c030303070e010f1403070e0a0e 71
    0x2540e160300840c0c0214002c104a001d03040040310034200340d10090001a002c403c840c00c41c1c01440c106003103001c0d1041ea076101098202110140041c0c2522240750f101c109940c00820300e0000d920701480749003130b000d40c22030b010025074082400e0452607000b647e0300076210b259a91b9000c003071000e8444d84c810303a807003099180d007d4490b9000d1015110511980c02d0302c1038146044542c010300708840c0c140002e510400e840b05084080d0002e1141e80000150803000c44560f07941e9400000603d66080c540d011b00e10910141d52681e00b0280420f00b00300900008090381c0c611210302d2100b0781d0708041c58101c4950444a000c5500815400507480c00d1070000c0001e41080c40010300040340b076030560014106000c0e0507424030403c05001110311050581e401043d4198108200c2d0726107080c051105480e45041240964a0681850000a0558008032803072400f0070340e11400783e11650381c0501022800d15032814288114442c00c4001510f03400014080ca043c0712000070303c03003401d40e146032174170b401032040d1559910031703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18080618 1250 18079368 18079379
    0xa02061902040806070c0b0a050f0c07020a030602030403050403150b011b0f050f1b030105061c020d0b010308030105010908010c020c01030e070e040c06090f1401140f0d05010e13020d02060a18 84
    0x52206001041e203071455000d0104184100d00c9c050103005101003d0300702c20755182ea82d100da1860b44540c900b01d901c15003000740080060f2450000e036100f14000d8490f5078980e031a60500306288214002c0d003c3c259031400940d40d910303a8003c002084004008800d000b0740840a1520300c02050101c1c201800394411f80e042e0484003400005d0740c1c510402048500b1030023103460b505241c281d82040d0741e86031b406004d559000e01031080c080d03803090310503000a02e44039080300701e501c401c24054001e07041964507600010040c00a0750300031914400404116008000900e0300b10700081d1540c007080c2c4d02904054541e04840440303a42003008201030102c80d01d41c01c07010f0909160800002c002440b607500403550445000034080c806034807001c100e0302c03900400411900c1d02d80045a11a2000001c4410a00284803072107046207941d010303203200c034040a0000f0301541030006500f00c8005c010702c5e078211444000c040d90300607107880181003125541a900c42c0d0b242c00380084280c030301c000004103041c42542544c800084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18081868 1250 18080618 18080627
    0xa0b030f0c03101406090915010605070506060603040f12210b040b0a06050406050c01021b0604030305010b090f041107020d0b040c0b0a0912020f040f0c0e03030a0206190204080607 79
    0x79100c10440840700d00896a0310944180c40000281080c1d40f41158001503441c10400f50300c5038015070001c140c44030f03040c2101c5181d8018000b170300301c0b50010b60042042401c020080102981001003165030302d0551500350b484111480411800034144400741c0c1c014010240140742c283c4080314125410401030b4070102d0f00500914006005501c1603051003103d03552410001d134810103a42181d50351628041c2044001d80389548504500f000c01d65080280c03000100b9003c100c803820701c405401810301b900745420020282c4006030000c4641c0c01e8200030b01e6003280e45a2502d01d040c41020394011445500c0107182624501842001039080381d1020400801c0100c8401d507280b09038811801407002c180c544110780700c00c2c00b41c00b414801141c1442e10a100c00795290100d06060303480100003030a152016008101a9642e00c66503214940d29a0000c00b82141c00050126407950154011420314941090082d540c80c80076200d1400e0454541c1c5e400196486a011035010301410b000310342060402d001c00030f1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18083118 1250 18081868 18081883
    0x10f03090b070e04050c03010518090f0a030c03080601020f070504150e0108010203180607020303010306090f02040f020d0e031215010c080304051b01030c020607050a03140c220602060408030a0b030f 87
    0x113202d0b03807400c400142009070203400d40381030720b401422545601068504401c040349003c0d18061f01c0c4c2c441c071142032a9000c800c10040000a201c5ea4a6404601840c0b030007810b546030240c811415504000004030500900090b6602124400c5802203100034080c000b20350f801810380c0105004101190000c07500c040c05400445c0122280030003601104806d110b51a101c44080e01c0002c0143c10820040000c104940c002c400b03168044d001e81e91201402e40e0003e412190384000740b00d29190003081c2d00401c12003074498044071110b1003015601c0c0007074034520b540341c0500040030710a501c2448040e02000ba44500c8040154070350200b10907541c0d04080c204243d803014941e01040c3c034070007400001052540b20740101c4140e134845800510341d076180c60100f176685801c50001d100c1016602c0c6611984810141c1250f4051031855140c50b80d07420384924860940300812a00c0d0a00f9814102e04110703465000031f620b6403245d00689071640b42e440e0350601d48040c1c0108400030f9814814100569280c03000819000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18084368 1250 18083118 18083147
    0x140a0207110102151b0903061302031b030303010e07030e0d0e09070306120b0a0209030706110c06030f0a0c020a0206030a0b0103061401020a0206030406060f06090e0f1005010f03090b07 81
    0x403003505803201c00480e900c08944808044101801011410150030003944400d134060700c03042e56040c11030b0b40740402d241103411111150102641048201542404d001c1c0b00b02c010060030a10601182c82e0700440c0e82c921041c450000c0e000710ad140000d007218420f9200502e07001c445002c5c2c522007008031000a04013100d80c02880d2007202c010001c900703100d000380f00b10b004440018180c003003905425159140105001480407000f1a000c00642509aa0070320060340506015219102500c0035504003d16040049005034011101001030200d40074080032141c0e80302e40e61310b4021901c0400d410003281840c02c4000c009402103000f02c01d00c5103080403a00440d20102003a0380c200122655051020718096501c071845025811400758000503042080045901501602001c184180c0c3c1b98250800480c440c0c0c0a980002c140c05000d0210740282070500f5000308400c5584821400c00001c05101c0840234824a414401d0740e00100705020300a4201075001904240021070510341050083c10890120750740 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18085618 1250 18084368 18084383
    0x70804090b06131401021002130e0f040b1f08070b0c0c0d080f070f0803101a090f221a04060501020f1207080d06090906050604140712140a0207 63
    0x900941e800c04400703480a01c100c0502080200345400201c010401c20b002006046008118040d10741b28094001400020202c0e0a8405218504045000910380180c0007000400e61101884041007810b2003650f00710603840f035904018580c20001035001406c0b0b40c0031010314080c400b03000508600d1039003c1c0c2050140340040e207098146c0541003150300412600c00034041c003818440101d01841107030107821a98468400303005030a800b5150102e0725001142c00d401d6401e01c648040c00740c1e1031801680c1c50043c00203c005800c00c074071035000408480c0c8680e400f81c01106011907401c000100c400802100520b01e500802c46080c40744816a0401d0340305618501035418050f000400e5407000655095500704c40003e41104410b0f520211420341c0300d02d5064070024824807252000d00c43c140705180042000c034600003036941040c0782803401c6e0340008001d1446a46042007080e6a07826218186600c40c0c0c0520b0070103d40e944600c10b5000070003a01288200c0c80340c08108004100b00b880d401425041d005824 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18086868 1250 18085618 18085631
    0x1101030516210e070306021e030121030c0210020a030216061e270e0f010302030a110303160b0105090109020406020a151107030512060109050127050607080409 70
    0x6030440c848001500d40740c0018003040201e00b540c044071030841c01500141001086480c1141ca101e440e0100a80044d10011b5000038141e90428003031100e113000101e900c00d19821076241c0044a04d0f0030410b42001c00d9102ca4680c6410201445010710744003165009180340140c1d4100301d00207650700c00b081c504801501c180400880b811113460014002c03242e0541e5040130942c1c0c02d4610341344170100c7c840218140814807136003c0d4440b901f0228100e141183c84c0050a070340e458020071000c403e002400c2e036440c102c44500144050b813008141000280d42000010030350000680100349144142d042204207c01c00415660800031100e29450407034000321034144459880e2208a0f00f00c0c4030700e1103030001603031082d1040c2001a8000d80c018607191114280003130460707001081d60440d54400d0004400080c4001074000da48071501e400c05800080070318200f2410f50612002a1001d4803d1004540c0b810f600b115500f0100812140b5501a2101928840c0c03105c03401e24010015402a01801940c0c904105 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18088118 1250 18086868 18086881
    0x60f0714010b10030b030312072706050301030b04032307060f02030610110102040305030d0207020315010b1c020415020c03190b070807050921010b09040c030204020903150411010305 80
    0x8078250710b4401000300e5a0303074503807a030180c004040140060b40c05000600c44165a0307040b070a580e030b20803d1306868a0001c031170840ca080c100c03044049518032450850490600103030303a119041e41e040d2a13014285800c4e6880b135041c182c542d600c145c0e09034100c07015407100d6114502407010190108520941c000e0041c201520540c0c4141d01080780c034960000d00d5007141ca440342d4410364922003072949405c00140b80c0b503201c0e15224110f60000201e0140349400040400440c10100520105010081c02084a82d4100b200030f07140d91080d214144001d01d0035820400041034603904135001416101c014101601881002a40300c40044030800c3c801c4c000c40d8038840446486000f6407065980c0040112400d5481d07060030b0380c0182016113200304105090004c40015255250f1107414108040e803954916801030701d50509454034056042e0080f00301d60240070015100400040a4035411600542c035031150300007007841c0050040902d01d000004000748002c0c0181c60710010684503082c2d8040c4110703038030b60 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18089368 1250 18088118 18088121
    0x50408151302060703050d020a020105190c020c0112150305010606080c070b01051306050d0b0603010614090a0906090b010303030e100b0603240a0308030910060302030d050711060f071401 82
    0x2226040060314400010400515003d8014100c45100381841070034800f5142544003260481206040580c2d598805c2c0136601d02d55444107900032404580a105030398110310000d4a03411401603150500410030109a00c081c0650064107410452401110b00b40f45e403401c0c1039018016a104000221b088040407421951034441240e02c440c1d00981100c400740d107000180050a4824079103102c01c03650390180809c2c6a82c0b85480008517078011195207a042c100081058211403c036071160b05107140d500b03440d0300035071101102d05034810607491001a95010301e06107030025103000301d80200381d1b10b00b4030004401c1542650200804201c40c8007150242e180e400d0204007100c14000c422940301700c00b440058520340342c1d801d890744620018a8904132a00780c82e80460000c4080d90403c941d920004810484103000c02c100039041e501c901d04050010915640209031a150840c01c1c4500300b0900103100c205002c203000c5608104000034040700e66135100c1701002d61954002000480e02d000d80f1441c0000703a003105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18090618 1250 18089368 18089371
    0x3011703070305160303020405060d0c0212090f01050d140f0103031e0804081e04120501050f1005060a02030405030d09050f0306011a070f081b0d11060414030d090305040815 76
    0x260f2220342c541034482c5101e41ca07100c02148100c080540810020400d515020060300001c82c06240c0416140440c203400782c10549413108000007144203004200103030f03450030b104030700c610400e083c100d82e160340821200c800340106820b84181140d50006120380c0d4500b542c0d800e41200d000766141e50a50020f2019161b0030802d83c0c41d020000b40b03d9002081c04520a8002081d50f010070100c0528804a00440040c1a42140e031140303000100101d03140b000e014080c00341640c842c4000c0840000303481c00c2d91707a0000144107400b4003400783c2404200c41000c1e070300030011103000d40401011503040840b9031800506084c0180145401102c02c1e048030082c42c2070002c0c0c41d5041c0c1d41000190a0489007503180c2107540c1d001900c0c151087d040904000d402304091030014180e030061b5504285000071441016031078280349115020420030385903c41b8042e18400b04d070b060b0304950700c9110b0001040c0d050311303007078554080d4610203481c4a1800500f80f0415401c040100300b00d0706104145c2e9442102c81d1080d0410020 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18091868 1250 18090618 18090623
    0xa0e0405030306120a020a08030307030b0906060301030f0201090806010f03060606030c0e040e07051c02040b120d0806120609010f0509070602030f090301060b070b0105031002030402010f0c0c0503030f0301170307 93
    0x20610205000c0d10b00000c2d502c1c65101320a0031615001a00d40001d607074a10250300068582c0c100005100070250b15020b0084500c5042e500d0f80c00c00e080c09008a51035110501c000b81044180c0700101045a10aa0b860710061a200c1c0c00ca9000e561121004c032600002c0b4801140c54034541580011014082c0c05103203034a0445450b000c62070348248060002524200072446e081b401610004215aa500c0006a0210030720018065a44042c2e10502044850b01041b0303038410912800c80d81015080041c811584008510744103070151103100100b003503480000d4103010b00d40512410400d4011056120607210381003c001070103591118146603446800c64050440103800030003240014403e48001404050000340c0000780b83e69861280d101140c01c1000104c82c0403000800401441c942040741c1202c80c00c0c80e100441c80c5040550000c0c00d402003400e00d0030148004006150280032070b40386088004c0501074156551580f04945130388813a4400d0044a4103555111b4005000030400001c5c0d603913899 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18093118 1250 18091868 18091873
    0x30b040c0c02010e130f09120905030303010308090301090807080d0501050a0b04050411090405010b1c11040e0601020c0405070201090218040206031f1503060311010e09010501110f01060303020c0a0e0405 89
    0x10419001160f504c000c0d00c0b695a00011094190700c6038013405c0c40740400450f10b0103000034081c1c44a04d40b0001003d10383c02c100e4100702408005210583d80032040b00d04480e80940100c0e0748251580219025080904010380080c0c1c000ca0003505110354075004003800341400e2802c1110f6070300c03541004031814507401a0510500180810b100e641090703480b040c08070380c43c91080c5013404a80e000103802e460090300702d0080b4010102d034070b0346100b0b004c2c8203d4100000c10b2405000040d00d0701c0c01036231a40100e10a1a081100d100007046641e4020300502d00c5a000241040c041441c12841c064003030a00030008a0040b902c8002000c02c0542ca251203034051a07006151a02e50349800040d0301d04401290104100071040810000e803d40c62490300c5400a1040c0e01d0103c0c140d49142000002a0b11246015042c8070300840021629070310180035906441007428001d60f004552192a40f0f08400312522840130741c42d0400100a142e00000c001c0d140d0b040032103c230072520b0b84541042a400405440081c003d9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18094368 1250 18093118 18093137
    0x2030715111203010603090302010902040c1809020408030a0e04020d0c08090c0108040b0c0334030b040203040c1a04030609060905061b030103030c1406070305090105090d0203030c0721080601030b040c 88
    0xb28440c2d0030031487d00d40a480013080140007600000d0458080070012004184000101c0c01503c0059040f940108144d40c011410180b0f480001a01e9100c2d1351030718420000798041c0e91280e42d03103e074191101201c00308400c1010034503021020340707984800e4a05816070b00c900d01c0c807071030558850f2122901c42c580c800091101510380c51201a41a000500104c5c2038020030f54000e5051031250a0781071401128850341c039a01186040058100d9000507042805107004004000200c3d0020148500311615072103a413842520f81100c2540600444d00300510003030401045005000072a00b00703400030f90059090b1642c6407517170b0681c05400c0102c14003035032510303d0510042000c280190f03031210042d409040003982a0b00805d0640d410b2100480384c4101007030b0703141c060109a6a00344241030b44003080c00010140000101006540c0c2d000c02011076520003000030b45101000303620404030f911515041c001001003040140080d00400044510900083c98100c4220b000e16060280b00f070100e9507170300d9840c5030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18095618 1250 18094368 18094379
    0x611030c070504020d2003040c0e0906130602040b0c0102090a060206011a090103110f0c06010609060210110403021c0b0c03010506042105030a02011a0303041d090a0203071511120301 80
    0x180d08070940b175a096644e1000c2501881060103104103562900440d5681d591502d0b1a0925481e00107422001c61840098200150b0f00b00024400307400c654a0f800148040c02d01d0718100700644510b0b00b04030400714001c0303140307181c0c203d0540207000d44c1d640445081c4941034440d8030890f0b44410074070401c43c0c504882100e21601030300d024010202e1035010324003c1201c1912428060007540102c500103918080001c109289110038407560380901005e00e4124001440c00800070741e01c0500c0d082c09488241e8440c10055000d0040003250000c5901030103000003551034401c8a1040040402d043c1d88108203074001804000e404002c50781030b10801003405084c44d080c1410800440103120108070701281c520452000f05004001400c0c9031703241039001180c0b50f208082d140905005040c051030180e801880b0510280388410204154030210b90082c00c115600c800001c3c1c9801c0700851301a415014a00d004181d2511115507000b4103451500c0380c604144240d49490354039040e156801040d644180018001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18096868 1250 18095618 18095621
    0x20316050c0402120609100303120c020106080d02030a0813080d180f0c0f0603020309030a030902060f0301060905010305130b01030b07030b040609050604050c030108120304170d05010611030c070504 87
    0x4265004800715001c001c16003020030201e07880411a2106542e146041004074500254100c1d40041d1504a613046103186943c094001c004a520007201c0b42d480b0700404004034800d5100c1c1000340300c0002290340707400001202075140e030b10a010a00000e4041c3c0005101c02d080410111801d59000500310f2805840c50300d0003008004801b108804441880403d40c003243e155030f9042d100724000c50003070440d0b600c2c024200300d4170702099002400b03041c014410044041d1000c400e80e40703c030341c0c1d1341004a030980c0b851002910318454140003103110034002c0008500507a100c0d20110a88801382ca0402043d1214018000b80300d15040d0001c00d10b00c0b40c00014800243c6107911190800f09034200440c803d00564002004e82c3c2c407070b0704500007090390f030020828980391034001c1c40d4210040e207003d9840c40d41020300580d00c8048400f0810508040080840d08012420b195031030300d1290745100076201c082200c0790801a10007072090500188191040070740e17511022007104e0945500b94000c01095142605000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18098118 1250 18096868 18096907
    0x2030307050304140303190c02011e020903030424020105060105070203100c02010b100804020901050108040c0902071b080609060a0c0e01030b040209150307110102030c03070e0d020a080a02090a0c0203 88
    0x40c0d15000c13500351881d40c10802c002450066152000030901c1000510b0100125a02d8040c00d02c216810604407006254078141610020310f582030000da9a41100d6000c01d165100c1c0d6805000c919180798050411030071a000b4105e24201158024004e5444005c01100c4a0048800103541a003100c0305c103a83c8415107900c00060030403140000b0072407495840008150002d404896400302d04604108021840d0510480d4050082402d0201141c10b1944841451002d00e005642442d40d00250307040034000407030700c9009024100300d00c1031412900c40d400503031250415200d1000e85c1c0f003403102140452810340100b4480e0745050ba10030a04015100044014101034104a50060303420031102e20729407203940460000c01e40620b1096542c2c206602c0042c0b03000c82ca20349524443c0d10600034402c01e00d12103021680c010069113084030301d60300604006021203d500000035032000c00d185e000900a0320204154103c507008172061003480e584c5203001d0054131002c81e01400148c1040290ac103039145411b8401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18099368 1250 18098118 18098123
    0x1006020d1d1807030606020709020309030405100c0623060102010e032a070906061202040b040302040c0e1207090c020303010f03020d0302030409020309010209040e011802130b03030f0a0801051002030307050304 92
    0x1608441e114030207a07a1064090f9a40303000030391140d10a000a40c1c04004e40402005440021440c61a0488100b0385900a9007d014800d000498030314100e00d224440342032405800040411a00c0d4201c41c55500914100410348260301180000441a40c0103200e102080c0e01c0307000166141c9084c1c20a00c11202144000c02c5060819600c0c1d1803100c10310800401010388100040080e1040c02c140024194030039400c410007105004000c14040304840c00155421a41d046e03d020034819100501611100011a00181c00c0810041c22182c282400030b2500c049a140d00d20801295015071412a00c80c4024000c110746a81c0780c0e1010001401d100c58650759040c000c1c811703681404d40356521a4280d90040e51120010380d0045800040b61500b07108512000b0052002084216606140003940f4503030b0300e00c0a4031a070440c111200c0e802c042d1307400c17605140f07400405a80d6074501d00040030105820410700d400c00200d445001081605040c00c141d48594039079001141150307205c0108403510740c4020000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18100618 1250 18099368 18099379
    0x81b07030201030b0d0b0c030907080109050d031404031d150a0804020109060c0206030f0a020708030106031406010305151002030d020d061e08100504050312040b19020306100c020a030b0106081006020d1d 89
    0x2856000a10030010300510441c082c1c005040d44fc00001d0540e0a00500d80403014000303000c0c0030003c0e03000150b880c5481221110317041045040d200103001c2c48441c0142e0307000032070009080400320360301c00c00c0141b0580c0300341c90354503001c0d403501001c450500d03c0e028000e42080080021820310004000c8580d401904001c002d40703010199518921150400e034819800300c0d440b0150800f11502189841e980070741c00303207400c11447c5041070801661900280203d401003840d0340c0c08420040c428011108440d404e0307407080d03590f00000c00050009040343d10803c11100007450407080440c0d491901380342241c1c40d0320000d140c8480000511401418041e00803907107407004115100c5494240700d210b510030b60040040414a06d814401742d0101c400c140c0e5242c074200e10401c2044200e03030301c2c07044c290044100c0e454030310b44005992000c151101c4207608003401104818000103885a440a0442d20882c01c070110000c10035aa40f0080c0e0b5203072240580390b0081041425005000102801c2c4002d00050090a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 18101868 1250 18100618 18100633
    0x60f120106031b060201050c03060d031107050303130810020f190512010902030405060604060501200f01020c03130605070c0504020904021c050a150b07030309081b07030201030b0d0b0c0309 83
    0x50b250383d84035010075000b100d26030f40941041550780a21415500c00c4901606c00d10b103241c4032000600ca0a600c039002010301c030040004c0e003c0030790100a0000513210141c22aa65000a5810001064201d221741107203441414800c1a40515600030b407200290120501e0341404c44080d02200034042d90030b06e1400300002803113140c081c8014001007600a00003103800580c0c0f410306052090610310002c080c0d0340602d080140800950741c0c04660f810001d200041104060b14101c051141001c62280001d2865800410310074100c6178084000c0071011341070010354801c0d65480d0016210b600030307508050320402003400200018202600204202c80740204014980b19440c000395409a07850713034556210590301c2d400c1040800552040020301d2209110100e0650310340060054a031040b208001e080503240c40c4407101b0020b0801c1510042a00800c007502c84080f1a50980c0d074031211480140d00003424981d1001c05810008148200301e030300259903070f17859500d580105043e584058502c500078071450302e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 18103118 1250 18101868 18101873
    0xd050102040905060406170a11010c05030c0d0f0810060305070509030105040309030308150d060e03090a0806071403011401030c0e03100203010e0c03010501080403030504030201090f08070515060f12010603 90
    0x4001c1010300704414001480c4d003040310500c02220141c0e0020119040d0000c0b8015038804000346d03043e80c082d88030038039800030f212220040f00ca402c2130b2600201148000704281c3c03804180440c2800781c00c511a5906191018480001c4450b5107043c0c421382000b111204062140f00d00c030b034203c80c1d802101407e2140c9800345001c08207007121130403202640083e004060620030141c0c8282000c0d0400c841040340003020f14000300144074045001c40040c2040e54403000082020390034810340d1520301f8010185441641c3e1660807030b41342d2a04550f03840004130f031a180158260301d48170540c1d0507940b600040160402407100154001d04844480c07506004c01084414007940d4201301c0b402c194030617014050f0303c0703500d44600000808400b5040c9010440280b0061266903804603c040e8810707018a070105064030b031070038107034010219210080c03d0070800b54400401e20100c04018031007140304004941c03960364400555040100c054410035400740d2140b4140c0c4440c40c04003000e47d2854102000050207031799a0703 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 18104368 1250 18103118 18103121
    0x705090a03081e0a0504060503130203070303020a0b06010f091403010f02030106020a020f0d0308040219080303010605070209090c030c1201110a0c120305041e080d09030908010e031204110d0501 85
    0x3503100320b80c01c0c2000500c0d40380b82500320411810041c00c0d44000b5040c00c210600180c124080c9014640810501200190001c070300030b06000c0c166900541038800d010b441c2d08009403203194040060351180b54010203d003565100b4040c50540a00c03030782d0780201d21401c104030014000c1c2001c05142c2e041d074031441441c014010920086009042c0c60700200070070b009610522049458012a031485201c00075251400f1a030025165580540e0440b40c4030300d00c10035902105500700340e64000e00d00510001c000841c005810000800d80d10303008a40031900340e40c03400040c95503101e01c64251505500004003821350f43c18002ea610140d851403c00200c3ca2007100c00c154003464014021041c00109500039010a100744035500c074145092629042c441443c040d01c40c1c2d200341000750440491852140050014044a001520406283d8105c1403029034500e0800520000300b5005216171540b0b0906150f4400c00004100c2d011464407504643c011b58494031450550040c0c60301d141d40043c0540841000268203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 18105618 1250 18104368 18104389
    0x90b0412290f06010f0207210311060405010c140306011d010e031609050f09030301050d02040e030a180602070812031b0403050a060b010c052a130e190803040605070509 74
    0x2a61403881c1c43d140010005002120394030007003007075420480060007074850100384c1401c0c031440c85126070032907800e03483c00312000315228481c001d842c0140d02c10b000c1005019005500d101e1143d550f0355045a04020308219036200c180c6600c0c0c040740c0c250485e0f510713406032020044102d080504083d2a0b189018002c6401d08018000c1e0441d00c4000300310a0040a04600c00e00d034011031081800800c3c0d180110b80f803a5288410300900380b02d9800126550300715901da030003c000c0c40c1c1929007940e803030311201c0801500b00794540c0040b1b10800155030b00450034070720006401c130031940b400c001041c90000e0b00079a40b0660b800070b40500201c01240701900011000340000300300451144000346150714031402c01c1d5003258000352065042111408101e0041540003900c562219124028004d00c0f0018418a20300040808a079a42040f48018056036581041c0e025414655104040c4c45c42043c0c1004d03a5242184181d50041c1070540034004200440c0c116407001ea88a04e050900c10300d0808103d0004500502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 18106868 1250 18105618 18105631
    0x20a020c030105160c030c21030507090b030c0f03040206040302060304050f240f09010609180302011103040320010216081908060303042106020a0203030106090b041229 74
    0x40309155801c091040d16032203c480030b928608150300081c010303c0c1c4a0b19060141c1001354103d615014080d082c108000c60015940c40040b0b02410560b000d0302074442110140c1c081191124001804500001124800c018082c901c528000004460300c50365013000d0400d98200300f044c00f0100c01078544c8c20066004038050002072807441c0c00c40c2142c1e460300000c2a0f0f0034408801c240c0001c0c40f6104480605c0750800c1520541c00a55034803c49000e0044c0000da00000400d41000e12003a00119000100303400039009031700a1210031805011080d59103c03d60b030083c00902607100c1007031880c0e60320010031070007482c1030000341c1b400038210303141003003c5c03640201070b0b0f11094005108000c40800011040c8502c44500317181882c0d162a50010707440b4040c9104481d030b82021400400703c61640c410740700c04956440b0a0440d01d611030b03580c000355260024024100803507103489000c02c11407080801d032002c41d010310101d815a4042c566401e003800744801c0610b0880003069091280441c0c0c4a29010f11400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 18108118 1250 18106868 18106873
    0x20307090b09010b090105120405010b0a0308090103060f180c0903170414040509060708060d02090f0108010c022e09060504050a050705010f0c0b06030c0904050102030a06090204060e0f0f0301020a02 87
    0x3802c0005145041c2c0c4945416841040a0002a604402941c0030041c00d0400c00050340d84904240f4054148808041e610011000010040004002c00350899003020b81c1e04100d0302d600c92007042000d50060086456101e0702c20070f1862011100e4000c0c4400102c2490581010340d91790707032448070405c84564121400c0030045024001001c5070f0001a90542d4211810320885c2001c8203c580c4520018000740d0030400d02d0b00004055480e0340942c40500c90340605803104070701d82000c1c00550007200780180982e0b54202040c07000150310001e04002c055070910300507540654000300c0c0207100e001d2540c01d5844981c0365545100810518803405100368094006851482200e140541c00e1400681040c0e0501c05864591010503a2152020000607808482612140c40301800245802500c10445500c4402c0300100030070450190003440c05040b80442c01d21116840d900314405a024a002d4000001e582e813110401c80d00d4103a900900365007000c0c15104400d21017034003107420ba9001c50000c5001d41d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 18109368 1250 18108118 18108131
    0x31516170115110f030304030e1005030703110c030703080402030606010804020603070305100f03050102070203060c2106030f0a0c0602060601050f0a031e1a0a0b031005060304061107060504030f0206040302070501051602030709 99
    0xd50840c0c054101c102040310540c2b4140f16429019120b404041d0103130080513555865104400a11000c5420a200c060101c1c0c4d140d01251500501c240c0080301c08174064007170302d8042880c650003401c50a000301e0b80140748030308580d12540d045000700303402000e126194002c0800003411484455440f4080c601800c00980e0720612030050502d81500039261805250040190002c2c004511102e004402e0581507003a609d5223a2400080c50008450003c0c0d240f4010240004100a6410b0780f44c412503069809035a840d544100c015161405441500ba100941c01c11a4804c1d4910907400600701e504110401e42a40b04e40d86201001c80e1302400030341814820b4800400001e00c0d10201c89001001c00e001280e1540c41c00307950004200156214180c0a60801300c00700c0c08110240d00808120150b101246480b50218100200940710940d01a00812907585605031510320105900344110741540086c08018038140044a49070b00c1041031002c40d51030494010010f84c0c00f8494000204610b401c00b0918 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 18110618 1250 18109368 18109373
    0x4090b01031211060105040b0a030b07081008010209060702090406140f09010b0906030705090402060717090f0301050402012c1503010806060a03030c03030507030b031516170115110f030304 83
    0x50b03070352600a0205100600c20400124040061220f0558605031400300e5070081810104000d8507082d04014180000d42c4100725485500500c400d10405103541081c49941c0d48009071403c0f0f11409410342d8001008201c2c0354050700b001404950070a208110000c0c17020343c042030712201c00c40183c0d10032a00c44c1c031007824404010001d001e1001010400c46540030b60382071203070000c1d540300c0480c03140a004514550014040d5900c40342a00e903d03a41003a403501603080c98007d255980d0b4440c0c044a40308100180070b020450805104803882164180c441c02c06011a880c507140d10604c158070850088904070f020400c4980b1030700500000104031031070840c0ca03941401203c41c100240140b95901a01c40004200f0100380c0c495415940c8a825080020b903075110300394124007900482420f16018810502001c0704080e0030601140720350081080324440c00c04208007100c901c05140a54410520420018450f0010452a030326035180039041040d85c07208041701c01400c140c12012a004a5040407040106 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 18111868 1250 18110618 18110633
    0x6050105030d0903141207060e01150e0a0b030102040513020301031226060604090c050a030b15040b09040f140f010801020f0a0302031b040909140d090b160204090b0103 74
    0x140c0000c401030911103416100051100ea0303d440060207641504070405802c0c4001e001308440d07865400d40741ca95592150416402610f000c0801030f00b2076181401c1c0315605041845044180c5a1181c1162002c2d22123100140c042c0040c42000b550555007008001116500e5041e0410490040c2c5405600d0b58914244000d24181da01e05150501400c03d98444100401d20000b441e00248080e08414a03110500418000d015980121820f145090146400c0a8000c4040c0c04800d0040c3e40030302840d640982403041e120001142074603c0d070030620080c00300003400d00250000d440090000284000d082d0b0f00e090a56518030460080c1c0c2092a09003c18034915449850140000c0c1000754503201c048020440303e40f141144d020100b41e40440460401c2408403107520303503c0180d04145403141c1d01c0c0c040001c000c0460305401c885605450045402c071040114400c400341c0010744804140600d045040c100070380c054502807414150f40d000010050380d4504c204845103001e00c1c1350300c2c070641c150300e003102 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 18113118 1250 18111868 18111871
    0x16030204050604020a080c0703090503120409050a06051f0c08070b07200d08060d0f050d030c02010b09150613080606010e0d050c01050903070b030a330501031a030105040303090605 79
    0xf80036900420104807a01c0d00b0401258120700d94203501951802c00d4203044440c1d45050300103592500502004c461454601c10181c01590110a001c01c2030b41c5960401c0c40c00c8074240e214164129201e4060414000140f0205000d20b803034070b003017a601030841ca60701c6031010380c01002d0031a03e0f0301e038640500c86000d5004c41091900e4845c1051901c003214107a01280d940d55040c540481045801c600040031350702c0d4003078000380d51980001c00c0429030b0340910300b01e52510381c06444000041d18250400b0b000798414018100c0c801d04c003801d645040d450310b0305440705404034071081c40d800181c108810382c042c0e12005600c00061010401400c21030800000050004003880da40500c17a24440c0000780c0421000701d910920002d013400d1080e40c070000103000c00c1c281549580404c1401a0100420031000450340245e13807180c40e00700c01101440e4890100000f074160b4446440102c42000c10b00340300e5540640e202913100d8180c442010401c0c04235000190a40d60100c07400c4001035240d02c0c0c44820001e0500646 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 18114368 1250 18113118 18113131
    0x801020a02150c040b0d1b0903050d0504180203071103040312020607090518150a0303020606030f03131208120c0918010503120f07061d06090309150a030b031603020405 74
    0x2406082900c903c1c08540901d0203100040d201c0007481a0001880f6803006c0941a01c030360b0000d040000f0302e5405004048a40f0080d1100d000d03818620300c15900c0380c1e040701c00760340041c608581c01c44000340d451002908001c0410341400701c01118251041742c100050001144503540039006e902602200909140c4041d09907005d00c0000f00c1c0078131180d551005507802814416170011141d40d288001e81100b01114003030603070058403050010051650124540341309241c20b404403000618442e540310307524481c0e0740d02d580b0708a1b10800180001c0108024014041340107907159402c09515078002040074400740c3c2c1c0000141c20005006420b82402c00800300103d44008064441d0742c941804a5190781681c20180080c0000080d603441e8131100c2c40c1920400c581041c402c006c101c203504006111241c0300310b040344291080d0030014050460000880e0590040584101c3d2803600c400c103080b849030090001401419110000300c01141c40402c000e030f404403c0795891825041c5140140001c0340e0024208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 18115618 1250 18114368 18114403
    0x504030f0b0403030b1504030308130b071b0206030708090c0301090308070507030309050106090902031c0e09090a050f010516030902100806030304090f0903031a0d0602030c0d060801020a02 83
    0x1080032a05000340300d495560031614142a540d21450120014034606110540c0310800042036191022000c000d13000f6244243c44201c02601c1d003042c0c0c40c4c01031014007130041404107203a00007007055124074161a440302c1a03a040b81d66080e121b42c00038055410855030000019550b034208014110708004150000c942a0003c002980031610300804c4400002c189030280300c40000c005041502c264021401c00381c01c24000c0251589803c0d80401820540c20203074803901c1400180c03000b400c04402a400148000d484032032004041105005096038002c1c41c0148a00903408010085501032010102c405014800082c2518020201c0b510045d41b00c8683c0d0101840c10400340c006850307801d040401ca562a081c5004c03695180d05c0006c1c0340d0700c00c5401c900c24450801d40c01118615107a0881da29851207510305001007e6148109076524041414056100800080841c0890400e80c000c640181d0b110400515125034240c102d01038a031164000b4103640e50004104002c0c59043c06003a0b8525400d00c1d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 18116868 1250 18115618 18115627
    0x917070f0b1302031203060105040b120103021009081c030219020105070906020a031704140a06050f0a020304020609120102090a0b040801050711030d0b010e0a06030902040c0809101503051c0e0105 86
    0x841c2d52101c17032645201c400800000400d0060380240107a4008113402181e80c3d0341e4031200103a100200500380b00481c007481d58046400c540a004107175400c00d990181b0001c190742d1140240b01407608821700d5004050503400c000c01c0407040007002011000c00c031075400128803810024002441c0e611694402001c40d00024501700c0000e81c01545007a403105501d2030f00200740c461f810300580b6940c0d06074068400e4450b19800000b01308558108a2150301c5da20070821541e0b0b186001001640300894009500220130010044540713017039840c0900106005000609006186002c60f184040300d400030f60582d03070045410080b61500f401556402806803500d04400100a8603140d81c070300680ca040d82c5a00d4035402070307215507403050900c2c00d612103004200e020003a0b40e40030094020721706003100340e003e103082103250005140a04405ea0240090000504520a0500f03800006101964078117072095100703c030001c0854800c114608004001b00c401e41482e48607620b01414084003011850b050010510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 18118118 1250 18116868 18116873
    0x507060302090a05150c010203040506070207120804090207110604090b090a02040602060c0a12050708010512010603031b0f060204170609060408030a0c12060618091e0917070f0b13 79
    0x4041d00e04584003a10101580ca1170900003103154017070902104407946c0302000700000e00000090440c0502401d40a9a0050b6140c6402118019481d64080c1c9403810402041200e82107903401001418051480c1c500c1c040115000207001768040c0d0321140c00103403596a03100311480c082a41a8010a00550842c40c0916000c0040d444540c0140580f03c441d50101d01c40210034003c440030f04240c104603000b0000c0d840c0014015008002c02e004590143c1003000151400ea1014403e490550703805445445d4291134a99a01140e8140e01000305d456020124500340040c51500240029080c81003000c1c3c14000138200031803038540c0c0282544025803010081c040030484070002c40b60800e400040105d0340840400c825101d400302e6440184c1540e18029001804950003071000c1ca980301c86415031140c00360703540b4040041d18002c118462100c6120100c40c60071204503804107079210b105000200c026001107078041c0590300291015644480c1c42111141000180504281d1080380301c202818220b42c0354 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 18119368 1250 18118118 18118129
    0x180f18020103050702030706050a0501060906030504031e050408010501030602031f0612020a0302120f09010509031c02090f061b0712050309090603073303020406050f07020d020904050109050706030209 88
    0x4800203418540e5031000300e00c1e607500c2070044411440e0090424040da0038491400c000900c824418000001c109802c04903003103100303010f40c1e401503405544580c2c040264605007884030340785004440c00c1c0070b010000050214000c1c01317a14021406600d0040c2c0700d2034050f0105907604020084c54180441800051001f240c02c580d04007110a0780304c10044e11030200500070390091240794126000800118100310390340b5a122251482403c440b00240f21603280d1030b00300d5551740203031a030b81c0b026011790604404140f0100d6015180c0790400800b40d0b6061940c800c0880c0859000c1344e4041316416035040810042681044880004c04c040020740340d1486040d12026100e02591002600c44ea480b0b101103500c680d02008143c0242a2150345044c0e4000d280d0421040313040c01c3d0242039070025601c0d1321003401c64028425a411110305803140c0d860012a02e0745600c259001d0901241d02c0340a059180780580c40d60310840744218400e000000310000380c1c0c01c001d8500300301d507805030301054010041440151680c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 18120618 1250 18119368 18119411
    0x1202060f0d0605150702011106060d0b0603030403170a0e0303030609010302010e030a0c1509050d020303120415020a05040509100b0d0e0309060c0c10090f03030f020a020a180f 77
    0x102903041e032124034860030301001d0b0200d5445030b0341c00b01c89001000c02c0300b5404402044070901c00d880340c0300c296082222080e242c1e10100da1440d80f04c165041036001042149552591100000341030f00d140544030342d61101580e203000d124400c181030206041301a80e810145030b14a20800302c000314254035026000a5040005000090400000000c28a0b00e81c030b04000400b4040d40c4142c0341c21041d61101e010750354030004030403048002640e8040001741801c007183d100f5005038001e00036500e4011a82c030703159401e8070701410499002c0c80d410b4a0981d408460320143c100c010055403042d54982c80c050810100e290003804001c01200003c130304000710b01d050001c41d0b0b0a04e110140104006014814560940c0038814407190007010008559460402c003040440c40390314101c0b49032520043d00780d0216495030031800392003200098408140042400342148404085080c41216004d04855000c102181c225502807102d200210404003001d941d00d0042590380d10204400708650205585a4448490ba = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 18121868 1250 18120618 18120637
    0x31a0f0c0c1006060203030613061508090a05070308040e0718031106090303121b120406020d1805010e0f0a02010c02190506040b0903070e070e0f0109050a080102040f120206 76
    0x100050700180c04003062103403070100811044100095640e5000180d10b9600c1140c00510401c00180d05440d4440c1c1e0703100c4d51054a64000003e407581001d4907064405074800b92482c0405e10a544417440082c1d0108070b072001451090b4446030729a45407010050f12050081e101d40f050010b0700404610030a00901418200c0e43c10031101213007500c2030740214200b845450a03994250100080040c2100018020280a403c204c2c020380d004084c0c2c8440340240b4080e203180300b03044c10b04a00108010480759000f402c0e01d141000400034502d40441c0740304408941460307045540ba51a150404417514040c030507420805c1e954006428100c41640c0020030401250800900c40e01c01c031600101c002c0c600001a10203440007910341c6550325105c40c0007101d207400c071104440c030a200b41100880c401d008458200c2c0210240d4562011948802c001c001c031203c1032030b03403240c10401c043c0c40c00109540e07403003008002010041d00041ea82ca003008070f1403078a0310a981005c03d0200c8800b502000580ba4002151b88022 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 18123118 1250 18121868 18121891
    0x31106070504120f080c0d02011a150a030b040212040f0209100f0303051305090106020a06110403020f04051306020310051f050301211203050603060a0e03030106050901020f010c0207031a0f 83
    0x3044c602e84801a402144c50300f400900c25110380108083e0150302c00b400100180c44000440d0b000c0c0401c000d1500c0802000e800750000500144030000c1c000d0304880100c8400030005401c040c00b50075414501c113803c80d01a0344404000c9410000c0d41040303d0841e41080c0402c025510301e81c1000b900030041002888010104840054184800070880140c90052b120081c030420440d6510400203584403000e10007652114508046141c103481440101c6084a034050504034040c00c089080000419000300302800c14003040c2c5001000590610003140b08020410741600c0181c00c100c1404a005204035041c0d079624020215540803030b8110303013a82d0450310144901183d5400216601e1314480250b10000d0036900c424400c01000c50b05504642d100b020150704545c655078070007030704c0c0c41541c1a18285002c00e400030001488007600c510000c06404030103004071208086104581c07403c45260300c2c0c41c1030058005010620030030240d004c00140c244082991880c0380d017030052441d007003c00041e24450454 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 18124368 1250 18123118 18123143
    0x2120106031e02130501030c06020d090e180f0106180c0305010e060d03170a020a0e061303060c020a020a0f08010b010203031005011b050d03060905011a030f041e03110607050412 78
    0x550328003c0200f80d100313250205008030f503900d2400041042aa0081d2005401345903106902d1910805a0030112901c5019181098441034079091064004155058803801000f03449550310308240694002045a0b050a1038040d042c400040c00300c550001e140c4042500b400c0c0100244103800c0c5a9035040b00c001c69400610801a113000c1e02c07003913400354400e41c50381d04480c100980626070790b001e1b003040c04030754440700041c48032513080120911602003d001107050240c0140b01142c001e50003040c400c42640116600e0700c0305600025010846075018694000d1201c20a02c00482d0a008038002e1490a000442c11810004035984491036140601c604000d80340400b50000b41c0418119540c00b81c2120a403040012007000c0100504218001c544d922410900001040d100c000075038030071100070181840c15603c41c00000c61003041e002e0019908c10090000c041440e01c1f0f02d00d05408030328403986400600c6a1030038041c60801030002d0107074060003030a00007009104a0040e030002030661105c11146035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 18125618 1250 18124368 18124373
    0x10020304060e090c070f0f060c0f051209030d0906020403020f0604060819020f030f0f06090c0a05090a050a0605040801060605070b0601030b0d200112060303090501051305040903030902120106031e 86
    0x903011700703040a81b00c60b503200c045009001c054504684054000c18040c04040f9015605940c903295003200200012030030403c1143c0e801d562004da540103c071800c20303685008244269402a105902400e441c515800101081140740c80c0901140c1894151611801e281c90818090803510b40140211880501b40380b88441181c40d560441d08400c01e03e0614940705e0610032508141ca80040340c0c20301c203003002e880200c7c8041c82c0810009102d8a40130502500c0c200e05c2e00b204840c207800440c00303250000d038000408101aa124403500c806400035036920f681703403407030039800c242034480700d60050301801410803da0700442c2c0c0c50300e45c4541c0504e0a00303000c01e00780c1c81c003000b080c142114450054079044c2d0343e00c403c1c01c5000909d40c1c0f800c03401c1e4090f61107186440000300d200c0e081703c21510005000c41c45540b0100b00c2c55005001414041d542c0e0b595109100c1c2d6180702050a075118400d0480000e41d46a00680031882c101e601c0100d2000c03448001c0010320b0030b554400e081003600c021a040080c803041c404070308 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 18126868 1250 18125618 18125641
    0x7080c0304081906140603030f0c010608030c0a031407050307020405150406090618050606121909050303010509010b1809130f0507030b060904031407060f1a10020304060e09 76
    0x10302d160340c200c0709001040b804003545441d01c1c00301211000d045c8030b403c1c41c0c0745145102c1035001b01e4004024526003003000101c61840e600c5082c5000c00783d505c0b04030010301250b00348044d0140802c01c01c05845400454030340200030040b01d075034030000f03104140042e002084000065840e01c550507a800141c5031500311500074480301c1010380592040c20480c0c0840c80504e190461002c851400c018502c0705400205c0c900305070340007140ca55030411410b10491040b1401080c4c0c0c42e07005078000140401d039031504000c0744241c82e100c0b8419141d513800000100030f030741040c0c43e2060041851065035400d00321030005410052100ca00503074455841a40401d204160101541052560090b4440300300060751410310380b205002d2009490144e582d1000501c241040b2105510460341aa61070802c01000040c0132402d40000b41d0644003640e40f110441c00d544040d208410010341243d2400c4052001b031130800910b00d00e02c4801d0411134100b40010040c1541041c0c050b584110116940740d81d503a62201c0001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 18128118 1250 18126868 18126877
    0x50406050d0609050406090201020f0d080609060409020d050601050a0b190305070203040f030312050709030b0a05070201090c090516030c1407060f06060f030501050306041208090709150f0807050607080c03 90
    0x20009440e02007413000308511b039880001058400e03002c0c1c074141c5600c0c01c845a1105400028100480e030000d00064440c980118040d9104600500016000c075060300031a4400801c0c100841d580ea10401c010f110924001620900900d860b6a030f481c6480c00641ca111b07890b451403610b03007040c1364481010605042c028420f031009032645c8440c041c0c6030713070703903801c004246500004640e85058a0000810300c3c0f2481940100d0641b0b4201615403410340300c1400800090400400440031035603200c80110006100c000f280c0d008010805003c541418a090b00050314224984980c051601d4001b1034681d113a0015400c800001e40e540c02d681e1074117198200174000e070500c124800c0c0d03c50b141580110350075800903c0d082d00041e81d607600b0805030380c1316000e1541c4c429040d07070040d1a01d8944078840398114860f100c1c541d4410901c1041e10105540c403211181618580319858a43d100d580c903050100c0c11402d83c515005020b03a00c02840d54a1401c03022071f406119012020740400c80008040c3c240c90000c20846 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 18129368 1250 18128118 18128129
    0xc060207022407030809010e121309050406050108060703270f0606030803070908010605010203030406051f15270506030402030703050f0c040b040b090a02160206030c0a020d0c03050406050d06 84
    0x14041500e103101002c11540c0b140c001103001c12080c1c00450f060b4141440742c0b0500140306001464529014901c500c0d00f41c0100d6007070f600c100395200c40450002601c0c040c56002d2846180045a99410140c04600701040105200308040ca44240d02100c50b0780815182c030000710b150034010406405081c55040390103008400b400036818203400108103c3d0074001548191850b5413841c4e1500d032108015426100944586c5006900500104010494941c040d0f41c1207210019103502d240c00c8509901c51959103580801c4080020030290386035241c11107001104140c83d01c403d0402c2e03001d40c6841928901c1d01e401402c2c0241000300000d011914104061005140c001c4100c3d035002009050301075841c6440d54905001310704046800c805d0341854040ca0101034001030080b030b455510040504029080810b00b61540600d50300840c0c0562680382c01980a01040c04050350341c0c9102044c0689030107844140c03841000081060700001c0b0ba442400e0310b06550f414170704107556031130f0420885d0140540e500034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 18130618 1250 18129368 18129409
    0xe011709030f030f040c0803040803071104021909080106140913050f0a140c010c03020309010e0301060b04060c0209010506070510021c11090108010f050a0314100203070903060e010203070c06020702 87
    0x313203c06081007000492159100d503c82200494580d0f440f540c4034040d034440d2a9a9074001e116040004681e0208550507a04c00f80005081808426868440e0000f1441c0d25000c1180c00300705001802080c000d40c0007520a100888030200d9550000c6079525400621070b00114110385001002c008040c08400642c1032410120f030341204845c24811019407014001340032500c070707040c2500000c0d40210b449100081d05a00550708003051000190780c4450301c50140780d8103550760100825801c44000c0130b0800f411f0740743d0322111a0b811a10520901f407006030000ca1081c6010f008000000d000040c00040c800c0b011074005d0388502c1c4201010b10080d00c40d8440c00183d608008c40907050200361800f620901c08260382d0101e59990341d244030040000359014046d04101c6c4c210b005e00102c0d4904030200020559030088401d010b0000300c003031040740c1003540ea503000a0180b0000b00240300503402121035140460008524500300500060071340c101595000f45026000303c0c000c400d55944100395501d86662054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 18131868 1250 18130618 18130621
    0x406150b0d06080a0c0608091f020c07080a05030316030605180702010f05061c030c060e030405030f06010b0a12020d060b03160c05030915190306060f0e011709030f03 73
    0x8010515411401d920319580380340ca0070000d0f03824400500c0b4450719800804680f1120f00781101164100001044c2c0b500c54881d0382c01001250b22121000720849103005c03001a1602c095045060074883d5962044029522003403850000c85c00c040b0440c0e400c0070310441000000c1c021290183d02800300f41d8061070b0700c03007118440ea00030718100c041e5461244560354000c11039118941c2c003c1c022150f003520750a80140c900361001c00d8441e515143c940185003e4100a454003080f1764886003a10100381e80c0710324503000030074100014203042080d500006260400b801040d818064001070b81d02841c0300600410503402d40d220000503555040b1000c050a142c02400a07135128400940c582c0c8c03090b556182c0080760881c14541041c800c1245408065001c0c0c003035460485480104640101c04c2c078582d040c540020000048070462101c071281c8140143d40340810940e03d8540044c00005c0302c6d80c00300c414041c0f62a0229102c2c0c0e400b41d611140c41c0391406142600e916205180e40c0385003d03840c00b03884020320010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 18133118 1250 18131868 18131879
    0xe190311010e091005010806010c0813060807050c0303070503040206040806090a0b09030403030e0904020a0f0e040308070306050907030e1606090807050f0607031215090905060105060c030d05040615 87
    0x49801000c120282c0303a011100300108140803403601c00311a61581c00000310414062980b2580c030032904080305150100d0003a505864588040d880f00c00d04200c060021481080a580c0000c0910380c440002d00784141000e1640d20000c0e26071200800c170340308003c80040050f085580f003000351400342c01c0380800c54640d4030740380601c10365503002c05500b80e408000c1c820020b862404000304940951342c0c50f94540c41180010302c248007034658068400c0342d00041c40c88000c01c0c9140e81240c072900511840101c00d6441c01c1c5803c01a0110b8000b078104410035062200c02d22094403004052508510141350001d14a440760b4204e43c1054140c0c0c0300041200c0580900160303203507010b110041510364407000d0382e00ea2655081004402c400c0c490006800070000c1c000031011900a4184504101001701c010510b943c101c7d0035003085800c140c0200404075594091703201400810001d0f01e0140a0640314189040c2000402e0b603641d0207035260213100940c032840014200001a0000c0b10400041c0300e1100800f52100d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 18134368 1250 18133118 18133133
    0x5060a0e03040f0602030d110a021915020c060708060414011502070801020a0509030705090106200a050319030b030a020a09021c0c03020405010206220803090309030d020105060f1f0e1903 82
    0x10359015607ca007040c00c038512600f0003104072855007942ea0000e1111a40030340030302d5030f41c00c040303203082d204060560507500322000580020803003030300f009028010301d28200030701500b06030020300390b180a10b15100302c1d84110441540e030035040d1090f0046e0a408150b220038100e00e400401e402800d40c170350010070362025840d000400b4150f03503d81101659101a111310600c15405401d00c140000101c410a9a669200340d100d0407840d584940030680751960595102c4034915486180519101c042010813210f815503d445400d400c4401107004c4d0046852580010340c004403d4000d02c00310980c00541c0a9100c080c20181001070718201a00b40040c030000301c0b0240c0290401d1007580e0141c010640003440f2000c8080e109900c2011409421000d460143c0300c2c07403030a400c000d00c201414441008051500d550030851001d0100c10b40c0c3c0007050034038000e130a0003c1809810112405145906051070800040c8051459031445501e04015021030060026407854a5800c00342058140c13a100030050101c2c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 18135618 1250 18134368 18134377
    0x90307020a0609080709110409020915030705090406090c1706011b050a02030607020601060903080703050708130305100b011e09050a0303090e0c030903070f170c0109060606080405060a0e03040f060203 88
    0xb44c2d0b0a98008503551031052040e6022002c0000400404210602ca80f075416405001990005004030802446030710400c400c2d58029540b90001c02d40c04600c00019140c940a2140540502c1714248441c441100015155010001c446414100c40c140029002e91040504c40149041c030003040150b043e0303a05105403070390255603050f030090144400040b420341c0001010b41c12950f6503a80c01d410070746180c50703a40c1d440e080114210308100307040003264007051004001d4814000e030744500811070380c80d52400b189043381c2103020b05902403c18203000856a084200801c40da891f864052005030440b0348110f0300b545694000381d51100304a42c0c04420705520031070392010f442101131032000303d40700c0403580300701c502080320701899075403003004410b00046050a080d4180e5200c0d00301c0c10200c40e407940029030960800b181014960790350b01e1071a8144541d5002d080c006100b81e083c40d10030b50600d9194203440d60001000b0340c4003140c5550000c44120005c004940041122400143d94941c403000c00a440c0d520 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 18136868 1250 18135618 18135629
    0x90906060c010c030204090e0a0c030f03020109060204080d110c06040605030c040906030f0c0906120204021315020f10020906030f1302040207060912020c060a030c050d0e010506011205040812090307020a0609 91
    0x5081007148c403240c0700040001c0e5454100b4141c1d14202c1ca15070b03e1480c1c11034914022002c6540350140c00c0005692400940007611a00014040f070461481000300012040b080342d84031903016146a625644454040f1429100a86000e0f9a01d42e102d0903141001e2099078450100185015000014000e41d4060b61840303500c01d04640e03031500d95a041c0300080d19020b000304200c0200200440e00146001e5001340100180741090311a96551450424640b0080355080300168000218030100700c501448031082d0102120b1085080c41c1c1d081b40400c4003400020300c0e02c41303044031800c00f0410385065808005001a80103005550782c10051a04c0b4025140b040000c441d42a040c04041581c1400860b50360500fa4000e08400c4c00e18509100485c068134408124109008040013000440841801440e14503c090300003c115401d00c04001420b445082003c1200c8901d000103100024280508480b45802164500c2106881e51807000e403d5200b03540000754491310f800000980680c03c803458200f21038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 18138118 1250 18136868 18136871
    0x80d06030b0109060303050306040c03091a0109060602030f0301140607170d060617040308060118030f0c08061003030e060913050403080c0c030403120e1e03100908090906060c010c03020409 83
    0xb40e80f00041404e031a400c0c00002c0100f0002d01c009106424a58814092062945808281000c540e11840504180009000032150f003150040c401c0d090039002c1e02009050900c0250714121950001951500040c021036050342056405004071360b0340c8409a80b460354200400668441d9078a80c4404180c0c01106640e1101e4102000003501900505001c4000941c10055841c9a0380c6c9903821100818006c2009050008601c1440c2c401000782c02c25001851140c000b503606401c2078280301c000f004c250360100701180e01c9842040924040d402c0610304484c0d01d400c14040c901c1c041d4000802d0742c040c082c0002e8112a001084905042c456080103000e04d00070707201c5140607165811038201900c1a06607000b8554070030841000082e14144404909401915140c030290306500d00203680301c02c042004c0203000480c080d103845580b409005010501d910041300b00b00c0341140d42c0e9880c08500548400a204501e83c0001464944031503003101d1241145100030001090300e0880a0000c2d00540219020203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 18139368 1250 18138118 18138121
    0x9170304121e0e0301020f040605030f0610050403080715020c030d06060201050618090c100f0e0603040317060a03050106060c06060b03010503031204030e061209300901020109080d06030b 82
    0x28003654040302500e0908054122941c0010b1003992154400e10b80c040c3c241d07608001000210991101030405080240d85d01c44e62810007105044c910a4003908091040381207503580c002c41508541201c0071640c0c04800f80d520f0fa41319003482c0d4203c4c3e6040007000320150000404250b00700005c0010002d4060008040000b41e403103000032070813030300120f4805401c4150410702c0d40c1000d41d0b01c6007182e0f00c01300444c100ca6504030070341d000c10900400c0b2224034012550004281d81180c0d0401245911220291419419440c0680b0001c0548841c21072050a200105d00440c2d180e440310340c005005503030040000d11260303640d00c00c0240891042c03181a50310b07070314045c000304901c02420204da040360300050003182404821140d01c550540090300840901002d55001074041d00e9082c06401c108420050340c0e8820b00d0300000690511002901c0f5046400c1415000101c101d4141c0702c22500060110000e51150240d80060f8010308400708082c0070b9950209807964224081e40081094074410410320b07035076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 18140618 1250 18139368 18139403
    0x901020d0201060501050904020d02040801060b030f090604020108130204180318080601050a030803090a0f0812010b03070801030605060105070606180b0102070608010509270a060b030a020306040b07020109170304 93
    0x202c0f485401503500058041100050501d00350300500100910114010b107041c0d500e102c81c03401c490165000c251084004010070081061061586a0000c40040a420246440d03400201480002000b078070340709025864920a40d180c0e0350114088800d04030903281c0c407280a040181400b00402050382d4030090608011800200104903a4101c49000c0e0201d000a42136030354504c01c42d00002c08195040c071070401500c0c04a03d1861590f601d40340900c0341d90380e13100c852040c04401044160004001c2c81002c1050181081e13010300d0031070459401100006640d10340380b004a032036116190000d40003505100001c00e8040b03034625010014031401c80c0400141c00c2d14001642c40740f02c030b4450000840d12060041045003483c80002c2d40c0102c5240c2c3e40c140d03000e005140c206042c2a2000000d82d0b0741e1044424108006152041600c86102140180030480b4941d002a41d2894010f0000300200c2c240d8000c125164001d41000d0015944a000952541c020181d45211030304210b60680701c0c041d121b03110401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 18141868 1250 18140618 18140621
    0xc020615030706081b0903070914010e010303080412140d020301090b030c0a0303080c09211006080c040207061104080a030207050919050403090503030406030b0103140f0402010c06090b0c0901020d0201 88
    0x86590f00c0c0c0312007080c1d58550500c2c05140b90340300e90003200d000d41004640c420b40e03010301069018200a00000412188400340640e8801c0142c108513460f02441005102190f086014268032075800455071400182085045030105014010a020b00c14041405500b144541e000b0314140e4158000404c0701c1224241010350f594a1440d40304d40020420200384042441404a42d50000c112490b0742d1801c064100440c031429020549540e5002842d0324039401000c00b4084102402452102800141e0400016a840300e41d086074075440703240d0014110003009107581000b00c2c3c6103030104100e502c0360f68401289850700d00d117480480041c00780c000d0126003840c02209807805000c0700100c02c40003030200d91040008090180c03081d01409803140300041d40d80d400f000100050021503502003000502c26002400f035074004940504101083e008100c0d240b640c0686843d485602407901f4580f41800c0d0a003100100110034024041412503010403420122110081c60303042400c0c0d00301c94203480904022030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 18143118 1250 18141868 18141883
    0x61b12070b06090a06080a060504050d03050114010516020d0c05031207050a0b0402030a020909031b1207120c05010507020a110103020a020a0b0601090801020d0b01020106060c0b0a050c040305010c02061503 90
    0x902801180740410028103102069039440484000300244680d11409801e20742512a44200c9510b9101c000308020400305022006985070141814440c5504202000003060ba000381100e040120106004051030441444081025009030030010b04c4203071400d00405c2103282c0e01501d4028814640c0036000100070344110707209181c0000c0074147d241101ea0f9150340014014005aa05100e0380c5025005a52003031007850007009210010350b0703602107424000c280001d4040380e01c1c0e200e0f0072228000483d2902002280e00640d800310f490000d1842600081d00d0a00c50703400d0207000396180608200d1700603000030301c10b0b560764051a050810400c2c0080110f081e40304241c0d1031001a000666004000360400d0001070304014141401c982654031900a5030880c1c00c00c0080c00324207600c0340c1c0c0030409940c0a204541c00380056141441a9007561b4542510424000e002c40c40d0702950f81000544070796002d419180a0740d407210080c0051030540d0b8009617910029a0310355151100c4201c920074030f107400034031780 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 18144368 1250 18143118 18143123
    0x2010c14030412121404020f01020a080409150f08070905060901140409060e240c03100e0702010b0d08070201110102130308070804032102060906060904080c0705061b1207 75
    0xc1d00d140e8455940070030360f0400030344000c18440702e850b020310340030014002c20702e0101014000074000d1402d07004001d484115480e500e4155003185000340c0c041000c0c2d004440584404080c003080070a0b07508400300c2c21203401d40c48000c0c3e40c01c40709000314041d080031401c44110b802d804818030603502e0728802c100c0351507801c1c40303a0313901148070189031545410150403005407903000f50030005d80488411070140c1880c140c4110354003140d0a041001d4514080c1c0111a42c11410000032207055241c0203280f46900e000b180150400321038144005070b2000d00c00d400c4540d90110181040307401c4641b07032074401711075040110109d020440e0030350801415801403091b101060b5030700311203501d07082c1b0f1a10340700e000c6da104410607200070104000202c003113860540b0250112022030b0a0242001c41400001d080c550090a602804e03000a011f0060f69950511882d0b0005d40051042c0c0c2d85034040000785240403203a61280340c21410122300c22208002d40708080800004400903112880058406013103503100b03070f4400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 18145618 1250 18144368 18144407
    0x21807030f0c36140405181e0703080403080405010e0d0213090303020408030408030703020f010b03060103020f180702010608010e010509071205030d290f010807030c0314010801090302010c 83
    0x141c054103903501c2d048210342d0f0419100c030b541074040940c3c00440180590440211840c07407840351149810144951644002ea95200103032880740040707625241c01c61038191aa5158500e121180469010700021000310f9011078041c1c0c0d43c9545e8a03000020350003511500c0d005c5030106407908401d05140c00c40c0290154000c1510044010400f0490010120401305404050f828000030501440400007000600075030002907442c2d08141c60000d1508041240f52407069052002200c2c164600040c400d040da0b504840c0e14207500d0403800421100601210901c0c08444054148580650194050710940e05204000d01050029000c900c0c26a0380139502900d0307a0b440310f1003c01c2402d0262030101e44192160054034a0448061407400940316044950314402d25000c0c8200c0c51245040fa129982003010b981000641041c00000f07818404014250418103844070380740040c043c442da0040081200500655042c0d503110180c081c024580000201c02540c640070703c5600e10b40c000e44c101032601c0e50b036558 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 18146868 1250 18145618 18145637
    0x210050307210908041205010c1107050f120105040b010e0105011805040906020405030d020c0406090501050f120f0d170f0610050a03090b01060503040b071103070b13021807030f0c 79
    0x501d428059402d4810064080da5840035600150407840104001c140c3c03080b480500b0445410003608481c0d40c0c040050038812004051003420901107040d80c00c2f44c1040341c5411400a442001c5201582d0b0440002d480d54030f40820042001440c2c070310581a5003405100c020766a0f01c40005440c883e41200c021a07028800c2c0104101c14034043c2c01000c0c2c0588244009400c02e5038903004240360800c0c090000000d030f08120f00c40483d03800c144c42510001c0c09011003d020651500001c9650024401c203502e0042000c014100d4a0f00702c10030005407402080c00882d4010070204100524017203140a410100400c49404200c00d800c81c0d2402031b0050038018a40c518505400304140e031541d04c80c610302c0c018940c403400e12a01103200503440a0090030305889d400e40d03e02d802c2c07a08003484c8000808030001c1c4142500c2504095100001b40c0b001c0a40c4014081556101c00c4041e5001c40b603101c50081d888610080321f00030100d11403260783d02541450b101808014070103801641501c00c40304801000418404 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 18148118 1250 18146868 18146897
    0x120209030a0b040f02100f03050703020a050403030c030e0303030123060403110622090506030c0a0e0a0209061209010e0f07050d0303020d0f0c0201020a0906090f121a040605040210050307 82
    0x2411181c210307104e04040320703650306642d020980140607810b045000c90282c00c030040016070036020f550380c40100d500d400c514007860080007030154021030002900f084414214901010300031040e04140d080b0040c102c0341c803136a4546a03143c0e0042040c248010b40c503451142100141864416601507030343c8440d951183c1c010940620219070000085003000100b095a001110350304510f665024101c010800725091070170405142c138040d044171308039002d40e02c40c1c0410461200300354411500300c401c080d00941d58082d050001000b50203100c4204035210342d41c406202d079040c4150711000d240c0e0003840c00d9039048464464540d484070014031030250403007440182e400c0001d00c00d41c02402c008805400014441f1005000241111444003000f0090707980003c50141241c0c1084156004200510f007286500782400b403076806040300e80c8900209802906001c4081011512004c0d0304090b140ca603074019843c2c0781c1072140162006842c2680200f00c60140719000c0c4d84101c08030380c13042c1c00684035016480b00c03c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 18149368 1250 18148118 18148133
    0x20f030c071b0305070f050d030f031a030114040c080316080306130e06040213060602070b0a02030f0d0203010f060e090612010605030f060a0510030f03030b010210050115120209030a 80
    0x18044402e49500031800390000406030b00080a540544000c251503400c090400000942640109208015010241d070010394400706030080b0340e486190100d00103408040c400203040c040250264194201a514502510a100d60522070b9011b454202c1e00c1d281e41d809080d0b11780c4615112200e45008001c01000491030120003142c000401078807962f05c0140703500034101151800544040b003904440107020562426000d00c121104005504201d440d14101c000303559441180310350b6010303403004030740900d910340240b05949010f005118690798030070702c1d805414020340c001d01407000603810318403001c81c0561041c002d4852070701c406044101642c40745020440312040010205080b50f48811740441e0b19207013401400c1c03a0b0906100200001c0c28180f0910301900c1c801400328600c907041d03c0d410004518051510040582c250400040301070b1601d0040782440b1480c02044013403030500000180078100c10401e015950020340ea07086030a114600500164812071143c0c5925601c20000c0f1000708403003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 18150618 1250 18149368 18149377
    0x30f030403091a030414160515040306050112120302040b030c03060a08011a030c100207030212010e06040c090507030504030801140109080f01020318060f010e13060f050a060504020f030c 82
    0x79041421603966214070030002d842c0d0b140312481c55180048240310410812003001420200d040016103075104000040280c0203440d44586442001f0002201180d5a08041164055900300c081442030703603120359103281c00b8440484100c420621058500040a00c01e1003034400b528440e01d00e00e451901c410864004a800190420b0750140500c64005a40e0307000344034031040c120140e000700d940e12050310b007003504042640d180540245c80711400300703900940c0860828103581c0c0c11103d2012515203819031030300410207040c0d4580c43c1d1013164144810b001803480f01c2411907688410600444e0744610b4100d09958007a0340c01030104040d04010f1208a041c984550043c0300185040070310255241004d80c64401101a000f480380d600006002c08403039190198030b8164180d0005142500742240382410021051044002c2403e2010205d83c2c3d0901000c991b0001d103400500c04c1c401c1c1c6140d01446001000c0a43d07203160028504400000d850a05009903192001d45180072404c59940001004c00e5030300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 18151868 1250 18150618 18150623
    0x30608070609080616020c19060306050603010e040602030405070e0702060105151207030b0d0605100e0610050d09020f0607060e0f0d020a0b0405120c010e070911071101050409021809061002030f0304 87
    0xa0320302d800a00e62181412521703d0f01000019234a941c0c03600c84050111100c540006008030030070801031002c6480d040359590481c1e4408801a0703290707982d0401500700703407094001d01c820800140c14040010307070000d10380303041e610704689148000b0384c820104400c030710495406003408103c040c0004d0010f40070b0340c820104c01700d0252580d2951900c0395500340c1110b0003220180001003915605000c4040c003100441e6000300f040c0e8072540240203a00d0050818003501010641c42521041c1c0c0808540700e1008840c0703807a801400ea0f80d10381e8a0361a141d80581130043c0918800d01c44c00642541c124000103403c141c03070034290040e2a10391010f03101c12904440051098581c0e2180280d402169061100100041c00c6030100005030003010101050511800d5070051003420b041c218280061120b19088030111980700000d2845400306a00594450140d58800281d403032000c500703214410245162100343ca0740498060200781d03103070000c101c400c241607484100161710074058101d030215820010340c0c0250 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 18153118 1250 18151868 18151873
    0xc0d03020f030d0906230f040809040e010b0316060e040e011d0a05070603090305031303020f060c0a2703030f0302070203070b04030506060109030b0a110d02030703060807060908061602 81
    0x599480032078034540c09070840c51002595004c1010074440e1900c60560346200200d02054981c807a5a19100b00c03c001411301400d607c138281c04034042002a0080300c1701c40a0107031040c01104030b944580f900800b0300b900301501900400000e44c14404040800c10141d54968581001079a030480c240f0009040103a00640b556585010750508d400c40810703049e44400c8004000c11151006241007800d11411b40d100d04241800d000c413410000e600002641c0d4401c000c596039140043c0d50382400ca1810780807240a48450190b0410710003041620001440d0a00940d00c42c100351800d015100b44440818916034858a0300603082130002a2213901500c1451030b0b00d00e17000d0f06100442c5c00003814400c15900ca554481c2e4001030420400405000860780007000f428407800e4107180d9114101d5445c0010a84000160340e5504450500200d10a44244040c101e400315200d250408006c0c00038001406136008521511000058031807180d0b0510055404c007002030081c41d00c03444481c4108145140b40b090950 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 18154368 1250 18153118 18153133
    0x30b0106031d0a050303071e0206060d0302210903011103010812090a0b040b03220201090b032806050a05330c0a0b011802131e03080304030807031d0c0d0302 69
    0x803400f04100024540038002441d90703418100300140403ca03104054449814540b0b441c006a6078000c03c0c0c46500840542d0b2001321103001d8038007282001c100d00010b0980c40903002040c039410b84c3c1c80c40507040240d0254000c0004c040340d500c400c2e01500007440b480b032855004411140e080300c440c40140481c0310700941000c0480340ca4145c0070710280c0040c0c2102e5010540401001610715190400800d000807612140d1150b03440350300000c0c00c510240c000e4524800000001c100c00c06180e08400002c445030010f030002604e8090724000142c080c62259510544078141d000c0742514124088c11a2035034203503481c18103403d801c8003844510300700300b4402e14010405d00000310741c44410301c1040d100c1d5229040c4401958100800e8624020b0000f5680020a2042c00401c1c9080301c440d0802d000d8400d01c0111410710b0307040102c60f215000d0303a600008c04800000c0248000c040d005055a0b000746d4068070248070454841c00c004081c42c02c800c404113883d6000412040c07141c1030800103415164000c0c0b041d204003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 18155618 1250 18154368 18154421
    0x31908071a040204050109061206050405030c0304080f01050f190f0b180703110f070803090c0a030308040b0615040501050901120c090e0f09150903130303050406030b0307030b010603 80
    0x5155401608076848042001040114949442100e003d4540c0800400155040210303070900b075003221a0080c5507075600c10100302440010010344d8109102e5030102d035915900c1e150301545a5800041e221200d600740004101d924804918680c400e11050000300c00d5400101c650700301401d4480741c0d0855542d41c6081d0b1007216201c02d110404502c43c2c0142c01111405d08200c000d00329200302501a019690a001031640031480c10100d40c00da03a0020701850b225200c56410364144102d000e2150760201749101c002082542086005122341e00403660501d00e640c40d079060043c23100300d05d2030040c2e54500401c010720043d80110702030088031f141807500302040130b280403600d01280d0103560280042541840c00300500c8841d80c06c010b5200c61a80c0d100c82c214241207000f1640c86041043e05014007a203040061040c0c10200103862401c050500700c13586403940c0c1c0c10040c02d160300034003034200003d04120512070300b401c002030404d08403036205403680c10350380c6842c404070000e1072419403400040c0600c841c602d24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 18156868 1250 18155618 18155633
    0x6010c061b03020301080d0e010203090f040e06010806090708030405150304150e0309040b010309082b0c08010609120201020d0806060c0a05100c02060106020c010c0f1e0309060302040503190807 85
    0x2500703805902e0040c1c2c1c950402112a00e0280f00151001c02c0000711000b100c05030f6800f0081e604000819500b18400410100c0094041c084168032070000c0d2142c02c00025141000240c1c842c022481030f415560300c1c41e1141d441030303100d100328006c1d150802110407010b80c40004000080d0383c0980582d00c1110070b800080c00e410180d5101c1040f12070b5a40c0081100d10f107905e02441402d10510307090804014180941d03a5411080c014100040c030034404400505001030780d40c40b42d00129440344a010080381d04060400f034030a400a0140000040e0003c40211798442040142c4403e1034058004020b0700f031160404441d0461b004182c00d802080601040450039010003524000c14450b90150982e001c0c076002400031501055504411540103000420100340c02180010300d201081c070700308910036003900b80b1480044d0f15603001031032035410307205c800603500390781b94401c404510a5a4210902d551028110241d02a5010301035064000c255400712000315080312420092040041070704005454030f5240 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 18158118 1250 18156868 18156911
    0x328020c0105031b0c07230906040f0603081201030302070b0301031a061c030e100905100c020d08030114090a1506030b120604050a150c0503010506070c0509010b090406090c050306010c06 82
    0x1c4561b10044040c0500c80300000511440d001c2c0f200c001c180307034483d01c0000e440c182010b41094000c0d1b80c2e40420420203000c40c0c002d0070203550881c1e45140d851850520401d0450300c00d22055006000d20341d0040b481d02c0f4114100c0f812a40c0154040e01f406c8840459181407540240410340e2110700c5031683d201050680710035808660081d240d09050001400c140031046c0ea040d00c0000811000c0401072210b5135514825a10707101003403038030076180c0010384040b60001d024454003070002000440001081c5400810742c002204095821040907116500f000003641c001d10401c40c02a0328803030060081902c00d034842142c542d0020038840482601d62800f40c1090700c1500d00340c0305038019150040600c6030184280040c03030801001049001c1c1c0303000e0024003900040c01040e1080d20006108001c0c040002120b2000e040c1c010004900341d46c0d034041c0c0303044607030003c2c076010302440c1000320000f1141441e108500740344185403145031640e40d41900460714a440031004a03103060380c840222001b0120a803006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 18159368 1250 18158118 18158137
    0x50306010b070b09010501080d0c03020102070b0c07020420040515040b0c010b03060907060f03320601020d02010b0a0302061605070609060e030d020a03120204050301020c0328020c0105031b 83
    0x82e540b038040d400c19004a420060803084561b043c400108054840018001012006883e241c0c1208240b440c08030701922170841c000c7c20640c5003605108040f000c45004040c041c0c8200c9041280007500c20510803080e0110301501100c8000f0301c800c1080d804c0803c40348800c0a40e450a69140c191502da201515070400c2281d020103079940d6406605034102041010f4020136101c00820034245495001444023598180d154105900c5507242a0100c0012442002c0f8084642400300e41d9400300703010044010040b59154014407485180d0503500740107210700c203440c01015002840c0380741150240502036214403035000c0f8981008030300c6000301c3d1050148002808080c0e031040b038843d140220050aa02108200d00c0c0300e500240000d1403e81d400281154155516081021424200d5103854000303004580c400d913015400003400454800e07001c4008e0910700ba0700603921444900600000555080f240100760160784540d410840b40d40c041c4025543c060740b10740001700d10180b0a02c04200701d0f003141000c1e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 18160618 1250 18159368 18159389
    0x705060f030f060d080307030c0306031202010510060504050d080901200a0c0501110c040b060d02070c0f080109031b0609120206070801060806030307060e01060b1201140306040f02040f0605030601 86
    0x140050000d150440e00d42103c0103e8402c52600b4044e00c0d1440144005066041030690321420900c0313160081c0c0000c0300640c0c020522a020103000744029020301000c581710312204219500200b012070042055809695010342408001c01d069a5140f0035540241041070511001500c0100d03170392000d940c007070800741010f405422505035500d8100315410f032035000329060026051501c4906c5000050b41c0308082c408641c0440d07011840310104100d44110009e15003038500010709c8a05100703400b2807510894012440c40050680d9482c082401c84259030300081c0050324590041c001054401249400c1c14046d0100140c400320030798901031300e0300d83c1e07400f842d01580000080013011600124080e0060900d401c01e20f04a14140c80000d44038424440c00800039503648030141984131003540f0403400390040d0074506560704420121b02c40c55560034410418018014445000b4506010400e82d004981c012464121034285508203c0540106c40ca981030b81a40c1f203c001541d40d030200302481c001e20704500c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 18161868 1250 18160618 18160621
    0x606030c07060b0402161a060f010806041e020c0c01080a1404120509041505041503030207060f09182004030305070f02040b10080601020c030a05071512111201060305040209010510020705060f03 85
    0x700708071f201100800142c802d8201c01c0b40c80403140d8101c09070035807001d0304480025a10083c6050508600601610b40050754404902017200c1000002c00f4000c441d0b090304c3d4080300b540c2d481120380958814040e04054048141c2c04070700094400b10181000600e14103000e4100071000011400701d4804255071900c2d007812010400c10703401c00d4800c07141040300c030f154598502402d40c0c90181d90b0700d0b454891041003020080302c414a95104400100c041c08410101000e0300d01070194500203401c0c0d4555885040089103003100a50180100f107508481d856101c2604021154071803021514203090281d80280d21802c0701045a03540d0341038142124181d03202c41c9010304080000a01d4503445101c1507010703a0040c08908041780380040c9420498206030541945401121011501c8444001e03030300c00c606040c40c21054066003060094010302d810400300180300da0740d0320070440688d1015030300a9000011600144910700303040140c10104495401210b01265841d800300d44554020784010000b0103000c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 18163118 1250 18161868 18161903
    0x1206050a05010e090c12010b0418050606030a0c15030b04090b01060e03030f18010c0506040c03061112041b0f060e0301060515160611030712050606030c07060b040216 73
    0x4200d07070143c0010740701c650305880c0c0300c000c02d9a106480c00c422840f807190202141d021079025008695001c20141042c0580a40b44100c501011032803a8103c5280c0a030390005120380c20000b60720050590014001000c00d8070b00199120032036000c4440c40c04150f00d070302c41d4590315102ca00510202e140f1400c0c1c921031b19072402400508410841e06e13164400e400401c00d003014041441d00342c6018400405540e40103001b0100140c690760204200101240121804c0105129140b4003000440b80244400d00c054018442c01c85080e01c1404ca204142c080c00c0404540030403141e0490f0448990200440ba013600c1d15415611510b26896200000044102c00c10250700d080a000b14402014203607400c0a41c8540703840e120350680241c01c034a1105941802040c002d00c112500a070f405102180f10155a078180480f0045c4142c81c0c1034014042e01d414200854500c0c1040b60031a4402c00d001e4150360f00700681ca5640601818040390415441a0244891040300110400c11241d25206050f0070880c1008070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 18164368 1250 18163118 18163121
    0x90b18060a030b090d0909061d0a02040e18060601030501050904140a06050c040915030308040201110a06020708030711060105030705040f0209090112020a060c0c050913051506041a030d14041206050a 87
    0x41c2c00001032a0b00b804d10030000510300141e640310489244c9d58100065446100c00c00090003a030f4000596490311000b03214013800f04404100c1c4000450059942d655030f80e20040d820348000f07224050300b0005848c0060045004a2250380c0c95034100c500380c411040b0301d42c9946c010f5480640384010100000039003045080c07510311482d111101c201d41d00b008180d1443c3c0b00940801001030002c1d050108032242d80070b4105040c0301291110340e021500315220b42045c10801d100741c100f03e070f0b1800800e0110169200340c1d1302c0000c1c0c1030f040342da00400421a01d4186014000503091000c00403400d03c0c0c081c07040c00665912119020300bc6e00784840c4d401c1018025004010708006541d215209111403505400301140e0003040072802d6410a85100c50545c507218603403601c1c00000040685203000300035141c1c8a0849040255000d600c049130180041d03100c0c0c1e0348100b86215a60700c020342c15445a00b05040c1035001d071554043c04040d0800150505a842c5103d5002c4085004100c0c0d00540d44d104100010b20a1b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 18165474 1106 18164368 18164387
    0x1704151e0c0903020414160e031501080a02010822020618030d0806040501090c0203091e0d050106030302010c08040f020f1302040807030507090b18060a030b090d 71
    0x10440000d10507a0603003c1280b24600342000200c4005440b807903203010b1856901810131500a6070740544c0c1500c1e1006200d500343c06040c19000c94880302d42c20050081c4904405040c42e903c6034400180000c00c014100301e50015405035950780e002441112180c400e0341520195580c404e840003401c1440c0c81e000c02d00b541841031a14050030150b005003494040c1d40261418000c0d030342c8800e41c00741034403030f03403203807140181d0003070150110074903201c50001c04248a0000020b80f03881c040c00420162441c1c0c2c5825a500d81d1243c50400400d0341c24420071101046c81d2524029a080c20380d03034008503001e4840040d105540c0c80265540d01d559007005582e03000c0c848102150b0300c0395030340b00c1c03903031038902170300c400e40ea03600543c1000260b4911078040c0e000720000050044d00b101c020120100080c40c4094000c9800000300240800040c440e4000b45000f07400d800001e200a05160000034a500360 = true := by decide +kernel

theorem cover : BRFrame.Cov 17985618 18165474 := by
  have h0 := BRFrame.cov_init 17985618
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 17985618 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 17985618 ≤ n) (h2 : n < 18165474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
