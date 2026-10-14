-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1483
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:11:41.361272+00:00
-- url     : https://prove2.me/submissions/d00b17b0-757c-4686-ad84-1de9d824855a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 266546762 ≤ n < 266726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 266548012 1250 266546762 266546767
    0x30c051b0303070212070305030703090c03050a030207030210031418071509050103140105100c1704060c1101020d1220040b120109181103030c0d0801090b060a090308031b 75
    0x40c2103400300c0210310407101070b0300f03131221501d00c0380d1951810b00400303a020380061414400250110300a40c0a15280c80c040e8042c5050300d40c0e83d80e0b1f0304d8600090750f4021001600296010411401c00307101826140d0400d040c18441c08134408a02000200c0081c8940940d6000c0b0860700641041409800041d003180c80540e184526602405010055588101d40c0001c1c5001d01503800901800c020302c0c1a550300600d256829613000c4011980e07100320b044140c0c0c4802007515030b02800c241c59402800246120784031000100c445007042c0c0c044500b07128901e810b641061003076000941c0d00c9054000d000800100005010075989240b1200150f1008554400d4000140200e02c140c0010017802590704d1086065490740e880d803891806642c07018221911401a004d00113001a2070500402d988031001b0701100e0802030380b0ba201c3c51414492115800110300503000500072054503000314609804155090383c500100381c000148074044a2001414070300011003c10f02441c6034020481c02404408023154 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 266549262 1250 266548012 266548057
    0xe120303011e05030a0b24030607030605010801090204030c0e07020a06050c04030b090111030c0c0102090a030f0b090a030507081b0d050d0b091603021e04090507030e06090a03030c05 80
    0x40402020281501d03000c1c0b111500080c10780390000b5080000c0b5071051400507107480f0f500b44090104c07280305611046445404045459840400036184200d5140d82e002c15820328000c000f42211506800c01818140100310038004500b540c00004102c81001040c8209682d6100040341400b8200600900660416060040004104001d0b0047d02c1c000d8801805548444039070500f04e034001c244a1203a4602840024141029a030150003821040400503260400b0391001910166179a08116500d5031045514024000140f0301d45a01405080040030480c04071340380a807240c042d018006280840001d0540026072b00c0d032011181101c0c03403500700c0b1000a5124030181c8150050b6909040207850b00b10348401b58030300700405501400030078200c400c60b408081070443c0a5800002201c0400c09106000104490504010b0009201c07c19000034181400c61006081e601d00c582458200e80c044024812610320115541c094503505041c0014440240c1109482a00800c08a078021303202c05803205 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 266550512 1250 266549262 266549279
    0x6080c0906011e08060607060609061e0609050d231f110306060a0e1f0e0915040e01060b070b040203070e090307030e030a02060408030d05010f150e12030301 69
    0x41414000484419103240d40708401140c414141400ca015903420b00c000048501d4018448a41c001d01c0150106103040c0c0207450742c40c107a8100398022009140d80d028108510b001d041003144156188590b0a04420302d4107100078150a5a070244510440c004503022040120ba0031014442c03034030700707990440e2002a1340c070b042d0384036400200e011481c2e2601005044078103081b031060789000550094028215100c66050207016000800807000740154046000015621082c1c1c20000403287c08043c01c00c1c03e0b40c08001400152507000c014000d01800e024001c2c012803255840300c0100d02543c3c001004940a00a540900200d5000881d42e0000082540c00d118441c0d202034481c2e4001e4044a81040d078030400303c0420303103086810b10f4982d0030034004000020b200b041801500e020050489500c1038036500050920b80c019030080040b9803000070140d001a980d030241a00605403190301140283c81c11004055201600c5012010881e01d554a8285559501d01000101c100c0f5030031251070b5030310744103803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 266551762 1250 266550512 266550523
    0x10b0913060e0c011704060f05090703060f020306091603060f0f0311060a0e0d0507050a2c1603020913150e090f0304090509100c18081506060a120608 66
    0x369140790500d204840b02910000d0301240c0d841040e074842c4030240e11100403920580c4080d104844407920341750300d4030004c00c050140f54041d55001010b08616899440d00d4404c0b20040340b5403034603050052003040700544d40d130701c403171071780040004950744c0c200c85101d400f20000c00c842d40084692400081c0b020a03410302d0f071040107060381c0c4100b10340500c40c610401000b045001d20700200b800205141042c1400d8104040c680d40c48600c2542180c038002c0e100c80c00035620b820907420542108035881c81244110061011000c81c452035410362040d50b05042c848100124054405e01c0141600020200c0140e00d0b803191700e0303100940c401e03810058030030100000140500c45101c0d4504a00709031010502c3c3c0c1001081c02d049420703803800103614103890520f40d240500f10043c04001c003070161900390400d82005006004c43c0144940d00c290181c2c0004c04a0401503007960001d50042d07000b015640043d4800d1001d903500420221101030303c031010200100c1c0c1640030703040340c945d94500f4041d00040020b00080c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 266553012 1250 266551762 266551801
    0x70f050f01060f0b0301030c0b0714010f020d050105010f081803040b0f12011e030b061305090a1b1a030903090a0807050102010b090f0a05060402191d01020a05030a030b03010b09 78
    0x404070341d00340da6141302a40e0307010030b002c003900b880340640d0100105101c01d001802c03602c1c03060b52040c01c42c071103510282c0d0864034420020020a80c0000b5200c101445078412680504002d08150301008400c0344010561440200b00007d44016218100702d00c80e0200240c0d0002d20300c0f03003800daa80e011100d0480030640c2251010320b07549644000003060880c854101000c00005240301a2129461919034002506015240d41c1d0424001c00010052100303c3c0610307481000d04030000d142c1d000c02c3d40b07803200403241005030100c40702139488024400000401d25104100248a455581b6a11440007142c21441111565a408640048001148200442c28000321b4409030003c02080041805100c24402c044540300da01c1a010400641010000d52009070803a0014000608100072170140e0007490f258500b501000c21854441c4820750041d080340e04403126400e102911a401407556544d035240110b50b4103a0074952104610302294809504c20101840002e000d0595418001c1d50355410340380025 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 266554262 1250 266553012 266553029
    0x40e0a111306061202130b070822080d030e070e07110706080705070845030325140a030906020c0a050a050d060902060705031c1a06070f050f0106 64
    0x81100c045240d114880c116442500c1e501012840d000084c0d00070340c00503080c801c00e0071031003a000c60702c0095000900460b610a41c1c610f60780b10400141c01188200049952110340c0c0016003d001402d80415400c840040034203012071081004030b845410080030b0340051241c440d80310b04000040c0c1d072100000410740884015960701c1d5490307200885011008071201408039100b0040100043d9000c00104290694030581d04d085002d804440300456581710420005164000e0b92440c4e0001a146000c681c0781040f001180703403003e070060800c01b8400f121403410000aa00c0300e0f00b01807109454010039110300c510251407003004189809441c100c568010300d030051003001800080c0d0305011000d9420f649008102c18070541c5040c00f0007103540e10315201107501c41e4991040c040140c6611019005051040d00919210001c006d020a2114500740300800c255060200303081c1c1000c41d400d1461400c0e80305a07030a940e00e8580b410841c08074043c440c001403d0740304140d00704890303800c194010b805407401c00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 266555512 1250 266554262 266554279
    0x90303150e01050f150c0729070b06090603030c01020f030106080115120b01030b04091412070b010e060607050f06090609030a08010b2208010501030b06040207031706040e0a11 77
    0x1a001d0800001c024001c0d150041d1842040007202c2c9084203c10028698080c0301a142840741490103007058000da10014041d81410724200c0b002c4503425100d10000003143c1d4050409036142c807428011717000644621302400c942030100d01d49481c248201d54821441c1c10003990746185130780884009034403d101c0c22001840745000458044880300b0300120b8207401d0382c0c07064074000424821030010f018481d219410301d561038000070700e40c1d01c40d4090000001d0091003c0c000990098100d0740c2040070529021308041400c016400004042d543d00b1810364030762040940b200e580e810042146d91180407005000c0e0301c5903407400321a5030000140140b05404040603502944c4450000d16079038028145c50340c2c0411101d10050000202600291610412001101201c1440300492a842c003145801c0005582d44610060042c0300070a00410f400070020b95085150589c140c500130803801101d5038100501c1083c4c400309100340e031141c100044042e00041a105c100099140980860200a00c124001c4980 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 266556762 1250 266555512 266555519
    0x3010e04120804030804030315361811030703020a090e10051611030706090c1e1805041a01060903050c060a170408130f0501021b03030409020904060909030315 70
    0x2820618002c0350725840e17400c06034941307a400b40c01424214018060303a03400e42000080a021040134442c00382144000e4100c81e5071141c140400842c3c01001e5086400d0400d01911514400c1103c484d0078141c100009103a02c80a4000003400c0c41141da0020703501c544950300c04195080154420801e01c3c1400044a12440c081813003d0280c44089403c114600191034410326810300880068100c061208152032800030f0741e9650750202c9503074007400e460891150324180905047d10b000c030720408090942d044801442d04000c0e03040d8030014030780e50003c15104c10101c0c2c1001880003802036031029904591040c2d40c1c650000801d1042207100658003842035a680c0382d05420688110344510055982d1028001601c803040107403464090300c11180c0d000c040010f000c0d01e0843c0d20105020307250311521140a00d1900000924040301d07094a68001803c4102c40c2c90306990000403501140c80301e50f80561070703403043d00c00a0002d090507031045040a0030068201c003055459070001030700a1006007000c034095213 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 266558012 1250 266556762 266556767
    0x171e1c0c080a02090a0e07020a1a0103150f0b0a140f01081603020903030f03010306060608090d0906080601020a060603050c0a0b0a050d2c0703060608030f0306041a030303010e0412 79
    0x206280380c000481c403010702044080c010340e0003c00010402a0075848403d035a00c042d09070341c90b0304032030a0006803c50003504040000c00c140108060038990701d045415415500c1e08002400f81c80001c2403041d90b100404e0040190300d4004407503e0000030200c1440d030b1358411a01d00e60038440c060051141021074a080d21030760190b4480f80c086c1ca8140071200b0350b80010042035000b90303c01082554503100a03c0044d0a680c0c044004501851041c02d021440c5441c00c50058480b810107002503080b500110318100310720350b001c103419007102c10618062040341c950000503800c180c40f039000988010b0410b200402030050025080800003020303260705100560b039078440744460003941502c00000340c007040300201041e0260000d04170003a01e41d40105100141d110340b11485030f00310765007914a800200c4200700348800d07441504010b2040c400958a01101c034105080326200c02454244910ba5840c08a100102054440d60f070400002c0d00320f07030780c9584458000b4803580040383d080f2080d14003400394102151 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 266559262 1250 266558012 266558021
    0x309080a051b031209060906161a010b0304030c0303090c090213080717060115120c0e01030f05151210020f1902010c0903020405041b1202120613171e1c 67
    0x1d410b031130340f0703403c1c80a400c0412815030b10900d06660301107024801051424400011407080a00c6a0850403840c407c401d8040d105c288142e03c0b140007841d041c010440402d800040d69040c0951500d400103054a092030303c088a041c003904a5005144085403120450010f002c0750425520b80000312403145540e0300f0400030300c10403c41a04c8164104e10010040026a00444500001c0e01d04100008500c8031000707a0888000040500008004500c0c0601b50350f00340c0710700440806000f40901262810420f02c0c0046c1070b5151030301e8082c032060000d6210303010051150901c0c82000382019903946960251000d000e4010710f5000418600300c480c1000319900500c110310044045464251034640f8503000c11000b080c0040085e0b030401100c400800d243e00e403541900c0040c00d850007030807035200c480740140006e043c110702d0b0102d003542c40a02400340b10021401e020980c0c030f0f8451040e03a212020b21605202c0b90080394403460304007044846810225801802070001c06090011134032090041d001c0b08010746 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 266560512 1250 266559262 266559283
    0x807320c090403050406080c0f070b0121110f1c05010615170601110c03060f180712020d0203071a071205090d020105130810020705010c21090309080a051b03 69
    0x160301017200b00200c0b801440500d41c444a1310f14058108943c5180b91800d913400b04108985150050700140700d105034200c10052001084100b00b410040e6170f41d9003881c1c0200c5d80e40319a00c0f401210b00c850005580388030040f480907402042010001610340b806034083c001c2c034001c0088040c2000c0c0381d000c406120b040a0304203509900c0101c00e43d5202c2200644218021500309102c41c010181c091290362010401e960103420301d0740b03c0002a1a1800d13030a1181c00b00a40007100d01c5d0040c110030805e115400c0415100a6011155044140d000d031000a241140580c403800f5040303007078803031148100c0c00640074200b1140103141e0500c40241c40f070303400c03226845103624442e88104003005180c050352085018003046d1000d03001c20300c0020384689481d407401464205c100d00194002842030708106003030080c03250203241401c0c151541d100c024500c1c041c035080041c1c0500b5440d60340c51010309151003200100d0080041c803007900e9403401c960402c69200c980505041d210106011205011800e000070700c2042c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 266561762 1250 266560512 266560517
    0xf1403030c07031809050f010501081302010c060b040905061302030d09032102030d0609020d0c0906020a03080a0b060c010e01051005060417010605030d11070f0e040807320c090403 79
    0x10032210390f0f0159103c600340d0320b03c00712000d41d1080c086030100c0203109030350250a245800342060740c900000100311080c01000907160103410011100140d801c200300c103610039400240440c159200c1c00c0460001d01000801800301c0c452101403200103080c00c400005218001d40a40f003482c42002000d0721410641e00c4020030702710303404844490f60103000400542240c3c0d5441540d181280381c4a05100b62040e5803c6030390360391384c00a44050a40028410340d01410100d080902042d03261a4000e900d4100d00c1001500b0302c00c55100050441c05180d0203040c075844d0080036aa02c0720716821030507000701500110404150b2a1038081070030008003140002c100c410041080b4a07080c01c0c44401070303120410b1350902c0319a640f100030201d07540d68240005000600a5603c4204c883c200121041c9000e4441c0d1191140c00717080700090004070a444000c5504c5504030400079940c01030303898402d00c0c4112283c070049450301c2c0c13000a60b8040052071480a6180e19120854407141e65007000c100c2c000701d055500501 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 266563012 1250 266561762 266561767
    0x10b0103150b0c0c03070f0f1205031e0c010f020306040e06041101030903180308030f0f0f07030b120105151203311701020d06060f0905060913090f1403030c 69
    0x541c07005000074070700c585528050740c104c1c500c001c000c20b00d000440d0b0070601072240e8a08041c0040031040592000601501640d01c41c040400c2d2185a00c074450fa40e00c80d5007444122070440003d20140b4101c44000000c84d008100c02094280d5000c001d4009444052203541408803002c01c0e042e0000e00ea601803a00030034100c1112031b2900040d0001e02859174110180300e820101541401658203038140114091080242e60780342405808030110b000030402c000b070041035403c0c03040402c003a000c40e40e4011003500300021f66088420014a0752200c3c2e400307180c503642c02e080410108007100700194080c03000c1503070340480c1040302007041390b01d03405164407000b268441141c075220106918805c540940d00751000d4524910b440751801c070484103542603044c0450f900040c401800440c10721a150042010b4038004d100c2298400c030007400300070700e0302c1420700c10100412940d68560b03440c850034080c4031300400104100003680c0b5080392090420901a12606911200d1044102d00401180d1040d84901151803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 266564262 1250 266563012 266563019
    0x11070305060f150109050906120312010617070e0913140a1202070608220203060c1908061c0c0902130905010909150507020106030f0f0203061503100506150f0408010b010315 76
    0x1004650081c9420b070f203d010002156120f2707a090005040140c1c5410b990314075903040c000050040d4001402c4025070b40e941504004c400c6a0042210031155421148844d05840d204001a00c0301e003038031f1010308044030407103013030004100001d20b04030000c1c0b040740000c485440600050342c80d40c02601c40c000c0401e004000181004031081151036a80c0a8080100340304240c0f9000b080c5041c2080700c50288034140041c90f6410344400e03001d2000d038030105d0b00e8803910500e420004200e030350b250a01c154002c40d0100041d84100314140c00e01304043d1103021021074860f003140e100d122110006120304000e1324070300400820011024064001081d4001079514400ba2004184000a000041c0245e007155a50100400050070000c0c0c0e0016070390040c030001c4e045140ba40101800c091000d064803800b5000c04280e600c40342c0300032818055510b41440001410b80c0d490000c24841e103108514081491800140d0801600c14140900b00385c0729400c0003000110b0f440c00040d412180da044462107000f00c1c0e070b0400c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 266565512 1250 266564262 266564269
    0x102031b0906120115031a010c030c020f0411040906081b01050c0f0d0507020909060432070f15090b1605100905010b1201090c0608040311070305060f15010905 70
    0x10440311002034110b5140107180042200580d0b02030300442c886070a900390359940c481c0e06001e8034400410700080341100802d5400003030301038104518020148031084041c03c066684107502110400c4000d042130002c11030b1040145074940c0540500501c0c00e140c440d01003900000040e01e42421111940c540000300d080c2c0005445a402c5605d1061480c030803954005400c4a00784250001354040b61100c4c1d03114183c074410042042d1008113004000c0d0701c8002080046888204454070780882d000502282c02510010303c020603640544040251290110000e500f8128004110072180c4180044105c0b07607800504845143d101d110390070b00d1110510800c1e0800380c2c080b0481c51814800c608640a00c00d64541550580b00e0090302624540d64400c4c0d18407103405c00f50000c1c8580c3c202e54008101c86080759032019012807941c0110001c0005000020b010103008117052842c183c907107811100c0a95407441e00541d52442181d903110b040404001103503c1503e18640e6150b14603050311000714450030042072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 266566762 1250 266565512 266565517
    0x42306040209072304060201020714010b01020604150b09040b06030f0a0305070b1e040f0c0b0f0d020306010207051c0203010b010e01022a0d050f01060b070c15050f04170606030102031b 81
    0x8400311030020214481910781142c020001051b02e40c00250300c07008582131540908400c45003078031003a4100300a4032200da902048140e4007a510211508014013141c001c0d200078000020080d40110440d0140030511942480c133612800080741140c2c824074182d103246ea140e40e07000000078041b0b80107200280000d072901151380d03070101421403202440304120000340050740c01990300781c13184540f107400038061081801e40c0b031340504a0640c07040c1c17824201805070341c0d2030300c11848100e0311164080049411b0b40e10034400300b1b0041c0300042501149225000e2402c10658a0203401c0744250710f42020054a940101c0b4065081001600503110030b29802c1c00c03084009a07561200c020b0851120f01d500c50513558600c1070b00c0703c1c43c0a01f00034085400e16007401800c5a0854000517092081400000001003e010740507064030032208000c00078540320322065602c1e0090452400e10300c1004600401d00c1c2e00da902524010910305412501a62280c0007494201d110076a01c07032161040d074855404444815100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 266568012 1250 266566762 266566787
    0x150509010e040f060606080a061e090b040603061d0f06010608181c020a0b010509040f03112e0b0103111603020a02041104081b01020c0d02060d0504230604020907 71
    0x90b06800340807181d48984c200c0c0c1c010340203440400d12a0302400301030720b064070501010301440b400c40700314044114450b50503006a4840c3c500c2c05a192904c0384803070b0311507812090095502140c24044a02d0480700100e2448007084034041d9442210b03110088010005211812510702e501e0300305042d241c600c08041c5004a440c065017013441442d010304420201100c010781c14202550141c0b0301c030b200d02d1800e401c036000c040e80014441c284080c180800308844468412000761305082a00158010141e42c5091007090b21110140b00e8107070300c05508500c14004030042805a0b0401085000c4030b402c01541160b03a8031031001ca40c50424010005240d084240702c2601d5800313801228030541c55030f40054145d40c02031640c24119540460708001400307080001400c003c3c50081d81007201207083c40000c2d07880010a039100e104881d1704903940e09644510f42101c030307022100c4400388120b103071505100148444506980c0c1d5008404a2010819070010445074020703580246400c3c40d549900c00c04603080d441246 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 266569262 1250 266568012 266568023
    0x1021507050909091608010c030c0c08091908070312030506040203040f170904020309010903030528052d0f0a230702030903071710021903050a0e01090c09150509010e04 74
    0x801850130b0711420481c09004095171000823440031103800c8010242e8400108060a10407101e02c56000500100d042d00c07403084e01035409080c41e0070b803405034071450403c0c0c4c3d10030340c280d01801c03201009000b4102350001c03e81003240ca0610494480070300780b008910040300c0c06440e0700360302c1b40d00c0c00c0012240c042c1c816403501c1c0c0e0068a0300301660040098101e92040d1588800c5030b6494101ca01010741500400d64442c2c0c910590441b4007420244040751800601c443e1009590748070000382420b492990300c40c2e1241e00c28100c0c6070203045214084403201000351230401385054080d00260403d54940110311005140709181c040d40c5000745850826800060b10713045c1540814025240d450300c080001400500d4851680e00c55144040002e509140e52421790002c1c241c01000442c0c21450851007811a0320902e160000d501e0303850400d450020100e184075043c90354201382026050102800a100c1924020f040822224541a1220300c204409100d0507421000c510010806440d88050301c0d51700c0744c040c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 266570512 1250 266569262 266569273
    0xd030c0201140d020d060e0402090a020a0306030f06021b06010f0b13240905030a030503010e070c05060a0b04050108030703090b0d020d060902180a3503030c04050102150705090909 79
    0x14000b07a960360428400419115804600000d0b4501240078402c020142c250401406052a030049100c0f258014001281c0070380002d2407609040c4207501070002140c100c08400d81032203540c0391070400395002e01c05800c146103100201040728800450b030141226032886200403036525002e482102034024078000740840c0035040c0300050300b4154a1241360f081a601c0d0240704824107200c0060700401c601d410843c020390060080100098020040380d041d201124444010f0b603403886001c441102510300010709601800090140514258010300220f07401103809002e03d030f8817090207039600d015001024000641c01c500030040196400f00a10703a915101d0405458040154540e4003981c20950000703c40c240e0004d0f261140d00e408005002c9054002c40c0d1626500385010620310301b480c60500040032040c040c010f8407140a039015110114440b0b2581501c1c2c483c07610003030b02035071600544103160150107990714000d11001c0080d9028403810884c1c450604000c1890248080c03100018002a214481c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 266571762 1250 266570512 266570537
    0x117161106040c0f060201050f06090405010e0a05011b050f1207050712051305010512010b0a050d060f08070509091915151707050a140d0b070c0302060f01050d030c0201 74
    0x1d001c868451405510083c1d0004c0c90a03007522418000c0d42d002c00e045905d07020901011068130300311182c025400301e13090740c40b5485604080c1c1c014500410480c809102c0c001000080101c190068640e00e044524125042d061104040e80c013442007001d1074041d024208882440061b103842d0094203e26140f0384142040c006643c0c1000c4e0385a4010441c0c0031030f9020900c3e40c0300604e04122117000d82028a44075080080070048801c0d4604103002d18041894003151781100035100300203585d281514040140440703680c1d9204807802d140140504400d5014003030f03000c9a075040c090600c50003054520000c0403c641c0700244800322000108040318070015043d8080313a01c51090081c0d1841110740c0d08050112850040841d541d2541c1e0018501c441d00104820805682e526000c8405c40b9401400420700100040002d43c509411640c01801c4964800c1446101039018215880140c429000c59009440c2c107510070000c420244601540400142101030000f4410041001101d1047c185401d0300d502 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 266573012 1250 266571762 266571797
    0x5010e06030702011e050910020403020d0201030c030f02040b040e01080d08070305130f05010e1608030403020d020d0b0403050c010f1a10030e01050702240103110915061c0506011716 80
    0x20310b0b041901c0c250786440c180441c551f014031a140001a001404601d028510b9000c600e464801c540040d060554444940f0050f6001c0c3c2c0212144011441c011540d40303071240780d447e43c1034005002c3c0a84d6195402d001040720f5400080c54554603900b43c0361403149039a0383c0800c03401307071400406031602507071209020400500700f900306d5044035200d50700110320708501120782032400384121218841d19450080400991502000301c03000c1d42d4054500c05220551400810640c01001100500309400602000145a0b203c0041d281d200301c0d0728028030590160078a44000c0c2c0d80405510007411114007101501483c0200400d0582102c1e400c0116825001c00c400c2c03403c480c000c48218001d41c00003508020070081446545007919500d1948860950454884102c91100d660441d40a00007045c0819051300c1c03181c1c0341c007078aa00300910a5584d8903400d001302d0b500312407250109481c2406c10010801e558054400c803000d40c00d110620801640c3e464100b46c940003d100440300c20301206107411140083c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 266574262 1250 266573012 266573051
    0x709120303230a0e0d0906030c0201020405120a03080114100f03090b1602150c031303020f030d140906090c040216020a0f0302100f0c06110d0f2405010e0603070201 72
    0x2100c410020030710714004204800b40c84421404c83c20541007070f404000310316000340110301a03590600e000144100041d109070300900c0740c1d400c29980040d2500b0249a85070000030000d00261007652406401d980e01d41c0106103181107074007840c2e44005150350700854140314101c0d200a1111900d000300e05a00d00780c440c01c0071480c007551801d040d004c62801ca00a410340400918440031040043d440c3c0e00e140204101d19540405090701140409417030342c4005142c420021034031041503100590f983e45400f0051030380100b491200ea00d54410f000c01c00201a2407010580502c45c2841c1005405244510780821000b5400728004804c00c0403889146e80241e1600800d485c0606011860140098214010001800401c80c440410020755024600c607841d44907242040340b0741d014030080b030480980345100d00700e40103002d003c0c04100c0c903190030014102455004000540561000c54840202c08032440c004020240181404582101c004041c1414060001c40d800a0b00344000100c00b0041e41056a001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 266575512 1250 266574262 266574311
    0x30305150618030705120a060902061e0301091104050622080d2001060302032e110304060b010201020f04170a05120c0f07120f05070f0b0d05010e0709120303 69
    0x741c454542c41500d810104a26005004c04840302c02c5100c8a500384a5510000c9000041c61941c440071058119199039007a5613040442a8441c41c8280d18030940080580007441901740d168241100b20380d08400d088200c3d0150703080600842d1070540b5500580504605078005607000e90306903440002c40b0001071200d80f120400c90703a9242d0034100b1000242000c90190f8602c1d60150745014020401a9400a020301130012101700034000c1c1000c1000110308060001c4841c0031003414000010f208041000c000d61081c0d102c0c90307041059a03603105c0124202d000d0303880f101954981c104410700400305058400c07105284450112503c2d00401d0b59042d040c803111154a0401c202c0218880031704040c20b03c1b02110742c0f5004001410807a29200352040c1c02c0c502c2c0e101c00342c520300342c4c441e4070b00c00d000e01440070001503e680c2d901080039590b02d140c0280194006140030204501e040004903540e00085c984a0003144d0b607a47c1c1103016424260003003040c81c1e10100460038550349041000d2131030380e1007607012000d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 266576762 1250 266575512 266575537
    0x403080c070f060c1b120f0512030a0902090f10061101060b0a03050f0a05070903080c0c030106060207080129042715060b0a020d0516050703050304031a01120303051506 74
    0x80c0201403614041c10400c215411824201c150024081042c4c812032141c2c11b2a00170205280c001c1d1542801401d2a03c101025003944c03130000b04024208000d84c204866041c401d5405a800d5036601a07069000c41d4255900c80303c145404808200c864480c103001f00086100000002d0450f82e10105a40c1c694848816000881d07110003c204a42200c100115800b001c80b0382c00348460b280c1050024820402400020b001007400f00d0b60a007220300802c844100001c020380200000c40e140d8038041d40d0313480d00e4425040950300300b4280000b00702e030060341c248a07083e211501c2401c41c030700001000701506454480c09a5050104600c6417400c17140340c0341d004064050071203418200008058075081d6004c9422140d50490100a2408420350001e400d05002c1c28918001c2c1e12012420710291800142c0b40f0050300390700c103070340010040c04004401403084910900100408118540c0a4108040f0901c00c00e0340d00c807084540702000c0381c040d80180b50b1003c0c2c0c5409000c03055884800103002900103c10780c109 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 266578012 1250 266576762 266576777
    0xf060f1912230f06060d0303020c0d0c140a020d0b090307052b051801140c010204030302160e0106020a17091e09091b060d09170706050114060403080c070f06 69
    0x4840c54481e0102e601c26401c000d840070040032200350fa42d460001d0b21080c05070341c015000c0b0701414440e60580d9071040d0b281007640c1219194150040c0a1005240c040c1c070b040b0041c0c0c16403400c41c5000a56400c0c45079003c1c042100360704c00d944400e2030303140d4002c1ca00c1c403240c0010040c4e00000b40c1d051025901d00c150b4031419072001c400e60351480c20070940019042e024844100040c0c10310b4610042c0302803a0306424a02242000f004901e098254000d0000400f41e0358004103010017007507000725030090410101400040340380c2d80c1300301050119000f8030074803000d17030070215250022502c1031110780450301e406000d01c1c0c900981080441d108a96044070040445a0003220b60041d20b408518250440000b03c018400e95501040c01050040f00702c405d01e110701000031b1104107184540d0090000241c1141c801030002c50905100d8000d58403225080b00c00600e03050000c145141c40030f1100452180241c0b010307003401e0030356451040d03a0303204010a0010740302d240800164003001407142000b40800b9941e090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 266579262 1250 266578012 266578043
    0x115080f0c0901030305041403100c030222030b010b130302031501050405090c0a060f0909020d051806010b0306060d0b03120a020c0402090f1c060e150f060f1912 71
    0x24103003600e14038602d1045420100400200e5449070989059504035020345201100e1103000074a030000070702c00e1010480c105003080341903036055405045120082542611461810002100c000003036010090010200d500117014688580d0040c01d10500c0201824025949913000030f403410380c1000303600007108500c1c3c00510050900b806000d400038a94801049004000340016841d00c0ca00e0080350100007403d00c5905115202d0700480d0000d000c540d00440d80d0303000400100010740f504840b0081e0b03403181b1050304072100c90005030180c12280f030019594119102c1004004c440d91080e81c206d102d0369103c8160000c907580910404007120b0300b00108071303a11300b80c10702d01030704240b48030300c0d518415441405800700b2900d42c0701c1a00c0d407800e011100b02800104600d1000070103084824058551464000f07464030119000a6042051641004441c010303640c00c01d10707620510702126905e8000560b03051052080c100031600d680403603a03a051503801c1035180c03403a29215009000054032002d10a48021 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 266580512 1250 266579262 266579293
    0xc06050c09010f0503041205031b0d150803041202091503030c1f0603030801030b040309120303020c070e130b0c09040c030506150f030103110f040c020312150f010e03011508 76
    0x10043c2000e802e0880c00e500d0143c0b0b803100b6050071752410500344140040002c1d162202681c0040c0340c20b20f080d400549940400c1d49c06d00080072000c5030b0003803c40300d910b80854a40e42c00801e03102151064058442e00c6150355090202d03418001c0d00184021601054221685c1d40034409000283c50f050001c0401d05603601e410030407611080300880b0601c5c034081060002c01e80c494a840e064980040c1131095070380303651900300c5420720551b1008090803e4074540c42c0c101a4103800a201c281d2902c0101c0b80169190070540c044407409480b6521074404a606540000d01401101035109117000740c400c1c28143d00501203000d880642440400080d554010000140303407581121141040554095007070404814440b0f40c1c0744418080501016016045482256540c0010119140010b07000303100d1000002006941da4001c0011a041c10202c1030011341c1041ca691010900e8035401000403a1fa040000015102401004103154240d500c505a81c82c98007030b844083e0700200150740042501a500c6402e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 266581762 1250 266580512 266580527
    0x204090b1005040204051305060a1a120a0507050a0e040605060f13080114040308090c0d080301090c210e0304120c0302010f020102030c0a0806030c0315150d170a0c06050c0901 77
    0x40f44902e20500c03041c8203546484400ca055000b50f07280025041d20361a00107822031016600480f0221921a811520908800007814405580408100c286c0c0c4450040c0d0303050302c1044461200148040c059480c85605c9800c0758012404054400240141c44601140c42c91f403000d40d003081d98180018000201c8804000d001c801000c5480080111504072620702c400a1009800a81086034420101d15107680901c421a0325000007094040c80c21110b00c3d040f00690403d01c58080310910b041c0400001501825400f24120202e091240303100d00c0351400f5900800000c161002e65200a210100d08103142099041f0707114000c040c0c520082d499803000411105200441c04116401401440402c42608055480000c524105402170791f684a021030b10301403402c1801c0d6814420060180c0c1a0381030143c0c00c13405518044d094a03245402c20080c001113640c60030005010704102e2000702280510030f00513000301040c902d4180900341c61900c41e0380550750b045e40c52600f29000080c14070399660b0083d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 266583012 1250 266581762 266581769
    0x80f1c0c0e120c060f040f0e070806010305040f14120708040905060a0311100e1305100b07051f0605030f0607031404020916030b0a03050c0f0d0b0703180204090b10 72
    0x9000c10b01a80704000720b80c42d5080404424000c12000c9a11030b41e0032400015100901140901240307080d683c1c802061195030160f49020210f44040c0108000d0352007400f03605c0c8a50740005008091075195074801031080905c0c41c0350711082c000e5a070001a007500301d9005100040c02000d8580d1694104000380c030444801600c403500c9481605003c00c005000300100a01011003156440105074420400343d40100b04250040d41c401901540000c1408440e4407841c0550008150f001503242c582010031124415108040c0130390340308095030454000c2550300340c00d20789141a0007151444e40c4002080c50070004880c00802c542100701080403580d85440780c1404140707642c00b03500e81420290049040704034098180c0d800c501349842e6846082c0d0080c1c011241d403c2001d001c1200c80ca9407400c043e512405030148043c0b04811260701c0f100d0724a03141b00c584175041c0e00404080328036141c4101c01c0e801800040d2035680c070b00611000160141c1d48502c00d9600346400380d451080329142095162100c060130340c2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 266584262 1250 266583012 266583019
    0x52704110d050a2a0b0c10060611100b060f180306040305040e150d0b040611040b1804020f12040f0203160510030c0f0e13110702100219080f1c0c0e 65
    0x204a4481810300c1340f07404d040b1031900d080e16550344030040c50142000c00399110103841e1401c200002955a5001d564401507855150170f0b500100e000011007002c4d10740c032400459200c0814440d520240a07400010005040c107580d030910142c4006000c00d0030a9000c035426404503078040342c104418081c5a4070241c2c041e004030345030004c8286010004000780c2480d60050003892151001400304041031703000302d2843c520441c01a489aa0f0b42134501100d40c0700944501c0b1800d48106400c0d42410280280c5030381c0880c0d489914240307101c100444c2040e2800500550701c044803030b21410096181401010826070003c81c03180c4401d8103040034443c150030115025001c041ca00302402404a5121824088000003407501a0082d2114000204421040c501c1514018a041c0349002400c6580f4001c244450ac00d80380d1603400415208266168440d40c3c400f0302c00b05428040c184009075500d0001d00100100c1c0000760705141c4449424850840c1407800c074403155944054001c0300780d401020b16988940202c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 266585512 1250 266584262 266584313
    0x10b19030b010605070501020d110c0f030924160804060f050304030c03030f020915040303090e04210c080a09211e0203070b0a090906052704110d050a 66
    0x6076a15045a9030500c198400c12030003042d00f0017048401c2d011a0f0540c601440d09018000100d15482042e50080d4407143c0e444c407079070a5689803450080203480310b4450040c003a8450001c400007030394941102d0b03400c117400002c0c1005020004030041815000c00d44c0110030103500c560030444090480048644442706004091040000007580040060016541880c01041d0003880305d240c08042e00601422590000b40c25415111595202e0003074402c6034000d80d12680c4660342d0390103404014001740d4000d01800050810380740c00d6820180401c0381c680302c0389042a0b40960179118082d6a8020602040000e200c80404001c0d091001050b11001c14100d802d40c0460482940c88164008040039031108034125401d05c10190340e81406240300a0011520903991140c0700700c00204031018034003600d2090361400d0404101c6091482200b81020b01210038200d060502e50a07061160320006c00c00c58220807003040d4003038651a14219805e0303540c0b00754000d200d4012a881d0010180768000080e80d07110514 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 266586762 1250 266585512 266585519
    0xa0603140f010e04030e0a171515030307060e150a0504050c03011a2e050c010f0c090603050406150b09030123010b2d0711010201090b011806030501050108010b19 71
    0x543e42a550003a41c14182604420300740804524010300030307880a8103100f0318040700507071054085407030307500c2400000401c2c8d801d940b011284110411001e01c0707203130998800e000e03150000701c0d00e0b84071605161000003152103c0c040084084c403034800445900042d191071b00184401c00c0350401201e14490f201320004d101c1071076402002e14140008951561240200140400c0503807401e0300c0e10032003011220b15000b10f81c0e440d501e0241260b8840740c200c810540c640542402a861241f18422400d00c04d6500c0c4004145046001c90140a01520075644a565115840140c0c2007558004001703184c052009912024404101400c4a922070520507004040d030800d4584d48001010003415500c8902d180f9468850741c0e103103104000c1c0540540120142d982040140c121003a03800f804a2900c02d002c846100c010001c012402c0e40c50165000308011511001805508112458007075694640302c1c000031919642e44816013174810030792050089035544c180d084c4140c01d00e10f450900b1000d10a4503800c0d107528 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 266588012 1250 266586762 266586779
    0x90e12030a090f080a08180f060106050a0216060e010e0906060406111f0501260c0103110c0a0807110307060c0807060e01140603010c022b0903020a0603140f01 70
    0x4024405507050780d50b118041c0070000c01840f0003c00940000340d05450300e5656801809810042c2c907010b142c0e0070f100c4000c03440b1040000d11501c020b01d940c400340519900e070002c255050b800c1821003000350701914903040c88080c4c000303004900600e0255181c01c9803401e050009000c20b8000044c0c2400758114034200030043c0c40c0c1c001120200ea9117458400c480c10700c010109400c00040d844011541a41125100110340b02508010306a80400f0714410015102c1070300440e03001c2c0c0c200b002c000710f46c01408090081c1c0d8002d0f40403006140360604128500807104c50118248801c1ca6000c03a027144003c5a0391050004144480580103010307402415001e0508800be0b0a895a44800070008600014070707404005441d0081212820f819000340020381406480544940d82195614044c1d0301e04620004150300c0001c10518140e00d00910180304289441501d071554544070708407082c000c1c2c0e1300c40007006849030352000c0010700203036030000ba407003040701d01103e00c25401402d510009000390005001020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 266589262 1250 266588012 266588017
    0x30b060a090e0a0908120106030f1a09100506040f09051003020d0f06020706020301120b15280b0301080d0306050301090b0105011206050909010911150a0f09081006090e12 75
    0x20882c84400c48255915940c20015012201d0000c0ca07070800811a19001005060b03070342d059503015103080c09101412807401d001c880200e400d5004203020b00351030302445d08102c004140c02c83c02c000d00390704c10f694854001c82c0c516807140d404400d81c0c0820420030481c44004d0310929800088140740420718a01d10380010315a134a4640c805400101c900b02c081003000390a038125011b040c0e106009546a43c1c0d14030015603040744401060341c03645a00b100040c42003805284150840400500d070000500d9147e1000c145900c103d0001800650441e4021031101400c81c080c500a0440c100148036200d0707081c10080907101c1e5603002c58000d80c140f000d424000b807489a103c2d81034480a2802400d241d03045c110842c081e0810303038040f07900a162201846504031043d04150f25032070007610000300c0c2240c91400c1c442c01c0c0703401d100800380000c81440360045042c45403c2e00c19840c905441c2c0140000d45415603142040b9a0411014106070b46200c1000903400c580030b40003240218102905808903005082402e03403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 266590512 1250 266589262 266589269
    0x3130807080d0804200d0f030e0f06181c0c081204080309040f021e130807050a050108130506070e130c0c140f0312010509012405090a0e070c03030b060a09 68
    0x20414102c3d04403048209002d0070a0b040c0006d0000c02c43e140c803400c04816103c001c0d10168001840860410010700308200c0014507564040c0caa140307450b20051141a600310180e12460384000300020403000381800ca00a040706d140541e1444040a01d0920854034040024070068885a01400208201e050200035148003203415a00072a40c90b640321400030091044224513060345002e80c0c400140c0c1d9040d04007601041c0106012510015214400c103030395000b140c881d1a45c400503021040c0100d505c100030707050700041000060210944660b40b51411300100300e82e140001010140f6040c441e103001c9445107142d450b000340821405041410040c00c14140003005080e45900c081a02c445c0d49041140c3c030800950501642c0c0c503007c40d000304200381d840c02c1c4035491007680300780700110704041c8003520b010640194102c0b046550340c1844003030301d05400000f103c0e580f220642c14001021070566004a100f400c403650f440c8402c0d4404d00c0d0240071901c03903000c090b0140c542400440a5550402c1039103068 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 266591762 1250 266590512 266590523
    0x714070215040503011a0102160b0d090618030e100c03021b06040f0b09041518050402040216060b01092106091103121c0c050f03041403130807080d0804 67
    0x92824242903054580300d03d601141d015071a140381c240c248208a6000280d9401c26426601070403658001c07010301c0c41c1540601009640b0401c00440c100380c29500901d030301449008003140c8000f0340380d80c0300a43c680c003003400e8001c640300c5c21102d4402e01d00f824400c0c0e584501814000d50700b0079941c030000c1d514051221900c0c8005400c10040c429980c41d101603400a0041d0700d00f90b08429290203551010360000040d07203020300c0c101005101c0b80700b10000c0b00e0040c0c90709240c001c178004107880b10210150201400c1641c2141e03007000351400c21255544103062007405020040b0b0303050402030004003140e45a62000c00713140d840c11140a1104c10f60454454519000b410105088525003020100100042040c0340d061113039841143c0600c0d0000040e0042d912000b00498900c0b5500340c140c0b05403089440d0020000e1020071218020280e480c2c06950041c0c000d02c0e40c1d00e140c03400403405a2541e44080c55100001d040940c00b0000d10004004e6800035144010140040140b40c0402408020700030f4401401d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 266593012 1250 266591762 266591779
    0x90c140301061b021e0102070509151005040f0e0711010b100302070302011d0f070b040b1e0904062607180c020f060703060303030c020c01020c040c090e041a07140702 73
    0x181200d0140c050315029001048041780500f09482a0f050342d28810b0018090302498100162a240c1001d800d071040200b9128140300320348078010000203811900040052050621010808204030301e18080503040c00081c121450400718405006802c4d103c802d1300c2c03543e0408100c0100c5481ea030f0503010103640d8a041c0581c881245140c00d0b400762907000c030718000400c102860f10418002c001518468080114240c1d000d0715244e0080030058842e82c007400a104204110030303020b2a01444070a0860104141e015042800d480009020340c0d40e10307800140000b40f9400c1234960f04042e071204c181403a5003000140f90b040d282100101100c0c01d00c6208a500660701c0500c0b044460007841500c00c0c4510000a550061030070301d001030001c0c0410700040e000a840c0c070910300b1006000140b50b500e581d005070014003000b42c3d03130000c10014008100e41d14040041c05d07000001c0c0f1075101800c40b4025441762020360b130990550103000d890280c0041440040001c0305075910003141000c01140c10003601078503400d0307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 266594262 1250 266593012 266593037
    0x801050a1a0a15121503140d080112030c1b05010e030a03020606130b101806030603020609090c0f040609080d0c0218060303071203090c060509100e030c0a06050301090c14030106 78
    0x102c0300c4844000b44d000e101d041000d0105252404174164003070702d10a400420f01c0a1900b84495680d2036400309020110b1410340041c0624101d5042280190784607281400300100306560f8440500401837031007003c450442ea09019641e0042d0340d901721443c1c240c000b84880c5469440081d502c0601810050058255448400d00d403c0e40d80c10840a1b000054024030380d60603100707001030400c10006a00030044039011000301c0d082d032103405007008a0b50010846810140f0000030000216005807070350040001c00c1041d90f0900c12900b02400041440751101c1150a01d07083d80c0c0341c1881590841441000540c40da24001030359405501444450038440010740340e80c1d000003103072451180300c00181200321724000c0000b2159254100800c1c00d03100c1c10b440e8403076950350b01007610e8a008034404654008900c0540c00003803807140c50072800c0c1d01002002c40f814600f07214003040200c501504510300050000005010035041030280b051107406518201e0f1000152403c801c40710700040c00b60408000b00b00d500403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 266595512 1250 266594262 266594267
    0x1c1205090a080f03011d060a09020318010614031b0306010b070309030503070b0105120d2c090106080106081501051602030309090c0901090e0907090902030f06010801050a1a0a15 78
    0x40301036a01041140d0f0700e20200e41d40d0660340d0024450280051281003661251100d0a00c2803401120082c08070540c0504114015001c0d400041c04e200390095281043c21001c40b090140100520402188480c0c0c840e01d2410306003050004d4426206150405c0902c21068500281c4241180c6040103041e44403c86480d00f1101c1c9656540054100e00c4086510800d2080a03c2c2d01070484070101c0300c42100356445241c0c69100c84d603481d040c01c0403950201c0c1030b81c2149282c0003885255210301c100c2d581020003000028001c40001e0304036800048940c00184105601b0145143d08104154062000d01b181180001e01d54403890882d46480c154940000302191402c0050383c04c000c000414503c02443d100506100582112050701c2c0021501c00001079540c00745982ea90103600c00c031028248050414034000301405003c10126014030844000095005041c4510fa010344140c0c4008941410004030702c0342a44c0400c002041044107807035102c41c0d41d681e204682c00450310a0140665480e0340c001c0c06 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 266596762 1250 266595512 266595523
    0x2030703030c032304050a091b05030a09060203040506090f0f060402100905061b010c05040311040e0304050d030e090c04050303031b040504023907091a0619021c120509 74
    0xc42c440b0401a4590038101d00f6850080c005030303101a500302c0707010f95440d03c420307027600e0705901d0713501503005050b52038a2060701c41c90007140c0c4090404804601c1e600700313a803940d040360b2080f02c054899070851010f100701040c00344805811410240c00801c0c00341010942d85031181c0b80504004d1082401003500e45005001d41401d6005090040202da00c69001e0300c0c60004078152a1540d4619518103410700341c10038010b03c2600e040e240c1205a80d03148404040c1440001c100d0003c0500461000f4800003446540b10b4a4003028140712790b442c5204103404800344001ca803c05400a120000c007444180940c1c0ca0000c1503c1d8460328552084e45008251030046a43c0d20070303900a07582080c000500e28185180421603100d511000c44e85409004800c103800d101c4002c040e00e03010701c107504854810861028144c2220b891020700c60307078801c46036094000040c025840304001c0f030030000d000203642409a070140554156240c1047c60403080030151100240b5010b0070055103400607594601040110208200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 266598012 1250 266596762 266596787
    0x803040e0a18140a0b0a1a120115240813020f1807020d12091a040c0905040606060e0d3504030602120a0605010801092a0518060702030703030c03 64
    0x75070280651120343d41c58840340c840d1010f40d000130700000440c0015616202d00f02200040d003146c0c07552816250104103c200042940310340303564031014000e02030a03282c6c030780c2c9005004003204241c014045a40d1250202c03540750481003841402c4c0308000c18108035100d13a4a803107034101d0301191040c280c02c0010305c4104014003d1041c0394a15420882000d0300024401c519000b1030b2648440311000f44e8541d425500f107603c009080401c800301c81d56001d402c458540350064400c580c1d0800031030321145103901b25601101c0039035465440701e90402000782c100482c2c1c0b0f6881016142055040041d4540781c0190030100304540d41c4a100025086e4460301d103050b0841686c110916240c2c0c0c480c0d4174202980650060380c603000200040301c011417001c024500c01c240403201d040e183c0304000d80c41d00507850000c000d0340c9020200e8002e410640d402c011901e060705043d060054640ca512041000034103c0b10026800070240690710801c000c9015039400211001243d605141a40e1040981c2c641214009040003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 266599262 1250 266598012 266598023
    0xa020c0f0706022d1915090305040626061002010603021509030d020601081c09080a0507060806180a0906020903100506090c03071d04060803120406060803040e0a18 72
    0x6901103540d039404a1200404c045081304100746010304281c09101031080e04200f0300d964881076032000e9805841c030301020307501d024282100d403030403d120f90142070313505200040300098000035041c000302d50003030451a044d50003a9403103901100c0078150200d5001000d803004d0312440035000c8034140c043c800d40210010f5a4081c0540385503541e01510700303441e50846214248240100030003101464070009901d8101c4c0c0f1940020031040e0341c0c1d48142e0280d40b055201510800c241510f01188250003045080d9500f44940028800249400300061001201401c41c0d03109000b04a6001c4c0c5400c039110f9070903000181c0b000c2c002241c003028030b800360084c0b040c80f40d5240c16016524066146a030142d210034882c110580c0c0041e060f039a0004480d080d844101c58820128505a98000c403a41d10380c0c022208444c00900002680c0f9140c851251460704000301140780700344920100400c0142c240600401040d92000540c145402e00788c511500020040101101c955104c1004010f221b500010800c01d82c1c202 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 266600512 1250 266599262 266599273
    0xc17090d0f0b16080f09070e0910060b090f121e060f0f07080109090c0b03160201110f0306010c0804090204060903060b01020c22090b0c07021504030b0a020c0f 70
    0x24948489502440310094801d4000000043c800307152071689050481c455030740f03c2c1016a940c0c107004100000141c50030301c00d4406e242011800c005091042030040d50f002d00100030501c1e0031131200090714010b0b0001d1020b140d080c031042c0c015441d104100e54644d1412204252108075015655240005105211900024040c0c0350041503002060290180b103402004000b61703520700008041e1050241daa84000800c02c1c0010000740c50140d010440072441000203803542603941c9540c020542064907002c5400300070061000b0703420340910500400c1103c0040c903c2c101141600030105c9404020101414054144955010858050704030380103421444021521151980e50040111010380001c6801c585004100c02140d8000500b0140a010040c0b100031900304c20461115001c071981a0003c16035100c0d48980b00086546150906c9101d074139185644507881d80c010841003408507083d0b805501c204000900201e10b00850455012500800169840d010000c520380342503058141c06206000d81c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 266601762 1250 266600512 266600539
    0xa05151203090d06180f1407051c0f150b011b0b0f0615040b0909180a1106070b150906120c0405100509090106140a08030d0c0c0c0e0106080f01060c1709 67
    0x450070450600da000b01c0003181c1e04800e1001c422380d42c0101c3d001d01540201c400654502c018104030f10310504a02c52540e80c43c024250750ba4445151030070710b103040881e603180d6940d104a0b580c060700b0002c070407680c1c181c0380ea145115921111079042014120000d1300303000700000780e42500c58415115080030460080c0d81d980b0b44e15114031429401560580744141c0c02ea07400325001a0420b0340701000d58042202030040e5152641d555079150090342d400942020085c000070340803610300c10f5454461400d05408841c000ca02c40100414a84014140c5102d140000200503c0201c00141d030007611409075400106c0380c4400000f4414444954030441d03100702450300f0000820b00641042003100c1e01e45100d40b004000361000c101c80da805030300848543da0700500501468003466045145000083d040941e6482d490b0b03200d0560820043c3c2040c40403882c0d900c0100300c0c00341d01c03111896001441150710800d030f50402c3c500070030303540303000d00042c242e0841201d81040514482044600b664801003180d128100d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 266603012 1250 266601762 266601773
    0xa180f06080112020f19271803050315031905010b0a05030c060f130f06020d020c030c1804030915020c01120209030a02010809030702090a05151203090d0618 69
    0x24103000e80d0300010091000041ca940441000d1544141d00030711040382c1000f03a8041c4501c42e2a04800909013000038a40024070f480c4000c0e00c2400000300190f01c0d2000c07150131222030150b900d0b050702001d00c1d2908005d10320101c0d070b110341540d030400314513440b8026508040c03000900c0d08804c0e511002400194080b4a4200041584900000f0300140d60704040a5590000c254440c0741d0310a4280e0040b004114101d41c507009000281200703449200daa004140e01c0e881e1081ca070903680c2d000381000d0303881164210981c60701007050480450007100201007001c100d1020400210b00c80b100359244024207408101010b000d00510406405d02d0360b090a41c1c641504402540c2d0410400510301160380e0921b9043d1a40040c001c1300c00d825409801003011004680c011100c0580c010310704c00382c50009210345c50040e81c88003003440c0075911860000c00c1504000c058002107500b1202168031412002080700745d80413003c0140d411030b10080b51040c01c0b081d20303804d02c0c07000b03031080200da1114407441184c440c04001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 266604262 1250 266603012 266603039
    0xc0b0d0e060f24060a0302160807050106030203060a0207050703240c08100f08120307120204030f020a08030c10051e0c0406140301060806040c03020d1d0609010c12020a18 75
    0x40c3c030010340350700c51190001c10300c2c81c000341404240e000001000700c0c6200a010380c00518440c2c1c5d030003030034458a42c8661100200341d0030000045401e65102c040400c01d614081040035042042e0f104c0031468644203699080c0d032a8900d00c0010101030345440303400714000b0440070070345055903640d03401d100200035200014187c480840e0b0300c11443d08034003400305d200c0d06440811010354840100034100c0700700c0d100c1184010b41006102da410070079961b0b4520654145400500000c43c07280e030044540070030a00c104041b004035500b1a04c0a5031050101c07034622200060410365124580c0f000060036102c0c9861007a80c03121141c28680700d90030b008144002805104014401c80300d066131071a82290800940004601c000e05c0380c0800a95a100071403214074240e40000544080b50500501d0702d01500d41c01819204481c032005c2034002c898603411100301040c032880e94050309090007005a504009805800708a040c02031034a40f944c00f00d401710b404c3d40245c2d40000c42850300101100314981d070707010141828 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 266605512 1250 266604262 266604271
    0x4120b0403080a0209011d21010219110c0906011115060f060a20011d01050711010612030e0a0815070e100509060325030f05130c0b0d0e060f 62
    0x2515100003e440401510a0311102207051351418003440713105039043c0d000c032588240d26510180b140030707040454549105d469809a4050000360701c62a03d070800031402c503100d42c3c14200344520010755008201c00401c0c03101c0c04107021a5a4010382c0c80e0440100c82407240144012401e2040001c030b00747c04d42002c2c2d001031084404031a12103010747c5141c11702c00c0c54010b20541c400850074051110190040c0c1e61040400d04011000004217220150381c4480b4414010440e82d407265555028444039035448074045090a04500090104d18a424841ca04560728080040c0422611513810318030381c1d40e02d200d240000c043c1607007110803135025030218076119407041e242c4201080005c4d510880e103081c00306404e40c1000c900d032030b01402e01484405228403a070004060504100803000801c440b51080d0442c81a031801c2550001100201da501c040100c500292100b010003c00c0f550b480001104440e21600359032018010949602d103241414000d00785c0711090480303d028203803c01071060441d0003d40e100c1d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 266606762 1250 266605512 266605517
    0x3120509090c0c1509030c012316120b040f0f050709150c1106071a090f010608190203120f071101030b13150f0326210c04120b0403 58
    0x164441010040141c0f00d100c2070380055400012129561032a03444820350311181c80002e880c070341441c540000e800c650b402134509440102900501700c45968501c0c3c029403008180c2005107800075042d2015194060040400c5110b070b03241e0058400907204c039003080074000203441d820f11a02000840d00c030060002100c60b00c00164100d2400259881c210b400b0007840144c94481c55824655612499044000c50020540000d410046000001c94488210841c254a40d03403040c00c9052842040b4140b0100c0718805074103030304107401030113814800b0800d030540c040c400040c81d284400c0d81c0302003801d11842c50002a05a6000b0030481c070400981401405514864110300d0300d00351080c001501200c9030011503e401c44580310310b10b55a5591980510404800c040740314501580d07407640d0b403045c040944c0084a0a900c99441710142444040d1465040c0c550034144038204010501300f0250240c090f04024a1851820701003101c4a00140c1128082c1c07080140307900055000d03003410a8050380c141ca04030300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 266608012 1250 266606762 266606779
    0x103050c13050f010c050a0609030f090f0e100e01060801030213020c0c040b0a0b211b0f0a090e070e010f1d0d060e1c0f0215180703120509 61
    0x1401400002100c0444806410507901c0301e050000748911044003400c0e60f4140546540042c001c60010446c850b0722612680c00480c406c0c1c00c61900030608005840340105200580800b4015072204c1710307a84095a1000c1403000e01039503442000d170900c0460b07912801e0715801e04000410340f20343c400c00950580b40203503425800841051050f0781203201c4d100542c24644c0001c40c490802d890142c0200090400c0140306c4902c880d12550800c6866029181c2c09d000804440000303100320925042450384820306100d10303d61004040389a503107e100d52001220583c13000184110480e004002000c05030500d01e188007450b01c2c0050f4080c007815910841c2030301180780c501c034195955200c0c007800a540c0096800340d00340d4860000602055030050f800c111401c0c1d480756a1b1406024013007148074181c5d0000301c44450a881c650700060580187c03102a10110740200040c0c040c2300101444164000404c03214551b41e01030568096400d081444d04020140a500c800840540d60b01c0030107442403140031a00642d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 266609262 1250 266608012 266608021
    0x15061801060f02120703090e07030e0303010603020d15050609010f030612030801081b03120a0c0516032616030e0a091b0216030b130606090203010e0a0216201e010305 73
    0x4130341303024010340180041d110f02020b00ca90f5102110030ba4121031141004030f003c3c080849040d066404c241c02c064006940803070006418400c40c020001680c0800d03403840704050400c0080f500a204240b000380c10300c03150700340c000c00312032003030384808010044510140000120b41c500289040028401e48103c1d1044100704202e01c070040f80d02d8095800001c00400315441c03410448100394201007e03400601400074001404030781d0038007100408000440d50206181d007035140c46c182d506024400368455808800c042e041801e41c4200311512040042d00d290581c40891030700b20dc002d00c10b046140c1d00290407070700000d10301503240c1280e040760004104000200044480482c1c0e10a040700c4868003010002c0010408503542110780354100e21410654044200c01f1b80303941059880950000c0102c0340d00100400004121081c01a00040b441a05510309030400001d44210085075001901342c7c042c02044201103a00945200c005410103488a4540c420010100c4211603d041103140846e0a040025 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 266610512 1250 266609262 266609293
    0x3060302040f0b09062202040e06030f0a030c020f0402040b0706050402040c1403011e0b030115120204031a07120e030c060609131203020714030a0e010305010815061801060f02 77
    0xa018060000e404c0400560355601040201800490050000000074180240b425840d000500282c098a90903005505042007458a010403180c8000c0180d000b9a0000000a521150074400b4a2f01102c15000c0d4800b01030008009201c2e99008103014100040c10004104082d00200d00c2540204c030100003c0640c43c1c03090f00c0300341c03881a82e0341c0390b044100018172103528146910840407800c2c111499480b520394144424980c42a00f00028800843e40c0070506254440d81e0000004528001542494917507903075244081e0142d81800038801034100011155032194100340d5004200c41e100f4001030340c40841042e12644a8405900d0a01825002030094280011407601881580ba60548811050b440d40c1005001c94140c0d01e08068007008804041540100b410790700790000d00c0690355620440b1005000c58030060b110074189810140100000c2c1c00c045520720b4040480c0c3c2d40d8442c2d5646800004080d00108403031070030150050800807030065070007614080c00d5030480e0200c601c001ea068600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 266611762 1250 266610512 266610521
    0x21040308060a0b0d0f1b0206160212190c12030b03160302061c110406080f0f07090902070c05041b120b030706111014090d0c0203070e04170a03060302040f 68
    0x3c4a94034581000301c51907288042c0d2061800b007410041c0010340c00f00d03404a00810002c040c1e100c8005900201c1400030b100050f2040641501c014002404036204c80c0522a945000b035100b00c03c1c4046444c0c6c0d10710002405604d01c0f1100c0c950041052170960407031400500201800b88945000b882000311170b08041c000340c005001680c4e001455181410580266003041c010102c15910440e44c98030050780445000101038005800d0316182d1071071500d4000c201e072a9401d0000d082c068a0045601442880b076007104000050b141003080c050703035889060402e030345c9805080e400f858025250040f4014001485072900108103099600c8502c1c10042d5200307101640e800f00c003074540c1908146010080780c3c0c020070200b6000344d203400903114585036003580c501c11541d14112038882035071510f0130480070b0340d000c0c088203000407101e01300b0100d8810a0b40100303070703114528000d001c0c0204062021406004104142c10400440306400075541d529481005019100e0b6100c100d000b035040c01e0383c0d648a08028043d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 266613012 1250 266611762 266611769
    0x1d0108090307080304140616080f1308130b030c0a020114010b09040207150e01060303033804020c030a0201060915140906040f064e0821040308060a 65
    0x640c249106601e03a00f03000d900203081150f100542003181030030085c083c00414401c00724410f0044080b40c0700800501030100c01080452980d000c2010022015500d103542d204c956001034400783c94108a014141300f00e100d42c0c100c410200380c0442044440c1c01c2d294014051100307258001d00618800044040c0d95100038011030094210500407813803d403c050307000c2c240540c000e01e40640303150040c0300000700b00da00004001c40c1c1c2d41d449441c03d2042c1901801694000b03420f21507010f8008403c2c8240c0520714138290410518105150f024100c1a911501526500d00401c0c068076625020600041e000340100c3c131400d0b04c17190819500c5148070100a034100c0894171070024641e5034040510030064120b800605090b40550381e840c5200407622984200c00103025809d00803030030400c0500c0d682c80c10741c250807540b404480310200e514084895910103019003174a0a9000441c0611031700c0c00f010070b4003d180303054011304800c921261081680e041194001c40c000e40740d0785101e440d24014802843e41320702 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 266614262 1250 266613012 266613031
    0xa120e030726211305040c0305040219050f01050d090b010e0403020106060323060a1a1e0f0427050c030106120b09070c0c03060c03090212010207050a020d1a071d0108 73
    0x182c426002c0c2c03031102c0c021318070b203448060707080030403610b070f1002908407078600c1c40301c0002075510000c000450820000501d040c60044040107881480d0800180854441c004c206040220104018110760741c960080050151720004441440da141e68003a8401c10741100c1c25001903081100026815001e0701c1800709014800c180d604907105030062166108102419107604054407000000d04103030907003036085da00464201c8803a41e51605000200454000381070880000c80104142040300da00c1500f20b508554420403000241c200001210450361100d10051008505100820000e03003451001541a5000c2e80c654450000d1000414021107114299140d00b1044031804500301c54041c4000480b8507110721180c01900d41c0725616642980d9103c0a4000420749400b102030840c5400c581008441107440000c41c100300c40c0781c86030b0755186004074019000b100c00411100c00e01001c00c09802c00c031022000c00d01d425040c0001d0080494400c8840014130110024038900150310881000d800381e205034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 266615512 1250 266614262 266614303
    0x3050718080303310c050301142208040308070507210201090b090409052a010c120302030c12040b1005040c02061f050a0b0405130e0a120e030726 64
    0x20038641c00740311309400c0f440154002d1041c42100314500900c6080d003107031050f1000c1248078988001e041c00c0d1048141c2d80902c13403900d02e041142001d030003003880703072140011004130000b08810b00f0408401e12032604054003a6000040740704c02d01800003000000c80d013003002c103510000d40030002001c510098080007070000e0603038502040b0340020340004d03241c40744004000042d04c0c880c541c5c036145021209848040247e200c403040758201501c5201d008a104401c0c00c2800e070030607041d624001042c4107007000000307240d40440800c00354203030802a2005610014903485003410a418420300c820340440382c0e2100d081c0711400c04203440c241800341d0030302150f9036001400c0e945c4520006a075207460880d500c503540c2d00ea5002c002403981c1da0441280060140042c615540c50401081c81030010707040262040003030904840000c00000014800c210540082030741001402828003101c9000c2d0b8810100d0f03152043c40710120720555089107400340c01000440c217600d5041c2303101d40c180e101c0510700c0c48035915803a80b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 266616762 1250 266615512 266615521
    0xe0604090f060b03010e0f010905060601091503090303180f2a050904050a0c031416060f1d0604181407080f0c120a020a030e070308030606071e0303050718080303 71
    0x42d034003d003002d034100400108010f2002c214451030500350408204040e034440e003031780090107414040c080d001202864010702d40c500341a041031011440010010425540784404410b05100b58080c50b4600c1001c10100c1e500340090406131400d00142d03400f52031558141e10004d400099800f40100c0100c424040041428a002c0070840c120000900a40c0c0c58042c001e8200b00141c3c2591166004e18818042c3d10040c001d00c405091400000b095902451911418144211a044104c01040c2038980ca800440032449090790030a1a00700642c0c25044100403c010030408140c865030b01012646042c200039042000e4070003c0394000c1940c1d0640480c400d40003150300300c80100c005662014141e101545003801c1c003a000324004400712840130800d0303404a00e07100031a61501855401c010200d00404030f241c00e58558400e40d2201400581c41150000341001c100030501802c2c400c5000b540110184ca840c490402501030a0f040350340100081590102801003c130015048082c0c0d407008006509503502d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 266618012 1250 266616762 266616773
    0x3150f09031b150e0312010f03021807051606020d230f041a070c15020a08060f1207030507060801051801030618050f0d09060e06030613140c040e0604090f 68
    0x3401c040565420301c040910700592202401069450401a0000c0d9a5107920140d18401000180c008d0503101c601020100f0141c0d4664121a0100300711a00c40310861310382c444282d400340304041760a00e900d610041c17010180486540074080d2a003e0f544180300c03034021040848505040005041d00d50090403020504c248c00c0900d6541e805840b401c540740c2c14000c0312840050b420b00480300400040c200040304000c00002401f807180d03c1003a0041542800c5111401a20340c0304000d1440d80554505000c814080d0b4440a00202d1a5594403c0d0303a022030f16801c16940710310f0302d0301400c8041240c00d4000120780c2007030480119950b4404c0c07000d0110743d00f541e0b10a000f80080f45100813452649071510b0003c540f00340480c44000001c54020880b502e80080044d000c82201e134000320038003a07459240b240301c0e00c0d48000c4aa101340125804085504036600e040001c0800b08243c4655503000410001d24002d80c80041c002e03103202007200d21207941d4a84c01c01c415a0300845004000c030429100b107000152 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 266619262 1250 266618012 266618057
    0x9140d2a080a091d0106030b01030e0631060506040c02070303020613110a0902070311011517070306020c06010f050301090201050409020c0c040e0102090906040b011e140403150f0903 80
    0x2c6151921843c066034030720900300d0780e080390b800307035200d240e0700d00d004101c0290140f181881e04a801c4c02e00780011207016455a40350600140b100b031041e40d0016a8038645030300214400d00c0c80c8280e0707401178078441d400d003410700c01410125a114001c2c0d281100341001c0300d0002602c4030850342e14ae0700415260340e8035810100d40d9509170004883c0c001c0b00399461402e0340d48885100000d0140c1f80b50041e02d0b00090b0034002c0c900e084500d9489071592501000402010100c81e2407001d451b0790300f4010540080240f24a03150220580c009810785201003070707400ea40c1c500415080d048881000d1152207a41d01c03407041608071590303444001d0203c3e500708410020a00141c01800c00e84000200b650902110712020800b51006420300003601e9500085a05c00c6c1d191142010342c00207000d942c1004180120700019251080c0d41c182c00d030000789038a2200b03540078450707146a2000104150b2850710340c0e5591074412600e1640c600d941d00c61609180c01c0c0e007000c0110340b06580707007250507540329000090041d01005054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 266620512 1250 266619262 266619277
    0x50906092809030c0302061305030a050a050f041d010b1912020c1006180902030c0103020702030304080123010803090a03021504091e11030108060a0203070309140d2a08 74
    0x201100c1401401c018a4451194a14002d0720b48204d5900702e0b160081c24254020441c40400004529500c0428000030589015074010705010340d6540c100403041d03515000d0412030707208101000070040780011402c84c540ea03144584250300051070341c1783c154050280c0035410107040c00010903081302040d14441c0d01051081d002c014801032a20440a03e01400c000e4840440c2e0300154440c1d004200321005021441c0814851321000c00071481180d0001743c59180d81c0c06070310b04141c0c01048007000d642d418000c580050071140002c101c1808200e02500180c0c0300740320225110280100005030300d40012044446a40005122021982c25942000070320f01982d42c00c1d05103181d0a11012582480511803025a4048a044018840d10864a1009991140381c3e2010303244018030040000140000c1ca81e6009900001c1c0940c89640e0107104030001d0051410182414108514441e4460408100700031195410f030781e0508402c0039001d1041a240a000121070118030b040900c4000c21900b002400c0701c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 266621762 1250 266620512 266620561
    0xd06080a120c030e011d1201050906070201111207030e030d05060906040209011b06061e05030709020705030d050c070206030f04140106060c0204020c0106080303100f090b0619020a0b0705070302060105090609 91
    0x40d824140807030190b02445041e07c6d1140e40d58010b0122401c0c0c100003560b4040c04070701c02130289200c4513907254540d003d00301031680e5040c0500c0101b907580707001c0d03003003c4020842e4030b04407034803243c1c0c50704003001030a01500c0a40c000d40121001c54102d0406000715061214103071590106000c221012105200b8204c0b802c1d00c0940d9100d00105903240f180e01c030120020030410200501701e080804040c14009283c0c0a22121031041007103500069011040c0d400e4041c0d9008005429510001034500d240b14200d0020b500c01c070000200b2022040d41d041c194081e0740580d2402060341841c81e902400c80e07480780100c1000c17402c40c0c40e806c80103240940060020b031361090004554036a842c8829441d64100380c4020001d200220341c18040e407021005101e0040512407400e0000000c0240031030058803806242c906484044100045a01c4c002c005d110840c41c3e000c2e000000b0740c03900000c0104107800c00d54088005004120000955150100b4094051300008200c1c111640729034403101452b510132582c4028 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 266623012 1250 266621762 266621807
    0x609040213020a02240f0f090a050706050a03050f040804090b1f02060402150f03010605090f130e0d03091106090a08030a03141303090b030a020d06080a120c030e01 72
    0x24601c00e90014108408013030b0020a440340c21000001640340c1c401c0240107140300201c04025085c1d10644e8000e401070b1203200b8031002500c4181c0d00d107003815518030003d06148a2001d00007102e507442030090020341d400745d8081240b600c9032900700045410039036000d03200d1801031106001e06020b41c3e207c0400b11400424a1143d1918003c2e40e8900c50000300c015030243c2c00c60410041581041042b441c02010f8a9802902d4030064840d95496400117004020400402040480068a80c504246c200768001003031001c441c10701ea0106c1c00070f4024000781200e18000d6031a000c25250080c020040c41c01c0d0b20040d22001c00304504123000140d005003040c558400300e1610005404181400101003041d40c5940210340441c80e540c0408ca004d40c0501806100b1040c0100d1001107984011908180c5045140d030645e80d4440c80341c00c1001c0c0c019005200810b070300e000e000240b00d00c400545c2010300d0b88510003610b000300024005982200111a010b000b040c02e400c8915100d6215074031002d01c00b0760300b030305204 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 266624262 1250 266623012 266623039
    0x160801050f010e040e0307060b0901060906120905010e0a050c0a0e04140a020a0b0703081e040605100b0c0106050406060e06070b04020a0905040f030212040b0703030b03030c0102070b1006090e06090402 88
    0x70280e031485002e540c3c142d0000547c401c18483d00b40203440094100b581c6002e00c551500c1d40051982803035108000400c0499040d400214005401c07213498250881d00030f200c60490300c0c0216848204099044640c0e120b03119203004030b03003441d49003c1700f112041c0c00700c8016079507151901d40045c3c0d0014030200003809603101840c0141d407484851405003103d50070303080c0c85006618002e05030a001419040c1a40039038148803001d0112480c03180c0d40f00d9130000c000301d415181c0101d441d000c40b03115000003c0a80c7c000c5140c40c51201e05600000031100129030610031950b803030f0800d640303038000d041c0c3c0607410030010800341012a07060020150098400303070100303894036a0707100e400c022244c0944013211290170b003074240300c1455410007000400c4018610014900791070020320b80580c0c811008000e0500d5119079066025990a00640f06a860903000039542e40d14149015804040d0859840a404100e801c011030500c0c4100c0249050350750324161580951500b0301041841e0380018030880e8000480320650 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 266625512 1250 266624262 266624269
    0x18060503010509060411220b0406051012060e01050307050d030e0604060c02040e0c011b0c0302060c010507090b0f0a030f150806160206090606010f2312160801050f010e 74
    0x38854100f00300a8005424030303180c61207141c0d16610640744103e141722140720454000c00b1402a02c1c600c01306000441c941e0302e4001c1805400c8660040368031006007002d0030b00301600010b2184d40c00c0c5040c8002c214041d2502201d500d010780a000e00d07034040d40101002c3c0028200741180f0500303903000717061100d480540301c2d001580c0d0b90301980181000800c01c02c031280440c01c01b1f010300485171281d030018052074100e50300001d0000300a40960800c1c500048180010b02040780040c1e00a0b58015000715690024110707403034080c0c5400d58900d400240d90a0000a01506140c159201d8200c4201c40c1481c004152504401900000c4082c07165643d443c50014002c40110b910a4002e262000203040b25287c0701c207010240f042c000d540801590400340c10000c5500000c10042c6d44200c007403c084c980c3c0050b4810031500c010014040303a5903e0f0203c00200210712101e0003801124041000400035a0341d051480b10b84205141180001715500d84c0062080e0700c5d0561078603000c1841031400c014100300c0000003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 266626762 1250 266625512 266625521
    0x15041802041d040b0a0515030f16050d0809010f120c020a0201080601030c05070b04141f05070516060b0609041404020306061504270c0e0a050301151806050301 70
    0x2614111540080c0410100150038041c0c0700b9240c03544200c80080c540354031241440100100f0304110701e503480c2d00042d00300c1803481180c021418042d04451007405100c0710705039248074581d02c840307203006001c9000030329142130481540080e81c40223034a41040407910040d207004e041c4070a814107100a200642181e0480d0348590030007443c0e10340c02031101014a000140c070f0480040c04607410181403010300a9031981100c00c0712802640000058001c1e581c50070b00540049000d84412224050b5500051032081013481c07101c140c055003e400c02080d240c1e020165080c2c801c2d131412032a4031150f1001e96001c143d079980104070520015000c54501040d0100203422689082d02600010107808280002c0d410100400d0303902c10415504038403080489503a43c513082c040ea10810800c2c05089195190b04100d840e100020a21605001d02c180304214a015191035081c0007070300d005d00c403a1000040c07203181c1400350300f5000040c1c8414480890500149800c1001c60103980c00100761039007000940340d20240718 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 266628012 1250 266626762 266626799
    0xc120702032812020901090501140408010612060501080601030209070e0120010911040509120a020a0204090c05030d030c0f03110c03030f070906020a21110706080109180f021504 78
    0x2100c11800602e5640a4240341001c603600300b900c0d1040c003242d03d080e60000d9085090b03446c01d081c200c41d0555114030059141c45141c100c81004c0d402c0c00c10004c1c03005d0010f0f40261a492140d0010321a0380e032210b050550312142444040e5100c0c6030030707003c100a180110380c2d90010700010300d054071030604034004004800081052001c51a9507401480313050004030044c405000c0701c101c4040c0910309151124507540d851038040390313080c0180060b807020640c1c001c111000105502900500c680680c1c1e05040d131880b0680e10405001c0d00800224a00083c401c3c030540e40e07103035000c1d282c4844c8030344006c1c02100140340c0c811200800210407c58142119010130285100d03402100c4c0241d031615090f10028a010f83c640c1c084400e42d4059520500002c080480c1568081c840404201d20082c181c0310458a52010f000e00c04043e01035803002040c0150b00140182c1620310b113580610003898850310302c005416521502514002c44031244100514014003008003c501261010b828662155803403c170013440ca01d0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 266629262 1250 266628012 266628067
    0xc070b0c0c0706020c03070528080718021608030c0405180108010e0f060c03060406031217130203060406050c070209090105090c0d030206130503220317030c12070203 73
    0x7100c1100c007600300048400703449148058408280d419003c20703580c40590280f81d20034444084124080803541e43e0b0004d01c912101082d503022955080c1c2142c4035402805500c05449500d0080c8110700d00d180211020510340e1000d4403c1c403102074460300c08503000500610301240c01000b0020305580d8001581d901c120800d900c26565500d00301e8a00d00716440c00d481c0b4840c5400a10030303036521140124100b0341c00b0f10141600c0d662940c902e400540100240d4100810121404a0842a982d40250042030780380002e2419103550700c54503245101d9040d1983c00940c16031100001400003550354000681006a411145051101550018101440403140c54005a554400300480070004101c156440b142c01c0d03030400440c95403501c009440d440d00a00010f01160a48500c0c0700b041002c10032500d401054140369203400e400c407084020110710503c0705880134010712107a198041e0704401224020200e21101c3c620701004120364071490354000f400b64065004c14849540d000110030500c9000d01c607501c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 266630512 1250 266629262 266629267
    0xc0c1a04050405060f010225150203030403031a030712020f040203041a130804050910090f0204050301050903040e0610050d0504060209130515011b0c12021309020d0b0c070b0c 77
    0x25041c0b00449400814252140d2200c050820a50b6000b2078400010081d40045000303501c0d80c3c00046956050030b1f40321280c03d01802034500300d8244d010002e540641d2003507070144450801600c0c0c040540703558034542a03140d0010030b000c002010100d50400500b0348094007d5001510f410002022600115401e8514865080201002c181600c2c0c41c95440501903c091070b407403c03075880d0710646026501407a0301856050300415800340c41020300000400c4c00400030301c018201000188065042446264042c0d8208001b089003410040141c4040c0d0312000d501600300d03035030035080221015022a4032401d0100c02c000707200300e40c0218080e00c1c1c4128014800075a0706c2103070009000798280b4003c80e11507003520384018091400d00039401c6c505452024600861380c035406d103064400300b02b00d00f00002c0c505000d0880002e282e0102d15100c03a1414000c594401e03e01d01c00700d600605461000100075030050380c1e01400c1c0b0001d07140605854108103110f4019040c8851959811080c40043d1111511148003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 266631762 1250 266630512 266630519
    0x20f01050c1905030714030403030209090a02090f1c060209010c06020a091404050609011415070506010e0705030c0d18080703030b0f0f0a120602090a0e0405100c02030a0c0c1a04 78
    0x141c07410801070400d149025480e5140c90b800c0200040d440c5211b40b140342e83c0c004003190525100340c060b600003181c000c05058090a18aa00200035880000018040d80c201c00d1402c1d514500b00f004055180f40300c4880011000303495440030700a50140949070f06126520b8440301c0403a0340c505c05848d482d0001c0d100c0307041803400d08924080c0c080c50800054031403810a270422004da01c41046441c115241d10840c082c503d02c500e00003410302d040c059581701d4011303000300c0c5c1c2c803003480000280581203031400540d08c0850f131610403040f12148011140708135224810031484082031529485540e03403082c28800c0350070048072560380c01081d03071002d94182c00094403496500061320706203080010812003281e02290b540e45000115180009038482c259181c40a00c0c10700c0140035090b01100c00e510302c020f18605006450b00f404451011060300d0540742c1e4400e1b0702c0c0b030000c4568948107940034017407590011820250462021103030303020341c050111110b05001c0800181c481c21055506080c0c00c81c017800c6520b4506 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 266633012 1250 266631762 266631787
    0x9120801061b020f13060b070503180f0d0b040c030602030a05060901061b060203060a09062706030f081317100e12040b1822140106020616020f01050c 66
    0x52001100c1200800214003200590392000f0240340404141c0d18061844c20410440e030041c2915441f5400144000811b41e04000000c0f00802e04000b055100c00520607030724040c020001c440d01c1100741c01c0110003d20300003043e200b03500b00341d001c0d124402d10900c082c0c507640c550059030000e640d0214090f46807000d000091603d54405809041c452038000d030402c2000301c0040580070590b80103481940d0000104905881c0c00410101611044600380152982d410f20303904007a04004922035410081c510b0f40e0442100d901035103041b42c1d0404591004403015465205040d446131030003041d0050040300c00552203c01c0d11980310305113543d0010b400c1103090241140199084100f000141d074000c00c008c0c807d05655081035030149c40e0740200040d12520465001030040c4900780c1442ea02020030b4041661850316024220013040700c084013400601203c04c9016040c0b030003030142201682018001400c07601080004501640403481200c0205007106501421030314241c030b40024032000014084400350303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 266634262 1250 266633012 266633027
    0x12d1809030f080702030d0c1107120c0e04020a06051803060103050705190e070507140708010203040204060506071a0a240602070f08060408072d14031206040f0912080106 75
    0x180b241c10f0000d454541200c0094aa200301105891015641c05410465038400c0c0784007400e01c031401040303a40d040e0b00d503031000c100100c01000c221404441650003180c0040030301082030280354041c2440301d0755420018180d034103030410303908804100c4104d04c0c040d15954040200b60700950281000e00607203400d1000b07005400194061a01c02001002402c005849480e490b107075211041e842d006031914281d14049801c0000c0d40003844081c030410303902103451035040d4020b502035442101c2c20840c041ea03410600010340034091001e81002c0b01d4a0f0107600e260801e0740113690248202c0b00008003d5410340c00710401d0840c01c00d55050000342503405101e03980e01000007001403c044d08000f4850781c503022070390f561484000c00041c86960041021002c00c280101d02d46001e05542d610101000d160709407160031030ba00030f01c0c03d54100381c140208089504021080700c003651220099544195203910510002d040801940c0c4141a55806814040798500d151242d00b094a50b445004651402ea001005c16 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 266635512 1250 266634262 266634287
    0x290f0102010b06030109051806150a06030e060f1017100b040e0703082b1505010e010e090402030703081923160c080111040504050f012d180903 63
    0x41e807400c148207000b65906800d5a04480396030a011079aa503e087c0019000c00310405880150301c80e010a12806d10400e043e0040d9400007039036440c10603552031a080301550381c80c0e4205820741c0c2241e408200072005c00c10f400759100c110a0000420680e03125100460351401e00c011400b15040000c0c00304038500c0c18001c1d5036010340c044405010080309000311036168045484000c0c001c5400140100c02180c2e0702010004404160a1858106c03280380030a0018011461580380700d0310480314003148035805100c02a6420340180d40e2502400b1f00f20040c441904d0000c5d0080c0c0e030511030a040000064101c40041002103102d10500d41c640c0508080a40078003d401c0c00c000c4920803522416001702c070400181d500805240111b40400c64203800c00600c0c003641c54200c5807295080c011040f00361110240180300329801603900300507035550003078540107404083c0a185070f190b01c200c000c411164524050104100da8280c00e600e06aaa036490350f400600500480a10642e11035148406040d0040221401c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 266636762 1250 266635512 266635517
    0x80708150603280204020d0603030f0f020c12070b18090f01060c020d03030e0a03110d050310140a09090c05040c0c030e010809120c0a0506060604031e06290f01 70
    0x10304100000a480f0288412050202c1c0d40c000c001c0d450a51680000c2c0e00540d801910440d5211003030084040a40414002503001c20106a180c00285110b8001a1203940945d805040e0f0102c1100c1044030004600400800a214542001c40c0d85c0003210003c00c140003072a0001d84410140c50103025601000501511040d44180c1c010000303d6040700031075412070b50445030400e5111151030207070b00074217030407224410070310400c40355034101504624010302c1c0692070011100101010f030400c5440348000c8661001ca407000c203904100c010b0a03d8200007866100074900b40c0e030a610f8042010403201c0010040c1c0c0c030703440400310400084c1090f01c1044070100680c980029411540c0c0c40181070380422900650412008800003031090301305010100355544156030036a92203020008241c3e4640a01b001030710f00e0701810021420500c1d00d40f046074100d0381d00c1144842c0e500351006910409051b00081039414039143c01603510440312900c450404c244d03048444074958000ca906200c3d0748150394101d81e05 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 266638012 1250 266636762 266636803
    0xa02011506050403060f020418060e3105150a0218010504260c03030a05181807140f0307120b1c060509010207020612010e0708040336080708 62
    0x1d050380c80b40403a000c2da504050003003021840c280c400c2d0024802c0754400100c00c041082c940c1020b50450700304000302c5100c48103680c443c1d11070440000701c000c1205503c2c004e80c8001028004218091070003c03040ba80140c0541d40d02c000f110a5411810384100e4201b1038090380080c0c03c8128506441900801b004e00b0710b00701e03003441d05200d860a211940e42442c0741800c266486201041d0108010722000242c02906503a2035542a4802030f11035040841898907460120100908a003031410f0a0380c61203428103191081d079203440780151085c83c036028801d40008020020070445261803002107004102030742c0e98100403900c02400300101c45119090503c21b0702640550304004120b403810f01140368011000040c46e0711550301280c024822010b0007500000e010640d801007840016940741212010001c10b1403698801100325101c12040724010003007028803200303018a0340c0c04004a810140300003210380d40b00110035050803004400350303c101d40c1070784050410b0003484810700c46070f8800a0095079540 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 266639262 1250 266638012 266638019
    0x2030c0301050603040c090c0c03030f090506010e040f2108090616110304030606030602040e15210a0b0a020318010209030d0c0c0b0f030717060f01180e0c0a020115 72
    0x816110601c500e900c50580032010a082c89003214000340240016041044036104c1d21001404240850303c1c1540400e14017860610840b03298000e108003194450003410071607003032a03c0440704040140040e0b4011042144500010344203040b81c3c10880b45107e0141a0030b00e04060040c801003004090001d02c1e0132803030920107143c11002ea01c202e44590303400c00c00b204060f504042491400780781e0000d0300070343c180b2000009200300303607004000356614440b00c48030550300c1c40080da00200c4040501d82d0418402d1500100c0d0b990021007010907021054142d0756074041c1d5403218901c1101c2621845c0d80b0030381c00010311910b44102248a0717404140c03c0004e508103042a0006900d48051004400900c00c00304110703010401a003e27441c015003206642c10ba01c400190000c0369298100304d4104010440010501c1c0102f40f09040e540e06c00c04000300341d00e202c00000c400441740ba031403100c001e00e0b610380c2d401c0000c0354900c1d01c00926480b544d005803c6030748a00c10050000c0c00d40d171001c0d500450101d40148c050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 266640512 1250 266639262 266639281
    0x1101020a0b160c0c090203060f01170c070f0807140705040b011e0512010602010c120911130605030a06050417030f040602030c0904090302060a060b1615230403120203 73
    0x269004042c401001c0351408600020f0750103129010005002c4101c81d1004a2030146590185000d04030696000024100074001901c2c0c0000c0d419500600d10b1240f00000c0c0845034500007082d095105580256000140c1e58510241e030704500d008540c0d42031600c43d03000c0ca140d0f0030070001006100c00c44081c4200d06040b400038100188a0225600c03021070000740c548980e000310111558040400c1403840c084d82c0d40e0f4402402040b62001000c001452100d91031294103484c00b030703011125049104c1c1441a580340040101c440394032100030901540f42c1c82c0000b1071b941c0910081440e0b5000b04004103007031909280c01c07080c003111481e01c541c01200030300038401b8180b4440c0e00c0550055010500680d25260540c415001d4010b451b040d952090501040174101580428064001c0c50b01030402d21202d600c800d80944207000b00903c0c40d070003e0540c841c900c0490100c00e00e8131076181007200002045509a005107045190440b008044068100c0c148410035034410f0764240c00d02f4145208509605185c3c4c41c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 266641762 1250 266640512 266640533
    0x3050c0906180d0b0103050a0b0a1e090201020c0a301a0907050a030309081b1003090303020d09111002060601080126070e0105040b0607022404080d05071101020a 71
    0x298100d0100c803014850382c0741c03281260b6070b2920742c01140e40350b43e039a901d01e40240d88054008048a040c4811408204460580e016240f418110010018108980d9001c0500180001c49040c1e0451080341a401401d8550030544009011040b052520070350342c2214015000d100d2060040310f603007202e46130700301103040074038941e480c2c00141b801012144c0308e00c0c55187c500009034000507031180001c403001040503001550300c42112800b1050711040090f40040851240810404680102d1556011104030303101c0d60104110700d01c6804c0040c2050385000b2020100d07481d2420440340b42c07080240d0400946403664280c0c17850001072000381250300e094000200b44240c1846222038032420b500c183c400c8025600f03515000c6821a400300c590712030742c1d2505031701104828131a20f4051450100d0300001c83c1440e5048401176070300581401204a040b08600d000301008010310b044100044c4808666540240814600d82d400346ea207440d210002c0f0304090700580d040c1c01e800c0e07055600082d05840050000c40b40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 266643012 1250 266641762 266641777
    0x12010f0c0e040c2f0f0d02030306090609060102060105150c0102030a020d0612031407030908010c0801030314040302031b010e27070503150f0609031519090308160e060c0d03050c0906 80
    0x2e16044e4003034004480c614100001d42c50b40e90501400f9400c840d070f1640000a94818242101ca002041c0c642000b48524808142c940d180140c0207000148090301b00079a1960010100d149032070b14065500c2011406c98006940003600e4940000b881c0012a1040c040d82c0094170300c0c0c914200f1078031810b076005031114070b80c900721245014002c2185800e244c002d1800100801c00074000740051004110001c009190901084021070f80540c1901c0e00c42d5550410b607002e0742c4d40a0700514100084281211070f4640b2813070664100080d04410300c0c040d440741c010070400f070404003409401c1c60b8201e080f0f524441400425070000c2200a004010f400c184049581c101100162110711541c90b968000c43c082e0b120340b0482980500c1880360302601c400c0f845002511940f5491000c1340108501134103841503e640e0000500004c1c201d00101e00004451a1f1800350340d84107007484801e40079988041754407500000c4045a81c0c0d00200501c205003034140c0116a80200d03007200d21032401c2d003041c0004110740120380 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 266644262 1250 266643012 266643077
    0x60109060b040311190b0316020601080a1e120906020606010203090d030503090705040501120b0603030a0906112109130c02120d0b031b100305100512010f0c0e040c 72
    0x10101c11050b105d0704060450b048007620941e01440d240c2e2002001e584c000d44410304600b440d41c501d400010b10105045040e560094094044103034070b5190800400c540b4001c9201c803082e1484107a001807501c13080784904004036182c42500d03074500304003c0e00b040c3c0010401419501300b080718540b40d071340781c2d40300035201d65050501d29280d8490881c81450180240c014641044c5050300104038034540a420140d254410010b1011960301d4405060b01c03070003030b64140c2c030101b041c50105200b203600882c8807010000705102141d10074a41c07070720740b140341005030075540c034210000180c0c0d00c7c06420b05900b19051a035004c10144035402400100a5a80101e140203411003407011400002c854016004032030010001001c075107501c003034582c0c0c4c0509280ea40c804c1520078070840508510290007401007504c511103941448010614010500402c55061001c9407240d55a030028034140b040d046c1b00e1303580310403c0b95407100480d4428100f0701c070841301c1500021050051091800c544041340c012004854400308 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 266645512 1250 266644262 266644283
    0x31d06101a090409140d17060909031603030b010e09060d12050708192003030403120e0d090503070614090f0411030a020a18060c0b04051009030c05060109060b0403 72
    0x10600c1904034060900626400f604100700e0f002400070400581c5203440c1040300ba208800c20800080d40c10200c3c607880b07112550500c8001826500d0403c032041d0740000542c0a4902d01004020300f800c088007000c0d8114040395440103a9506941e000c02c0058001c207042d250b0740c80c070341418000150032584000c0c00a0451100a0070142d01610810a480249900000759602d80e12810070001c6090301451920000501580343c6005408440c03a81c1600c005c800c40180d8a552103d8804076540c4400c1c418070710310181c03203940c41c0c0108202013009424041c00c9540b1051854202000c05040900c590302c8002001b109428001c5400d44650481c2c80070b440c122030103a000c02e03c1d80040b0303014001d200350008400002000b0004e00d44030715002407601c40103d503610409005090b0041d4601c8540c0c0c02142c2c00101494030440029001c1c4005070f81003806030080b01c440a1754370502c030f02502c1034168124005420320f50000208041001100d01509440ca818090301d410500440418040c40c4809440410070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 266646762 1250 266645512 266645549
    0xc02090f0a061a040e100b04170c1f121514180403110f0307030504060c0c09060f080105100503061303030603060f051801060503030f070c050907031d0610 68
    0x59601c094010309280da09041c3c0ea1000f0168041d6030b0300184654500b4081c41d100044c842c03200d00700724806881c0c442c1041810035081801e118541110706412444074030410303040d8003040da150400300c01e41c0ca00d08103130603410b0074000000404981c995070b80c0313a04160410034009100c5610300e0a0005980ca400e15100c0d03500300d0140003800207289507504103900b0442e4028407081c5079105544c10003009444d0211190451440da54580c0d0784568a405400100d09103c203200c03062045640d410014010a03880b41c02c10385580e01c00c41141c1e441d078801d020524080800304100746080c0a41c0781d00080041c07803e080706e841c01001c603880310001005044820b0401400700d08140c001c0c1c1c80f41002d10707009001001120311140d200c00081c0800d640c0e0501068408803600b40000050058600f03503000034024604000142c04080920340264604558018080d20080f445460f4481c003e131250303500355030109120040c4005095141907038002d01c601908164200300c071681c090160b0b0703800c0301d81900d10748180561 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 266648012 1250 266646762 266646781
    0xe0f010509060d0621031d040f060902031501140703030c020f0604060b1201150b0c010b091603110403030207050105090604030f0c2402100207030306050a0b040e06010c02090f 77
    0x5007500180e4040000302c0ea0986070b07001c603800802070b01c10f84811155030701060414800c01110350712004000030340090000240e104051004480050060b0000c501c440a162003c801c0c0d8580c0d400c0074844030f60100c00c1101c0c0000601103081595400c3c00e002c00c140151042d400000d01c00c441000e01810b884080001a01e4801c020090f8aa01e501c0c050b030303d080c200b034034010b0b01412650000310b2041c1580c00281ca405030062007040309440207035241c840380c5451315104503069002510241c0d415540c88032031501c5901c40140d000e2103188803006400c1401e1103000080d044851032008014903100500082c40003c2e00025001c0607100709007022a1541c8070f4000003078581c880c0d40c00082c080c0f0000d180050401c980d41e8180c0040c3c8000e040482410312070b013110389070081c0b02035040400503480109602051204d0703034000d00030756010749000700d03219495502090b41c0e848954401010716500203000c200101c06500602d82021091070301001d0b541d281c1d000940d0b0404094217907682d9405e0000811400d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 266649262 1250 266648012 266648017
    0x80409110f0d1a060901050a03090320030409050c0c060103031817010e0c03010203090a0f0204110a26040209070302180927240a0b0a0b090f030705010e0f0105 70
    0x804031801c15618080741c4030440c054001c404034610f40303a040f0f0160b07001d6032416505072445440181d4915080502d241000c41c09800071060030340c24011000a00380860031049004a48051400d00071aa1a440c0c14a000101c80004041c510441e00500048454020100d40c203811241c040c0340c0440311a1035240040c504101e80c9e806000ca914182d82d4030b4a040354190420702400b524a81501e154000240c141401c5c0c2c8021294400c0d180c000003001030001d0303030b1030303022900150001d44002101d01108051100a90002802d5004203100d14144aa507009188100c00344048a120304456814594049940c480c800b4042d18281500400c042d020140319100002130450700a00280d03032414000d001f043c03484052551031900381028080d1007106800040c0e4040c0c075012070a164442c038020309003460643c89001d01f034001d81780d81300c20030164556032320342c040e070080c00200140c59960f00410040045003040c03102420700903007203c0700820503a03800086d4120601000d5410120250075100100e4051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 266650512 1250 266649262 266649277
    0x150f0a0f1e150801091a060f0c0f01060303230717070609060507050901030f0203010506030f13140607121b0f0c050a201e0409020a030203060a050f0a060308040911 72
    0x2c1902c0b01d92090140d40006018100c075102c2404010008030b00c01c0c202c088240580d406030b0445800c1001c009401c0c422001415510990025100f88651a000d05401c2d20090381c0150001810701e6a00c0200010180110340c00301200418a450400a0798404400c2001c442c0c818900000208640c2c080c48150341125011561240c400c04c0b040c42c204001030f1040d0002e60410307000030700c1c1916108480820344216810303610000c0c8590300b582e60320010300c00c0c0000010714054240710304e1a00c03c800039003111a090144205d00300508054503100750300a0a0000031441645070a082142c92000218010303626a070740c1d49246042c01903440041401d59103900146001440c6100c0c401110061142c5010083c910701c20740d0036a800703e000003004002050020020620980307503c50002030070380c60070b6030010612a101174145a10b1681d00d0b000242000701c00c4420040709912003042020081c01000c0340390380454204020040303075046484800d418051805908165591600300005180795a0141d9220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 266651762 1250 266650512 266650529
    0x303030903050c2b02070e0606070609020d0b061905180a1b020a1109070203040b210c0307020c030f0c06030a0f020a020d0207080309090408090a0e150f0a0f1e 70
    0x50555403499034614131020513100190685030121014960710100b03c4008503054000145900e8441408200131580085000c450321642c030560700c030041e201c10500280083c01415108242e1604105102004011068644001f10118828001513032180121010000390340140e450782e540e040c00440c02080c0380f5084000341c0c0130422041d40e016500103440c500c6144600c46c510070303c03045031080c0a050307001038030f481000d600305020034000c851558000d040c4d040032106041040719041030b684074008209441103002d5290020812090580411010206190540041c100003e43d5550180c035050710300e8809115070070000c08075681141d10b41164050084480c821592519901c1e006555511000e20704000f60141d400300040c0c0182c0070040e84c0b4100d074003034040e80c845e40d01d0741d0720843d10794094200f40b0b511440c100004100c032019204c40760310407008941c0781080c00031001d04000468060b001602e1269050260500080d0341c045080c81c200c40c0d452504c00c24480e0741c100e00b9084d0362441c0d04094030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 266653012 1250 266651762 266651773
    0xb150301111909080303010b030c130b0f040e10030b0a0b010c3008010e06040f021201030602180a120b09070e09100609150608070306050604151403040c0303030903050c 74
    0x2102d11200b040b85200300d2064071110211681c50102e540c43e80024401d90410b04000d2000030a60401c00c2d00510800e01040000025140c4403900402940c0240300c0204001c0c1c400b00701401016020b869942d0481d603107840140039a451940c0b800c44c55900106400000d0341c6840030040f40741d0040c81c94008040d0b0100310007180f00312026442140128054828491400000002501501402030941601c0321322803000e01da540e0316420b01019004210f5128900b6a00b0000c54000140c0040d805002c1d600c1764038050382e1751004090002c5000c11400b03140b8410041071104000b01d580307605040148039400224500d181e52002c21a03030515145502c00100740c00503a04025102c4070104018000c660703048000c000017903d41968004a408040c0c800410300050002070010a000d1101940c0c00007030b07880e004c501c45071150049103668010394011012603484584250070b080d00200302100400761148500d0862400e62582400076429120141c10b01d0b1b0ba40b02d000c000d15105104440100030382008649 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 266654262 1250 266653012 266653027
    0x20c01090b06030d0f0f081305010e100f020405010e090a0908030405010c02061605030f090c030a050f0106270b04020405060a020307020a290f040305010e0304030501050f040b15030111 81
    0x1c0300c4210032076915209010304c0e16207030421030082c2d031510400d80301c0c0d6903148001501a1015250801c000c0c080344007800c1c090310594001482405078040c3d01e4080c1000d401c07102c8126038807400b1b41c0c00780e03101c0b0030911340180428445c90360b0001c010890200d041325000c1158507480f281ca0010080801c02808990000003003105000054211902d1700003039900300e07a95596400c450f407005045031034102e0001a01040401e0401d03030b4004689030080d2641007500e01c800060390004c5d1a1441105003150b43d600444000c055020081c41008014a071641400001c1130a038844540308403451045032400756983d00b002102500e403941138074003901c1d020b072546594140682e0040c0d940e0f0400d0700220f20403200385201040840155100241d000c110000c500c212030540741d102102900546a03000089d54203100c0000481c1003405910f522514401c05545d4450542c00e141d802e45100808101c003915007041030200107551404500e81c02105040310b1050103031500006070141140302c4030031090708404690301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 266655512 1250 266654262 266654273
    0x6120307080a1d0a05041d06150301050c0301050307051011011103090105360a080d0606110a050c1507061e0f090b0f04020a030b010303090905011202090c0904020c0109 74
    0x9007070030140c03600c600140c243c5000030310a1250103038030300a82080d856001048a801c09810200c4440418200155142c00e0202120304d00340007202c00d4010b940e540700c1031500070f04080c070409403c90048802d2341d2440d0b04000110f5503aa505204482c05070300c03401403d40c03a02c4c1c4155180d0150b220701000030b01038201501c2e403400b1540c1058500b98040d500e014003241c01440050304082a5903040d180741100341c191030b031600c180014020189a00d50140201d004001800b080081c0051540d01900003040d80c24400f00030300a1b100e200400841d680700d0302d811408150001010380394030700e0455184c1c1d44e103264800e01c03c505020b01d03080148420300340040d040c3c103c424404103645138072480c0410401101d503203005130142d40d113422001c0c010300d0404021a81200e86608072076407060024200090316070342c80c2d645030b2070720000740e100b40e00107108800d081c004954a40143d6004100074020440c1641c80f83d00001c414600241212020140000b00c4581c1a00c9680540307020750700e000020071500003e410030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 266656762 1250 266655512 266655517
    0x1501060c03110a1208090a050f0105070314010b031b0f03070f030c050403080712050417150105010e060d051801060311041d07030b0703110a020a0b1602030a05030612030708 76
    0x71804036000c0d5240c2c2803220030000742803403a1500700a50300d01c5400440000e91345290040c3c201c0e1128000c03064100082002003141c600e10000c182c0001406141c021002421110011400140c401400c001000300c01611015683c000c24411481c00540c1c0c1c50150702d541c02e00c00c010000c210110301004010006030130001c1b5402c0035441d518107111000c221401103455100b140030042180c4018883c0300b0100300c0c0403411400350175590511503d010f1300da09401d450f003c1c84040380c94450307100c944134061100341551554010482820844201d008401c001801800b80002d0b82c5440e541e22000502c003105040034003c1c00b451040c00030004503482c0c1c1480f840c44140c44010500440c21b05a003690245100302c1540e08608466000c1c019590441c3d6801c52400d9028064104168880010120618086004003016074894004161840c0e007071804024103140180743c900354120300d08001e09101d8000c8121030401c10300785003540d41ca0b0340316000030380300d4100900c400300039100c0400c07002c0800004800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 266658012 1250 266656762 266656787
    0x807060b0604090c021e0f280804030819030c05090f030c130905070509070905130902040f0506031b0f010e030a06050103050d020f0109150f0b03010504050d031a100809150106 77
    0xf03040c50746401d40c540741d0f947c5d06d40c0d51901e01c0d954130408035182c03480101c00720074288001c0306120303150060340380c0c0312084e290b0410f8105640b403030800607400bc2c05505613a00e401c96000e0a003020b004007806500003074001e008541d64140221803a98000c201d999080c0400002d801c8010300300c9030f020240e0a20440284034010044401e4420344a000c5507030318100d44032030b200704250365824403c142460103205c1c164281e541c2d0449010707240d580880041e0f956020310b80c0706609100700000e00303140c90b104040c80d1034100c200180544c40c010b41c1d51401510340c00d04807400740e8401c0c2800700070511f03d40003091503c589040040c001a18040001c410014003040451a0700600d07400ca402420356020b4943c02c0300c290140090880e4048186031f07508406603041800c10401a04000881000c1c1da8007203401d4600443e0700300c0d681d070003001442000a40501c22241030810b0f16021802072a800e4020409500c60200241c00348404640010b012074001c0000c024011264006030700c8a50b555000900080301005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 266659262 1250 266658012 266658043
    0x3030d020304111011190b010501030c09121203050f040213020327010b0a06020303070c0308061f0c06050a11030109050408070c031103240a09020319050714030a0807060b0604090c02 80
    0x4228806c40e402000ca9a0091350401c0c0460040c0e460000190700520302207a401d07081c041401c8000450081012020b1380c1c1c1c5026500003000c864040200408441006003c045030b15681d5041c0000360300c40c0e104d9015000700c1b91900503981c4c1c0381e50070303089104c01c640c1001c01154072900c4042d03449220103400503084800181c030b0808000e911690183d03201d000803140c2c0c000040c0c004114402017840380140d690821380103000015405024003520500d51244000384001c5005502d0700800c2040d684241a03001d45172803c10402004420490740c1a448180b03d1000140e44400224051116a6044420310b607800321a0b00701840c0c0d41d20b480540030480c0c0101c07521900034a0740d0f0340ac60011803461407005e50890340c518140b5a03122580d40d0000c0240c12800d981601c40d80000c11840c041700700c8045030460180d00100019498024980c0d00d649103010410b00940103180c912000030300c004280c1e141a6030000340411403842100102d860380c0555400034142c14100241201900d0300414040f140342c1103803 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 266660512 1250 266659262 266659273
    0x61802040915030203030a080a0908072004060821040e10030b0c130303211d060a14130611120a0e07030b010b0a0908012d060503030d020304111011 65
    0x11011180220024400650503402c10012000e1f410700c140c00103980039884507800102c1561039110090903420407442100c6071510701c0d80c2240584102840340750200c40c02c417030a000d41360401c5001502c422105501041c40d07050310000130707003440c0303200140c2d0003410b0762408441e801d01d84640e400c01100d60340e100558010700c200c00440c01d1348880c0011034246061030008510420b20f181c1d000c40e000c111450740748404c83c0d940c0280541e40c2c00076002d04010040300d49200013407140020001030900704081d0240383c2c40b070700e00320307108e00341098640c00d0035485500d00c4100c0701d1101c5141000f5000d001c00c900c02d520b484100144079a022407082d18894004c0c1c4200704d00f00000501810990f58818140c00080c1c00072050b440104081401c82004280c010410b2400b400400d0b524000700d0b0a41d150131028120501164200780c1e482480400c04848590b101d080c140103a500d4000800c1d10f83c440c40d02c0130b00341240c000001070240641030400708030860b0003800d00003083c0b002600040c03420f41941e5100d146402007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 266661762 1250 266660512 266660531
    0x90309010809121b0c0d050105150a0e0121061107031209050714150301080a1e080a0e1f02150a06050306010510030605030d0c0501050a05010e06130618020409 70
    0x42c25840c50401075016601d00500d0072880c00045113004d60390030181c0308024680c04c0c0382d191490001849807041c0004a0541000c00e1844640c541e035024050044210202c10041071070031b85031450465414000c4207100502500b9268a00d9a001c0c03005000345080640390340500c41c608009003505402659407980c3c04c02080c40038002d17540445c00c0506036500419081c402e109420140503c1000300030480104a0305d200000c58094100b64489403640d00202c404109000c01440c4d07015400303201481c140710b020041e668107859800703000112010001c0c0488909041d8a0382c00d401d04280c150280c8401a414103464002d40e5031103001066030a685010f004500e411545004400584800801a1031a47c4c241410700000d51a621410302c1015259100001c10780c409220035079101e03090755101c1c014600c43e414000d00b91500a00300e9111903103010300402c0800f00031990580c0020080b100b482c07802d1503001100703019000720b4004a0080c04201002d94424103203600904c00c0700c162180c00d04c0304112 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 266663012 1250 266661762 266661781
    0x60504060203120907180506030f0307050a030305040309030b0411030d0e03070e0606161a060604050904080702031002030702070f0b0f0306220c0f1206180e150903090108 75
    0x2551103280d015a005005a001900e0010541e50f03104144a0455035415641e42c140043c02c4400e80d501010166148103001c1c0900701404800301d0645240021032600d2515907840d40d58054802d80a01019910790124040500c601a007000540e040110001e1500309030070440350038203070f142e401380c0300e44500022140c481c1d000780001804002c0080140c6640b42c40c0882d83e508a00740103058a5001c0004c02c40c0400085105070014450b81c019840d81c2c0190b400700700e41c480c05000103489644a54810701040101c0d80c1c81c054540d6001c0d9020000302c0c0c036000c4500c0800d1030312005103903e88040c0d0001c000c10a0241c2c3c0040c04004131030090481c0d9000300c0e6507001c01c0041c0d100e1035084000d400010000520b1509180384080c41520301d40c0907420081c046071029030119202c168503030000414030a000c07202c055111075010700381c4071100da00b0410240761a41c5207003ca0200c40804004503207507410300640080c20300031901d8001035103500e08024900541020340360b500004042d40400c2054000c60560310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 266664262 1250 266663012 266663017
    0x30b04150b0315160507020307060302040f090902100f020115030506070e010c1e030c0501020d020304061b1e020109060e070906060503090703030e132409020705102c03040305070605 80
    0x45409040003620b1315090290300f04203802c1da4140741402010820840161003c210b054000c1249940c010b884a06200da90003000e0040d84c07110360060705025058026960f003440464001c1300c3e41c01c002d4512007680d98140e014002c2d02c203103410003403010000002480004604a4811101c0c0e5a0b9909a1010400150340c0ca0300b4000e0090084000312200080602d4040e044205d440d00034104459404000d5a61030300360ba010041000300d864000c02400f08104030790207899640001c460b10302111800d0481c008000481c041c1c0f00c40d4402001c2c21030303610818001e41c81151041e82000081c0301caa00001d0303450769548480c0c4a051000d5107000c0700018490711813425603015061000280c0511403941e01c00b01c0741c8241c07070070b041035204043d03001028101201e0b1007107542e223a190004420352103c080054507050300d125448180a2401042520000390b00070580c40c1003560120f00c00114240682003030031703622030311404108010a400103680300290001003d44112071150701120190b07a10340303034101c4030360 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 266665512 1250 266664262 266664283
    0x732010e01140a0b0105130621180b150a080109050f0706080f0702030d051315051003080c03091008040b06040b0d0201050c0f1b0a080604020d0f030207030b04150b03 73
    0x182c210324045800d00c256030304138052031401490a0741c101840350012100d81c0010b40c3c05000820500b102c42c1070109041c130060464031040020030000620707a094001001301403c0002441c025656002480344050380302030344000d80001e888000c0860b1540211402042201000d84151294000c1c1c00c200640004051003540d10070383e1341c0649a00c80d95001c4084580c090048001d500052218071820001d030701c5907a201d10700d0219001c0302e0020034141041007103c0e0f0302080740103d003440308110302130b003084146d0b90480340c0c02400b4a40d1034403000c41140c00c5014021855611030409c0100350f02103980311200d01d0295000d046281c20baa220041004219840c4041a0b500100720b8501d1101640c0950003920300c0c1c00400d0143c9078180210b28680c1e0400302007824201024503404101d400f0b0742011a10311000d44040c00040c030180c1401c0e000590807880003d002048240041c0303c01003058030a104c0d0f600216032101c0d02c400035013446c0c1f8000c0c04d0408000c5405070a2840d02c82242102c0c500042c0c4040007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 266666762 1250 266665512 266665541
    0x40501030501050a1d041a07261015110706021f0b03060a0f0209040501030c090609020c1009080409050f041208040210080604180c03051c050f0732010e01 68
    0x81c500310170b030503050a040c010401d4510985a85031541d4043c941a201e5101d8240356036141d01440304444080740130800002c0080c5240360f01d070100008030481d14191016903498030001070000b80c646000b26007a00c2c03102e0440000340603a050004115400103980304d00030405080c2d04010711204100c4c80b084441d000443d81d8585c1c8035001155072503000d5403024000c084030b24009850400400c0201d41030b12400c0c1e10440f4000c03415a000c00c400c40d418031400e40504140c85d015032801e03e50b07564859581010003020001d60b60349004990800c40101c080320300500e031150f07007030011303203000b0754000c5c00ba030812101500c03062170751000788800728030032145e0364481d544c020a680ca0502004108580e120401000141c000383c1e85c6140004d006074100161401c9489440f008035000e0031881e0460501404800d040003149100e152000003d4001c0151505000c0f1843c240341c27500480c0c10b101651001001c0304840405405150f29450700415121000f4038000800034454082d084407202c1c201c1c0d801e041c003c4a03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 266668012 1250 266666762 266666789
    0x31903020c06090a0305030c0d030515010903021504080708030a0914012c0a03150605090c0a120605040e011407211107170408010b09060a0e101703040501030501050a 73
    0x1e8940309024040d80030b0050118403002d0344a9850514562010311961155402000060005036060140c264084a41c500404203100302e000061b10310811340c00b00a01c0307038100e140200100302c6e8000036200102040c0003103904059440b081c8944903885440d221000a89941000c1081c440e000c007251519401a5180744c2a840c000d081c6807440c0c04800801010355640c0c016002003030380c03501000c0014500038044000580007600b003100032520940d01c4035000700c1d01d000c10049000301d490251690050181040d10a01c401c8180b210010000d5400c150743c0b003417400000c0102e8103415802440c001c2e0744440c1e2480c068440907000c4d00c0c0e00e2001c3d0002000f40c0d40741d02c00030f80b03080c04907000312012403000301d40203040c20b55a82d6032408040720304200f80700c0045c1c0814100200e0600340034281c04803000317980c500300b5814050081019040240205010701001c240400c0034a550810000c1c01000880210300580e1a81c0311410740780c0d40f00d88240380c002828000003081e9440c26040c0765040b2001040c5008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 266669262 1250 266668012 266668033
    0x506031b0d0f111218070e1509010e0f0702010e060c070c030b010b12070c3206070503190e0a060506010903080301080601050405160e010819020d020903190302 70
    0x55459122120050400d03803102030045104105003d410038601c0301041443c0c84443c1d0000e031010100f13000744100d401121520a00402c44000f041200a131000d0045d1181c4554610700417212400180701080c0d080038050000090301c0c0354400c10766018411524000019407102c101c1203098500400c8000800d400200200d134000c0048030040c00003c3c0b10301210031030241d40c0d84032500155000d070b000c03d10340440014410202241d105249912502d10704000000c0c04d079603103940c0d075070142610391040340000c0043e40c168001d5220411206003c000400ca4880345040d40c8014030540081d02c46196580c0d541740da80704a99002d000e06a030042c815802002c81040903103400c0e0181c000071b44114140700c0e54540110100f0140001180a03005d1800100004e514080900040340d20080c8070804844451104241d56035006c03500c56540c0c1424a000c55607516115085041c82080300100c00540d8400160102440071540180044407821400e644036401050410980b54003203800050040c0c0002d807145 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 266670512 1250 266669262 266669311
    0x5192f070e060109090f02030103030207080615061b251a030417040b030421080402010c060518030d0b040e0703050d081510030e06010f140f030a020603130309050603 73
    0x2030b030784481e0503d0900c441642d074a99505c01c8610320306400035001c0c0c00100500c14550100180740041102100600c3c0c10300e1304c40146d064513400c0001103885400c1c0081d46240001c000c1c200030441490fa13038280c401c0900c410080c0c24412030f4880320301c1070010030b100c80040e231080d480301c02007100d418141d01c0910790f40d038a50320304408141144d00306052803018000400e00c9220503002e94420352107000d002c0b44415082c02e241ca4000c81b0b4807403034410402e01408110041c0d9000704100300b01c56001d080416a6110791082545984017000d50200510010503602040143c3d5041890102c10503101000113000407101d0a480f40300781d00020300302c1d07801800c1411182d0703ca44904c40c0d0100c0540c0c8107041041000c2c00090305584407081e40c10009884404440c0300c1c03e4148521801003c4010101210900d4844c01401c0403200c0c4011030f2060001103c140c032181c800344a000c986c158001d08031a5645401020310300c1120f9011404e40008203001c0c0007044904101040301d00901300100481c02244500320304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 266671762 1250 266670512 266670539
    0xc040504050f0601170f0c0a030f02040f1e060b0901050f0315060304060504111905060a020109081605070801140a0b030c030f01050117010b0a09090305192f07 70
    0x326101d2048001d0b94601a4040c405580640075003078208607455400344180d03140c4a44910314000d55040030007008111f41c1e0305a05101240d5000b0307200810303480d032170000030010840340302c2d003c00c25410031450880b42d50080200e20441a050282000456215000e1142c2405000b0300313140801e000b08088031a109900d0040c42d40048140b40f8940301c0090480418401d400035201200e078682c40301306000030002010300d0810074000a4400840344142c1c0b503200355015440b803242074040c0d00c0c00600106010303c03c2d00010301c2d143c2c0010140b41c0e156510000100f6500806001303442d2405940c0300810307003140602541022000c0075145408a031681000c0a005140c000301c9242e05128100c42c10003540c90038000d451440740b01c21b0000455614010f01e00203201001c2c900b000d1141d01d060810340300340d950700c0c11080c1503501e01140043e6032105440c0a560340c2c03159640381c589100190160f08640e9900c2101c4e0b0502e00c520491030b00403d0710042c0300e9080e96402121090175900092014488581e11801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 266673012 1250 266671762 266671771
    0x405070512100216020a1e0603020c071a040e01060206010b030604020f120a06150e3318030111040e1501051908040203060105012606030304030b01090906110405030c0405 75
    0x740c66018682c1e200900480c0d00005040c012190704d480c0d540c041d403400081d1030008003802075410000c0901c4811081613400036020301018548d0200782080d04031401c01621000d452805c0d1144c43d43d43d0907826089a50708035128501040040000214015201081c0d09040321008100641075480f44c40c2040040c0d08401c8016070b00c001c09100c2800c1c48411100700d14001c01d040800000c100f800c21107c0181100401c4440c01442011a0f81c520745456480328495503010092483c0c0e45119203007600c000c2818090f80c20110b803500071829402640e000a001c50180324101c000700005030440750301548501813131140301100740885000400c4056048411050300b032051501600d4441003852440f15142c3d05c1090000040d0030000700000c50070204185405807509003400e88045600c6d01c000980e69906000c0c5e2340c2c19203107400120304141c8040040c2c43c003031640080c491000d503840d00c0e89000101980401944d00d14181007201d0451011801200c0a03a00e02a0141044283c44000d04c1301600c006032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 266674262 1250 266673012 266673049
    0x9090905100624021c080a0e1c09080c180709032909030c0d1d030d0f030b040911040c0e03100203010302121b01120219090603060e04050705 62
    0x440d072150540c140d02c00d04019055290b00030b441c40c00032110f103031182c1441242003030035580001030709403d118640d1a802868135013071824005030790b83d00103240b002c0c0240c011580d10300e100d03014103407070000e56800c4101e0f4243d81c603603182e00d005079840e9800b40e81c5110740b50304d8681281e142400000e43c500b02c0a107a6901814600b81055429900e980c0c4106a4010b04c00900d0030540f2100c0468001c00f4403040d0329080701d0321400540c14440200c0d13003035484520003445142403005a034102c4845203045000c4101104009041c0c884071010b03903078043c044010000035040028a400c2c001c14842c6450b128154002d9000204801c1103038112081c04014a6000400801e011240204c1c207810303030301003255250225040d00056165451072060140020000c0500780d041c0e0400d945001d43c07030205c0a00ca40328540246440201c03080d4402d101030085c860b41d15140780038481c11060a408940001080302250540d075000c10207140d03100000300250509840c0200342d90407242040005150803030b20344000f03940c6003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 266675512 1250 266674262 266674273
    0x60c0503120c04080c040b0603010509070c06050403081b0c1c1803050d02060606040308090907050d0f0506030d09080c060304110a120b0a020403020904060c05130b070212010c09090905 81
    0x1c8842004240d0700700c034800c2500341c0c0014144800e0105110140010310f0664040c09604c5c400e10008103c0e0005005080c001c02c81c1200042106115107881c00007180c01c00c504020609040c00d00502c82c0004a40b480303048610303508594051000b0504944802c003c0201604844d505070742c4103841140703044804001c00500d031180c2583c03595040607031030094ac032810040c80c0603669210003a090410060040b40300360003c0c001000401c03040b000321424101d049408030f056969480302038585004109282c0c40482c68035500000030721582c1e1109002d40412412a030400843d510300303c07010f43c628021085690001c044100300c5042085c00b650b0842c0c81603c01034402e07201500400d0f0b00300c020364010003410094401d40014040d2199003180c000c08820010361505043d40c0126151100141c0700414042e56180b1071052031b4803501c217885d00d0800702202d0017501542e81044c2007140c4c00c2410309900c2010128032640200005118000c2c0170200794403050480c80c83e040004004088a0405580038000c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 266676762 1250 266675512 266675527
    0x2030a120b03070f08010507020a0f06020d0f0f090204050108062208091906090b071e140d0201021206060703090e19050708090d0201290a170d08150a060c0503 70
    0x10b210440140810400e08607543e0b203001417403405d59038041c1012095401c050002c0c0003140345086400306a0303820000c00341c0d039a00004020401400c07000140042c061030705118001c043c500748c210100003030007120148441c0e6214505d045e00c8203416180c088a0891007005005c0b807005213203081000034069180795082209503400f042c0280350201c1d0b0700c9800e4000150a0000039081000c12020b000030000300c0f4240900703696000440144101c15001032205044400204800100800c600081c50401c2d80c00c81c07800f1400117400307500440a81d0601200240000b922400c005094030380c0320307415031755000400f890b2160030800300d40050504448008420b0700001d40d4003841c0a0f9600441e000d5540714140d1401c004403d04099a030301e080011641002c02c41201e000b10104814a440c4c0b100308a080c6500c0d07510005522101b03164010841034545443c40c0010160200d900c1e6800b42e2030b030702e40404540d200312160340012082d49600d40c4c4282e86103c1845075521414103061071a1250007100d18000c1c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 266678012 1250 266676762 266676769
    0x5030a151205030702121504080c030c0709020d0605041a04090f1406060f0103020304110405070e0301060305011d030408120d09050a0c03260403060b010c080a030203100605090102030a120b 83
    0x2040d000503200b650001500100b1818145003481115010320007900c0c1000c40c424100a42a40142015000201c0452403c11a031000e1080b00d41360161001250744d1159074609150180d0400504400070742d01c1c00d4000651030402e4000c09410714021003800c81109004010007000303004814080d9198400c2d03408400000d00b06403080c050f20348a6034010030301171a14408000c10a81c002801c07604150041c020b100001d0270340e00a81c00039000031070300424140c2d2501703000c842030012220304540c5507092885c0001401019844100036441c1c0c00a00f482440c807800c00740e075503489188500061603204034040d0242501074805011505000c0c1c40200700f09501751242e6140c0480081c059400c480c400c13004004102c96102c032041c81c43c0325039a840329840c098440300c1301d8600481c0310251032240c80b2491030034030b603108117961003000e640210041d8907003a02e83d4000303000390401c580c5003012041540d40410030501400646240316016801186001c080c400d04807250740704c4040203100c840d15100a04007998 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 266679262 1250 266678012 266678039
    0x15031214030906090d031a090402151308011a030a2a06030e0d11070308030a0f110a09060c0b040602090d020a1502070f06022104150519020c0105030a15 67
    0x30100c00034000d5040000b00c4505111404e11800c0915180003100071185041f00c02503019908100d810b01386030355850001c16101c0036080c1d9600c0364403400103074142d00103a00c66034003c2030303400f03400080002c002004e0020242c020b5586245616500031080b80d00042c000c080210700c40030020804e88021b4140300450700c1801902d41045000c42d8403000c0c0310142c003d08011103000c1000da4688140c4044205082c1d03605c88900d80405480300e080080090032900e0380340c001007114000000c0400800640212032086030304000305141c0014048600082e0051240c0304004119812406054064130b5545d6a03000950294118941000c0d1804032140542c0d54107061400a04000010070301c8154112402410610301e9000b804c5401003210050010a6002441215100070024420041110529550b407180525030251922010004040c190940e005000c0c0000006800b0040c0c040751240000340d8960310b04060907030005005100003a910a801c3c1c000f005008948520803040301e403913011844150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 266680512 1250 266679262 266679271
    0x40305071403010c090b0d0f110a0801170706020726060a1a0d2109030f0f02090a021207260a0603050c0901080607050702041b211503121403 62
    0xa80c59849a4a2281004c0c001c500541240e45048004181800c1c5400c005004000c3c402e1b0a107542c8000a000c02c8030f0a9000000001c0c9102c6182d80b170388070280000380428000d008440001c146d01c4030340c0329283d00c001400c20030b0b601241c0150900c5424540c00380c0c01411454900718600c00400350540c5485414807100c0c1c01407140d1275003c6184010001590340c0900c64004250064030300050071804142c0c20f88c00900030280103060151002c101c05002c40340c0c5007961304081d08080c11451044108108054407001c860301c2540c0c10407456448140d030004900944d03130761000038a0054001440e5903c144030340012580b021280c20148849440c01c80b00450080301c246210b240c0d1390a05106204ec200038050394500222003401c05581490010f50b1a1070010342244103010b404a0b030801103503200d0b000480c10824000d00340c000c81b908860000c0c40003050945400818251031a40a522074150280c0346035086140108090107207941d807020352401000d0300700b008000d91907540c0102d100e40e103070046004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 266681762 1250 266680512 266680529
    0xe040305210115092709140607080a0b0d0212011d01020403170301050618060d020309030a09140303040501120e030a0507031101050106140309120a0909050c07050703080f04030507 79
    0xa43c140441d010a008440e0441014442c8418081101c3d540c000c580ca12a083ca0780f0501418102c1c134603100d07001c0c060006000b42500300e02d051085c4014000604903109401c031b07650f101540e495410342001103504004e840c0f038000c0d602c412203401500341000e183c2010502d500c0000348045008900c82c0b0500026908402c0c0d47c4d400190820910884c00300403d0b034000100078651941d40742c440010118070030410a495101e0084141c202c8590380e9a0075900c01c0c2c1d01412042d0759924081c44045e890f5807103000d4030001700303043c031502190038141c1910000e02800301400651405062500640c0d185070032081e8400c4040d210990286604800c0c0060706842845407286a150502458090030b2024000b43d00700d0960b2601004210311640110003204080c0d6012496540c0d480750340350142007440320381807001007410000c0d010000680c031241110440e1040b4108100f143c403069094a403500c18000c0c040c04030752081c1410f0010541d0b00d070051485079040f120b800d1070030740d803561024180005940014403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 266683012 1250 266681762 266681827
    0xc0a06021308061b03011a1c02041706040b01050409020301060f0303051e090901120206091918020412030f17011e05090402010c2409050d020f060c040e040305 70
    0x1015504100c001e422114011944e0070a850240084903140814030801d015000000c8000380500180e01c101c407400d1460440100b07d054103180c80314065881743c46607032154070b043c228a214030000842d80d14011988044035282c16480c100410020b04200f08059070b0555030f4803400114aa003400d07060000354840c0d11001d0b112031441c50039a000b1050b090b00b0503a1030004022b41d100d660b8070301136041c0c1504c0d00510040302e4420903002103901c034014046a1a0032002400c003070495091036440e004201c1e1a41c1c2c482001d03000c484490441070380520f114000c2813011500d90322000034000c03c10790040203100d00d010301603070700c51580d0000541000c0c2d02600040c04241d0342e00038220440d1404401609c4252010045ca003007640c0020110340350042d01070007884002d140d034035088860341c5a4041104079520244800c41590a010341c0322414000e25034054031800d07104030b00c0c02c50041000d0b446800d5161229003803a00c2c210030010460001081101003003c1081074030000b800c0050100b18114100c0e0380c041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 266684262 1250 266683012 266683019
    0x5120a0603020f03060f072003030a06090612050307230601030b1e070c021e12030d0509060705030c0d0b060d020c12040b040303050c07051203030a05060a0e010b0c0a060213 76
    0x7264003c0c081002c1e000350010300810009403010b4191980001d940d240c10011511501800072048100d81e43c000c209000c00000c0c00021704443d0000c6055491002c0c04010480d503c0c102e000d40b00d1940d2340001d055800903c10b000100d00002c607804134a0f00e1803081c01e01c078428908c1d003540c103200c0300b60022a602c0600c9020b10950307030891480019180c42e800b8240081d410100c4000e41030400c0d4040c003e12941741e441d010b50a610010b0042c51a82c8405041d224038403521071002622608101c8043e01014074010001c1e048120000e00c590050b503c0d030301c07128074644514401d000158003502000d03140d292550540c0701c4030303240c41c801007104414240340107071158a41081c9504020b0185008a402d02081c882407140d0b00500c4211b604807a0300d07050203561082d5540e5114240407582d0b21056001680098036441c501300440298800d407030380c60b800c02c4142c0d200c00c200000321965024040700905428018031403820018002e0840901000844412032019581d040507a031001c40c000261110740c0d5002c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 266685512 1250 266684262 266684269
    0x209040b1818060c04050402070507081204050102151b07110307030f1e030e1c080301090203040c150203071202010b090c04050a090b3304060314160807030c05120a060302 75
    0xc601030521400740019003498a2805490b000341c1c010141f14660010303040f400c104003008004010845c8405440400d003003848003155a400c68880c0c1030141c00792141c10041660138001d500d12502d650030f18030000c80c0c010801c0e84c100f0f80104004450302c5801e075084002e1903030301300134100040d841060340107002841c9240081d007081008400316040c0f101c10f02e4103000030ba00a80c480342c0040e000e0f184600d40f403101c20000c5445250702072016141c440f00000200c1e401055800840c4a28003400e41941055070f0303845500e4003810171030b0044005800902207200061007240e0401c4a180e280d20020914034221800201024002d8803203d04240000030204158105501440002d003001d2504008145900001c07a1085004040344c01c0e85405500e0046190520318424190038411603442d82d80b01ca803690380150040c8540450b418007422200002401d0304012078004840d00700556600c0005e455640701600985604103001c1c0c00d01ca4140411840e40c401c0f00089441420020f41c041441d03880c41c01030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 266686762 1250 266685512 266685541
    0x20f10051e060310050a090b34080126100608060912040512030f030709091404150b04110a0e09070309240b0619080105040213090209040b18 62
    0x2034070314549010449959008203440c1300b03e280d81400400c0b20390f903400255000388906000140981e13100c40912507044441642c1c074503200701e0780b0006046140c002046014542c103c0704100001182c4a0060001c62481c107407400d4a20b4800f4500c4184405401340319003002e020300a00b440032665410100250030701005400d422000c00300140451540c0f45000180a12aa0295a001e6500c142200010746c0003041162200c00d01088095104e05059500419501d018407580c50710905040740c0c03d0034180c00129050103141e1001494407042000c041d0342001e4550008010f40c0a59600032103d10540240e000303000d090030f141c1d1840d0340c8410035000c02007000320181a0404052424800e0790002e101411400ca0f000d200a0003055031440740300704031001d8211055003542240d00840c240006040b00d0902c075031411a291184219030380c98406100490280107040790104a880c142004242e14680c000c1c80715141c003420200e4105010740200d58040340b62120b44241071060009c018003200c0c00144c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 266688012 1250 266686762 266686801
    0xf05071814011d1f11010e010b01051803011e0603030311090d021210061203020d0e090a0b030a0b040302030310091509020a0c0c030b0603010e0102070f0b07020f1005 73
    0x203840030401c8010340000c0036510419036400700c00076000d14140459031007115400d1450b40b10444980d0707101d2032600c010000c0b442c280001510351300740081c10351001c6046c011580068410795074607007086420f4162000c030381030041445415550341e52440790300906021089071080060030f8003203050703807452078014201d13801c3c000f815582181c1800307010034681d986d05402d4020398040302c800280001c103100c0d05080101a295003c80c0504d003d00000381e001240461145080c0a60255420548107420a460500410100b681d2013000007001a07000d610070343c4800d080540250803518244030517611004c01040503607040c0c01691000c03040090012010059901400000c241400002100b00f06000307800e0300c5008540c00c3c4e0f1380208491408500ca407218406158000701c5101e200c641e2400c0080501c401690480c0c040d500340005002601814022074600ae03074031454038284c0031616195595607100140203041180503400702061107210400054600081035800000c5900f4401501e10702c4040891 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 266689262 1250 266688012 266688029
    0x60c11040b0d0b1801060e0604020f041e060f1d100309020603041b08030a080408030c160c060e0117190207020901060f09050a0305030a03090302100c030501050405010b070b01060e040f050718 84
    0x1101440b11f01d03005800d10750003d10a940168450087d032401070418020703070704039458460607030384141c4d40140c8031601001100c6103600d451031412144441210003140c01100b1403054050710000030600d040c8002c03050121007031490002408112680000c40c20360041da000e0301c08234603080d001100d00b130700e461a4200404080c8011442d00b022004e0240407584010300240414001200103481a023039181203800328113102c0c00d50040e8160078645900120218014a80061503002e05a8280d5005807116017050129a034030741d9040e030300c0d0048001854035001d07815542c26000d2101e00016200c4080c11400780c11140c40c0c089001a606500804402d41680203d1060b9101c40c3e08101240d004422104031440da40740c0802c104c0e0250800703034a003550354640c844280307181c5603a2810007a030581c00b8506a07a012242800703103036610104051140265803001e044072080c18010052240200840e148052015001103105452048224100e800840b0311101041c2001c04000c0c4100c0f40b04139140c058500300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 266690512 1250 266689262 266689271
    0x1406030f01060303020d1d0904080a140412110a0504060e0117030f0301140120010b0a140f01050d15180507030c020c0d050a062a09060c11040b0d0b1801 67
    0x113841c020360b540100400c0d282400b14094840303001001815039080b0b21917000d0907644003403c040c07070010f60a80c840150040010102a6102c1d20b880140c03040380c040310070014240b00300741c180d82c64060b550842c04800a0b40304060010000795626a401024018040302c1ca48420561400e01640f0300095180c3c1d0400d600d0b0810031810902505030000e482c15620084541042c0c04903400050310700b00c484126034120101c40d0800c1281c011415009401010f40a0341c11040490f41c96905d030059065890903158402401500d8644a500c1140500300d152000480402c8a2a01091504480d901034004010a5030351034015041c6c0c148030300031241c01c8465490204020a01e00344025215012000301c83c0c0b2540100d00b03500180901040302e50140ea030403074020048101046011308005821800b281030510b560f21f180c3e0f06850040160404445190b150040d110000740ea1300d14145101e1204960f1003669034160305425100c0c55080d00c0c0e100d00c500080b03829410000c00c007181c80c1c45030380c40d44803041e03061 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 266691762 1250 266690512 266690519
    0xc061617060a1802073512010614070807050105240f1c081306081305030a05071509050d08010803040521190c06170f040f02030f011406030f0106 64
    0x40000721003c40304030907000141d01d11840000c0c0081d2040140241c10b9103040f542510014002582442100300c012160f41849075488504800c94041c1008840c2c0074070340003004004040c000c451281c580500b01d81c0c11481c6c4a840d90f40e0350740640280c00c084e1501e039503074010044200800740582450f014803581b0524880140c100141107801a90700d154001c04081c95075200d40305c445600ba00000f5400246151940500c01403401e000300030340f00c2e00c00082e03030203c0480c1688045140800d00160030030b02440c64403001680680300c039070000c4821251075990b082c0e00410204584981240035205902410f082d241c61200142411f1068100ca810742d00200b01c204004c4c1d036402d51b12080240e45071a00001048020815410401800001c141e110003514810040200e565a42d80035540c407511086042c80031216407a0901c20125030300031848202c10041008104c0302c130392800745284020115001d07a042507200c0350039141c4030300961940340240c0d010300141c1c2c5010720a440c42d0400c604001c00282d441e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 266693012 1250 266691762 266691769
    0x70503090c1002160306051501170115050f0c0609161d0a14090703050f0109030c0305161401020a1707090524040b25020f13020c06161706 61
    0x10706044180c418401810203501043c001e104a681401100c0c0c0440001d42c1d0320f0602d030021b48011074200151a08090307100ea80d81d0b001d25402244514480c1c0345108603820130034a088101d03818400001406010303c01c070201c0020a07402004440e8042001e8182414041c1125251150346070640c0d0f81e414048405004511400c01800c0405503024140801600d40380610310003025007070f0001da00e002e6100108100502d000030100304691082d42240c07100080d40d020030f0300700e0b00074840c0100060140c203c03010200b44968003a02504904040e010361400d21590b801c110820004040202c594010511401031504440d64001d612403a0000e00550f140c5403400800004040c010740e48030740506010200c01c008051007407a01341404070703c426911901c1d042090403980214a0100301c910000850311041c8000f500800c18442d17001d003200c1c090030314280400181e650000c01d408525503091100c04030b5040104144d500920b011078040c542000603c400030000002c282c4004403525025060110300d07103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 266694262 1250 266693012 266693023
    0x305040815360f010501030203070b0f03013506091212011a120a05040212010b0a0603020a02030c060103120f021209040b0103020d090605191808091507031707050309 73
    0x30842c115075a401042c02000303a50020880d21144180c0c0701c0e01d1800701da0b0010540c000c2e8140e174000c908171150580e0704d0440819034850003c0d80103e09106000400025070f100e0250321000700200d01c6600809a0103802c008590002d04948c010340d4441014001c00a50501903a00001c1ca81400030b072909100c0c0c81e8042d400d02c01841060690881500103041c01000d00c41a20a90f05031991407034102d040c9801c521020307000c166816445460101c07806105888144202190300e0b5005e4000700140745000c40507002504079040510940c001004080d03030580c0f0038000d8034042e40c407890440c1092840c00320b00802c21096100c8040543d030141208000e06541c42040d40c45c4c64a0480b408074a030842a00103c0190148a000426080c01c02c06a90100841c82c1c00c650301c62401c4490340c1c0c140f11940344180d0300342c0e142d80e90101c620104400030b0b500404c0c02a40100404000a0016140b41d80090340c45003042d840f43c60700b0340002e0104040c500760316a51600303080d003280051a0290850401e00b02880e184c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 266695512 1250 266694262 266694301
    0x101b060b060c010926191e080108010f020c0607080703060b0a020703051015150203070803130201030f051302040203060402040312110105060103051e1b16020324040b0702190305040815 81
    0x2082a6249240c6c0c4a12854201c0540d0031030f4100c1840400c403952014216040a000e0f9446070b5007448080c2c0318010142c8242e8460700d098100501540d200c018041e40c007041c0140200013050703201c04021a141c44824000c0065080c554014000640b4500b0160b080c9040101d40e4502c4906051b00d48103001c0d9100032040036203410301454181c0c95041c4070f0591462280207402040301c0c1c40030040008003212503000740700c118000c0e203061000c0343d10300480000b25002141c807172a074901d130f03c00c1207400341c100365014550240b4041e2006161603245d0315980d00e405840a20b000004521001c3c014400c00d003070103190342151081c01c0c00c0c001410003190341d00002c100d003100d40d00a200b458001a0811035a807900c2035420306020a8542e4409424440040700385030824164024452200000308010541c0031048103480e2811410310b1a4680f941c03181d480301000344c00d40045101d4001c0720f802413040c68a10721b058070302c0781e01c4981c0c0e1145008819400c0140340c000400303030f003031482c0101301c490342603466641c0c0c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 266696762 1250 266695512 266695537
    0x2030702040605042d090c0e0106110a05030313060b04020301080d0909050601211814010c050c0d050a090911090901050102060402130509012703030b101b060b060c010926 75
    0x10518007172030b4004184400b805890444c0c10400000d4850380300b00681c0c1070764610380d2441d000c11160740055a4501c4001002410350740100700040380703942400301c425042845a24041411000000010140d030400e0300140f8503030704055115150182c10804400c01040b00341011302042c03400d01c001802c660741081c40070b455440b40d0088074000440550020160316541c0da410362401903a81441c1c0f0003024600780c96603840d8038016000c284117000d441914640c200300303c010900714414007411161074000c3c030b1a044c10b001e1203241c0802ca521090040040e4140000401c91704d0780119410080c2018041e4085410354200901b48070141c0ca40b081c0300c50b03605c81581008281a01c5140006005054200030701c0e60492000159000001c2d9a130210017190b8041da03404c0c0f01c2901d003075080002c011084102c031800305d2941100803240c24285451707982c01900030300f4000789ca00100d00200388a60700c8400d0a079802c1c2d540c0c904400c2017020310080f951454a9480348010f01d031081c0001c244040c460001b59498 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 266698012 1250 266696762 266696831
    0x1305060a05041518021c0c12230a03020d1403070c08041805061008060108040605100506030414070f0605070204050a0603140a030f020c1f021006060203070204060504 73
    0x140895000c400c0d2140f1203a1a0802a013089201402840020000102d110380f283c1500300881c504010031660f941d5800c0b420110605250040011035010b042804840d40b8114030050402c0e620002a405505041c02024202a40507443c000b401c044c07800d94200248103001c0007030100104075070103032030f0310920a0505002103034042c1002c8038280035a0b070103401d8280040900702404202c0e80c220500030303030703003940e4409001070401c606490107901254210b001030300310742c000f401040c02031304055044a0b02110160085850320040b030b1440d03008076030a580b0036070a144240000c5600f002403030018042000b81c3c010240c10514010100d1203681c0001e4030840e00c43c00892a1011290710403401103502c0804882c440100000850b15220485015000300d0703042c54402040da1300100320303c28500c0b401040940412810550704510525425041085101d440640171168443d482450040c1620b5001036440e4040c03881000260b0340c413a044070340101d003482d80c010b414040c08918918109602c0c120b205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 266699262 1250 266698012 266698021
    0x11104120501110a120f180314120f06010f090503031605070f09150b04061202030403030b090103060608010c030b03070b07020315041b050913060c0905090a020409051305060a05 78
    0x1405012804000c44100f40001100031840d500500c92056050191905010403450000d181c0c080b10540f8034260b2501c03d15000a00010f44100100695020101c00d207506060304449a103039044000c583d003802c40c4000e04148412503800419a50501642d131505051013810440425101e00444000c1508002030303201140402034240490300c0500599420020340c1641d900b500d030040d104001c003020781c048052001143d200041c030120340a5035140d485580300c4008102c01c030360003548000c00c01c1d010103039035800c18441c6036240000140214025280405c0c0c0c80d013403014550840d46e45880300740034149000000802c540700400e620f0308981d03d0304100358581466001090070300c3c14034150351100000030b9040104000020705100c54626102200002e415158018004411400e40d41c000380900c980e1200c41c001006504000035a91291510007520307980c840205021400039a04000e02076000311b428801c050491007030135070007400d441d8002c01c0c09003180c031400e4543c2800f41112100341c7d102e00014 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 266700512 1250 266699262 266699273
    0x8310312090803181815220905061006090608041b050307031421070b0a1b03050105040c09031a0903130303050c01050c090f0108090a02030a0506041401110412 70
    0x100000c0c030510050740c0d658404000104c118202e219012803080300e9041045950309980301c520340c400c0c0c54201d45115200018420404103903c00782250b085500e0140b4000444c1c0f03482d004000e9494450707401014a81000c401001d80c80400740c000d10b0170480040c0303081104951218000f5003040d041031582c20003542c01c805000b90a28581c100030f03094440c0a40c000b0030010300340d920b01030074405602616200d1440b602100640f0780c1400601103584003d100e0300f4080b0f0b101c950941e40086a600001130b1805024080205151031449207030003003999034004100c682840e02030125004110f1904814484c215600e041c4126903210b01001202080341c00a0010720042088035415182d1000f07904442e992441c0003001507104102500f05c1e5400c0c800451075213210390090710500400200a4440b40500c000111341d909002030007000c040c402c0040e0380d00561424400320040034000c1014244a1600d41000404c0802d003070742c0e10300d15030b2402c0c890b0b059003962441030390103842484890715400031150074035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 266701762 1250 266700512 266700527
    0xf070c0b040507080106080a03030516120b0301090204050117010f050f0c0304030315090204080f06040503251b03120206040203070e04020d0c08071e0506190c0503030408310312 78
    0x1350109601c0d00c03030040f40c2610005902049280f09a8050203250b0b41d20131028000c00341e0f00c815030301046000481e8050203907a50084a00000c000d40001410509a000030b41030b2003080c0e01c03031003240c0b224094038503031030400f80150000119148418041410100203004680ca001810424030402c0032000c601014441e40100c1e01071a07409018440d52910b803a11400258030520501c03070140702e03190621f5a041c50101e03415101c0d507000800741d0304080740c100100c0114040d00d01d0a860f040125139000c0e001440c1c900100c04584a110010350b0160b00714680045104800d800b40d10555000d0020000141d0740020480107540b0301c8000c0000d244c0b124800300d02d00d6404c101c001808120010408104000006030031400c6982d454501440415090342001c6030010600840380c11070702c100007081001602400c4030205400310302c1e005040c40010384070941150130540701110b00542c001000d10000350f007041c86e9a104a05c0c0905d051207007454103040120501d103031100a040000c01400e580700580205c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 266703012 1250 266701762 266701769
    0xe060705031e04030c08060f070809062403010e0706171012020109030204090f020102241b09060d02040306050a06180b060f07320312040206070210170f070c0b040507 73
    0x840304a540d1101d1415403107c0045541401074480840003032004d034440e07400140100449070141c10300d51102d105000c0101007100298082104d4a00c0d45240c035102442942c040200c00b81c050b0000364240040103200b0309444d24402d80d00503080c0180881801000800003c48181507443c5030180481e10041c0c1c0d558170710707034006036009241091810a00c9400650b08032454401d03401d54900c0e214004106103104040c1d40b43c0d1010008000000d4030000e01e00c443d80b01d034115481c032894100b12803180091000d6005280d403c00841e0042010001c20040340076281c1c2040f9161420700625042602c04400104d84a1020040d0384d02c644e51801c0b1f40c1c072404112082070070340046950f0b44000c14189045072020003003684150405010f000c00d00c40c01541c030382003400b80141020b1407034801c651661403149240500240e80c00303503042120341c005030f4606148414411140c2c80344100100010651503029400a00c80400c0308481000c03c078004d41d002c0d40003451b940d441002c0d0506c64407603060031440c2414640 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 266704262 1250 266703012 266703023
    0x3030c0901032306180106050a080604090b09160909151503061a0913022d03010203010905160207060e040c0e04050405030405100314070c0312050f070e060705031e0403 74
    0x810324404410f0703034802c0612400081d5400c00558120100112100000f4402c55000030b10500c4002e0f00b491003aa64182c01c004024004175050307a054468410524041d20000e020364403e2413010b119890102202000f02600041040821041c4d22550b01d5402802002d503881c0d035894080181d54081581c540c0f01a641201040052102459003d2122001340350828401e10109001800d02c2c080044210803055000d00074040c240e8070148401048010000300000703100382070241d9006a1002d102450080461440109007401c1c07140124603018000d80e694021504154402d00a00350820b0101d03040300c4080e1030004400c806180101c4036042d03840c0e580c81c2d00070300300000c0c032007440400005041030b5201117a5540d80c1c1080800241d088401302a40c039051520008000b4117141e008034039041249000c3e003083c1c1c196082c80300410048a0003116481e0510b07000c0740c05e00400c03d81c4003005030050001510114602141526025903d004181641c1003042a011141a941c00542c09030f80c010356200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 266705512 1250 266704262 266704301
    0x509011401170c0415120c0b07030e1e0915060d02070c06020c0901030b060f131410170613030203040305060108060712050c0d091110020c0307060e0303030c090103 72
    0x99071500d100102035004031069108003c2080403d142501c07501e411070090000f01480540342c901d541e0002c0302c0c040b400780d40070710318040006003036410f03400140040c40c0719503107a504400b01c0800308003580c0b22114220f003440300701c080b4100690b12504282500884440390008500c0c000c40e0015409202d5454405c40450003c580e103000c00c40c20300d12800c140c6095809440011402c40180061f4000c00d210180c40924400042161400d002c400b00c1b0354800080c020b0501c011005480034242c80000003152a0344070400e003008204204662244040c000041050042c002c07440c002c035582d520090301c0c900c82e42088404c1d55007014020000c84008517485001d80d2459070392040c00a85403801180d404002c03072500110804040711038400d80744201c40700c0e04603505021010b0f140350010019000201c0700040b403400b2002041c2d84150540b6000140c036401001707070418030002d16050100b0350f400b4100784503038201304403059907001c01580d81c000c424100c0103450f80c0070703100100d0181443c00804035015100 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 266706762 1250 266705512 266705519
    0x30d1a03070308031b19120902041b090501050307020a110d02180a0b0406050a0909020f04050a1a030a05060412030f0203010909143403050730020a090509011401 71
    0x10400341d03114001710540b481a4043d000014501441543c15034000d00c00c0100070b0395031050041541885c500c20301400000c09042c0b95000c5000c5904501504140654030b024500e00c042d0b000240c0b0300a0202880c2141c2075041443d0b020355110341000005003041a502c80312a8a6287e0764541c200740c41d00180040d00420000600415018040d60412140c0b810040268100d0402e4002e0f0001c4070005071050145903d0a0000c00051900d4002280e000000c0040e94802d03983d107009180c041c0d88030b0500003410800c000c8a094003070b401d41d000d2a0181c3c1280b00702c000442c0c4003103001d662280d0881000c82c080c101c8250700310001d10305055000b8040c1c1c4040b00210b407660083d8802d03403000b4400c140c8402d81c8a000308035107690b054680e181090341c52040042e00415061588024040c18100018003c0304da105d664803410906c071174100040402c508042285210007500c0545409000d6a030100c0b40c6645640114548040501811501c6a111404240003100940c0700e40c0350714202220341c5806584 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 266708012 1250 266706762 266706773
    0x903010230010b04030503040b160f03031a0d050a030509010c0b010806011a03090705010311090307090203390304020f031b0102100204060c11010c0b150307060503010503030d1a030703 81
    0x8100916046849914001007140f0150303c0c2141c05994004005601700f902c2c0c00c1d00318a480c1d00c81105010305114000042d00000c0c071602008803154840d403400f1807090500c4504030018101112264814290400d50b4004180041101c248040c0c141c40d05540d079440c4480140c030a01d001000040800d0100d400000754194007160150589440a4131040d507400c13075183c0071030f043c0800d41d00c508403500301020810017980a50b220480305541c0d940624140109000000c2c01d140060744044007040d000002c01c10120ae000c0740041d081910100040c441d0701e0b8914903003d103082c0d10144e0179840100000810103650b2040140d80681a00270112481d003041c02c46150300344110318100501511450b89022030300300c1e59000340c0e400e80f15203588440d003003ca0341c1c588011881c0024021418803100074100400b0a41040ca03452090001000d81803280000c1400c1c5880c1c4283c3e41d20100c200441400140a41e0b0360200444001980c10341021400442c0381030324031b18213604802d02c01e625200344d2000004201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 266709262 1250 266708012 266708077
    0xf2109050111031008060a020c06070e0a090f14010b07150b06091201020d0c020d0c26030708040309050d0c061d03010e0a03020f0114060907020c09070504050f010f0e0609030102 78
    0x30702205c1a11900d407142890f02040e401182d0b040300203500004001038000e0301c1001004407a0000400d03c89100350740d20300700c0c41203c100c04e60f05030019071501c4c00611402f86180c0700600504140c500310b0b14000103030311800006941302041311006900c0d040b000d1000d64458090f00c0d14440d004095010207000c815896001f90b000b40b22202d402400e002d5507074046400800d05000c0c0c0001501d0f4240f0394800d640e50010003851000400020000d10040000e10f410f42078050340c4904456226100c0320709140c00d000c4c0c01c1c3c0289038406440b55005801c40400603041d00c24400444040d41000c120214003508040e852a03005040711380c00d50b02e003008141441c20001642c1a115010342c0965040310b50002c031039400c0c0e4900d2103041c0c00c401441000300d491410710748030340b5501501c070380705640310200140c0020790400d10949405001507404a0300b842a0b140c0304c40e80c16140c2c2000d0030649445803220801a18510f500034540d4031610300441e0b411640d8500790111a02c40004480d0b0324902014258130903a4013 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 266710512 1250 266709262 266709269
    0xf04031a010503010b18010605070f081206131a0d080c15010f082107080c06010e07030c02030a0903170702030a06060311030a05190f021f0f21090501110310 69
    0x139820f00445080718140750090f442a0448020400880d03030a0040959095000010484107101120500c00201d142c14001d0030981c44003d2000c203240c00d2400400c0020420b460340702c6442480d1601c840090120652200c000030000d84052483c444541030500c3c09008151503441203018480d0340c1c08483d040c44040718180c8014200d8040300320744071280c1c2a9200c4040030f180c2041100300b6040b401c0c1220a001a01441d0b2061401500d4030b100710002c1c0b0b09000080e8060707906900d50105000795144c241c01070482e03602440c4015800e000c80f10b60000e00c40b10701841f001d8206001408030124005c4440d04848403160050300720f90070303900c0d20f20742140200100d04c0b0540b24070b58101000422441c02051100035590801c005050301900d8040c204060101c8041c200d81e0880840840300051719121032004110304500820100c1071088013001c1e007500c200c01020410800001414009011364050104808503110300000d6210a80e00d0180d00502004482401070000401007022400b0b5400030345041c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 266711762 1250 266710512 266710519
    0x4050d050706030e0a030806040b0d0f05010234020f04150e040219050a0b090d02040c170703050108031b010e0109080a0201060812120402150a050c0105150d080f04031a0105 76
    0x1000c01d007000d135445140f06000140002c403900041001ca00c0c040c0c000321043c041c02444180c00c1e54a80d61440c0800307040a01c2102ca80c0d4003c2500c00e12080c1041c40790803a111540b611850b054804950788251000510000384211704000c848007070382d11658030002c01c1e01c000350454060540c8800c0500725141049804921810826241c0101c00c070b40a028207045404c0904001c00321400d0806443c4240c0000002507040362080038101c015135154010640a403078661501074601510301d82810305440c00501c99424141454010081ca030342c00001c41e42049907501c4070000140b50741e030160303000d0b2100c1500a0350960030401d041301400841c100420300c1240c40c0d002045007940d203c0e402500c1d650304048041149006008940306000c0c0803603900d034454402800f1100d00d44003245544440d030400c04682d0f0000b0004551000103140900c80e0f41d4119554144404407800c0c04000101c0c02c40b8200d0008090540115082c610300c1d500d9030540c0d026680c0042e0f00c1c188411400c5071024440030903c00e5603c03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 266713012 1250 266711762 266711771
    0xa0606231005040e0a0908040e06090a0905030307260408030f0f0108120c2a1804051024082103100506032d01050906011107150504050d05070603 64
    0x60501d03164100e8071054006403111810030345802c42580407410300810281070140c40701d944400040f4444000c0001d041101e1201005003042030174405541001040b90841919000d84040807440010942c0c0e4022094a04441c41c50074407003444240c0071840e182c2c544000c040390705002c20420b03580702a42c8140400103011501d40c1c2c2c2c854144014080a104401c2c17140c004404001d048280704004120040a46c400c440f085200c0c5102078058502c0e108024001a08c01401d408a51501d0075405c2180000201e14440a041c1354a416450f240c042e10441115541d61040c129080e0300c2d0042c03100d007404141c0c4001344055460f00c4260321043e0720040b0021580300d07008030011417202c04069a002d03003078280c0d00314102030030041800680d0744058884060024484844c480190b103001032a05c641c0d004041c0c9801552500080c4142e6070070251030300d03040c88460100598031000000d004401c8602c0414408a010708a81d8192400c1c8140d80102d038008010304890418400c0c00a140c500f2a40300743d80c04c20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 266714262 1250 266713012 266713079
    0x1050c070c03020d2a05030c03010b060423030601030b0610110a0b09010b0a03050c040f0c140f07021215100617090f0f070315021201030803090a0606 66
    0x1140e108540004005600814080c0094105140c410a28a106a003110302041072200150f13030343d941c020301880b0000c0800409101600b41400303818441d007401e400a11031a04880e0000c4c655005a015078000d4580d941c0c0582c0610088449844400e0400340c103607541c82d41c490816840f0000100c6555001d403080044c01a010381c440c440302603144004401a0900709250b540300030300d140000c0c003400d20329902d0b40046480d03543c41c52040d200451158004120740c040d880140007d40b45c02c118491041490a1490700200d81c004140361202c010183d141a9036110041c01d12100303000d079007006900325071030440d050b02c1d42d800080c6412025100350340d084002c0d5910181022118054000d420005e03a9410005042620b01014075400c5244e08040e00d51503442c0d01c5d1204d02e40607030160b800c00d0a5104883c100180079140800103050b15400307030150b00e08a04021118000071061000034170040c0c00000142000b4028040341c01003a42c02681031080d146d4501c040c4400581400400502103800803210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 266715512 1250 266714262 266714281
    0xc0a060c1d09040b0c0912061303110d092c070306091505060f0a020109080f120901060f03020d0f02120102090a12020906010e030304030501060308030f011205121b060c0304050105 79
    0x5203d84e070321158072081580c0e041c2e0100360640050483d9500812090038400c0e103500140300e500c2c45120340c80004107440c1e24506009001902c4003c0284481e0130001032003001c1c99200d443c030f809580c08a20000d41450340030700400883d4a4005202d40d400102d1000d01005541c1608030204481d1000e00038040080c1c3c00c1440740c50f0464a2051551001c0200078082c030034200380014140e594080d000000d909002a264002d065000007143c4184500000300c0e41d40c0c13203003d0300d001c54110110708000c021150815991003109062808064403e002c100c0c12031040005104040307403075607405031a120035078642c40314071b90107034008050709440341500d8900404c040d00d80b81d01403156076070000d0200d0250340700c600054840c102e5a40c034094041c0000c01010021030401d0003024021b46c4244000c0d640d900c0c1501c090b201001060300712048200043d600b41022607000140781400301d044034012541c0702010800881401c0925104c410b40d0b01914007002541c004c503802840c403460040000f80020790365529103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 266716762 1250 266715512 266715529
    0x1170907030b0a02040e010803221514040b0d0f06050102012009040605150d060e0106020d11010f1103040209010506070510021608070b041401021c020c0a060c1d 71
    0x220055020321401c10200d10303031902154109200140040c94151601d0006d02c01c003609070800150382c0d1000480502c201c1a0f031280c1c9c40201840c0901d9000241090500700e40482c501d1480020465620300502c00403a07010f04507402800d40d2200e02d130703a0f0794500490b1005001100030b018003da18040000500394010b006c2d440d10040c1d0307503802c860301081c0403040f8041504a003050b00d42090b036a2401060b00e45944110065118010f5901c0340c9030840580c031441501d01c560421600500ea48004110213500000d90314410001c905050240d624a15503250050000c280210401410901c41361051803405000b90700850099903016016a20b550a01245e4851b204004000340d2007445140e001a1140d8050301d41c000030032010241d1302c10640c41e02c0b040e54010352000c0e980044c0c110140130401020002203206200204000d6040c500d90400001c003001d200781040141c02d030001001182c18109010001580c0c4c0d02c140c0410200500000c004c04031050210a90034a0390307050116441c43c90550382c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 266718012 1250 266716762 266716771
    0x150f030501080c06091c05060c030f011203080c092e1e090608132112050f070c030e04020310060801060c05030d02070212120a0e040b21030c100207020117 68
    0x184034175007400d000c11710060601c030541e5243d800d40a40000000a00140074860080002450a070744030705101e4054500d010040c3c0c000c1e026484e107c00d141d00040d410010041d8003141010f0b505481c0c4010320007040005440099000b50200081d0308082c00030224017842d0940c036841e80e200481d05201524100661261030b5001011403a42c400400c455480f6603001540002d0904041820100319134a03d85071a0100d20a0132465051480501d80182e2144801c8103014940c5018405801e12080c51215100d001e0503100411101c00944018580210f0300641c001e00003520456503860032807034030010320381035018000000303c151000280301d501c03032480703c00b92a800a0181d4075040300b41d40140029807101004076084406c0422022040303001780490300344600004080c954400c06003034001e00300d03000c0580c134500c101d10b40a080700c46519000008640c9041d0181980c030000c0c026090a8618020001e14000a1258040d9408030f4165900070304200ca1003078079008101040c11b01d03601282d030011103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 266719262 1250 266718012 266718019
    0x10f050f06060307020f010c090627031704030b04050c03010b03070602070905270601050a0b04120b0604020c030d1505040608190c0504020703080609010b030f0718150f030501080c 79
    0x340810a146801402140c00c03045a0044070300340391840206a003580d414400d10001300e039000c8801c10055820240041c0a1001e105201d04101149013203244401c1140c000a8541d0b009058861608070800003110051354115618031054a010b2411a54900784850811700035400c2c001d9014240c00e0018901e400c5d2240740d00540301250801841d00c0081400420010076044260340c90303461500d8a010110a4443e40000b406142d03060600b40034110080e5806203081d280704000c2000143e95050341c440105902c0814441d06496490014001e07000c3c840d4440c0d1a80400548515404042d60000340311080c40581051181d0f80c1d08200400c5071400d11900c8450b1b00805040d180000c10320003030108085c171441c00c00007490341f640041400c982043e0710840c0401c610b001408214640082c0c001d0061260070301c0c441c5145011440011000e5004c2c15007001e109410715024501c00c0c03601180d602406115290a400c40b46054000b4001805440600046854400080741c0903c01040a5a6030b00025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 266720512 1250 266719262 266719291
    0x30c0304030804020f12030a092108090301020f0f040303030b0102010c080f06032a03010e0a02150f04080109030e0405070206040512130b03070306030507080a0210050304050309030f010e010f05 85
    0x1d48050b185100c000740101e80c420680c0700101d480703540c0c4041000d000d114450081d41c80e00000040545401c605030080f1940000081e4180b0340d00b4200c1070360041440d8400150b54885035005c0c00302c1e01a02509070000c5091401003034154101c00307510b001c2c1040b43e002e603074140072108041d0016402c03a00c181c0c40c00c1000416080000d00d14074080f00e459030f08078802a0444d030134401740d81a000c0b42e850040e04882c102c01d11402034080246401d00400d1000c00f500d40c0600108282030740004e04c5060360749106c485220700421400c81c00d400440a50b0001c1a030346000307000e00e202616004042d482003400b082e00c66454580416111440021000c0c4542d41c440d000340203042251440c2c4203a0303040491000400150581301041287e00200694000c1042c1e480204003142546015420503280742c1010711503034410101360001d07a460444181200301c030307801e02a54a44890400504602c950700300346416115082003c0d40e41e05056001c8061111000000c005092510701c84000340e610a0b148100c0401d403c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 266721762 1250 266720512 266720521
    0x3060315050402060d050f01081b1f09030c09020304120e0d080d1e0902030c0d030807050d060305010507020a03030e01020406021b0429090c190c06020c1917030c03 72
    0x240c1c03155411078002000c10f401c4c000b444200d80140c0b00111149011640c11000401940e142008510f44418250300751425013440000031038001d0600c0000010b0001200e50103542490003080c1c501d001c3c41e0080c40c605207040c0c0729082140a540203075021500c000c40740c3c0f91070507540d1140e6008000c3c410b004060b0081000643c540784040c2d00403600f0341003216980d06c2c400b030702e014902002e14840c54540c1e00202e44c00c1c01d180100750400040841440c002c1100d13008110000354030581081d0300030502e060803034980d0200f9180c000102040d4100030305a40ca0442802115030b00003413150315a0b84a40d8060103520f40c1041814203074000c0b0b1141c00e001d80c1c231141d0440010a82d9200c03003110701c9006440010010400388039000340300501500070f214074501d500d060549081a004841d844031070010705a1070030302e8540c0030984214071120b040c020444002d0011040100710340445070b000c0c4102d411115605200000c4008007402d1603811a12409200060714904d2910307000e480c801c0b601c00340c00904584d603 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 266723012 1250 266721762 266721803
    0x503060d020409030201150f14091003060c020307170306120106080c0609180f0f060103052215360206030105060d02041d0f070201090c1e180e0d030603 67
    0x43c0d18008405554942c1d0150f4560baa0407244031004000c4e9a820b4414149015401c500503007100071011b00556a141c01c00c2a4010b000c100181169030151001070340400ca00c108038214040c00d000140a0205041400b40c0100030a001d140a000111466020135408494880c200c4a041c0710b00d03c29038000208001640c07406401070200680301400e0b80ca60305c40c440742400b0f45c101003150724000c1c8881610512500c50780c0ca058180e0f0001080c00c00300080c0c101183c440c42e03030b6141d00c40140e420007020724001042020107010042c0d03644881000340070400e00091005203086d0101c05a85e00d04488140f0030400451011942d0350043d00600001e01c0e40e402c103014041c290340981d40c10700a0f103808000000b03c0c982680100c040c15941003140244d00e05080c4944079446602400103411a0b0500d41a0000300d05442400800c41d4010300300d00c0451401c00c000c582411100350300256003da50090040c2c041501e03504403207400000681901c00c0200c04681c158200ca007980006809a4414211400c1d4000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 266724262 1250 266723012 266723021
    0x10c120e0409140f150c0301050907020c09040b180102030c0901140c0601062d14160507080618210f0c010203041407060f0c230a0303020a0e010503060d0204 69
    0x2000c1d101044076821a141c1c1c107190301021605811591000300e44140002003070040180d196000e5419070100d081081482a440c08103000b0288120458070118031124000c00c00c9150303c0801908851151034607050017540103070103d8118401102c90600c0d8071803244103108a900c514031149100b8140050000119020190300944044154040045114a0000700035aa00034001e0365034810071102e0b21440da846501568400a5441d54443c5a801c00c0d0398025004213110f002d0389503001c3d2522801426602421180100038016000e9100b0110f0b5103d00440ca0318424440d0450004040d2402c1c1d490503a180d070060840420075102d17030012a1040b407202c00800c9010030300d140c1a03080500d0a00060300b2640203a41c11101241e40c00000c440207401070248000801142c00c00180c4c181401c00054800131031010010815401d04880015507202c00f03103403000250740c680842d1100f81813850094001e6010200c8071002c101301200f95507066109008980c456200a004a01d40d0702d000c1e130900004c1d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 266725512 1250 266724262 266724287
    0x90109090b01120f0c032006071203050c09150415050901090308091f0c03020c03161206090b010303120b031204060315150203070c210813050913030e010c12 69
    0x54003c004404c4c04038801115840240d801080d2064141c10116244440480758101c810700505060000c000410300c0d00342080d0100c211420007081c41ea5400d411f4512510a00e1032072603000044040390f043c2c0c1004100a4010f0f96841c4601501e016680201a500303400b80480301400904060b1042c0006000305001d0700d182d5802620340301c0352071902d25546034074000d1100c5410014644140800915504010100a500c030681c02382c052030140903000c007031007920b5010301000c00034940900b074100086903000b00580754215003140e01d43e58503442c00034500c403460403510301070a06000d5602154500841c000f07554001c1c2443d0035141915200080d0041d1480aa002d900e0642c40c40c2c0c0000c103850180300b6102150250740c051552201c07189040700840945400c6158001c0d030b11001d481024202000b5810b01c2908454250303161001c000d6410040c0b0501d8012a03000010039051000d40c0c5400c482561441c0d07c070781c585102e850040401140d0094064401900a80101003000d0303283d40035403941d0090 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 266726618 1106 266725512 266725523
    0x50f072108010609090b0102120703090501080a11040e13020a0803030a0f06082d01090b18060402010f180f120b1f1a0403150b090109090b0112 63
    0xc0313103d6015020000c0e030394000548441c4e00070000c00f444d0302c00e10b581c0241c0d40c000514005081c44200c0c410700d4080303409000424031a8941e4000c00c11256400440141814680740c19040040d1028013291140c072002803003000036032182c0845101908550005555a00b0300e0f8502d0002c460520200ca4a480e103851b00c1401031050100d40ca19178142a01c10500c510100c40c28128202d0400c030141c3c014943c6409260020881c00300c03141403207009112486080c0d07000b2400c1c4c00b900e036076040398001d000502030056010528018a100f00644017a000f0460181c1d071140c0342030b40314000d1900203004035a11420306004009041d09810780c01444036121b505a84400118550550b040c0c3c064000c11681d66921040d010b0084400c0c3c1b00210f4000d10112040176942c00044010021541c0d0075005141d004001300c0c420a040c0141030440368860f401078416882e04007600c807441d004890407500b = true := by decide +kernel

theorem cover : BRFrame.Cov 266546762 266726618 := by
  have h0 := BRFrame.cov_init 266546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 266546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 266546762 ≤ n) (h2 : n < 266726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
