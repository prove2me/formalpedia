-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:55:14.64287+00:00
-- url     : https://prove2.me/submissions/a8c43011-58e9-463c-a620-e33c62f6df50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 926438848 ≤ n < 926618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 926440098 1250 926438848 926438867
    0x4050903040f0303210603020612090a060c0203130e27011e0b091f18020d09030306031a0702060a0e01090f05030a1b020f010e0604271b0f 61
    0xa04aa25282e65029450a5555a41c200b1400644a4031845941040318000c002603c40040002c000c840c0c42d40c0e0014000b071144400002101a642e070005890b04024010140e441e40c10210a00c603007591038200039207c0d844121400f00b0311400400200303411000c01c0d5014840c0d000040006c0c1d440b100b00d030a4007048030520180d020071f5034a0750038100c4c0210032010114000e8615080219194507580304102810324020090ba040520018944144010b03040f680022a20159100205182ca0300c07001006813007141c04000c213660501c00d00f88101641503000104413030040f0081d50303500c24a1b00f00402226426658000140c0c480c1004c11040b12050340410500900180001100041c5645248003c5261181a19280c02c00b0801a85058020800c0c00c1000030041c440d888105480d40000d20703500210103c0c80c100b00c450384000c420740d100c0c8000c60f405420344021007061061b00004d042403182021191884040c2003800c640340c1010300441c00d40f4403000c651a040d01140115108a4583c0c60 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 926441348 1250 926440098 926440111
    0x5331e041a07021903030305160c0c03020105210c0307230a0e060702030d080a050604091502210a05042d0f02220504260f09130203010b030709080d0e0405 68
    0x84800c2e5100c4e041e03240a860300c00441c4251004209490302030070180444480038502405d0000302452040000c0c01d00c503032041900e5090070302d282c039401640d0656626604904108800151981c00d00480350341200140d44101c9166456000200c51481d892012107140341e50034200440521511a00c2800f42c0000c03003024070064101818860141c00180c5412110708103200814101c40501c03851680721300500b0352240c0c003950144583d4119030b40d180c04900ca403003070401c0c0417903010a5038510891005903014010b1a4444542407074100406601c00400c2c0c1564101c5d840545c15110480008140f03c102050a00f41080b17808050f18035155404d03584248032089a00180703110032000c01341004001c060140105000009182c0f03054904120400030303d0018951240041c3c80308074a03030b6540f00c1250507400a1130180da4440c04508080341204198141d038100071400400040740f07040c1d56502646c411485a660701e42c00340c0e5600c2e03c0c01d403141002c1101c140020404030200040b800e154008640084 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 926442598 1250 926441348 926441359
    0x50d0f081315050f0609010e010b04033f0f03090f0b04051c200616050a0507060501090f0b0a0806070c051c08060a0603021305331e041a0702 62
    0x503000c1c0030ba046410072601c40302e50031a44001e102c607a0a22440c2140589113002c00b502c2e507541441e2241c43d171030285200003000c1c00c400082850001c404540000500301c3c41d04c90040b2a019a4286d00020060062500000514141403801054840d000f01c18005810590640303c2041c03a86401c1804a0000d1055910380305540c0c644040d40110994510340b011203070703a0070314141480c500a0145a211700c0816a059001400780002c0d010b200c20f03048208a00c3c2d040450b942c4040c054203496500176601c000e820310707161034000104032000d40c0010015000041080051040b003808004100319039001e103a00a03445140001e10300341c00340103803162072409072040740d49044013126122003510840401c3c0e00020201c2c020b104050401128500180c04c1e40d080039820f002500882886504240c41041d22883c4000c200d03018299214581c115040080c4140141021f0500c2c100c100716070020030381c200800009095403080540000540301a210b4008200c10403400c1e08032240950b41000340242d80c0038 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 926443848 1250 926442598 926442623
    0x201050910030227120105040c050f120601060201021201150801210f06020d1118060729040201320d0b060a0c02010210090302030a0f0216060c050d0f0813 68
    0x48150120084d5a9070f0282c201001c05091006000b01640c1160200321580c1c104014800012884c200c2041500c500303035002130202c200400000d210740040e103070079041382c0a03550021030440d40c10b400610090000407052102642d84841080c00e8140041010002844040051001c220302c0705050249500f02e041c03000c131002c1c1ca074580c55460725000700e04032030555000172115109400e1f4010003140310031003071213907044c60340c1d80818a100c44032200c0c29511030840003614408011200480d100041c03280300c1c04800e001c0045004c1f182400064078241d012820400306685504043d01c001d44070300d44080b1000c3c4050034a003946000541240c030070383c42e0564844820205a0300e510026000302c81070b0307699590114807540000380c10104209040e0f03007154141040da0f00440e03000001c46403c40c030381c0e150244042441312012410041413040c07010200c0440240040c00c1d07a03100c1408025503005100b6104130f100305c91001d0383c2054080d02110082034000e00002c5400c0e01040800c03030480e01954141101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 926445098 1250 926443848 926443867
    0x518190608070b120a02041d1f0303030b030c120c1e040507020a060e030708030105010c0201090510050915031302151303060204090507030e34032103020702010509100302 75
    0x802d5800d07000240c40391404590105007056070000d603070b085603012038118070340b60502140c00e800c905102c10a0364401c00c024049a00c17212a00c040e0114110000c04001006441380350007009001d000078507074030904c10615000b010f8585810040310100030400105480e0600790b06001c0034650350480c44440b100c5008203400151120f004a0b03125800d243e0180201000500d014002c0325810390100d07245500030301c906400036105c0c3c4101d07410340c1c4003404d02c44000c0e4404d10040350001050b40160ba00119261611403031150801c02512914004451b1444200c00d005941c920b5800308495116841e01e03410411000350805510782030000620466a43c505041c600c00c0111002180c0c1c400c55405a0010702001008240d00c200c0c0e4010310f082c9000c0c060000500701c0c2d41d0b0f9a0740071010003200603c3c0550300788800c9480c00c1c1040d0b0350204120f084074000e035aa0801180498103202c40022500e003030044010013a119100321400542d058441504050f1610140b1410b44103200b2403034245070382080020720 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 926446348 1250 926445098 926445103
    0x30c10030c02120a021c021c12020c0a080301210209130c0b0c2410090e010f09140d1b060207080c010203190b01020118060203071b03080f010518190608 67
    0x350b00b04d65400030040e0f4001c0d4081c040350641d8204000742150400c0710030103801ba020303c0040040e04030501d84135001e80faa02c40300074001d12510650b41d10510947d05914100455180954121102c00c0c0100300203181c41c00c88600c4240208000a5109102c0e400040e100d0b42c04103c5a803219014000d64844e03a0307183c200d480b0980d4424039407006140d20207201c04042c0c101c1d156405040440314841041e0a041170075840386400d03e40e01800b0140e940715000d1040d1050254494044010304840521011b4000d052000300080006540002c038004c440c20000b04902501a0085149104804654000050300c40701c000390000030302201c0f28070040010b4a481031003400690b0041000c982d09400002f8640c80718021581d0300004203043d03904081c15400c0440c2c0810851100700d41080703000d6070340d075507080c0219440e48211040081040961183c0c10a1562040005101d10604503100107246d80315400c00241108001104075402d145800150501c0030307084100401ca007c0000100d810380d2611550360 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 926447598 1250 926446348 926446357
    0x3040f050109150902150f0d050c0c030703030b1f0801120305071202030909070918020c030d0c05030a0f050408180307030c081f051b0304030e0429030c10030c0212 72
    0x103091312142e0032010740c9003004d03d488800c50b9041485e031906500400c109114042c00e0303005107800350f940000480201c05807045400e180800c0c4256a80c404d0b0a14010b0000d04540544e035018031040340030404105800090100e1651207515041d540f40c0c40d0250840a10750320032011000c1103414004c190000d19041d40d9101c2d1191990041c0d6110610602800b00d503441c0240854100951054200800150401d441031490ba51420159690715a03c400a01c1c52061005003194207141a002c0045140c1c0003000e9406510052000d01165600c0542d07801a0303141564080c01e1141c0c10092240f0a00200421100b0b11a0107401c0d00c070503030303900e0f02c0d9003001034000da0012099401c40102c880c01c500c80814072105400c1d08400811040c201181c40345056590640807011a01c1c1c00404201410f0194410003003110340180203100e4082140b004071866045400c021103003015400002042d40b9000c29840f100907000340c078440c07541e004005c003180980640500704065010300d140589806c0303900790060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 926448848 1250 926447598 926447633
    0x5090f1f030c08102d02221a0a0f080a0b09090f010c0c0f03030207081606060f050609011205060a05040f0c080f010e0c03071b110f0d0803040f050109 66
    0x210040c038074207207106007012444108110340b2450511804109202c1a0000940803090754000b00f03407560305c00b03d04000b8883c82e20920204031200a09281402c030140d05102903818040b44120220b4202000c01c1680c000c1103400b0340403c84c4001099102071140c2c90542c2c2c807817507a48010444034080350214442100950f640c4600d9080b000c00f600081000740520f1342856010b1a0031018003016407a04402c0300c00507203004040540000e0003905019141041d10b4030341d0010520701aa900c198500300b00200102d1058a881c6000c1100024039441c00e0b034151915445c040e122450019048602403005050081042d0b501200e000d40202c1c164995200c5c103403845800743d80001c0c042111120180008200400c2904400e0074030b03005200c3d100d02820a180c106001132060b54132a12000001e03501c01483c030320000e008803a000114018070000302c4011103000401e48070415043d801c44180a03819459074009460710004101060004240c1d03044501468001c0d400020426101c0c0d80f065885040040794 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 926450098 1250 926448848 926448863
    0x1a0f030901051023042c06100b0412120912060203250c0f0c030803090a0b0604020a1b02030c06121b03040f02010f0c0204111201050a05090f1f03 64
    0x10008903411021288000e0401c540d1110f04ca07065101002c51002d2400603a00c0c00759894000002e0310001e06622020f8414000850889202c000f540c60359a0f9841110f0070048000c0f03200c000210821040112416501c0e2212a4050040c041d152070405950481110b010400500000602c541c101003504d07054502c203c20250f52400c0c903032281074030504044542c8102e4003207a00080401500044075248841e071202d0f0329105c0300c0035810940d42c000c41a03072026003d10300010400c81d80034808034110142c5482410007018a03247c640600c0201d000d18042400890841540071608002142c07500b160a80f0040440b611084001c000c00c0450b0000442400011500c005011800f46000e0503030805c0290f01c0226400c1d0b07e000e4440380410350241102074140401c0070070110005108501c04038210360050018070a00303480d0348041d5000c1e48807506040c41140001c0010581d071038003560f40000c4460082c03624401c0e403102e0000750800e42e0081c04180500da45607030b0002a80920b20342c16002036010310741 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 926451348 1250 926450098 926450101
    0x507020304090f05010608011e1511060a0b0f04110408070f06020601080c06030a0506130e07090b0d0812101a031b03041a1506030a0504030f0c0c1a0f03090105 70
    0x306000c0d94a070f840ea01080c2414030f00140302503035110700e0341411120205031030341c0b103505160140d21500708580c101e8034102c0304207019609800d03004159032082040c50004c50304a40e40c0c980c51030044070301591400e0b6008c0c0c02e1071640c0d20b440c0303041e8215070300c0030f010441d40070707d060ba9403c0303034500e4900385620207071200024a508014058041c410b641c0101802400380c4000c02c02900003134003511009204140d81c69803140458101e840705281c0003440d02070070100300181d02d00c506040780d81d80114843c12030090b081a07a048102e040400b1004490796011041c04e0508041e442104031255005140d4042c02c41c0f002e100280b084001d004c1003412140e5512283c0d0b903800c11100e2040303160124115001c036480104180030000300006d90904440e40f03803005103051603c540030060100c000c151340e0240d1095010040c810000100c0d80014001ca2084d01ca1076114443c1b85800c1d10900110740010381010121203040080400d001c203001501050300c41494a045241d203201c07401d41e00103686514040c1e41d07440 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 926452598 1250 926451348 926451359
    0xf060f030b18100c03021c1401080c0612151f09171b0a180f05092a0f04020f0a0228230706020d030b04050f010611100507020304 57
    0x998280c004441c01c0890300036200d5025050b5641410003e41840c5694452418440c54403c0d81900c4960106170b880d02c445120b01750080c000703800724008901030029500000119101c0000d00c2801c50b200150415003003511030ba0802c00032100040c0340e050034000c40085030034181c2e56207031500d58507581c01e00d4a0324902018035005024410340e400209090503070000b40024140005208071b24450a00300c1440b51140190101c2c81c100c2d00b5900120403080803416121040c88180c018402d280714041040002e0754441481a666840300c4607510a0f44000350b00d0003000c1c010640c901e400e2039001800807040942d40e032000c28100c0c0d0003190001d21035076001c994515002c2c0d05000312011415020380100c4d80904401101101244000004040500d020a00c0b030303406c4469030005003075002c408143c5203d40e0341c0b450065100c1e0303c018172080003e45440041b10492400344201340c003444103e084040d05a01300300090790816000d5042c00100d104a2107192003e808602805d48039001c550301941e01d4030b1504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 926453848 1250 926452598 926452613
    0xc1c03030c03050c0702130f0e030904110406080f07050c0303070509040b0a0308030a0c1b051c03140c0702030a05060a06080c0108091506010c08070303020702010e0603090601090c02010f060f03 85
    0x61001c0d0007010f04010600c0f500c003030781e03a068980064040fa20900c00d4a00503810300e0041290700e59074402e803030500f03120102215011000d48511030056405001c020070403d841c824a00c01c500520011030100c0380810040e0b0746c900c820b00d0740049141819860302040c8030510780765070003c075902d50016600280100340340c1414001c1c5800340d1002c0c0d9184001506580d26078119001c014500394019a403404400005846030b0500d02c000e8400c001e2224a03590141002c40d00c6456082d80102d00009055519005038403910035401c4208220a40010680350140c0f9803c0b590312180c41664103101d02c0c4540e80c040b030024400f146c01201c120000041d0350341340c8005582070101d0124800d0501160a0030884c1c10500401c1c1000800305401000e5603598030000103072010002400081c10138000400d8220030960035500030034061b0f001740c960208003000d9400b00004c41c0310480386814280c1000f0300400c1402c640d9003025080280900021590708040c480483c1250740d00e600c9000c8000b42004100705210b0b88 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 926455098 1250 926453848 926453861
    0x50313090c02030c0a020f0a1a0a0e010914061818090106050d0c0e0606070f03081f030210211e11130b07081306030c020d05041a0c0c1c0303 62
    0x201d0010710b00308000101d845854800c4410087c1c0154403076000c1c210f0690398041c400000e4045880750889000070301c149101c140d0440064640444c4610304029050b40c050714510049171030100200040120b20b00c10b1003030b290055080700e683d000b69600600f0080d40d8040b020740003078210a00b01c80480c600000900d007901e00d564030540c0600c41d504001e40108000048060940e212455403042030303181d103000300c0c02d60711030f6100c050806806044c220301010ba0181100d03000301c60220401035094080b8100d109848201e1000135404400700250325030319409809846032824075464540c0307509001d44442415120708c0f030401035102c0e80d0034100802d072030500e10501e80da058000541c1805c248200c5a9001c6018441c046c424016401090356010043c401049607024441c1c11103c400d1541c0d80d05c00030300070b41852409203025000e0852705005a610900c1a1403c40c1e501c158084050894035084c01d5195200c0000700245014a100c029181d49401200030030081c11302e40d801c02003d01c1c41c20024100d580 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 926456348 1250 926455098 926455121
    0x6110d021b1b0a0b0f09120714060405130e0705030706030f060b0f03060d14030711030d11030405060d150b09270714121f081513030c05031309 63
    0x42903105403d444001100c030a03956002e5204e50785903804400d04503940244c4440683c0580441e118103010707200480c03260304035100c221000d242d50780c4a500704001c0d401540500c507003040d00c0e043c0a44404441c0d41020030309009220607103c0068442c404a420811280c10410101e9101d200500a100261142c0c00c014450210003509202e801802494181310103001188125032400c0c0c104144440c08685826000040c0101c80d9589642d00c2c044078848452003206103e4000c042030401c0403405107811400d0682d6800156140a0030502000b0080d040030000014407942c0e6203130b13206800000701d00302c070191050801d040d480300f80340820001030700b101c42440f011000c81c1031036107040b81c3c410350070a940018031824103c0c4400c49045208407140500705450094111a4080c00004001e00303510508200440c520801ca041d20b0782413090740c07580400b241c2040042d61900040c40001c154144c07168070b85c820f2a200304a50f080c1d4032941d10b5074210601c0c1020190302e200040114490f10f2261121803031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 926457598 1250 926456348 926456383
    0x120e013f0c0210090f031107120b0f01090507123209010605031b0108070c020303130501030b030703050a0b060109081005100e07020a03032a1d0102010b0d06110d021b 73
    0xc0130359031143c921801050004003484100c0b144160361a00501101c40a0b04036940f5502207840d82c2d052406140b8002e0b50451102c0d0114400814661102e004051043e40300f40c5442c40f035045103c0096000b031000d00c2c800a0005009141c01c941d10800c0007041d2025000550b581e6024240982e049007101c046901040c444e61041c1005910340c458203103807900310309090802c00c40300c0d5201c44064881c80c1000c50020b500d4040002d41d102418090150034007a602c01380d908210318a0144145981c813012800040c0c8250b000206140016907040b2411f0b901c80010b14003009540e85d00e003002807800300010101ea101c48e03202e80c104070b060361403540040c0c01031031081309050303a5040c00c0f580a5240c6400c02805410151641c0c26510302c4118015010401100001d25042201d84c40c0402408627820801c1c902d0b403107003528803150070341d071050044401ca00da009107200012501a030b218001030400c038612801011003031001010306592480501083c14085100c0300150003003400701c90910800071a00c4a042d07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 926458848 1250 926457598 926457611
    0x5070b060a1a0a0c1401020315040e0307020609061210031208010f0509060315070207031401020a0e01081008010c050316080108190309030f030309120e013f0c0210 72
    0x40c0340e404449000b1040500c005a40b401c00381c101300c13800303400341d18045c01010901300d0715400100c0541c015440b80310310f00300005040a040003040150750b40c280c20203203207900c02d000031005032a00c2c0b00288244800244014682181c0c00441d8072001000c4511000d68880d120042050080300502956031040c01d140542c200d60408040111040550090358010300c0134000040098070208240c01c410b01608503680000d00d0100390095952047d40070441e008001e0f03952000403c10140266200040c403a240c840700ca40528004640031b000c0240906000b00343e040c00020152028858003258602c2c0c1e50742e80d5520303d031040c00314880a041d07007214030401206800421075400003096001c50100e00001c0c104140c1240c2c103040b00c10754030940000e0020b0710800404802c264041d030000c01302c10300c10490354140700b184c50410355510700c04540d807901084014486110100502c14030060f01c9500c1d41c1f40c0311160300356803980b010705900f00079800b030500c0d47e8100809020303404124180d4400410141030090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 926460098 1250 926458848 926458859
    0x61302031504020609150c0d030b0d120903060501080a0b15032d0304150e03030711090612060f0f0108010c0203040b0703140304080d110403021c031e05070b060a 71
    0x30751000540d001c89904900d8085030031540c07400700312110000014101c0c0701d515562010609075074450450350100c1d104116a45003510700034015100720b6400141007000c82c00b200c2c0c4585400e00410841c6c3c03010099030240110021300103101e414041e0003e2001041910110b00e48030f008030078040c4c8008a11f2101c0344105038659400200101244080701107190343d481d0800f95162481c0205004401074000800c012803100d100c49188200c05105030381d10b000d0b00c015501419203901c10860060498041c1c545141d0355818001d08550b00040040d04103040000c441c09200d050504c151440040d40509000323001220201d0441d40c0c0c05010160000c121614a000b0082d50344c1c421489445c50031540456440181401103c171400b0b80c01c0603280c120b030b891900d07180003a03003940002840d1449030702d01024580d020810f0800e03501900d0b40035080402c00d10001d00c506081c2401c4d4181282004421203801c040340041c07403454101d00e0016107071a074036001c052030030082160300181214080e00601504000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 926461348 1250 926460098 926460103
    0x10c020f0d020102014107020601060c0c030215031b03010803070605181504051507050d020c070807260109021507060b15030a0c0201050123010c02090a0501060206130203 75
    0x19010403150107450200610050340900a00541c201903040181c0710000d400da212205004464a0781241c00540240b001201c1340200e030584a080060b0f000030010300030180070b00c1d810101e00c4d000d030031a100c4a503601e81c000342c600c0d00404100940c064012091100291140702c0c8180c000004040d0380d411513051a01c056034901580e03a0240903e92100301055001c40403a8607007002d016035006a44031348003200355140300188166411502489204150b4000c004501140e030b004204035981c0e5850021001558000307900040e6207001a030013240340014120300c00700520320041203880b01181e00c141c0b0104640e803820004c3d40c55041031b64180b42c014401681c07480100a0150313202c412145c0c540031241800c0b401003400362040740d0030034840c3c02100704607003855018511401c8130040502000c6e0104d5803ca00fa52000c1c030401c42500065008519034150110100801501c1894507101136241c0c0d400042c0e8000301560950415585c50f0b006108195041c4101b541c001c540910b004050f44080c0d02095 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 926462598 1250 926461348 926461369
    0x109030308150103020d09050a0b0a2049051005210706050315031915390516293d180207120c020a05010c02 48
    0x507841d035103520b500c41d01d680c06a4151603e090f01c0a6042044013030340d182596850f00d00000640380c05203050f0005a0501050164142c2240c402c00a040ba503c0c10a0720000c69400c00d1150000000c0001e25014885000d203422600c8441c03007070f107060b1401d5104030b02406003442e03010100b05803c0c2071000700640c0720f03060210403003180d000b038540b0358a80712900400c03940101e00003a08030b03040c0106900001d02d40e502c1005140180c81580400c4100c885100400d42d60324a2401c0f0303500082c03001801c40011445034003441c4040d4580d20004503006049112040c40a0b5408054003211400506500401000c0084040300d0580e68140285000303c143c2d031200342c036010b0720301c001e004900070b031420390100761119541101d007000030000d4500d505056044a00302510f40c029034401003264660b110108280c03180700b0803c10040302000c95410708040c0040d1107001080f070050403030758003000640002040c1c207841c0384800e86d10342e684654464891041103807070b604690249040080078105000503a0362a59402c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 926463848 1250 926462598 926462611
    0x9060504120807031401140301150815060a0e07030506210709111c09020102010209091905070905101101090b090f0f01090818030a02040213030501061725050d0309140109030308 78
    0x541d0184007c0000e0140c0f2310300c03901d407582d00c9151500040e0140c001074403c41c485110a01081c0e00e603034400500c01074032510b20891440004050116084a009500090304400080e00813606030f54900304450381c02401901c091764562200904000e540c0315803041100070407009140c149452001f50b00c003c2c0700035444515100b10750307440391440216030003541114203044014180304100e141c108407280000c0700c40c030100103c3c40d0400c000207102c01c1c0300e4901482074510050080142c40303d441d00c119011228a00303010013542d81d0740343d0340010803419168240300390703c1500140003868078290318030b0030300401c0303020540c09038180401800042d0a000c161a8241601d0100030b85d039610b0380000a16004110344040e41181c40011141c0e61001c0769a0000192400740d4020704c01140d98400d2804911014402805250008111235202d111a0800b0180a1300000341111013140c40d880040c0c81c10a00f020101c01080b0a003400304282503820900c001c0311002401c0654543e80703152000340c040c42c0c006042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 926465098 1250 926463848 926463869
    0x2160e0c0a0c0516080d030c021002180306270f03070807110411090a0509060d0206030c041a031806060a09020d09080412060b0d1101050d09060504120807031401 71
    0x4960191040000c02d2a00d5003141c100da1640c58011010565540203028000140c0617114040345501e0003401129040c4074103a00600c48000c25802010094002c8043c0c80c1030000454203110083d40c0030064640240c0f1101c3d64000207204000c2070f503d46200072050520503030460030740358003180404419503c1007500a00d20550341e0b81580b50032618114106003096015260416580c10a540c042c041e102c01401074400004e940d498504005403602c0880700103601082c1b18520704018249040130b181c20060311100b03182800d8541d15407d80351400b615000e4180400401040840d5003020080f55001d191080503041c581007407404590012070b0381c00780300d441036000540750307000b9401540000c1803c0d03004a085034807141c50f2103203060846039001042d1016802c0464051544c94282c8554840a5102e05c0d118090214040107440c541c21a00304520459580d05800002c03507030754010148680e02c0f0b01c40c000d0178028128070103040c880d40035115404061801d0405020b50078000002070540c0c004024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 926466348 1250 926465098 926465107
    0x2030c090a2403050c0c010e06010602010c1803110d080d050901060e011d090c10020102070c05040612060e0a0f050303040b0a0b01020a0201030b0604091104080c031b06130803040b04050102160e0c 86
    0x880166910031b1200f140700c1980781c402c03410032012020605605a0364241d000344041002003400312036000480400034000c8403c0d0804000241702001d00c82c4909a01a0804141c00c0450b00d4420b100d800c4001191034468460003080070180080c803805014003200132000c0c0055040c001a102d513900e040021840350350100c8007203503101500304101c6160510040c00040c8500351540b001b4045d41120310122540300495801048a00d024002c890030ba98021004910310920b94942c0e001600c010b40d0201c003180140c1c4e13403400100b11800b591041d01c0d4040c074000c40c0c1d85e040c00d190100707070040c005220740002844c202d240700c071903a40492000c04458092030046039450703480c2d001992030b00c5143c3c0f005032150719000a03400b82d5000140500112000c04090301e4640c3e50400038561941842440746aa81d004150038803000c1c54080013426211080510f0032500e1502d60714694a141d00c82c0e0440410f03048c000c5403c1003e507034100680701300007805210805d002c13840c004001107940300c09800c4400091010a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 926467598 1250 926466348 926466361
    0x80904050907180c030f09050a15270b070903030504091112040506060306070206090706050f0c07140406090b060a050a0203220e060103090506070806040603020402030c090a240305 79
    0x218050080315400c82c4070300c8110034083c4000c0c02e01c60302c070801280c204003201c45001894803a0541e0103030844050401001c80795140b05025406080c0d01613500d40c0e40c550340d07405410014402c209041451811042c115607800d0401c04c03004020036800030081c1000040c0700080c4d0103400d403030454408034000b05951000a98a100310b024642e01000d03003039543c100300024824006040d40c003502d0181c0c182c0b100d649230110100c0c1c42e11012241030180d0b80c08140200a8148210024008074681407201402d07d4500c20000d402c1000b1130b400f4040311810110326116500d0203210315002000511002c0200c0c0e80c1c114013180190140002040621501280741e4401038003e20444913000d13035400b040c0d043d0382e02c50024880400020f0003030104030002c490000304103500030302c101c0040d260003100a000503905c2650485000b0f2005150340d0b0015140c0710004016140c500182d8000d60716010090303100c0c8100310a02c612095140e100c48010f810450b02c0740c00000f03071101d81011304800c0d464003141c580d840c3e5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 926468848 1250 926467598 926467603
    0xb0d060b060f0f03040b0906040b1306061205101a0d080a17010308040602011109010c02090907170c040e03040617060a03020a06050a020d180e0a14010e1009090809040509 75
    0x5042c0980d10480006a2100980c00c2d0341c02548158800c03039009086896a49095a0321242210010b042e26079400109a22030707400003840301401e105060104400780c641c11650800c44480c0c8085039283c3c4414000712080e890360280da1001c810b06110404042a001c00040c00c580003040017401d040030000e000f0b01501e1080f00c00000642c1c0441280c505940c0d03901c1c180281d41e01a1280c070300194a0002d50100e211b500604031409130b54140d407000c0f0601c460b6000c00c4500600944044920300c20550001035034916894143c45034811078000c5c0803000c040c43d090100340c07489040888150741080005108603600f002c1c00000e8007400c0e01c86401c0d00c0c0d40317110100740252242d40010354085400880020034503446401043d91035025826601c6014440302c00350350201c2025a80e211101111b1011311134804d41c00803d80d84a100d130780300414101c0000b03603c0350b4841000e800100c400a01d40080040c2003d40d45110001860014000c000d00090798a83d02d20724040c0c5801c3e80e1050b0740300e5003c18040d1404 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 926470098 1250 926468848 926468857
    0x6060f1809100311010f0509040c020f0609010b030c101403090c150a02150606030c0d090c06170f0c04050906031609051e1e0c21010603050a0b0d060b06 67
    0x54040e80e09030400c0d8810803100e103020f1004441c240d140704441d0109511404954820341150b8880a0503d0791314420080940789071000c22003140302d4011701007224101001014040d00e100c0f4000281d0300d94010515003807505110a0900412a801c0951001d0f85e221150351031032451007030515166201c0248490602100d488510350048218170140c1203080c52800800030003a1a80072101481d4085038010a209411992154450020300000e03003510b134054010f0240e0004068005845480365845c3c0d40c6809013030f081728000849443e034003401c0c520f025040d103411002009444140789414007280205201c3d42c058035000d50801000719007503481c10000d04064900c50314020200548030707401c140c0181802c40b440b040e0200071400044c69003c2403003806009881e0005a04541c01e0355085800351410041c01c1d00321844010008201006400c254064041c456800d9002041d40341800040075030f000904680d1013580b812032481e06a0f6110031032840502d91110010039051400c0e0f0000d0994045c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 926471348 1250 926470098 926470147
    0x31707090905090d0c080d150b0301050120031e070503030a0c020c010c08120c12070c0210030e1c11030408070315050702030706020f070f11040e0606060f 68
    0x4414091089268010300031000380c51038100208542c2d075406200070f6451601c0003680700400c00001255003c2200340000b0b12101c00100e9020502c5215126144c0031000e042e8400d484000000c03006001541e444001d444080c034214000e8000340c0c1320052040d032032340f10b0f4071842d608800c108103a0592144500c800c0d04e42132074100d0b0560f5120314107049035001070240201c0136001030058003956821366014451050445402041e803a06004900c50000d0f40320501034289104943c0c00c2c00509030010760000d560340301d03000c66039411074015298410f00c070182c030300000d413481414101201c6541060f0005141201d40464600c42500c02c0d012840548016409544050003800009004039241200081800882380f10703055090760861072460141c00c4540c00d5402d0390068100b0800c0310085001c40c0c0180502c03100b00d40840703160442d80c0d50f54686807603582c2403c80e4800074940c4840c1c1d0619061240224065403140544181e00c3c03e82e0000365648544840000a44000320300400f2649021010141c0c038179 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 926472598 1250 926471348 926471387
    0x2070c05040914010e0d0c320708150f0601051e0c0703021507081e040f1508100b09060a0309320304080a061107061a0f04020408030a0c03 61
    0x1542e5040c60754441030400c0c020152503007824800c0c05a881c0014141c0d00b0f54805648500c8100b00d03d542e180c4008000c41252003075014000f41d903544401c1401111101c03400d00c40001c104c00c501c0d0100990030041803d00d0509003000b03030002c000032401040a0a68004001d2a00d03a54640360b0031a03403480c042142c4281403807080d0204075070f1071007100019194280c83c001c403000500c01e01502030006061007041e00c010005042804000360040c968009021421200340b580c905090726218800c40e4502c00e980403401b000d400d4015400801d42200ca203507002807c4401360400c036810304016000d03500c01d840c0107d00801002031042000c51090340728862065018071003011012407443d44040301100703000c0007180701c20740000491046200000700e0342165401c1010b41102d40307244d110a0010300c404421941000010040800054000d1090499032460440d00160f2800303a1010700c025802d2810a0030f0099204102c2442010b1000040d1040c0454610302021402c0c07140c6000c480071415501a25070b0342 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 926473848 1250 926472598 926472611
    0x1b120c0a030c050a150b04110316080402030f01050c0307031b0207030b0c0c0f030a18030c15030e01140a0605030a0c0308090f0607110301201204080417010b03060f010f0902070c0504 80
    0x1005c15401100382c54208031001c1c01070050001668049100c00c0c0d52800d1884100041c19000c140614400c0e90b00c18001400e465010215414403401e485040740c01400314507000040205840d058030a502456082d000804850059494087d64401603800042c0c190b903070f003400083c010120345085501c07548162080c0d4046240000a81c2c1d9203801c540300d194081600c030055544200e0410906500f140e0300045203540f80340c40c058105100d010140c000008064641d64088960741c001d02880000c000400e50014551070040c940c1021219283c20003032081d0845081440810703500000d21003902d402c0b01d0b00b155581180c00000e01c551030000d04154214002040010501c40c01114000b405103054000740201141030803456036420440c2c2d00400241c1081c06800c418020a19195a100c0d01c210350f400d2074039840e1100500c40d10912a025601d5a450b0301905201c1c2c1014403a00b50407406280301c0c140b00d541000d000210701545400b41c2ca030107035408155101480410703000d890040501074400c0000c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 926475098 1250 926473848 926473883
    0x7151805060a0b060f0d09030c0602031503060a0c14030c1e0d0e06100605130509090a051204050609100306120327150e0a03081b120c0a030c050a 64
    0x880e041110210b0070300c1d1a10300282a607040640032100700002940d501840c1c910314510403001000c1d2000300360b04000c080e54202000404c50720085001d1850342c014441c11170350700e0040614060000702014401400c00300721807240e5400c1243c454501005014154488d640c605249a45002d081c07030940000c00f09400c3c1d8128095860001c207003c240c000c00a1110002d503107071590b81e4040a503001350000300c01520410220344500d001c2d040d100700d5051050000c40e684c400241c0344100603601c41c1c0d1280c2282d5101000c1000420000840c03412060020f42072525100000c2c0e000d0188100c15800b0301312550002c60340a11962020740a0412610550350441e02410700030546000482e416102e56041007040300c4035507140c0840012180703100f07129182076004400c100d6800303150b09540782d08030352010380210000e40c280002d000d02695144c4c0b2414500e0406a003d8a00900c1da20b03c00701e00541001011603001c804900c0380005601410001c1d281542454005c0c602280004040d00d00c0d1380048602d00b4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 926476348 1250 926475098 926475103
    0xd0e060c060106090e0a06050f04090219243608010509010b010914090105040f060503071202190b09061309090c060807030b180a0e0d0201020d0510080307151805 71
    0x5e840030140500d072699035480e4160212070b990b02905a1100341c3c041c1d5102149007076017015405601c00752141d001440d4407800c0210b101802d4201490903a02c0281c2c0f25140c0d005050845c0e05800d20b46805000303100e41c03c10241034035007040c2001c075003c904402c6844004d55200410700050652100070440703440c2003100d0324001c07c0300800f00e0b4001181c85000042c687c11200c6403000420340202200e025902e0001000010110f400b0303040c6120761100000109650140500c800a0070001c42c4c401c1c0a8030244104a0912005543e81200442e4504140026510042650100314003503c0c91990f0328401c5170705580d004003541c8103124031410070154200300034a0712040d008950301a10303603c00740d890701e500650a44001406580e0007039003041c4841080407a0f02e0403990020b254070400144102c2ca1521507003015191a40c510142c0c2d0001401100b42c1e9413481150b502040d90040030944a003480301c1310b6240d1081390300113000da01c0d050369240010030303075540300800101d40440c5002025016180668 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 926477598 1250 926476348 926476367
    0x1140d0203190201020606060a0f18080706080105090f07020601031403070609111002062e050a06050c1603020d0b060315070c06150f032d2409050d0e060c060106 71
    0x4c0c014043d031004034289082003000d81d140c04400341c803407030880804120100c40d9004580c840184051a400000a64500c24031842c0d005e0840707562510500d60615052101c5404094100d642640419003000015035022030701c141542c0d4170007048014103090540c5a413440c0a0b9840213011685000810340030040505804500c4010944184585410b448000c0e82c44070303000c480f09503001d1901c1c0d01c5200e26400713014404441156122000302a25124800701c0d1103035206400400105200082198585408101c050000302c0302c2c80d08108003500710340c0480c6452040200007003040d40c032900440c0c040e0740c1c2401022000000c0c1240c40b9000e181c424001002022540d9040d9651860451583c14000b01e0001300800d40c1c14254149079154950b640c0c0903134400100c45941003c1040342d1401c4624000015280d001500403400b0b100134051914582c4519803803160f90030310030780c6003843c04400141d0100d0480040100b80c10540b24180118003c03540510640c05060700318000c110011921603003014100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 926478848 1250 926477598 926477603
    0x319110a0810051e130e010c0909051e04060b10180603050103120f14190f0804020d170403020619090806010b04030b25020a12140301140d020319 64
    0x240c0691103441214820030000c0c002e09401c20075504840340742d03640503035140101c01d0b001742541e0030409503000c15404441d0107408228642c1d4681c16000402a481031800010709200b1400304118203080d030b2243c0c1c0c0f4008010030301d04448043e6000034180030655001c1852854040d20351241310500820040c10341c0314402480241480310784000ca111842403103618143c95202c200a850070b461124290780d140303a10f030140b070700b044441a54a54003481040107081c4015a840b1042c65140300050702411003114000c95508001e0705004000141c0c3d034145081056a820500d9004880326031208840607204681020303402c00c6000403d01003c08403121a201148542d503280305000c0e031075454a42e110381c001e100c1c00c010800f05002c10710200e440d040c030840d04942d14401010f054a0381903200328088070080055405600084000403e212610300c00b5100540e9038500000651404061076005010600a69842d210362011152168031803454200a4540090032140a0f02c61514000c0d40d62941d071408 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 926480098 1250 926478848 926478857
    0xa1e0f08070e01050d08130b03041205030c0a18050a120c090e0a03052a010903080105030601151b02040501030516050f01051909030b100501091d0c0319110a 69
    0x9803048010410030251842a4008400303030746000c0c10090074001005050310035a03020000800001d1804044400800ba0103131120340320f04e440d08022800c43c000900304d01c1484010002c0010000300441280c600456034101494a0607202054905240700c0380c210075041046002d0215004407285601c0201c0c5100e00184120720b85c40385240c00580320511410000b60784000e440d2000a40600c0207081015640c1000300c1c1083c214064610781004442c3d24007290380d42d66a003645c280350307000c91141c6c054081580101441c0d450b107403a00b0341c0c61103510000b80030001400f403020f000036400c50150036036540051060180e1350716400d2481d00c03212406900540411b46400001341030601007800c5120b144143c41f11810f0480401851010150b0306a004080103054180800044c04004c42c2c14003400441ca1901c466a00f04000507010030902e40225007a800c91046114080c0f80c441000e1b9804901d031204142c0340e850f00c400c0034107202d81c407000c1d04081608103040c44418441c11000b400e801c094035070301c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 926481348 1250 926480098 926480129
    0x41217090f100e060606180a06030b01020f06091e0304080d0e09072a0218040b01060207140a0b130b0706020d051e0a05150402040e0601110d0801060e0a1e 68
    0x29101c08850302e43c2c4546000e90802c000050140c034100002d000b20b069132004402440040800141c00081d59400c160080b03a03850b1510304280d6810400e00041002050042c80607081c020318159882c10a03c180c10b200400d50100c25140d180280300780c0e130007400790740c00316035900a11050240120008001050003038080c1000a0450f9110711604030a1401e04600c186e80080841c0d8032561040c1420300980e0002c507011100c20781d0700b0410140d64403035400f501c507080055041807030003402d20349654000803011f42e440c81003030340c1c42d030b2001511000c595815804568840b0341d0f840a0f08200420b601c561707081075021582e4070070301030660018003e200301d0b410f04120680e07d0141942c0710a504120b40d890a2400c0d000082e5800015031003160014a000300030f0011500500004090b0792090704907490040030b800c1840b2455030007001213492501c0c0480070304181c5141a00081955005101e80400c202c0615590707070b040d403114400440900011000460307001059203050341e030b02402d44110000d56042c0710 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 926482598 1250 926481348 926481373
    0x512040b073f0e031b0106060518090a1d0703120f0e011d0a081507110d0c0804050d0b190c0e01030207060e06090d03050c03040308041217090f 63
    0xc0030300308011105429107200302c503601c440c1e07620b50500201007180302d41d110b040111404042000d440b07416545140346505011241c0c4403030944035168019001e0007020b019804581130466440304120500b517480f40300981e07590184030050202204000c1c1031614070a1003101000021038010103480c010311803c1181c1c000385004884040e45040110009114a1402101c2c0d610801e4420803441d098131044441c0c06403000020b174003c1c0c07240d020301565405030f0355041000789000d55507a031040c6542002407145c51401000c546419810741e542e001c01600c190040e040107a258190b070061b05000c2c1a0019800103071814171103410007521044882400100505c0d48540c03d4064252003186130350758031484a0307485005501030b40200008403101d81e210340c81c50710109010000244140140001030003141510304001c0c08440000d4500e14040504004000109412000040d0025841404400049107448084649a510709150100c40c100f00062040b6a00c000440d4901c0c080c0e008150f404914528 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 926483848 1250 926482598 926482637
    0x60303110708150a050403110726060f0c03130b070905010e0a030c181b03050105090a021806160c030309080c03070807090c090b0c0102130e061f0512040b07 69
    0x19803681840c04407000001d00d13603040c0f6001240c1103440390034040e05a134040d010039820a001c64110031034000381d4000841051a0100d030445c901c862038000740c115400d1200e21112128001001c50801c4a000004103081041c64500b94507165000a40078440d428450301c010540c2859208040c00103000510700400380c036228069104803036212040400583ca4400c94410380362980c8503018049076118800800b80e03440078510012a0190364001495605000030800714043c0a00325070100e034414400640303004408200b035004140100c410585904509100c00504034016200811b810f21510b400400c15801000b042c00350750510040d10110f80380d030801e1541e284103501c01c0b229680e0241e0350030444e52920744c4c46543c855034a4035101160b2a1115200c04450b80151040151a0b50000303000340200305045004000d840e005c68004101d0501e000058100f80c403444864180420034806240e1450080c0c00721440100c1a6540041c540340604114940c004200c1e44000403900c2c400740c106008800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 926485098 1250 926483848 926483863
    0x10908010c2606180a23010e010b0418090c0504021804110a120c020c060c0c03010f020c030702150904060308070204050a1b0c051e06100609060905010e03010f060303110708 76
    0x107850040103c000502404080b000a172101c42500d64921203110384010110368060040341c42003401340c043d45010b40d001c1c0364000503400510740440034001445405424014031121041100001c19009000d050001052070b03280c0c406940a4030010700c54100c00100e0300c04108581049600300200d4211511001c05480f540c01c4a90014030204661280340380668041504000a44100e03503602c0d0a01b030204000b03034000c0e881c0c1c000940c00705c0c1c810304862400f40100038650721000300550a003058454000d90324003805000920618049503444003852109040d943c088000030070500049641f420990020750204100b03038012801c00000034080c10490140003c040010310200d2000c410b41e0804649100d6981d4085401e030040c1c09400701c446217080c0c801002c000c45c00c0d0281c003040c101031a0040000c2030650100741800241d0204002e080e400c05e02c3e0000300e5001307017000e5208002c068000fa0040424030601c09038540303071100210500d9070004011300b01c14000d004441c29035854007280c0e95290407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 926486348 1250 926485098 926485111
    0x20f07140111160803131a1f0501081602010b0301020d141f030b0705070803010923070207092003040f03120204030f110301090c0312030f1505040b010908010c26 71
    0x41d44003603100040078640150345c0038100b4144481e0030f403c0746c0d9460f013000550032041d40010000703005001e52384101c09200040701c92610007204009140000282c0220343c01070900c10505569800200b449000f0340103070011680c000c0007195a0482d000400d0001c0c03540c0c0c082c0144904455000591040c4120022820070481c9003041010515582e1088204480141b0300f0040050a014090000310030b00083c6010301310740702c80460740c0e1114000d8080041d06c04240e44000c2070036242405600c0b50046580010b4502000340851041c0041c0d50440360070105103039082d68030b44c00000308810f1004181c150522544280c2d588005801d03014800f00aa006501015024180c008500310010350001c0158007604400750010819514913110549103041c0b40d070095524003603e04076149159410b104101090b074a486040202001107c00c04001c00d4003805254000c9540321807401803607019134483e40040400d0350023442000b0644c5802402074000180d2800200e6800c000c1c50f00114446040d18414507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 926487598 1250 926486348 926486377
    0x12020c0607230a0804091a030c090403080916030602031005180109090c12121116051c15091e0201020d0305060a0918210807050c01020f07140111 64
    0x203030300314a02142100d801041c4842e41c441c1100300c02c000b51860000c1c0c0000e22445000148144071400c0c0790b03000c4207095500c40c0c402d42245004a000d0399412140b50303041505843c041c451b44d80d8a15000d45480e400c0210f1040d9084907080c0041041070341d070025489405c101d2003024103180d036001840401d4400040c00c1d500f00070b41d840144001501544402c08050281001d01c07501540c520810458046000d401d0315011a02c01c850391280d80c002500c100e401c10030800412410303120310485d0145c0141070003a580304680c01000003040348100c6030740c0d85490750854411000044800140e8004008025003211040d03000c25030214a1040501d0459a054042c0c003d03010311500709004400809000b00401d40c07101007aa404141c200040c41145608051917020f0488281329080084003102c504070801c0b2110181c2c030100103001c1e40107000c29080041400d10a40300c08103a69002e01902844400d075030640c1c004a10786080c00f244158424580038010001c01c90903100c0b02001c8000e00c5030440b0140c150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 926488848 1250 926487598 926487623
    0x50105190e0c130b1c110306060406140c01240503010908030a0c0c0c0902040e0903090a031407030506151f1b050c03060c0702090109051302060a0e0a0312020c0607 72
    0x5000000246a540b003031032000d00340c0f9034407800905526003000c04403c5500d01540324602903d80684902d50704440303105c0f6403d04614292000429034403076406030100300801403400c401d80384440010380b07615150031402800b19850b0b1605000380d054242c600f01910702c146035400034507400c0621681c0e6026403c0034031a840c6035941c3c0d400c0000381c2590000b40040186040b61100070500d052010005072990002c0542e5030361401c0e81903640040d0151400800da0800c00c64414140d403601e01c5c1c0403c032039020103007080c0643c420100030f00f04080c9600c0642075020715400c004044071840d80c0c0154020041f101081c01c09030384e4118100c1d031860f01d036910020902d40480d107400c0f1622100d0040c03106101c0c4c0104c50000c155840807a051000a40d00f0301028400854a0b004514104107024050420b15208122a00e4400114146400c1031203000c0d00441c40020200349a600c036207002d50150b5006030001c0e5080d42d89240c41c6000c004500c007100e0041c0128400ca51070f510b0840c1c11aa070303080c0c0014205198 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 926490098 1250 926488848 926488861
    0x100e030601052106070305160509030a06110f120115020c010c03051605150411100206060904060e03030f0403030b1905301f0b1807020c13050105190e 66
    0x201011158900305224000780f604010602004100e200e07005556011440c0e08140310009240320450b008a030070310030203200a64503510001007007801e482d0041030114003a001e200c581e02c45803041500c15600d03640c0c0010801e07003001301034a1846c12580c0c005203001a00b00184412a29000c02c4003d15000640c25040040401d10840140c400850030f0010000d00b103036250b0b146071030000009003645901c1001070410061101440c010360805c41e051340d1482031301c0030b0002c009480308001450148501d180302c0c0840d09001c019400310242d0004582141e640b41045581c100300d00c41c0c2218214006420419405070341d09140d5241c0c160f02c4801100c0c10503a60405042040e4100400c104131010b0520380c0038003030460a030603880c114440ca0200542004a0074080c0404501003140c1c544082034100f8041c5841c6e91201c101c500300c000c0d00451040656107403000100e05041c2c2c00d2031080d6224060481a5404444950216040b03038400c5410001c0413001b114145074081c1684550f504103021031002946 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 926491348 1250 926490098 926490109
    0x301080d0e04110c010b091024020a0f0303020d060503160b07020f0301180507081218030703020a06270324060e040c090b03010902060f3402100e03060105 68
    0x3207000c4010004070300070f0340301a42000c01d900650221015691504410055818103014442d001404049540c45447c00c0c200030748180c0144152015103040d910030f009440510a01001d4150340d4025007800b1f5460642c14024082d403c2151410a000d1400d40d00007003c0c9000100b0741c0785540c0c000d1070a0521440c01c80f212800d034121000c10b03038001442d4691405140d03000c0c4241a0200400380c0803800401e6941089403810010341c200c81002d503c014403121044060000380c1e81080c100d940c45c0c007030315030000c40030a00b03244803640029003110141001180c52904031a441070750b60050010900206030b107200071818000c0e00d210152040d042000a140c0b26554545140d20f43c000c2d03c60085089541c440a0107105ca030202e80c2510f003e4800340c020711801646019003141400110024801081103400144962107507030446681040001842d50000d07182c0840a0500c00c80c9941c420b0f003184a91860103c052442c00040384a124044840707000c1e0744c003500021101840240007800e890303007440c05104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 926492598 1250 926491348 926491367
    0x8070e061c05041202010b09150d0611041707030206040e04080408030d0f06080a110405070306090e030c0609070b0403170c1603031b05030706050a02130603060e0109020301080d 78
    0x140c00c50800c0180441503003414540c0d03900e071500008005000e16060070101030001d05501c1c3d2404590504800108680e242c105a070b03008071741003030402540440300000426208079007400410240c205501034280142060251003107805501e42c240c0e40d038480b185110b07203a60050000950280e001d11041c05140c40344440c2c164017a10032118180780940300c6015074915004260405082a290205076403020418045d0200418140c40189411031075603890390b180c4220b59501c0d40c01160b54070002021540b00707030440801000d10203c00c01400340c9210300310791a607020000b80c4c406d41c812240818050b060002d030000882e681a0949030a15007140d90b004104e0005011240243c0424005074020386018402c040c20b2700c5030a0000b4010304e29601d00585596041002d4002c0c280c82140094040b407404003c84059561201d000a15541d91080c100028000c0340000081036000ba0030126034181c04d49d01100a48841c020031000e00c1c1e0741d07020030200740e1009029802554001d809201071080c02a00120b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 926493848 1250 926492598 926492627
    0x8070b09011809090c050907020607030507020106150503090105010611121c02030f0a06060203090d020d02030a0f2003030403031d0409081909080a0506011a040b18090a0b010807 78
    0x744801c10402c0d61104001c01c16400050b44644d840d0340e510300f040101030900d402400c003521000c04614102070003030348400d4001d0000f010f0645400000300300701d05c00e6001d1070280c00940c0c45d4960420701d51a0040c2503070004c80d141314542d8030700400460014010119808841882402400361811792001e04085810541a00c5040205103a00701c080706240c0c0044c601c58003501040c0e1a4171704e0f101c81030409541c2103a01101c19508100510112502c8922540b5000d0b82c0603a0080e840342001c0c80420b01c3c01c5440340700580750008440c102010016032055405100c070a0b203d1500c800d45c1070104054581c401c80c030005012507003514018180325141d082c500c0404000030720001d1140110340321000b080d40540c030078045d0000c2510360a030b1441d170829140000b80c040b50700184007407071450f5030702542d604040c091000b100c2c020300100e05070850404202c03030180c208212400d4880c00400000d0000504034003c2c90300c02c80c200f000042074800d051003058800041603440d244030780c98480f400ea9101c1c0c0b00c00d584 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 926495098 1250 926493848 926493857
    0x30c06020c030d09030f08010b0901030207080f04121202070e06150d050106091a18090c0f0c0307020f030303130611090a0e04021813020603130f14120408070b0901 72
    0x2006000003807000e0202d12401c180b0100301340b42103240040200c80041c070540c00303014a00006102d15030b10724064400340082820f0040c2e9400e8141030040f00741c0161021240c60003000200030813490780007514060030501c10494850744901d84101a84c442e480c82c0180250300e01c00c000000c58a113070110106800c440c5020401d07280c294070b1140c03842500e109800c5000840d040e10340400a41c060051200180c2045030701590030300c8081030f0400611868200100e21034a100ba01141003003104804a400c15a100c1015580d1520009009600c4e500064016880303808109032005043c1000300c200c2c2d208102c59408808a04a65074909000385a819042d04940c02e080c807401811f602d039080d142e0050601440d801000d0316151040103550700c400181561400802c9050100b5040000c0180d680294110380c0ca83e101e6039928200c02c4800080c500c0900301450f1245004c00b8890800105070603100100f007554801414480140d5407807140e8820031110b030f4410303142000244d204502801f00340d03c05145c07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 926496348 1250 926495098 926495107
    0x30c031609080f1609022b180f0b071718010b030d080f0115121a0411030702060601051305040b0604031221060b0301290c2404020a03030c0602 63
    0x7016842c10390310440700300c10790340030480111601448992600003806141c42c20341c913003a2030740b0540301fa0400298030704126074400c58149090350b807503400074183c8961100350149069814100118020006e001c10b50b220b070400804100054411740440c0c040149584500b4115201c120b402c248410500d01c40b07009956a45040d001166024451022107041a589200040c10700c00300c41c00b280001030340801441141b80d500a00882c1d001104ca1610446a0400042248031642a501c0d0303c078004000a034403138039142c01c000d6203082c0b034006180101c4d0141e003224031540d984801503c4500c14000100540e00400c0001c00c41441d050300b0845880da4040c000909003a902c0d070f901c0101c070380c0c0b488250000c611000031445c0141e01418600070745920000c028410545000c3c00002c0310310041c01a2020b1301ca01407902d00f2180c865030004580741140d42d0789242d80d10907078003003151940781150341010700074822049800d6039107000060030301940d001032802080b5450b556080e550580da00d00c0403948641c0030300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 926497598 1250 926496348 926496359
    0x30b01031b18030210030c0e0a0608010b1c1b02060907181104150302030f2212051c0c090e3d03030e01080a410a0b040b0303030c031609 60
    0x1860f00385c00385460340f004102182000d80c05881694002041c50050b810380d0010403e00c1e610021240c1180c100058590750387c0100c3c2200a6030800c10713082840140c0c14115441180c03c0015840036242c2d44507030075610683c81e100a07664036001103110b0450f010308540f0b13524414803102d5120ba800c1d000d039402c80fa07242a40c0c42c64881c0c2e15012561405021079408010001800d02801c1a190702500a440221007292400440d5040c41c401240c003825000d208a5076800c1c4d540504115075002d001c86040070804180300c000341016004072148840040d000410000d1702f1900c1940c4140500020407086000e4440d0071106940044840b50a448181c041141404d4600c801204000a1802a5a0600c101c510440003400009024003c0081c0c94a010302c2c41c06038140b0080c260a500160603040300c480940810703602c000c449400121110f01c2400c8003071040403610395102c000b2000080d203050041c1440d40c800c00da241e010449540c0d000b42000c100158012281c04a142510001c50030505010340e100c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 926498848 1250 926497598 926497609
    0x203040807120b1b1603030603021c050d02070305030702060a14030406060e012c0711030d06051c030807050306040609060603091403040807030f02131b030b01031b180302 75
    0x15848026407030002c1c80800248088008060b0f84402c80c1115600d12040800030001607204144083e60407074215040401014480d80041d001036400615480b0714100d814900107801d16070807800c603058800c01501040841c00462804c049a4000703000e1801d000c401c2e02800556030150b00100c04100c900c0c02182d0200103840061070040e07000c2c010014140b41014a41030720b45806801c15945480e0521044c042840c0c03a1128286038180d139003858565441d0404240c079054030710104030400b0300010441015001d501d60090003155411200d811503540b8400765001140b49060004d000501610009503040c3d00910040d0b4215202420008001d941c50b1400c9049403403682042001070b440b03882000500036500b600c628070024000255150601e800c88840d510100c1c0d2100800100c031340c1b84001c0641d5120302050300201e1041005000080c0311000103a400600d400304040031030318001c0c00010a520900c01c04054500d9101c00113007600c1021030944107272034500e01080180314070720404401038465 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 926500098 1250 926498848 926498863
    0x608010207050a030e0a180c230a02060c04050d080c0a020d08120601080609130212010e0a0312110a0c051c02030324060d180b010f03120e0a031202030408 68
    0x180b4050144103849150081420340300800841c070800309034200b80001542d86882004054a0400c00212088412002d40b80900303111070915034102c001c08501c0041c9910310040411041540c02d4940a07661005a48010700a42c0070b2160480302102424002400c0d040c0240900c4401c00c0403039040e40b019a0008200c100d00d8401102c40103070218070b607007420503590503558100409003010101d0b4075190001c118020001840034641410310800c400c195181c00c00d440030a0440309000b03000b6070040c4e9101540e0351008072811000200200e203070404641f807034031420030300c25210240b0034a45801d500049540310b4241c2c0050301d1074001c0c4501c0c001c00d00340c200c044c00c2c42400d00d074001d16101d15200000c1d001c0d40c88442828281c001188480c00c41a0340d0740c2c411a2020341c0441d0700021080540c0c94100390024145400070441151a00040b45903c003c4c003c0401320b134820081d040029089050465010700a8180079400a0602c601440010100240312600310424412242030550300d0100c50b25095a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 926501348 1250 926500098 926500103
    0x3030504030b090a020f0616150e0c010c0c0603052805070f020a080d0914060a02040905060a03120c03110d05042301050412020d0c06020c120d0e090a0608010207 71
    0x40d0070010002040080783d8442c1690018200b0f0440540100d9418060700c5c03e0640f18640009504035284078035403455466640103503500e480c0584d4202c100b4000d00210128415506c81d0080e80051580b0404540310419400181c83c1d0302d541c500b42050700600300203880116225511a620116144624902208096509400f207014289600c004d0103451200b101141190441444103011400361421034081141c0d4960018200001d41407000781c02c0c16603002c84000e400f8440512000604940150056901075601005103807107036810807102d00000d1100411004900307548110460180a40241041c080e050032030060140801181c20590030080c080302180d0049030511040f1464809081040e41d00050360410804090000c1d0180c007942c460f0844100d0b07818400320840d01c4001058110342d90142c0322110081d11600003075150101000c07103902400805001038900d00300019101109203aa80300c0c0e8072030015400a10486000080182c034800b9140c0c00d000a8002091004014850 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 926502598 1250 926501348 926501357
    0xa02070b070e0906091314030c49080a3e0703170702150a240e0a0e0a120503040212030306011e02010e1b0f041b05220303 54
    0xa0510b010440015030141585001c1c000d201c2c01c000b800151080400051904058042c801a80d41440b180c81e600c0f0781c0110032680d002e6110420f501d024400c403148d60a100002d045a8286010200400440c3c000e8600580a60b42c2000c03070b82140380a91103054004030340b410003081c40c407443c0340c88811840504201e140c01030030750340d01140d03058032003103288498019020b045403414140c1d0320024890000703a883c00018000a030f0208481d40c1c02041100440041c00300e2301c001e9440c2c6241174000400e441c0180c01842d8000141c48100103c0004241c0c080d5540003403982c83c540c0710340e030401c401403140406104c0c4030b1040d0320001011035411642d07003416242a03076686640b8540707403042c41800c0242c504c0d05105580309100340119a0b0704130f003c413440f042c0700e140c40d1f100a8500c454102c0c0544103052080100d802031020985020380d14611810ba100300549040940b800303460240001c84200200140188103c0035030002200c3c8108006c0c03003d50201c0704030444c46260410303264144440c6520446c00315 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 926503848 1250 926502598 926502617
    0xb0406031506060305190b0d0b010905010510030b0108010e0c070203060c090f0306070822060e210f3901022115240c070504060e0615030a02070b07 65
    0x1074145025010180007545410700690a00035040c0f40d44c90402504001c207151190040242c035201c1006003141250021000034065070f4920080c40141001c2c01350790b01030000801c686100038000d0040030b4442c070381a03403148903503031a1031030f5980031240141c107070886a18204410702c0940e07020842540510312440c88280d4450f00f040420140801105060307010380c2014007003001c2c69030070240e100d51204401c0c0d80f40e412a417001100d050030002540c002000c41e444c1050440c3d149400181d9100240704140c10513042d00c0e00d0321460801c41c002c8c80b09410030903008020380c15071b500f001c5020303062100041500c410b025003444514000c0d0b100480c1c51908903980070903030229464018070f04c03031b41d0a40c400345486440c0c24005a022000012170580074082c17403034840c00310b42981c140340359209604940050f007520303444298062a120055840350901c19418070304042040c2d83e26080d4103000b44e0f40104206000891900c4a05040e000104484a119802c0c014803011400e88009540f190a95941c1e84940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 926505098 1250 926503848 926503883
    0xb0a1e1b030e0a08070516030b04020906040615030b15070f0c090b0904020f2b0524070c0309120605061008040803070309020406030812180a02060406050d0b040603 72
    0x14000000040c400c1500380300c01c10010751004101d0501d100e401c244110b582d620b0f20300b065454007085030804000c40ea40380b4400801c0c0f28003010f80d14061882121004007988036041048281c94190085009042030508503542c841c0c0294006059540c0150a000740c0b03142c4000902200d40164070196821140401003c0030440d02284220180818038810809010004081070040304004d10003802544038a403040480c3c0e9604004072032081c00c0c081c400c002c010b643c0400481d141d103a408100d03840d10460800812600e0000503110005810286000a0343d0711744404480d8960050402e50911203915000b144188885810b500014021140454207052040030300c0b0b4503804111a60741001000002e01001400d13180c12245c008d465072401040850180c00041c004110301d40c4000d00e00500014040c03900203252951501c6480f95550f5100007202c07030100e0b2501c884000d08006d41c4100c0070070042c0700713480c050005444903040d4030600082d504045d10208080740d12a1b017040d200305994020703c000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 926506348 1250 926505098 926505131
    0x112050c04080f1605090c0702120d0e060915070309032f030f0c0105031008010203010909032a0b100503160305070b090901140d050313030309150c0b0a1e 68
    0x140840100003401e184440138400300e0905428081d5910541c80354000c103140b80d5010b8140d42d42d80307030000c003003e00e18009000c0c001d98880c6000700900200344880080459882c04409403120301e000940204640c400742081c400e01580510008c0341404540e007004408500c844090642001c603049110150040b5000c2134a400f01245460901c01d602c40480f1040b80031000ca101701c1d020300c1c207081158594440c0c040348103500302c4a8200c00b290350b102000004840c0125001200300c0350194880110400c40030181010a0311121010880005d5041008000960000c0c010354080d4034010100605500c520010303003444407070000c1d1040e1402440b81441840001d00ca25001040c5003c3d03101d04c3c0080c050b0100e19800f0051080c032800c1101c03c0f200c05a5a00c9071080c0c043c0d015030000c1a256903801200c51006907116034041500061540030b03020694081080440042601940307810101032296a0340c480d030604010088402c46850360101d01c58031000c07021001c241142e001010500b480c072080d509a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 926507598 1250 926506348 926506363
    0x2060c0f06100e2214120d0e030a021c2a060e0d0912061401030305030a0c0309080f09030708030408070e24100e22180519020112050c0408 61
    0x1861811070400b44907560f18411981300003855111813001004c0a00c0c20208000e0b07014585000040c041c5003040241405d100d0f0041c10000449081006610055088259203009056920700540c6c4240006600c403074200d20707010a503803100d1405120840c40c4208505801001c9181c4682e007203c5c00e01000d0810080340a809040c01d024001414400305c0c401000304800807a1051240e071031040d004c060180450f9801021140e10850100d00855960b0700d402403d580c41201c10204c1546402c2d1124039052080c0034072708169400000160a121135601000100e80c0b0a103641c030780c540324481000031101c0013031014100800d03642e005031181e11b00d450480e40c2c1c00c0d0401894560a9900e400711070401c142824081074411304207560b020141010032100703a490389001d07103c165006e008441d0358402c01d40305044544026050382000d004400c0c40074620810140c01e8a402082a08001443e0002e40300c45100e03000d81900514008244032100490381c02140c00a03140104041d0b00085c0c24001c9510811407075 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 926508848 1250 926507598 926507609
    0x3009050105060931060212010503120304170c0f0105040510142a1303111201090c03020411120a1401050d03140a0c061812030b0f06030402060c0f0610 66
    0x41c8440c9060110180c0481ca041c0060a510540421105000001e080b03034584ca5648040c04541d580c0c9400442c1700b09990034032a8600c44d10404401e4007c1e0300d81001503070301a540c0022000441800c1c401c90f01050f8001d2208032415205034001380001250900540d8000c6010384040c15401340118145429518100700c0e031807203414a041402049002c030344c05003844002413880f5030b00b00a400e00349035540b44900c40b00715083e00140d60010042c0f04100c01034030413040c4115802e04205c28250b543d10300340e880c3d0704005032204d48a0700003000503081c907821405060110000c00c52904200c00c1d40c003020351a083c0c401c07a04c240d50360003064111200449a0364054039007204e114240c0c0c000b50b030700141640441d0600300d00141c4041082c0012600813000b034035000d548000203014030280c540000381c0e903e90408003910311600c02d426806a01c3d001e4403a40c1c850000c0a018040f00100000c180b003e0355101510881e005507080201c0143d10b01c00b0300030061134a08501c05072107103080c140351005c0c0c0404650041c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 926510098 1250 926508848 926508859
    0x90712051503030403020d050a020d08210906190b041118030303220f020919060b030709120206070f080c06061c020907092301020106120f0201300905010506 69
    0x7412030301d54000040c3c034100c030750465004116018a10b000c6040540442c0025005140ca03c40c001c02c1204d12000f82c00c0c140011000180c403140070700f0b080070203150107841c4140b90740c0196000c14010103810180c2c3d02c210050041c0071440110000114084420b1440140315103140400c3c8803019106090000c465001c1c00c400441c25400c0c00d01920b00c074025000000c41390080809110300070003d0102d0780a014507001090b14010b0700d060b400340c800e0b849220040d842000e02e030110118151101c141034a0248410390340764400c460070704900445101c12f000c002d9074441d10900250f40051b600c0d101c80c07180c081c8508951707506e41d601d8102c2356241c004040c0c0440d120750495000e400004040317900400e055601150880910749a01c0c00683e0038420a03000303002c0f04600405000741c408908540555880420f034004c111203030fa2100b101c69413030280c5200602d490a20300072400950300c103a04107403e01940c541e0b20200840d5980401c8200040c01207140f107040d480d44003200a100007803103550ba12400075071700c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 926511348 1250 926510098 926510131
    0x24180609010e0904050c06030c090117070212072105120c0313020d0212010f020a1d090a2a0e01092306031e01140f01090f0b0d020909071205 62
    0x2822066000402d14000d40914000809110702000420304000000d42020303501c2c144000000c460380c0c00b200400340440c1213044541480317419644082d00c150082d40c050144800c503d5108106540032075001e071000a80d451880c5440e90003940081150f40481c0c840f0390342c551051814011241c0002d00810b0f080320300b0300030403004040c2111005081341e4100c50b005032014580c40058405040c0717441145440d86042181c0e00b01e1201580241000c82040c0c0314400f00b8125031800001c004e4804000c150800030700008540b4498941e0410b001c400780c8801e103602c4409031009a09000d409910411000948521442c041540c2103d9180302034004a861100c0120846510700c202550749010f0902071000040090010a101481c900c601c0c4809010a03895503540e8000340b800c94044c4040510600b0001000041580107501130000c0b203400d0030801070303d603160080810894200512028000f9020010040195a407000721442006113851b020ba40580c41003200d4100d41c0c0041011020000070700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 926512598 1250 926511348 926511367
    0x30703110c2121101211090703060515030a0c050307202404140327030705090c0a03050a0b011718010203010b0415030c0e01080402241806 61
    0xc05452800d40e01c80012142800030302c1c42c000500c5a21807a8007680726001c4050b01941c0b41c04210b80c01090001d442c0441e650311000384038410320380b400300140a00b1000703a0103016800c01061603a80420a8100094026a5800441d5084940b0710796842040400000c008030401148240b003403204a910b0160b0842c90052405005185620b54005009102d11541c40b07210300c080100c5036140050042503100c0c00d507500401e1590382c00a55045500b110700b04410141060000203a80685003185c404031400081c041d40c40d0400748680d03030350030b030103008a001c003040a1b169441405d00494003485061f13901c4c244000e0050450388043c0c00030000d1410011249200e07a4018500c68041c462499080741c9915040c5144900100741c0c1d1040609500100000030030a0581d8090b00450b840180113a08105809108030211500415032001041e221a01c00f20309510880d10700750321900c007038880340040c1c1c0714615107055941c000c0b984a003076100014026040038009405482d030350000b608d04d5414400b444 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 926513848 1250 926512598 926512603
    0x70801050a0504021317070609090c1b050c0904030903120908071703041a131d010b030402040b03101a180703180b130c0b030403120209190b030703110c 67
    0x20302c01d091040d50017152107481820040c03d280002e100d0038042000b203414103082d054a60149118150101c0c43c90000003074910028000c000d0500301d00e45e2440d0b581404031002441c00b4413168000d40d55031150b14a40c000030340740c1c2000310b4007a500070703140d0440c07661942c64884154683c1c40a48d4042100f800000c102d00c4c48000303000000d40b450000a00e60315014942050718500544d0710502411005800a5a907000004024101d0480e41ca0007196050b40382c0c0d60b0345918610385d002c0900344082d0b2000400825840d24040c54005100420120340702d400350340020314140c09004142e501d82d0317844032501c405111074084800b03030310310640740342c40101c84809202001580c01455602815202c40003130b80c180250407202d400c1c041e44220307410041d081c0740a051000155040044607841095000411210300b11015248115810354408501c1180b51035175802035000200c800d80c01840c0c0a00200e41a541c121544001d803c40a0000f5100e1610010080999541904508400728200080420304101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 926515098 1250 926513848 926513869
    0x100c03140c190b010e011e030803060105120a060e0108010e06041b03120f090501050403050a111507030305042315070203271201020405030307031107091b0807080105 73
    0x200201903141d000703603625142041401208031032810a0004082d0400c982d155009050700c080a00c05501c0360703250080d03a07806000503840051603146085041000074200030041d85d00140602d010783c01c1c2140d2005100c0031071410f07501e544515440e40c101b0310400c4a6030200c40d0040803000024088980e9400c905916071001810107840034581e04000002090f00b00410030065901480e01c900c80003042400130681c1c0028820000000c10148000800d503100704d0644041ea900040548100446961007284e0290041c2000381c100301e4038100d0043c1d41440c4000391a01c1d43c001d4402003118509440c002103580040c00d220403504e41c5602c16600310110010341441c2c40100341d021500d5130b4a4003170090f85180140710401102c9100d1101c0400008030703050a00502000a44065841c400d4410038035080c2d0046004180d0141e00c180100c80100344a401911400c0f03401405803010592521001d03421f030382100620045510280160006890380300c05000e61001e600d00d030503c165410000081c814429 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 926516348 1250 926515098 926515127
    0x406320405060d060509270a020109060e0301090606080307030311070b0613021911060906071b0309050a0f1703120109050c1207180b1903110c1005010302100c03 71
    0x10702180007840f1007400d501200113420300805884407842c080c0101c0701c00500c1c445e102c00b10f52800104118005e2000504504081c0d4141c448200b61410f0000031155100481209035042d0741301c0f00900c011400b0752090b070000c1c0980754041d658070a803d090140030380b4008916000310b624200714480c081250608140e803c000100d6095200c0c291a48404010740262849d4000182401c601c0c24a03151704200c140c0c0b450300e041c0d001d40d03003180d4407130710304a4581100712444c0c1c0102e05960701711300b034000c817103510b420302d0900c0307070800c0d8101c2070311000801e0360150f07150070007840d109482c401484423110f120034070081614074200a501cac001003070044c3c52500106110fa0a01035071643d000c1140c40000c401600e88034500940720449a180840e0004c01c1010b88a68050180703c25000120300550000211000802c841000110511a080c0b04900629110210400400c0f0500c0340020b02c09040c40301c1621140010070201d060f504500401892210180512044c000c50078210320002c0d0700a82c04104a40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 926517598 1250 926516348 926516359
    0x30912120c0705010e0d0b01090e070306110a08091603060f1d010501060e0d0f0b070201020c030d0204080d03140708061c06090b01140904080a050f0406320405 70
    0x18008009915054054100c0031640c4004074404001c6200001c0c000708036442680e4a024000d02e20081c083d4a40c0303852005840204403070010f106810302034018041080342c0c03200322041da0350749465060881e0100d11000c5107001c0e00081007040c4d281e1107585650010254800303000001514034049680f4180303844010405074481801e00408401e82d031140380b0754101400c2e0809001c0c40d1400050081c0ba0901a1030081147d42c0c1c8010303850700f0007668900c42d40d6440b254801b680e03c881d440312150400014501c00071176401308900c03501480244054181c180e0701d008056100c41c1820b20f040d06118070000a101090318100c0024281000203080603080075050818440c42d4031502c020a03418101d044250740c400c40f4004c20b0104000d6258400442c1602a01000384141d8039800b400c0ca40342441403589a01080900100b0040741c1070b1001030024442e40c0c10540c2c54000e480d4031604140d0040d521600200b40302010076400312400c0c44c1c0c0250400740b801d030f5040d1a40c0d510720040c1107030300460146038080c8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 926518848 1250 926517598 926517619
    0x1090f0204030c090902012a1e1a09060c03070914180c2a1c110703030c14210a03020c030706021b0708030f0a031b05041a04080309 58
    0x410003541220081c541000450325070136200c0000350060616940124005550b6019041a07409403881aa2012605d40b80310354a01c20592140a4402e00b103100c030101c103480036141100081c0c540d9050b4990701044660f440610f00d030601c07c039820440c0c000c0080c101003e08104114500d540560401c054a107000c08507040302e008140401c14072194980c1038540c0d554070034140085c2900050180050b131030007140b03d514a80010801101960f000f80359002c969100b84408200c00b6030070342c0c1c003a00c02060303460911080d4888043c12450714299910540204110410240500c81500e141207440c0f081c0c080149040c0340a01d034a507101400b00b882e90690054003040090481d446031301201c00e5103c2d50004c60351594980d0a0440007544042a416041c00c0031050785025018007180c0c0c90203c801c1e54003d5801c20b0080e00c0d81524a501000d41901050350743c10480c64920a14408401c03d80011340e01c041e240c81c103212400790802c07500c01035034054003c280001c00c4603400000440781d40503401e40707108220 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 926520098 1250 926518848 926518871
    0x1270302090405160b04080708010603201305071229151b061e010311040218061b01051b0409090516030302150606090f2b06020c0f03120109 62
    0x2803c004402501c1004841000000c1c890542c00180041d205040141e400c2351760345005c0c0c14221031840c44010b003448040d40d25480034200c291442c08400b000900480e03140d1258400c2c0030100c0e0011210400841d12414560030742d00ca483c880c141e0001c96000c800000651500e8588448500c14500c0c0391042d0400800380d0b51228403002580e0780500e82c4029840c0071030f080300510341c42e15401c070741c10303c14070701000380703088002004e01c041c58120380d08541d601c6000d00641c0705010280d030142d092000070100341c1e0780c40400d40d101c4100030314048031240030444240b1031780302039982558405814411fa41011400c0c40c0c02c5a4186001c5404a401351140056102c1251a02505040c251180790306480d41d081000000e02d07401061170f52903c000203c2c407101f166525020440603002d90420142c0010302002c00114a00707141c1d08802d280180d521240903850024584001e18a00c00ca4049030403036004504030107410420441200300596810245080c1680d06a40141e1810144070303520446403214002541c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 926521348 1250 926520098 926520103
    0x60513111b0601031203050c12040602040b04081b04054804080d031e09050c040519050c18010c1a010b072307060309031b050a0201270302090405 64
    0x3014440291a00c1e070340c0e1400092601c41609220503500e5207200c00f05084d00038401e00c60b031480751080758201410200346403510390510500400481c1c00540c02c00c03001c642c00040c40081c0005041000c000c000b90051700d4099a00c100780789c1c920300d0199041400340440890b54071080107140c0d0810b03200d088007005000b015004050b40c07000002081d251b4103101c2004444950080c000d840b0030317070115801d40701401e8044044625106a903880b01c081501c2d41c152040c1c50303412180002e8064411a01c0b03811180740010201d940c07c0e01d500300c5451900070041064010f900595030311220710074a02c1e08140003200e400c400c241040c035045040140444e0108200002c216501d61030340c4c01f0051081e025a19400514400d030701020040d0b070070f06d800318515402908000020b0740314544650140c5500c2c0e103001004c2c0c0203081c100c6412020301c802016455958103a9001d00d5402c240610002e0540c0360550001611140380070004a40da0703042c0a1029080c1c45c941820841103c0c6d05a6014403503a441d07050050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 926522598 1250 926521348 926521357
    0x6081e0d031107020a0b28080106110a051b1801030203070b03061f0c0b060d0302071a090d210503010b0f1810020f0715021506150703050406021006051311 68
    0xd610806044e8040307002c0a1b450054a5030606075111070500003051a08a01180311003510b4800140312440107110440c81211490f0b000403540045585450309603070741da41402d4000310144a4413800d03009400755480c148030407000c51a14441d50121070b50464000c0790300e41c2c034139000c0c540341c40c800000410303500c2c1c841c1016240240d03c00a021500b203960900020440176034088240d0301d11100c4004a03407585040c9800c100034940c190001c10449103013907075074894144100741c2d103000e0b04070a01004240d0744410041d86da16501c01d0000400c41480c40091034100b0807047c1d0b1a20030030809000600542036000c040f515856030034401a42c50380c00d2810740d42400880c8000058000580c0c031600c210890300068000189485001940d1885da00d802c00c40b401200000100c00040e03110880d11418400500c0040350000c9001c0d008000240e00360300c7c2c2418540c010b1350102c0c00a90002420001d2946c1032008000c00d1640b0075003440220318140018942d428191111003605a0f280342c0e082c07164091f4012078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 926523848 1250 926522598 926522603
    0x60e0a0b0f0a06020c04060b03160c0203010b19080d0f0f030f201324030506040e0a080a030f02041d131709130504050d0f170a06081e0d031107 63
    0x2c500c003075141c0c08001c0d00c03440c26007981405503017080c10100e031128101082d00c4c0726610600034680d4000802504907241c1d041f000d416a015583d400080600c1d45410031102d80707003409d014184404901d800c6525141511310081c07c0308005541090b0002c895000051591440c840d19000c1000d06000a2990050281c03480104484100d03c084103035002040000d41903a44014410398495076840c06546040c6010441c00c9011103244038000711000d0096101c150842d42c098000581085844000741c40c01c00030200694103104e0209d611169103525001d4809811f58204042d0f003014913220700c20080105407401c0c1c1100e802d504001584400d002a074000060b6085803c1e01c484c4006101c1c004a21303840900c4a83c050105045510800d40e610301403280180d038840001c101c0251035034011a9200c1100d070b816020002240401d00c0c0c5143d802d2a400d004035042c9600151592614031401e14084900340c2c080d40c05205c003510400b12800205034002c0901603814045507403c0c074003401c18110321400500 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 926525098 1250 926523848 926523859
    0xc0b0408040b0a0f030c020106060e1504090908120117031b0309030105010308090f240705070b0c0706080f1303031815050901060f140112140414060a060e0a0b0f 71
    0x8841460707803040304211100250317102004402440c3c00224242c94144c050304010800b825140042800c11411254100d0702c0c40700c40c1e07400e0681f29071501c000c0e0b44007001c09131904000419005109250825040c4c010300c0341a944c0c2108504980d5010748a0040000752811030f101e50488000c91541842182c82021008008111540e100c2c60000e04036004003001c60b0280c03480401a6a4a081003094400f41020860300b00030380381000d0030420360f1b40e407080301c0417242d501406000040480c1000060443c02c0300f428058943d02d030030300c0f8004140400080003080302800e414140f01c080482e000c00403071095014580030440785000f0308541c0800c1c52040000341380b04445050005c61341d0f03841c1d01184c080c0d811080244502581d4400c0c03101c02c00400e001e030001c6620103046811166000f18164041820403010120b40c07201000d03080341c4214800c5505803041d2080790303803003c00301701d050200d5030b8401e0000e0000c110882c2009501c0103100030050200d81100e50b103094018aa5486120000e8190402480c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 926526348 1250 926525098 926525107
    0x604050301090b09060c0901120b030705060a0c0b062d1207030c030c0e0709150c0b04051f18020f0f1f0801061b03081b0301080d12060302010c0b0408040b 68
    0x100215180c0c3d048031340c0718007401514003041403113200c03034202c03880300c0c005039a8143d81901420178603004003106000f1076454070807041c0c00107180d2070300d002408403021682c4407a080c4181c20300b0301b1050440001c1c40144122054080491107a280300398401d40d5980c0800d401200320040303000f1072841c98910f06260b080d44a02c0c40000200854441d8600589114524001069541d6108014043c0080c1ca41c2c0010541f0a48140500c044c50b4440001d000030500d40800030782d406449006400e2029202038030a074020381003c40c4c2e408080d00e461a00748906017010010028003000300d04000f07130004002885030700190425022039440b40e1442c0c14907100180b0506d0084000010402d07011607200794640411903000000400a005902c007141d40320282003808d508100710740c0e04847c0103000802c00c03220201007507495000b0f80040300182d40a42900d0004141c451021580a020640c5884180e138015042620600050b64007500c2c110084e617020b4400d592a07161440c000360a402540c001790f140100215 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 926527598 1250 926526348 926526353
    0x6060b0c011a0f01050a0518190302101805040f0e030d0b0a0e070c12020118080414060403050c0103021b03030f0f060409030807231206011e091202060405030109 71
    0x14003506000075051540c0a41e5240481803100d0300c0b09003c032850104606000300301c0c606000e1002080d8040e4282894131050b0003032400512001f11180380c4503810340407100b0038011810300b040240c3c140b499038104180d22210111214000303003843e001d2640610388600090320803542c5500829104003100c820740e0749030500b4044000080c4202c6100c2d43c402d68605030002000d848503003905015688a5580601c00807103501d501c41860360f082c48001c110742d40c2e50000b904003a4801c2100d5241c07841109030340d07030311840d010405843e42000003a5134481c0004110400001d000020070036a840c40a0a002d600c070040241006000701014461010501001041006802c1c060540c0c61003100003003c00641f070748614080c007086035100360004000c90381c04d0700481c15540c0100c02d8506000d110000401d07089a025840c900b098018426140c0001511006c1c0005581c018442da2500d00804040252024031810000c2c900042407084615086c40c00c4040c2d000c0d526860f0484000d840302600030b00c4855000d2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 926528848 1250 926527598 926527601
    0x902070803040501060b0a02030f0a1b03090314030f1b0304170a0501060614070b04080d092102010c0206010614040906171c020c130204030b090d091e03060906060b0c01 74
    0x80341d00f00c446500c2d0510100d95442000c0c2500c1d0450481c1c0e0046007002001807640405500c1117810000380301e0100c0c841d40201d04090071554540b4803030350b914a2090314501e404100740a0704c5004c84d190380c005000e00718100380e1030070903990802c1002800040c1201e4000030b090451059401c0325a210048166400352190001442000039214030300801006954140c1194004000c0c5d503181031030001041070201140c181d401568019014006141c640a9400d03400d4040307501c511811503102c204060740c9070460203070482000d50140940000c2c0018603c0d424025220501400360074181b08070303d24482100350944050f44d000e000703458000c102c500d469014600e40c044a00c19901d10f41c0c800c074520750004010700090302411400d81e4008105194031002082400161040b42d00e000b03030b40c00e01c0000042161160034034080d4a000018101c4080900c000170117005180e081000909800c450a009003200d00e50502c003103e400c1a40041c804101d0f24104005e001594404164003401248010814006 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 926530098 1250 926528848 926528851
    0x1f23040f061e03050d020615040c020705100f02150405150901060510050405030d1d01110f061006090e040803270d0504050f0d0b0a050916060207061d030601140a0902070803 76
    0x28030122464000c180c90107e036900c00c03c0f110b03000c88042480c2c0380c901c98181a00944900e407000d0055078043d6441301d02007030f1555002040c0324001001044400b420b01d0301400064000c0e24042000e02e01031409440f80c941d101500701c0303e01792a200000008101080a5001d200680300c01000341c0002e201162000308150001d0140e1880382c000c002c104103501c0d014141001c80d98000d1400b15504219070f5006480402c900f042d00340c01c60180c01d1000501f040c050150900c2203848666044450b400c1050042c1b0320301072900420020b06120b410303c00032880c0002503d0380100c3c00c10340c019070200345001740c001d48420080d035000c0c18800c000d240400c07240c00c403029200303072074040d620480c020b400d460810051641a960242082c0034450100302d0401160704040d60100d402c5089502203820400a07000b001050350002e40141c00c4070100b48092a44a0000140416600c010440f0b09484900007500e0791010310400035140c0c215081c1d10b016440d03040140c0010405010115101c03e81c90034250342e554030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 926531348 1250 926530098 926530103
    0x6030f180609070608060405040c030b09101803090614160c0506070317280207030903050312061801080c0121060602031312030903030e0d0b1f23040f061e03 69
    0x1140c0014407d04191090300d1282c0d4100364052145440d6440d030200307071400500340c0d4a04e400303a20fa803a2180f456600440c0d00c0c102e5084541c4082081e01d06000300040701c150042010442e0102501640342c42407030950342030b0b015403e0211143c1c00c02d441c102c1119000c6a009903001700300411b500e014941c10a82001c1c0c0741003d00003642003940c0f610a008481080700018407501000d1000703111600d841c82e40603010242c07090500d202c2454503500c0e07183c6940c00c14200c4510326414501004414145080901400c030349841c001d03140d5504042540d42c4485013001071604000f1004510304120700b40461514000340d804004101e0705072074560003500c0e58801451038454408000c40011600718070003410440c181c05a07244440d007401c4d545d044414504411105030b1042c403410004004c00d0308c2428050003000da010212817414100c080f01103500d1001d41c0281ea1270001503c80e50100d070080005043c00340e000b00c41c002500c82c05130340b004004003520781012181160540e00b10121041d45214002a2030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 926532598 1250 926531348 926531357
    0xc020d031a0303180316030f0c2108031f0f080f03030c0417030d1419110a03112503080f010609060f0320031608010506030f1806090706 60
    0xd00c181c645030001c4400c80701c1141c141d40708001030924600024100762584c0d074000c050b1040e0b09910f4109646110f440d801c15641d004505000000b00a003881700d180080015500c0d0381c80c5e07940303645c0728008072200540b4094000310002000030186883d16148003400386009503c0451142c50303400c00914440d80f405801018491201c2e800f4650300700100b968403641254080b6031600d420003458010614000141800c18427082c04070b40700080351400f0b419071403000c221020a282c0780c030710900540000c1d4010030300310440c0f905050392160f10f645d00840c0c84032600c6007404200e81e8846c1300d5400107441041c110203121110b120562002c80c80c0f40c1490fa035140d00990b02c601060310386140f11003890390207114030b90114514940c2080024015103001d085443c0c1800c0000b01162100d145962400c1c114a45d281103010000030171400e900d81210340c0c0101803003860034248942c10140810300c1031001811088642e100e010000d089420100755055188c256402541c0b0181050040c080d51880344d40100404076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 926533848 1250 926532598 926532611
    0x9040603150b0d08030a0902030a14011505010513030308070e0414150907080105010806180708060406080a0302151f031b120f0b040305041a040312031103150d060c020d03 75
    0x5280448800f618950440d0071186503480c0c0c3c242e464002d0040c0709040f60980109201e0f81c0200f4170001066032451884d800208000300160100c882c41d0001d80c0085060000503c0b0780100d2032600c00d81042034950605044d40651110702c01540c0c2c80116200c80360340582401d82a0060602481d20030b8001d52140e01030024480542c0100a0b15140450b0744030001940c440040200d0b601c44c0403000d401400207449040003a245400169070344008440c0e24021608400c180310940c1840d02c9000b00609a210140178501103c0d82e001351101900c2201013a4104210302080e40b0a4080c1d40d5012607400586c0c19440d40d071358910f410329902e5594482100041d0140c4030004440c84042800345045a11036415a490701c6c0681d18501003140c060016000c104042c40082000711401d040c0030340340c2c1141c41d46103440b2450341c50803181c12900c100700b90080501301f1060828101002060380e411074805038900d00d5010f01e80002c50900d0014050140420b4203200d00041203540209082900c1404e0390b4050108 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 926535098 1250 926533848 926533871
    0x307060b01110d03180f03021b0105130506030402040b101d030712030518120f0f031204171207030f0f0923160332100504080904060315 60
    0x1ca00064440b05034020880403403515109501c0880c803042007440c0c007081010705440342014000010070071400750744000b5035100721540600350700429560902c0c1541c038010b4941a8418084200d1090724002c1c0408000710341150b40703d401c04002c601c4041c1c80205208444038ac000c0140d00d801c0c40790b0b02414124010001142404514241074610360b200c802c2450030f4030381e800c541e203900402c5100048602451417120503958103001d8841044000e00130241c60603203c0c1c2d41c50130300e4054400c0040b20340c010444900f40c0140d0030b080c00d80c400d8010116006107410f01418441901c21800d01c0044501e814081225168155220200a40440307a0810080c03101c1c8040004803100200040c1000d004402407241c0281200012501c6064840030b664541c55003d842c068070a440c1c0d04101d80110301d070200b941d0302e035a8002c00888400c001c0c5c0e440d40d40b9200c141d0074881c4c80392810525112190b8691000609021a5904130780701100b000d03104001c0c066490402420a02e5100458824181029002e40c1c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 926536348 1250 926535098 926535107
    0x91201021e1603080c120403020601090c0503040b070f02070e090102031014090a0b1306080a030f0c17030403032c06100324180f0c0b0a0804110103020d020c0307060b01 74
    0xd2003005103094080c4005183c40540b40c0e04070050214110800c108528041c0074807141806000d41d1198005000b15410045604240c55105940c60108036080c4100000300750003001c80c541000c941c1c01c1c01d480000e524107040382040c00b6031f0403030780c1c424103a601400030318001580114400d55060a00981c00f42e1641d806040e076003002c80c11580c0c80559800030901281e010b6110310000900200344007a005012900c80741078030131302e030705c94030060304200e0051040c103420900d0131808480f58070340741c4071551244e5500807800d0b6504041e0384403054084000340030180242d1011240308444c0284c03140144080310b100f0040c2d11000074418440c018000802c0c100d4808440340e0040d0303640186000d01c150454004181e0392103112905050286c0c550400c0458440c0d10b4682c6401c850080d024601d5420300740c01c01c02440e10303d44d03100c100194000c014201140c0d0740900411342065110070309404007100c000c0105c3c0680140d1314040c40c0035100280c80e031607880d0000010501c0622840d405d2040003d580700545 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 926537598 1250 926536348 926536357
    0x1260103120f120e01180c030204060b0310030b040204021e030702010608060c0d02090a1d1b09011d0a0f0603060306050105030c031c02151e060906060a0e06091201021e 74
    0x2000f1858540c81c12485552a4004410f0f1280d138000004121015074110703844031040f40703015583d200b80c414092065013403501034500640181c2e01d255181d0700340030003001138401e0300b840060400e29100b800b18085585903012106011303440020880c3d0040c0e0000c003055240d0041d14080701661034050b000031451700202c1d2481c4034241c55984c25040000d4014003902941c0310003002c0340e2200c0014408218842c10402d10502111801c840140c6868480c0b600281c40728440119404498180075060313250b0b0340000550740440c21440100c0b05c0c25030910218400541c5504a154030214140006c0388107a403551203101100e005000502c416640c640c1859180c80d0404241074142e0020b62320030002d2200c1c0f4802c0244601c091040b54000c442000c41040142401d48604c5c1c00da001c4640480142d1811b0b1040c0394001c1402c4403186c0090034000e00140151081210b0241032200d0110b0003c459580c4070305440c4510390140c01c11080b105100e018900030341c0072003166540c0d031102540d030041d40c03084401a90f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 926538848 1250 926537598 926537627
    0x9070c1b0b09091f0501050d15080105070f090503100e0109060e16060318030503090f060a090605090d120c111b01020f030f0f090a0308160302061f0308090126010312 73
    0x4d2049030400c40119802d5000800813100c0d10b44441c500004400e0100e0604000e041c9140001141d0500c20002001e0b000c24605080811080c150280220340e40480d903142c5054a02c100007030701010800d1002e01408040780c0103400f1a01d4a0b11694072140e010407018000c5040884000744240c0b180801c0d401c6460b400301d103005035082c1d807401c540000c0c004e900550700b10100d00c044940b60944074a0b1103180240071034201b407905031a103a52904208140c0201c0760404c1c10035019141c600c00a0100519a240c500c003ca444503071214032801100e0700916442c00320320544025911105028a810461521510031590040c0315481b8071402007000401600c0b03134514009840c914000b00108203030100c0d0007800c2003030752201800c0c200000055006004010152100f1408040c911281c1400b07420841c00901103035030700c00c844403140000004d001c08103007031ba0f6121000b1512115803000490304140520070035a02a04444403c203010320241420340d041301d00c1024500918128644102d03034190895820 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 926540098 1250 926538848 926538901
    0x70909090510090f020a08032701051c02370207030201140306030c2d0109080709110702220e0a110904173609070c1b0b0909 55
    0x503008400303440c1c100300200f030300034000c0c40c1202020381c000408650969000490765030001030320001c20700049180c40724004860034280031a004400010b01640709540030030b00945848040350742d0414041d41a501107140e100420700b00003c0080c00e02055416030320917041000c10100307050180c1c510026800303094940c1a960398041003a81d540c100c682c0d0b0070140c041503050042d040000b4803500d1b0310442c6001d0205000c0801182091844900c4880340f005580904006001d0340600450740e00090b16000c407024500c0001e29100c00c020b6100d800d010f0900c00960052480825211a0b46039404100c00401c05803010080a06420811a41d41456000061095080325101403207850b011980b00e9005000d00c9a44403507602d02e070b01c40f1405d0381c00300c1000d000d610040c41843d1109605052030003d508410004210300034003000c001800444010800383c00c000303034410410200500300c10000e0360004800351031041c484d2a101d0603035240e0030082c42980100d002c04005000d00e201a9504094207000112 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 926541348 1250 926540098 926540113
    0xb01021005100b07080d090b0f06010c02031c0201110f1e03040209040f0618060f0c05040806010905061207080a0b22080c01022215020a0305090415030501140709090905 74
    0x180c3c151550040c40341036900520034050040d2030300c158012441100c0c8200c242c2c135100c1c9030190b4030885200020b0322030350402c40d000c41741c4001070f100064001e0400007203284c20214100014801c0b40034086da800038044150021401c9102c40b4620009005450a100984840103c3e031031000d004a00040300c0180d0321114403804200811342518110202034024000400c42d0030b8550720340600c000110004446003580d03000300c42c0c1000e40c40c1c884d4091082840c5003541c5010704e440c01c5a507888106000324260142d845010807003079035403c206114100c01000075a814a56503000d403d49030400f484054407003140810001c0c10f0102c21500e041d42c0a01d169003a68080c1c4095100d41c510398000760030380c003110340d030800002644000c3c11004180e40180348020707103803440c00d01c0c140b07038500711141c03e075582558070024000e40007940010075114280070981c0c0006000b0f001c1d031000c0a04a00c0b13540701034415407804110703080381e28524000600c1040c058440c1d03841035035200d16160441e081c01780d0150454200e0721 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 926542598 1250 926541348 926541359
    0x201031b1d13091a160e131506021605010f020a0303110f1201080f0609060a0c0207090e0318060f070f0c030c080708010c1b0b280b0102100510 63
    0x7003807654120009800003002d1000141e0000840d00f51a40070f0703c5030620103860800f1119011420b56014802c00204001042e01c00005000da40b40780d014984615003412a081c403410050b40b01607030110707410b44000d5035599103c00103034450f550344045400342000d156001c40c0b29409100c507000b401e2110390090005c041180c130202c00421105002c0f1984400411190250410000c080c10008a48803280c00b03440d454550014500801b5120008081e0000030070402401c40c0031620a03030202d801000800e0031412000d0807420585941c04c0044010300d48626025110800000b40000702400c01000300350007120020000540110550f61400aa0030841980054034800d50000c9841c480c08440b04a1030f01c0e03580f41c190030810740e08010401d5010702010428031000b40160162807429052450310307000031102030240c1e00440304001c0d0000800c3c1020030340e0744080082a40620001c40d4044059080c81101c0038081d21144846c107006220380f0000020110852103854003402d82c50ba200741203146440f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 926543848 1250 926542598 926542637
    0xf070b0a0606120f14091509010c0c0f0c0b03070305012303100216121112090a060e0111010e011a040203090715051e1c021e130515070201031b 63
    0x80300350701c4003a0748034024552881d094490580c0640d86800141c1109000c44000c403800307c0c001400b41095a050172600042ca0350089250052260040c80e0740c5802034040c207200c1c40014440c5c3c8130001d0319900208002c625685540400e06076034404544110420540c0e00c4d1310802d020900c0401d5140c0c105280f182a0181d10b603005220707010515680c11403056040c0c448401c002e141c0c2c180b01c07010510114103000c0041013449030500d040030440c142c0307013010004400b20300d41c04503038024201444607541a0031110b0380180300607130110006034000c1c00019101010300d8064042c7c00c1c980c070341c2c401241110074480e1900703000b47e91050100c08002c00ca9945440b20708003180319034012a805000c801c00c01650342e035040002514455105a11141d43c40409604c0c0e250141e0f03001d64010081403041c0440c1300b1603c0740c0140080c10301c00000040c1c5e10b0318041290921491610f81c440c6a110400202021b032250707082018040d158001d0302c0c10082e00d080d9225030703260390b5694000980003c410030202d00d9140d010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 926545098 1250 926543848 926543861
    0xb070305061f09030218070207050105031009050c0f16031d0321120403080106020606040614010c03050f0417011407022e05010b0720030c0d080d020f070b0a060612 72
    0x50b01d80104419600d40116615055001ca407150701181b0310b080008280e01003001d000200000c4c64090700d1032500041c4002d0030101809010030a83d03d503408a4a0740401c641030303465003e030040d8266554681020ba0142c1d180004900700c1c0860840f140402c10025101c1c040100c040b40a070181900c0e41c0b48416084502001d82c00c4c010105800340100c04550702c1d0600c0180c4207903ca600c0b80600703541000740103443d1100c0140050701ca0b0341022428000942c0d06864511800c0c003c1c28003084420141c50245d88900808034a0290302e080402c0000f100001030021041c0c140c02180204405003880050705c0b100082251800c2c0543d03c40151944203692420b00c0303207804041c1c95440c141d44100e542800091300c270207034021050210042280d60074030005941d000c0c1540c460421035006501240d0209480345800c800c1944201200004d00c010300501c0400c4808410000800719035502c42c0302401496908102002d417103c15160001624a80c00b80c03180c00150b40e4207444d410b505502d02c00c00800504403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 926546348 1250 926545098 926545159
    0x4080309040606051e21090a201008280c030b0f0d03140c0123060315060f0303091309171c02160210110d2a02011b0309030b07030506 59
    0xd003c480503490801940c021440800902340b0800141041c9113507445000d0940d001d8410394090740d5559862140e920104059810b1148556442425502507401c1429842d56898200752421484403040d0744200f62895a81d20208400307201801031201403008005002d4200400b4203024000c40d00410f00d030b41c1030103103c020607032800942510241c2580e1305d4404007206050105400300f04224886040c0d6400401036000388070304c03280c450b48003095520180c12075019103109241250617440c140101d03030b11043c0240c05086108507107540003008102410003560040d01494445d14525544405c44d100b0849410f01c0860362006c2468280c003d50024035804501d10b495610707038005072144109503418408540750940c03160f4519041505084210802c203080101c50401808440d4240014584041d50b2071a2503107030b0380451005031000000e1611240c0c20b6540031004204041e486041d00c2c0030f032440780c0081d8880e6103c0703400035010f031102075075100d910440d180030303101e000e4900103500c44500c203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 926547598 1250 926546348 926546377
    0x110f07030e21010902011202070c050f0312071a0106020a05060f06041b030501150504060813050a14070503120c06060906210303090d080f1303120204080309040606051e 74
    0x40c0b1a1088081a40c540c00704900740d443d1250081550303000f0306860b84500b0b200700b0552130020b85545007203519007503001706403040e420070070240c0c41a141040040d001400044140d035a400c0c090a010a900f0f21410b000c00d0000c60481c0003041e02403002c901a803210384d200d0028500d82e202c8841c0a40c1a9070002c0c03125410558400303825080b01030a01c8002c42d8005141c60015455051480a1840c00d54104001c000d1040c100001c10450754840c0c0402d501450044181500c0c1c503240c60441e0602c00900d501402d006c0342c812000c256008007058440440348124100c0d0701000d42c020700191113000701c1c044484903401000001d003060811a02c4694408001400703c0d040e500c004488506032030042c0001c0c4420740c4040b04024a00804010500c3c517141e5608050b0020f1402005030b510980006010882c080c40100e07001c402c25000c0d01c0c1c0ca49908454180541d1103075151071521f0b030f07240c0214503618403860030210005070700f6004408503070420180c040c250901540c2500071b107455900c824050304840 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 926548848 1250 926547598 926547619
    0x50d11010318030f230d0e0f070609080c0301060311040c030e070f030605010e061014121e0f0601050d11090301020724062103020a0c030b0a110f07030e 67
    0x80420b1030a0b090203210340c1300c107000c1d0300c01014003d001c1030a2160840c20002c81c100c89801d03200201e8261021400b04203004a480321501000d10700b405056031000c1441d2241e48008a4596004544402a115280201d03020100c0030302c101400e85915100180840b02035002c414921704054000c071140741245d05010510001c0e1a540504d0030500760701801601c0040d0740107008110442c02824010080742c000312110303062450001d2100d541111a031001d1000b10300124083c11480c8041d1901d0499504280d09946020307950107081c400e143c84080030301100c120014245421501c1c40e039014000c103960b00c90810150081d10b90003862443d040c007201c0e56007071280402d00c0c3d50074002848070502c508109011102907100c441800030844225000190030038009028200d1224084a036401144801b240d00c00304d80c4c14281d00300074800c1405007281e02060004024002d034004402d0240207040000c00601d00a178a040d04075004e5000b0b00d0598407403c00402011a02c01d11501c641c9900081600035803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 926550098 1250 926548848 926548871
    0xb010e0a0608060f031609021e03040c030b090a0506040210021f0c0e0a12081c020309010e06100602030d0504051207120f03050609041203110a1701050a050d110103 72
    0x80d00031a078801000640d501c010003c007828a48034407111800160300500342d9000d1030700c01e0705401d0518001c1d10340142d4080740001a495220f10390746180e13200c42002c2e030f40d00d0515041100c0b03015810f0200b40e868a41e003001180c1e60900000307820500641040203030001da11141d08202454404e01003950441c03185448100500d41301c08118065211028000a90840c021002038500d4500c21222031080b40c9003001000742c0006030301102d00540e0701405aa40d6180103051442c003101001c0360074545140b010041009900b8150f208455003054402155041d03a10909401e01d004514081c403c010b806c24420f00c0440a82908681c0c1c05c68815419100711103940002d4801c10b80180000743e0310310202c416400c0307000342c020302d03007001c44190740c41c0610282c0f51190124506403009003000f0444418041040300f55031207030340b00c82d00e29030382803208681c0c0d000030700c42c0204011110268425004460800003074149000c1c1c41c0f4004555000c0c001880030021600c4461001e110384d40024141912503504401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 926551348 1250 926550098 926550109
    0x4050c130603020907020a050d030e030f070803070e040c0e0910080f1e1504120201060b0d020c010b040603030c080c070e04080c06101a0d060b03010e19051003060b010e 74
    0x440028000050721034038600420080680240110f002d6401c080c62038400302c0c001284a000d104801e0030085802c98900c1c00f01440c520407440d1100b4503240c04603010381005080c81c01180220140da07109403c00a04604010885000d5071008000c250303888035203e51414540041a030203082e20f12542138099890021038102540e10007004596001040c8548170031145d40c0c078611400180d01c0061102d044c0c8004140919040a0000390051001589140c5603504c00d4004d100a0a4044051915a407601c1c0400d0702a4004442c0c00c0c240b035091051110160034a40318440403207400d540c500300070a025440c6d000c1c0319441b8140b010942d0083c40305c08a0703100b0140a078280564800e80001d542c42101e9110b0702c0c10004090300e118100b8003541010824181c25903c0340c44c2500090382c0f003540d91400b42c00c60b03100a00296002da25032802c08000091060a80c4011503c42d02d5009114030765001404104012240103c0d0180b0400c00e8035001403005c542c1036803081d60842d0060411640ea540308800041 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 926552598 1250 926551348 926551369
    0x60f0e030106030302030912010c080c0705011b030c020d03050c042c0f1009200a05090a0b040806010807061407020f030604060c02010b0d030801140402040b18181e04050c 75
    0x60151b84005070301c01580c20701c0032819180c1c0c1c0b510340c000c1241079a0103900070602c0703070080d144c452031207400300e4404c080c031100f98807940c103070413101e42c41e0340e041c1c503c0c130380301802820002c4203c0300035000300700300840c946010b4081c0d64440c804104940f450942494a00019405400c183c281202c040510b8200c00050080303a0134000c000360a4041043d15241480700408020341e004000400e060070007008075095204c0309451960101d6003da902c4039040001243e5500401074241c1d441010408001201d01e03e107801041916102001d0b144541e0325a00010741d00d08062080c0380011300c403400c0003000e6007503000140c810544020300c01d040c0d9000d03000000c0c0c607046003a40c0649400d607030741303641c40c1c5d0854092240003542d0b402a24600d031940e034941c4018081460510543c2c1e0700400d80c02801c1c0070756580ea8100c5010380200c941c1140c4070140014036101801003100c286010394040ca0702e8401d0200c0080c0038900c1080f40b1681e8207403034140111450290308c80940103e03036600c900042e007450303559111050b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 926553848 1250 926552598 926552603
    0x312d12060207200f10050c011404060f020319020c1908030916081002130f0f1706040c05060a031d16050405100302010c0809031218040e07060f0e03010603 68
    0x15882d50ba09040a40c078034031000c982d03588400314412044125440c0d600702c03042e95500c2200c0010f160800c1500981d414401e503100a2000c0d46460444030b1000b140003902c0d40102d0080000300550f48242c0c1c40e4404910064071410300b20350380d05e55401e61624151b0000c00d122a034000c191000d00408840000b00d00348000005c548030f450100c10044196010400a00c00000c810039518405103004403058560f101c2501c0c4c08080c40d000a41280030030002496a00202079408450300601d0f43e8a6216551181e18020707001d90443c10f0070140c060820006005004a800610310403c0614140401c0318551119202200b40343d00c40900c40c7c00c06050f0204040030804000c040c0468210014035041048000c0d0045440303245464140440380c0358445242007aa0742c2030809058000d40b5042080705401500b0701c0e2a8144155280b101c0e0421550001d81181801091421072682d0380310104001d4a0350448901003507441050104007a07071003405a001d039101c841c14029160000100030a00b0349000360401e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 926555098 1250 926553848 926553851
    0x1701091203091e120507050f0706080402030d0801050a06032a1806021b0f06040e040c050a12031d0f04020403080316090b070201030c050c03312d1206 66
    0x2d02c8184000842d060303003181d00c61403040000070501e940d502071100d040c100d400b08004e00424103034204802080000c6910150404407909580c0d035581c001c0019408540407070207405041044240c0e0760080702c81d28140c41c4010510f800050814800b14014420220306d40b6800448400c0c40303416100740c103900245c0740f41c5036441000d5414005105112500076500c4501190301c0108031005540f11000c1615449404403400c030f4074200e68000190041c042c039081030461400178003d2000308840c904501d0102d8806855071240035580c0c000300e1070547c01c0c480000d4045901d04a075001013540100c21a81c40d8180102a091104159004241240c00680084900ca2400001d200021030509104100c107880c1e458030010113410f01d41120741d030f80114000281810b4aa000c141140780c0900256150540c00c001200d407100c0001e425444c0c0c694002d00982401805200445440d40c04c1e0601482640d03800420440c10701c00442190440c52030810314001c2c0c2e9900302c03101080310030845203001120b5005120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 926556348 1250 926555098 926555111
    0x20a17060907170c040f11032a0910080604060f030c2d0608090a1e0317060d03141306050c0f0a0201090e0414160e150a1701091203 58
    0x20140b4010342a000b40301c228034141e41d0030114510000b10280c0010081d1004241c9000b20303104c6c18050308544000d0140ba030004801c100200007032242a202c0b429428540d4051100440d022806510464101e190002000c0000a00c1c50740905185a00640054000141e180d0340308511021602325030021156941604d10030042d10595403c00160a107200c03039212819400005000c00441940c456102480303000000580340b502c0c280184202240c0020b0814400d01c012010318a11031110a01140811408a07207030100f40d85042507248554800380161800c0200c0f52000d03254000100101e68845038100003d16003011080d0851004100ca500d0321074440813210b190078100741c0040c1d040da480341c1c090303001030016070f030b100c580e89040f40c05180010015480300d08190031720070540c0c0e8400e07481d44150744040c0400c20403520080304850310005100b0281c0c5030b44915259250403160b00d04d40c8001001e00901c000050303040d446000c040c0030800010180c0080d40c0d282c041000005140000c08c2d510310 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 926557598 1250 926556348 926556361
    0x12030203092d100c08062209030c030206132a24090608071e05070606230a081011070507030c030b0606191107210c051e0d020a1706 58
    0x5030700a01c001444007881500400f800060801d07400400d503502c5480424143c2c07d0300640400e031000804104d4005000c140584d04000d0000a08850100d005100d400009452805a0080040e4055200303400c08100c00c4078604050001c040d034000d181c2c00c00c0c04203900050301d80c4402040c5000c414801300300a40c6420400f009816120264008400d00c0740240400c103105038030444041d07003d002c010560907540000002160240103d003002480079160103000704020480481c901e1903440c00920407031410202400b0310951102d207105d07038070003a440511010308145682e00000c0100030034481c8139050034001d0721a5443d0000d1030b8030070303104412992414428049080a0a603001c0c00641d265403030b02c20309845502e001c010b00240d8000300706c4030006280d105001888124020401056045182c3c030010060400800c40c004003152403800707580e000201c90030324044520fa4064042069808038644034180403580b41600d07000c0b41e100910040200e04000c0d0000d58922041c1c04074020000c4d4070301003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 926558848 1250 926557598 926557603
    0x1b100905011103011a03040303091509140f03160f1505090606091303211505040e0a051c0903140105061002010b1e040905030a1d01090312030203092d 66
    0x50341c0d600001402080180138020540e0000c080d180740300b60444e1b60b65611400c0c00c400508510800800710544003944040e440301e55085044102e0061203c0c0070744c000b405950030351310350303014409500c150010b02c40f000607520740740400b40710180070b514240001a1903aa801d425881d03d4156907107040d5845041c0401882e04000726984100d041d00c45421134100035610305000100c1981c01010032981c07485864003200f00c5010018040007488080c4607888480350344030001c9101d03004044c0100e2030480602d2610400040d8a20516000f501a10022003c00c2c03c14407001001c04484043c441c1000001000441240703400751244100c03000001c0a0810404020b98000c003403441d082168100040303080c02d59100c400d4298400000e04158150120300000704026142e8a0303c040e0141c000414010106a0400c0f4900500c108102580464800303030030040d24030ba002e9010140043c541070701c1410b58580213500868205282408560001c4c031b100c600340b200841002040800d10003504c1d005c0751020f504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 926560098 1250 926558848 926558861
    0x5071110361202010603081b0a021306030204051506041511071706060f1c050a0203030412020916050f0d0e070b180904051903050c0106120209070203130b1b10090501 73
    0x791000313011003869520f540722540908101841c8d16507903221000901c1604104407a00c0c150301a0031003514040000101c001050070384820382c0101e050400040b03c0b802c0f0b00368241000500108200e04240c2030480480111028502d10002d00038624400719082600700700d20030041040c0e0350091510f81a1448040c10000007809540c0a0204002c076000113a507812010300c110400e80c565010541c441e82040c62400a035844040c0d0540400a00458079404840901c81007500990700d0042948501c00301c0d1160000018040c0c2c0060302c1482042c203a110410700400c5040400c64000c0780007030f1500507847c14002c0aa101d0034405400041c1190002c0b0011000510b4500840301d140a624054580d980c4650150003043c5140311140c0c10321707003050300450607a0482100c0f10020480f0a881e01001106014100e0081e84030710554400136040510020844000d400f204210b43c0c40c4c50318110714100355802156030340c8844500c2d0040501800782c04c1282143c914495040810801840d0030311030308540d107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 926561348 1250 926560098 926560133
    0xf100f06050108280f020408030d0501080307050a0f030e040c17060d030e04090303020708041517011511030409021204140303060603131e0b0a0507111036 68
    0x48040402044583c541500c0300303490400200e03079013428400e102103c010091640f528160620208002c41c10f1700f0b0001c040c00e95100c5101c8100f00b540d0700d845496640f40200c00e00203000f0f40c41482c00340f002405081c001c0003600d02c203040070400c0325003a5000406445030034040c0340002e8415628801c0741c20050b101c1d40e802244c00e5403030803006511510300800c4070b218003012078011620703086142c0805100ea411a80100c0e04104a10344981c0c542c0c100008080c0c5d4180319400141040041450f106070312041c081c101c55412030066561568120b080d1505a440c80045500d80024003000032480c499000901c0f0002d26090010311034030313007072a1100c2070740310320843c60200e81e000b402041807640744c5204070303034001164002d01d103d09078072860410302c0c0c02901030075455913102e01c03c90081040240c40e90710f80185100c050601070f60b65079070340c01c4070240e11311010400d055000c0e800011811456920407900d81882070310b140c072440d4942001e245c02d07400c0304000780940815415014180450190f52850303006 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 926562598 1250 926561348 926561357
    0x201170a0f15420f03060f32040c2303040507230301090b041e02011209060b10170702030c120c1f050115030b0907050703020f100f060501 61
    0x181085400c44820521003005141410320340415420b040c0f40b21880210000d051040301200001d80c4001001c250b210b04407480460f05182e00410a0b4001c12524002e603052446980e0001120000d90052050a203180d088000055038401d03005032514040d00d0710400258890303003030228501214400c015281d0080e11654013041c42808005480400c850003202d590080e4071850f1281c0c0066811401614a0500d91540c6002510700401c006e024010344260702546010341c1e132084150004481800c201d10007030020782c4000507488150700c80da005a904500580d000162070103c8000704680a4441070104003140d05000707003808071003281008541c4101e0900c060f50501c04c40000b07042e03a8503100512060344040100b007148182c0700130002d4540b01c01d105e40c000d0010940c0e03500c0c890000c041c2030007660800c1054070002508640240120b01e4a00b001500c06181035803030010456080d00100c10440440c094051080c001000070040988801d007048000140d6030307145a00781045401350ba000301c3c10700 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 926563848 1250 926562598 926562641
    0x60e092e0f140f010c14010e063c100512010209213003070c1b05060d0f092f010e010203090d050c03100e0c0919090201170a0f 56
    0x7a203d090550000050a081142c10300e41140b034026500040c0d04280b620561a010100c241d810001545600a185d403231000100c03500040c60326030075403902a4000c800d0740d5088480041801032801120360002c1c40484d400f203043d4840e800130342c80c0c03241c00e43e454000369001304031040e075880d0540c44080c41d00400c07030311118504002c0c1c070640d484038444844282c400300600314118140003400c030b51001144013000c12a65921b400c56001c0c003400c15502c1c069696004c0c40d141991000401030110042d1540140341a081c822000700e5400544501501e02e4942d91703c40c1d00710b0780000c411b041d0101c0c191a07803201060140b1150b02c84012440501e865040c108052404100b80c41d98000c001c5421010048d40d200c4c37003d031700b0341c24018544000d00c0c21154043c415900c1d600c10081c0d42ea4000e00346a00d041d016955a034299a04014248405490342c1908910109024141c0581d41e44840300c03a510604040e5030300101071140198030381003100d13045101a181d40c00f8401404a502c901340100d42d528001c035054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 926565098 1250 926563848 926563889
    0x1515130f0504050108154813051201090b01030c1701050c040320030601060c031101050105150703030b04110403140d050f160b0403110f010204060e092e0f 68
    0x751034800c030308411000c01c2c410100e0008816190b1041d0301147c00b03040c2c2030b11031010144140d07030507a150030900d80e40c8032108a259000ca60a034110765044c2e00008215940504003010400040c1300b0440000c025980d420343c40000a07205640700c0d009500480c0580500c0d403810751581c12104214042d490182d2400341081502450001510180c86c2c01c060228451191403003900000a00d0491142d41403040500005042d940f20800000e4140319a6500040c10591020b55090314000c3c001c42c0c1d44084041c030f08950700c060369009403011502038980490303400c19000104045030a44540c000340031800043c03d00502c04440003200300f5002d2803005280200c4200300c001c0803401500c0551040c094002030f110a20b04480d980071a000f600404001200e08082c9401b0b861503008844009040c02601441c006032101071080d00e045905c00e88038004034070081d804001d41010018400e605400000401794103c4e02c00b14103580c06100074007020209a03040c400c01c800440801c0c0d111515030010300014080 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 926566348 1250 926565098 926565103
    0x9140d03020703091206180503041707050a030b33011412040204050603011d060f011e06031d0a050a140102090d0209090c06070506070806010e01081515130f0504050108 74
    0x12202081070350050f1741d0203450840d0107418603020020342100802109814003101100a00c1100da804503d010102e1140000a44500390743c40b0307643e4000354120040010680050345189e120b030320515080300810320315240f030b8071701c100c501e0001c4080c01c1103010b0b0b0b6001f175030441c61080c010404110340c0e1f402c1c40500314003508900d500400c000d005545500100f0183e803000d401401403014803032440c44a4442032000300f80d45580072105618000d554800020301000f6401480f4401140c0b070004074003085c18018140d004c2c082040b4001104071404034100e10340c12050008001082c40b660241440300c0e00d60501040c54a44021303400d0b516403040103e0f541e80e60741c003a0010401c0307a06590400c203994980400c03a0130042c0b107204030780d0440c20000b1138208121002c50480d120b0a0030b030310740c200951100d00c0110b0f8010107500c20349001c00c43e40780204040c408a0f504900b4440e20042904c05505010148151150060041c44180c40241042406441d10086056010340411303201085a50b140960a65 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 926567598 1250 926566348 926566367
    0xc2107090501050325020102090402220506090a06390b0703020c0c011202070813090f0b0d061a060a02030703030b03011503291014031c1b0609140d03020703 69
    0x17000c1607440600202168001c1d0162110b122000b00115120b5003520001401c011030241030a40c090301c546004130700c51901100380d42c0401c2004d0050584142082001d403103c034201c05608480303603c000441d5180c100f4200026038210b07502000c105800d0004e107800740038000d0107490710701418010701c81780003d550005450900c10b83c00b464540c2501e003000c1c0e5000024410528007a02a42e000034145000c401c09442e4007089506080c1c1c10082c41825201e20821288813002c51944a130150b1000000300e01c0701c1d08a00000036482003040c881055180000b070341a8080c160200240e0404079003001415054840d034141d03030400740c000b1b102d84003541d0314139496060207000080c40b200c0b048926484001000425400156201c0425030040c2485180346c4a103080ca0b128203003c05c01044001c4007139040110380002e805040590818010b0304840042e00c1d148480003050b00c10140d02d042e00c0d00401d456004501d4101d00070002c0b0503001c480701003031508200c3c903074002105060041121500095005c0c40d5032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 926568848 1250 926567598 926567641
    0x61d1008120f0408060a06030c06030903140c030d091104150f0302010f14030c041802130b0a030906022109150c09061b01060f0512070e0c21070905010503 68
    0x107642d580c49880351200b5809183c0107441248078440c00c0014004084e032140e070030b407800740310100322941d5180400c8040d10801e800c001d00040b06040c800020010040c01fa0001035103400a076802c000801900d00d00711100040c0980c6d200c86800c801c42c030b00741007900c600144502540d00010402d401d01071a1682002903210003810861007401103a4418400d284c0504420b101c04000750f82d07410402601009500140200358a1030803628803d4407078803403442201c24102056902c6446145410500b640a8015043d014107064231404400c00081d050320081c12094081c8242503194a18244551344118004281c82d4441d407200c1c1e0074070310a0502004540d03000c11982c90310b0b40d0b16071410020170803078000c014601240b000d011300740b9002d070041034001005568029120511050f0b44000b00580e14010440c142c1241e0880b2070180002011406440c0e80030211000851404040c4108550440b0700640283e003844090380030711203a19446201440108024a402820f500b07000005c0c04148002800f00e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 926570098 1250 926568848 926568883
    0x60703020a0212011b0e030d0e010c020f040b030307060f0b0603071d03120304080c100b0d030332010608011211010e120607050909061002070b1804061d1008 69
    0x3c03032480720425005010700d2040c08165010406110f1400340080d20101001482809816030403e02c49105808000401c01c05075142100c0f5a10f507000c0c8901640200c084a4002c2d445a03011031080e04c003040105040341c41044001244428280404c080700c0c0d0219844e4421001001800202ea60080d910603028070040420030b42030350001d001034034240701080c05814865010080000340185030020302190100030054448114017000c0c00030407124801c2c1c41592040e90507000d20f01080c420341c490403160648800704c080a90134101100c40030010b1700e40803008001083d0052088550200d00d1500610500c51944130b100c2c015030303d882d030000045e8075082c100000521040811345c1d415102403103080b5000f05480c2d050a0101c4000c283e9401043c040f4007a0f80400046100341c10324148a800f2421640e000d4401d81d0704246080c20741f644a02c0d80f00500c2c1040210700011955103204950080c80c0c0152507010780304500300350010b1a50014500410345603d00b50400070020086080380e0350850300d164 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 926571348 1250 926570098 926570119
    0x7080606101407050a032106060f0c1406010b0a0f050301030206030c0703051b0f07050118030b06030a120203040501030507030b0904111315080705121513120207090b060703020a02 79
    0x40510b464021160050110311a0031010000c1c1b540101f03c2000c02c11040c83c03440c2250700031000f03940507204107105107000100c2900380e143d2194443c0c1c00d1801c011b8803e000341c5500c8a0071407603051524400307030400e0001d10030015200c4031258100e0b04454009c003550410300e05541c9190005015404014001d414101000514204051058003220800c0a080c2100d43d280354903040d07240c2d03175290341d0706a55203640309007000440c071907014409001400017400e40b0b0a85032415640c0382c040c98080071b0041d6130184618800c0c0c800107a1a12100400f00d611a4019612a0324001c00181540c2000d4540b109140c034040d16080f881d140c0848040d0710a0300a04580f0580320404003296180d804440781041081c0361108c1001c41404805014080303441140440d44000c0e10350007088103125114080201691180510300301024800b41c919500c042080443c0c1712080060321001109004280d903e80182c001103414840380d100d911400c10b42d20020345900c0d040143c01c4d60065601c559441d0080d104c1d4a2040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 926572598 1250 926571348 926571377
    0x906080c0f0403021e090a020c0616020f0604050604030801230103050712060f150f050703030b0319081c0c02032703070315290f0d050118050708060610 67
    0x800c42d801168040c007a6266818142c1c80048500080034026103c1c04020000c140064258004c1e5400314850b038002e000a5100d80414000d4120811505000c0d80a1058520040e840030300020388154010360103401c80389050f150003040440160000003810f039014803070340118101c0c0c010345074591000b13003000201d40d243c020050b07841040f0309003003140440c245030002c01e0340010980208101c50040c41e4003006103009110503981183c540c01030780002170741405000d01192107500300d07000408000c0c0569070b415006050865500c031807400203890310750380010392105e8030108241407c0040150381c006c100c19040e0400081d164400d40403020701300058a02100d540882140c0a12000742000303040314005030f5203240480041d90254210760f07403e41f4080f038140010b400d100c0c00091015a0018001d0070040318010000780e200400031454004120b0480000000e40034440e080f1381e6070307052920b900d240752140340c0146000d0068010f900369400050621200352140b10b1005180d40075030800403902e01f00003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 926573848 1250 926572598 926572627
    0xc030f0b0609010b0d200c07060201140c0f180301150501020d02060c0409020a020c040f1b08041203020a020a0605040525030c09020f0d0615110607020a06021308010501030c060f0906080c 82
    0x1650320b6544514001810b0507d02400103566089681e01c1e0024450001009548040a50112051103014100300100f00448000100524100c2c040c1c040300c0e0b010b0280840031030300b11401d81d0032580d040000700070244403940c3c042022454840c040d100410440c585001c4508441c01688220810765801150300002c076402440220001c1002501c201302c40b042d2201c035003000c1c0015401d040c02512400d404440524800d4100b184155080015400188060a0100d00030341c81868900110300031100d800e40000c805d40a0140145d001d01c000305055030920f41c003110007600d40248030f5a202418042000054500d01c000c2c03003200c091520050b00c8901000c21200799101d06a50315070000d2808001049401d41d00b2040711440740781d03070341d40406041d454108503600c40041e505000564888490500042c0c1181c00800740700038412250f1945a41d198181800d4030f000307800460301050310007000d004290f4021640100c4200d01d103000b2900c54948040940040c1d405080b000c0e418400180c4440c5c203e111 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 926575098 1250 926573848 926573891
    0xf0209060f06270105041a07030e060304111e09040b0c0f1201090c11031c1d010501030b06014407020f0c040509030405011107030c030f0b0609010b0d 66
    0x50842c5907611410a844082e000c07071610500e03c0001100000141948100144c40a44042c1c1d2001c283c0e03481c1d160702640d000d401c518001c4040107080021fa184507101c1c60040c500035441500c008000900c1c2070708200d0b0481c40280c58189050207840d9000341a40c60400c0190800e030845156130a42d2964000300300303203104102407480760f204001000141c19404105440c100e40f0400d40802545500d100119000002e49000e00145d0703106212158000c5681c0282d00c0d80703003904001c00039617a113020b000186070140c40346e51401e85035991401081488041055240d0104003460500b80c0c10a0980004c0e0824949400703d200d1450740c0d11011080c0c0c542c0d81995070400d103080301d0f41c0b0117500d40468025917903441d440c4000d040c5d00135034a0f9610541000d0003942d0041c101c540203581024102001103407044541701c403901042c800c0a0340080410650b04060016500400e04902017441c1424501c1c0100805402240030740c3c501c40041005070103c40646c1d442000100d00407c5c014040005c42d98034159 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 926576348 1250 926575098 926575129
    0x6030b0909163020060316120f151a070803010e0901140a0501030201020d0201140c0901031407020114010e150108070e1005040f0b040f05120f120d0b04090f020906 72
    0x3950010f018030203007055548100440c00201a40c151600081c8002c6000c00d0700c0b0940c8101d0200201c1d141280200450b4510f0503611900189020714407140e8402e540280c58000300c6131603c140c050001c4485404c80d050170b0b80010301c5a41c503000303107035803442aa03110501c29804400503940201d44044000e401420000c550b00c0c91040190414056205c0100400c0c070081780944101040306040c940103003d04420b4548880600031203654071170351400e030b6a11440540b41015615151405e146014485070385c01070900b54000110740803d04030f407010b4440b042e0014400103003000204406080e1080628048403400c2c60021450b0300e030351005482c0f0a030350010b401e501c403080c2100d03201c1715a4444040c1049601d00340034410610741e0341003441c203184183d000325044002c2c03a074028030950404211251414449504554007200c40c42c40c064140b0f40f107024021148080007624a007072005a0050300981c1c20100c3c0c003001514655035440c0504110b1141c000d004910b401c00184859592140300703912441d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 926577598 1250 926576348 926576429
    0x620030403060507120e010b040b01020607020a06051803180405011a180d080a0c031d0f060304210302190807020c040906150e06030f071a070804090606030b090916 72
    0x8104000c0d6008e440e020360b069002c0d07850f080340e040c015880001c1c00da004008540103041c14040d40c2e1250070284c08000d1400403585d060007030303c7c6e44003c000c000501c0c044018900c00e0b041d0210500402090b00c0e8113038001070780140710070309072400c8a80160841e80b12001841c18041c000071144041740c40c0303c4140002a000c020003044080c2015008105d445180f480782c1d50341c031800718680c90551158010880441d8100385200141e03d030750f052100066070002d0003002c04034080e04220a80b262002e00d1130700c007800082d4022036030508240d07892949450744201070034588014500b8400003555100507007482131180c0e444003541000d0040b103910024000e42080710380064240c807107003810703038078070301555454000d224041c11001d202401140074070030396600440f040c9001900d101b00c5000d50f00f06810030344a81604010005402c4014800c400041500d500c01085000f004020800800c6000b08010450f0f00480b0030301c010a010592007070280c60f5929209d0300c10310341c00c540340111003c0500c5000d0142 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 926578848 1250 926577598 926577611
    0x3090303071815030c0f05041415090a0f060e0411090d0606030605151215070c0515040b330411040b130e090304060c0b06120d0801062003040306050712 67
    0x10f03039040c0c0000c203a4030b5094980043e114000c1c030044810344507610680c51009500c0303614a00d1842c01c4140103580d030744d045080c02d041020b01400110420310540c40060720a040700c0080010701c0d008005c030f4031600c030200c40800c034030155090140d6481c030030013040a01c01c80400e07034964100403ca91003c0c01541c0c000c1d400b080035142102d5100342800407502c0130303480303031200750f4640f6202e003070019522280c80c5908400800f1500d41103825200035600007011a16805241007801c51112400d8100344510b00480d0203038075500f40400d4104600000c030910321010442c02c1100120000d101081000206081c1c0b80001c0b0301a101040c0c04150045410020f00d070800016034104140c4101161429200020355502c1251070340ca4103166039100b28480c44011070054100440451000c000b480e920140290000781560281c2114500f03010340282841c000c03500c0c050040c03118540c0f100310507064416003010710b08000b82d44c4407825620b00540c4801400c071500c400c00240103900c10707044543d000c0c01691061142 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 926580098 1250 926578848 926578889
    0x3021c0c0803030a0f0932010908120a0b01080c0d0f142215020f04030501020c011409010b0a0b0f040b0f04050f0406030809150c0a0503030a11030903030718 69
    0x5962080d0390a02c6114100840c0f840720080d00c1c499500459802025039524541014003400c140e850180061030641002d1a2039004e4442030040e06c80342840340c65059680c07068000301444081c5c001d41304433a2039103040038008071640c0150303525070020709102071241c4400c207a140c08000b03002050010308201d82410329426074106a62003540c064055000385e0105800070300c8035020b074515800000780c00d0119034042c403051a441680205003032118500c2880c50107840b522807509981c81346074592076517952081381c400400e80301c0b4441070304062064001d201d08180035000402182260041e10180003001808034001c00410003207c0c010025000c1081d2615501340c0d982c02c0ea41c002d80300c1e032809555400c156911618207031007103000703580c1e02c070284c1c2e03040894100c14020440040d50481410007010002e0281c845402c000e09207006100e04020340d502d20b040c403500b0065541e54a282600450180103000e805040401602c0c2d0040561070620b03100a0501c001e40f030307a8002940961282055090407000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 926581348 1250 926580098 926580103
    0x2114030d0b03071e06030c230717030603150603240f0a020306010912020a0b04170c0405070f111c080a0e0c010f030b0310060f03020102060108010b0a03021c0c08 71
    0x40550110b0035128650342e030301007160640f03540b09005070810502c0d19003840450301941c031264003440301d880e000b4080340007007011000403141d140c3d41016003c07010070100100003400a9107105211500031041c15414a100402d6443c54401181c1c0c10718940180010840e443c10041d9010000340000c002c002c1c804618101d0010050983c0d881d001c040d81400010b032034824a000310782c091541a503849400c1ca02d001300709085600514000c036440103a041e40003540e488884c020f4805070200c0140c401e200404d40e49001c0c0350071103409085d8003890802040240f491340020780e103d4086068207010104045065650b400d10b00044048501e0305495403d400c050f43e03000300c0c083d11502ca00318003080703580c5001c4911030313a50f0030300841d070350004820a6001520912940002c03024850141c01c0b00d85c55502d1005003025950260000944144980360030002c1d1360f810020395004040001c0200050035004010420700c0e9028000a4020144007040700702c00504012580c542c207400c82742203020301e510750940e6034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 926582598 1250 926581348 926581361
    0x30a14070605070e130c0807080405150702460c0305031204020a09090203100c020c09040f02090f070c08161401090b01060908031b070803040602010e01152114030d 72
    0x50146511502c0c405d0152241d10a035141d60100392600c445c00d81d45c2180445a01038010002c842900039001da09102c1a041c08405010b0b0380e1130303006000d400c00c1801e201a55804108a401c4402c5100f280180520310601c4005a40c0310562041c0d81d14440756003800700c40003121340e00050842c03100040c54032175590801c0009004502c2180d20040c1243d54000c20700981c1c06056020b5816080395440c80258000d951051051b48014015640a1512203000504201044509656240c221401e19046280844a16900140d80300c940c1c40e41342460400104007400024000703203440000620607074002059420035401d20b0b48000c540c0b03440074483c00d80c01d003e44626441110089880000494114066136a51054a00308070080d410007001408105083d45400e101200a004020010a109034140003d2000d00382a07000480e400185a00c140e0131624144000c407017000300840c050100c1c0000c01d035480501001a101d0f4042c554142c1400e4410040201e04e0603040e2100003070300b4001c26460342042 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 926583848 1250 926582598 926582627
    0x2030c0604093c0504050708010606080906010f0f06030902010203070213021218030702010e0f060309030a022a0906220b01080a0b0612091504060b1908030a1407060507 74
    0x1a41c401c9070410241d0046603c0224034074145002019801500a50740d0101303074403900900c1181d100702c0e561000da5084036455044500020f00e80b100700305d040001048514010320341c6212100394245085e07940c419450711400f40c4420181c641d0300c40c00035607200b0000d9171079030768000f001c0040300000c0c454124000c0d0f0104c0c1651032240784050008036400c0d081c1d4140ca02e4168a10081d614000d06a80112007080754540038592103000304104d580151503000242d0f200b0444c84009507030f00c4c0345140010385818101c1c60032900305141300c00318813842c8400007a50b040d030000c10368040905483d89800103c138040d0280100114044103603688135802906c1d00000f01911003030326a03555a40301c4100311016071343c0d40e80804d82c00c41000c212401804001d08441030380700d41e040d41510702c080000c4144c1004108262025104551641b44410071860101e002c102e20408038909068000e1070301000c20349030302600f29901d0501601d151210b6600707810800711460b40346c0c003290400c40f0b403501c008040d0800c080c200c802e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 926585098 1250 926583848 926583881
    0x21201140c180301060b0301090b0303160b060913110103050703020c010c030c030b030303060603010e060d0807030e12030a080a021c140406060608041703060f060304032016090902030c060409 84
    0x1203600d0406102e0302d8180d0300d01b070800c3d5203940e00300380301c1c00040e100c809900f0760940b1003001890308001c610742001c0b5000b4480c070402456414280304002ca4a40043c02c440c02c000c0000300010700084040c01c0d040801c800a0901292a40d03e034403090f0700034015031040b48115400c1000240842e41d00d0741c0300c004c202d040c0342c408100d00403818050555900040312620b0704103002b00014072071908090503060b40f08400070109980028150f45143e81034014140403008543e4012a0780b21500c0d03c2c484c590241ea0f2135000850400c194084014145600503040e102c0c25a07000078000220285030602c100340003a0b90809000c02d002e910b560708161003080310143c0310136180120100f0b03490300c2a07c2c0d46000d642c12695a6600044400010020b98000342904d640f0884880c400c00710750702c9440c0514802c50190301c440c6060700c540c0c2990410440f00d087e00301403503004401421106981c003000d10082e0340120200151001507480440c1c5801050b8001940c03250001c2000942c40741d207500f00780882e44a0013034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 926586348 1250 926585098 926585137
    0x12417040201031b0c020901170a0807060608030706060f06030b220e070e09010b0103050402180a1509020a03141603110702090f10060e010804020913140a0308180a021201140c 77
    0x14980808000b44d0071909e040e00b1551240c0041122140034008060064400040559507035a685146520090301291416107910081241d1b00c182c0301c40c00018581801c01303102444880d8009100e1000c040700c45901081000c42800e51a1401d5128501d80303d0303c50102d42ca103c0d11080c1c564000c000807210b502d620360030100c0103416544039000d114040c03a13001c0d00400d0200341c40c0c0100c1d00c07240f6000b4903402e402503072a5104c10401803036115000040041d102c005907603040c1403400800ba0fa8140318603040c174000001c10700894500c440003400740444245400a03151040008080092281c140d000c0d6226550301c05004804c28000700240c000d0803035000040159076514015107a4403001d1590038041220040020054140309050a60021301800010b50441c907654440c40b00010f102003124807544000c09000805030007115054000700720008117100d61400985640da1040c481100030700407410f800221101800c250851105035180506900701032600300610101c54001c1e840c4140900b10294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 926587598 1250 926586348 926586359
    0x3060e032a160602161d060907031e0b1f080615040b070503090a0e07051e09030a03050a031505030a062003090a0b0a1a060306010513090203012417040201031b0c020901 74
    0x10300c20504070601b018888201d03500c0604104c00880c00030054820f25890340d0403503010000000c0400301c0380c004054000f80d000217460030b10468402c1d5074468524415140084920607401152580c5d020004032800e1452101403942c81655000c1d40d40401c1141c0008120b007401c100780400500740301e0701c0a03200044100d80c2e928102c07203003c501b40c58050114074200300b03002101100c5c0001a080c0320ba412409072a0150050100345070034950501034001580c0807e01c401c41a9160007140c1c03e03042d07202602c0c101242040c0c0003039202c0072085001006540d46180c0442401990409002c6003500c0b9034440e07440f4a40302040d141c407a1581001121850503d000144040e9414482e901540381c42015400e2040380450602c54154400352065041c000213003d0307450003050382c59451014155550b07015841c1c0d450806c0000f034012694400b1510401c0790750341214000d84c01f440b90020860040c0c28503610f80c459000690003044884c0d120101d0b14900410704280b00e0b00405800c14052090301d003980d450b031340c40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 926588848 1250 926587598 926587619
    0xe0a0602210f060609010c02061b01050c070510050702120708130902030f06011812050f010b1002060f041a01080606030609030307021e03121003060e032a16060216 72
    0x21149402e48401d0040070980900b0704a018084220041c1040280c0100c01e80014205801c150181081c110300d68806a400130820300500760400302c135524181c245016591240d0f1101010b5050030186076035440090340983c400c04c1981c00c0400c010101d103544803001e0602071207a52100c6880c840f0800071600000740c100d040c0c400c0700d03c00c05860100c20032588480c401140c401007500b0000c0001d100c0140040342c03110162030b0240c1c155100c0c1d4010320801c50854004d81c2904d1134000894891841410004161358010030f98a50004c400e80c121602503403245018441c1700300d00303036090340c00c245200c1c00801d004000181c1d6078000d0500310b08075402960355a030041d03643e201c111006c0380180c100900200c03944040075440709484030f9140559042061401d2088400fc00881d800308280748002820001d10800b88141c2d1a41c08686000c0c524001c40042d050380c5503a2581c0c03052800d003504020714801c1d6141407140000282c02c3d040701551403507071984029036403500b0088405090111900004070748404 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 926590098 1250 926588848 926588851
    0x20030409390c0212070302060d0f05100806010b0c0f030d2304080912011107050a02150307050405061c05240a05030d0c0318030c181806020d0e0a060221 67
    0x182d95070340011041d0307509102242c80344040252003480340a102000503914403014014145800600255013041c1c011302c00c05079480075048605c5054038010510000710b01143c098155440c40040b955030f0b000c5540428a000039403508d04041d80008030360001b10300925040003040303071080c2c03103540c410800760b4080c121916801e540c0244400b000300000c080301c1c10442200510307403640d00c0000032b03005c40c00d14040c461948240404c4507550000d00c104e50442c0342040b0b560940c1800103495606600d403402c2c000d4058822406207034803840c000706a1110b1518030314500801c0c43c0307890340140302a040c00b89010980030001c10004ca01c03c2c0200000351140e0405442d190211403000b002403114031400802911040d800c0a41076040040e40c0d040c00f4100d1044454840003180302d054901c01c020319103220208001d0f010403442801c1810301c44512540e103201c850840c15540c03c07507001603461130b4862401000b03002c640f0302c4c1c140d03a000c0c460545080c488141c0c041c22003640c14100d6132182280d00350a07189c04000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 926591348 1250 926590098 926590211
    0xb0424020a02070501030e010605040f020a0801120b010515070501090b010f12080d0207060e0a0b07020d09030b062115180a0305030708060d06020301270c20030409 72
    0x2c03407501040320b17621079040031400d03200c1c540001480c25103400c040740545000480b04040d0703d800090b0541803e500010440c0100356030304100040c0c1c0c0c1181c0d1011480345040c42003605c100c40a281d441605801c031001c440c00c16070701c00c008005846461400068a0f102485016884a01d40c40001100809205e4100a441c5e01405440c5000c1d0649d000030f009402400050368055900c081410b41c0d440b0030407a0000c401d008102042107842c0030ba1000b40740c0311200d48000100b01c40002d081000030040b050b0380b50040070446485020b0b22440100001d55282c48803011210b01c20303450404000d5101001590099440500301e02124a200b1512555050840302c02400250200300058003148100340d036540054004140e1b4802444686500c0b00340d8000381c01c200307642218041c5842c42d01c01000055491410011414014260415000f500c1c0100d402d0803420101c00d0401c0f0380a40c3d8070103000326400741c0003c1e03904011018200d02c1d0300c1c524003d0010f58400206003d40640780c120107280940d070b54500b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 926592598 1250 926591348 926591353
    0x11030c0303040803071419050a061503080403064715030106080a0f020d02090108150a14042910111903020f0d21090b1f030b0424020a02 60
    0x202546c030009408600c2003260014003400750000040c0510103090000b0a014400910b50594141400c004940c040c120f81089029200b404100080c1d401d01a00c1c1101d4220380d0014400500c1c1d20302c4516001c0c440310042e01020031480c0c961010300c0d4540359800d01d6941c20301e050460f00e030060621a0009409102e285100ac041c0300411070f03544140d2025611aa001034041080b041204010046c0d8000e01400301220740c010a20b43c22650b4400c1c40c1c00e5100000d8510f420461400e51b0100300e840000e40103400c611194020703c0f8140d82c403607400c10403154190070130007400705441041000120204180c10f5204a20008454041d94070820707100c480f2110100142c00304880b50405111001240903007182580030b80d01242940203418885544911b0054540c090305081055100c0030340b22506001c14400b034038001c814808181701600c1c1c59805503e040021415103005001003031024003507070004111100e1f010400c4104007040390500c10030700300c03019407034108009182418103a0080080e0440181e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 926593848 1250 926592598 926592607
    0x1e1d030d200a0818160e0c1e0d0c1e081915051f052203120e040c080903070b0a060b07031d06121305070b0711030c0303040803 56
    0x81940c1d0700c1602038060700c4012405044010003034048035044080000c0104102d0000c0086065803050b140390f0039000e64024000c00f00b03a20701924010703102e03409000c104030401e0000400d103280781070460f803960100c0000c0c0c951580303000c48600d05981c030910b440c121850410700c0a05803c0d00503030301d40820007626551013003100a0b860b030484115070001c1c003c1c1c44012200900030841e20052013036035986002556a0641c80c0d06000c14045050362514200510100c035284244405500500f40c6403405503080380c194601c01d1203800e02d5600c9800703800c082c02080c8807100d500b50082c0c002d80c21000761602502d0902030044004815141c00c10115011010340d0410082500000d07003004816a0040300940b000403101d4480030b0a002076048458104d010500045070552001c098012802c0000c0c4112f4040c4d10700341005112011803e40540740301002c070450a800001c010302802010060211000203a44500c8181419001080703290215800ba0003414144626070902100302c030300361086c030340056240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 926595098 1250 926593848 926593867
    0xc150e0303180102010b0d030309030908030a02070504050c0906030c2205090103030521010f0503060108010506060f1303020616021804030e211005041e020a21061e1d03 74
    0x2c102c10425098115565019000f2241e81d078981c401107564040e50340002e00802501d0058030741e80c106d0b003001240c0c1c0d00500c00c2d15443c550014400b002d90b0b405803401726180d10b4500902c82640260031401e03902000c080104040040010090011042d1004100c5400d03141070030010030364041130250980141da41001440460300580c001c1c040038050340001401c04004008d900100002a000a440c2d41e406000030050746c901002a10302508183d00200f1480c01c0820014145100d9a0f00300313400a040450003403106544510810010340d0094120760356000c54000210441c0c90340c0c03c049114091190000344c50070110b00680c0d100719403680303840109011420801000340d003180034841d490351104145612541c0144440300303400d400003501051500341841c0c400d5030912488008035140d0310000500300507a03103040001017190450039207900c20609902c090700319010103000c0070b4003860a040e94100814603c1400d02e9007020444810402844040c8510001084050200340558400d1055095 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 926596348 1250 926595098 926595127
    0x40c1a0f03010e07120c0206240a0806090c0906030a020904020a0305010e070f1706041119080a26030a050712181101020115090f060e070504500d0c150e0303 69
    0x8034400b958008800004607480020342b2081650000d90f01a001749003400600c40d01000700390031240c2c0403075580c0325920b454000b0075950f01e080f0034003038828030f01d1034042025034503010040406146c001000b07200c0c24201d503811a503903030654032482050842021000915000684089a01c100720b040602a0ba031a951102a0f40619581a040e4440c60021052264000b1000b44000500d5030101602c20040030341000c00307500300304c2003180000000880040c1c0007284c40104032a8401241600080e0f680c0383d04c4011191441c00070f1a05803050b01d0f20420420080d86110007860191251a030700c10b804000f030004a00780e0301c1e007508008540940146c24010b00001d900400b6883d42500f0000903615030360345880182900903a440740c04210001420311807035140e9001c4180806000c0155803d00c002e14640b054072018941e01121a00c0d082c54040c844400d200c00d0403a14020000c101a0895100e410480100001071207240b41411505142880507409a081052448d0006000d14100b8000603207442 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 926597598 1250 926596348 926596381
    0x60e0c121b03190c090b06040b0316090909050303040b0a0c051b3f0f03060409022e1706030d0f0201090206040914060306040c1a0f03010e07120c0206 66
    0x307034140220f6000600368810342ca020940140611410b20102e0f00e840740400441e02030300710403401040100400d1055501c400104c070303000751202a030341c207a5400d440c104030b40305200381d00714071109420010b03400144680040a14000c40c09031b1101c0e890383d143c540142003258805862080421424002900042d485003048014500e240c000d540d80045004082181860f11003803120003101543d44101a90255400213105902c1c1d1040161620f01002c07801c2c00140002444140700e0740c2c84524000854480d265042c0c144000000c004035100717980014006617403a616503141c0022140c0c040c941803074054101e018066900500034203002109c42d0006c8031000c8450b0960411340d0348403620301e801a1903081c001c20041c03428a0b000242102c090f100c03200c100070007410040c4254021000d02012540e0030b04032004491091402d56000410841d00c01c0540c00781441618510f00040000140ea00920002520910f495540c003040460000303101c80c1280c502d0002000182d004000080840303d81c4071191 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 926598848 1250 926597598 926597653
    0x8070f020f0706020616080405030702040504060b031c0f0c0f060e071a040f0b0703090e060d140105090f0a0c0b0d060816030b1b0d1116060e0c12 64
    0xa400640c0d100c4101c40c6444290342c80800164403203400c11031643c95003502c0c81d5060200e46400480c07420f00f42c46403607490007540d10181c480c0e542c803004201044a03e9100c0844100040c05894901c2185240313200b01d50464040200400c039064640c6d0103852003616822455644100da66400003015250300c1d008255040c08480300b0302c2030031000f041d07584255800340f0800d05d1020083c0c0e039032800d080c41e414034501a41d00c040490542400181c0001e50016402c9060311042249903038241d59540c00542c0560580f01c002d00443d10030742014045001c1034001602c04c0742d543c422030340c031a085007613040d0b503500d040d00001d00b80601d514403d00c01105400d00401d1a821451030100307040340c9910030700d070810080c1c203042d41140e03a101408004100d01411855403000c94280b500000312130024140c2118032070703100614007807030b2380341800c490115400c015240c030402c4078842c0e0700c0c2c0c01c0054a88580201144501c0d0000c6104201d61103000b81380c550800100c01c404240504900780c01c0e000d4000381d000d52040b20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 926600098 1250 926598848 926598853
    0xc021b06040e09030409060e090c240f03040b06010f0f03050a09170703090b1806090a0b1204170a090e10080102130905130803310c090506090708070f02 67
    0xda81016000068003c49022010390b54603460414240112800e07a40b00309816000c0000b00114584049218001207138107030b40e400e1030184111400e020b200200d0420000c0700e030011a60280c01411340c2c000d14840c9200f80900c0c102030722640c00549104070f80310000c034006822110b098241034480c2c1c002d19003200a070080811740481c1a40c80c0700c00c0c00030141e2604140700e808583e02c3c080c142d02c00032020090401039402d03854203a2610501403000c1552401501480002070760100035100d0301e90400c0204254014151503901944003042001000d84060f1244000d00e10301d00e08100d190001c5440155940d21114255460300075a00d40d5072340000d0080e00ca03800b03009400200c280007030000b01080050303040d10300043d40c10700e166181120406000020071208580ca10400a40e0007422242c004c000003c03145c00044030f424030100c907840d00314220805d18071002c003030008220f030000000041c0d4a5050b030034400340e55004103000490707900320b03000c8000a03105070104015a00400e5406040c0074103106 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 926601348 1250 926600098 926600107
    0x304030221010f020910090501050f130f08161e030605191b1b02150f0c030409051e160302160503032707080318010e040504050c040b040c021b06 64
    0x1414212843c1c0d030001140e41d0340004508200f407900316a5010054210b0501846680c02e10000030854003172000c014111450000d450f074100540d00d00404001c14690300c0d40b55004e40c039505525129917020320b03892082a032810303000c9400c013207601d50380c0501903009101400462039610b031400500006020980c0032808190700c0c012444d00d41c0121100f0303181c000300d44200041c440000805075025240c14000500c56281488016906c1194030f40d11546040700d4240c51360400ca110903281e00c58502c110546100000c0c1c002161841030301b00c14419580c0d424001d90a5a22010800e400c01c000c070f40030410007001104651805009034090700500c0c241914204031203450340c3d10f942c515030054442108a02e15a5000d002c5102c0411302c40070504200805800694906001d1235a41c1c002c10074031441040d074942e80e14056900c56170100302c0da220300900030b110702d007440c3c24003c1d240c0c40600c80c0c040c0620705001c10701c80a41014080d6500b0000142d00400165284842d40440882c61002c1c45500540410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 926602598 1250 926601348 926601409
    0x304180c0e041a03160501021f060f090608100509030915040504022701020a151a09070e1009060207060c021c0302060114030a1a0403120e070512070803040302 70
    0x8200010115101d80e43c0950019000401d458a8841c05506480404140d814006640e0119030401d1821900c000c0840c0841d01e180c1d420003a103076070b412100484a00320300010300300e045a0001c604032a030342015900c4d1407800c0d142d580b054070800c43d03100845a00800c8015001d0030400340d2504600b022100d800d04140e211800201641c0c085405803841400e640c03698801094109a100d542c81001d0006241c2d80034295600a0080040c41007860003a5888880c806224480341c211a42590014006a2207203844e50f0050000010540c04500442440c4911420703d8010403a0809664450700240400d03803505030119407502c40e464080340c1110000d00940b0303060086284081b81c03c0e20940142010350304044043c040c0c04441e504141c80b0781e014030705103c049000c0b0f00c05012858005083e05c1c4c21903845007130680c1c40034840075141405914201c803921081e407000c500d46003590030440700c40410200d00308130955a07030141d00a400c0c0c9600200710030030040c58905142280100b050110000c40403210303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 926603848 1250 926602598 926602601
    0x1140a020c03060903090f061e1309092a050a1e0317120703090b0a020f1201150e0a031e14060f04060e010c0206040b13050a050304050109080304180c0e04 68
    0x5540013038803907101156071030452034803070001d210080003030750014104034520400910400c1551505004002c0025000808031032025040c00509420070060005204078a4012a20400750a410218a1081d69030790b04ac05440304410040303900c018840007085003881500c034002400c000b0882001282c00800000048010764480340902c1c01000031034071507451003d441142c520040580040500c1c02c4040c400113580d040c01250444a036000041c3c440024285007a1a4494942004500300c261000090249000f40c4104403400c6203a48594441400d9030600070b0300c4116010080c520607165044203035844032203c050786403601030b1128038a0300480c0e512550500c4001c0d1106040c0c01146420041800003d01407403035081c42d01070080180d071800560094070303010007503c000e00d801d5080713002c2192610a801540c41142c0c0001c152048102c8a15221343e480e8028458280400c500a4000420200200a0742c0845d410a0481010048000c0d079040091219200e8581400b03c140801000b41d1200d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 926605098 1250 926603848 926603851
    0x80a020f0a0c090b010206311a24030c0f0d0206120603010b1c0b06150a170f040c06180b0c012f04050105071509030f030e060601140a020c0306 63
    0x5840b91030001d50800e0780e0681038803c00000380d0f05640c4004c00380b1000c109010842d0b1600f13900300800f08c1100e034403070000400591440101910001080400c0ca114480c40341207a4050ba0854401c807018030284110700c0c40054030380d05c580c1c1d0306800011300540c1504010713980d4240074100500b100c507a10700560008015802042031103500440c80c8040040504013480780b8854840e0483c0c0d40302801720104480320084070b0444d0000c20032110130011038080d40715840940448480c0003e007541b512600300b0b004014400b401d9400309ea415003140031840d00e90300425000e0049411000c209003d0b82402015180a1080030090b0522490058005000d0255034080c15030000d06000204000d0007010040c8184889081c900b6600010b44010004500030203040fa03080710820309080f03848203041d003403403001784408080d00b600c00c07818050030300e082580c00800c07581850450340b0108019168007a4156903030340d0803103895012400242820303d9910144000d040f90300c041303204a40c0e000b840c00c6c01003401d1500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 926606348 1250 926605098 926605103
    0x70204020a020d030507090b04030321020c010905120c07150c020306010f0509060316120314030403031d0f120304081e0301050312090f010c020d0503030c1305100c080a020f0a 77
    0x10049800e03441c0c3d5030501900b604841c091400c1e038032080c1007a520034030303901c1244401401d0000c100b00f01c280b11030703102d80c6528004074485021511106d07168025030103803220340310880c0d89001e200c0e03840d22103a06e454150f46502e40e00d04003c28801c0e040400e020300202402050106020000c1403c1006035020402c260191803244c0000e00103500e8a424480c444101520f480c9c842e400809070909001c0c02000240b04130341541032112071701c0c200ea0400303039a07240c00315082c1c50b0036090010401c0285601900440c41801c40340e141401e000c0e039080400c0da2200302c4424108242e40100da806444140c40d94050341d00280180c510f54504907130420f0161595005032084a118580803004000070b140500203400401d000c16249458000301100290711001000c0c0304905014510b01402c0540d20340b41c0d0200c000540c001c1c201c81d660308080300c0e880a01d030010401c10901038030b05440170980e400c00070060807603d202c90f20b03040c00040a541da1038040c0d42140c070700702085205151800710100f1040000501c01070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 926607598 1250 926606348 926606353
    0xd080906031e270d36091b051318021902013206100c080406080105150906030a1d03040b180f0904030c080d052509060c0b060303070204020a02 63
    0xa41081d100d40311200f40c040304000743c0c02a4a0140d4401c0d0040350114104070740000710301c0311003103641c000c000c1c550310b82c03c41110500300c3c403c1c080f40000d104d030b2000c0d604050440101c201d100312090201c1d60342c400c0b5401c1603040d4030440402c000300c100c840e281a10014000002505202c444540ea50500c90380796175100050307454030400007164495568009402e10780c424000403d41144203000c0c1c40c0c0704090030f910b01407280b940c0030520091184914140041d881842999281e588a0008029003401e0042c0ca100d450508100c030545441c8404413201c8040141c922411947c0c0e0f40c0d00100100040c0c102c5040b0b0304c80c0c1f5140405024001c1c401000030b0030000285684500d01c05c0584103000c002c2d9144c05010311002d00982e003136981c1e80c0b030919034019814603003a0702c1c900b49490829030900416422011140c01c003024031107000720810250f10786400c1d4007040101c00e84403680440d83c800c650310900010416100351440400d5018680c80d0b40908003a007101e142028a9001c24126070242c060b100058 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 926608848 1250 926607598 926607631
    0x51e0d2108010e060a050108063d0201060608010b03040201090f08010609050a090302190528060507022e18060506032b0809010b030a05060a0b0d080906031e 69
    0x21504059460701602c0e03c00303490402440d065012a042d02258012681031207072071000030314542c2d01c00c4180e602d0843c1e000140f88120500e40180c140e440003000384c031074002642d140707001c2805205102d65801c4864940e205c140c00d034130f0038034104045d60010f03100340e04114504401003681c1c2581d0030200c0040850000015aa0f0301c0c16000400f22040a01055505810300d031003200460350018004400e1f415020716082d10041c0c1c0e29115151040704103c1a40c02110300b810741b500784413081c2078807003100d0040c00c0610140da40c64204076110380b092000305090544c031403050549500c030254141280405400000392200d40d0203070040b00949018022241207459804204460138140f041c0c400109510381c8001c43e04a1484110010f20ba00c6070054041200c4600011080300c800d421560b807811010707050780e4074500a818141c2d25950103c0301010314505010780000241041c0c0300502050b60040728040c1803c02d11070410029030300181406071114407854011420134003224000d4054401d03189104e054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 926610098 1250 926608848 926608913
    0x15011d0a0e09070503011109010e0105120f01060f03020310140112020309030409110f0d020f1216020f0c130c0306080d030c0e010c03170601110f0307060e0601051e0d 73
    0x204500790700b009010340d0400480000418104054031041e088c2420702043e02588100100c0d814042c0e1b8004050070b005990034001c082c0c6561841d18180c03001a550113071510342d044016000d138801034490040a0840389020025092034180c40d502c0c0e000145441c080d002050000310050307800c1903a140d030036600001410404007401e4841c100040003001003032424003c0c00030842442c1d01078514030742c60280c0c000038901c2d51a16083c08460ba02103149694107014140302549000f41490180d0300005403160458a0000040024003140d41c018010401c0290064482c054130190400c03079010001d25482e420003241c10001400701884007041c0f6030f400500f80241c03450042c010101c00300c100307040c00001400c5001095000202600400e5801741c0c0092644608004941141c00007000040ca4010503001c12440300c40070000340381d06030082c04148030a186025003c3d403202c20a10605a0058405101030200e1058010f51344000e80010545030a441d01ca80b0303020400e00160212245001448507024030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 926611348 1250 926610098 926610103
    0x200102030f18030d080f0a020906040902030a0b0909030405030a020d050f0a080d0f0501182a0c05010b1806090403093302070b0d0e0109060906060e070815011d0a0e09 73
    0x10445400d05e01641d481c100104810760001e00945242007140c0c000030f0340480c1d0b4840400b1a80100840c070400c41d034bc3d2170000c2d40080148469840107111b00c0c01840071400d142c1d00042910b080c0e420041c003801d6424070315803c000700c402c0315010454a50140410543d540c240c1440124281d60284150030350b251101c2100004481c00d060b241c0080d94079210042c030503c8070f59881600001500080001e84511140b8060078940c02081c03000300d403031469802410510303072041c28210000c1c0300700003e0110b0444c690801030711441c1080e000c0104001c00c030000d103403498070054140d0018001d042c03002c1c4042d141e040c0071940e54482000300c5200c400490340707440301e14660b40d00d200084826201802c441c600f0700e9194101e41c4034a01d00040d00d00e0316105000110442035008803811a40108100b080b43d0a52403e44068074181c85214a50302070403002482d10f60040d407019115800101c0c4202190100400555807140060356905c0035405000449203d82c8460305410044c100840380c03d545880d00c240d4251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 926612598 1250 926611348 926611363
    0x1120c0314070e03191a190f0c12110702012d0309112215050d1401050912040e040f2901050604030b0f1305122203200102030f1803 58
    0x503204405c0b0000d55002c1141c43d030015071340c940780d5107001c015512840302001110b80301c2100300c44c101d40742c03600d1080c0464490b48044403a111a41301d40048009100d60481142d121600d80041c1c200104104c1340158030905540d4166100c000c0c150300030808201341d8980c030b000407417503200c0441ea039a240311050003120507140c214500c0880700041001c41384080c0c461440783c1d04c11a01034054036120705021000150b82118054100030b00850f0710045103042a10003442002c0c0140c00551030325000c40c152040100340100340000101200d03140900e8040d5921148a00600a556001214044400261012052801e1740e0b0030b40c411104408094105118090070690010344a903108020400019114841655004040300d41109032507407032441d48030300f4010601e40105140540c260f03402d00c0c480c0f810090710702d00143d4550550107003440000710717020700901e02002c0c0c80d10342480b4100c481040040007880190006106407820400741c40640680d0b9004a4248400505003511807411420104020f5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 926613848 1250 926612598 926612623
    0x4050c0304030c1202071d0a06080d02190510051f0807051003020706060312180e0c160314180306150a1203020a0203030d050601080603010b01120c0314070e03 70
    0x151441c00d0596000d4000300300301c0001041a00030012052204d070003809110010040c0c0307041000c05511800700754484c3c07e4229100f107402c6140c03031300c081641c140c0040c841038000c21b1600200b854401e14042a11303480f0000604503882e202e02c801e003400e20440b600400b40104c280800c40c154114002d20100d0003c100740e0030000841e401034000700617555034450b527002c00541c0c41c14010703910301617818040b0284c105500083c100400046040b00c08035800344e02400b0380c4040e4000d141d155901c1d080c22480e10401603403ca9170141d012311402e80d4124110450700b940500ca8207203079100135404854000075802c00c1c5803810724500c09401c0328480707050601805500542614544414001c40400229803125a01030100f9007001c02c03441c07008040c02000a54142038004049079110001451400c010300320844810340003c0c40340d00401c03050f05050103a61030000341616140c103180c02c66844c0d08000c20b8110281420141c80c0c020098140c0d002c910032034000c008030303640d03004c0c514202824146001013003000c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 926615098 1250 926613848 926613871
    0x1020d02010908041701090203010e03120a06050906040e010b09190e01020f0f0903070b030f04211416060204180b1801151e080603061008100b19140405 67
    0x21001c1c1d013200e00755070b00318403003c1860340200d154500408080308000d400d0361900c04120381c040000805000c1d00900400070b0300840d40c0b2504c040041e0344292040c0c1c0e0308041c20780d021820714603180d006610f81141500000800f070006800003140a6070603580c2d550048110012180030310f441d4000c46541c4800c15000b54541008005101d400303100b84000130784108004510920b01d5501804507600410501d40501c2e164140500546081002030714215469940324440710b41810644000314880380450b1102e600300019021102195488800450f0b41d001403440b21030006110303840503102404440d840341c468408034001c14021992020320080c860100d80700da2504200304105228155038070f00030b09010401203118144c0c4d15803d131148100e20000c2c2c00482c04011948a04094481c040890884034a078407484460b9403030203001e019a40700340e08000000c640312016500816407054010344451042c200380b0300c029a4108058208a00201d014100c6030424076050003060340002c44550b2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 926616348 1250 926615098 926615111
    0x15030106080f12070606051011012a0e1c06020408010608070510050d09060612020102010609022508040f06051224010e0a05060d090209090102160b0901110a0302070201020d0201 78
    0x49142e0783c0c00300384a110108240000d030712000c010161300940300030940542000596254440c1c0038104202c80c1c040d44400b58a081d418040881c41c4042d901e414540080749481e0701c1c1082141180d2422108a41640001c0100d0030220000d40031203205c40c039a8016a80140c0343c03420a0070442c04d4034269480300703003590700402c0c040c000740c1d8500c8030b00d103484411410200e41c1e890264044a01400c070150010340700700c2c940300d4000399941042d404445424402d030300811140307846114031012809012000d4600c9111a807031600c201020342203002c03015000b40282c509140d600e802601e4851101e0b0072400016002007100a559074440d10459080032200d0781c05d041920048210b52080301842540341e041004d403000261036903c1c0d0703d1051014100191040c3e40e504451403112001c0c190045040b8001e4881c500080c001200c18402d8a140f06180703904001c2501c20b41e00c07140140e00c000341160013607542e640040c0d0400e1100c0c03001810040c1460300c02507110352440c00060b041c803820710b02d9441503905000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 926617598 1250 926616348 926616373
    0x30a02030a031b0f0c030e0307030c0302010f02060124020709051003030f05030105060a03052505090f0604081005061f021608010e0601150509090f060901080a03090317121503010608 80
    0x83c001c16190044c1350170301703010499043c04c4910045d00b07980c164040c061580007109002d10450081c0035213000703884140d00ca0110a204903901d1000340b098452071400c4a00c01c100e202024136054984494503c1101c50164403010040111030703081c3c51451988001e0602002059040422118240c0a41c2444c80c03c542c544004a01588200000281019510700009102031a9525070140041c4600f0807000b00c45d140c84000b40c141d500c41038040d4070400149100322070910f4000300300d505498511000d03045d00032a880c3c1c1034010700f0303000d010740d90302c11481c161140000c01c01c0b00070942610816030040c1034419042e4407218852080d80c20210301a4140f0a000030040e00001e40e1504480e1415642c804100a956044515000d0303640c44542c84201d07075080c4003865280a81d22801603038212402c0d450741e643e900b0300c117940d00b040303940044c0414403404003000810901300e0340c8005c020340441d02d1031809001010a03039440c0821140420300c1121134031454058142407180801800e02c0000402d00400c012 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 926618705 1107 926617598 926617607
    0x4060f0e0a030f0e03011a0d020f12011b14030f040213020d02030610020102120103080304060b0d0623010f03080f040308040e0411030114060d1103030a02030a031b 72
    0x4c1c1c00d4071542454188500c4003241c040072514038500b0803103020720915101e0000143c1c1d10001c0c040c4140c0c811340b01c1001c14490003110702d0000070074542c06038060b2100c5030800c00c5d4408010120001e000d46501e00000c07a030b01306040f40c04003020f9940314800a90348007405448048403a002091101d58401241c01450040e441101c1e0200d603407200310005c80c200c1c050f582c04001b0b02804ac07401000450004002590072a004101c0410f1140a1501152608003810b100300c80050b078944d03801030600448a0030744a444071400464009500d4841040c250090f1030101815005000403981110155042114021540b000220b5140ca81d03885050702d04034801c50f01617070424001ca10103041da113411300c83c0c10001010309540e2002501c0d25000e0000301c00c0041000c41e1034040c1c1c0c51000d442c59600308081d0220100c075500130b684d500d048140003001d032070804042c5450034503207106035494542c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 926438848 926618705 := by
  have h0 := BRFrame.cov_init 926438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 926438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 926438848 ≤ n) (h2 : n < 926618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
