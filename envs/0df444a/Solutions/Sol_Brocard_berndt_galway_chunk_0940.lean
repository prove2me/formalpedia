-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0940
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:17:46.734794+00:00
-- url     : https://prove2.me/submissions/c8a96266-f191-4478-b112-10d570c6bb68

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 168884892 ≤ n < 169064748 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 168886142 1250 168884892 168884899
    0x2423011404060e0d0501110702090a09021008090703020a080f06010f240903151406010c0b0a0b04060f080a03020c01050c031b070b070b06041b0f030e100212190209 72
    0x3042200c90f0190005420400307001d0000f07101860076079102c0d800c6516000034003d644078049800d10550400030074466002c400d220f0f04020074011600052100001c404c8203808002000340010806007050020704015607000e000405040c8c3c84070046502c607004205419214481c01000003100810120504c045520303116a2070304a41d880c1880001403044110b001050144c00d4800000141049850141c0c402c8008800110300d8a0200306040ca45801352001d410003c5200d4500c011942d0f0306030351500401c10050000300000d6030004180541aa0741c01340310010240200065503401c04110085001c0c442e5094541c210400340c015030b0b16018aa00c50310980d8000c0c415214203c01c520070f10310702054060100c800e0b40e5130310500d0035481d5000d07100c129074100d0290b0501000381070a00034000c6a550600900c20f01c9009544020025640c15840318201625483c00d00b88401c03060001e400309178450f0b0000e6682d48083d4440180030501a10600c0100c0c0c030a8003050b108200510941d54880d0004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 168887392 1250 168886142 168886147
    0x70201090317040b031503010605030c011b02040b030703050f0610030305070609061d010618060303080c0f070b13021807080711030f04060c02030d031b0324230114 72
    0x15120184070650300d41d002c8802480400002c0360090f051006035114004106480d00c0c2000c005040c5401e49440380d102d907009502004007592942e821401107280303442004124100c0014070700000d406840d41e242165010b0084040110500031b011894024a0300428101d50b101d46841606480742903451001900203541804074800298454104400b4280200008140c1402d0300c1c104480007a0f602c0880c042c903039500d18082000605c481d44208480850700d1040114615503140a01046001801c105100c00006030074012a11110169010030b40c00c58901840c52a101b003540034200c40c885030681c4140d909610020203882c01001440c0b0501c065aa44556625603440c01d0f9041c03140350050b2601c6010500051282d50140700140004041603521041c1c0d101d11401030500304008110106c0402d810030744000d14044403141c028003480e034035180020303a061004541c5001280c0c0c524021a090010400020b05460041c1020403d0500c41c2c1b105a2120346140065030042104110548825001d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 168888642 1250 168887392 168887399
    0x8041b0e0c030c070506010e0a060618050d0f0803130b0105040e0a0209090f120406030b120c0f060f0705010b030d021516090803130e01060c1a070e0607030305060f030307020109 78
    0x4280165810518030400f90381441d10b250b0b01da5080035400d8002c83d180c004e96204015103c601405044002c0140341803440031920410100f0352603114034043c2500504083c1803110422861050070400b40ea0001101c41d00c1e070506c81e00c0403105c01e140720400c1c1d520b80b40d0b0304000f0400d854a8031858000903a400b00428260602d50300703201e921440204000782c1ca0007520103c4a050000380708245141c8a07580429554904011001e8111000440700a00501c0c080b11040300625000910120108007165080b18081040d000120f142c8940c0d41703004a84a8042840e0040107815041034010300740440c1542c444400f0858100d80d40e002c0c48884050316022a030215041411260a0441001462500b03c0559489803010751031a401011120042c90003100100404542646501e016025902d0000c4000c0d0007910f50700060034031150a030512021001c00304030700c40d00030404941500d00140401d030b228801818042c0040404582e15070207918000540725042c034003c003c940c54103034140c5544d03681a05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 168889892 1250 168888642 168888661
    0xc0d0606090602032a03180a090504020604030611190c02100f0e041e090305030a1103160e040e07090207060b0f1503130b04110111010504050c1203160308041b0e 71
    0x1c0401c040c505c0c00010050507884800030320040035491040c402d00c2d20720748162005d010803606c4550003858890700d031406110069560302e0032501200c2e00a080070508108034118450188601168012040c0200185012154014159803c03a41c0201c43d196170180d072000060b525510218016000210300c1903009041f481c00f41e024103510803034079244a40e4044052107038030072288111000d902243c0b001c0100404071031035000381440540140009401e5040c06a601103418840c40ca50000b40462801ca0603620380326a0711010285402004031049a13035100e40220095001100a07a446030510005c1e500c0d90030304c1c0c40b6400b0450005400d83d40140f4035004410341c81e4101504e428040603a501e0064081070201c0c0800340680e009800c024040195040007402908070114075036226410002000042180810040c0d1104000d98140c0c945401600d000b606500c100c200c51204556205030150030715901c01c4010703205d24851290f80d000e50061900f8039201e6101ca2140b01041c0340341c0c5000814010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 168891142 1250 168889892 168889927
    0x607050306040c09080a060506130603020f12010b03120a09270c05130803090a0e15100e0607050105071b0503042304050411030d05250f0b0c0d060609060203 69
    0xc0c1e444d10000044e107840140b4240030b200d40050350f101d40c40740c041c0700765450250342c080500320240380d04200040c40c580c00300700d00422440c4554804c102003984c0f00300d0a002900300d00419080101a501005510001c0c144a60025001c2000044c00c0030804917564800c0300c00c618205140202829406140240b6a0041d041000280042003002c2c010f4941d100410407103200070704080b070b0245d070312072480c0c000b44245a1115405100400d403440d080c000000000c9400f95034500b02501c4030460350b8040b10065400204000c01070741c1048001139500144401135201034054155581d80c038a1305100504100705140d03001e1400342590704200400c00c12181080c201850501040c0018085486403800203802c13039404440c15110130928000301850b6103014004800852607030308140b4203106e46403210b01d40c56121f2400c1d0204440d141500e000c1801080240070080980c405036038042450070035504132050300031305481200e203420010046206030051018006607280d40d13000f10b0074140012074601805 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 168892392 1250 168891142 168891161
    0x3040506031b03040302070602100b0d021306080a0c140102030a020709180c08030307020d1115040f06090f0302150103080d1e050109060e09010209090c13050306010314060702060705030604 83
    0xb602d800304001d540300c490409075202d2800782d005850340ca85450300190800d1103034904e4103c8540307022096550b5940e000500151260144e90750502252020180d6000309210342140d0030520400c4429410803800c000c10400340e450351001c45082c1848031005a0b0307039014400400b405604038810030b11030100700d40d00c60b2005c000c1228221303201c03880790f86800190f860550010315541c2c20002c100242590100001c0441010b40e01e04601200d01c82d01c000c1340c40317456400f900254840c1a001003024000241960301110b50400010800607a2510f8000303d001100d9070114094040d5805845c0c40842d0294082c1c100d03078002003035620781000351100340b00800740140110b4001d4100c1001505042c1244641c0b80a84000d02000400c14140f6101d1440c40394001d152151903130041094000d07944500000c903800200c0081481d8440c240c5074901c03c00780180350006900343c801c820001040c0600c0208800c00c081c0d001c0152141509d03091003c98075404e045684801280c0d041000c1400c1d41440c1d130003130100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 168893642 1250 168892392 168892411
    0x3010f0509030708032e140f01120b0d080c01060501020d031a010804030c150605030c0604050a05010e0a031a0f090d0903030e0d0c0b07060b0612040b0c07020d0f03030c02010b030304050603 83
    0x44210f03400000066400015074185560f4207000307100d071f11010340161152207411074092509201c2c03600001c2048a041a0700e2020503207586600e103258440040c5451a50fa1000c40c954440500c01d400a009094600c05c05005109046001c04418040e20030704040d0144a4600c0b0b10424401006588100d0041c000301c0402000f6034540c00811080f0240c0c80031102c00120100e4038520700002c2614205c0302c03103689845030074100f000300300070781d950302500c4111803007820055a035840c0c1c03c0001c2c40260042e0300203401d001616500e14000c0d444078030380c0d501c03072001e480160f051a00d4462001d540d81c1101580700e404248800000d20100b4014031b0341d00d0400c07400034202c1c00d1203207032940c4004c101d0032a58007009000e0008910041040b80a00601d0081ca409540c5181002e07138280e4103405003580600040c003811088004590b00e80c1407801101c0403075402903c02c0c01c2c003a10324945144040c0700701c2e074141c002903c2c013440c00d120284103001d072552000c00200210304090418003040002e46c00031b04270307404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 168894892 1250 168893642 168893671
    0x7090308160206070c060906021614010e031507030f0513030804060b0a031109011707091107060507170c2a0a0f03080f0109060608070c0f0b130203010f050903070803 73
    0x10f0b55000002c040c8148901e119646031480d006003e8005800c2d50051815500300000d00c1b552034002c1c010b10b0040741e40d04014500300450f0300700160b82c00455140815003500541d0302d03001c2c69407984844213000b0216a541044001114124003048400c00c2d80c140c40c1500401c1007400101c0e00c542445a0401e004082c0010010700340b03000503a0400e5260b10481c1c7d80281440c541e10340b80792481e0301900400301c2c500c2c40d0b000c0e0b1a040c03402c80c0d2240d0840c02410641079a4061000f1803041050a0b07603505c03540b02b0403c001500b0f00c141c0141403441101102a14844c1c203000260020240b401500c450000e1600e40200f0f50f1248202c5090170080800f078803825200c1d1382400800f048141102d00710050081c0c5032000c050a100017400700103d03058212085c51707800d2010801043e94480120b6911100901d02135140814514102a1000c940c07000640041c45680c14030001540c981c180c00b0350548218001c00c826001c1e05108001d0b2041100c5044158000780401e0011601820045512404800500c2c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 168896142 1250 168894892 168894937
    0x506030a1113050406080a0b061909020406051804060602061603140a060302010f0203040303020613150e0304080f06060f01030b0a080f1b030a020306010303031104080a11090f07090308 81
    0xc0c0c82d080182e041c0011510002c00b0480c50030700d849002c0240c21080081d1034429801e4035001280700001d04454069401904a080c08603061007035440904442c220941d80c032603482000a11540080034100003800769284040802d01d482d00c100300444055030058009035840074041002c1103410b96902c1d050585a044490a200c507819075148180142800012030608600004003170303452090707014041d91b108100a002180d0001002680080c0075802c032a030b201aa032400c4292640c030300c1d900344503140c184100640c10703c0011010f482a1040002220f545110401c1e44903030f501401d0341d03071360f030460600f29110307485500c00d402c100d600030300190481c083e183e914940380f0700d012043d40011480e40c00407014000300e4046c10400400021b021002040f21500355000652190b03810312009052581c0c8020302a0300b104158140d42c01094000113842d513005003402c19035030b54030b4010f29940c820303031209000880e100003880c0e100c3e00800580e541c007a0340c0d0f0b0a5a0321f07001076522018984035610300d1242c0d00e6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 168897392 1250 168896142 168896171
    0x60408030924090d260402040b041a030c0307140609060f13050118030510050a0b040c080108060c0a02061302031218040e010509192102061b040605040506030a 70
    0x11000c2403000c02006102e02d490b881803400e110a0504a100b000428080d4900d80598008030103684000400e014055407624400100181011012103401a082503405807002c0712f80e40c0700101501c810b80998100f0705181080548800c1d4500072520052641a030307002e801c3c02e080c03010f426007540107048070703186c5000070411100a41041d02c4200142c55000406d00040d60301c0a4540d00601001c0d031075441d4581503980c1c0c590bd07006004e4441da031099036100094844d5826802200134100090801c02c03e008080c00002d1458009006a284c20720a00d400320700b40c1c251035030460f00b0054a9034058411521840004103100701c222805070f91500c00c00e000300001144400080003d40204106817003e00722000a00040d60140125405241d241c9400c000604002041003014030400e40319028031390409140c0340c1c00405421245000c00c1d04102d08081417a1f0700003e6041c0170310580c121600c51030360500740800c034038403e6001d02400280b040c08100524105100556040002800d01040910903607101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 168898642 1250 168897392 168897433
    0x301290628110d080a02131502070302090603060f0112060603170a0f0207081905100608060609130203070303083411030301032d060218010305010608090604080309 72
    0x1c2641d11592401c104407640c01a407900035100020002d40101c140107003002e0048140241005209030300003502200c1c96100559140c007618451242c90607507203003410001c5d41d80e04140000c070b005d05a0f02011490510b400107030355115803031031030700c0400fa41c3c2044032a200324044131004680180c0c43e48004000107140341e401a8480305440c01c3d2030b840d01c42c4100014215000b41c0c000c04295008800e0901070594017054005003210120020001500b1a103485460070200b81010441c851820f00b010580f180c0c00308100d8019001200e416405880d0003140d520301d4110407500035031581c080c1c0c1b02080085d0150718050790284c65071226105040c5408003001480500302e4000e0342000003001202101500885c00b51001e4428200a504540c1140c1d80e1a0a8500b48880d00d42d1808280d81c0c1f41d520000090800c650203680700c4400d42d00c449084181e01e500518594030180464200f60010890301c0c485d10080e4441d40f0f024000b8401511152200910740e44080c002c9000c078081e1000850000741c00743d82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 168899892 1250 168898642 168898687
    0x110c1e0a06060305280b0c030c04050d06060914010b041e031a07031b0c06020c0106051305040210030207050318040e07080303040501060602010501030510050a060e0a021803012906 79
    0xd401940c0c20a000a59629500803081e043c040a540202c40820602c0c1145640707e1080401d241c0c0c1d80c4c4440c01140c0150055a001d20750002d1302401798801c000c11074000008650b4003110500511055080e11210500300f4020b01040007814403040201656081421780714071010b40b0a00c040b1510380e29941d81c074170b1071542c011140e01c3c0144144500302d607042c130640304c0c00a00801010918054004010300507030b1401009000e05030003045203a0000300a50000e001410001c04030b00e0740c5404c0e0a640805020708a40c240c3c8540b107000390182c1c5260003402151440f03540b10000d10301d403a1a425402291181481c05a40c2240c1d0b2182c0d02204140c1c10082c0602a140e800010b549919151420509541c01178021b00d085905100041000640000e0203000012509801280b180d842c11081002480142c0c4150610b0f094442480f0b083c484560081c1640010a081489070b0b000d01400d0600703940c130384484641810400154a106010305203500410303942c000300011310307282c84170a014000081080c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 168901142 1250 168899892 168899903
    0x120604060b040e16020607020c300a030e040b0105040905091c02100e0705091b0f03101503050c0f0711061810110304090b03010e070b0d110c1e0a060603 67
    0x1400d000c003241d400c80c1403082d40c4c0510f200410032440d0503000207450381d90050000d030040307181150040015400381040d00140300041c0f9030300e00508001d9441550742241e1742c4e05131f010402c4080380c1801030416000314106400d0684440b03240502d007104034402070400405004642c007858031443d00e4034280e54040780c44080c0603402008081000349803d400c5850200d40164241d1040104100c1506c400c0c21465200f00c1c0303000d4031814001d101c10600c0c807500c80c1e198601d2101301c002080044c12032410b8981420345911070411603090400701c10640c02c80f0700550700c10503840c0702480301c100041c804074000c103400c521499518000041c40030110b080c5800c0019440003140d15801c0c0c0d0050303400c11002d0405020307076910306283c9902c16908440e0f145e1082e80180c0c0c18807074803a0000c010903102504200080e070814012154195900e00401107282c0100c4100c40c10781e401c14054000c181800b200355051500441e01a0a11031030001c003424001800d66000440340c000d20030018003041540c450f8500660286 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 168902392 1250 168901142 168901169
    0x4020409060e03130b21040503040e09070312021504060b010203070b0a0b0f1f0804141c0201180c0909020103150902070b07080f060d0219080c040e030708120604060b04 74
    0x1500120800d4042d00017035001070040c0510482c0050310b05042c11401c10401210800da115400c0c81ca05510454120106103183c001c00c1c000c4e01000001d40502710380c041c909940800080d100e00f240c507040705c2941c03010380c00d1805000c80d0111b4501c0d4000b170b5040c0014012245004140c0d600c00101400c01c49100c000c081c1c2d02c0d248034090f42400c105a0403138080031100210300240d42d541c06245491004542c0d0304008002000a007000040001120021a510b046036404229006681490600c403c02c900055080c099040300f910061314620f0701c41e960000c2d15503225401e00084100034800f4030410703810551201c0200b400759006804440c0680042c80c40565520602e0038050700022024106c4c104109a03030003000740348240c0589460f08a80c0c11282c4070086e041600002d0401c80014141c2c0706030400064000442c52800039a0440154041c0c0d010b1025444031440241c60340181b281c05440752904014055054400c218a02e0b40500c00030400983c8a0310380e8078003040d0ba009074116004644c1103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 168903642 1250 168902392 168902407
    0x9061403070906060c0803060f040e0d09080d0c020d080d18050d0e0f04020315090c04030b0f0103050604080a0504090f0207020123040b07150c03150603020301030c0e04020409060e03 80
    0x14000364000c1c0050b404180302c0c051400d00010800e030074010000d8040000400807801c0355a40300e00300104040010014001130030701034000f030340f104490040381c00895589203000820f0790b00800c03c10064141ca1b11101d02c0c000a64003880343c020a040c104441d00b00040007914400e8a41e40f080f00c0303107995000651045070303050b854a030b0701d0051511102414040900740c0d04020b541c2d15481900c42c207005540161300ca4488950364841c040f064503206a00c02c0090080103440717418a0041c2003200e003c0c0307602c2c03401c44d254055080c2800c2d4080c04046c105030004000240820041c000602d440304051400300d1400b562941e061044402da1060940c1464000410600f1356a02c03440d1254442950307482d843c00c51680508940c0c0ca441240305029007214045240c0c018400b044a0030410303640740ba00240300d05000302d08000c2c01480c8441c1e400e5000034082c800032407964031920a40c0e0580781d02ca40c90700760700f47c02c03c90540360b8480000c0c8120380c01781d100e0043d140001c0c0380e8002e0185445803940112b80b03c05a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 168904892 1250 168903642 168903649
    0xb01080c12120f0d0b0a0603020d140f0a02030702210a0e09060a0303030b0310180606060512010e0c04090c0e010905010c020604050f152803060311010f020304090614 73
    0xa440c0d40380e44039841141c0240e5015405011034070706000c003020b1190b0343c500018042000c5c0ca81240541d5000c01403071400102950141c000702059074984108004100741000c00884404090b0359440c20302e03003440001820516554000c0d90420b0450040380c0b0303003140c94030210641d4514896000d0b84e5110102e1001c0c00c6603000100b00070442c004940c240501e2070450b001c00d01003007042c400603080603121450320b01320383c5050082c0e01c80000c101d081071041c14001001143c684180c0c003412140180b50002c0000c00a210300256170403035500d2146c40d08580d1a22444000351200a071403650a15010000043c50060600ca0703042c1c002e1064a408041341002c03c005408101302d9400395040c4180503400c40c0050f5616021141907500c01c582d118040300307200c804681c0780b045404880070244000104200780710007015a0710410f20502038862035108109034120151151f0388030060114180701544003107507000304894100e4a06520449041c141c2d500c2803407003030342c80d00c2e80075148aa40c43c9007500b26030b04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 168906142 1250 168904892 168904909
    0x41a1c0501060501030e0d080703110c25030b0c07031704060e010b01051c1808040f03050c18220204050a061404020f16212610050f0303070b01080c 65
    0x20007400c1c108011b082da0000e20f5181c00c9041c1050003002680d5000440803806a4080d14881c84a040751a4441d00c5602140f55209030499030300000300c204e804508030540c0707445e081c0c0003903991102d503040740c0342c582010515858106140403814040e0f41c003140c81c0318141c40c100c07041c4194000c10000c10b618003800d603d1821a14411840d034104182081a004500c003c000c2d9081140c1200d880041c20306669030700352002480014005003142000100016803514144101041d030740200151440c245c02c0d03d0403c042c00c1c0c5040e0012031000540000148030b4030368440c1026040001c540700288000359030340014110741b000c480c0400ca484d620325040c080c0c6483c0c6075040c20f41c0c4205640441c500428072000c1030b45802481003814162160000700000c014a0304c4a00007811400321044c400c850440c0c5000e400105010921a00c0d0043e81c0030102030780b2030741001d15000e10004460800194104020b0000c0c4c840411a415003502c0100446400a58803030f0700300e4000c08154002d414600c022108210b90304 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 168907392 1250 168906142 168906149
    0x3170408030f0a110a0e0307080304060f090b0a020c060304020418080d061a03040b0408040801140a0b0315190b2d060316080406060b0c0c0a0506040311041a1c050106 73
    0x7031402c0900d00030344d01d50743c088860240060401018403990400061310301000c0e03802081541c000072a000031004d81200700c2c607620924a456040340ba64030f48222854600074444008010781c04141907040a0800000950f0060700140012030303250340e100e01c1c80148000c114402c80307041400094044501d2520322890300500513800c20509040b8070b143d042c220501000e4806820b00e001d100120301040b814108840046c981c00c0300a015803c0e50408080d6a04001c4640c4490f490801d501071040b440e0201c0c1c1a00c1840000cac2d0a100c1540300c8003500800c01c9000440074443c0c655403006000c0d0307940c0300c50000848400c80040001c00711005075003410010100190a03008480134014803800302d0181c07401d400700c0c44080c90040c0c56036440d4149540a091694001c6003101c00c0024580345c44400468101840c540590300c81e6500343c1d0f01e10900180d842288006030800c00391480e510640d00d015000a4014241001d00b8008000d640002034121424210300400c1122000d50fa20104102030090b180107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 168908642 1250 168907392 168907411
    0x1a031513120306151d100806041a1f14030708040b060102120d050105030705060310210605130b0f01140405060402090619080a06050109030201030b0102010603060c09030201080f0105061603170408030f 88
    0x1b9034000700c0c80541040c40c040c10b0b8510030b584400f1041030005048044514101005100441402c00c04141c0d4894058020b0440c001814195183c1c0070071500300100c0e0700480c080e5503580e82c180d071a9107a20341c2104c0060702d0039046000d0401c4240349419080b010304005c840401c2e0001c4e080d4506010540b6207030181e407005000741c106108002200f90414404401c0300d401c42c01411040c0e00f803406507000c000390b080005105505c2c003070034000030090030320182000c240301d134500000c0da45503811508102d0000744a00740d1840700f14503803080d10b03050a41003903811003005803000d401d010a43c00004ca558101c81c0c02181e40c0e1141c2140c8403403d541c801c1c8001d4020071910402c00000e0306083c00200014090b0101030305054a607842c05034141d20035848040115000700c000c01905240c0da40c0107011501da44420ba00203040300700410030840865004504031800240280d150005414141482c480301c0d180c03d400b030081c5915a11a540c04d51480948640d120f03441950f41d0f41741080315021035a0700034114414 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 168909892 1250 168908642 168908659
    0x108010f06050916110c061201060f0c02060307030903090302060a11100908090103231501020d031b0e120304080601030c080f070e09010f1a031513120306151d 70
    0x4400e0132200005000215032504031480030200c5d640500d0320000521494002c0c3e0000340c40b9000c0e205610403d4180c0d9190741c0c030001810101c1e0703011a2401003501010358060700420110750000c0c040c7e031000f65920300c20b09112031a59500e80004a42d60481d28604000c540304144420403204248440301c01c040c0b102c4001c0200c40c60031744407800607010380c401241c141760380d403e0125140406ca20800150036503001c445e8145190000e802071507003040403000c6d8050f11811007248e850034024081e00302c40c4200c00c3c021030144660f101040381c40e0a40050342c60b8002c1780c0380c290302c1c0d45c500003440248060131a12009080d43c3d4903510b0400c0d261605540102c20350340003c07004d00702c000700224a07a0b003181d400c801c240c047c075103440100318010f20850006005803072a00e00c1441350018400850712040c6c0f0110186c5d00c21181c001880c4403031034000c4500380110350820000e031001402041c8184c1d04a0403502d00003070410344075079155079040e80d040700c09000b0400c5040d008a003450203074034080f8070840c1641d0840303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 168911142 1250 168909892 168909901
    0x2010f050c070c080a030504060305060a210606060c050a06020904020c0f0606030d050403081b0c1008040c091103010b07030e0a120210050922020919081002040b16020d0b0108010f060509 82
    0x2400e034000c5001c1c009c101500c1700046103469507020400805002c0c10001e61030701c41d90b031905036901c0c01010301040302e116043c450700184144c0294506040c00d03404c02c0203000c0030781b800d55411700250f000d014500d0f807241d42401590001513040003a481c1d03807400e1034010400781c104001054907005c031040304002009030410013480000e00344030588404294100708400100a182d0402c0d003010750031805103400060000c0420b510300d90084100c0d020301d0240c1c9040f02044c2e101c0301c1039000e0360f000075040c44d0134140810041000003400030041a01501a1911103d00b482901c00104141e1159010a00e400716628034807080d07203804002400022461f04000c1e1400d010a0080782c8680c01d050860a040d01b07030002d070342000202540449821410090644028458840c8110088800750050b001e60340f281c0800301c062040c0720f00c03c0310190388000103d24180004c55480800544c5d0b00c003005ca811000740c40066002409520856010b001c85e840041110b85071140d01a00311407051380814480c03080c1c2070502 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 168912392 1250 168911142 168911147
    0xf0f07030e0f0a05010c15050a0c08010f06020607050a031503030e13140c07020a0b040b031006020106080a08030915010b19020726031303030201020405011d0f040b0102010f050c070c080a03 83
    0x4030413181c080c2002c2c0440303d42401d00e080d01043c00780d10900c3e034604240801c03d000e404e550181c429511291070b0000d19903251002a03440200d1809450056844a00800c0307035a0302880103049050051300d00480c100700c3d88001e056410509500c02c9000c00c81ca1519019249001c9010f4440c5c103146010070040300414480f8061800c00c080c003061224400002d81406645680211340c014102e10300a1945d50350b941c02c404e1480703074000c580d60144021b0010020a4191043c003401c030444440c100149407030400b5480390041c50740084d0201c03e0038423450607410b045158140025000709080342c0626222218007003000714060000e9112421500480d000307001d655000101000d0141e80a0701d280492510383e19810b1540c4210711182d4a4503407030034400020198150010800d5410a07030b03400040c080400b1003506a115111f1060764031120102d840100b50416501a13060854144008207415900e01c41600c100c1e1820383d8004001480020f00b0000e10108800310b9008150b000c004080c0c0d0035264800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 168913642 1250 168912392 168912409
    0xa09020309210d060e04110f010e120a140607050a030c030204031208100807060207030b04050a1b2603070215043305040b0a0c030323040611030c09010302030a020f0f07030e0f 77
    0x12170344a11404959040d50f640b1a480d54201002b02500d404c3c2d0f40201c0e159403c0c0c1c5d65101d84001c4484010840c01c1c2440141d010070800c0c00382900762241810042d01d44000e40c00340c4149049402095800e01c40000443d001c0740c80307030344d8840302a201c1e40310070300b0000c0302074966102da6005038500303510a1408000321580020303042c0807250085440822512140340c06804c00a400f803001e03224242d0344124081c0c1c00e110300288021501030a561421911341c42084103050703840c44040d01c600b60010310046015081c014210191200e0b008002880e058907010702d0f44e00103c2010320120082c0d5504000303504445e4041c4207508900003030071f1543c01d00b0300c0c04001d14242c3c0b14030400d4004108945c092a01018000e03040318000700108140b00607009074110741d446e202c000803a400c0e201e140c1800c0038810055424000c803801a151311070303003c1c50444264015030196002411445400d0b0382006180400c070361804c081c144041c4059401d560318405428003e00b203500d1152054443c1e414200103104654440701d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 168914892 1250 168913642 168913673
    0x2250501080c0705010204030503120603011406010809010603053f0a0c0609020a0303050306030607090f0620011d0609060c040510110610170a020a09020309210d060e04 74
    0x7004402560b404820007554011414020240d6001007008001c102e030100180c01079483c403010101007a07a44030101801d1701c017410f0b1000100e049200100c0c0b11544101d503440c0d8080100800401c000e5641d0707a50741e2910941e014040707103107101c0d12a2200b0507040300e140f203a00b0b45034401c00c3c40327101c00842d440030034144140d9050703509000c4200c407030700b003085240d420148800d90000c021080107a034a040c05041d0394821103805102c0c2c082d180014810783d0061405205444440030681c0741d05041c20420744480f00c0490001e04e01d1550b10540c0c1d1503074031007406044400914503100c0c484c0c03c000d441501d843d00d040904041c0854001c501084210101d10050301d0440c2c100711048803114644101c01d45041f50349412100b95401540100f04080d440d40001344104c51b100301440412500015213252142c000c0c58000f944600092010040c21041d81c0245030440401400d0704d01040c81d0300300e00c80c441040345940400c020408540441501c40500c81c09004114200d00541755240030754600301c41c33002051 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 168916142 1250 168914892 168914897
    0x5070510020703020f0d05030103060501090c020a170d09081207110a0305070212190b010801060b122d01031505012904050a0308190c020a0e04080d0204031202250501 73
    0x2c0c40405040c401c102151000311610290f0b81d10369651400140f896000340000d0b01e0040c2040000101c2c038200b4404d021054035158040c3c450000140d40c0e12900d001d050350f01c140c00c1d120a00c159000b802540c400e411926200f50a0f0039902c40b14a1340544034148010032610500c0501c9254804d2081c0c0458004072130f5070301d4034080d944c0d00c10601c009a001b0ba15500d0940d540c2c441e40700c084860080c19116200414003444c0310110030380e610714409017664010b0148a00100e0705000c505452000c0c0c04040b40c0110501c0000c41540100300010f00051307481041c03d45041401e034004009000da90290f602040d5030f0390000b44595030501c00002241c61141c494028042c50310012030356980d101d84140d9000e0000240a0301c01344d66a8284a03649400204128820b644180a1000b43c94002c1c00800c074603d50150030384c640180b5200d0f001d02d195900600681c1d80070303400c01c0007002d504081d10042014500c140b07030180118004e01d50080c90001c00b4160140055100c0a02100180f40207803030404461092 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 168917392 1250 168916142 168916147
    0xc032007050307060204150905030118020d0206092206091506051803060711010f023901020a120506030c1e010903020406030302011e02090d03110c0d03020c030c010507051002 77
    0x41c41c1452851252000140240d440494003040d18000e400034001100560303682d10030f12540300c40c1018220790b2514068120840742207200c1d001818050b5a6030f03071903400149440d082003a0b03040800c0b084041c3c68400700c11704030280340105000d80d00e44214005400303d0704c010011501440c600306110300c80f50140e5801e202b004648008480850811740350300c4031002d0142d80190030200009800160103100b42820b035401e00c222030140110910984010304840d403c01b41804103000112001c0c40c0250b03c0c00450204e00305004241003009000030210300c8007070340e40c80c0c2e404032003005003c00b200c0002d00b480303100390010b10720715855035950454001d03202c80c14200704140080080040c1c40d01241540002e4000381064400010f158040d0312070210010429000e6000020301e0107101d04034410400d03115445080c038001c000c04030340320f200302031401081c20044600740e00800c000150b68100e02401280142d00c4049041c030141001c1c0b01a034035901080c24010300700ad1701980d603035454041c005a000d6003207034003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 168918642 1250 168917392 168917407
    0xc15070f11090a1406062a0d02070603110415020a12080f072309030a0c09090c0b0703051602061210051002030c0307120c0b011d070504050d02040504020609040606120c0320 76
    0x411550b800700d0000c1e010455079501d2010302958807060b400780c5007005802484ae000880c50f000b405548500c02400c10000d01d03080c10510080c54180c07044c0540320440c400d0604090000310300411003000d0740c0450311106102c0c94024400501c4120082c0f007441008403110040c041030300e5a195201810400b100c0c116114400d042c0801c0c60102d20040280401659880c00110550341d13034001c0b11094010a07140305030301d031200c250f4021849600c5008000440820560b404203645d018010480c41c030080007e45800002da00220321400c0a41c0c503d42c920318218002c12443ca012442e0354a60001c0380095800c00f549603100580740d00904030040c20760000c001f840700d040b501c0b45410820341c079800089000b4650310b41040b203d55442e040350000f1460085004a415a4016415501100d500801300da040b101280d00340b202614028100b00d0b00b00310140030b102c00581c2c6501403030f0087d0245a681000054200c01d044082c0c403401001d11041c1864005444a070304900350203044030103040048182d80e42c03103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 168919892 1250 168918642 168918667
    0xa050304082112040f1b030b060405010806090604030807050f0403140f1f0b030f0303040b0708010f12080a020c060c0c040f142202031501030201021c020c15070f11090a140606 77
    0x40301e0f8507a00d885c5030f0800040200032320341104c240200c100703071000c0086a80312415155070b500107035078420740c980c040b40004000038441d403401c65000d00d0a15126003000300c880c0c0051030507005034008440841080300045c140710303000c012420444090a00521408c0114000c8088482c00c80240310003031910340b0207039000c40d1010810300c0c00300c10600007166900e10703050a04c60700000f01910700c04001070035840000b0310116421070150549442c0001a00303542c21a40e076044451b4070441d0540700354011000c110740c0c15a151005040d40700e150002a14140020000300401c841d1361003110380845103015038191492a041100a92080620030b008460001001d544030302001c0346c6000070351600c2a0f003800c034080058548018101da00c00e808407181d041c064400c0a00b401465103a020050740980b120034000d203400121040c100102c40103c0b85001300b030351500306510a00c00e10980703100340311950010345814203c00c3c455005880320410802c2602c55840300205450150081c0d1181a000c10005080319 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 168921142 1250 168919892 168919913
    0xe010507211404080301030507080102040311010f0c020a0f140105030108030d050405070b07050304030c06020303072a060204081b0307060807030506010e031c2606120a050304082112040f 82
    0x10700c2c01c0200075145024544024254024001128680180d03000029040300c1402664143c95025048549030029040110707502d8a400c402c080030041151480030160b290202c01c0000b4196034406142c0c07007400c096070400c10014202400d410001d08100400800501005885c9501c030300b01c50114107601e80741041d034035002c16038000e2203d07198001010400c1000020050044a200c0c148990703810ba0340f000c0603600c038001100c41c0400b09030f101c0c080003600901c000e40b80400404031214564940c2440c0c071001d040341c000350089865688409140200050613400e0b080401c00120300900c8082d00f06030004045020280040301455118808181e40c2d81c040c1c0c503108100f8501404032442c18009403803403001c00307106490300008500c000c8100c00b10b10202e00c1946c00c1e0b02c1c0750b0190311038554450800b1300401e0202d015074200b21740944c800e9000002c0c01400100028101c01c001007410301203642d03d184030b40c4d010a844a059284c200103c44c0d82460000601e9400f54114983c4e030208c031402c0c200080b004 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 168922392 1250 168921142 168921161
    0x40204090c1505040812070f060e0102040b0a0306080c060a0c03080a021e0702010e0a050303070f06090812010e1e0a0b03010605090a1d0105060607080c1005040f060e01050721 77
    0x32840082d0101c040da0b4400043c3c812506000112502c51282c000134840303d10078090b014020081041225021901503000040444503110005203020703901c039a892820703000408100c1c0080d465440030003410b1002c10a2092100c01240e0a600d80703807227444e002c1c0001c1a18034000b403d0100200000702c81d80440d906441071300c4070540003070103410000000d00a06601ca02c0080780480d11320700e00c1003034078240706540c1016500080e005500e040c0290b2030301d4422003420141181c17069110321198001440d104040c0c89100021103904507154100308481000b000005d111810248018040050444c50011120b0b004062484000780d0340440d14046405007200750861a0000a0030b4144a000701461b0300510f44841352895401a01c504038850707500360341d01510a81c0c3d0242080c051a000301e0f060b00004c1248021040441380000003a46d800c00540c2d40c01c030350a6420b18030304100700040c40754a000e10140701c3e0240e030081159250070340018140555482414140c800702d61403400000229500c6020300c0d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 168923642 1250 168922392 168922409
    0xd0219030203060412030e210f090d060509100504030519020f1203060a080f0309011404080109060504030314040c210c0f030507051008241c020109050117040204090c 73
    0x3444d180c1860240340005510a00c000392800a58807e082c070007059101003c0c0401d0444c3c4041440018220959082899000480760041003005c0307003a42e40d113091210952182502050500c3e05003191804c0428859144010a00741030401000030781c40320482c0e0001c0e0500750285021450800200d280110511a2560f140700d44c034541520b02c50610007440c81740e0300c203c45698100d52214607103900c036111f00f94080010b901c2401441c020b580203007000040c150076a998107050650b500601800e4070f1241c44142c8000360707114140005d156040c00307220028600100c0c048024109981c40000410b042d118441590519600d09403410030031105003616181c206a074103071034985400c281c43c21800c00d4802103c0c248101407000030903007404803a1b019602c0c0141c44880c402d030f0310806070a44004100380b02c81d07040c1c883c00c00741e001c803a55040c01e441d2600c030622011104000320351001401d0340d8083e800190600c2409450014404101c0503120343c8503505a0340461480450305d06480c8000003a00710a14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 168924892 1250 168923642 168923653
    0x4051014152709010f15030825020303040b03011a0403080306010f03021603081906060206070c020a05090c030f0a02040807060c050f120324010801090e0a05100204080606040203060d0219030203 85
    0x340306015003100503a4120705c4000c220311001a42041075910703051000030514102400000e6100100c00003078400b10400c00d0107188070000c0d42d40003d055602c103801c0383c00c1d81d82000c40140076002119184515808200a541c1e00d0306088d903c0708a42400020011070400103000c0100507228401e40540b1010018600f6130000d86030745d4680035012040c12200500ba802060702c0168a0440b203018a42c115034094000d80019110a00c088804c0c0440c1603090742c001d152039134000b80d0b60f201c001082c2c0c0f288400d110081d4803410301e85968000d081c400f512002c0640d0050205020503400422400101c8a05040425105116107003c41c01c180344500d248505005601003c860507080341d00451090207001d03c4102c801e4144d10070b80d02000c03140c40d00c40b40094000c200610010000d580400404488401190720450341d941c0e640f071600b4030f240204160b098000c0b030100681b54003008031581018044074103500710b207001404a03403428680705000e40702d0104910880c4640007004041c002440e00034090341c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 168926142 1250 168924892 168924901
    0x607170f07020102060a0c05030112050f100c08090703080f13030b010e04031407050706121e020903100504120e06040b03090a02131803050c0c09040510141527 70
    0x8a607007040105a015010b400000707103908006208108601082d070b00d03500e040da42407202d041c0310506220000c9969125100d01c840c468141000385210f1098407201c007240c0c24255420051010301c0245c1075040aa000f14014070002d4008810b4403012400c002000e600c8411481a0603001040c0354009040b050b9045c0c00480c81d091031141c5944161b010703445410703800c00161304001c03480c49001c8014199411412003884028810340070441410039403040401c031120360124003640c91020111000d122036002905129a040030f10100c4000400781008204500d0240c40f00b080100c94010000c08100740f141c1607203819640c0f00b041e50064001e42c42c0f4036440340b5002c0441c6a50381800780050b071042c07c1900f40801996900e0098109101d0481c181000d803248035074090703500e5000220213240300d01540f42c5c003611035110a084141300314091001400100c0381c46440d48101c1d40c60045650740d001800c010020f60100e41130802001c1d400545442100c0f403014241e0703a40c82c0040124503c00c003d181401d02 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 168927392 1250 168926142 168926167
    0xa09062f06040614040804091a0907030614040e190f08070302012315040c030f110403020a0803040506040b070501060e130b240405130b16080108061302060717 70
    0x544103a118000410013410008008409540119401040c800040100707004917020f07030f0001e40fa100540c1091000c0c2c005040e00241e1042800c55032031300084e0352903d0401c01007102d2402079807030000903a030420040c04164502c6803a2207030520129441181501c5030b4007000500d070410147d458110401d00d441f100030740f0b002400303003001c0c4450f418080f01480d40400c12024018000e030042c5885440c0f02150340c042428000509061000300040c035565846010143d015405980c0c0d480c80614410703980c40b8114410007040c68a5500703e000c0541c81800140120703260102183c0a448a818002d6154069841c0c0b860152820707810038503440a0000902128891591062144074820380d141c02c13540e900c5100d00b107801c000c1030b82d14800d03240d52920034155034101580045d030090500c0b040381e105121144ca501d00c541105030f031b02c0c10380c2c003d1101c24900c0440d8041040707405452094054030140c1030605582099142880c000303403003100001154800c001001c0c0030341d000c0034080c8503240d44070781058024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 168928642 1250 168927392 168927403
    0x30c0301022206050a1b06090507060c0203100c0e090a110a050c010c03050411150d02041707080a0302030702040e0c0a1412031213170d0603110102030a09062f 70
    0x585020300b58800204409005405a50000c501c580c2c2c2c040c0781d41040c1c9074010981d090100103540381c1d6034404075100401c1080c04200080c090a40b10b494a0107901d1040c545003070b0b8507184034202d07545000076040c00c1c140e2010040310305041c00c40300201c43c0e885032110080101040401c00b1101c040c00103542440075000809010300c00e140f580204800280441c2c203800783c81d4116002007602c0c0840152642502d8114915201410381104031800c003078510501c0c20890788141c200001c00150745200303107070480041260a0240c1b08020280418641ca55800795a074015804028440d58076080c5000401d0810003c24491020040c404500c8940d15010b04000b158184540e5001310003605d000c030314545002040312604a1550480312071941c4000d81c019102d00c0420044458688001c0000c01901814000d06408d900388100056214030f5403400070003540019011605541003408070001041d0494030300c408807001800c0092006a404034041800642060910003501c03101084103912100000c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 168929892 1250 168928642 168928687
    0x203150a09020307080615090d060603171c050411100e190608040f020a030f03090e0a0c1d0a0815090d02010e1c0201140a1406060a020304050f030c030102 68
    0x420440d159103909500081c0d00c411500680851100c50114985003450395900f440c0d040000c0c1114101812040000d04d103281d44501661007a40f0303690203106000613044c440300c480ca4400700f42403416200e00c6407840c01846004000f041c00c1c0d41c032000a000d12100040e29004114020070220001901a0015000d4080c601c5211302402c3c6606c0703011541910002d5040994a0030303101c40f4002d560700c0e526180d160710401c10032600210350355000000200d0f4901c039050920700ca0b4585e419001d00340b91160b58469401480080c0b041d00700518007610680000c404a0007c071081004010880c0c69004205090750f0b590100e2210b1068000f15025400110b580318002c06008054032071300c5101210072801d03101014500001074000f0080c40e035a498152a040c00011024000030421460a881005c80d840c400c84819907807a884240c9296a40070032a0102c0e07028500311411410000041030007540d07400343d03008035802492202c8030212179540810815041900c02802555103841d40904030007142c61804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 168931142 1250 168929892 168929899
    0x7020109092a02030a09031118090a060c020a080f0c0109080409020c061803030f0405010608100b01230d020f091009050102070807030201050d0203180a03030b010f11060a050601050c01020315 84
    0x8451050700c501c0401242c0c1182030603500e4020ba5810340e1101e5002921231442d160384007012010b8610310310f13030010382688980c01c288003920041c1e0311070400f0300581c0d08031850142103400c9000301d000003c003114281c0b00c00c040b541d1030302612080c1d4541102e0061034440710160400130041000a940c18050700203161000050060b1034103500c40401d22110440580000d10558009000013107550710000d2805034400d0240001194541c0d461603024200406030083c0d000d0680c8407003484c480703940c02c44440240844c1581542c000e60460f01c10035202405100b01000b0b1864000410041d8a20444207940c003e1400400a600d0700d100010058a4104180b00e070034094042c0701000580e413503021903a00d01b01c0e0303010784030180740019000b90798000b9400103100b10100404a014a40030400400000c01028172940340000e0119414001520030b80d07801d6000c00411146035107490100c0400301c0c0b1103811945d08100070500303480d09030050711540164048204558800f00400540f10030313085040e0400c85094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 168932392 1250 168931142 168931211
    0x90209130204080a08070f0609080d050c090a031b1a070b010b07030c06020706061706100b040614070501020f19030c030e211b1b040615050702010909 66
    0x100c118040c0c0c0101d00ca80c0c1c045800584114001c5120b80000700b040c0d5210b20965a03a081c00c1c1d82e500390407220035040030742d22030402040b0103035420b003640304498105007a010700c28281601c100005402c0794450100404c602c602c840c0c600030f008241070f4a030018202442d060403014034410101c90413a00100d00988280302020000a4003081e0101201c81e400e40559a00140d01c1d00c9840d050301075842410100c1c0c0c61940c9450000f07203103240c08003280d00c030007c500207403074142003843e41c100740e1a40355041002680000c100410545402c81004000c401d400100a03854040c1420300300c0c020b000304944065004000074a000c2d1b00c0310700303480c4501000b401d92000c000034100c8482c11000c80e0401844d038176060303200500000100d14144110546807402d03280d282e1510700ea40c042d550079801202040700740b0360702411b00741c5464884408441215030003590100081d030300c3c00019500229001c0343c080280240042c044040d03901c52100b11010300b555540c18020180309861440300004500b0941c000700082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 168933642 1250 168932392 168932419
    0x2011d01050411010e0d060b0d171308240a180f0606080106030c12021f02030909060303161401180309030605060f13180f03031409070605030a0c05070b01090209 71
    0x17506001c0000392003d170404090403010356518006050301100294010b810315038810000b000e04222201c069200e604080c0c44814183c0f04544002d45500080c034540c205a00c110400001102c000080c242d08101500c00b41d11001a90b100a1003005007030303210311882e5400d42060003400c10801101a120f0307441040780507680c00026080f5003040c00000d1280b42050b404101c4d0103000d20300701c01030b075000130b06a1415800c04d14011002e80350a40c40840540c002160382e26144ca09185801d5201c04d00303030082d5103402c0000071041503903480707044020800000c440d00429203410035401302c1e90360002005914820704440c180548100c0b03641c80121007007130400c00020ba660825401c0e481c0340701805401e1025035001403170550301900d200ba418441c0072401140c1603010844241c1e9500e21580071b5200011701c44803000901844846c02000852070b80e00c440c40400140360300400300c07980400c489200007200c0032201c808584030f210344070003d04071000e1000007141c44d03030466005003021281142c407070442c3c040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 168934892 1250 168933642 168933647
    0x6021e130e13030c0204020c010609061502030414090403020717160909020a05010509061213030f080903030a1112090c0307050f010e0f0d0804030305090103050604090f030c0302011d0105041101 85
    0x110b92030040c0282440d10315002a015800c2d609078588000c2c00541400181c0422908450311030b840f20740407607120401041861071203164160300b620144051480d0504009607440c001004411f40d034068880c0000050501d0320901c2224040d04813900d405070022042d0707107056a29440a60225004021506e0008a616540c800c400000d0b88c09407102503058a80030054580fa00089030711f40e08500c0401006c4c09000c9c03d041c40912030b00802d40d09120700c68a900380149049d16220000b424401080c05004400c02d001055a500510722000815000304110018100380039171300d0404040102d01d001d2011a540c0407074a040744171810340444420565880400521411501c45e00e0301050700b0b05500300d070742e04115081d210781513005860700c9400001660790103696801a032058001400102c2c01c40210b6a0502130346800000403503081c4007220081e190f11000c6c1d0301e2040004c040c000303160b090408141c000c0d04081c014800c0c000c2d841e20300c01404565603028200483c0c1c104c4102010600040c0c0660 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 168936142 1250 168934892 168934919
    0x1e1204150c0e1005040902040f080111030f0408070213231f0303181d070306060e130911060a0306060e04050c0307051b07150e0d03081306021e13 64
    0x210700d6a551912401e00006100e00301021480a00800ca41040f01155070301242c001480204002c07226820036500d880400da084032021503c0e290b00320010028440712490303884403c1d8000d0341022070655aa00f0328400607000c081c0b104560501c3c0c0741003648820794540d00140b825180c800803540c0601650303800d9146243d20403c02c9414000502c0ca000a00c08644500c0d50040d050200344000000d01340c03142c48806411009146000c02d840c08082042145070341030280c40014100c9041901091104000052035015400b000c000155652091100bc0c05140342904220700300140195a64030200300005003e000f0320b000d5400401e03550701d440101410203208551243c81c4004c455404c548400300c00325420f0703000710342582400000032101003155106100d401e0040000c140c0c4040041246a8082c121511703503890300e031081c0c01514121021a4016000a82c89403640507454071501e4180340c500c000340691a440034a001c01d981650350312100d040300401c00102c040c0d0704d21b01d500c0d948800c66918032 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 168937392 1250 168936142 168936161
    0xc020106081f0b090916080f070509070203070209090705040608060c0a14040f080c01030f020a0c0204110d0509010c020c0d030c0f020a15030b040e0d020606061e120415 74
    0x2640110404401c100340d40d07001c421506128a4041008070b2444000780c13080f1001d803079842e000c0c1c10101280780816000003505009180c500040d20703400d024041c0440c0c40e81818403885009a120710005802c070f520a004a81049500800c010407a00340511042e0340e600c458040e1500452800e1000301b080c200004850780305001c60440e03a40750002d109012150829a9480502224002c0c0030201d484214058410b010b054604000c03c24007458800060550b00e80517021840c0034810071004100550100d8a020740e1601514041400070a0503425141d51050010800d8614507050500458002c10341142002100b251300b11200131480c8000c00810110840005020490181c41080000c0400c140a40300e40c5c001088000c00c9907544405144d5403035003080004c00699280300f444024039103032044040d8145204001d010403c2e44a001070341da4039018081c10301c50b40b808101c009080c41003000380380d649100d10210685034544070341181c10305441580c0c2102d000792512035032110581c0c5031107030070000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 168938642 1250 168937392 168937409
    0xf050f1c0b01020703080f070302010b030609010207060606050304031d030c03070b04080c0117040b090a1e020108180712020d05070609031403031e0709050910080f030c0c06180301050c07060c020106 87
    0x31711f20041c501071001e03071115000700c2c01d55494008609440c0d070144813883c8038a595100241e40c1d00341c00c1c40c1030400c6400507004501800710910910000c00c0e80304c0d0044611082d042c188414129500c03000030314014403805a01e41c18400c4800c040f5030724402802510881e485002161914444000152595070720800346c0d0490420ba03800240100f1101d031843d070f82141c8144165018950540c6070700205a840a03503601e51121b80482c40c03011568042889a84400101070300320700f21003c80741241d21005144540300900030403684071400c0d5030711100d40420041e4000100d40a042d07031150042c01080b03652200351043c80c1c400000500c99078001c002c9178481d01d20620600039041d901c1e00240000d81014003100c082001201010460341c481229803405240d1f0419074141d6a490040c000e8070301040c1d41924605a0410300c01c02c0e032001c02c0001c48201c038140031107074031b500c81c1000440e80400240c00407250b5419800e01e0240020582884020403480340605802e20010513464401d80c04c3e1680ca22400f443d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 168939892 1250 168938642 168938647
    0x50115020312280c0f030b1e030c06120f0106090501020307080a1e091a0903060c1b0106150e0405060a14180f0901060e070f0f050f1c0b0102070308 65
    0x242000008421580145003003456100071514004100083e95400d15240e1040d60b2242d040394132030b03041140f80c81d80301a64541481900d124a0104420074030103d010708620080100c1001d80e66000c0c00403046072000a0b0405454101c440511030319440300b91402c1c088490031800115289118102c240103071201030300110300d0003095a5131400158884507280c01000041d18001c0d010901100203a50240341e15034071050a6806c2034400a4960140c00c0d04182e9400f04200c5501e007510003281032640201c4080c4a2505c40b1103a03015641d001402c0108101654078150000c01d07084a1484480524a115034070764078000d0540050008803582961241c1c2e03c800149003c015181e100ca00d500c10080c0050903010400f52070700328012803444280d45003101184481e00300a5498000d08c14603001b03040c0b81c82c04082e5410710000c0608101d40b001c80b020100700c0700c80d5551a03400d00603001c0301c2000e070494a8460380d8007040c0102c900c1495451144c2d40b029420711098180035840010400305498000e10000d2 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 168941142 1250 168939892 168939907
    0xa0c02060906150f030a03090e0721110c03040e041a0106080a050702030d0204030506011e05010804060504020d1a0702010c050406020d030e0a05010c09030615060c060f1d07090501150203 82
    0x8072003540040d10b15070003907030300b29544000c2d241407004281b5613200b80c40d05c900442c103000342c40200400042000040080808201c03101c40e001d15481d44443c44e201070002000025000c1c0000c0501c24003c8000c1c45110008000a445000107913641c400c60080d1080078281c0c060880d00800a9000c0c405c501c00100c6580100d80c601e000c562009030402010b004592400204c03885102c2680c016a00a8070a90440001000300003100e40040040300c044601034102c00d810500041c00790100500040c184990700c0d0000380840d22006400214142c008164020001c4040502513600e0001c4a9050055003443e54801e1704500a1b4181c070241e81d40c3e070f0050050101c100e00d04a0003020b100e0441d034084d00c6003103069000f041083c45584461003499480094032421030034400151200e08032003d42c151030003041041032643c001d030385039400c0b075010300301041d1400b10220250280c00c0030032003442d914482c08101b54161100241a000b04c44143e20305100c00da03a100d1480d00d0484a80c50b0b44800f6070010401c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 168942392 1250 168941142 168941161
    0x80105040e0c09010b0c060109020403020319060908030c0405011805031f0912051902070f0533090f0103050115051b0f0102040509010504052e0315050a0c02060906 72
    0x201c461204000300e500044951000604501c2d00782d011016841300003a401d40c51040900405015100700301c0c0a51405255a0100b6900c0c1c620340701401c0001c000d000da50040042c0f41e0410181c03203803c9445903440c0d08001100080710380c001e00c00e65011928507044103105200e04521a0110344000b00030302046d5418080012110f80b0320880c0d03000099403822006d0003e610001d2145820850760b0700d203900c0382208502000100003524102040d036002447c20081600c4914107107081d283c068503045112404a5000d01440d000141896000e00b4540c0500b210300c0340d00d002500b20b440c4110b40d40031200d40c002c401503040b61020302540100304213500001410b540540028041450300304c491185101c2040f00c013130704000ca0104642c1080e5000202000585004110240035040460f81080141400e1450341500c1030100001c0c0900c0010403d040c0c0011700d4400001c0042d50400c0080400030317240c0701000c00070141203d1041902c0c2c507060405880a100041451085c0e071424018a1180c0b1504c602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 168943642 1250 168942392 168942401
    0x2030a0303181a01031b0e1b07080a02010b01180b03040807050304050d03080906010e060d06150b1c0f050105010f08040c031a04060506011103090d020a0306090b07020c04020a08010504 81
    0x80c02c00011280640c00c2c0001d110403101103210204000c140000e506500d070003201176550000f0343c0030340703400480c051081c500c599103090341166028038141c901d0400000718001c940660f440c040c0200f10f001c80d440342000d40641014a0a00c0241c0c4d689442c4500005258031000d40380c050010903607410700008001612140082070418054030461382840c1e0b03140c000509900101c101240003508241c01d00500580070402603014281c440901216890308a02042d0020b50a8501504240e01c544503400100030745000d40014180031714540c0d0b80d03001c5a41d0813204800380400d6000499141004905d900c24103841468141c501c16503078002c40c0300e05490200d6000401070000d841d005030300030002000401e5070b24110040490321108550501c0e0a0070000112100140440d0602610b440030300303200740c004411902103440c211040b50822290b800801c0711070b502600f0040800e80f501c9182010b01a01c0c82141d44510026400c4030740050796401800140d0044080e80404510094014009441c19801 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 168944892 1250 168943642 168943661
    0x70603020d0605091e0a2a140d0e0c09070906050705030f0313050c18070f02010e0a0303060812070314091212220e0a0e0a150209090604050402030a0303 67
    0x20229205031540d0000c4d81492040d00d41803c01c000c400c050b400304080e24174043e940401400d2040010300740d41c1801a07290500803855003030342d20110740903080490040c03020210b800340c1c101c0e400d80c95103400c0743e1203002468003000804952007001084402c070b243c20001e41d403103040d403079035a1001c071031400401391896000384404550f580010300480103121b6052010314440d10079480300048100880c1025811718401c0c02501d401001040d20402805010003100e40c0c01038000d1400c403600b0110010100e00600051103446005e0040c550190181549501300b0026540a0400d8603c556518200850a846044401004646480b460f050006030660181c5220040617003424042d04515000a080112903042401c2e417180c003090400004000424192807401c50900202d50f2a041628400c159030004100c42d01e200d803112506040c510061003240d61071580410440b00c0c1e0011003081d200a9044003c2e440d0290301c004001034400e180030300900f0300454001e030203011146241d0700c044020300000078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 168946142 1250 168944892 168944917
    0x180102040b1818090703020a12020a260703110114120604020d0207020616060e01060b0304060207110303030c22121b12050307050d110d0c020d0b07020c040501080f07060302 76
    0x4521a115640f01d102148a4450380c005020464250320400c00b02c00700e1900407914880c0f01880d10703401a1511021141528001920070750046089060800d6001d0103405d502402d000b5810000204002c2c100501d01542c070076206c40408102900754000f1502600c5c0c641c2d5020402e03100810401e0605500521941101c1a000751a1030b640b45c0228000303610902d4040c0e0410ba01d0303021a0184090b9220350341c2841c02d500024003034145048000d5845000c094405002140d00080300c004203c401da62803801904040c098076124039022040d107515030403817802e403a9110800f151981082107007080180c20303a80351200c0c03031003a40301d540c5505103e882c042c0640900041002c40100d400c120300c14010703001620410096070340e00300030b140c541d04002d4000c4803a0244203040b0510000c4142c04506003c2c1007401e8982a100d10301c4500000c0d200035010540034010800380ca0501900c2a404501c88600c59000c1d182841640d076580c1c8655501c2151889090084d00b00c0c54044c42041d1294004040304000030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 168947392 1250 168946142 168946159
    0x103110a030b0708090c0303040f06030f0212010611010c0c0f03030c030e01110406020712021807050403061409061305031803010912050a18050f090601110a050105180102040b18 78
    0xb9960307041c40c00360030341c2c552003c2400181000f00c00d907001c01c0614814041600a581002e00d44680c0000c000c2090140c4400e240d00c4001c3c0c4000c5450640c19a0180a031005130100c0d01c1d6503854000d4104601e55403072082550a145011500c103014503c50b0308aa036001641d050304d0390040e2001c034000c05a0005880416844660540c1c49600900801c1161000d0208040e9150b24000020f490521240c1c40348480040762005017000d47d030303058403034407615155040c0d00c4481ea46440c021a4144600d8000600f10780c98401400c0345100880c1503d4404d00039407040f07500340e482d1201c0311800401500c200810a510800c0300030348130820042c41084081c0060000310b0f500e07806956403203a1039005c43c200740000700c0100f408201c081e4031069165a0700c84c100c40705070784607040c18041040f541c10404510700903110a0040f540d164032441035142c2104001c0c09031104c070041c52410134040c10055928009100d09c0c800803c08080c41842110110780a25101d90300c1c0c0001c800f404145c020364040084c2d40310318079 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 168948642 1250 168947392 168947399
    0x80706030b2806030c0207050a0605090d0803070806041112041511070602070c1502030405240304050c031e070515070f0501020a02190b04300909050c070b0103110a 72
    0x4101d0080a045900b810800220b052200050460f0b03090720004c0c0442d4001e1104125603103c00c4444000d031406458038a55a40700000031501844018800800c0d00100004000d22a83d001c050240500001c90302404125100c040c2c90116000c0c13030980701405600c00b40810001881c1c5560a10140c110074004240004202603c600a030003010302611203d40000c1c448007080300e0780141078080c1c03200b0380c8040c0e03401d455800000c2d604e000d01e00549010b40000086d0003811940c0c01c1860031044220b240807590b80ca0702d071804584484a160416010703105860f002001c00100c91750765441e03518094000c0825614103010401c9108004e105080c116004203c02c4011a24042c2106070081c092000546e07201d483c1440285020603ca80140c00742c0900b001400005011022041d000394004124050f40d42c0c0e034a0111518403107544c0b10038030340c0c4034400344019010f07000b00c9501e088803507a0004004c1941d440c05020a24414558000c001c544071000500004502c442c8040ca020800348c281c00300540c8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 168949892 1250 168948642 168948679
    0x12051902031903080f0a06060504150e090c180306061c0c0306020a020703051b15340303140c04050105070303020d060909050634020a06181704080706030b 68
    0x10b02000b60009a949400c0040301800076a41681090020808101d51840c0480080c02e9020b64081c401280c840113007448a150710a515010408000410a400074207190000d118181d101c03c2d034803102021504105640c5250104609110340c0014050801400c45400c0c43d0b2800300064000302c0f008100d014020000c00c00a10107001131403040e070001e0040c07a085061240c03034084c8075004c000031a140e2103500019030f10707258a2820003030b143c6201c1ba42c5442502c095101c10b00c1412100d0340301898503a01c1140d00e40b08092000b40801e0007510100045200300b502c0d4410310340112010400b00c1000c020030000c0e540b154005020395406882c006050884a01c501c07019103210341c2c4140001c9440e20292020300c60300f032120541151482903284044403402c5481c100d40f0a00241600e550240b45884445c031038002d100c0340d5001c41d0b1095041000c400482245910555802000c2d100720500c00d80e40305508900d08104c60a1310001d2004014891400908074003404550ba03540c0d80010140300a02c14109 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 168951142 1250 168949892 168949933
    0xc030e0307030e09091c050702010c0506091c08090c0f15030a0504030801061d01080c0d050a14070c031b060605030a0605090c01030b0109120206071410061205190203 73
    0x80c400d40e210b50003a0300d000c0800c603028001174852402500503007108114100c00150344400b0740756508240b9200d00786800140c0d025400404007601c02e004003010404154008220b041901490004108082c501c003003048505940c100e900b010558030940804443d80b034920041180954014496050903110b2200400180c005032035551206480b50305100c02c240e0090030aa02500d6140b03024556542c40e21429230140e01caa11005060094400c08254008501d100300e580d040c4c480101400641400140c1100030301d454820850903c59540100d82124840e400c10301d01c0d2509a42e845072144503003c0346c4500e51400b040200c50465071144009000c0d01e0610012074103500921000900b450400d062600f4406e5807072620f81018075010f032480f2641e07000902d04040c1d802c9103c0d8074190120310702c0803503064411080c02503d606084501500388a0002a140140340d00800c0e0600080d80c3d41d80001d810610100c0000b007041e04204034000da00d012415802061900044c00c4510028040c1820000c91 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 168952392 1250 168951142 168951157
    0x5060d06090b040b0d02100e10020a05010b09010b03070810121103100203190906090204060f060f020d09170c0603070906031401030b01060c0f0218060910180c030e03 73
    0x540d1106020007107201c00d4410701e0800c40090310180800b035000b200084d00d82c81c8440000b8440c0401140e89001c00340301e03480c09000810085d0280c0d5201c5503841010755a00c2c0000b804981c0d540c03c001d1100003038102503209a04840824210714296103c1201c250707001680288035007145183c500d40003526015141c403510400307008010510307451003042e051509212041c0080741d0075a0040007271011462900707101d00c180c0303103019800080e81c601d1842d20740701a0480e00030280d4854100740c00841d091075030007202d200305c918903242c034145000c181200fa6290341c43c0065250106250781010041d003900310f402e600c803100080c401d07202155141400030390070307820944042c000278980c00e206000454040c803a80b038400b0b15000051300360b907146a64080040405000f42d40c100003502d03400404005540d00810016540108400c008064603c2c16480c064004c40e1301c1c0e4132504104021404007004a45c920041c0c401c105550003a018064081501820061211740c0c10166942c0f55008000b800f071010b80b0030f0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 168953642 1250 168952392 168952417
    0x305070611030103060f18050309010c0f0602030c0c0f010e0c0904080d0903030204090c0c050705010c170c0a060b060a02120a0c08160201031d031608070b07021e0d0806190506 77
    0xb4803407400e1506c00c036401001005540700080e003000e808075a0000685003a80400d2a0000c505c0c0302504d458210b4000000c001045d5900100600034845616000b504c0b880c181c0c501291024400c40c1902801d175035600c50801a01d0300415486809406c024a0040d4405e002d545241d18215402c0440c4d030450300000401e8001aa0202d01446040003c2c002c0418101c003078900b60341e090005440e2140c0780c0204d8401c1ea03061058261043d410440442c02d21844503020884d00f9440c2c041031000d00740c8903425500c00b198100d02d080398030101485c2c55000d0701c0209140b0703401040e41c10300e41c04241400d640403010f0501030065031b920b40710001d10b502008120900010149072402c42c4644000b606030b0303194440310560030320a03914008600d42c000007580c910b41c000308001301100c641400d1041d0320b0701c500c03038010b814600b881080056440e00002e401a01c00c1d06040168078011152030019210218070503e0300c005440e001c0490b060b072400020111406c61402008040103030ba4000081c07451f41f18417111080e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 168954892 1250 168953642 168953651
    0x70f0b0f0601110a0201050d0209010207080a050d02010510030b0703050c0c0706031b030603080f1c0c0c020111010209060a03020d142d0c04050d14010c05040302040522030507061103010306 83
    0x4030b5034401a03142d00308240c2c10043c500c1d4002c5500182642c0507000a12407090782c0070441d40400c1c0c0c0b0030405000100b04540648a0b5001107040180e1030359004ce580d80050b60900010421004000d002c45044940209034009c0315100c040c421401340c60b020b40741025100f014411411134510900442e8001c0c042c60300d0010f4842c01c0082e0b14906c80490446580078103241060403c0403071001c1c03048030100b8140c880c41075628903001400030401e001140850780303000d180180e803031000c9800c0340c04940100c2c000d88442001e445003504507401e17841103200c81600b24400b4041004d406000760007600744d5503012a4080f50081c950340b51001c1d6002c085640340c0d0300b000520141c00c01c442c600049e260002c001c0300c10307001c514604600c10045500c00c42c80b40b24042c10840100205000101c941c0613143c603e600000d101401c0b40071b40c0105281c005000507403045150034089980e030403840d4000d0302d40c3d407091040215110700742d48090f00c003500480c00c2650002d0300e40c801c4400c0c40ba8440001c40c040c511a403000107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 168956142 1250 168954892 168954901
    0x90213091b09050d02030a1b08010c0e120a1104020703201c020102030f010b03040501092103060b130605031e01030308040c170703060c0207080106090b01080702060f0408070f0b0f 79
    0x30200708407940214091082604d140016072008281e0a800940000d0114001c00b43c0c1a02580f801240e94040c00d035952030100000399807a40542c00580030703107045862440a4900840c0d9945030040000d00800a8490488540f20ba0a2a40240c407185000f4242980c10300c030352903a28030341e200480c2c45404590f005030040320903c4000c8540c4188081c041d2000310304529040700712000d00c04040c0154614800040001000c2060940091807100c0d0b0000c3c1d10490020144040c00d0940a1204034002090400d00c1c0801c06508050903104401d00301d03908070400d14135243d015202544050b0054130b408511413500c00c410f800d0050070038000d501c2a074a203061403810f41040004c1c01e540d5009000001c42c1135159034404240040c140301035036045280010303003e10b040030030303850305040354026800c0b5402c0500002d0341e8550340d40301c82080c010030703210300102d0f6540440c1241c403028211051034081101ea8045804030761a607010700b10440c0b05c0c40e00e0296940755a1074600b004070302180c2c15103080d41000c0410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 168957392 1250 168956142 168956147
    0x150f13021207090b09090429090607050a0503060609010c20090c0f071b050a060e180906130303141306060503060705160f020913110901060504090213091b 68
    0x99500200a1500f0030009050045284a41c031610346054072441403140850305100405842d155030544504840701c00c14107041e4101100c82040710102c0d0640a442c0000d0542070040d01142d0039001c6980d81d262560740d40104100e0950040d40c017050400c0f50780b071000700004019800100c0d154460030091400380c52400f08102d804440103000a02c0355209002841c6503080d207005507078410b94450300d025011180000c00c0000100d0560140750300c040800700004002d40c211034004400041035806152000c2010341d2b01504400c03e0f03a000070f0b203038450000200e403010403507603149900d403081c5400f0410401015902c411007074150317081d0300803503045001c8008101c014490f80d13000b8001500a45400c5c80d1002e0080d2560060b4201c5405907505416228200040c2501070483c0300e900900c01200ba0031b00a9546410609611044509110b04070090301a458080c200038100c031650360742c8500d41810301c480714001e50007605804d45039020003000410058502d0107000360b05402382000540542408100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 168958642 1250 168957392 168957427
    0x70c090b03031201140f1e0916080705030403140d0204060f03060b0d0b0f090106051b01050f0a090501180602091306030b04140f030a18080c09150f1302 67
    0x3611030390041010240f2000844511411030304098903002c3d18035000030201d451000140070640d44008681c50141140a0f0141d02c84290b00041d07900503000e641d003208200300d8208420141c808242480c0c0001c0d5118421401158002c0c030138a0306501c4045200400942074211800003401c10f0f401250a2142680c41140c00e80c000c03040d40703401d00055240410b0aa902d104007080040110341759125148191200c01c6049240400038000300902e6940c2c9030018001c0c0c1143c5007000300ca000848103800241d10501415000741403008280c0c8003925200340100040014000841c3c095482c1d070a90406004000d0400810034011440507982d40554010040071540070940004480d1400c0010b2011540701441c1c03d611540c403480030300c0480c50443c101c5141001c100e008a11714480042c01a0a036540180710b800e0b0700c815544120070b8192038000703140d00c424101611a4001562a0002c0c030004048100e0404240c805440075066075113040104c3c0100b5000c1004014040d0005403240b0a040708100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 168959892 1250 168958642 168958661
    0x3020f09070801050f010201152606010f0918050105040c0608010807240207030213060513021204230a0b180607090e0402010e0a0e0601021b1c0809030102070c09 71
    0x30049654a4540300c050560101030050710301031840e1800020301c0b81d0003503000004100391145000c2d01c25660704001510174420200d010104900342c016101c40c1d0f0400545507060300d18456101404c94201000307c0d0040c400a40300038050700d242102e4402040303080c0704150195000e12030455200f0709000010740207403010791007880ba81d400300e502000650810855540403c0d81000710b0102010146c400300d16101494102950000d00e001c1094440b41d20350303005000f180c00a0f5207130300304801902c40f000201c0c01014845601c0843c0c0d2070000b80040c41141c5d9480806101c01407a80e40c200c0f610030514908403900c40d0840b1303040590740c10300808008040d004200c0920300d02c0188034905d40820028240882846140610a03100e004541168021080b000c8682d1001d03105c06600e07a82c84881c03010210064a2080c054007642d0001d9a0001400c25a16080c0c040a00610f2622012417512452040640000d076808042170009050a96003030000342000340c090524080704a08090010040b1504400c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 168961142 1250 168959892 168959899
    0x5100e0702011a0102072610020406081609030210080a1514040e0d0207150e060a030903080f0f0c07060e01020d021306020304050a060f0c1403031501030603050a06021c0207050703020f 81
    0x2000240d20b1034000001f4107914068410b150400350704010301e800c03507220103406502e002050204001d030348503101610401420910000500b10780c8001d82d00f00c41c05001c0a504640000943c2812078018402250003448607500040c001541e00246007040c646a0040440e2000b8041030582d0b40c17900d07024401c13141003640f01919003c210600003a585031042c2c80717014240031411944001b07c50007441e001a45090240245942d9420450024000c02d0300c00b104a01040700400400c2541c0da441840d81e1250001406c200c0380b1303032601170010345181c004c8031044804a40320300c8440300c50907080c0050305084001c2a409070300c0d0740401d00500901140c6800c00c5085500c1400100a1a03480c00682800c64019041440040c400031504941c800507002d0080e1203101964001e8885040010003075202d090811007565800c0101401141a10380c90701c4040d010b41e114150307441c04601e283c3d004143e80720b08141414520780410304800c0580c0c025a2003500d154120010820030750504103000c0c0064403048 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 168962392 1250 168961142 168961153
    0x20a12050618071101060f0e01080609060106050c010b0409140606031b011b0f0c0f0f0b070227010f030302060609040203030a0e030c130509161805100e0702011a0102 73
    0x1880402c01c40c04001e026403441110400200e550715010700c6000203415602c20090100f55101d007208030042a0030b11485600e00815000065039030008107049014100300d501406540c2d00e005411117040c0c003c2510005070703550341c0b000c0c5440c594542c0700e02e910844c804c13a82c101c0c0e080f1180200030b082c084010300942c00794024805010301c0d0b000020505404c44030074280a566441031131840d040c10401260010140d000c015030060500102c094550b0448180203007102d082a2500c00135004030085114800c05298140480c90041c5070080140c082c40b4502c40503400240d18212489500308402c1e0310840314030404001c00e0090680c180580d540c040c10035141240e65050a5010fe603483c4584281b00d401c01040d1001030209a50910003a824200010403000c0011303a4030b40c3c810018801600c21118500c61070307510b4001100044501400c403010f828021024a45103e0304001030035000b080d035894482d00f0000401e04024181d20a0302440703207079000050031018008080c00701502c1801d902d0545d40300 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 168963642 1250 168962392 168962401
    0x3040303080403030f02090a03060504150b013005010b070605010506030106120e01060e0a06090b030f121c020d0935090f031903022e0c020f010906020a1205 69
    0x80d075280c00c154945800140c0441c5984204002d0083c00b884d10340c40700380c10b2000028800c580c0c119500903801100d080d803000040c80c0d030f00d02c00c98108040050102ea9203400203031260415600c56025155001d85800da03600e100202c000072070b5001d802c00759800078046420400d00595200b041d01410041e1581407031941400000380c04400c8171a0018080782e100d05460002c183c00307400090040000d45007045040c200b48007880003801c0c0070300420741c20a107230150000141c580041c1041c66206000f000d4220525492405005c42c1d1000342081c4002c02c200398036140011680c4000c22070f960503940300041c0c0c003219203003102a00c00072001c10102c1d101c1440d01003aa0524030180b510b10b0391044000c65565110820110b18400e9020380d032103515011300e8408024a0030304428142d440c0303100782d00380c8211201009180146001d669200d42007a1840e6040302048a80340d44090f20802d064011a03400503100454036003940c031484001c803103280d004070700c00e0045d641011404d0740440c024081840f0f00c0c5031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 168964892 1250 168963642 168963647
    0x10b040f090f020d09060501080c01031a01030507181805010501051e0c07050603010b0325020a02010e0109050603090d080615030a15030804080304031707021f0908012a0203040303 79
    0x140d8010a81078641e181c0604009a0080c0d04940b03503060249803d00c00c81c0c4450403c10010b0000344641101070041c0902d042c0c040d8801d10658085c41c511315016040e0f03941982c011001010000c10810500c00f0480202d0025201e04a00308000c01c612410740840c43d2601500740e0640d60b040c1d10240c18082d051000340200d10202c030400c010030303188120094079441d1041c000ca28000490348416000ad80000001c21903012580082d80700b644200c00d25035150450a200403001c2d9a2869201d006030880743d99080198490741b20226403403c14948000d00c4d0f40c8880010f08a54400d071010030241c1d01c03401c0f0314114142c1064032141d004800300d80d284551041d550500e0440c0c480100070030f2890342d80d07003400320400d06a10b00460295401818060304c0d180c482c0511640c1b680540402d07910310210590b41d6031041c0c00c440c01c403210349902a145c401001e030321010503040e005618008000340b0032a07040c081043d8a0910132209400207402d220202c5c642c0700c02032044008000c00c6d0340380440d0002c1109201094 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 168966142 1250 168964892 168964919
    0x3080c2a0f0108090102090d1a0f070c110609060c030307031d0a08031803040b071b03110d0302010e0d02010b0f0301090528060c031a0d0b010b07050a020d05060f010b04 74
    0x70020308000030b035a0b8032551800c1c02071042510103503020034110188424003415150b12014041c0311000380300c0a440340b03c04400341d03c8040f1210b00c000303000c6944030300005100c41501040000013400c03041c00d1084070000070b0f90726084904110060780c070200c100680b00350b044c004c0300448035100644800c0d2004500301103882d003c40c488044c2c44221300001040602101100d8100600d42120030340340c4a80d150140c1401550169400f916100d80b08544810f040384550950700450b0ba02c2000c2601c010301c0801801544040f4450640035956604c000c1030151900b484410303443d0302c0c664000142994800b00704045001c880c0c840901036890401400d00060001030f0031341240c0c2c00030717548040494880c40040241c0c585d800d07000744102e0505e0500101150107401606107040c111840f204514242402d10100e6a4010005000f00c00d11100400c5664495401800d0483c00741c0709952a07500103401103006a40c0744001217807154410820807008410f0001110f0242c19400701451a003407070f0250031140701 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 168967392 1250 168966142 168966169
    0x406050303160f0c031b09020901020a02040905010209091513090203072106021306080a0b0102100510030b040b04020306100e1902040806070f0906020d05121003080c2a 74
    0x400c1601846028040f050300e5115010b0751125104401079201c0c604031020012030070101141c0002c03060040350000d064000d4a105a10690041146121507000c02c000340c0300e0307864140d03459582000b0306801c035101c1500581c0300340d0074000c44240106503101449544400540a01c0035145411038990040c1e801194840c00c46540040342150030181c16018440c0c0800c0301c20041082c2d1000417401c020b01a01140c8030111001c0745c6403100e1550b98644100140c81c0302d00c0030f150068100c0781c252040584294070003170700f2000c001103031561b4988a03aa50b0780d4210040d00c0070b40d031000d00c1200700000c42c68100000f0303520010b2000c09040441c0360903d000440100036022814a00d504c6204a0b0502c01ca03505503070040140780c085418a0804c80340107440701940080324000a11070742c0000c10b10300d0000901000d940207583e5140e1912101505045d140000079002c0f180a99507100c0000200c0d64290242201400300700c00361030300020381ca040111005080c02041071561602c1541c070010355a001140340d0300c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 168968642 1250 168967392 168967417
    0x20d2703020909010b1002060f060a050d030f03020f070f0c050f150703030b090703150506030705090d050703080f03073504050c0a08370f0c0906180b0406050303 71
    0x40743c0300c0b0b68203c0c3c09448182046500032400300c042e00b006590004585000301002140300045446030000d2011903601806101d8208400d005a80002031007203c1ca6018030b080d518005003800c550555400165004960546424814013210782c1809203150200c4000d1070700b1500e802480032900d020680d18050100f44903c00c40c2e0100e445401d00d80603802c5500422401860021140780984024004291004c01c0c4840c020304818040740c40c3c00c01d241142d004040d9511030b50f0402c0700c0038003000042c0c0340d038150032115801014000000a404100070700390207600d0320354503501c0f4541498028139084010b080309481851251070380304180f940d901d859030320040001e0001840d5459007844c9203011840c850a03604a0124900080c500101140a05400000b0300040d41466418900003211010f01440301c040d81888410140000d8052a1440702192048091010341075039180100d00f140e48030343c0301c0105542c1218074640644003030b225020042800b201c04002c10b60510020980d04e00409440c03500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 168969892 1250 168968642 168968659
    0xe010e0328030b1c03030c0806010504051009050a0e0f0714041521061d060f01230c070311030a0b04141e1e0615010807110607020d270302 61
    0x4070a110360402da08440c4080d14401441c1a04640403e100055072019070000e440d1140304c08006100c6d0101c98000c1c801613684c9800d160424007002962025464000c0500003042c40c000341e2904c61056040040c140400c481d5864900307816482d40c8158006c05600070040500200602c4007048400c0c1c9080d0746140807c902040203026080e14900c00322022981030400078190010703e00c0003508820166150050000e50082c820b03114542d81e51001ea0350710351b000e051010410b0300355100740800e445110715604d854410054201109555138080035444005420648040c42801540740c14420000343c180d00078403d507901500c030002c00310404ac10080c0442800400c0424034041003220041001c002a066101d81403406e407491764480a07001c0901000c0011641d42c20382d00380100341c103486200b02c00e0655520540010044134cc40000410840c180218640c5141800300200300b500d00c21503850b00180000120100040c00f0407411003510000040c25112071086c19046a07031203022a6815140d421 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 168971142 1250 168969892 168969967
    0x90b01050c16060201111c0c1b050d1e0503070e040617070e101a070303152601020316030902040b1005040311010c1106031003150e010e03 61
    0x316035218a800c600881e20035000d44102c0d00d041c911030030045070348a4008104000078003440805502405040d46184c44c2d8030703210340b911030000d5080100300b0303900c500e010303481c941c42d41420103081c0b02c86080685003503000700315018a15401400000300d14001591007514520440d00c014040e01c0014071035010004404000034082d1a5500400003500c9920002803010701402d000da0f560304c20034810209140401c4000c5407034104202d1005040d1900304421900340e070f6210420b00001c0e030010808508055a9249400209640d010340c03501401000b0b01020701c09010310300c080c4811140c0c11002203282d1042081c030511600c0c0c00c80e89140209503050200709956940001002011901032070b9400c48081c000e1012569817110040c0140e80c4190500400c00204100440b801803c0e1400180700540c414181881494103102450f800061048090000c0c0c0e1a40d1701d403144505078840c24104503803a008008600314007170003208204044103005506040000c1100403201c08907440300c0400e030b080c0e011200e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 168972392 1250 168971142 168971147
    0x1b0609060c0f2b050109020904150503190c03020d062c0606191d04120f080109020c01020903070303050c010c030504020a1e0f150f050703080103081602030f03090307050a030309090b01 81
    0x14100c203243c000100119030752104080e010398080b0203640d100d689084141d20751107080300f90410544201500411000078415140450703140007907800d64001850400000050792801e0a0520107403140402207680a80064082011b47c1f603002c0e04000014440e42c03010401000041c43c56003c98102c8000d003440c410610002d283c502550401d140d80714000c0301e5481c04040307106ca058041c0348516020002e0000702041215403c6400785035000040400700100400013083e000303050045118030005140c04050000285048615402180482c4022502c2000311001707118008110300b05040a000f546020342c00110402d05500a07884d1200d240b0308619204001100718001a25a9503130b0385607819100d02e21010b1034444040b00c4800140b5203a40319415520483c180c466142d03040d1504e00490b4295a6041419001466000c01c4000c01c00d00b118007581d0b04019071034a12240c01c020310b40c1da150354020b150403d0420303008107000d64074043c01080000c1d48000000110b030b45a90740041c0000340c00004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 168973642 1250 168972392 168972457
    0x90616030212090703030906050c07091a130c030e1207020409030201151202042009012a0803011403030304120f020a020a031a09010c170c1b0609060c0f 67
    0xd40c2c00c0b124400100540c0c1d103000101d16050724000c0c0c48003070000303a4a6104071441d101d59003481d038481c1c0050808000c9a003460300000c56030002c2c200d80080090080012943c4500c0c000060f440c00c40e12200700c0f0100c5501485030710b0149100d41c0141c4002c0c2e114444c500765500c034248000f03000755074510400091502c02c5d07103c0703104681d100c246404407554070004086480c031000700c164030451408000118000c2400724443c0040e9084243d5400c1150120040d01c030b1000d0700c881c0000001101000984e141034000d9100c0c5800d218009458a80d4106484030b0035440490100c035009034020020300000ca503014855129007000d80c03501090881a280c8203e040c1411403a0082d009011040040308028070901c01100c0038040a100d0400750303039058102c0d0b00342c410b20180b60300480c045940101c00404e1a4122a42c06044554401d2400d9a845024603080660500221140c0c00180500c245684240310607a0002d005071801c07800c1235038054042da1680300e4402d18001401a902e00c0c6603540d08404071307 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 168974892 1250 168973642 168973657
    0x3050f190815151c0c020d0f03180b0a0e160807080106050a0b071419050609010501030210030903050c06160f0f0503060d1a0702010e010c0801030b0403080606070602160c0e0906160302 81
    0x4c244a5585040d501a5840c0b030310308000008140840d034400302540c828468000086208051740564100503200e520412402424241e501921080300608440082025500f01480c000e100e1b0388052601010b1742c100212038000e1101a41040c00c1000b4a503980c10b000030644240b9000303280d690f085486c001031000100780c080c030b9040c0191000070300700b6070744924140e03400ca00600580e001a6602d0800302d00300c4030709000081d401072204003980425842503008464051190501c945040c602c19205850074038101d401c0700070740e031100100407030055000361880483e04183c1085a0340c408014005052404018450b03801038070866005c00c28081201c2020360381c842001d640700c0140c24070f104001d010b06010940708145d0340c01c01d13010800070351164a42d28100d0f40c03c030340e10110b036441c1c95600720340442000d0119584030400740200008100184010088403001e00e800083d001024589013041c10b10036408040d22180c0b0004100d00610b02080030f503400305401da00c6a03050342c5661410341c0240240b18 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 168976142 1250 168974892 168974947
    0x11b08060127060e03071e09050109090506070503060102210a031407141309140a05070f0206041b15091d04050a030c0302070f0801020306030c120a0f03050f19081515 73
    0x180030f03d201148075050075040c8c0d030328134606120581e03c8040c0c44080e1009190010170550200c00080c1c0c915101d40040c0d80c0003c3d0503c1664a480c1e6002103c407420440f07041c031819040d00c000741032840240c05200e540751145a8a01000741480c3c00500503040c01c4103c1b10541c410140050204110003800140c0b0014100d0800100b10903820501100940c800407102c203280245040007040c0304a0180d052403112802c5a03000f0085070366541c0e968900c0c0000885400c00c20006100301050242038003407402d40c1000c0a641c0c00f01c81a140600c818180342d460030105442c2c04030013050102155020a601010079054108807000c6134051904070b1900341d45501c071104881c20700501154451040d0000c41c090034085040f141006d9070b05003040300780066030200844030380c4084002d10000390207284181d4224000d041c4641130060084030361034154007103281d9040d0b03504030510180556420403940d070b4228501c449242018210320f4040303410340c844820210504640480d0b08484550040d078502081008007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 168977392 1250 168976142 168976169
    0x60f0121120513060219080c070302102105010605030f090705060c10240302090a0b0402070f0302211b030c0115060206150f0909011b08060127060e0307 67
    0x2074002c0140d041003103220002d0507040c8000500c140b00103290802c2c3c01c1d220202170344000b160703a281c2201e5441510354550341e000702c050010240c1d442c00d042a409103499100c1502c0c0d5081545800d01d1000341200b4059200d10340001403120582c03242c2a244d003d114420754812644604110b03524290907076004035444030740020b580c01c00c2035010807a1511000103200a002030180c92420b1100e20413950780709141461070110403c05031401c00d50701e60300701003c01c41c0061b408071040041401c1c0e038020340050707640000d0444860100356040069030515841c80c0860002c0d20380c40e03e0340c4441d0384a560308104600d240b448002ca0711203024000c4442400c111002080b1714a02030040d0346041009118203405402481c0008084060805003400310f05001031145821000d400d080080c140405441400d07199a605e0300e2004960803194010341961031615116528a0140d00046c00800003152240411541c03006001480a20444007000d60740c103400c00d070388100200c3d4042072810b58198070000003035009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 168978642 1250 168977392 168977423
    0x506070503161101030f020414061c0c0305150108060f04021803030712110a05031c112704230c07170a1b0b060409060b030709021803060f0121 63
    0x515281e143c951000c0c0c80503c00546400300c00390890140348584410000300e1260f880c034610340080180010089148201c00340401026080304841040a0700340201c0c1d5100c0034016015600c9070f400b01158402d1802884918000c804100c0d21948012214002d98000c1582480303401861054068907001404807074544003141440d504d0100303460380b100701144003000b40d020488004100d0305005a00440110700e442d10001c00310448080108001010682e40c1110001114540c001880c03000e4000e44000100e40e00800e44404c041c00d981c0300f262141e840c140d440c40c400c4010881c1d42280c0b81da101e070341c40c00715038480100703850901c140305000381709455000300080c9185d040c0025001c0d20b146a42c032440020300c840407400110030214805495980003200042241ca00346e0000c040443c8120804103514060340c0103c0d150151a8010300b19168002c42d11042400c48040d000300022401c90080002d030600465180700c025041c000d0001241c8464514074004036040511002d030b65100c410340015025 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 168979892 1250 168978642 168978653
    0x141003110c1504060b0405041a04050718020d06050306010f0b0714010c08041a040206070b1302060a020312100302060a2703030e0306070804151508010c03020301050901170601050607050316 83
    0x10480d030031180710b440c00402c00c5c494101446103601c2990300c205c1460100c144500c92014803440200102c034203108019000c9540706108400180c03032040078201584034810f9041140c19903032590061030007039004500411108a04081c0c180c120340c2007a910135592943c6007030201c0040c143e9410881c041d828101c0c00b000041d031143d00d40d407055001d206100d42c4440c0c400201c40010101782c0700a58071040a109000200d55500d24498111903a41c1c040c3c0030b202803ea011582c01d810800d03107080507030030100b014122040c64841042c1e2104000410b2100c103419940000c1f070502502c400041000102c089040500310803070ad418042160000400038030307170758900e0020322060040a02600034000d060100e1001030094405c04c1c00750f036000f24001c80111009190b40c0040c044c0d5051010500c05507940040c0b0301c4800c0c0f00301c0540301030725900581e0760341c142028802c002c074060b4404410301c15040380d0703642d543e04041091415103204495050342c603901e50418070310b54024405180b080f84401001c0e03600708003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 168981142 1250 168979892 168979933
    0x605060a0818010203040302030712110a051e070807060807170103060605011e02060f060d020a09050108121306050a030902041a0102010b010f0207050f0102070b0c03070c141003110c 80
    0x9002d00404852484a00401070903800251002000359200703200020000d92a00e4010101405926064a143c500342082c5850980700030801e9600390049040007400c00100c54030060b061240342d004010542c03420a1035560340410788a40e0003040f00c1480481c0c2a54442c42801030441c00488074607800c1c0d40c59060000080c0101d202d0140421000c4905d032401051003010401d126203980c010b00925520384000d0b80d800d0100030141ca50142c80c030391f044801a40c4041c0c4220180c0300d1014001125070400141c9031412410420305140d0300c17070501a502c84001d00680b008140c032140e01d49075440b2103030320400381e02400d84000001d6019007010508411113484900c0d001851000364000c0c000b0152200055482c0039083d0068401a04506c4003070049080604841a02c10340610403145080d036115012002038102ca03070381c600290000682402032290241d000406040d4100e00103040c1c1045000040c0341c0d9403440e8a420038103480c3d1081113941040310781600e82e4143d8140070b0f034651034000305604e00c101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 168982392 1250 168981142 168981151
    0x30a05031201050a050609090705040b070503040e0702060606030c0c07050a030609110f030c09041104060303020d09090213060f020708030a02030702011404030209180109021801031505070e130605060a08 89
    0x6000301c0c0c000107002c3c9403514918045a5014004910b00210b080c2800400080102600c0c2400410040000c80915880042001c4c5001d0000745032142d0030030b0889210f4000181030070045601c06024401c091b6070302c00c101c94100c281c4850150780c80500c04201424854035900c09a0b00c8004281c0c0001440140d030801c040c001c0c810051850000e030745e241040340005c0c081841c20303010f610075a942461800c21580382e42c0c0060240d281410341200100008060b10381d03139001100140c01400c429007090fa00011450702030a0702c40760942c02c000310104804041c0c10b862042004000e036201c4200d164034000d0080b600038144900c10b0381d640e40c2e001400070b9600c1c0c0c00315408170300082c41d00c1c0840b03142d66158402d070b0b070907264020a69040750f114802c1601d034155200340742c52800e541e150206c0b00181d07190111058444981402c040042d89181000d46608030680341c4046080d0a2400f00003045900000d41500c24108880c1600800e403000c0c00380d00107100c82d402c900d410040005a0444058000c2d094078800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 168983642 1250 168982392 168982417
    0xe060a0801092405040906020706060b12010803120406090809101112070c0504091401050f0f070e01080c0d060314062208091311032404090305160501020405030a0503 73
    0x21000c81410f1408040000150040103503c60050100745050b401c403100d41401000b0160812020351070380000c51705140e20400c01d138900000c80c1000040000211801400727803801075400d2030400e646c00d40c088540144010801c82c0e641c1c2100b0f042000f41810b6411050028201000e02441c03124040c180c0c10950540c60700300d12800c4640094000d000044034240c0c1e0b40711083d07144092614040c4000303840f0242040fa079240b0310303600008140601348100c601c00c0c00c0d0b0038100141c5041022290707035801006003000c420441c2e28860800140d030080c44d0241c212100c01c0b1140d544204202512000302000d0300f00a148803102003040401c0d800010b5070ba8040d800c008100a8021559480d40020710700c0d44000500315001849440010b103406242446540920900400d215244004045d0035034000c69400c0740b0b07110110301000040e01401c0d84c1000071581600d040020301407030740780a0014000d0200d043c122040c00300403042048804e40683d4020507010f02240e503000c0040ca015074907508044403000e030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 168984892 1250 168983642 168983651
    0x30b0f1b180f0a030305041421070e0a0204080c0d02030c12070e0601020a0c06030507030b04020d020a1d0109090203040c12050709050f0610121415040e07240e060a080109 75
    0x2540e28140d00e80300f003100e515884580c6402d01e4645100e01d00307075039281c06951040058901c86114480f0844501c0b1050b0346401400109060411642c615040581000d20f0b061041c0411303c03c00c035000441a40c0140101c03090980216a440000d01d05100b890034140c10140c1c083c91125511800100d000554402c801421440d0380c805004a0b943c144902d0003030318101e0403c008018481c000e07405076030001a203140c0841d05c01d10034008103069174000140100900d0f8000b0f80c445a00b07500401c0d40d0440d40f505010a00c0a40e00e140000b000709642d8003824188a03800000b0400308019003690714020310481841c0442d444450a04c11744030301a82c0f06901c000c604210015040c400c0982256211b98401060188141603800040350b80e030403000c0e40e50100540d11020700003a500c5ca00b82492090701d03500c1c1103075a410400400e2000360303521805030300b4050b4130010007401800c4411018002100030401c0303040c544510620101c50040b10801e200f5000308001896014140c0d011003000d0584001d07840078003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 168986142 1250 168984892 168984919
    0x206040e0907031e140c03070e0c070803040c150e03031c091b1a030103050a0b0a09170a0306080604020312030606190201020703320d27140601030b0f1b18 68
    0x1d4881b0b00780c2014541c50341001005020707107244616101e822004040700346041c80d1481d51a20282d034001d480a0728400d141d0f00b010000f0400c110070b400b6580e0f29520f452120042010302183ea079001d6450b00781c05480c01c0d41e082c5800140c1c294003401403d50020341c59061444c81928004051205001c0c0c41ca45074a0702003005014003181048178101c2c0d60041c002c01d0380d8400d40e210070044000c060704504030203803103200510100300316000c84094500302170700c040e681c1c0d640030401a04480c2d26034400300180c0c202074200030150380c0101d05a20090300703130350b01c540e6603590300000207400c3d100da0840a000c00000c1040815810390550141452500c40d40313840401010103540c50000da200e18003a004a06400500c40704001d00c0003010b002d40c4000b0b0007000c5640c403203c2e0016000c0c80c496440a0305080d50790f041c07010a020f46424002c0020101501034081541151070300e001c84a03005040c2800f584103040070819908000200130541c8221030b00c460f0300d61026240d40b8615400443c0468030507404550b612 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 168987392 1250 168986142 168986183
    0x3010b0114040306020a111c09080706020714060906030703020703031a0d020d110315040203060709080703030c151a03010b0f01050a0c110a0e0702070609030206040e0907031e 77
    0xe07a8041038220100341881c3c61581c8800281d0b000c0c1112000300104403082a5421804000701180101d00080e1800d092a4442008003070b80140d9000f030040703900c60b020070001e542d0081080001c0d1012007152a4112003c47c010901d03a100c7c2a80b0316811400000821483d00c0d415805440181d00c43e070380500070200c81e041c56040420344220750507800707403c001e480d40c01490104181019648a0f580e01c2c40c8400e4040700003420b001441e1403000c50140c481080004514060194030381c440c041e410702030b03403a41c02c010355140c0e1152075000040500580300044d2061000002d41c01e11048050807007402011040d0107079032981d00113041518000c0d82003103050415442c00700c00e044460b01041e0740341d5043c0000c00d070317044505401032001501c42508580403001c4c503844001c07161000d070510301c03e100f01504003460000d14094059100c801000f4504005000503926001140c08480500504100c2903c131213146a007841c840f40e0006200025601000c1440203502280c030010700e0158404c48403091841841c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 168988642 1250 168987392 168987407
    0xe07031b0807030c03090206040b0a0e09010e06010f0903151b0305060616020f03060703020307022e0c021e0f0c01030605091303020a0503130e070216090f020705030d0b03010b01 78
    0x1200032807540000500d14a200342c3c082c01000883e4540482c03400c3c0340380c000c50f02c554055040070158160024003c544103401580e000040780b4251820180b541c907154500d8a40c0b50003030001e070b040020590b2100c400307520070b00c4407802842d0001c107219001041090f444009107a51200000160407044400d00418008d100341846041d000d0500c610300841054003031501a460941282d00052030080e440700b54504000b001d10400281d18016520304202101030b1808040d800754400c5c641542d649003149040707001c2d4140466200000101e040340c2e503284180d0800c4e00e403101c1059960f0b140001d080800e0b0740000d103020f03450102d206945103030f86800011010340f00c82d40506a04061801c01045111040c10a0800054040e205441000c2c0f0159582411540b1080381d40643c03009d41c01c810300280c020721460342d4224015000030a0400040d05034061015100d220f04805c032a0b030349003c10484202c540442d00c0c50f80c0d203e000e6035a140c2c1900100c40c0106900c1100b2030080d841d0210880465002e9030a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 168989892 1250 168988642 168988691
    0x506010e0408360d051b030f03030123121015170c04050a060515090a0b0315040f060806070f02011d0a150e030711010c0b01080c030d0201051603050c130e0703 70
    0x5054a012840351b214503012002c1c01090f05445440481001803500b03001031400390080c0c1c00381d200011220510300c68070b103a40459092007001e90f03408072584c0c10b00c001448a00201000000b117034405150900c0c8125050581c8207402d200030b207080c080d210780c00c04a0400d16150f8100c40410994940085500c121852030040c550031409106641d051082540c0c0585680784005010b8007040d07407202845000754000759242c031041400c20302019103a1400d402400d564101440301084501d00d803880d801e60b02c2d039025200400303104441d0b0722031a20034400e4004032045154464070482c90044080c0040e0780e240b80042c151002603006500c01c81545030b0b80504080c00007000011070a043c49601c0c1c20701520003104985040c0000814500000303000d009070503000b451040060414006813905260800144941d44011640b416040000b10b200e1000d4100042e9800e240000380741c0da80045404084c42400813586602c1c604000004400380e03a403072542e115841070313035092150b55407074515034514105a61 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 168991142 1250 168989892 168989903
    0x90e1506010903020d080c0106060908011b0e0904060e01020c1014010f0b0a0302270306160909020a0203071428080711030c0a06050915070506010e0408360d 69
    0x41000d480d01000084095008050702440c7c050525011801c56946601003404560300c40301c1004882003c0c41b49680607614803013200c030801c4007103400a10140001c11030b58403c80300e84010406000342c07030303001c5900d003549400215030312130072054500d54841c040032a002540f03061040100240c07403802d00450403150540541100d50342009032540c0c040e0490200042010303401c1c0102803150350070740d5001c00d803001e804844a08900c0143c0a050074118000c0802f5071101d2428801c1e1074040e84003000070203c8020f500700584460000c034040f810b600c0b4414003e0959020310b81c8642d01d0075400f045035002d0311702c00310800134242c54520022070150340341703c0d01801041042c04500d02050101100108242005042d5000d400740200068031205150300860001203010038614446e0038a41c0c4d510003001a14040c03982800302d66540c0a54031070050180d07048c1c000c1c817400810108001d0006030386040b02440c10034840310f50005070100c20300343c031501c01041101c139010a056060422116414a040d04213 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 168992392 1250 168991142 168991157
    0x50405100e0c030c0909101103160f0e04020a17040b01050406061b0206090114130e09010b1f031d0309010306060519030506030c040c12060812070f0206090a090e150601 74
    0x20070130084a45c030010007103029070061440000c41c1126510410712000c51100b41d881d200d007840c00c0383c0e000019101c0525024044180ba01c1150145c00c4a40c074030141c0c3d030844026940b0819090202c4000141c00c1b030307468200d81a8014842008940f40d0560b05840d01660200030040d56100d0403104142c185446031001c0401008450150600f20010004102d06040504401c007050781c0788400c55002d920303004200950070750300b13010440140302003582080340c1000074007490604000241000702c40c81014003030b91400c8590340e9100c9020b034200500c98145981340e95a008942e910301502d0341c0c00020001d0000c0e02d00301001c10014041c10031360b17040443c0548079010068203140d00b60000c080146c41e05034540720352521140c803581c1d14020b00100c040c1954036502e4071581032181c40d05880c80e607007019240d50800c00160b440720340700c8002e4921030364000e940307468901c00b1400030800b1071040290303640e04a0140722008c20724002036001104482c00801c02c40d0180107001062400c203c030309035150350000341d0300c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 168993642 1250 168992392 168992413
    0x302150f03041e080307181703040b1e0408031308061b0c0a08030a140c0307140d020705010f06151d01051c06030525030c120f0501050405100e0c03 65
    0x600d541c4104030302c203403103035080e824444d4948065070341080b80c0090000d0300110101400f4460250510002c1c18484803d00c203407140c20201030349a00580c011444001c4000c161411900c0244502c4e15102d140b10301c41e03c4d6500e4640303400710b403070350300070626100c0381000b009001a550200243c81d501c62041901c480344000f400250480c0d203079118501480180c0300c0c3c42011380201c1c0407500118054101c540c0c0008003040e03d0311905078040f00040050703c1c04101031042020040d040800e401743c48440390301450703a44048451200c003d002d988000340141d8640743d00000e008200b075001d032059540240945005e069800b404488920100c3c01400200c4054004202154001c030301601521f01440d0150071100703120507289044650990081d41d003680801c1d80c8c0c2c00180080444440e89070a1088168010340c04c54881c03c0700f1250301d2092050000c5408107003020700c04c60220290f000742e0702100134080c80c00c2604003241d9682000c03c200e0708483c606549442d01d80400506140c3c04074019020308580b205 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 168994892 1250 168993642 168993653
    0x206040818090708060312030f0f040512071a0105040c090e09071a03160503040c050d02010e03010f0b0306090307031b0804081002040305010b18063105010302150f0304 74
    0x3004525265811548400d040d41d80c2e8005014032a03440c82e61041d100b0301e00501094a09031480e00c111030661010000d0008080005910941c000c5400d001d028180c0c855151a6142403001c20308510b800e4008640c2e10100716a00040840006201e00004e040d071362118204002c95030f00202240102d0031505040021b00d4610100c1c1e941310728014180d510710b40d543c240c41c4c03504a005a8640c1c59040c800800c0000c030703400c0416046056180b030314150382545488e81e501000010a8003407188075a0405a002d8210ba01c20348210070f10314000f900034040300c0f80414041c00134041000c4400c0c403901811000840790324001040c0d40c1240e4255030380c180340004500004144191410055884c0d0800300000b0030164806c20842c1c40c2c0519030880140d807140340d070601c1d50031036080041d4103200e03050030a200015017a2417008142c00581c00c9610349080e1802d081c110303c455413040304801e110609490422404000d0340d03c01d90481e402560300e02c14a002d40d111741455880707150200509003c0a0004c900880c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 168996142 1250 168994892 168994897
    0x3031d0613111201060510050901080109020304050a1403030402011d01050d0f060b04080709050109050f0c0d1b0c052103011a04080102030a09060b090108070b21010602070501020d0f02060408 84
    0x40c041d202c8040c1100840d400303c0e8603801d044010110a079181c03102045241018010102c3d444080d10b051400d00c01000300003803502e2018445c6602c40c940110224050010912580c01311039402882d00f0b95042540341010b449030411181640031540070401a103200d5030448500d000284140d41d034501e003040100c000c0005141c16142d03050740c00d039503d1010a03c5c140e00030060003c0c00f070340c1c001007021620b020024026141c0503040b412810341420305005201d1100c01d61b29030826040c540c0d050304c408015100301c0003055004c6902e910b1f00011082c503c507103604060034480c81805071050751702d1400d030394102c1d441964007508240e00c403003800c200410030600501604404d80040c42480d0349002d40d1025190b080e80c0050b07401c3c0141b140d5a880341d1040118900c640301581200b52032110039585071250103510307464030348508590501c000a00703041d40a5070500301001107880e161035449550712030800a40e200c0d103600a0601501c11072071020030031800b5200000001000e54001c00301580c8903920784074280c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 168997392 1250 168996142 168996181
    0x12031303020c030601080102030103050d02010c0c0204020304020d0f0c0501090603021218070f090204050f01020f070e0601090308040f081213051909050f0a0c230309070b04030f03031d06 82
    0x5000c1d105400301c1966061101301e00030820078001603200c0d410740c00c0c51810485a00800425a85448042170209402202c41e0000380c0c3c04450040e02c942d95030010805498813035000824510960355000c007003200d800046003e581080ea110314a0310b4071090240c08911403070014004450194000a0605803003410f0300c820b01340c7c1d9609a4a03e81d41d00d1406640d45030b01500b04071042e58004c03c06003c02d05041c81c2c084a010800d2004000c9040201049600d4441074004e1000d4800354000250480e4011005c2000955110003d05e540e0baa0314000701c8c0000c1c02d640245040c034002c00f8181c072520400312054910340a42c40903400c210078507110402c280509444180300020041840008180c1214072480744500142070f00040c03140b424400c141c088905c400800c00a001c0b50f000b207400186070341c2c544403555040b100d02c110340d6616000d581c545002e89070b41c030020685000280100800c0080d03810248024802e8905011910460070740c00d81c0703031100e0115000d85a20400c00240c00f412138070826440d8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 168998642 1250 168997392 168997397
    0x20702010c050a0503090f01050901170a060810050405191a1b040e070e030607020c010c170a0c0308090312060d0f021c170f0702060a02070b0d0b090912031303 70
    0x507154203a9505042c584003030b0040d50f40e6040400d82d440703036007001c084043c0c000302c091034124030b0300320300d500084d00c0015504030700c00c002041d903000107803100c869520943c044c2000070100c900c181002c41749000a0241140c04075242d0040c442e0f1240c004440035a1140026802030995101c0004a030381d00403600f000070581c0301450801643e5003c007200a50091000c0c000810b01d01c4018030f41103034007130140c0d00c3d03a43c1c06034000d501600811001c1540468040e550130001d203020010780d00c05d0300700403441c41c041c40065a04103000003601a08150044049003e0a21039141c19956550b804456a2079002e01c000d01d4510821781000582146004004840303240d100e480040c0700b00d482d90300494489030720141c0c40048030404044110501000840040641d140d01e04402d15041c00030041d00e00310700a00100a0240720041112424103001348082005417076003010440d1184d0043c2d420341c016141c150300c000e0181800300c0c08240b45c01e00100d07042828190004800d4070310b032140041c145282070300c907009608 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 168999892 1250 168998642 168998657
    0x1050703020a081c05070804020913020f03010f0624021002161205090316050d0f020112020d020d06150c0314040806130b1807150e1917190602070201 66
    0x61081c101900070b105402c40f400710761a107044211400c45e8000750610b82403064960130000140d40c2c3c00d440300e0b40b201240341145001040c03440401d00c8802a00c0c1d945d40d0550030700d01c01130141c051540c000030868044108e030100e660440c0c80b01214030030318850980016081030201e040014441c1c1c00030051211442002090031580e6241c807178150840c2410100051000501096285006c100b150301000c9600190410107103024001040074200c00c000030803c0e404243c01605586c020146010a008121015955030016071107410080d849513400d94011854400c006c90310341c00701c4082c0e08030003100f51601c4224012175101620190708031108101165820400461003c1d0706201e4207010308001d420b10040c042c0c4074905114100c400501695140d2550903507608010070024400003141c0702d18480c05144880888202c1c2c04036100030800d500700c2c40f94920001c80311108002c0f40e08444c5002c8404007000c0020300043e884103044403100061000c5180341c1c802185680e4018010140305040100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 169001142 1250 168999892 168999913
    0x1140f0c0a0f0905040e01050109050117030304110f090f01031505090c04050a061502010501050f061207050903030d050f042003070504021b0703080304060605041b050304020d150e1207110105070302 87
    0x1019540c6c600c80320107031039440d440100008a0f4078020b65014041403192856032600c074070000daa407808010009080d200300d0309101c0200303803180c403404984000060211251450220800c4042c91001c0c0700450b1581150300360084404458031800d40110b12a002038440c42152400304000f814018040c0613500e561020000b070003c200081c0ca100410441d000032501c0e602d00800c01001081c0308204c00e0280318100080820200c481003001c5c1e00a5507400d0454a8500c0d240100f0302d0341c0a006c11541c0d81d58070308014411400f41074080188150b224100740c1c1c3c00e009105100076180c1103c40440c9406034001c075010f00051409401400656070b0050b0030211b8401801c06403443c3c0b00c2c80d03504c1540d07a48000400c0c0310920025000e201301400050382e042c4166054880d410f1100c9151480075410408080041070441d91303510f103100c042580180340180d881011104040042c8011101d01c01180705084c00000e030891810141e44049800080380d5020603081001036409a2044800b10f045000f000c080c1d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 169002392 1250 169001142 169001149
    0xc06040512071527030f02060d0f110c0c030106060801060c05030c0613050d0302030709090902030c030607050307030605190302010507260d06050f130209010203091201140f0c0a0f0905 81
    0x66051105640768100c00b00329801c100010714910042c0e203980744451300140007003003401415101130f542c141c034256a0b6000308800b03400100722800d0072017007082c20220007d518406040141442c00c140f0015119100804400c06080f9844e5110308800318031024010081d03203014103188040c1901950980c2d10f0b04185101103401c0840407101c0c440140d401040480074070404000d0804a02074138142142b45040000b0080c040404030700c5440c0029840f07664040071501d0070b01600700144406400c807982410100c1c00648944c10845010b40001e20b048000200b9190443e1450300c00c80c5284100c84071181541c00445196200003c00e03a540d040500e04803040410b0385034110380005003450025213401c0d03030b91403040c00d40351668040c0d441110800903ca6060359a5014122036440c2d440e1f0050781e4500b0840141c0c2035008841c88079604c1804c14900c28100c1c030f419001000304a15072404011641d6400f004001e0b900800e50b41a4050300e002d00c41074504502030030580c2c2c040c0300b4a040804849a842000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 169003642 1250 169002392 169002419
    0x20918060316080d090f0f180609020304060914190b0c070c0b0a09140f0d0c090204121101140703030b0406031e030f09080a080d0b04050c03040c05030c0604051207 72
    0x80c0020303034050981c0703595050740305c400c12015026a01018005c24501412141ca490a03800b4001d0050154148482a10100d9110f44000e11400c02e05644910382401c081004201080c0143d6010010414401081c1c0c40072a108514800c92014000215440c3d120030400301c078000d04e0240c444408100e4840031071860030500c2c009104400506e5951220288001c1c11400e541d07100f010b28540c19205000d959803200c0ca5001310a20a942c040c0010089042506400c071181d801540c3e1684001000300304078034020180d45000d402842c0303440e450400700c4011200c01032070b000c1e03054005c0c400b07010070390020f40b290700500400c40b0010300c0031a07216201d80350042110000110382c01384c500410440001c154118a0881d1001030505001c60140d01d085d234001c4e00d400c41610000d203c2c02001600c02c20345095648850180740c000b81c003c20180c40c08038411801d96009031010b507640300c506a00001c3c1450000349030000f412000c2c100b58100351410080c42003885c6460940303505401042004100680c21425 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 169004892 1250 169003642 169003649
    0x915081f0f17060714030a060f061d12070302061602100f03150302150f0d020a0c03120605010c0b0a0f0e030901170c1b0a0c08071503020918060316 65
    0x221041050b103014448028078a6420030001a6000f11040005040e001011074039032404411344030345d90750307598540200149020340100941243d450404601c07603038043e107031000d0000c103072080e5140c41d010b2008121585c041e0344000c10090740011010b01c01410f00c800a0208122140e2420007003040c560300040c1601100ba4200c030008142c2d004c801510340c3c0c107000b0000d03004030080d00c40c2001350468020541c151302810580d0381d040c00016013032000a1040c0c080300d45400c3c5c81d00045450f03200014009020b4000e451080d00010701c0c50361101421043da00c584811074105842f80d0b0210440c503582c4900300c1c2d900406000155175900e004210340e44849c0202400c01e100368000e10b540b101f03400000340000032400325074402c0e5441d4108102c0030a015808941c81010304681581708000140d0071540381859a48004002000c420b030b002440c1e00d000200d01e8242d603600c404d0031050306c082c95070440072401b40200c4580d000b000303a04401c0d0b4440441c103819400400240680303450300400c54a8144071200c6d0760 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 169006142 1250 169004892 169004909
    0xc030c0905040903020d08060a0509090c04050702060c03010306200a0c0c0902040614030a0e03040e010807051203070f02040209040213080709050603030d0c12050103050c0306070915081f 82
    0x210808119032240000c0040c0c201120b0401000716a510002e5682d068020440c0900007904042921a90345003030240c000c0c036005101540d2403504002e01500c5121078008035024a05201c0860003c5002040e5940300e0640840c159003981c2ca952580d5010b05808c8550f84854003910300c0ca843c101c454000148440581138480007030154192030704a840f407071641c1c01a10788620621040c4515030340110b4260f41203022042e02e589a840703802e0a90700600c0030b580504a82e02c0000b800103904421440d03414100e8000d4410368680a07951010300142600e600c0000c40103030001c201020005120109501400d80094001400d000c600d00c041000c9130712201015407512090700080181f00c2e41000614050701e00c3c984284100c0c10301e080400d551340103181501d015151214000c0030307114851100d62a940d00c03080010f02055039a03007400c0d42c5800003089181c0c042c1c050840024101c900411490b012604244510f421014200c0000c480c80800a8888240e000242c46000c40960030742c00041302910390304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 169007392 1250 169006142 169006151
    0x22110301091506080709030b0603120304150e1516020c0405070c02030606030d1e050d020316180308030106050d02070501020408030306030610030803060f010314042009010f1502100c03 81
    0xd02c1100b1061000e5021808101919003001900da5101040c40c0840780d00140040168840300006414490f950072459101e0b0030201c03c01062200092240482d4880c4400400c0780f004070125084c1c80ea003140700d2100c140341000c0e001c2140c10340311003e421608495071040d04d95155003040010140c550139140b100004246a410314158a010300c00550003000440c0140011046500c01410005490030240c107540c28406540c1c40040c0641c0448040032a400400c40d80e038070302289002030003507120702000c00140d40601003084805a01065400396908410018110303071800600b11407551000002c1c45025400b40510f0300000c80900191000d04800b601031070700c03494100c091610307201d4010080c41d8480014201040854401002c42e074000303105903480d4400000e201c0050380070308203010509000040020400060020194809000d0048403400280b022100000c1015400c420b0068070407600710780d6810404641c00203480d40700341c000b9005a0307140040b500b40003812181c0861040c0c0109444 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 169008642 1250 169007392 169007411
    0x90306070206090d1e030b0316030f0605060d030c200607060c0e1e1e18010503010c0c0308061c080c070e010501030c020c0f04060906030c0e0a0603022211030109 71
    0x113000b14294060f03545811007005020b000d0003d108403007441080305256071440d84045507207050086210001c1c60341c0b03441e010280c1c0c80c42c000c032100003800c1081c4c800504d4440440c4035842c1404030741d14039a03090760392850b141c0440c1e141c1d5049901005444020800000c09410f2240ca901c0c0c00340a0103401403100041002903040040c7c1040c0701c0121a03441000300c90800042100c210b07440204004003594542c1c840a003607070a402e1410100c0b44d0103a1700c400c00d010f0b41100340e8201c0c130180d416150706a000740071503640a84190340000100c0d0004000c541d802002600b04d0800d403c2d00c41049840c0c21750004d00c05441e4445a40310340c480340c0f28030150b40080405201040c03c1c2843e09004100038a420018251100c2e4020b44510700c3c1c510307041c811400e449018101e6a00c070341005025003003800d0108020343d9a0704d49009081c1c0071b441445003204821001804000481c440c040c00c40e0f4014021100500daa001e501c608140b5200b50f0f9003a1039510009000a031000501440c060700742c0910019a0402c0c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 169009892 1250 169008642 169008661
    0x708280f0615050d1a1203070c051e04050405120a0908010501050105070b0403030b0a0317040504050f09060f07270303080a050907060e010512040b0f0a09020f010e06090306070206 79
    0x30681140307010074840c1081d4441582c1c0801101d0751341c419040700280341c0203c160081059080003e8480d409031400c0343e466503811700403005114503407280620042e02960741d4103121450045015103000c101000c03a902105082c660015603015111390196007410b0b040c1c14444465400607c1044c1c0007505d00c280601000c0310901c929400340c030007400c1c05410f1030102e964030b00c009280140001c02b056141d5400d009980c4803a030203440036503803040d59403800500c034071001c0c0e2886c1c10520450b4030460400010800c4280b80388046401030720306402801e120303900d81071000503101e0701800010402140000200301a14041d442c11a120104c4248500b2546035040040c44210080c00d0418158035020511514010016903001190a01c0c100b25121011400040c0c54900a04024001c2010f0040811007040f00b01025a4800e03080c2049200703650722083e000070219a8510ba0003500302e10060704040456024100c80898010005c0c00b003494078190201003400c201049d9420f1016a00c9a401d00c0b10700390 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 169011142 1250 169009892 169009901
    0x40909030521060d060f180501270507061b080d05011a091806010903060515040c020703031b080705100902150703090b03072304050f01080405060708280f 68
    0x2182c80540b9126801c0c50390015040c41c400c0070780100416a680301452401003107030444210400200081c20140c0c540d4201a40a00022004080c2c00e200300040030110003401ea43d40350030140c00000425025042c0b210549070003400010090070b0411000c41000050306000041191070b01c0114081340765494551034025811002c0c046580c42901402031040035103a0551880525007449030802c0140c441e4001131b00c021480360800b8240c00e0405040112007042000341c4040140d05803010052150305810072a162040c6010090004400c500303201030000501e222400741c50301491460345060821b5403401e02c1c1280302924a1500c0740c440400405515184041c0c0c0c1c001c0050403074507450030071a5503004003241740e83c4c0224000d0010100210b01428400c3c26110f800c407d02000d40c03032400c0c5595004050313581103481003a02c10380c0c0328a4080c4855100b074500c0d90240b0703030000c0188090f4071080000d41748100020040c0843c0320b03011080d40d0202001640402215028040000d95980c03609242c205a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 169012392 1250 169011142 169011187
    0x40e0112060615170402011b0503090307140d1101140c0d03052503050910060807080606010203040f090209030a02030d050d0f0207030f120b090403050a110d091a0409090305 76
    0x104000c800d404a40b90004a400c50010524109128603030b40e501c016180e8091a20441c440100c1322346205080003030000040c098031070100c04941d141c503500e0388000414003507030401d82e8215046c0021240060342d8501c80003000c0d003050400706800610b141c1d02c00c103581c101d49a420542e03070001040d0721102e42c06108444d0000d040916007040407800410000e20542506040130070166900d00103041e80c0400c0c03201d130081140c001803d010041e80c90b030300f135652001c49024507903d40c01244003040142d800042150202e801404800d400e091030714189800a4010f020899007501528201d040140d5042c454281c1c28801d9071a01c03038850f906c510307800d421940f8641c00d0710381e030600c10440c0d000403d800607103110f111800c0b8030f080041c0c41800f0762510045c100b00440c440e0401840400c0c4010140c20001518581007182d841003052941208103030368400c0c810400b000450300303002c02801102d08108100070f40401943c1a103180980d502c1c80e1104403581003509a00055020401200c101042000c240c401b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 169013642 1250 169012392 169012409
    0x90f030914040e0c060708090607080307110a02030604020f031e0105011e030812100308070c09051e01060f02011410030203070b0a09090b2b140a050a0215040e01120606 74
    0x403520024a41d41c0e500080c008580310703500100306c0d2800c00040c039084851056000d0202038030780c62145070140d044d400507585000840c0c1c1d03c1c41401301e0803000161111040e60000d00800792500c9603000d220006c0300b0940e02c1034043c014205d125441c5808020320440203150b050000489600d4081c400d2018101d81c15102750342c08401d101080402c42081c01d48a1428840c07035900b410b81c4a40c41045640b544503880100901c10100c0c00c40180b0115450703510032111180f50500c46c0360340e10301608040401e2400300700e4500f039a02d401400320610072100f0105811060000207074070705500281c80d80e094021203000c540d00c10120303c00e000318201441050018003030b40307405500300f9038600340c054480340703d0707021740700e081541d40115402c02d07030b00d14414450500705000c224031310491442d051aa81d2520700c00540e8259a03082450001402c00134101d1003030758000c4017900051000394200840c401b10074044e60010302d02400702007115084452030034000d2420b16143e4800c0c01c110300c1d0032019615550b000e07401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 169014892 1250 169013642 169013651
    0x10b0102030a14092202190305090604030f02160909020f15121302040603050d0809030301060e06070c05031510080c01090902072d050708010207020f01080a090f03091404 75
    0x2c402d80c000c070302d03001d1211200c0d030442e0f2907034802404128042c0078a000c180056500d04603021080310f03694000e10784c900d0b01e884400d00784001a8020303415944c003602c0d2a155a030010002502003071187d16045101a010700c10f031a0a440d00600c0600f00440315000502c4107550740b4030442c1186804008560a0780341982c0b0720308400c0c443c03424144940110b4102c03050a044450000e2000442d45d00741d103240302c0d03000f84204002510390401c1ca594a4561240710045a0440042a510280081030307904944282c2d0b0342c042d00b07070041c0040c00000d40100e0011034105540d000046155603043c0210618030240042d1940e56141001624106010725800a01e058000540b81502039921085403c180c1d4003441001d0707514201494140c10300d1103080c1d11540d0040140343e6403010300c0c1091080008050085007100c0d840d6031038a00d107500301d101d0345200075170041d45181e20010341e5010701440c40d4080d250300c8001070014942c0c0c440d8810135504c00f20840010ba038800c0c0601052840e0740c840c80010400b51000c11 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 169016142 1250 169014892 169014907
    0x10b041a0a05011d030109080d15050f01050a03060b03010311010206150d020d02030a05010f0c020c0913030e120d03020909010e040c09020f04080106090209030c090c0d090c0e100503010b010203 85
    0x504a403070038081d043c10407001c403400050a00049841c2c20b0b1046014008000f0794401c2c0c21300c0d100b19044100b10b00255800c0c085003003207082c0c1c2a030f411016140d008180d0b81510068000551b42c0d580a140450281912020001003040802c3c004e14000c0d13000311142018a500d0700300080c2400c80003042542d140703480d8440758110741c8030319206025090303041e80c05400102c5c00e400044d2900301c120388010003560900c003607981e001c6160307001416941c01940032260781c084114100410f6110840d4010581122821131a001c24402c0c80c862000386009484504c0c0c400219505c54180220609034002194000508c0255801e000850900409281070010401c1c101b6940f020b000340c0c00703885203555268000c105240e5a1059200b00e41c000e150040080200a03920030100010f500500201d9200b8050540030700c202c0d05250410030302c1184818040ba2030907052015401c014120700c9001e6805020102d00851142c0703841601e5805142d49010f40b0303091528100800d0700703440041c0e01450440d00184500c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 169017392 1250 169016142 169016149
    0x60302040b0139050d020c190303080a020702040207080d06050f0405071b03030209030f1e0303091e0109020607030816030608190f020a1d010b0406090618050a08010b041a 75
    0x2541260042508584014001c3c2820a50403070070303160241c0240600140d0740d50701d90f0009500d0350070f24800d40300c241e10245110b1119090000078480a0f01240104d4005500312450f03600401c0061b100074001400c00000351500841034201408442c5034a0b079803101071146140c21142d020881d0b80c2240c088c05a45045440100f404c0c101c2c02c0950400281015180109402501501c50940006d42119401c0b03c0d0301400075038803001c50356041410303407140305080c025003c04070849224241e07a000400d039803c030034425000f0b1250040300d200c5031035507140e00c403500607980c0d00000d014a500075581d9019074240301d81c13601600c48070386051406061500301c041010a2021680c004a915000541849040d980c02c00d202645201030000f9448004014045003e6100340050a11122243d08032019070380c0729406506244558060200450061001000b01d20f108000c044480300e802e1405c00c0070155035101045060300e550b045590310742d44030b4940d540d040c03c0c2881542d603040d641400d006504580740011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 169018642 1250 169017392 169017437
    0x121012080c191a100b1c0509030703020c191a0306010e0d020109090b04150e240f0603091c030e0d03050c07111512040303060b070c09051305070306060302040b01 71
    0x143c01d0402620300150002030040307020001000348403102640d030141c10001a11080280c000100107528100c0490101d0500106603086550316400914040741000d0400043c05400141c0005468210002140031090703a142c05041620408801d902d0341010070000d0800303241140002e0140d05035560b4480982e90151030503048503400c0100007240c00710000441c006d01040c100c400000441c0000c0001c103580c4121150f4412002200360140200210112040c400c1c0b8078000b607a403100d8a040b0b007a9030307494031100070b54015600c482101c0320f032000e04402491808a412100c8040381c4d50b140d0f4075221000c00e000c01e580c80c04035413800300002e161a1130100298095580050107100868071a018191195400d80d134130348142d01c1c111902c0d010002041145d18030200d83c00c40c0040d0a02c040003800000701426201c02c1a0302000d66484a42000d0090f0300411004040c10741405500d81c8001c0072980511100c3c02031800f501010541c0c0c1e003075005010980b01c1c842405410841d041108010b4000d00414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 169019892 1250 169018642 169018673
    0x16030c03020c0307051605150304080f040504090c0807060e0a0b1e03010306020d060509132d080d05090c010504030609050106090e0a030908030f121012080c19 70
    0x400182444649004800a02800c00002050700c0005500c1e4240180018500d04400a9501c0c0304012601d44e0148102c45514240700303c1003590500c04200010302c0e840103410341a6805802909041c4d41e80001030a03900ea080007a988147c100000344180c2c003050040c280546483d0038555075002c9003101040110b4954030070005000030100303a5002000c03001110b800c1034445a800ca41d240d50b1a410140001d43c00202e10f00304c4d8910382320002400d820030a040c188038012940220340441055110341d10f1140340483c52070700c40d407004110140c214000d0030700e10390500d004503203485c1c42d070300030b801d200c021a41c0207042214683d12207401c480e620707a40701c004c54040d80d60110340420340c06820301e0510b0260006810446419080c00d01d03509924800041c030304951070196071102107065642e05401d8580c41307141d07201d40c4020b904020b1102e25115032144180c01054039410090f00c0c0b5070f41c0c1d11051010704000801c4510602c00501c0030841d040422000001e12605a40d44181e011103030364041a0744500e06 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 169021142 1250 169019892 169019897
    0x12050c010e0f0a240608060a0f1a010503040609240605041109120316200f010504090b0a03080a020d09060207050102030a0305180d0201020301060909021e1b0d032316 73
    0x44411354800001c90503165030507100502404003c0d00d0b41d040c15140c0c24115a00c0d09030318500240d48108401c0c6008401c100181908040409161900111116880107105039070f9135440340d02c01c5c00040c01a4181540c0c104e90030640207982030201c0440010786003203a00082c40b82e403c003003c540001c7c1c101412504002e1003250561030200e038000e4440d04500403002e28594540440030060300f808540100340c5900d41aaa906c0d01c41d44075114104008000705041050014500380001d00c0403045660040b50b680200500d0482c817640c1e00c2e540c3c40c4065106041c0800140c0100000f40c48540d0024640c0c4058041400030305130850606d40000d5490250310030f280101070700e481c0803c0a0001181d031507080d080040043c3c400c0849002d001178041c0d40203104d400300187c032605000603c00902d10a50392600c101c0d070001d4843d07082580408105802205500000c0c5a60b4820460903000402401304a10310b10344004c1240c4840007000008130040035030701b111265580003001564403041c00303405600201d60 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 169022392 1250 169021142 169021163
    0x5150306010c0c031a0a230121020a090204030b010501050a020d2003070516050111031b01140907030c0e060d171c050603010c05040b030c0a0c12050c010e0f0a 70
    0x6040480fa40140359001500080f064004400304003101d00d405440348108a40500080410000114021036080650100c41031031030300600000c484456035101c41c40354518072040040703103600003440d0303c5c8190380021103072039000070300f0001c100c050666940100003d080941c01c00b504c00001070345036189140040f0401560b51b40c9000f0080200480b40914040d440c00c070380d01c0d00c085107085541c944040404070703810480388200040962040b4040b06070f08840c003010b182840340c8480c40d0007611892011889880d501e50300b49400c54080000c0d030f035120300b40b4000107020103403030341c14400c4034002c0030341288480d68404020044103440380e28000e000e859100d40e40380c00010003145007007a580202280b80c099414068540f000c4852203030002401075508030002c118440901900380c46a22440c1304030a490b0a080c400108007100070401b0b40320380503041c2819035060341942d036000c40900401c550000425000b184411505c01709104408010401d10000c0c070702000c1c205c50081d07803481d903500014101c8561 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 169023642 1250 169022392 169022417
    0x605090102070606060f081005031203090106050910060806091003080306150a11070f030f080d150303090e060d051c0c02030303070819140105040e0a02030a0510060515030601 77
    0x3541290100c2ea00300004009980e2100401420304050003641000504400080780c5a0940c0c40c07415400c03924000c0041c90288280015480d840d0401450015555a1094001156102c00c0c0880303121b0b40d100c09c00d041003503081584c0a0304601e0090310a070f000f01c6141c8200304481103142d00760400da81c0c20030b4000e910381c1e0350800020810782c2c00e214443c00e1034101084c4060641c0d0000350685103007407850291000f131a02d1300300102074940c55200180810054400d0f0074040748154008000400c02460041014030040c180c24090300115401103000a0508500b040b0004007080303002e8000348211840200b070800b94552070340e0303030741080000e01c0c40400105104460a0013007510814041d40178043e2505c0707191012002e484180100c4141040c00a00746119580d02d68610401c4048160b000340052603900b880c0a00004021102c044251403140303404040242c3da0402942845520070340c020040da00c060000d0500740d88039540900d004162007640c001e4130345400d0060340c0e8041020319010b21030611 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 169024892 1250 169023642 169023661
    0xe0708060d0203010f0f0f0e01050c09040b2e170912030702010603020d1407170a0b06010c02030604060501061409030303010b0703030b060a02070312050703020c0f04020c01020f04081b0d0605 84
    0x400ca85d141c240c03d141c0b4103c40318068241d00424004081c105041200c2406600745500b40d034000c03034445481140800c00001c95280c1540440301c4400081e10300c40080e41242840d104100c507000c21400307043c442c10005031115034085131780040380400c1d60800320141007000071203541c1d6460305445400b039040480082c1c4000c1c07003580101e00458000f004a600e050041c107003004648181404501305005020b0b02181075090340009901a80030340340108204001a01e5081014901408481c100b085071440341f00569020000070340103270b009640004a552409070044c003049501d101030b038440c031030a20940c0309070754000c0150790460b00031004c199910102460304800505500c1c445550021010560141c0c50358000307075900a60b885030404c01455404d500050352203000d242d000800592140b4110307582400e05090b60911480080c00c05807c00b408900e2460998024800b00000b00c1004541004500e0341004000c65040c01d0540d1540252038a10109040d1113105001502054031071000c40d840c00e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 169026142 1250 169024892 169024901
    0x180809150906071a060910030b1003021e040b1f08090c0a06021c0c0f260c01230103081614010f0626030d0c090302090906010602070e0708060d020301 66
    0x401003900c0e039908440e281c03404e2403004640c01401690301150000311070f800c0c442c8820703001c3d10580b04064001895a5944d0303a100400503c6090b031482d034080000010303124402c5290042e0321076100c0005e1640740200b480100d9007031030f854610801902040008500a204100610b09024982201182d0310462040e103004c03554001c0b03d400003400c89001900f00c5e80030507030003103550040c040640000c0f90018111004844401c01411482d8050308140008940c05046400316540010303150303030361034160300700ca030103400c24404c40301070340d4403420804000d0042c039aa95001c200b984070b035110503504503164403045004801c8000c4c01100585040c000340f00600903c0d0b10118901c078000e01c040c0c4440c00030704001d040c461003002c089041c1902c01c3c0f01044501607010400000c0b07200118103016076645d00c0f00141c8010040300c4184001454080096140c1c0b80e00300d446030a0400060400c1d501d0000000c0c9000704036413020081c81988800d01011a5110319496000b0383c00f01d55281038502d5a00010f030051 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 169027392 1250 169026142 169026157
    0x150b0d050106020f0601081506180c0d141012031803051b031c05130f03120f0503040f08090402040801050a0507030605060403020310090501140109050a18080915 71
    0x40081981104480a40c01480c141c2d88281d003900c95041c8000d507034590f200c1003070140e521143c11140d01c00c0c3d44540c941d40030550011005180c0860030003103180c80005000d05031b82451840d0030004a0358003a14080c0180c401100840c40ea41c601c5141060b0007103880006070090081c485019510b000c2454410145020140001224240050b60b2498007640d202c52040004a6500500d034a1a41c21b00c2c003c5905800340340b406444100c40d00c0b054030b04407419800310b039100720654030a010104010b11090501000f0303500c110840e030005041c0c258003521142e416001c00040041c100204800600800d5035081c2e255405104191103121100c0020040d02481d04858025880d02c0100940c2981c141c2210707000c0c2c07406440800c40e1584a00920002c1d00c82c6000c0650154030422002405100d558000d110300d078010400020505401b005e20340b1001e100303034425881e15803203d00303201210085101ea9000001da01e805c00c1004642ca945840a40c003403210b000f0320500703007040307512007480c2c464040b210107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 169028642 1250 169027392 169027409
    0x3090c09070f08070e01390f061103190903030207060c0305060f0102030309030a0c0510020f030406060f05010e0d0c030501060f180b06030103140705031618050402011215 75
    0x2038900208020181c00302080c2c0100001e45030340215402c5405500032240d4888107a50320443c4007045551a100340048200300380a500000241c844030208001200c1c41d590321034416107522000d1400c00006483c400c0c0e40890401d1001c1003405200c40750341c2c44203518400030750f8000c42c0701c40c014102a0000e028481020301050b00709151a441035030f050384110b05c074406c101c1d9400548180c6500490780c0c1e003c1200c100c1816802049180c41c403038010031500b203155205108452141749202c1c2110141e0f0003f42d801191110040b041c80100601030040c0405080c3c1940300070070852801000138949a2108807440c005c15229001d6824060811340000c061608130b0b000f444140d5a0740c800d1040488244900c1c480812160350049403032189020324003000000078400c50840e4219120100d030610308015943e10b07842000300011300e41c0c03418070110750000850b40c09040458908030346950307c0702080c00914003844c81e1401b0000180c0e0030032040350254002d01c0000400d403c1036400213003030306015000f8001 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 169029892 1250 169028642 169028659
    0x807020a0f060323070e030a08073e061b0a0302030306100306050306010b030c04030b10090b040c14030c0d06081b18010510090902070303091b05010507020603090c 72
    0x32108101c2208004841443d501044403840300048a2160590185100d031251541c0d0b000c1100c60b071044000c0080700c90010169070b0066407964a60425a210081c21118046007015003034030040700074a1400c1c012042000425800012030030044c1c4d6089214001d4464600416411040241760880c003040f5003200c0100d0b81c030100e079420040d60342e401c00c968061047c444001048142c80c464001c0408451000e40106201d07404c0c044000d945410040c02c401d05d4070070a020010200355220b1481c2d0082943c00181c030041420403650300b090300c1261080d01d00441c10840400c06d000d60001d0f81040e030400d80b02d00981c881e251200b0280052140c0107010303003041d00b0004007151803800440d003040100d16080000c400541d421050100d410f000c205100c08000390f14004100508241311115114003040c41c080c5402526440740034200d80010800340c0009940d11805000c0211020072660301b0b614801d50401c0c00b0b0700e8580002c00c03d00c04c1800081c01030901102048190a0070170010900030b200600500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 169031142 1250 169029892 169029899
    0xc091d01141009090c03020f01020c09040b010302102604030311040308120a0b06040b0d021b060601140f0904090f1205210103150c020705061b0601050901120f0807020a 74
    0x10507104180c4098080d80309400700050110740300d1203041c000720b0348140c82407950361440c1c0812900651a00d10103040d8080c0e654400540d41e83d54068074070445c450010346101754114014400d070402044100424042c0301d40000c2151103415072400d68920005000c00d10542c1d0318501200505890451500204000705000c000c10824401030100d403085850042c19030340c0e4414100090b82d21154205400407420001403003103542074801050b005410701c0000d03140004000080307010080070404851690009001d1019960b0310080100c14001843c0c902030504460309032688081c81388064403445565141c900c002046030820807400c54942145144100320703540c0c100600301d0380c003026004030b0700e82c8826035406041d40c0c0342e003249058a4000c00c01c0c00611580100c4d450003044418064019413007405000900c2d82e48a80042c41482d041c490034010342e000c0850003624104041c0c114030322481d503840043c00303a50024038640755126040340000203c04081c2c20040504d1081d00700103500041d401c0300c0070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 169032392 1250 169031142 169031171
    0x40f050601090204140f0609060d02090d0606090c1d0f0a0806090a020102070b031005040906020c01090302030c0d030501050f060a090801020c0d14070b04140f10060906120c091d01 79
    0xc1c0b08179800301881e1403100a5080421040d0b20380c40c6c5c2250b50002041c040116503003800320142c0400f29255400502d0010040000b4a41e020305140450700540c40782c41c01d000b80d0310f041c040c0d030344001400d0801c8001c030020050020f94505043d046180602d80306c0c0b2404210f41da951072424011b01a8900740e0304181080c02643c0d03240c1030b240300700703078007501c44c1a0340016078183c1e1100701c0344034040380141c0b007801030300b0642048003405002a00b80c4066400340868185644203110b10240f0600c250011503454075041d6400d81040924481e0100f458907010041015071030b43c101100358110210749907a95514080819202d1646175046099030750320108030500001e50010309155607810350b403200392000f598036488150a11650302c004143c2c071038100100b000102c0a0700d40404c13821200302a0b60700c04241c41100351400310340d4042c0304501600c47c4010000c51030140700f14800303000351035500302401509440303141e4021000e105502c00c01c1e41d2524590700c400c0c91400e07031403904d111420003480404c941a40c074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 169033642 1250 169032392 169032397
    0x5090a0312090b1809040f120315090b0a03081b0d050304150c050a0f02031c0f0b010f02060c0d06050a0e040c06091503020f0d090f1505040c0509040f0506010902 71
    0x441d408108a1200440e08414480940d245580c25032602c0a00281303182c1845a074600180084440307152205240c400914141801d0a076102540d5001400d281484605c2e4032107070560784a070700428940103041c4d11035142c1c8000c102c1600d8022550694a102186944080003a0001021801c1c0a5080300600440d4084021800395002e2180e0890b0105410048003c8030018a06c14000ca2810800814100d021700440200d02101e40162824405d0394014078100009146291070090707075641d92900c0d503990f030b03218640000e4000c2c0381014404440d00c1e0040e40c1c03210058644905404080340c0b901d031140507074100b14003a000c080c1004850310f90322404a05000c40544040380e030840490404a9041c2c0324101030411910b44103400c50700d86640c1700090b40254006419000640c108200b5909070035064025541e05512030210030f10f40380341c181010307002c0c0c14100344000c16103070508080c0004100c010b10356000b554022510321040f40c88915040040c00c1d1a920001c0c094000e14000140b04041c9901 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 169034892 1250 169033642 169033673
    0x20a08011b110303070f0c06110a020f1c050724020f03090c03011401060507031803050a0b15060301170f0f06090d020a05060c0f07081909051e09060105090a03 70
    0x54104524600a000301d80f64041228080c00240076010061900d82c89510b0360310700310b80654400289040b107064110929840543d0002c0583d2020403070544d9030904024036403155041c0410041c40d81600400200036203c0c0d014045c20401d41d0390b642c1b016400d900c003030101001107407010455407401c0380e880941450f0021901c0990a01540d180e2128508040c01001344c640c914840b0300d00aa0b08000e0165040c0d0880c140503800c0102c440342c1806070000c28800103000d10701407030007031180120a240404000600402c09004011190001c0c5002c0e16030310180d90540740c00300d0b0003400c110303104003003213107003194403001c0d802c4d035100d07603600c03481d01d4200071452502880e8040292598110801c0083c1c0e610400950020142d92088001032010f0306020003822400090680ca40d240c44090740f6003170500d40104500726208140d1014211f0043d4028036410300400d030a4505c03941e440c16036540310740c100c0100012039000701c900030001100c50703100d05e04407207200b440246840301c0316840b400d01500c50395007a503 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 169036142 1250 169034892 169034897
    0x606040f030b0105120d0e01030c020a1a010e010609080604021003020705011d010f0605010203181f0f0201050a09021e13090606050414040b011a1e0c010501050f0d030507020a08011b 80
    0xc190032040040811182d1b1613802070749540500c400814011030082143c410303c10110701402882c140050b012002c603802c2e19000c0200c0d02c28550500052403201903040e03000c201400824041000050404101c25902c180c041301c110342c0c0c840135039100790040d114000000f0a0f0b5440d040f802c680700c1020440c00d00c1c000e84a203008224a21a1440c1c107c1210082d002e000c1c050780c001d0104034030100342c000b480d4203201c60140c42c502d05a4548041c500c00d21582030308290101e003201b5100d05006030709200d402d9001400c45800d0042400c3c41d008070300c180d10f1140c01d0030500f108908512a003906c2c0c1a001c155035490f2010204140308090401c10010100b90250074411424140070b0003541c601caa04060155401c032207048440e0340703000c141910405001c60321012101c01441090090015035445405c00382503264582c1d07a40e848000141e00711541600986d200f0040c4074003000762522512080244a039260802070b5031410b01c4d000086071079115521150482d820880612440c50b19074007803500000f00c58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 169037392 1250 169036142 169036159
    0x203070906050c071707050307060807110a020d140c091003031b030801120c18050906100305070911090409060c020d0c0803060913060501030b090c03120406080606040f030b0105 78
    0x82108840a2151060981e804ea008190a01c01c44103101c440780e25082049080341d031025a28004203050001c0c960190f00450310342800c118000b50003034403040c40004441c0180440d461103500144020b00514005090100b182c0300f40010400c04120407044180020300030f0a2500e0901c140780d40d981543c3c0021800a02d41070403112258448001071440355505072201d09407a07017815000c4495070391860300cd0780e501041c1c68000800c17401c2c60304d440c100210002d03000f040d1444d10110261400f4405009809106028503003000451404220075041d14610540840c85188200800156019800d8a95445444c00b4140403c00404e54072250804406070241c8100c000c128405691100c54490301400300581080069290703e051100c0035401810b401c15290208801e840b4141160026001160090418070610829100412141d101c2003000c5000303190680d07082d000e0680c180241d200d190180156000444c515585142c240c901905048060304a801d98a0401048207142803081d240225201c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 169038642 1250 169037392 169037399
    0x903010e030d1109100e01090e010b040e16020c0f03070e010b03040b010b03070f03051905090619090503041a0403020d080d050114012c13091101030e1c0201110a0302030709 76
    0x401060b030b0135903440200000400005e0410581c0d10074015000d0358100b0208840128040c0c920030110b602801d27902d005144c40d2402e03d00c02030b55212018081c400070700b40d6141d1850081d9400078440c002e510040e603900c0d03000210040800c0ca80513035500440385000c0c140001282010444000c0e61090740150f60a21041e6a00c01e4000d41d140310544200000600761009407801c5400780e00219040f00d8085034044000003025402421644140c400500540201e402d0101214050b120086900c0c0c0701c000c1004a10600c1d40c525550344521300c0f440400c02ca02a00c030610444d0400d054030002c0d81c0141510001422074648407100b644403002c0200c0b0140382c4000411782107980702d136041031014181c55070070044070040c2d1044802180c150b40d00e219400f41055694040e2a002142800b510306254082640c001c203241050f94940003014140c101032501c60a614005030004034a080c0d26500814034204102c201c1040b405040030340c2c00b5404a800006e2646c0314568582d0040d403084030b0998460340d82c5501c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 169039892 1250 169038642 169038671
    0xd06090c050d0201020d1107090603030c020f0312161403070b1605030123120d0905041103040c12050f0303160e0a08060606090a050a09051e040302030409050406020903010e030d 78
    0x880441c00fa0040c4d00c1a40080300142c01a004400306a50800803290307100c1d6a20702d030000b03a41064000710001400d00d030030001141821894499541c0d000c40191800400d000200c4145005150000c610501d03694070380000d04c41c00c0230081030745940c1c450580c2e54035141760070103000a00e0156034600858002e002d0020200344190b050300c1c184d0b0110b41e0100b0564070340280c3e9103002c805030074080341c1c4503608406010801800b00a444098407080e120280300074540420031003248c01d4450503180c074038810401c000001f480d201050b401e4802428500e0503400c0306090540c0b5091404009012501c00082403110a4108020020310030610b5910701c071011807584180b0003441c182d071094405940c0714a0200b040c80ca010005400201c002502c0500040e41c0e640004000c0b288503400b11414603615018001c01628802c84514110003440d00607040d41060f50307000f9501d114071300c154518545d4034400b01c3c00b009441e404690307903034100400a04c0200301c07856282da100d51000c0c1e0590011403821000e801c1c0d502 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 169041142 1250 169039892 169039909
    0x61106090105060306040b040218040605090106060201061518120b01050901061b0201080601021006030620070b0f04060216032d020a02060a02070e0c090103150e150f0d06090c05 78
    0x240040d01a0081b61241c1c3c0d00d0070902980500102e0b172083d200004050382600b1409842d00c582d000310004507640c07e044c0c40740750842c0c005401100071a41440011300a9031600145049030701101d00d441d505004403081441e08244442e00710796030490300c076040311040c0f0002c0c08849050b502c0403600e412480c1d9a501040e61098010840ca09041481c84580009036000c1c1c540b03658131450600507a00b02c00583c020f40c034103d0703505800442d40b095460321001c500744040f100d40c049000031500c43d80e25040d8551100101080c000340740740e8440c04490005001c100c0e9a07015a903035810065031407580b50b41c2e18a0081c02d13054400039400b1584a016843c3c03000f81c80d040122010404541d000380010b01125001d0004680c0580b400e08154030a12000007000e603200860785209140b003094594941c0381000004007038038509440e01d09221010b400602620101035215500010790803606000c1c0f03c403900c04903961188100c00d4592291b0b0070441c00041c40780c3e82e040202050f126a600060729910f5038200980d58 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 169042392 1250 169041142 169041151
    0x190b0f010e0d0503090409150606020a08030c090303040b0c0a1a160c050c061603090b070c12020111060c0403020906030102030c03040f060204030f080703110609030307030902010e0604061106090105 87
    0x620704410000c41d401c01c6a03411008600030820b4134034100e90000801d09864110104a0b154045040300c24101c0145d441244c02030300d0035101400b0240030540f161140c900000c0e001158856001400100071b076420001c0f9001004880495622501864403140e00d503408500f00f51082e941d243c101c814000102811244260781900c1d4640031003444043c106e5005400d01e60880f0b141c07184c1c103141d100e16a40d17103000d400c9250507038042241c049500e16000b40185000c7d0b020351564041448480d001036409608041960120320aa0504041e00c1c00100c480036040c1217110400c0c040e1109101c60708e00327800700034801d6034000e4031965035603118102803600700c0c8021a903a20030040c05201041c0080d1b071070565154001d0250801509040d161344548051139428941110300d014001030031320070503400030600c5044404d102c0141c40319140c905001d54403031100400480c101030b070784c02c1e51004680c000c100c000c241c04400f40075207440300d444440c05800b8078200d00070694140719141c00565100e80502455214 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 169043642 1250 169042392 169042397
    0x1f050a05010819060b0612061c0f0b0712061401020d020a0b070509010c200423011710020d0203010f080d050a350703150302010804230303190b0f01 65
    0x1003840740c0745402d1414540c2000700ea205450b01c040c0c405d10354800d00905000716507111580110705180c07080148564080000c0381d030981e07c0710203140200d8076803016020308582000381c40815540e4090102d035500f54130031107444010f1a00720b021034400498041035140c40d40031b800f00e0303a207142906802e994461007120010440551100021a00c612407030160002c4038041c1000058841203a41700100010044001d481d80104da06c42c6490f54a468010818803288401310203542c883d505044000d152414020415581d845883c4151190400c100c1003582e2082d10703104540302c44010040704007a600a03c10846041e210034804640d56001141c00c415464503516400d1900031054000c0e030301080309110900c40301c00d00c8821100003229006511510418400301d108540c40e004001074100e47d1382004071400c0b032800c1d040a00060760001011608a82c10000180c0119080814040e10f1402c103845c903010b07030001005025103c0c20820682d08816200311082c0040c1c80844188141c202e040c5a00500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 169044892 1250 169043642 169043653
    0x120c0111150c0d1806090b1b1206060904021818100614040e0903130b1804050c250512030f190b04110d1803080c0a0c051f050a050108 59
    0x1100b42e000d0005020034901c0c55004140c00d0807609600410701c11503003082d2917483e1542020700130403000b030040700c5e4421003084521070750141041c6146018041c0303c0602c40074100d05e0b80800c1d101d58540e07054802106c002081559607031400b0000310303074400038009002d024520b400c0000054007030403178209214a44002c10342e541e10b86082c0d800c0341d441448000e0b850060508020110f401c0310f00c0c00d4480c2c49003d5460045a80e040104c82d200d1000e400d0341d0011541500511043e42d10302d245850f00b0154000c2114007180741d8981c42d00a82c03840c45017400c031100e24010b030f1a41000380c080a079007aa030070f01d0040080d135011580620746c451951004440c40d880e00d2184000044000d8041c00312150720b0300c015107000603980d4901c8046002c99003c0e424004460b1030218400001d20014011041c5a20030641c100c0545c034031a99019000441c041c040e41c0d400134000c100c501504d442039a0780c0910581000446d21450401410300110359240140400701606000005601c520369000c3c490407074445200031302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 169046142 1250 169044892 169044901
    0x2150a0e06060f0619050403020310050124050904090c0b030711060a14130615081c031817070503040e0708150a05010f030e01051503150c070213020405120c011115 72
    0xe017644424508414400d0900012025850810aa0320009141c2c04009115414003113080290190150900042d0400d0307220104040e6000b4190341c00c0c48002e40300824002241e280c4071035500240d8118170180700000c4100314400c0e90041c81c00f8000d070007180941d400c82e01c0d903500d80e01c1542c80d44011648004644400300b41401115880c0c1001540a41000114846903114050309010568404d482d01c3d804580b801102d19540143c190305441c082c02c08201c0ea4a002c5450000f0100c10200505580514452480d04401950032140302980c081c059954544c3c0b160754510b50b4510650310360b00016000c000080c880303a000010144055401482c018405103440e00458070403e89100c08000c0580360964810042402d014050090122002400c2c0390b0760000141480e002c50200408403d030001380520100520980440e0a129010b0b251040005111107003803000e841a54405504180340603495840f03c0702c0402d4924524800340e031024100c0d100034078003640c0c60304130140300310000d084200410b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 169047392 1250 169046142 169046167
    0xa09120c060c290105090601170f060a030218041e020603041106040807060c0210020c0901030f02060f04030f0b18120705070f0321091409060102150a0e06060f06 71
    0x221600d44120b0104001071107441032110007001c2d005071207080d203e540380140510b1916941081c0d00681c01e10f400901450400d40c840c03015840904160005a04000410f10940345d10030000099034000d03084156482c607080115250242c00c1700c05640d42c8410341c070b0030503080d04509607555003150024425030840d2038948803824800e4455020982c800070030400013640d40414420100282259128081c101c01580148410381519981031000c54012802c801080c0e0364101840f070640350010501c3c9144801c03032010560500c01c03804d90000112010400000b0442e2485c0d10100d503d00c54810300f906901c8240344001c20210b40743d00140c4581100c081d00541c602c0e80d001800742a40540d04665503281d81d151400b6800301c1035041903403180f85c3c19000d0241010681d041c40c0f4aa001d61600500003844d100d51234510703070480d0303652078820220017000c100b55038400c0002c0d1042960400800b1030307d0824031303c0e180c024404800e0a5500d4092400024914503040507400705000300034080300e10700f400d44044c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 169048642 1250 169047392 169047407
    0xf03031b1c0b1305090a05010e15040312140a0e0c01180909020301060e0a09020a060809030d1a041b140301050d060506181003031e09090203150d05030a09120c06 71
    0xc154101c0c610011101003000c0f0342c002c650081c20301202401c2ca9280c0c0f4202142550400108002194030003403000f01041d04904c000ca074401d42510b860703843e1080341c6d92284e001c0c007000541c0c0c1041511300030a2203021350141d840382d01c8102d0078400b1100f102d112000103540031503102c13110201e0150b00d40e07020400e00180d030300200d0000f407000380002801074403605210440c4105031003007050507540e984007400b14141040030308082c00700390818031000d1411000075956481200280001035850310201c108058554500306541440200140b0500413541d125403450610710202c00c00094511a0111408071007800b00c0381601d102800000b0208a039031241d0000d0400500529040712462189864101200100c00c3c00381035001034203041d2500d541001011007d1840306429914504c056103403006422400d01012210010000b40c1c41356112070600241c3e6260740310254120410040a9040000c08001030240c12066111440020380703030020802c0d80e240d190f10040003084500018002140074400d0b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 169049892 1250 169048642 169048661
    0x50f07060906110a0c3015050609010b03130f050d02060712020408100c0c0b01030c0302100302030105090f0a0e2b020106051507060b0406090f0c050c070611030c0f03031b1c 76
    0x1000000c07242101084010645c03043d010351f03e04901100488104156014280c3c004004544501301c85d41480100001c1c1d101c058806030074480200800c604106070008840d004507040000c5e540c4210b007844001e074507124102c4002d00062500a242c0b003185442e0720a89040d110240000d0608000e869401c500a1500650031400d0103001c0102e0000507650b0b600070350207117220312141c4981c40d2551050020035080d40120030b00b0306006100500250f1954820309038070095070358040d02140c49903040f400040110050340c070300501403500f0908a441010f211215101498214a2801500c51800304c1c2250624041d807503202e9400404c2c07202080b02d0344080c006c0c0c0c80c0201b00000d202c003031340b00000e42264032952083c420140c0b240d140c1d0400f46110300c10100b800e01e160500d01c5c0b800611301c420a4a9202c3da0080c1018040145070b00c80748018100243c039814944401240c00c10090319046a0f940d4000321109500d01c03060848100c0c03135507024170584c0c807a502504000c014812070300c42103801500e107054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 169051142 1250 169049892 169049939
    0x1180b220f03171b031b0607120911120a0308060904020117150a0303030605010f03140109020a02100f0605120a0317070302070c0b090a0b090a060507050f07060906110a0c 75
    0x1002c11000f01507440e04a65410108005551b5030070f100c4448000009200d41030710311078000d581000040c03600100c5104881d01d00290000d4500c0c2c80d89041b00840c62041c0c0c040b90400803c80a0515000000640c100e407940030b03444404d000c1d80d420341005800401124000c2c001034100000c0541088480d070a80e420880080c0c0070700c400071091003c619500342c1d562003540000e0700d41030200101c5d60000d840c40c410001c140b400780801050300b03500000c80762040c490341001613030009140080d00d00c248030307004c24000e14940600c0000b403810421009051140141440389951012000794020009441114641c0c90307220404045140282540003440081800b41495000c120201c00100a450007402501a500700c00c0e89405010381405542d421507080514461b004002c040b40705d5403402031245c00c44000d490419038800f814642242449203184200f40359118810340421a10780080c46501954060b0f80c41d64080307041c104c011642c0352140f2201901e4083d425400344a4101c03030490b681ea0404000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 169052392 1250 169051142 169051147
    0x3271407120305032d010605090303070506040609020f060a141806030703090c090b030304050d0206040b03010f090516050d09051606030204090507021f05040201180b220f0317 77
    0x40d035080c160403410010442c0080e0380042004014802d2030380080301c0a4010101140d0818400e0382d070582560b042c0a11030a2200204540900d83c3e810000c80c0d2010341d0100c152105414940380c503201406203440100e1099221100d0000c050034400251121480c4558501b210045040d01146083d40502c000720060b00c500200901c0e40c0d101d02c0700039405204550f80c00140300034031782000302c8014040c0c0c11425606050111100043d900001960155881190940d0360f10104e84001003187c40f456111103c6440f020000140c0c01d00066099402c890700a02c007401240e981c40c10754801161035429a0021410a00000c1480c243e90361048801a1080e001c13298458072011004020b83d246612140002c0e40028003448004840d00903d0340240f10b43c001030200681e13050950100b108148828540c80313a462000070196845040040f828200380032307148810399220143c200d8254442c04440c0198443d500041d15801d0525540c0c0013240c41450551250900399581c0300ea44120012080341542002d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 169053642 1250 169052392 169052399
    0x30207060e0609040c020c01030608010e0a1506080601030819050f0301030602070c1a0702121c0809010902061902060f0405030f0901020a02180f0a02030405330f010603271407 77
    0x4c40c800c0500c0100781d40c00605148200b1000141941e5079034002004c140d0509410303021046000801700d0140f0380c0440f81c0044010480c0000300103020b5907116500710722071140008140302e10f05006182c400342c4000c0200f4114024802038845100d20b039040040e201e030400040002c85c80030340c007900940d07104911000328265240c407a403010180c403400d07842d800341000409200b14039103040c00666000410000c0c01550304601c0c9503034035005111034000d081c4811600095040d013170030345c401e2558550003840e1719160210a40000b801d0140c00502c50090321603076003c01c0d0400c012070012845998030030000c43c6403040401000215811813548141503228080e404001039940303170100b1109050340c800d04280c500d05141c400c014224007405e21800305104105202c00314001003402c04d1002328106840462032404c105041e0301100e035410124011035820140050702081c02d01150488105d5982845801c4040003881da045804c01c44224966140d01070060004900400212a40351401e00303640c0d00668 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 169054892 1250 169053642 169053649
    0xf060f0904060f0f052202070f1401020703032a0302090d02040603050102070203010c0f0806041802040c0809010507020d080103060b01031b0306051c0f1b081209030d0804030207060e0609 82
    0x100342c21004110300c8140c3d0600c0355058410a0000030b0800319000d080d02160040900d40c22840d42c509000d640d0f4000401205000502e2013100c581035208400c01070155000101030300035000b041007100000e0a002d0994080200ba1002900031812003518203140040c5810a17402584411446900a1001c003892401340e550ba1207060011401030b4009685c40140d031041508407216403c44905000980c0e0300c0d001441da02c20241540004140ca00054a44c0003001521a082ea4103100951190030b190440240c194031246103401088840300a10203600d440300c1c1681c55020b0ba40340707140000c0c100401000400c04076000f83c40403c1043c1030010f40000e02c0e642540c803a0300ba40f524540800d0325408104180e080441812060f600041111255151203550f01940c002c6034680c094903009400544a60b190342c2030300c2c2030300240104400c8a50f465026085915207412920b0507602c203015411611013440d008040d280c0c4501e5056018003189414480705540320300705800841c2d000030050001864544 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 169056142 1250 169054892 169054901
    0x60409030e060d0e0f12030f070c0215120601212007030c050d0503010f120302120a18051f0c06020903010504060501091505060f07051c080405060c03060f060f0904 72
    0x40c03c0c2d65021910406190b6618a00b90030001407a6440d44014446001c0c40101825260001600c40d03030303800c00352104e0004440b038102100019501c103c0e40c0c20082c072123419040c000c01e0041c40000f000b05080d034401e001541d03580c0403a2881101c500c0c0340c3c2d0307540c00a004942d00080116042d180010054025840081300b13907007010404401184e000c410307010611104014105c04000c0c6032804074515230400b0350410000425210b03a004030303418031556108240c0203000350880f44800e90360503500d0b1440e20398010004271040c0719801c481083c007540440c00d030402044800d034980c1d40020140e18500015030441d40940c0d05402a9440c581c00e00c4038014030307035080c01424003030350190350081141d505040468044643c140451080d0001d400b80422854540ca001d0742d0345003200c81442e544a14003070900900300400380691002510141001144103038000d1100c500890051089601560703400004001d60b220541d080d0751701102c61204c0286c1c41c509000180120304070070180605110461010600340e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 169057392 1250 169056142 169056157
    0x90501090803070507051009050a020103020d09020909101802092a040306021e1e09010306050306090715020f0c100909020c0a1101030207170304020303040f320306060409030e06 78
    0xc4c2000400307005200007041080300d807101c0b4035410400d22039aa80c83c195211074050009040c1600030411494000495101045031a0060a100c03114030340409550f07164120002d40019262274509421201c10380981c2d83d00440d68050f00b80040f80d2610070f541415400e10a00650125840d81d04007003080403400c000c1d10040d441514050b0312404803002c10404240580c280d12907040c0700f80004190780d010340b40d10742d641101d9188696a03d405e0500128003070540ea8210580500c21602888403030b00001400f030088414240d200d0703502d003015000803610f1303504026009078a030380203095500161a046001c401e080c4481d0a041c00a00d175550003280c1642c20401d240140364003c000c004040c44039451038805165000d1908610342605640c0391003203420b0341c100800811801000180854600304200c4002e0107980a11246480d503440103401140080000e0300305488c1a040d6040400d802202103000f050300007800350549a0701c5505000c0240b5074114184d0130440b000d45404004e846840007410031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 169058642 1250 169057392 169057397
    0x71a04110310062103080708070302090406080c0a0b040b0f181f0905010203210606070b010f06120204030305090f0406091104030203070b0c0a1e0506010e061305010503030d09050109080307 83
    0x19480c240d00d140c0100042030904100c0c0510400340e0740004c0d408100b959007c18207041c110039944072103004034000e00441c203404d07800038500300c3c01003040180000c2c602c2c02d040048500c002010344620248190b4081c0c1d12810096400600c401c0c942603074050080c141e4401130151040001d40c0c54800a84081c102e000009141030f8141c102d074160b9503014440a003e0182800210315240840e80c50150440c0c10307030040c2040740d4030032001c5060399641d8802c03103820541040b6402e0040d61203600c0c42002d0300c1e0500c01e40011851031070600e0f200305014001d850480390982c0700d040c20859504140080c80b0410040994015500d4001081d030804921404c0d00842010b881e0f943c13501d08602c14186440c0041d082031210304014010347d0400d000008202200590009150030120015589805044441d1400401ca805298004200c410320a81103c1c49020201c64024007210904003201c11110280142130705500100402040d0b00c0c1580c010b00b0300d00744100000501d450b469220207406030811380b0754900 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 169059892 1250 169058642 169058651
    0x9020405040b0106030506010806060d150308040f060224010909080d0905010516020102040806060d0f060f0b0f0603070804110312030f0402030114071e09230301060b071a04110310 79
    0x40c45c0d81032007019480711003820046668180400080d541c0d01078041da035641152a8080704030400c1140401d5001503070700c103522544480d00d0340340814400f005d6001e40401441080c000410580064a140e030810752072074011175059003802d0f02c0c0d40180c41404402e6942c40c204000d682186840380c031950f030115000700300004685c00c10308040907114001001e003004581c014041403045d50800700d00703aa04048116010880000149480c07001402c0a000140955103003d41c868040340391500032403120b65081301e80c401c1c0c91010104120759400290303050350000341d030480028005170110b0f0406117078610040c01c64400c0348915807900615402290816041d5206d83c00303000850409004410111800c5a201141440e01010003402070112465440d0021405d9154503002806031021001812715945100000021002d95034052409868410b02a40c41c2000000c0d1540c01e01041d81c10050340005400200307100d2998900c40b0035805001540d05081d0350448804594040202300c4014591030070104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 169061142 1250 169059892 169059899
    0x1051c0623061b12070609021801030503031302041b0e0406080307050a03120f14040b070206010f03060b060409050709080d0f171b04080307050c04020a0509011209020405040b01 78
    0x1011070886400301a44030601c0518555140c10546120101c085602c403981c80c48034031454504100d40403045155407001408905101c450b17044021542c0c0243c56601c440c819900140b03070f40d00b00920015146420510110340104103080b000a41c4038001080441c5001c2034042e044040d040140a0b01301068000f140c03412242018010b0000800034040075605040030b50b282d00740c548028600040c00c0004807500001030110319401900c01020302d80041002c102a0700e80008024400c1e582030301c0d1039046000054225100080d0130703060750b50741c13900317944032510716a19800a00620390071560300040074000841c00344002d1285d80c1c812942c696907008594900f41c0520f01f0009074400328400c10090200c0c800310f160b00b2010400d01c2c8428a00d001c0301650ba176200c00e10481c00740000a203806000014000380109000002d0142d640c003841c00d840300000d00c030381000124420200700780040b0b041030041c00c01a40c0140c0f0300340c43c11211a80702007071484c0c03e44c0c0000c0c1200c00882d011682c3c005c001c030052 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 169062392 1250 169061142 169061159
    0x512090103240e0a06270e0604170f0c0f07030c120f030e04020c101a03070806270a030203120703021809090111030f0103020405091603030e01051c06 66
    0x450001031403002d82000100784007035074881c4440710f0046155030807000011030200b444692042004046c80328544c0920303852410018000300100040301e907034034206800036a4004012075854007641e444240c075140c400c0618841d6442c1e401001c810800c0d15002d100005a8907070a210024404401030098510281103207403000540d4040d070007116a8819074191440000d4903114103030b0350350f6014181003010300d240d00c0c0001c000c0c2c454001c401c0d58ad40030782d0826480302e1620350810245480802c1881c4d865000d22001d00d580c2d00c02620403011141d000d4004204d0362141d03c80143c529014003102080c000d5000d2072014a4900d16040c11401a480081e405218030803c451a90b0801c9092800303501d0b080d150f00200390201c4050361118441d030a040081061003900354000340e00c0b801800001c43c0c41c2d2801005403a4512424401640100d04050000b440c2e00f6000c565104401c60b170240c003500c19421900c00b194040c08045e0194180801088416000c0181d0711085e4a16581034a01251103818080e00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 169063642 1250 169062392 169062401
    0x40b070206091f0b0d021f030501080a020904110301020705061003060c08060907031a041e0b06040503100b0102070b07210302090307030305130302180108011a0a0e090a0512090103 79
    0x80740296000404505035508800850420410a03041c0101c2c8081013000010380e40001644001e600460101c0300e48191450a0344500c9402c0440d20101728986e660240d290300c03840c0c106c2d00250300c600305200040014a00c5110b800c3c8081000d000142803503030175601c140c038203401900c0240d00d80740c0700442003042208a014201ca401030034900140a8202100072036604140030385a9000d05031141e1400301d000b074103d01c0c02d260100d8001c0051110700240783c505c0c000d11580030700e052141c1d82400c103820503030f0500d20300b107400b100c80140042404da121101410300400f80c11b00000d046000d184400600041640c000d004071600907081103440380022001e02e0101455001d44609042c01840003140c643c2c4c000c00d0500c1104d0305820503950b42c00c0306018099020100743c1000394403200c84ca02c0380c080c6542800d100c40c141c900400080242083c00074030301d54041c2c0580c00240d0710103600d020621040104111440e08140c015044585040f103175035540c2d04044c18040800c190341000310742c0491940c0d042c040d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 169064748 1106 169063642 169063651
    0xb030711030a0507140d020d120207052e0603030819020c100e0d0203120114010e0301110c07060503010b25080d02070c05120c130f05040b070206 64
    0x4001e85543c000b41300c00d650f030204c19290700d0043e0300b0000d101d494001c11a001825503214010086030003012204c1c44441c543d409000e2003000507420000c404490700b030681500d245014501d20950101c5101c41c1070f04c00d003400c01ca020404690407202356a0080352071003070300e00300b24001e0324000081d20070751a03216040c0c4510801c2c03141a0003a5030040074140c01100a580f00e20404006c03c030380c0c81c000c00060300020400e000042000c0322500108109091040c10f1200f40e40d2000b03000a421250324000c0c1000741040061035110540c0c0a10065000d4044d604080b811075050014100c20f40c024034440305000e46407641400c402c03209042000c1c80403a4000c484594509140d0b81110194100b500c0844444c40e07042c4c0f01282a1411646c0220b100b1004001000b107a0100304c01c02200119900000782c038582d4820000402948900450f0701c201c1c09050351003a281012031009240c00750080 = true := by decide +kernel

theorem cover : BRFrame.Cov 168884892 169064748 := by
  have h0 := BRFrame.cov_init 168884892
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 168884892 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 168884892 ≤ n) (h2 : n < 169064748) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
