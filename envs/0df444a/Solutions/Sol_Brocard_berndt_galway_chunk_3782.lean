-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3782
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:39:23.321377+00:00
-- url     : https://prove2.me/submissions/9085b905-7354-429f-a154-dded51354cdd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 680035971 ≤ n < 680215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 680037221 1250 680035971 680035999
    0x51c020309191a0a09020a08010b03100e1501080a03110303010506040e1b030108010b01021b0612090f1606230d020a0306090e070303020f070f03080a120c120b091302 73
    0x40301030039800f000011000702e040c0410310903143c10a82c09240b00301c90208a0940b2107881c2400c0b01c44a00326168540d03c5100d000050a0301644104104541d502c10307a5190558240b812858513001c3e4840f500d240e1040c443c44080c03641c0b12001030705c03902451014501e5035240400007443c41c0228020884440038110211386940c1480d038000c648000d040d42499181d60303603804002d00925000c07129a0160040c08030703013000300c01c1c18490041031500044c40c06003049540c26004036501c13001880a1081d1113240e9843d81e088504001c02105525020490542c031410070b40e000382031a0070035013080505036000070607408600740300c02030b078007400d10215006850740c0ca4020210b0107014180d0210f06607038a40380000c80e110901040031020380303001c0d4007103690411049000390390b0785540348100081d100084406100043e02c01008152288407482c22040c030165035195a81280c8820070740c100407900e45c0600207940740d40f5000340554110122015017552400c0030b11240302d00031040000744034800c1e02c42040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 680038471 1250 680037221 680037233
    0xc0b010906060c2406031b0902040f0b09120a06090c08031c020d0b12010c1b150507110312061504060e04020c010e1507141602120319051c02030919 65
    0x8813075166985014480700780e980c20510b10003503144000b060031140c81d00010600803143e001300c07001c95080c031540300c0f02c080c0781062079002d81e04403105042c0d20414070300301210b1510040051683c2c0034010500090705498a180070000d40301c172a4850304140d0418043d0b44001ca102c40e040c0c0002205502001d80d50f14001e000d03041c0100000c84003560720194220002807403400540c044455a60b5036202c0c5080c80c09403486000f44000441c20040507180d03141103210180c40c854110940050660030f00103103030f00d600c054075400e40c1c02403905c030081e50140303d04200c10351038481217004402a80d0707203066181038180b11000b4001174400085900990b0006151000c1d60740941c02072a503c52040f040e95095800e0118401c8622010f4400b44001080c1060707201c0819900411a8504507902c103484081856a50a000404054494000302c0d40030070b104101e00b45c0b1000c100da01c1e83d01c00d11340c0c0d0700d641d9030b066031541402c1c0648a407405011520600411021010004843c840c080596241c2c0d007101c0144d107088 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 680039721 1250 680038471 680038523
    0x102100c031805070f0e0c040603090809060714010f0e1009050a050d120f0c0f260c0405130209030c220f06210203060c280c0b010906060c 61
    0x69009500c040c0440061080c04204407007030ba0441d002d8492601c0d46c0d5184008448010789148262480c10802002010b010303034803021525100345078880c10401290000380e0f040e04115800c1d14840700500002007039000a120700b010303102107503008000703200d410721007555541300d08580d0700d015907540c41914043c848100000304407250301500700c88854081c0030004049041c44060101c0c40c03410171f0302180e800a00c0c1d0141025152036950380c481049110102204c00c0640c050743d0003011102c00713400b10308200440b039907580f0900c0c8030b0600ca6074603840c000501070500317107450000e06c03181c0c414040d6118541d004035526051070b0b000c0300d545440c46801c806e0900c0304118812804019883e104040040080ba50801401ca84144c1c151849042030990b008030803404d25040254160407900008150a0340240503120002c26001e4960f0350f401c448801300305a0100750640c401203020307060907600f0050700b0000da50150a140c40c01f840900d1070800090402e005840c0010445000151b24466039040400c40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 680040971 1250 680039721 680039741
    0x90201020a0602281403045105040f030c0812130209070825090f140901050d0807120c1209091a060f0a0e090f0a0c09050102100c03 58
    0x4110b640329042c90302d0016a00c0100e100240400e00c11003d03142541c005c0a9140d07142c2080001146907640300d54070000c00c40087c11074000d10001a800b40c41e8540c51106101a804084000c03000300d5280c420001103003102041c40d942d107074a04001c100000a101200000d002940c107081100d4180e1051503c1544d50044801d1042035048041c10010022500180d860380207000b550410650b8842c8001212441402c49150b504070101143c0c03490103070200b021206e9013114600d041540c031034444101505500305940324003064416035a5210162405007541070040c00e080794440c0c4604442e548022450207410b03006048020021000c03803100d40a0004d03810810345c4100d062945481402c0003a15007107a6008070160380745481d41120440c44d4104030000751b100f00403d071310308143e41c119400d0b486911070803400b002c20610301481041c40e26004603540c020364031648007003620b00e4884c20200032240010402d40c10004800c01c10403190360040340c20840400301410100301c0895040081c1e001c0c21036484 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 680042221 1250 680040971 680040983
    0xe1003020105090f042007020f060703080411130213090e0a0f1118010b0c010c180b09060d1e0b0a0b0301170106030b07021501080d050a18050303030a1a10050409090201020a 76
    0x1003041c2c001e00128000b81f0340103108940c21501902228280006401591001000708886001103004200e00208120806030014050350107015816000320503a04400c1c211140d100300d01030140300e60500b9000c1e00700c00200d240700914a140e0305803180c0000b00c610714405068041000c20307150407a26000a4883c1c0800030021090040d65601100082740e8828040d06c0e526510f405114004140f00b0080f0400c8155103900c6541d603182401042501356000c0070301540d2000c0108642541d460140c0100e00302c925581c1c102081c618000c2c02c84000740c94201461070b1161002407800c1c004c1c003038800c0036a030540e1000e40e400400711229032400c0b1300420741600003030711030444441009090340e4000b5118803040c1ca0900a90340d00c1c0d070b80f4502d09039165004c0d160302021600500000020701d2084113901078070003c0140c503d11040e84c540200b0700b168015150031030055101d0010b2251480103800c400034450080d80c1401c500c03101010010100e00903400f0b00c3c0c04003520b844908007560301c201b20351801030750006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 680043471 1250 680042221 680042261
    0x60803070807121706060a1707030b01021504030516020310060e1f1a03101a040510110705060f220503011d0a080a2105010e1003020105090f04 63
    0x2007004882034002203011116019203e5540426602c19a0b26004098a03119110b0740d54031080c0c20007405401601031081000024006c056054011410050103480c1d580c40c001340d019002c1000905260000014622240028040c440004e511000f11003450601500c92000181741e880083d0030800e0b206c039900501030400b64049903085141071241e000e906110340c110500520001180204803240c4903507488201c1110000c9c0c5410007410040d507001d11211030b40155030780c582071814034021a13000d07011040000401c00b4071131810042d600c1304402031282041081100c2d80710f0ba542c0c2d0381800f801018010305000c28005607803021349050758250f450564200c035010070f075030030b500c15100c460307118040c032030b40c01c0440b04004c02001c001c00d0042c2c0c02111000e444404c80ca521005841d50004501c00700b0090030400391028500c80c0d0140a0000e181440c006c50035500d802d59003234008501500014072120380c00300401c0180e802008840b00107205945c0d20340402461340000c0c3c0200359801e01e10046080328 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 680044721 1250 680043471 680043473
    0x9060d08070b0c161a0601020106140f0f0307060206010806130b130602192a0c1707210501050a0501151101020f0c0d080a3605011803030506150403080c0106080307 72
    0x380305c5c1c0114220321210025035620314004a080c0c0c0ea4a01c1150a00c9040d1140d511040c00d01d50300080c407000d0068511014000c0c0c4074042460140c2d243d2000006030000707001840009420b105a503008000109900c4c03907908070740c81e03110704908040c1c41c20301c1e400717000c0c20034004000039501270320f800b80c07040012000d2a902440340500b40240040040fa40d5081d044040b071091004264101e5402d504a02c40b96181c90828641805444c4400c1c1101040c4c868101c1c0040c000d845c03844081502c0030303507180340d42c0103101d0343c41c1c11401d50348090b0100ca12035090400610901880f00c5100b494003501d413410003400d990482100d40288540008200004030000744044001d1000030381d590700700e10555a4807610383e01c18041c10102c13041e00c41465000c80c4003180480046031071190700c0d00703811104240d40100300304c0381d0380d2682121400c504032a0746001002020080c54dc0501c5029800f80d010f64402150070702c2c0d5002c0e10b2243c412404010a41d81c0040355507500760509521500c098101c000840740d4030703009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 680045971 1250 680044721 680044733
    0x1101080a140106030b030601090606021c0c080d2901080c070309051806130605062a0a0b060a08061506070c0b16060f09020a18021201030b01030209060d08070b0c16 72
    0x11403208170b800ba2247c84000240c005692103518220342069000d0b04031001d200b450410701000c0c090880301044800c280f07460105800900400d43c0301d0081e01c000940c00d00b190f507124181d00c000b18424511f008070071200122640c015183d140e01108425100e5070382c9100d8a015240e806d0325401c800c0c0c0054100101d420405d41104000380246c004844038840c181a244641041d2a101c2c011150003481c140b28501c140e81440d13404d004680c1c0740101d0b0350303000307540090107600c0d24118450954000080d4400d22030036050484401000c0e140e100094403c510301606684000725000d01e03068007640c1c1c00180b0300280104840380c0c030054000e117001a5a40e044109116210f8103220b201580d4081c50050312400208980c458108250350260001141901e400d1147caa201c00c50041a000d007038080042092090b40c080c050b0b800b0b18880c1c00a4012075046006000d005034000306203030f002e40300c4c1d84c01c010b0200b140c0314103071600d0581c801071010095480403c3d0b007800c1c0c007401580b148407040c4050040304102e5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 680047221 1250 680045971 680045981
    0xc0301030b06090112030503060a0e070e0f010e01020a020d050f100213091b03050405010213060c060507050406140a210518210c0118050312060d1101080a14010603 72
    0x1026641088882d1903210410480c05001c1c4a00c081450341e2015901c0041c1c00b84000c3e5500400003003c2c41c43c0c0701d55030141c100e0032031411510b2200040e594181640b5034901160940115003017840c05c04840298080041c0d65401c6500c0041c0c42044600c9851040181c10003010b0f10400d201001d4a50414944101c18085c0d0001c14102c54004070360f100109004500744601e4002d000c0c0c4405d071805075440310f001a001000702420588565408010a02003004625101e00042620b540c0c4c03840b580302c590a0840c11260702920b02020404200b004000542c3c0c01203404d988003031641086643c80c42103100035161805002074204c9008991154203202048580c011803054070140c4036046e0703255141000d9a00c0d03407000402c6274403d141c40312583c0901d44450018001d00c4294600000e18120700781d40022840b441c200c01140c03160300018428462942460b40b05420010a8602d0300085901390b94040f06803121543c00c0d4100031030b900c00111074420a40116442031400030310050156121000100134103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 680048471 1250 680047221 680047223
    0xc01091b061b0b060f0a090e0c01110607020a03050c07090c032703021b04060b0c1e0f0c010804020f04050901151a0304110a080f0601050a060f0206060603100b030c030103 75
    0x2031482000340d10a107070b01910071140c260710240e0400c0307590f0392004120510034803213205178101745080e1022032403800c0303842103101d14403221004102d00001040010507460041c030440c0f200360001018001e440390000703801001c032540740c1040744e110070f04480220310305240740c2d220120041c11f281c107484503103400d03601c00449607140005c030000003543c0409141c04a50780483c0280140d2058100c0810b00b40c155403207440c1d0b030364014000301e01140c1e5120100404d40005203103060641051111400040c0b0800c9410383c0e8003d4007002c0d101c1a1410826241c85590520515040c400100001002c5640d0f014150240c50b80c0104208250305000c41050b0007003031964950180d0303032a058804100c00c11f5540f2020140e4091201c0c152070756036142c8d07515103203020114201c1d400181001022070300ca1802c0c40300061003403480c001800c2544c500000c0004001855100da028480c50345501040f059000c20307420b911910694001d0765a4403041203860110610394090780a04c5c8001c000d001ca940c2d49000114100c07 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 680049721 1250 680048471 680048477
    0xd0822050d050705010305060604030614071b08120a0e0109210504050f0f0a0302100f140702010c140c0a09022101050306011811030411130608030f0c01091b06 70
    0x80c0c5600c28801c40c24610a000392440c2d000600c1044607602c05e81100343d000d000506603d04150382c0c2c0d40d900c0d054624110341c0c955030311002020042c0ca01d520664252992104100400c4400c0003626044114403500d03030ba412408502d80001051307050103401c000444980344001f007101c44150300b46400c51001400b0312582c560403000c0d105210610030f109a8003658070081c005408401220f0070090700042c50f14440e41c00900441c4000701594903003150b200118000e44500803030f01440344004050b21681308400c5070a080c20b0080c20090b076030100362020181d42c00340070b0140b908040c0c00c506203010308203140698040c1c01500081000065a0007a01c2c160050160b400300c041000d50369003501c000240100c58059102c08010464104840100b40c00752841c0c00380001c101e403900105440e03d5004980582c0c00c400c440394004a541401e2000e40d501c10900401040101c0c01c015900351030b1301c9900c20740da4404a001c540d4a000c88000c1d4081418641c0c0403c044019022114000e189031515100310004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 680050971 1250 680049721 680049787
    0x6042d08010b0a090e0a050d0504140108010303270f0b04090b0d02010f0c1e20040c320c06010807061b06020304030e04050403120c05070c030b060d08 66
    0x38282050042010180340103120081050421000600405801e500c2850038810140c003031004c2541401101140784540d6035a40d521402c1c108000d482010b02c546990400c402c00d00104003003035003c1c2c1c0e0010042d08909030300807200ba04000c000d070000360b141c200b92421990390304009180500c01e070090041b40c00c20706045c44070103018030403c00001201c15020703010540340050f54100e03e201c0d458542c99140b007500782004040e44000e12080d4040c8100741100c03001201070b146015458a0240c03064966002c8500b03120740c241c0c00e4001020380c10030310510382d115003800421042013a090041840c03041d80d00f480d6151280007103880690348035028410032101d4001c003a404204688982c0c018210503414450344546003d05998680003940001d00a4042003402c0514251564441c001c0c2030055000c0d90b14085e40803460401da20031140d021411a0610100304881d000082c04400103000700c1e5040350028141d03649060105d10f2486010700e004010350310014404401402c54005a4808442c1103800c5c0c2d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 680052221 1250 680050971 680050979
    0x40c1e031b0c05031b0318040911060a030216050c1c03080c09010903210815090604050901110c01051005010518090402040e120409111309090206042d 66
    0x4120358241031040d9080c007041c414a800903014118040901d480382d42100c2c5007010401ea002d8865007859143d501613080001e4104100404880003803007000111801c000030481903541411045100007041d00448011a10005d042d000ba030503142da01c0e0401c14010244d6142d45003007610b443d104494103111b800a14007041c03070704000c601c8450010350301d500c407040c1320b8440b500511b64070780200412504000f245100800001d8280d60603001d0840e030324582c85654808640f02915540000700b2490174041c1c100500403607079030313806121a000802504d000800d61142c140741ea000d8002e6003646207400d2000038000c00c01010546c401407281c2143e004143d0060b4459004550600c20b25646458016542d1000d4100b407411280340741d0003a10041000800841c0c18090508103130b140c58040403003100c0800d04000f0014a40654522510380303001c440e1a000d141c806851094400b070240d220015030f10310388001151201412240603105480a011801030000300107071032503500d1300b83c3d5040307490380500001e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 680053471 1250 680052221 680052227
    0x518190503011a1e060a18050a030605040b09010e120306061608040f0504050c0315010c0b0c041a0f1c02040503030301090f14010e01060e0d0b07030b100809030306150702040c1e 78
    0x8a080a0080c080380c900341b00d800040719041007000030f1a202c15401c2d01e00103000d80c1c610301500004c505c5070501140d10b00e480d00305146400002045c4200c240d04044100d103140308046002c0d200c100c4030703040c1a038494890a01140046c084c1100c03801248004140794000d110540000d44129009880318038002034460b81172005460094a10502c1601c05001084406150701241484040c0c1031410008184040e2283d0030004000d030b4110501020015003444059280341c0c4801c0098500c80800c0e1801190004d1040180318030410b0071400d54080000341d8100300310760100d03402443d000701100e8495840e4201d0000405000c0c01c01400c50346001d050700361550602c0d165a040361041062903000380e00e40102680c0e510018014140d0090f001c03290710001902d0703a009903000d06040d6800042c1c00c0208000c0c008006400780ea4034040c1300f11310007003000d451000412294443d10646111000c82505070b0349191b80d0007204802540141081a41d03600303194440701e1203407695690074451040c52141d950607 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 680054721 1250 680053471 680053519
    0x302160602070e0f0a09020d201c120c060c093206181c0b0c1c0c03020d0509010b0a0b120103020411130f090c0518190503011a 56
    0xf06030002ea007400058035400350004240e4003040301c500c003080200c03c5500254aa030305490f8115444014071100164100c0c0c1805903242c19403080d80e04d0100170780506400c16403448c000800410f0201c01482414000344982040440140c3c8110b0a000000004070b0280400c007075802504030b5000b15500e00900c030808102c0480c82c003000f0486500794a44580e09003c01d0380c0c810806208080c45d42d4a024400c0d44440c8100140c1000382d6a000080c3c0209180405418801500b0100c003d00d09100c2e180240c1c055030ba40881350340c40144002540251107000358043d000321350010403c035117004104580700c2c9041d00101d11a000884550b840340381c9881c0c42180300c2c0a4691480c1c5c0c5600c0081c0180010704180d8031554074041d89000803800c0103030962541c1d07140383c0749411082061792203510400007102c0600071401e5604003810024104900d64001642000c062402d4521501031044a800c100b041200328a010302000390003030104020800c40800a45a060580c6008041c0044811b840c0b191030410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 680055971 1250 680054721 680054729
    0x4081b040501030f0b06041806050910050702060a05090a0b16030506060a30090c1a0a1d0117130314090f0d080c1e061e01120309080a030216060207 65
    0xb010b0f04003d22a21175074030010b0010003a81c1c01603500d908100e0651201300022401038031034640415580381400c00c55042500e40d0088100396402d00d014804416004240305a1080c01d40f84001490340c1c4201c64580740c011440f8000d010756184a042c44010007172406505d08a540c541c03020f1044c1d803503000138400a4403450924000003a2205162000724500c822100c101807074500016188050043c800011542480c008552440160008001d02c14281303504160345014086043d060401114010301200500300784002e100c2c188422100f400da0003085000d8460390000481d03081c030710301100b10021600c0010340603000715104100a07491294040101d621500340507080f501c106031514240503840080b804115500d843c00d0002c144a65010443c0e070b0b8030050440d840c00c811841800807a420404081c00415004840020b600100002e80303500a045802c00505008403503840e0408807005076054100b11010b00803040700c402416800202c0800d14044900d221907103d45d01e071000d994509140c89 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 680057221 1250 680055971 680055983
    0x90f0203070f0801260304050307060302070201080a0504020f040e0a0f0b100801090809013507091e061101061703040806160c1b0b030a0f060f0303020a0816020604081b04050103 78
    0x15461600c1102417804440c40808490a0070f8540d00001d00f014100d81184001a502064407019583d0240415400c02c00031002004181001c1d008a503030748490b1a215402552500d00d81c149041c42040304481c215080014071882404070b00d4003038813103201030b500e46489a611250104100b4018170034a500e46030720409040c81d01d006030f401500d81c003c07075551900e0240c0070400305044241c01103a2156055500103032017062031400403006400c00d0b04c503420031510701007484820140050102505c0c0c05403201410318040d4254904040d5015001503008a1140e61401045014100e0000094000d88246d80c041c0e407030b256104109050074528007254140090700d0402c49078041600300d4294401c01860300100406161600003004e035940c42a598880c0050751076258a8207000c0510401d0054040e0108074804585951802035480c1783c50a80030704010000650807600200120540345995409041c403915190344e143c0c0551200801042d9003004c040f03107500ca81c002c0c5020300c195410fa0354880 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 680058471 1250 680057221 680057249
    0xa0902030f060a17100504050f0601270b030307030309110a0801050405060a0902090712020f0a0c021e0a06030e19140607020d2f0616030f02091810090f0203070f0801 73
    0x1505d880141101810a88190062501400003c44148240c0c0d0180c52510795108a14110208402c43c850240004c5025203207062076190003540d0110440380299010700d00401c1408071824014040a80001f901c0d5200b0080031001a0800c010b40142d80315038014400d5488030b684040c6100c06403010301a000303500c000c0c42c1000590080c060390403000d000140354401400c2074441703940d10a050307016401c2140400c04200e001c01c00c52401a5411043c42e0690034a0019607400c4800309948000c1c500444c8181a210682d45000120422644020340521100c807e940c08541c1440d0107030720341c81d4140380421300460000400c80d50000400c4c18580d4416600c03040348050b84081d11121107281ca02c80042a647c0304416542020100800380c0150b201c2e898161000c0c2800c1c0020b02103d030100000d03108180107100c0d151640e5903619241d07004504d0301c161000b403583c80100041c00d07044560807200b0308524002c1d80d1411031145501840c850001c41e207174aa40035a688506641d02a82442010204980c132 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 680059721 1250 680058471 680058493
    0x10201180f0803040516090e0f0a05070b0a12060b0405190e0a0911040e0d0f080903030a0c020a0614010914060904060c0e0a090e12040819020a0902030f060a17 70
    0x80001998045e020f8001e0311854240e0304590140d80219078004001d42d52030344485001681309104e4034165030005401001c84040b140e50b90f5442d04803520480c920303203d02190340740e00c4d40d005810349411150350640c1004220389909400c14150041d008180c0582912441003400e00c1624000740242e400ca4801301401d5a50444401d002d0505000c04585030009600d00701c200707031640c1c091501d010030400e014150181c2103410090441580004001c200702d0554244040c4000210441e40c001d0703015003000c07032100041041a854821000ea00904503494066414110741034825104d0581c1c9468106201c41c1c50701c81d20039503030b0040a540d11680480f07090041400103495030300c40c1c8040d10b0700703040c070315810f02c42a000518043d000303a0165001c2c0751030302040d0340b4a14040c0300c0c030041e002c12148494140b90510403050b0f901d818020400e04082003441050055545401b50f400040011354010b5540e40b5002080c1c8600a00568009000e84e12036040401c81d644d4a11a958200c103204c00100f030100c1f1341c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 680060971 1250 680059721 680059733
    0xb0a0e0f01030216110f04021e070f050709061d060306060915060c01020304020427080a02010612061a101b11060a020708070605070f031d0618010201180f 68
    0xa8000c4090500da404c10914440210038901c03154043e00690502c4080507003d002e0190100713059562500c10f40c81000318051101076092036a558101ba03145060701c440e01441e08025101100b50058210b10a012002620415030341000054402d050085031010a060b0342580c850380c025904158543c0060b40040c4090400c80c8030b0355032154001144600d583c04032004030744030768420000d18046035000010401507080a006140500350701d1480755880c031340e40b00744100842c1d8007128000c1a01c00000b410314803640c801d4210354003074540e0b6600d5082564540c58401c4c004c01d034803010890301191000c0b1829482c0b40140400c07114417115128020102141104280107610b03110007160030810203006034a107900c41002038884820590010030803913040080d41c1d46046800ea02190420204010710000187c9002008031000d40c142030259030700700e00184413414600c00019280e000b030340205081e10900d194210b40d01054400703030000c100252101c06980c144c481c2c04d520140c40201d03005212000250 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 680062221 1250 680060971 680060989
    0x216180b0102100e070e180304031b050411070b090d0f050a0c0b2a36090a2f0901230301081b10120e0f010f150b0a0e 52
    0x140b064440300708160714014111100c86150248a50080c9003d10030150b101e5010780c0c03c1140401010030002c04804410b42c2c0e84900c1c0001020b00c041c22400d06644140702c4000b9003c5c040042c0b05000e032100c108c0a410068105407001d40c0e0041c001c0c004a4407030940411910225440d9680708a4003100055050703e0315400341500c0001c00c00030844070000301d04110540e5004814900040303410b40c545032040d0310702602050340d802c50000e00b004410b0960703001901061014914031010301d0078034003000d060110b50170140d0046410103105401c01281a1866000011004922410301000c40b00e060890032080070b20004298004001c100c10220740d030154040d01034100025103055080c40c00f441e650c8002d90401c1e4010360555000a0f0010601c11100c031034100304200c299900200b84040040003081c5151003080c0c0d511083d83c5280000c54454240801e441c88904c280003405038040c641a41c400400b0043c201829107c0311440c0894000700b640d0403a14140c405aa030b01040c40100010000400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 680063471 1250 680062221 680062241
    0x90c02010f0b0621101703190807090e04060603120309020108010906030503030a0231230f090c1b101803080703050603010b0409061b031107030c020f06030f07021618 73
    0xc94030030030000700f580604031a141c140746c1c18005580c072103010b28040b21451051b20340e40403d01060340d0030040000e81c01540c2c40308560140002078660b80b42d5040c001c00410881d00040c0010b0111500c1c00c10389070300340e080045958400e90711075905a9855030072900f15030031400000c10940040001c5200005281c014180e0507004d000d510030312007621000791300086141304003001c000e042d0150400c41d80c014950014000340600c0110803030329030050005102001c2c0d4048040c4100310b40c40100310b018400c081543c40c480c0007840d02100b0845485251581c0b00c0c180c0420080443c10940780018a40000b0f6640314035507031686440c442500d62230001c1d4003812000f041f0390f8041d940d40303102c0b040a5649009180d501800b03042c3c001074440034803035003000c4102c0c0c0708014002d0600b0400b03691081540750b001c5501451305032902214650312032000401d80788000e4152a8482004010b0110304121a030074135005480640803035980f1919019080e01410f140c0c4981c3c02049112000c5408a40c05600f10542c07039 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 680064721 1250 680063471 680063491
    0xb1008190602090a030f031701120212010608010f02070203060112030c080c0c310606050f070204020f0301080304080d030e07030b09030d050a1b11070902090109090c02010f0b0621 79
    0xc0000d95000c144c041020f0b920980718003180c1d040e540300380350b00a0142d00303e85600c80380303e18040d0305106556a00c825002c10090048400c41c043c00c001c40400e5000101416106000340004c480e0150040040e40049800340e00ca07021351800003135010b442c0c0f4404004613515845040c82d10395a82c4a009081c0c2003400303880400c0c014040550fa65603a6490030040140f094040c042030020350088100c2e2894890010380102d03450700c42d082c0020b641101c20364604d010750800c203d94400880c80880c001c2c1c000c0940e072404120012001144441001c8081d1003030b600b02e030048416940510b40200c0035100405d140282c0c07a0401c450601c040380246500a40c0002d4040c00c582c5449824040c00040354000c4611900c0c49a58980200a2096031039078200302400503d411580080094000f03911094188542c19000e40d0002d040c504a90140306003500030032480600b009503540750f1102074060100505e000c4010f44c5001c11000d10f91900d5030689108032600e0380c000900c0780c90880101038010000d0814490 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 680065971 1250 680064721 680064727
    0x1805062701050a020d0e0d080610050d050903040302091b190509030604030f0905031f0506030106170d022a1e040903030e1509150415050406090b1008190602 69
    0x3000000d000702c900030404010016545d4130741c1441101102c03407011518003181c1120700000c41065200c8400380c2c00110441d2a4400e0b0032007281c3c2500c4034460917003d940780d02e0816081202c030000100150080328003c0e5803402d41a907414040e5170840b81c1c0d00594810f134030b600b4030511070f1822600454000d40c003028180315107002409130020317240c820100c44c01c40005c2e0590a009001c15032000101c00100401d80060048a042c2e0300111501c80c90325a482d040315030355900040080c0d800f50080350080c080f02c03190705500d920700d5070700035120340f0500c01220151041c0e40710002c814003e00b01001c0d000c0c0001000d149003c0420040120444030000c8140c1008400307079005c0d820350b071107106408407944a03860009500e0300440c00b45085c0100c5150401c5400e04920410080c0341c0d010917450046200b4829200c010f41d03580c40c000100004955032400310b149031108210402005a11664070b0794050031205a01e40d889078200e030880e81c41c5008415960300100c410102c820301104191911074459507000d03003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 680067221 1250 680065971 680066041
    0x501050d0f020d2a0b0c0d11070b0a050a090e061809070f17060112020109210605010b090118081015080d0206042f0111010e070806060103180506 64
    0xc00d03c926800c980c045030603494a4000d04c8040000c01500a007800c020140c105034031030315296260200d02d4840400e0001075011142e1058041c81070302c001e8042d4232103554851294080047c031a402010700540071a800510200303484d250000000c1c815900201740050440e0000154105800094080301c0341e80300d6000e000c80c04440041544018241801242c11107190440580d4038000040c1d01204050344000124070150f40d01030700280a071807800c2e00400e0320b601220100100c2a03c2c402e4003034044c61818001280d0800307a4001031280f414241d980d0704443da49144502c65401c10351180500c0390380070548070022201070340c002e0403a880c40741440320f80742c2d65114925420180c51850010041e002034081004020301c80c460b000d03105240700040c040c0c0010014202c0030100201c071025060009141801d140d6403030135000801c0d4041200166101e031039490159030340d213800c00e44425020a00303043c00c0cec001007107217004500d50583d0001e0040946031508809800b0702222291008940450148661 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 680068471 1250 680067221 680067233
    0x3090901140a0e0402093103090e1e1803210a1512030815040f06031401230903090d0c03170a0522090903051c0501050d0f020d 56
    0x1030092a14640c07001901007140d081180358602600240c54180c0180280f0026032508500e050b0b2019130402031007444a40110006c2d075007001d1050706545000425415010903a005c801c1100b114090303034009586880d0707038203080c0b80303010040300b80c981c01012280010303809031030034500310086e030341d84801e0307074070380400098003440c2c1c1145002c40e174415100580a10070101802d03c56065500e079a0700d699041d083c1403545078902e003030f014040038041040e0200810007804480b4035a0b00c40075801401000400d4901c0880c0028040510041d240c0244100c1c101c07050680600640c0c0410072040c0c05521416403401c021491004040c143c0411844140603450140d10f400c000c084420f4042c103030004242d403541c5040e082c20390008210821404080c486284080c1d00038054903080b540100480303081c07021400c1188540200355128464640c10004030006158000300244003050307129040741c1c1038003500c030072483c04d68000380300b041e40120542103c100031030152824441c1e007620041800031442c80c180c440c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 680069721 1250 680068471 680068489
    0x206090405042409150b030318010203040512060405012702090c07020315150a0b0a080402180a1a060909072006151f02030307050c010b1008180f1e0309 67
    0x42d11610740c0e181481424820140305d640074113520f00c2d5050290a10f5000401d440b400b9450501603038a009070900d000913802801924050030700940140048554070250583e113507801e407016605c55182c0b01c070003903071440e51102c80c00b01140414209070403600141c0c01e101801c84001d0020f403d9210612002c03006940030700116060311080d803c4a610b03030030400e580c2e040340c401004807548a010740c03500403c00030304103400750380e540c10450070055031aa6460010441e40e41c10740c40b86040640c8002c0030803c00010b207a019903503041900c900306001c00c419506101aa110355030303070194030807400e2000036480ea01c200084801c84a4180c0b40000c0e03821350313a40c4140f070b000e001d6443c2c0481c509001140201c9003024806402d01d00f03050764034007442c0412144040c3d1280b2024040b00704003c4001040f40e07800c90250024110319001402c20844039030003a00042c03184006075071041100349210681607190704000b44100d180c01e4244007510004210200d001c84000300180244000d000a00c8094920b0b0b54000318 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 680070971 1250 680069721 680069783
    0x6040305060907030210020703030903121808061b031b0a050f0d051b03251103040306020a030b101209060f0c020a030207090e0606042418051003020609040504 70
    0x1400d503d4190f20401620100c04111303034085500c90704080000c80d90089c4500c040343d4000d6004241c0505141742140c000c1520070030460140d41301d480006000f000001d90521540204c40f0080c0b07518026491245644415101c0c240300117a5402822031035122840107010800762030a00e103142030100320500603d13801094513401d400d952013040140e10f402c03060b51444000040c0400341d145282807503880400c5600405059104007000ba031805500340503e010740d1071038204c0c2e01184d0700d460340e0303181c40c4010394045000000040d007091354425541c1041e02c42c0503441151600c8202881d012099444010810100c00761010f47c1c68082082050302c20780f14107001c1c00e482d98058400320380c544c107004e840c001943c0c1c002615245054014031964001141e00c54204c0022200031804500b12250300d03001e0b040301c15035100c0c040c1c010140013802c60280c01720a10340596000003480070b9a1141055039810704a844080c0d0440c104010f400060b184c0740c1d21150740706100b40d618028010500d5484000d2002e0098 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 680072221 1250 680070971 680070973
    0x60f041802120615070b090313170d020703050a060203270604030201050606031b03060409081b12121816090c02100605010207060c050c0904061a04060e01050609060403050609 77
    0x54503000c441541480541d014030140c4188014034038001d8903010500c034560002c6c103000d056101045808806200b02c40f80c0191006903040741903214581c403145425200d0390f0b04000d01c00d24107a104a07600100c1c01004894018014189900180d140e96020754402001f809109200c03500d01130307510007403011405203201c44400401c420f15103450042c1c00c458014050034424041030041040d0184286011100700d02d00401c140c0c2c40c0e8607200701245c0a00070041c00202109030100d881044100e040c81d5125049021904441c003a0140003480c151a104000d2a94001800c10000503078901034140d0064821700d40c5400c41381d00c1124000c2242c4480e072141c00c004c001c5501c440d08600d0f915070410050021000550040000030315010020f96508410302c10a402e1007085440300080c00350622100e07544800c0904824003507d40741c50500020991a03e44401c264503402e01c00089003068415081a03c2030015421490390a00c805c102c01e40d0881840c15510180400010000401c00d010007405031080710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 680073471 1250 680072221 680072227
    0x50712080603160e0601030b120105041a070c030509040b2103040906090b030a1424010f0b031303051b120417031207030b011e08010801050108011802060f041802 71
    0x207010182044040c140c0c000810350b0001c4240b1880c103400c0c6105400c80310908000940700205e40214900101900b42c0040300d5290804000c00d00a800d100c1d4101c201048001d01d803a80d27902c52040d02c285420007405000120244144030050505a110204802000300908260501c19810f40016401401e11860070340001c02e0412841009020701da0241174190014040002365002003656034190480c00b400da4040c10342000e08100c010700c00b481007e044c00344400c08a078800750904900000a2041e180c19100c0800000740b6070307450344280ea020b4030500c022800e049655850441e8560044c0301000800c0030000c0384d6403014142042042d4251030348010759602d481c500b00e464100100020354030032132504204040c0c1202e400031140c05501c000d450038000392080401004a69494550030260041200c500246803603d40088519048400860003845140c0e01c0c0c0b101176080c2c410345c43c01c403c3e604041041c41001854881d02800c43c0011104080d8101691070108551850410b0084d145a41d800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 680074721 1250 680073471 680073481
    0x54e0a1805011d0f010c0b04030c02030c0103090308040308251101150620010f0c02033415140414100603030e0d020a0503100b010914100f05071208 65
    0x18242040c014482400e042102a000f202068208058080c0040c801c2c094210340440a07800b910200d00e40320303001151400240340919016005245880c0180c1c4a84100b4105008940c46400343c480e245a042d9605070041c4c541d43c0d01a105d004000e030400c0301a0046045201c500d21600c41c040b611424596501012030b151541c1d4203003141c805140410b00300580040c1070001c07030307001003100d94016031800b0318000f4024130400340740c010300d000603181c10305e64141070140752010703400405044003540701104c50000e600303000e42c0f00d014000410400001c044544484102045500034a020030082c00c2e00c000c01c600c4d8041da00000300000c2286c041b640c550b188581c602120808121007110040b40700810843c19045460240100c41d64807030303043c0b190401041d85805c548951800ca8002c040160031501800100713081c41002c0d0800b110901e0002d54500030003d00c0703240340014410080005005042c4038482c2c0300048510641d516404000e011040200000241504405409503401d82ea0b40034524200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 680075971 1250 680074721 680074757
    0x180d0309020a15090e180615091f120804090c0206093702030c0a0609080c09060d08090a120b0a0b06070507140a0e01080a054e0a 57
    0x1840e048142640d0081c40743d0103207980c01402107420740d1115a49106156a440501c415480b081502c140643c000c0000b132000010100310901515181140c09503026034455511004180703108260740d040c108111410489454410a5000d0b5a0302034480c0303915094560241c0741c00e5400c5103810000503400402003200c0c08905000d00c1c455920020044680c01c04011602488400396018094486141243e00d0085580800644c80c0064003d4134040c0d01c0e0b40c1e503410181c25000c1c01e204070855030251701b154003240c1c0340041c4542e110b680e004151441d13078062510f80e170781aa04281401781d000041d101d404210f00840c4c0c1d800e0348070039114100b0401e8900e000084041943c80340c91b400c5016800074000100000c0000c40c1620a031510000d40c242c901c0714070000204440c00560200303407081d00600000c40e24040200e00083d000d401002120b41c0c544542440c0b40010702c41262940940310380c16202060003060180310700701c0c0708a01110081c0f03042e010f481c0e00c2d01a446812240b004c680403000389200030311 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 680077221 1250 680075971 680075989
    0x1401080c0108040308060105031305011506030608070e0f06150f090a0f0302060a030e160b04140a03080d11040504020a031b0923030102220306050c190503180d030902 73
    0x5020b01e807546150801d554040d107034a001030141e605000001c0006122034000d00754100c1229080402230102c00c001c0d452a060000343c40c01000700290070214042000d03003000601e24101c0e83e040756404e0803969041001e0301d07403010150005901c1080313500c40c076407003400c4038001c0d1000d051815100c5a50745022002c00c1000341c00d0364066024003a10320020030169803000300351050310b40b441c00c0108041c0c0d0110405810a95202003030f001030641e015010546d04122409441583c2d40c4031070031000c60072003904102c2400c1040c0700003044040c041140c880709180a0b080003070050340e0031380000d0400791107500282c00c0ea00034800074000a9035500ea03811f041000c600f100c0003c03020703e05010b01340314140740e80582d4070146070380d5802e0814001840103c194401b541212200c108101c44003a2000d42080c410841c217210344000d843c5030f428032010901000e1410119201c0090480c207420068050120540e6240c00007408062150003035940c2c01c05200003407003c01e0076181183c2d0002a8070b1490310401100d03413 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 680078471 1250 680077221 680077243
    0x40b0d06151d0c040b070507031202100e01061412010e0706050903151b160c0306020403051b0109060f0e090405210c0d08060a0305010908121513050a020c01140108 72
    0x2c992401801620349040301110b00f03a6101400030b0350784001d50f08209152005550008168015030325011030b02603800b00b48400200402d050034000401420030080c280c6100b401608816400c40c2c002c2010f5207402c0c0031114200b07800038008203040081100c65800e207010b40e0b0054021540005e44501c2c54075060020425171120b1100120060400706403a11080d904c3c0f8031a140d1075200094092092210006a04e0b5040d622244c040140b640340e00c0c0200194019100889680c4540b12003020010301c0c094441d03d2032041a901d91188510b000700445960002c03d00c600c0070b0100c0c68003d51003d883c2c203040e152285000d1030040008290010444001d88020502c4407900c10050007204d00f04a808a9075101541c010300e00000d5075200e0200003101c034001580020f000d0b610704a0359030304000c0c00c103003c0d04c01040404920760850381d803c06c0500c0c1c07401030b090a0300c0d4090051501c010301890281e0002c0d80041903c2c03001828031606845090841e4221286c5165601c0544010090300004006104e214 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 680079721 1250 680078471 680078519
    0x11072417041b05210613030c031202040503190c06051e0309010e0307030305010801060e06030d140f220b120a020a031b030c1715040b0d0615 62
    0x5814162000d80030000540020803448a501e0000b426001c8a034201c406018018665402c3d0842e00c420002e0141c00e0604160181c0200d02c0001c607004444440f4890440c0c02d522800f545804c41d07503045a1040c0b404608119043d4280004a22910304116400c0c00581070000b010180455040141c401d0310749070b0004040081c20000c2410045541050808452101007042e4a0b5160700000501416202500d15002c0c84082500002d05926400003812100404000c010544e12034842600c070030411501d0981541c0265070340300d141d82c410110300d45181e9164041d02d041c8440c481c84460540d018070035000580306d00702042d1002050031103685c001000c0c510880f5141c86041d1490030556513005007400c00721030307002c540503000300e0103600711040c00d81d03610741d03145110301341480301900800000380c1020000d01500c50b05150368034010311203030050f00c142c400e40d9104000c0e10b0400c0040c2c4000100e0680200e80008460001100ca00840404030304041c0607040702400d08404421b0344108941003c40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 680080971 1250 680079721 680079737
    0x191a07051e0c071214061906080105041106070c0308030106050c06060f030c060703050d02031015141b10020d270c150c02100e03010c0519050901110724 67
    0x501d640007500c1c908880a01300400040307441c90600070702410480080c508240150801c01c07203d190103025200c143d4525040c01c005158580c032183e401c846048400410312680410141e0b0149003540c050812503104075800000e55480740e99044243c2c10a03401480821008100031140540078082d0641c00007050328490011141c402c0020341d07034080b44180034021040054030a083c9407141d01124201c001d499029543c81c18aa038011110826500c110503200826107054103c980c41245541490000d6034101410403021500c181c44900e540001188684038132140c00103030b85281d0001c2d101610000000080c1c0c0703000d9004442c0003140c458000c0b0900b00401c4129400a0341504884041d03601c00c080f5548000b9416000b658030048404000c2e5201c0900c0f4500c0700e046030701c900c90110010094000b40001101c1c00c400f41c80c0e60042032804824644d110204548080c1f0800c050b11042005151aa100c0c0c1e03c84094142815421f80001c0c40b5040050329903072026601c681000160141c501d41445 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 680082221 1250 680080971 680080987
    0xf17130503120409110408060c07030311180402030a020d181b0e0a1104030609050c282d1e0509070f0806011e080f010b040503191a07051e 61
    0x460b0f4420780c090380c0000d5642d1540c43c2c56001d502030646010303007019422941c2c01d007080700e204c0070030740c2150380b08400203420101c00350000808081950390a42480e11942a1014510104006900010403482c19030f6428098246002041c2c060654803400c5189800c0405000d0f040590710a204103000c2680b074024000f04102c89554035614a9110840d8140000c103101c44d818804031501c180c0d071028000600345030460b024018003140c4400703202801c6650003040c0c41084c281581c9421680082c03940000c0006041040c0030031000c00d10003140300c000d420003912a08241c00e00035000d25030842c0d12018107011012040301c0300800c40c080540411501d800a074500b0400003004606080c404004006c04900401c880340d01800020b40ea12038a0100c100c5031005202009150a40446052003903900c82c00001809141c17007003c60301a10405800303000a010000f200516082d5880d00031109000400405125240117064040c0101788980da410341c1d91200c0d203820010001d0303002811106000030803641e1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 680083471 1250 680082221 680082253
    0x609050607031815120b010206010b040e0603010b19030c050f0a03030e03070b04060e01020c04060302030307081c020f03070e10081503010906050a050414010915090f17130503 77
    0x754105074149400b45450942c40050741044a0b1070b40315018005001c1c48140096030020080d00d005403000c0340820054804800480ea10b203c02c1c411214030190400c800c0c4081c0c90020a8a54808400340c0045000301e1340802096142991004011402510010500822019183c414000e14048458101c1000d4400c00076105426511001302400001c610039031803510240030600046c02c10311802903c1c0d03a42e60401030300c80c280c14485140180140f990111007072400d4802c00c01a07940250003142403403d00d81d500741c0540e0100c01803440410394a0b49810603244640000c090705009503131342d2600d03800c02650145c1801c040301030b4030b48a80740c400b424000d00d550041e51598402035000c02d521101a0001c0800d00500740340c803010301528201000c100340700c42079800050041d407142d14111803c04421340080d00322447e42d0303402002030609c41e040c0261900c5c150030140456001d0310444003060f4060b56801030724802113103485064003000c69081d110080d40305c50000200b0040e80a0704002090492003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 680084721 1250 680083471 680083477
    0x114030f010509070e0d0524040c0b030709080f0d090501170f070e06160c06050c15101205060a1104030206040302043605010510060807030b01052a010606090506 71
    0x614007549501001036100c5115612039030304170384044d12284142c00f60f800e203603841d41048004003103108198a00c80c14404008034020780310302c1c1c02c140d1030002c050501c2d00603c100c3c4d00140940301080000c1c44007080c07000d41030001281064040c2c0080115500d0703542c1c00340542c800c0340d00c03140c1400841c0c00120f150020b5400203503030003010304144001b9a0b0340c54009072494580088165040403000c2035580c040c3c50840418080c0d140075274104489155070b520211010b02c00c151103d5038a8101107991924040c15002003074200b18483d0311010442d0300ca011034101d440403260151019800034050180004d15071140158080c1040301071868941590003082840c411880024010345c2e440310305084582120102c184900c2140840079080a0001c00e6071030305845550050701d40e9403070b103008100001802072000d000c840058076039204540e240300059004023014801503061140402041d140006400000c20110042515924020390880800c80c2165083c0c3c001c1e50a01640c5c050600050390b804048d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 680085971 1250 680084721 680084729
    0x10b060a050d150f0915150207031e020d081b030a0906050d02071a0714070f0206030a060b04060302071a061c050307060c0c02040c0905010f030c0e0604060e0114030f01 74
    0x450f000043c00100803071071455610400c07640d045000c1c00b040c0c000d0320303070043d0100e8075140c1826510261503003408a01c00009000440250788459002c00004112508601949068565200780c541e103a8003c10791859030000c049840701da0014448030122001c4030024440c1100c4001182010a01d002c094815120390207001d00b40301b4041200f0340d1b0340a268040b242070540c0545030189c5131403490b4002624407400d1754017001148000d1500d88800e03000205540e100d680000464075551195005d000c0c0365071002d1710f40701007291502404100b5000c184002c1004295954006968000038104880119184800d4101c3c1202d014240140340e0307551800e1221200c9005074803a00040355140c482c0c07640c4280b1400420f0942080310101d0702c507400c402103c240c24029101400381900000c02100c02088501070316004c01c6c034201561820502c680c0c0080e505224906041100312008000a00d294000f80d00c100c3c0050400106404107507400b0302a030345a08000c2d503074141942001e5210119541050103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 680087221 1250 680085971 680085997
    0xa230414040f0f02040806010e060f010509040f0603110310020c1209010c0f030e09060402160b0a180b09010c2102070c0902130320010e21060f0108010b060a05 70
    0xd602030040d40c0d1070b4411903a21129202c1040321071241004100070313400c2486140b81500542d00002510500201c40600c00d001c02008014800e018074019945074001c00c40711a007295071790188600a202510590014600030903410010351010b6082602c1c258400b00c10380c1a1500612040c076034040c00141c20306a90749c8241e001500d40c0031400040f02c86404c00500a41555070111030030050580107103040a5401c002e54800c80107985600c03d0006a200b0b8003c00c0c203548441c403c421010900d03102407250003d030b1719600415441c80707606000303055451580040e17a544400c0790a010803412309105250094a00d4101030542c400c554807200341c0000581c0b15061900c0d0001341ca881004a62082400500700b00c503021515132405a60800000001c3e000c00c94190054801e10102c00c01c030300c41d049000c0c000580d17400300d40240e0b030030500031009012115200ca030350a0003400b100001d000c1c40514411601140440d20540c0b500c00746a0030f582c02040d41c24080c80381080400c0c982c07584501200c42000b0344407 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 680088471 1250 680087221 680087249
    0xc03021b0c15071110021c0302040f06030b0105180a18020c060a060303170c0f0406020309030f06062209060606020f010c03091515170102040e0108070e13080913020a2304 75
    0x2040130380c185801041505c0c0c9a80d1f039010002c580359010f07406172007500c00d038141c01001a500d9110503800c031800481c500b400314a00f44000d041104245c2c1008101d014017600140c07100f80ea540100c8200609002c0b2880b909401007050405270104200d280c0e4800f2000500707000d05031941d00c0c00340030b508081046402c80c091500008403c40106000c48040200303444849946aa407104000d450b80c01080407984603001d0b020301c0c280081c400207200346c001c02c0001d008084200c8111a02102441a8038945801c2a11240d00c000400c40c1803180c10000c10f0241c020740061010400c1c0d45085424007000304040c5481c4c8094480032800b212009030201e640101d000800e0b2039810704280c1003100c564011007000da00201c1c0d00710601c0c1d040d000351045131901e04071228566205c213030240d1182110301403c1d95090800340010701b00824880e00c0142c96018280302444d00c0040c0020030810301050211028058000400b0051190310404100301c0001d0551100034011282104c20211300c12446407140f04044170b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 680089721 1250 680088471 680088499
    0x2706050c0102070c0e1815010603020a0903120819020301030308040f020f0301052d0906220f03051b03070209070320070c06080105030a03020d030c03021b0c150711 72
    0x940c11903c0301a0059440c4090704d41e241410701c2400c00403071300d030382001201c0c000c5107001c00340c00241c40038981d40c07a46d59140641e0030070100328000d4006807107200c2080340c0c80354004081303000703403003c0800c41d030103999041c84610b89200c031820403e02598030748071003504c1000104040303503100786640c2d0450f900c0000059440c209000180c1c54009140126505502c7c210034441c0704001d0741a0380e6904d4030060321140070504813090ba860300000c21192440d80360030050018220074180d085640d5203c800202284007403205444020b52040800740481c00300e940041c08034603007031440000389890405a401589090084d50100ba50b4800151030b210515845400c40b90154903000c0302900300819241c902602c86400f81400c64040c20284900c01c0442c00410011850b800c0124085192503019001003e915001301e004030001c00d0f41210b80d1003090350a000000b2068041c034010072803540e200004100344000307282003207201c07034814072541d401043c03c1100400154940007498039a40088540c40c4150010b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 680090971 1250 680089721 680089723
    0x109060e06070f050327010507030207050d02030102040b0c060a0f180f2f100315030b04051501091401050306060f040b0a080a0c0806070c2001111c2706050c 69
    0x92108020b005000c00b1441414000342c3d00d0003080c46d0701c9407101d01290200d181006456600c03d90070040c00503003102d58188110f0070103010b18191548040c000500d002e54503101c0c10041d421141040c05140c00240a00c14021000d00440501480c0d50030b003048a40c11900b041c03003120070084802801d0901c640e28900a02005010040c00d1022900500707000d500000c84444071a08501640740c80b4075a51520181c1d42c038030a20940010100e41140160554219185e010182c400107008a4091244442d00794a03004800e120500034201c000f0007186c100c3c144c1800a18004050304841d000b40c0c030040801201d07641e0180d0003c60040240c400090340212800400e0f10030b1a0781d0071000580c414000c40e00100854800e400049407464002d43c0e0131a03c910000701e94140c0b9a510185c4181800102c1d80710480340354800202c0c0045c14105101c1e03c602403104903052282c40959501c0d500e030700c40506414250005807001800101ea00b003090240e01c41200368501c4031083c01204208100400c1603240060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 680092221 1250 680090971 680090993
    0x120c0e09070c0210030b130c0503180316030918111c11030720060103110f01031409070602010627051906030f1505150907020a080d050106030501050109060e0607 71
    0x40c024002d50440c00700d940b0041c01510203802c805000740201051f001e80044a880b80b850303112290313a250f0345140c45080e044224115422284404c40c00308000f00b04104c00c00030001c03411540b1079200c2d007501e83c0c541754079690103005010000340180c2c20034031810122514142100e0900c15021810940c401100e0700b070800030305a144030034800c0c210010a00030301075042481111001035405c0c169420248401180d5202c0d1001c2c84000c00070217803c1500e040500e030000f07005140000600d00019007080b0b1851200d0801820b0b150001030f5003041c2018024650f0a0181c000608036064004118000b08408540035821000c1040289135440c0c0104801814011981c070710000008024040252a4113241e0701034a40182c04030703a0150680d450114030b44a81c051f00384100410091580d0b0340340e2980501c9050180144600210b02401c0e21600000340040090007a4070301d1a03800003201d40c14020041c0031148181c0019040c01000e1b641040a0703039101d24055018a425a2840d883c0e40f080c1c600110900c1e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 680093471 1250 680092221 680092223
    0xf080903040f09090c05010504060914040906020d1a03010903090b0f041203050904050f040305030a2f03010e150a03031b02060406020d0207050f03030a030e0a0507080d120c0e09070c 80
    0x2e019100029002d075003030700186925801200d140c501c01c0c2e5180015039041c4190704c15007010601d0392104000c00c294040700c000b81103070b010b000803401c10815601c00e0126400035444003c080d0f5034008041c00450402c21103400b00c0b805038020040c200301620080c00d480d1130f40c82031030102040040c954207502c1a000c1038600030801003001030301e0300c40545006802c64211080240c081c2c0d142c0000141603203c4420250f020740d4042e250249981c0741d0311748231000b40c00f440c80e407030a01c2c100c0001c00c0c41902040280d0030a20103941c03240251a54140005d40b068171802400d414282406043c0150359543c40d0000030007141d0341414844015601d56080d02408180164041e6011201050008075140c01080d44041d0701422b50941d0519922002049044003014400c0303a0554803d2000c10740403406944200001c4000004035030302115555901841d05141e40c08c094200e4100030104502c643d041032030343e40d40c3d100452061010340742c00b940050914200c0550300d4410a20346c00450841070062100090203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 680094721 1250 680093471 680093489
    0x14070516030b0f090312014b05030111030f0907030219180608030906070302120d0603170a020a17090901090e1002130605031b04151e0f08090304 64
    0x103965a0708044a07040c0b011200031141c07064810008103441e101108035100742d0030710f4100c084181d0a10000c803103402a0107142c144c80048000e1101601150003d4000582c03189100540140c054030311004441c0a02e81d000328001e81c1003074589030601420006032940180c000240d41c00e10b60b1030300c4e00285040d115038000b0750000b071110354070340c03d03044001400816a5184000504000c0001c0b4a60003150150322507041030b500180280e94461030700350001c02e085030081c811680503005500c0500000d40c01100c558641560317030b081c2001002202c00c4800b0103620414052800c0c901c440700040c0d100d04480d04c0044c80a4240d59002d039031404403200381d13211480045c22843e000d41e140c09140c1c009050340c0241000d41d03c140c04004070038585900032124003160007039451000501e42001503c05402c050644038501401d19007400c0d9680b10a0060310080482d60b0300c00700c62209100001c2c0c8103d02c80c0800786542041051060720701c5400008510200b101850110195550303ca540c5003503000741c4c0c005c0410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 680095971 1250 680094721 680094763
    0x927010303020102091f020d360e060d081c020c010914011802011d0a12030f090f140d021302280c0b0c0c01020409050f0a060503030a140705 62
    0x18940d056000d401159001e1b01c0811844940007441054002c91040d9280143e01610b00d00761301c3d91040d0500c14180304203281c00510865084c0d43c8030110603070240d5042e03550303540c82000c101c0c0d20300e40e0803095045401912007004440d450f132034403403451055a4480604c03031040d02a2028800b216411500715988003402041128154078000e141810003200d100607660034508540a1908840c803a480c1c070550584035074140f00d0740521000040d10011700071035030003280c41000180c01d0301105c0070114010b1203507494628610340388070090f290714041d82101d20200103c020038402140f055074411860441220002501403251001540812541c0c000e012107c0c00400c9040301d074545d0102c6162412407183c0040010304208c230701220300089064024010882840101c2c2c41750b60000c008184c405e61101c00546000d48a950b00c0041c1e4500391038010440014030100504000f4508c2050080d00c8110051450021018402003480c41715182514005030300150301802c1080401507806203c0d4040c50b5904 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 680097221 1250 680095971 680095973
    0x60c02030708070308060a05030105070e19080a0c0807230409060f3e0a0c080408070f0e0a140c0a0e0301060b12101521060b0310080a0809270103 64
    0x205e150400d4900d0b6000e403410640c0400c0524041c000c1d035109401d00e94809020b10550010840380b6030765140c51100c4d410f144980441d07a00f6050010383c0180303000d040c0b4600001d1420303075903c0c81c10b071541d0b00104c100800003010320580800c1c410710040c49041283e020404e203000c0d040031303c01050b101c3d41291306640b605500c54658540200900b0060350100190305802e19540c8440e0800061210344100c1044100004440180944089040e2601902d0082d08060326014881e203004450b41094001c4091000d042060081d45081d4940c040d000c60001d02140900168172102807002600300d070008200415003148062085090310000a4002d00901001d03658000790906940800e801e400c141d400303c40002d40000d0b101e503ca01c100c039880000320b584001c460310111104810500380c0b2010a5403a0b00c020201140c80c0155400ba0001c8580295203042107405036010151540c809d052503000940b0391400304a9104c00e44545090a0341c128648002c50620440440c000c3c0301c260300c0400484c00040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 680098471 1250 680097221 680097227
    0x5090c0910080d02030304080304080307050d110304020405010b0705100f2304060b0904050a1212091a091203060d0305041215200a1413030f051018060c020307080703 73
    0x7400b02c50300d56041e909022842d1104985a100480740513111a0040010400040b201401544e000155103443c03401c1c0702c4009030034030aaa003030030401c104240022050005620f0241b241c1401854507019142c074002d015544d05885c1e10340160300c2040785070360701c0c4004940da925402181e0320815820780e0305440d4002d880d00e50f0b40b0088c00e80e025549907140010000c03190030803000182c040c680200041036042000c0e0307151640440a0492030703041114454007609500350302e00419010600c14a128506c0442400904a80c068010140c02c210380c041c410107038244ca0071004580d048441a141c0003103401103800c0a039503e10440e440b000d1a031080d580ca078000d00035410600030545491010034816a031440c40d544c0748002c40e250343c00c050038108100070084107000300d9400707403001c81c03a00342c090600400840152480d22554815281c8a42008200c010400d051207070901000c400001042080e071006580f90300905400d038010b001c00c0da1401d01501ca14000c106450302c95910044480d50f68000c2d203002 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 680099721 1250 680098471 680098501
    0x50d0302010e010f0b1e040603150c11190209040206041710061a030c090d140d02121204020d15060b0a02150105152d0306100c02031005090c09 63
    0x1056043d441e100d840c0242c501203000e2840d102c04001c080c5810b60490400411642c01c030b8643c004e601545c0c4950010010388a4010090b00c009207640003e0144849180689203d031a00d00f801c901d9000602004c5094856000200c03c003034040d20002a207035920701c0420040e11445c1c2003035007649201e070035241002c14001010a14100c2d505030034401142c0c1e07800d0307100c6101d85c18034042207201024030004511810010290214010007407034610905065210041c2148113900c2c10b80242c3c2040c2641113000341c04229041c1001040f81405140400c1c900c0c040000da031003d080280703e06e1100d1005001d0101070700c00c0000292032002c081044540c0d40102d412242c0c004e10125003d400f5107038442c4480002021100d04a507001b509001d0440a105920b038101d41c0700c80740b185000c07001300146490b507454141d2070080c2c40340c0c10140345660781004e4080013070f204c50301082c0d807042292150705000161400f180e88034061503640000319141c0c5485540d00e00700099040c4480d0003d4994040214045400400d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 680100971 1250 680099721 680099741
    0x120501020715091208371406040b060705030a20060f041a1006031e020d0b180705090f0604031a070801062a05071503020702130c0e0108060406050d030201 68
    0x2c210740a01d0540f20940b00c000007150240c12103c40180c21992002020f0164810000607100c0c0c00f1b80700c1c2c020f401c1141224418000070703444019220070001700c0e003840e1082c0b460b4280100c4c3d1603400d103146583c0d1240d0f20f106802212080060b01d281191340440000b1030807240c40018800d54805281080d51b01e140301074116810f68514194070049171248034130150b040c0c09210070a011500c080e00f40710301500070b44401c0b5103e500c0c01d1400c410004100d41e1b288050804001074100100f1409222000c1002490310804400b40408010f0280074040c0d80010440b0b607003007000e07920080100b0042000980600480d40054480580c4418507040c680c45403101d60301c24203050710b03920388503600d5032030444040741e01d26801d0f40c0c0d1402d0940c10000311f6072181d038102040d5201d18100c40e0815202c044202c4030f03883c0304600c034004c29000302d00082180303010005c4940314650f03440104848028148014803c034100584203040c0001c100108945842c0c0b60441c00c080d01024090001c000598038000f40203010b1150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 680102221 1250 680100971 680100983
    0x603090804140f092a0304020913080d11040801050109020a0c03230c031207020f1e010e0118140307030f0c020a0305010c020f0c0a1a0c01060e0103030309020102210412050102071509 80
    0x19201000e03401d04040c1d034011234011f41454401c0e60380c000500080c1d0244101625030a00501c0040c60410250180d850311644003200c3e59160f503d802019429540117800586c45a4018001034520301d5120460300c0745a80c00d40350114041807616031700c1a08827442c480847c1c3c030381000030b1407004800c0000003d101c03105442d600d603002a03550340380480c2c0b00d407481211000d154008117145c0c40700d0340303101c0301d6201c00c00c1c0c140000041942a49041c2800c45d42c0c1c910001c0d07220500403644c04203005500e10b160041b00200000f4600d0300c0031981d0300502c00c0c0603090404040c482100e0040301075480c0c03038255901841c1c0c040700070040d200a24102941d079014002e19100c03184120010f020480c10075a0411084680004081c04428078028808a140e0400e1200c120603641e104000581424010b0940e4025800303a2000216a419800028144103d5400c203a19242d09100d0440510203d4811102240c3d1012140030080b0340390f113000c5000e4842c1080141114105140880c403c503082c4e807100210601c0341ea = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 680103471 1250 680102221 680102281
    0xf06070518130207052109131508010603050d0302040602030d0c0c15022a1b1f09050a0b130902180a0e060a06020d0f0804060e03160308010603090804140f09 69
    0x105098198800203184001d080500340221fa001381490298145040f62418001c503000381d01440422000c1a15804112242c0d1a840e040007448030600c41424034082038503095151600f04003029640b485080205039415507241800708e2010701c649246003217140d20101d134a800064214842c40030350810030980030341c50000c0c080e0704040c079480150f0003d150140800f510751201200095200d404218001740e40107007007200302d00c0e801c080b400380c10b8007140b03041c0c2c4495202a04000c24850340000b00e4100340729480302003004200c404a840f1401088906040c0003690704c802d69201d080d50403103061111a044080200b02180c0c0c942c501501c0d134807922065510400441c2d40c0d170002c90751160005800008900e41403600c04040e03104611072980070b4090800460b42d80d1250790910300c0e40c0d0150340402030f81c2240402c2801007580c00400075004001c41d203014040d10003540c031005454402c62043c0c81031680703821900c003100d445100030070a8000f001400d600d00b901e4045860702c0050040701c012403c010b01c00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 680104721 1250 680103471 680103493
    0x90907061202090919090b040b040b070e032104150914030607050f0903070e19150f2306030c0414040603080702041a12010902030f0f0607051813020705 67
    0x291003660f5202100508004194881c0c44440d41d00103142c403204041141c480c9010310218140c3c00c58207000303503ca801030044038605820000c14464001d0141010080d60004048540d94000342058240d01000b00310040d084c00542123000074800d80d806112040002c4031568074542d00081c980044584500c100f5480a513100100350300c8800450354000420018826103c0040785113019080502c03003d0102c07100c0a40f504480b8110582c00c403104011004400b491301d14400c06406901044801c41c8440c56078641042d0302c803003500c440c0380200f841d05004808240290110841580d03031000002c0c00a680e24200514032009561090140c0700441000b8010003030241403c1c031800d002c40c0e42003036200b0705001c815401c00029146080c880b40707020f034050701a842c2d10790703c00c05400411510000009520b035214814103040040400b0110035070340210282c0c0c0085240481c80703550100e039a180c03166403044e10109401034480540205600000c0350700280050300b4956000740f078418014802c41d0211114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 680105971 1250 680104721 680104757
    0x150a030f051e0610021906150f03060f0c020c01030c030605090c0702011e1b0212011121190b0312040602030711060313140a06020d1b020f06011505070209090706 71
    0x14140c8801c0041c0d04c08286e4182c1c2841840080301a076100d03c0c004149001110144620014980c02000041c00c4015003001001454420701c201e500c5400000c0c486c910054002039158854103017400e052648601144111038402e0b0b0001d406010014203503021800c0a070f0f045041c89d0409181280031400c0020160340700c00c00e00303006994031013566880d68610304d440488040d082e142c084080381c11500c0e2043c4060b282c0804e01815507485440c0c00d80a03102c40b50900b40c200d03407403410290309002e003410905002e4030041c403000d0715a255844000200755119120701180c500001d52080104941b008180030801c0d90713001c03005143c039900810f424800e08401a00b00010342c4801d4034622100750180d8108000240b0750f95200030101d00c90000d81d60a82e2003910780d64241c1e44407102040080d9a02c181d110368030542c103040082c3c6003100d440100000084e03149810756902044c010304040d0030000d50b00042d040e114100f12044203501400340c040c1401c1814140b41d9812540c0600760200312144008a20158 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 680107221 1250 680105971 680105989
    0x1005040207211107030210211a01030b010503010515121801050a0c05031b0c0304060e03100b01080114030309061602040b010e0a0306150b0406210209150a030f051e06 73
    0x343c0300014140702c51a6078208800e00403000010000c1c007560082e21582d5055461005032024801d181c003240710b100724540c1c000e1050303a0100e08d0341498508200070f4a0740c0d9000094a05450302502c0c090150010030140aa0301d000d419000035a020125003000014011458100b10040302400280440c3d19120b01d0003007030710074400e80b01001078010710014046040112150794131141400e00145043c4484040d2415035000b6004640030900413400c5142d141010001001514030800081240046c6480000c10b2050180700c2c452180c000700310101c0303803650140211020900002d02465490044610802d003d40401e44140e02c114a03058004440e0350044541455507400140052400e07030071690340310300600c0042d030502c103030b2408540c2c08101c80d40014014009000300d41c460340c4402c3e1554004040c616450a040900315005000d4101946c0300c0340c000015201500402c9501d95041100850060010f01d030f2450030b1600342400d1100c12030080800d2251842c1e00100010b195880e10103200441e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 680108471 1250 680107221 680107247
    0xc03080a0204030f0233090102060a1407050a03140f0105041d03160501060302210708071d0a140f072604020f01050f04030516050f0901050603100504020721 69
    0x24220000303500c01072420060701218500601e0024118034509807000046c41907202092842c0c1000080c0c0c6d412070740c0c040200039031002d11080e0500c502008000381e1500c1e030310084c1c00c2c80180700000c0742100c01c680c000d80000c0994200703d035080303906150031540644848003c0c407809005d5450030207844030014080019124110f01500150304d400c40e900c0e03a02c01046c4d00317210b00756481d560381d89011005955401c44000d0214070540c518111881603c0031310700300045684194141c0e405214100020701e040228034400071000140d407030460780d500e03d1400192407100007048a030240c4c0801c0003400242215514000d03421035917428810200c0703032240013403d02c910f07078007503010200306002600514002c40c03280c0c1d51650601d080c5e8284144040c1405258105030012681904100c029041240c40144040014502100c1d00034003145030f01d01291004106000b1240629030000025031202000c001d140d009001c090402c668403a03050400e8001c0c4100080c07005500c419183c40028024800d056100d150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 680109721 1250 680108471 680108483
    0x90b0702010f1d03060a0f051008071509051c0302071d010504020d0b090f06010f05090d1401110d0219030504080313020f060a080f0f01060f03050408090d030c03080a020403 76
    0x80482d41e07805441c0a5001d220854031400c1c07208401030280c40500003117020b052418804205904149000015202c00070541072892a041c1030400207c00c000450508441800c1004051304030042c1040350324403860b03008190001e6001202c150801c08643e481071440703020340c0c03d0b15851910344540114040010f500300c0e80182c9048014021031400d54001d0421100070b45001a0038108000810f444160484075001c0040d0980d00b04140355800c0080004285054900b19240100201c002242c0c900050005483c811400c1440c59412800b580191105c03103841c0084c680720007401d00040040d60204000141d0181c480742203201890080c00b4060165911101b5107085541d000260315600d41070321416648000003034105200e5413101402084200960b6807030004924140f02203000366200034107010700660800340100055a8400180c0900c500c0720325010580d620703641002020750240042044e40584440c00c0c5508043d00041e81c281c2042c802e48600340702c1da855813100d008074081da110141c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 680110971 1250 680109721 680109737
    0x206040302060c1c0f090c030803010806060409320f0d2d050c10090c030201030b030c130c1808010b0a080f060112031e031a06130b03131b06090b070201 67
    0x4100746401041e00c4002e03400300000da40350303071b80c4404036083c0076072340142d446500000051081000500001354061001c0d00d05000304c041554491040e1051004000003c0c28018140b00342494130000f03c1200301a01c004507041c604c50082c1003500c0342e03240c0c0c0b03091002c903a02d400e5548800595040e20b10040f240c48030445014030920006032456888000200101d004119082070b510810307101d00800f0724084c45003000010705500c000b500310380c41600c202d84294089002c0d050a83e40d0002112902d04c0002004500d00b0b85d001400e646602d082d000e0f000344550390a401040c403d03815031180001c0103040302c100c105c0340d564540c0c2c0c94507140ca20040c060319400800050204101b0564600151842440d00030000f845003c0d840e080c0d4000c116908000945030800d010310110b103081c1c01801c1c500d0403036215142200c2030003a04088142482040029000440020010402c40001104031078102e980000614840703405d40b04172001900a0034007041500c88041499268401640c1e040c40d07040c1c40301c100c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 680112221 1250 680110971 680111017
    0x503030904050c042c0a15170703154107050c0a210509090415020903030d05010305060c0a021b03010204080a030504090e030909240409030206040302060c 68
    0xd02030082000c03c1441c002c1000040800d01009145080769032004000c0d10210350020054a0713440c094005003200b0304200e140240368001c1000d00d070403200780c29014102040c0c00d07084182000007591000c4c01600381140440300340ea0729500a48036074481c460041d103040d4916013034130074802c072001440014841a0240a40255501220503822860a0078401d06100c09221070382e00d4000150001c0b14070110a00b41c554000381440c0c040d160780070460416505200c407000100c2d00309000148007505403444407407560300c0008554100d403800c8a0207800d50707aa6409101c518401340c50288400c1390548111000501098105025a604c0c2c405542c090241800404400702e00c00d20807401455044d5420040090007807000c001010440d4801e0315099110f52034804110211030580c51001d040b600f0802c088000c0c0d90f92035081507445007038441c983d4907010400f00481d021b03c0340d1260440d0040d2a0115140c1450f4000604c1d0f4410b07842582102c0c266515201900014016040d013031000c0100342c25188 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 680113471 1250 680112221 680112229
    0xd1406180705031f06020d020105010609150503150a0b0a090603020a05030f100510030b040605041103070c0614070c060b12280537050a150e0114160905030309 70
    0x54029482e100c580c00454024505100d004c0203903404103000d41c1c801d4007810421602070050a0044c03841d42010a441803130030304445010808604050200007001000032010b80d44070000c0c4004000c00340100705000d450703d80c080701c81d0f440307480c00b8408501d490300000748051180c000c482c0ca01c021603a4a60850b00d4840112031102d0303024040c503a145110900c0031aa6841e4100e1007a010360345994040b0703840d150002440100d030015009a4040d50400103142241407a030000c0ba900300318146071566880030242403a0004002991030303510407540d0b0000340014242d0007a484640d20380a104100510b8070600108100d05a856604035155000a03a40d2410410b0400c03d070090ba0368800800d404d15141131741c55900308485440b0040c5940d039040c600d401c0078604212040c1c001d00d001c1e000550300008585545035242280c0e4801400080c0110840e100c48042c0d80141c0d500c05d65000081c40800f01e10400001130110881d00e500f000c008a0401740319581c840d9070303a0301c116a4040c02441c54100201c00344 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 680114721 1250 680113471 680113477
    0x140d020405060409023312070509030a060903090923010603020a0e09010305010903110a0507140a18050105120118080a0306030f0302070302010207170d030b01020f030d1406180705 79
    0x2d20f5205942d000c1070f0015072a9600484a0f182050a1010900420322095070824031421010303041008180210181039258445c1c098100e503503270030602c4d21041a440080e1516080910041c012130420703450f0b004050304a1441015120030b19003d00c9540403000c1f0200075a0380d8000b8481ca0340d50000f004002d454043e034010310300b2142d41d1508100c04424031002c00d04a50007030f0f0044503035a41d2000c805040c154011070074140f1000040c003610003a601b40c2c8800380e498015002c1c0c0400784401804022040ea01e480d0040010320501030140d60000e280780c101c50081401341300e19400759080d010348090300304061056031100000b080c0c2208031514a5120240560014000c44013070550781c040100c041004100f00104940c400d5000300081811880020b013000b001d5404800c140014016000f160036002c2103c2c85400760502d00003c00002a0004030720b4040d182c4007040c0d450000003802d814014881e00080d01c601c2040307108040301d440d00018420b0007050960f1100b9100400004181424400c3e401 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 680115971 1250 680114721 680114731
    0xa092609040213080f06060a060807170a0c030e010b180a091403280c1401090b070309061406030601030b0a0e01020d05061903110411040b0a0e0307140d020405 70
    0x40103040c540e00501040880c1c0c41404119001010700e581040303000020403914251008000250190741402070201313100c0c0c9414040c1c0d4042c0401c8000150071140316084a004001c0d04084d8942503003001c0715524020002c5003080c01c00071f4103140425508032014000e044503c5006001105c0704000040b201c40605006050303680070540383c00c0860041041c52080d202e5070711000010716901d84690103500703040005080e02e80760384081030304101c1006401465501c1c401d0b4025000c414001c043d103020a0040180100041c100ba454409100345283c0c590b006800300c510400040107020090391300300c0c5c1e09080c2125a5503256004a00500006d810920502d411010a600c080b81d032510304040305082e80c100803013080e8190383c1c41c403c0001600e40701011513181e841c2100d200280702d01310b40f03840c000c280a503081580a143c903061400030811001c400c0b03800510292822507203d862504004201104d1004118440e120340031020031100c0c0105010024224001d0403802640003550a02001e400000c0c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 680117221 1250 680115971 680116043
    0x60d020112020a021c03051f050a0302040f09060912090909050601050d02010c0b0a021206060a0210020a09030b0405030703021627060b18031e15060a030c09060303080a09 75
    0x380c00d5207170181003040b010750107580f91004030b00c81c0790058501c3d40002e076511100d90a8050300804110b82e0300d45030101c400740c90301640c012581d00292120342010341300a00d002001c032498011584144441c0c201d40100c1d00100d981c40c4441541e0390008030054400000c0007030700079046600100160328140d041400312501c181851071010f800341d240c0007003006080307a82039a80742e000100d40403a0a0000310880d44040103d82017030400020120080d03980b8241d56000b003803583d0024014101c24010b1080c00001c65105d004241980307810701e8415240d421050088000d445000c40c6070484800b09038005c425502c58020301c2c0034010440c000244d14150b10032899950b190740308008116a0150300003000501c04240b603000b5503201030300616107040076900e01c48102d11200d44500c141e0035000701e014882803051700c403010a191240800541c0314030641d40020240c405070311000951401c15040001268001c0d200c0031501c3d0b50b07855503d01070703450145000b001282411000c95a951840080b0030510360101 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 680118471 1250 680117221 680117233
    0xe04021503012d2102060d06030303021206030d1d0112180c080d0509040213080a0302060f100b030105220509070e0a02040b030621011112060d020112020a02 69
    0x403006034400c0d842a0401810f03084980203121042c0d000356441424207100900c19440c0914114040b01c40390240c0c400300c0000b402021105065503101800d54500c4505400f040125607a20310300035000f584800700b140718070407407034001540c6c03440c01141070175445031246c81d00006d0715000002d680e0090070710b1041606121801c81107e030900b50300d2003804108811610440e8241485041070400d40a05a0000201e0790000b245c00b010350341d110055818801003510b0145e1204504100c540c291883d0740c01c010fa0510480d5100c000389580060181e0040d081098890b58946418000a100400c98000c01c8686941000100058241800c5940d050144138503803400d040120420003059900c141c1340701150b54440d100a2116803036403040d007900308140d00c00c01c52806140031200201e6000040c2500d2081c0c4c480145491034003e40f5000543d440d0540000704041010314440c0b02007900b055510408030302400340010750380d09080525103541501612002800d401c40c1c003226001e03500028190046010b24 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 680119721 1250 680118471 680118499
    0xa08090f06040f0b2a0901090b030a09140f0d08090309030d020c0102070b0909060f0102101e0b01050a1d150c061621091719080705130e0402 62
    0x500c0442d010780d104080b07802c1800c8990814007401c0c08060003e8051400b080f0001002002d505034071202914180d4a154680e40c0c18401680ca80e100d55001d108442c40010030408075400e181d1020200d640701d003c81440510005001c2503840340501c1a6030841c0d404848964a10b80c01017051984c841a618100c0f0300d09a8800040303402c0c0440e8002203c056840031400c80c10560301800075002604004c422982000c3c2150001040c800019004e18000c0511020000c040c0c0d1091040e16580500c60405020a2100e0340010006411403c2c004142d5032501c01d04071802d600c588211402c00c2e506942e101c030302072441c07070020410b10421801e941c2d1040c10702c141e1b00c52003c0a0400f421020600700c2c0902181d01c1c144440f0640300715088901c4040225510304081400000c3c00c2915402644840000d04400c503403a020032082080c140d000c8011a0101d44c0305525030540c20a11541403040d035401312942c880040503101030240241b40e0503c0c0360045018462101b4005040381e10034001045410a1803207 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 680120971 1250 680119721 680119723
    0x60912151b0c020f040c0c0b09030f13090605040207112b080316020c060f132d150c2d0b01060207061412250c050712080a08090f 57
    0x511585980402d070118080030541c507207914140c83c2900300361400e100405617514000c1092940000c01412000c9039408981680420415102c15400170308409940b40c0729401c41d042414410710405040340d080c00302c042054100b86c000d94100c2540f0460310492101050104104405100844200c1c001e41d142d40d0f80182d41440352502d20703280591006039903410801c11800e14410300c030441d10b042d17510202e211082615090100c07482c4081000c0541e403952071244850207100701651040c03100251252150a020380c2041d6007009649a50140000a6a6850f00d003041ea6070740c0707064400070980808585000c03403051520a60300e005450342551948403009960007402c4a00c650658900c802c0000600806404210030f6014203014144260a0403008221012500c5111203030080a61800c0201d001c1c045a4100350304141ca5135130b0003c80c0c1504019004001e08100001620300c0e2080300c0001a0501c0b9802e4580c08180c3c01640c164541070550405884419018103402c006109003408003942c454 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 680122221 1250 680120971 680121011
    0x1801050114090f040c59150409081c02120c0f0304030e030c130c090506070809010305090a0c150e0f090a150b03090303060a06091215 59
    0x41070008030940c0580c0c180600c140550000d008000900102041c0000700350300580c020119084892405103401e203043c500644c2c80100300c52038450380661603000c0824640c82d50007032580004101031a00303c1104010000304600305841074941c904902002c0b10250806800a0103214040c5207a0352a01c251001c10b075443c1d1030198840d0000990200d00ca9103102c0314408000c0d0803507502e09070340e814411510034001c0d01d40700c080d00080510420b03400e101981e84007840a44036801009000348120005c4500d0b0704040c0400f00341c19000500f141501041600e45031003a140000e030041030550400340b1400042d40100005884800c151180340034040c006100301c1d020034040c20007510503102003061074901411181e11140138910a5464410b9003402d03884051032190701c43e40c0300d0f1b808110501e64100c5c0c0108101c5c0d541000000e0b60000040200e4004000011030151100750741c045a080e5031107600311030900042c050744031900502c428100c007040131032040386000b40720110300082092020540441c1300c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 680123471 1250 680122221 680122229
    0x30f18150906071b0b1317071b061704141509250b090f241b030403080d0203090304090608010c09061e1b1b030506060d080a0818010501 60
    0x39020004000550780c0c072030841e040300c00409880c00c60708500344e9501885e8000c01010300c3c120303440e240000024013100486d441c0400c544030b03c08550340e0320b0324140010707441ca90291171000c0c0d00c0b081d0710020b5140d11418080525034810908440301c4c0c0c9880c1d0350030140f0008020701e4480c62081c89400d0b030060501e9901640101c1d4080c006040740d1100501d10011214000011030081012640400011103038101b11642000c00300e480d02c0707907005180c0004220f040c0701e25070204203825000c03550060200050042108000000c00b001d00f4520700040c0c1c3c0c0e03881c8900c0c00001e20070b010622407045201082e40241d03410560303410980342841d031280c1009044408990041d0b01603034640c004855200d800c6840c14000c0c1070545030000b04201c24116607021045c4c3c200c0c21108220030f4885080b040710860108100b10b03079022601d60228402885c1c000c03503104541c081078545001e01800328039a40790445111107616480701220b4105500c5100070380d21004010005e200a620050214403030389030a101c3e40380a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 680124721 1250 680123471 680123473
    0x91a0c0d0513171306030b0108010306230c07020a080708030f0c010902060a03060e07080105010212070c0f0f170a03020d0c020d020310050a0c1b06110c0f0d1103030f181509 76
    0x511040140d5104e03800c407030f0b0300c05400d040c54070002c805c0b507036801000d543c15a0f070400e90100743c15201210b26501d41c44c4000d02c40b2a40c0c5190414004070b480c1c10380c0206510f82c02141ca0031203494031514459240c040900c82c0710211780c41000074950440004014050b04803041c0e0002407105142e4010801750752017544a5000a070340c0c1e140030310101e0030504076039404c04018074150109605080010755103040c0f0504020b154500440d00f9010800c85458000140000800002029a0340d24009099100c28020344125a90a02c0640e0000d4000500c0c01c4400e5010390041600540051059602c640c0c031031016030300600c5490981300540ca0420000c003445102c40c1e000509494040300e424201d40f10309010100b00481c01070000580c10030000d12510240d08440c0c0090f20710040c00d04400103100c0c840d0500d006000c0c546200c505440d012032007118904064551031040480c0c4210580c5a1000b10360042c0800710b0b2801260100a6200c1e0115101d40d010040303a90a6040400c059020f480444041d40350b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 680125971 1250 680124721 680124727
    0x201090606080d0210020d020d1503020111030f190905090f0103060b0d050717010e0f0f01050a09021e01030b0406080a1401090317090c04050703091a0c0d051317 71
    0x800c1040d20601c0010b10b01403000d41082c82410a000791207900e00d4031000c58030794003c68000c0a051599044450b10340103403804200003030042c008055078042da0b10040e40491944004941c0150300070044900e0380b91108042442c010349075010394240102c580c0d03a8000c02904000200d5540c07607040c0720b40d014060300c44030f44107550b2461030b002055840003e00203000b1141603940307030005140003601a0903174942288808481c0310b2100010700421100800c40001c0c403503204654031100002c01c2000741c800384040248010780d100803c0c0001c4e1840e01c04020341000000c10598107848469214001c0c10347d0515020031220740000020f03058516981194080742c0007201c01400700102401b410102824050003805941040d40b406072001c07200144100380c0000c40300008100c004140803d10003484020030400c603504060000074020002b42c02d04407400b011091400c64a08040342c926441220030f445018504075001d01400041e01010b04921030356a0410061400240d154130700e03000b881100c102c1c0d0384d2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 680127221 1250 680125971 680125973
    0xc020d031206050a0602030d0f0b2110050610050703020111030c1c0506010e120309130f0b0f031f020906070b070216030b0408030c1306111501080a110a15020109 71
    0x20442d540e42d03020910407100204100a0300c0e401200303a0301e00c5d1a0b10b140000754281030344480e2019000405100e41c4c03148110805c100301ca049401e01c502000c600c141190480c10070700f85250100e40c0300380e170100d0303010700c40702d05a422051043c0001d05065100b0310000c0741400d42c42951010a40050f164045e101c100031030702c1700400d00ba03080010268a1549401e02460401d8000a080c0d080768840141c0520700208203450420410803c640d001c12000e0030076441407009428600046c44c0f4103030300829060800c01c89008501d001040c4421003003000303000c0c0c2420480380510320540c0c0e020105250038540c0902c040203890341e64101814126000e100802140d2803e010000e0410103401d10700074a4190708101030005c00c0c2081e999650140c2c0c00303011203030380b6140e0181d1480b10340070300c0c0044d2124013081c1402045c25503019440001c1011001c04036110460200b80c1d1180d20f81e800d026400c42d42d0f101a80741b4002c0340c070040c000c0103a80f001411003516181c60b40c8810409004a890560141c0e4580421134 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 680128471 1250 680127221 680127257
    0xe06041d060a1d0105130609050a0b090307020a050f090c0901030612060203041b29120901241a09010504030206070b06150306031c0216034e0c020d03 66
    0xf0400010000810152034001055008110f8421020701095943e0014408021081040107030442d0040c000e96424078121600c0744d629840854100d006547c201c1002945040505140c4002031005200e103003144c1d43e00f1034541240e0400c4004038100350300c030314000990314200c00150385014010301015903646000e090441e00b94900d054110301c1d810904204000304003411049059410b141d00d070425030020415958031090007400c1810108a64a40a021401c01c056006011004258102c0c80d00a5804c140303a22103482c0600c05e02c1e5450380000300c0d076000d0450300380041c041144141001410079480fa00440d1058001160455100d074036002030140c03900e0f141c2e5035003601300c500701c420510b1031030720b5800f1903200c0e0412480d0002e0a8842044000d4807070081c00883e000700004078200c000141e4a041910255086956000d600402149541542000e5800219006000031041c40d042c402c0c2440c07401c1c03409135200d1210100100510300c0c81c01617991503160040a0700035075407000c48050f03d000078 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 680129721 1250 680128471 680128511
    0x906070b1f0303050c06280b01020304031e05010f1506030b030f0114070e0303070317061206070c0317060321070813170607090501141b1f05010e06041d060a 69
    0x4144088000705040c40340504000c0607c001c040c107801c000c900785044800507441c500079508000c2c002c04032900c44d560005130a14a8480c110b019900921805403002d03032400c221070f00b4405c800e0303009c03400340b000707000103406500580c480c2c503c0a03040740c4d8070440c88102c0074215612038131008040c490f404280151558032070360140d10048100c01861030001c0c5682c1c060004100c50b0090352a200000002034507699818080d2101810101c040e90210301d08120003d0840c080f43c1d10450101e50b030546030315181c11584c00018465040036000701120ba0326802500140e04091166544120b0100040000180048064110740c0740b8489140c0d21141014007140010151046040f941d911500070000b03110ba01c8140082140c50a00f4110140000d071002d20404d4410072a0f800040c0c2c041060020040c58000395907030310000e4206c5007000240c2000e014805403413080c07050b00c0034103a1800100d60303140340ca944184c20583c445092804901d0029090b1030402c4011100c2c20b8440e6940c52804051046800003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 680130971 1250 680129721 680129731
    0x302030318091008060f130c030c0f06030b0901050622031a0106020114180709290a1203050906040e0907090e0706021c02030c1915020906070b1f0303050c06 69
    0xe038255150509901d6a641c1c17800502d0448030031000404108503a40c11180c030411903402c00040d00c1041e8603400c1c01070614403d4460403c0d00d04480100150043c030034490288540300c001e28010003a40381408020a41c2c1204074995030182c443c11240c070941c0c0c043c980e5100154441d100300c0c0f1110b103c1808000c10114161f1000c410b590601e034442c80074501ca0070f081a800b01241e00000910044c000c6100c4c5080001e800000c5054504280c0c41d50541c2a2701040c42030f0b10304040b4003001d0321103075814440000c50318800c0060303084044000b07a001038000d001901d81001c0141809007007950300c0f40e901320494400d445c0308805400801c000d100081751800384201c096a01342c001c0c80c8c0a481c22400039583c0040e0114071030002d8020205002462013802107801806942046903801802d100701e5082e03007a044d01e001c59041c000c000b50900c50080900030f03a20740e000014480c034280551612101d10700c0f800280706000b058112701620030a420b164044102550113907075032540b01e50b410f40c9401d1500d074020305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 680132221 1250 680130971 680130991
    0x8010c020c0d0302060a0c052101140a06020a0b0c0706020d090501050901231b040602061603050c030a0504050705120f210405010f140409020a02101415010207030203031809 76
    0x42c0e481c00700b0740026000703800c4950080c000800b20200c010484071070048101d1360044218110401a501d256801d215040c0d624940c00c4180301082c00c41040140d21152054202503040101c000c40440e0101020039400242074540500d885010b035113071803c9074070800740c0b1110a65500700d9a0b003800400d1003900e900000c00750003000354220611920b0150380414118441007004500040e26400807020600e00c842c01441da155161500c4020103500d40c03000b00c171043d188800154018a8540c4a8000c550040303240d03995651454031100400405440014800d0710540704400001480f5100c03082c6c1c1c408005d03802c20107840d00909542c02c81e420070100c44810503035200d04081c2c881d81c000d901e40c101c1d01140d400b422b005542007800300044c3d401418000f14000000b201050010b43c00e0101d0f0003c11080801c0e41c01e5070307110305c00424400c0456401c5442141400c4180001601b220000b0b0a810b00c0c115050040351101daa580d800649582e10040b4050001940950400c15506000660356003001d0060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 680133471 1250 680132221 680132239
    0x1302040e07091404020a020f06090a021906050d0f0209030607030605151c09050f070b04090f1503020112140a3809040f12021e03040b040b18060408010c020c 69
    0x40e1150300000c80d41d241c43c0c0c0c8160f90000303840300000d0080000004080b558400e59070145090f8030456240d800307581d01070b4000c290a4000a840c1c0c080314a409081c0c0e01682c449904150355a81c0c202c0042112523025510320341d08024503c0d6070380d0200105445441c20359004074440c0d040c1401d000e0989000154808007020510a004100690410303035030445000b02e20000e03c0518509150303243c610790515106a03400b4141c0c0210381080040d000b401901c990040903c01e00741541800f00c200c41100504211103003480740c1c01e0005610a000001d4209a400800708003c00c4074070310120748c1003040e07d10000341c60342c800c0d4503004285032090840b803c90341c038500c41903940502c40d181c403c0042420074403440740042000207800c1100d18049540b03041d810814484000c001d44001a544025650782125821001d50b5482d4442074008100e4081c0c4003240e941e2410503290060254080d04280d030b21001e61150030359001e0703e0b40c540d040079100401301080003283c1c02940a0b0080d04019003060400e000e01809 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 680134721 1250 680133471 680133479
    0x9140a06060e03030f0a030b1e030105060105120f0613060e0103020a0603140f0903041208090102011b0c0311070503160905010e13120c0203030d061e0f03031107051302040e0709 78
    0x1c0156401c045080010a070f58541146c01100240f0240c045103910071004502e0f0100e0040b504140128400150000c00594491000545550141400001c4500810300005100d0840c0d840d1080c1c004901402c001d4040054a40c5034090359107a8108484501c41c12004005504d88502c0b44d074010705141c00c1c00c102c41442680785885034140100346e182007013038800110703ea251081048400030600e0100c851729501080c908507285500880c0224010b600b0498030001d001031590701118825425200c0c41c441c00c0255500b503690100c40000364810780900c100000350381d00c1c04d001c40344120601200e801d80d1581800101e81c00c40724103030051644a02403100300490b00c0a59080300142a400480c110038900c40004200c2d0b4007401756200940502001c1201504010150404030943d003005500140b080c80c0c01c41e500d00c2c2e04419215200c1000c03c80c51080011902980d160302d0011032980584401c0307034a4801007054601d0081244500f641e0008040000d04c590842241c2c201e041841c000d8065468 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 680135971 1250 680134721 680134723
    0x1c0201200a09050d0f0204061814160311090a030c0602060f0c0f0906130603201801110f06010b070309170a0206090301060905040b15150d110409140a06060e03 70
    0x90040e5030280206410300c4c001e000e90400c03420304040d40100140300880c0c5824523955400e60b00100c0c3c84896044c031441c0100c07185074101040c801c070300d05031110f054003841c0103040f80a44040c025002c1200c07001c000e908800c0d164420700001031405003690208240c0b42000007071401030001c02d4107080400c10070602141d4808403045454401c98100c0c1c494880c0c80d180b0008101e0320030080c03041d01c40c40f0004000600d42d0b415801004035a1820745000d0180e80707020400582c61702c02c0a040d0f418410400e55002d010f50b0044000416000443c0120703850300012106551030010282c00c8401144808101802015400300141000d82030382c030440240075904003004c96480c0880b0600038400c040120307104001e914254003041c020401040140103e0905041207007080106544d4100c98201c40303100801c6c103051003910810404882241c00c0e05d4520010f42130001048407148410540d20301701310005d0312072800d005030001b043d03000b034104480d4106501c07101e0480d140c0d81c0c0050103000b00d90f030b48030405940c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 680137221 1250 680135971 680135987
    0xe01051e06030304030c1223010507120605060912030910050702030d030b132711090601022803030b181e060d0602030603030906040602070914061509031c0201200a 72
    0x411f1b101d03d05800b498504403c28024500c004c02e00000e01e900c0d02e040e011015000180140c1840e1562003003003054002d12000d80b21580039894021008100d9207200d03007484118051170080d00400c0d2030800a0b030100095040c01c4041c03d40c00010800715450041d468103010b0f010010300581020809207800d50003140c0d000c513820350b4103c861982c0c0d42c84001161040c40401c20b002001e2454030490310498503040c00b070301d03850b03005540c09038a40c5c03400924254000a040d601e122140d40e07071992030091520400900884d40c000031010188c0b81c0003030740310303035220038502e09041c00c0e20f95844942898150b0958410382149103688481c1840c50782800056110151102007103600f2030710140e40c81c1d170f41402003459441441071141e0850400100000d6aa50100c0e12806445000f03a051000c00c10305503411100c2542a07030043d038130040203240d560070411010001e0182070400380c1621031000104d000c00342c003a4683c0303504802603510362025190440705210720207403040c1c46000c020b0414003e00d5004107021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 680138471 1250 680137221 680137229
    0xe010302091602010f0507050d050c130312090e180c0d0305271f090e10121a01030b06030f01110d0e0a060e011b02031e0d0e01051e06030304030c 64
    0x401600501c02d041d00c01e4211407100e0195002c00d014a09181030000c0182e23203c01803100c282c5240c100418421052402113405134900c40b607001c3d41f0642941c90340c00c41c4291025540f0240103450200040245026010034031441003c144400d01142c0c00c0e94880c28010a15003072407190001746203072000a500300c000d4449110b083c03600030b00710059041c00d1202e2100404121a4040304481c1084045182d04c602c800c0324002940e90124542e41c2c0f4000c50349000015107a00c0e28804e00b440c0c0500c50b1450b650024a401c60041c000d80e80d60a4811000ba80050b90030303001070f680c3e01442e404018683c1000c2018528200c40d1800800a030b406102c101d111600420005680045d00c54024071031200040000d80b139160741100040000c5040c83300c990b402400c41e0300c25990302c50f0001d60810344c032500100613641c090342c404484a40444484400e00e2541d442144199070442d511107140e401c0401c04d210b134501c19109081c04401c1c50200800000e482e60340288101d01c80d604c200010700c00902c40200f07402c100d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 680139721 1250 680138471 680138491
    0x12601030614101809050114151504030602130b0d090b0606270d02120105060415060807082703070605010f080d12020d0c210c05090d020d020402040608100e01030209 73
    0xe110380c44e0340c51018104100d00680150300301703612130031041151101540a40d50007014892031491440c203010000440c0d81030309407a20340520041001c114950020104000354401110100c2e482e440c0e000307469007200740513038001036491200004210941c000c064018000711103e50800f0b10b503038401789005200c06661066106441d4050394540c98400030020003030760040055066004103401c25000b0311045405912880c1000024546441501d180b0000c0e00c059954181d460398852400b5902d0850260005d4081c05002e800720403080940d00107119180c42490107140e4032400703030030100117440060308554001d01c01410f0030407000c0c00000b08603c050500d8101840c00f03c9600c400d0f03900074060004c280c1041400c00e110101c010b5400103201401c02c4059040041200a05440d43c1c111688411078402180c010080440b062800744203548941d44010007040811803a580400c007030b6005640204017042e4001d041c1b002c05803080342e0902c060318840c015503000e5855030300001c7c2e081030090021488 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 680140971 1250 680139721 680139749
    0xa0c0b031b09062203021c0606122f030303131403090d021002010605060310060f170720030c0d09080a0305070f0201030b090709080c010504080d0e01260103061410 72
    0x440c0310030306800d2001710340040161210f4115030160b06010120110100c1c0c01c40d242541c0402c0c005945d580c500031217074000808000c90f41c06102c001c8002110150450084480c1d0b84440a4540c2c1c1000194800e82003260720f108a0340c15440d0500009803481800045c6800c2131100302c0c4162110960a00380c1501122a091150f60b4050183d0040c219600810303001440042080503000b402d540400c01c40710180d441c1d54126502c0d003411204240101c01c103140c2a0170000100e2004c0340315002c0450b0a1644001c0022001c1e01e03a25100c0c80d55000080c61005c641200d044041820303007080b00c040c0102038410107000e074100f29030703401041846955002801c46134411101000e6910942c03000d444503030003a001c0180c1d81048000505880102d215030810762248040c0980d040d481801503500b290034441c002d01075580b0043c01903c46c407498031081e50410403000307102d40b003900c20410303084203e41410706a02c9080d4114140b100c04d030b480078910491401002400d1010006030602d0040480d0113048000c20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 680142221 1250 680140971 680141017
    0x10905030a05250f0306090b0a020711150c0307152a18081b04060605070c1a0c0601170c0a150309060b031f200f0a020a0c0b031b0906 59
    0x3c9200d1190300210100c8500c0c10b804800c1017450360243e0040c81c064814100c00d96203c071106401c2c0d10642e17030010542000080100c1c1e40c0e08042c504955412803a01038241400242c0e008140381d81c00214043c0c03034072400c89010002015161058441104680c001e03451a400e2101e12901080d88000c05503040201d4035000030b10504268802102502c0d40c6400d4400d8050040c00c4108a481e0908a441c401c0e481e1180000301a8040c0d4211070806612420985046160036002001e5200b41540c1e080c000300c080000d41e072815801c1c4502c41c042c2800d408030fa00d05081d080c04e51464030b0010351669000e000300074401d100d002040c0b12a40014655440c001c940030710180381c0b5030003904100300311a4061060030458a600103e0b05146018442802e40803c00411811011a4248003034403003800d5900080002c1c84160002000902620030f50f80100d4004d000665101c40c1c142c085944071200b5414007109203c61604045103030510b40108141d03c9050054010000e0882c0c4100a59034440b5450300485007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 680143471 1250 680142221 680142283
    0x10302191a180d0f12020d0c020d02150f0301090b090717070909022b092a0806040c06020f010501050312090a030c090501061814040216060c0e010905030a05 69
    0x40300a03800035003c421024801d28104a98118540003181c5402c1000003c800c004d01c0080c0300d11840c0b42942c0c0d000c1ca400751540074401d00304402c3c08160380040104240c800c1015a240c018400c40b001c03031808950340d41c0b42451860803540c01c40b014905ca16440e40a200e0429404810b00c510280d60000e400225110b034641a181e5100ca07078030070045980041980004c1d18641e140c01203440a1b912400c1112040c0710046000b2503c03060001040304541d07543d035041142110002c2900c0047c2c01708070b043c9064130b500d270780d40c0b804d0b10072241101c148241010600445074103000504012031800000e001e254180800291990300500704080c5265020400404c285e440c2100a4001c542040000203400d0f2036012070000750009000780000b15083c4042041d8542c868091003040341c4080d105142002181d000b040013941c00084480e217190703254019030000c20080d201c0c5481c0c8000c40c0c5c46041c07002c00c03007800140c040081071340414443d80185810300c000c100d01041ca4918910031568209000c0301ea0b01e109 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 680144721 1250 680143471 680143507
    0xb010509090c040f05030601030822031703070e04090c090f0902120f070f030803060907090b0a0c06051608130302032101090f2a030e1005010302191a 66
    0x390344a44100244000400814002c0055440c45030600d030076943c860303040c940e48003400e10000704060002c004000c40001c0285030f00b07038803440081061301c58950740c0e143c0c08244c1c400208100030122000050000c12a00217200590003c0709031018000d4080907117900e0b8000380944030300210079071115120311070390910750701007462254000c1c20000c14059210b07c2c2a030f0350302d90005c4c80c10f440c49560f50100e460141800380504403a4050040d034a19a118001e0081f04000a410f201c2404543c401c086545501c54001d445070303070300301c0c0d503921904051410f060003500c40c050005040340d015000c40e0f0105d9940420000e038002906002e5204512861408a20314450881c41440c1c40603040d0540204030700c0c02182504a80b0141c0e07040c0074440070140c250f02102c4100300400c160b080342144044800303d1029080da0f4585c3c0505002403e01d00c03c1040f00c0c28511811140088a60744400501c110325041040308400790b402424484014103142042410490001010782c10041c0400c0c401c210038200548 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 680145971 1250 680144721 680144737
    0x30912010f1104050f09092515020c041b0507020d0f0203071d0c13120609200310020a0e0d080705070303030914010b06040603020c010e0706050403050d02010204180b0105 75
    0x1c100a00341045800d1012074000f0b005081c49020750640c070640502c2c01e000d80034001d0381c071113010b00040654150b1301211448508074450000004c80c10000e9100b12042034002e5660850700544001c10b082c004000461340c0844a00704050b0301d02d80105412903000042d20351459041d1184090391501c0d05001d100e000c241b10000b98944580d0a0102c0c1c1c18070289403400034014400400d49454a884410b0b031140e00404104405081c4c000c00200300800e8144000c1c0e00660050070005000c2c48640c0324041e114150f00c0b403c151a100078840342c0c002e0705080104040059a0540441c20b18102240040840d400c03001307283e1094090720390308000d010300402180c1c1d90507031010403640410b541e407801078043d11182c0d80c26035840f03610010449049006002c0d5001c00c0200814880c5030505180d070a800941210032250200d6598a42d5591081010001780b40904071540340c0319192407951a049281200745c901c0407046900600080120417400c41c001004160090000700f904862039004170740c2401235038a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 680147221 1250 680145971 680146001
    0x12020c03040302100903050d0806060f0307030e010c02070501020d0921031b0b0103021c020a031b030c030b060a06050a1e1101050a06170106030503030a02250501020c07090c0203091201 81
    0x600c0000540d040600380c01204c1c800c0d001d0380c00788002300c0d0003611800c00c1119415000705040103010b4180a020340190751110050400080e00b2100d0405c46d403c40d4180250302026a01100c41480300d5a01001041506440352801c80c041030b080205180a42d10743d442c800507804900e91518007011301503403580041c0702d4102101204100a42402000c2c80c0d070a110a074010f040440c0e6154004c49007001398817240c0d13006000c03043c55900c1c560740d51010060190410f00c00205010713000c4006001d07055007000541c0540c1c0583c81e2401c10038103700380d060f42da0380020305024007080340040741745d0041d0b00c441032402115580c9c1c44d60350110342e050f0707102c5282c0c5015100d107510304070400c20024610b902003816504a0426600b00c4800804a5406c0300d01500004c1d056074402e0001880f10b41d05500181801203a4038500300074598104041d900c03418044400312626500411400380031807003000300714000d0404003130034468603440301000380d140d10500a040c1d00580b111f10012525110075041419130301c00b049 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 680148471 1250 680147221 680147239
    0xc0918050303191a1008101802040e0901060501020d050c01092406080d022e050c03090c1c03120b1012050a02030709150905030307032a0312020c03040302 68
    0x102214040c5102810042200d46042524440c4013542c5001344c920000140800d501c10b00100b009888207030006003030182c50380c220580800c1d44102500c80c40c000341104000941c8a500703184641483c0d08006000c100c1c161f00d0001708005c42c5c0c0e400109484440218100b86a440b844114014050030702ca800190071309851034255040e507a02c2d5203c0f0b41c82c48034080c1c4208030729038540d0041d07034603100c0c10b42030341c0f00507480740341203005500c09500c00c0d804042c011003040701400400303400e20040d0390044400c046c00c105c000c01001005c40061202e401a000d084481c40540040528501d81d881203009000c0e040105200b26031001000982c002070030002e005002d044800c00062000304108005562030520509081c0410b00b6000903000b501d002e100c05884400610381040060004d0f040401151410001b1b0b0160004503901d080c0000c0401d24040d9407240e204654011180300500320381d200909216100340c07003000c04030340e0102c28814441d0002c14056507a510840c0e866195000e143c0020707601500b10 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 680149721 1250 680148471 680148481
    0x6031f030309150f2f120901091d0109020a020312010e1b040509010303030915050717090309031f0608030c160f0b0412240603060b030a0c0918050303 66
    0x21020800f107031540c402120140c0c0800030700726050b14890100e000400d00d00600c902d0180e02443d4150800030117820450340c00182000304030715080507044a917003030322400950b1014a5074071045590161041e103d100e41801a20000309070080d00c1441a0400c080d03000c1800018903200740101c5000010000103a6000e51f101c90051156120540d44d00b14a01009008030f0701001070710040d9400c07288010080880c1d030b8038540f81900600050403044901850307a07400c080e1801d80030320a4501403420fa5030703500300310a101304818086003405001024540d04c144044820b50b42e00161000d40e580d10001072000020002070b400014110320740144105000120325820350400c0061a048075202003500c1c18046641c0310043d030700510142c011924007103c00c0005114a0514030101c0110f80d12508461280000e80300c000040d50140364101144140c0725034003001031150902500b001204100d020f41240c0f071072655100f19448040c0310703c984042d222140e86a560a01c01d980082160f008010b4940e01d10304 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 680150971 1250 680149721 680149727
    0x40608150d1a1303020a080a030e030a05341401020c010906021207170426070602090406080303010501050414030c030a03020604060608120403030509030c130606022a06031f0303 78
    0x111660007140110b100143c02502d1080f07101c441c15400d9006000141c0440d110f441041c1c2c402c04c0c1d2078052580324a000fa001000400050100b01ca06585035900c03031081d4600c0d82a28206034502998940b000180821084031100c0e41108455102c103449a0001390303e041e407400ba000d51207140308103519104513803042c003071660007d0081100c0700300c0c00d00c4250354160080da0000304241100d600004070070001000140455070040464088070307110351103800419141710707071540040011a235254003c583c40c43d55080c240940d101500422024509640c108000201140030b94410552444050b801491040c2c406000006031560b010302690020009424013954641c015101120600d151200024958101140000d45200701d0024686090300c3c0d91130840d0185c22030103119a1501031a802c9002030341e40c81e000fa4492214020000c00c0b160300d0f000c80070341022014502508a19103480154076200c003403440052514038100c0d0081c1d10f80e1140d03080f0145064500461204400864001000789a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 680152221 1250 680150971 680150993
    0xf2703030a0921110603193207021b1201020301030f0b0c0a051b1e01050a1113031b031e0b0105010c0506060f011107031b1a040608150d 60
    0x3142c030b00060010b41d081d4004400142d04030070702500400790500c813000b2030700e07003a130003140c00a200d4401943c40480300c85080c070460350100051000e4090200c10070000c42d0a86180c0c820040090310404030910341030070f004e0740780c0c040522901040d888908d0030480664400f40c040c00303180042c0c40215100d41c0c40b0724090303900d500358035001c0c0c80665801c2c0020f5081d03640300c41154028401c81e500c0740d060017401e00c40c80074096004541a102c5005005000000407485d424801d0100c00300d800202d0a405d1000d00082111007150b0784501418081021140000e400c00c0b40c00f0403668003925462007410031a0030b105400340d19070030040c2030304c3d641380c514041c1e103188082980149024010250702031f41d0710790054982c013505401c0241a03800840001e000d03441c10500c083d840d80c2060518207402001108210704103542e6405c1141e40400d0004041010300c0d00d09005000380650000026510081d00045210781c02680305107400c116a440005a00300805100d14902d02006025105940748514000b04092 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 680153471 1250 680152221 680152229
    0xf0f0215010e0a29092212081501090e0c16050d0e0f1c020a05060a0c0501051003050601090b0303070f110117010f031412210a020f2703030a09 63
    0xa003807031303ca064902c0900800d241081d8046003c00303441c0c4000000d11030700140041046050001d420341c524401c200000010000610521860704a00304200c2d010307018000143c1414a2900141100000d598102d046401999412440428035a685c100c5d85034031446138000904a416044011a082140002d102c46601c85551145a10a08842d00303000d01ca40004040507444283c1282d4410415000480340501c18006800031340d54a8440010135500c2d0310920004000850041c13904082c42030030301ca8244c001400300e20360403c0130301c2e68803184c0d81c682d010301a1060450f0380f154180803035602081290300f03055200340240803880c1d01e401c2040b0349885100c00c80e40444d01940c01c81c0d003582c40c4e01c070740075043e2240c040c03a409070315007543c960403c084c654480500d124410740e0600320700c61100c10301078200100142c80341d800c1c1408100e040701b100d030800340000b9017145c0140f0a804111f41407000741c03000c200318001380819212080c03000301da20030120407049415000008010782c2951780201c0000903a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 680154721 1250 680153471 680153491
    0x305010c02060601050d090609081b0c0d0308061314070309060f0b01021e030d06080f0712020a050f0303090409150e19030f110318040c020d0f0f0215010e 68
    0x158031890000d030380b030310021142c80e0700080042050181310704080e4440091035000d103000040d81d400c1a81c030011542e1103511036545c00d0240c20601c140c00c2c0000c02104503000b070141c41c15052160966005028120042c140500ca000035003003004006c280c1c1c1d80020815400c00f1007a0810342000b220240040c02c04180a41d0310314101181f07221003103840d0103550590030301070f4028400d043c0783da50b40d549020341201613503106000401035020201c00d0303400743d2070241c0001d1000d424011191900c40e89005066070141c1a0402840391120150b95001844000c032041074070011040a400070010b41103110310803585034003514055003d0240401c6e0340c10000d0000103038408109100c80c610407243d481d02e003583c4446888010b000010b0000340300310844006183d00742400c0154080003550705045030008403030800d442281d007007a20901d2078640169586219140003404403c03180700c00040600f010070351401d007808840010040f2091003001071112021090079100e5842d6104c0d02400c2490109030744180718 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 680155971 1250 680154721 680154731
    0xf0d0b03150103200d080c0106050d03140f040803030403021b010c210504030816060b0108090c010c14030406030603170f030a0b150711090f060f010806060c010c09030501 75
    0xa40e04000959035184038920075100c110303a18581c0c2d6808040c0141c640101107040c000107000403a1030782000300da42a4440e071082078546400a034001e00711400395002605c248000b11400010940115034142d1003501140d1403503492000c0101c48000d803042c0e620007031003884000304104c14564081a1110300341c2e116807815241c80000d0f401150309025020000d8011840e0604010020181340b200c4503610030b050810130704055682c0c580c800710b0703009104071303502c0314045190071020480b0510580e00c41000908054805046c000c07003c983e00c107036000d003050600c0001c02039003042c05031717181c89003900c16520f038102d03580d0341d441e0180203000d0075541c0300468400c8604041446412040c0b130540c0c1450342038030880b03030940c4c0e12000e440703014100b06600180c00881c0380444e1100d18641c4001070065a000b810302480c00540301c014451003140050082d4103160582c0c05014150b6071783d0765500106802481c00a500342c890500249c0144036181c1c0403012517191541c4185000d820084c02800c582c051002001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 680157221 1250 680155971 680155991
    0x90d03031b0518040b210d02190f020402070c091b080a0e0d2703030f08181908090d03021f06081903020102120a0b03010c0912080c120f0d 61
    0xb914024000385540400200ea208052410154040008888014400e0314500c0340c50940c20024440580402565040410109030090f0100854404c00e001c80c00050304080003138071050303000d10103140c0c000d03c500d400294a400380222160340343c01800220208000b418003005d968039407114100700c80e00c0420700315400281c45c91954800c1081c96000c500140040e000c4444d0100c0c2d40c0601024010610020700d040000140c6005410780c0c0610b20940362188100040d000103020040010806403030f8041140b0103000680740400c100314268641e0b00302c03102c96615171030030b408a4000c400c589900944d641c40300c0020f05500241420022a07840150240011840c02100988041d80200c2d0315a40c1704034415424103004117075150006000303200044c00c00c50740c0a4080090f00341a203184c0d800c2e40e1100e10300d014a14080c422024000001d0a00c0d5101d03038a441760365000c41714020006407540d480170400c1001c001c403e00c4401ea40703403040d082840c1d0700d00700e40c44102c0090708000980c408042c60800c0c118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 680158471 1250 680157221 680157227
    0x4110405131503020402070201050408062703090109030809032b200303131505040b01030b07020a1707020612130b010f21030e190513110f0f090d03031b 67
    0x5021040100b0035403080e82140c0901001c0d510901c3c0890412908010004d0f010f0003d1040500070b1500c00140340d543c0790580c24481d0300b0352610040c0001900100030381010b03a030308040210102c03a800000103468049001c0003a0929080a030701089004403400d040704404500444240300c4c00c0c0540303c0d225140c00381814004060f1259028400743c1d4400c00200d041980700700c0208101c44d00c905200c483c0f12040b20f4124041e11030a440c00c440c158a580014410422035400f4154800041c0c401003c0d400c80940301c016600c404003201c00700038000041d0030781c00d5484400031200d070000c51050190a60801080e2070030f40010b032803400e8501c5401e03003001040e0354030800e0f04e1808582500344541030500b0503101c103038902d501400d4214144081c600c1058040d0700c0310b0350002d003200002c800741101c3c3ca1400092041e01100083c0148045150111003801241d286081d1005541c074001300a0f200c001007260072145110b048405a0f1048549001da010190f00d500520030030962040d0003090729050072819 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 680159721 1250 680158471 680158481
    0x1805190e0d05030a090204060806060906120a0209041a09030301150e060d1508120d0e03030f16022415090103050613060912051312081608090411040513 67
    0x1414241d0041c05004515910410180d81c1000c8405400181580786078000307801c82e06250701ca141d1507080394040141d070f442d01c02d0249a0001040c1c0c1e640d9525801c820320b0359121a96004000d100702c09041c045000e00c01200d0952400b626003601c100130900f414a034559503604240301d600039188200d801020030a1044000c0c20a07403d015000382d0404002c0200f190140c80c44080581e25091149000504c10701c041208100c400588070360341e03a132018801107000c1691000721014805500c01c2040c40303600524292402c0c0e2010140f04602c40c48140074102328181002d0701411440f454103555040d050420341044180180c00d0300c9849d51240c0380e010148610b144003480040c005811400000789042409041d10700810700c240350010300868141d40d83c900c55540422030744005030002c0f403800010000c5442500c09051004c0d184c2224107242c0ea11601b49218586e040041d034802410850300708040401900d00c40c7d00b0040042c0420100448100705642240c17041a116040240030241c2c070032702034412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 680160971 1250 680159721 680159741
    0x3609010e16051003020d0e0d0f0212160605130609050601051237020901080a0b130b0712090b0f04200112020c03120f04020a05040e0309010e0a180519 66
    0x180e080388030000f400c1138000350440c4984080058956406c8412400c0038024940030b05c8960302c40e0760820401d000000e160030081107891421600411950001e0907090140843d02d50303000101042030742d50085800309201820742c000700081d003000343e0601042800f00722107040c0d80c404d49003c0c1855402501c0d07259039260401c0701e08400350226022000c114003c011841c010703000320494407170190240e408561220001d03400143d45400ca4030803001001981c40d1992b400054100402c01c40d45002e4032402c5142a01501078070a00400c0a130b006a406000c1e000040c3c40c907081500d0101914100070310118582085401300e5010b205c80c00c02e00146055001e13000c2c0814010782d1550600e002c060507031300082d884000201580d02c018070450014400040c00d41d4400c007001c106100c0bc2c0d007050700c14007031519281d801491050341005040e0100030070000a680c2816000d10304000c1281d01c00300464170012940c0c0040b4900c0880c8008103540c0603094102d58041c40e41d0904400340e401d5440065001c641001e45 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 680162221 1250 680160971 680160979
    0x240e010801110a1e0e0d060203010f270903031503050307211713050d1101060902120402131413030e0a03211106070e090601020604023609010e1605 65
    0x401c445091189031012810000c1030801000503180c0900140b4086d0000f201128100c1c0c0000040c8801d0310b00d41e0b000070041104800c01e90444d0050000c4111b520500d011120203290380303003d80e005061003900030815088104a87c40032258903414a19241da02041c0103458040d00340209034040140403154894074105652040140f10b0f000300c000380c054201074240c101c0132a05e040340102085080c01071040c2c10b071807134540c13881909259408a0a490103503014203a01841070104050820030911780c90b921980c12101c0940303e440700b5a540000300741e40880854200081001c215450008000d600d01250203501e40c110710841900c20001024117a0200400d00341da00c00c882d40c1040d1211a182100c00d001c0d04164012882c11046113290090450344c043c0060741003546000182407507042aa003244087c806004640b801c4c0e00401c1d4081ea0301e8050942c24000741848544661004080c006840150711f0305064500b08404203d004c0c1c016144c2601540c080c034020419001c811411139003c9401c090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 680163471 1250 680162221 680162237
    0xb190815010f140d050f010c080106020d05120402131b0e040501051c02210c040f05160f0306030813080705060301060e0d0f14011a031b04240e010801110a 68
    0x9102d03020301d541d034402c6184c0048440a211001a4050104205085480000060807404040001c2200c0790607408101903400041c002e1200562020846440a400b140e41c0c402549981c8086403840e00300d0719036400c480d0b151034802a540084948107403110f1245030b54035186040c01c03000308802c6840a2050544c00170205000f03800345055042104011400103040710624202690200540c1c90780d9030b00c0e002d450700006104005c40ca864402d0140725581c412042109103000541c03150760304030900700740c003d11a0048400b0006071181e04200082e50f404201c8680b20301d41042441c03d0300203a40104003590091000100b12400c081081d02e04032070441d0f80c0d5240100d00082030000c0281e143e9819038000320403081d92070100d9041c0b40000c4180c0900070000070032017408840c0e5548800b440410a20980092081c68031585c10030618034800030040310001122903600740c8070312842c66080000b5003040d68007132000500d0441c1d091110704841203940280102c950b03c00d030050b82303841100ea5600102c0c0c440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 680164721 1250 680163471 680163479
    0x60206070e0d0b1e011409150d0209180d05040513090c0306111e09010806010306080c130b0406030c030b090a03050f031b0c0a0c12030903150b190815010f 68
    0x41001184c01a02251245400010b0b048501180303d800741c01600e02d200b0218603011850030704440c900c2d8400390b944410800100308400027003c07005c0000000e40300318030b100049001018006112400b030039142e402c568444403210780142403504244245803068074501c104405454590103030044169016244980e11401d40e030b01e51005003010081210040302c1403064408840540045c5000e0703030707201040300da184c910490005141d91740007826141007600700402040000400942c0340d2101004550803a208003101c07078400e00400440108640c0103060403000030510605801d00d40c2903d0140b21040d41c160fa80115680e03640b1403442d030060000344100178860303a4070f61074005160451404848020711501102054507141c00c40b400d16402500003c0750441000303168008580206050003580a616209840241600c0602d02c0098045012a00c41c1c451210440d8050320080c50018698400c5c0b280104100c00d80d60310303a0103950041d03c162000c100038078902000660483d6219103441035800e0034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 680165971 1250 680164721 680164733
    0x50714161109160f030608030406120f0c020601140f19060210020421050102120a150f18021b06010602060f0730021c090209011211010e0a1e060206070e0d 68
    0x22034204000c05a80c6c0c00c0104410005000510007084a90703100c0000308400315001d0b045500802d1007441c0c5500e0b106011a0480d00800c01c981101c3d03c11280214030338058000c5414002107851055220f01002001c0c0d28403840705815200340c40c0f00c1c0d0308403010040e506000c08120320a500a5240c40ca0003109001181900d501000c50107500c150000b60078880096800c1c3c2003c4800e580c0030181940340c60005104e00d2003014110002c0001e01524110a031803c036a4158008908c510580455000101c81c0d80e5a15800020f0741c001c00c03c0001c488056944c0c071002510b41509030394802d006442013010032a10b6200d640c4440c01d8140010180c844501c2d203003a400078036000d0307440c4021500d40900c40812445400b40103603406400b0f031480031407803c0062040010811058000c80d07000d50700c440c18080802c003130044a44601c0303021300b8024050442200007845a1a01d03034403a000802d481d00141c200010341d0708041040b11000d800700c5602c1d1b2a8000c0a0301e180b650380403543c2d0480303000c00100c404180 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 680167221 1250 680165971 680165987
    0x405190507150306150c0629040504050a02100302090907030903051207030609060b090420030a020304240b0a0602030c2109040c0c0c050405011805071416110916 71
    0x81400d00040b105d0740c444000c0b0300a00e280400c10040707912040081b013408528040d41e089041e40800c6410030071800c840c040410401e401c1240c3c09a9503030b6002804008080080042d86c98008114007125100c081005000e5803243d0f8585025982a1000c5001203001380284652250305031038250620000180610000200404110815444000024824841c1e10911001e00fa41340005c5940301c0d440d9061005035450b004d807050180c50315911020076030110070141c94000b042c400002d41d4a0b00c481c181103151001a03206d4041d40c808000003c90b0200c8958086002010705a0707c0103102541c1c5e0005903281d0041b290003900e2174105000b259070007a006050511104031030b061039400c1a03091000f041c1143d01d042007103008100d452a104d018400d02c0092030000300b10448060001d076042502c5c004608035030100703045489071104045070880b07006640a06119080d01c00c400d4030340c01c10240d2400318050704c10040d202d45501c080d0120080c01c065840e140b20350000b080508211200c4182100d00b41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 680168471 1250 680167221 680167259
    0x71206050907050a320307060c240504150b0906040c0306030c0608070206180304030b0c07061a1c08090f1c0b06130e0706270902030405190507 63
    0x70040c1500401c0c1070303803244d800001501041c0300006903032011401d5003102c903116034248100403601d10740c0440c1070380c0e0003c2c0040035610a0b142100c0341072103e24140c104840c0407102403c0c0d500012080f13080c071a02c2d0b81e211920640c01918150740c44680c120b018802c07148030030201d5030043c807040d00080307160a10341c0203003090b103c191a0000380c09590f5120000740000b607420200000b482c50040c03080341503042001c030781c0018040c080450035850203940941c3c0d80c8034911000340100e682400180c21158064140e8807003e4201c5814485004961805041c80b40140b0101c0e12a1202100040b070b030700a0b51208030b20702903116900350714000341c080070030051050301d0003d150301c020049903102c040c0d40c0d805d41d410303121445002c08101c01e00b030000c00c200460280004108105140c41c80c100c406070000504a01103c1f11800e004008403c60b8040060491401d1541c001e1500d0401001590448541c01184110b0050040c0d0303440401514250744d84081a400141c807a6101c100284030000d1608907010000e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 680169721 1250 680168471 680168473
    0x70b06040b2d0a08070b090409060b0316080f07050f040b04020c0a0305090a0509130b0709080a0c030203060105240f0909091e011b0e1201020f040303110712060509 72
    0x3401410310889410801202d182c20302030382d4901c02020508214107000054602003010300300d0710381800001149070040b0311440b441151914403000c10302a40c3d510000380303004041d05407041d4440d402962040c00d2024442d42d0a01c0c40f5082401000c9000030800d201941c0300100b514440700b441100b08009480242d4401d03034403c5c4d0030000b440003082d04000b8041070310711079103e05450b41e40100c20001ca660b11944810700405141c42003080258038440e040c0c41490b0300480e1180d881c1c807820400c641101064100d00300d079201c1c2020034010721001180c400b00701e030300c2101145c40980e200c84c03d01079443c00c800c07a100c4402203010360750300d4151180005810b0461802c0304280c200754115000440004044da104542a0041c10710414183c000c090917456a5401c03100900c18110500c8602c0305404074000f000007048425007140b1219a40c80d100c4e0f996010884c030095449103004c00e0840c42e03661092200310040380d6400d890955002e00403410b001203c0414803040e540031565240d84000d800001c0072601e80e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 680170971 1250 680169721 680169739
    0x304090b031203130b0601030c05030a0c0c05030f220302030705100e0604030b09010c030b0a060e0d05030409140a0b0303070809130c020609120421080c010c180b070b06040b 76
    0x2512000156104050340d4613401c0164125060000d48807001420441c10181445080002a83c00600301c80c0c00c590f44034400260f40140c03010450f040c801e240c030001c00d540000202a444a105800900000c3d40c07002c0400c0d580810501a540d4080b0441c0f200035016041541d04004514055229103041e8a460174416000c0d242c660024065a1042e08115a601941030512107004000d03c1880780200c0a4201044800e060900248282c44580300d40303810071400031600c0e11a9101c5508411340150301038226501c0700d449001e000302404030760305400f60300c50b0200d00061204d100d81c056003003080720190103540381c06599214104540e008800d081e0f0002c50825044002c1629480b030614280b40c2540076103180e04142d0031040c140b00044a024000c1c1300e0034041404509261550528120001101854980c2d41c0c0d10303040015000e50010b4140551814031450591f41e0000014280e0000040c00e043e001a01c0c0d403950301503409a100c02034290f6590800007200342c181588005805d141c01441503513 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 680172221 1250 680170971 680170993
    0x207050f0d0306030317070e1e1309050f030304200f18040c05040209220b0a0303020a030f0c032007080a05150609040b19150605030403110309030304090b03 69
    0x2203000707904601030000aa88180800603d54400104000f40100b00c0c10700c00310b4100301c0d100070000d601c1c6900840c400d0881c14900c6007552010030008040c50006458071003252101d88502004001901042d6544e02610082000406011084902c03580d8418070701a03020018441003600340c807142d048950402100c00e40207205a07589200400c1040403004a54040d191600e8006000102c59210030f000e103005121242060703507107002210381e412016100342402d42ca00070b10751003e020792015203074205000036404000d140d4042100b401d945e00a844036032083ca02020308072a40049070401400241d180c0b44028218214071032036501d0020301a04031004030b40c40d645c106084c401c90034002c46031588030411001c9224103103018294042011103e007002460a074460440102d4014140d0301501112a958044400c01c0c2d80248144001c6100504c0059101c68024115034010b49094001c82c41041061410a20000c2100c24943d00035024505051070056040040c10034400d45691500450540d08 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 680173471 1250 680172221 680172223
    0x8030a050405151915051809150103120f0e010c060e0c04020d0204080c0a0602030702011206080102070c170a05073309030c08030a080c0d1506030b010e1207090207050f 74
    0x3502403c69010090041c801c000400b100710345e00e4160321900c54200520800042d034440c1c80c038200c40b0140f03504905460740e030501749a0810400c0401d0b64941d8a480d40040148a08003042d40000d0609880d2001d925a1201066a60403445040c079800681b04a5016001440d1790300a00c0c0d90072840c8040720040c01c40740d400901030380c1102410700c1404d0381c04035080044c1003003044070414a0344c080c0d424000c46410104001d480340700f180d1010b0b06120301001d6188050049a01442c010501240215214100c17803a1004050311940b04070780240f10003d8801034214000304034901c029510100130710350701d85840a058040b45803400d009089200800b01da40404005141c40940c1c20415554401140c1c11880c01114898aa030800040c541c414003462040c540c0010f2407036008801d60500a40310400c10441c3c0d00a0315501c100f0640300c80a810340020101c0e01a0415640a00242c0390510b14115034814131010120700d14421503941d100c1602041401003e038010400c20340540c003a0790b01e0020082c002c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 680174721 1250 680173471 680173513
    0x609031c080a0b0d050a0b060105040906030b0106171e06060d05010306090b0f040506010905280c080a2c0106051f0f03022b1503060203061503010308030a050405 71
    0x18000c901541c080200b1031907144555084103404039a543c1280740709449044d03031100d60802c0102500d112101184440c0c0c090000d80d0001c1c85c0c886810301205842c0d01c0c0c1240504000c1c46120045104051600c48500350b6151080c0324040c40c1300040043e0000c0d115503090401e01501d03a5030070400800144000410502450f4043c0d0700840000c502003001e40b801a540000c01841c0c51503011a401c140000518045201030450b00c1018008ca1242c407807401c0d0301c030b003504008a600c076110f4200c2410368074010150446001d00e006500c0e80601d03603448c03080140595244c000701c140300547c411812642e0b00702c003101000443d41c07000b000003001e41c2c5810104200b0480b484220101c41c5403080804001e036441a0f40e100b03410510b03c3d041d0305115003442c3d9040400c85004030b100003c920405c210303140c0d40d15603010303210450b43c1d56070400d1100d0380d07820408000d40c401c0d1000c40c09001400d01c0340e03401c0f807820700440e0304880d48403041701e00d1942c0d4010100c005200140045525000b12031050315685a42100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 680175971 1250 680174721 680174773
    0x6050706050a180c1403030f07030c08040906140405011403030f0d020d1503110604031a071e0f0201180209010b0d0e07030809030c1005030c0a1e03060501020d090311060903 76
    0x208880b25410110015820860fa40e001c80c400d031f10400a441d100c076030540035620381d10342c1410f1890400c90300c4d00e4401024004d64000d070340c1141c1351080002e154140c040d00704042601c156800c00290341c03150102c02e40e0b0031501c0b40030b54040d8810084103a0b09540c09000f498503d0319030703000605000c50241c0c04801e4890682c2d03e4900007405c1e41c4144144850210035540107801210342a20349032550751944000e80c51100c4004080d000c0a001800031802241c0003070010031540d480c1199404968805040794804080d480c1c010b40c070b081c40a4103032847c03e164214419400801d95401a0703e040700e0809158040317070010030040d44500300241e66610820410340a18030604c1069200caa5030320a1619240141810a01c100b0f0780d250858400c60700071049903001100b240030603940d0301224805071030003541c1060120a145000c40d0030307801c86a1650114040e248240d0a441107030345802011075030041c3c0d5000c042e2928a00060650f418603100000b00020719000c2c00381c804070151120181c001d4202000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 680177221 1250 680175971 680175983
    0x904090b09190209011203050904050403090807080109200d15090201030509030306010804201807090815010524120a05012c0403020a052406010906050706050a18 71
    0x500000c0d076000e000500290280d1000020b034a4442d400140355008180701c1e030f0302c1142450202406040c4035000b1074070068005002400035041900e401800c004041c82011024020080081125481030041d031229a800004896200c00030007181602044a20041503002c0f01d200780304000201c4c8003a0303035444980700c420000781d0000036000150681d54024410b1115400801c20000c0b2603801800b01030700503804c1391484991047c02020901c4000c4030440f01d560010322045042079035482100d5451050f40c45607200e40805559005540d910107031403d0361080b25403120014400c4d414034501d4a2140e1f034200c21040c41e0049401036007802507009514800e000401c02c0100b010b00c0580740200360040c61098010760041c0024111540c803d800815079001500d0048046024180b08000d10310515070003a043e1400410485004141e89024951000003400c81c0800103c0305d42c01090304504840c80d64984c40c0c0303000800d980e21070040000410915000c1d50740c444e503102030720030020100b006520a170 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 680178471 1250 680177221 680177243
    0x30d0f0201110403120305100902130801111204031107090e06041a060a060507020f0301020c030c0106090c0906080a1d01060e0a02032502190b0a1a01081605090409 72
    0x59002420355800320304514040804200400014100e606a41c403240060b24001a00d07480340c10200c100e17200070f60f2090764428004144000b074441c5204118088444410007007007020b001294004407401140c0d020282c40c5d041000190100f4003d1010a4000504505a590311525511407108039184112038680f19031000040004100203842550301c0c400007007044d01c40d94507158000491081a5014403c00c0102c042404011501c0d4145811000203006000355110382c260100140d40b6041480c02006541c00c2403400289075140b44580c440b0450a5038030794a0040c141001034591000240c01040000d03900c84400840201128201114507802e500100340c2034541445440408009081d8000b081d2040007400201c082c54120b03000e9071a0f20881560b456503003a8016801d2031110501c5014041652041d00100420756002c00d1054070118000c0000c1080c892600348070b18500070006000c16807840c0032425030501040c4404c40f021b901c0c0b921501c3e00006d400170a0540341f05a0046480039104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 680179721 1250 680178471 680178497
    0x80304151515030e0d140705070e040b0a0c021203070c0b040b1f0513090519063806160f1a01230609040225020405060d0510051005030d 60
    0x1241c0040d03075003d18040c480045003800d46519948602c80c100c040c00314080315901c07002c0c00d000c241e800040d0000305891080d6614184c1840e5603000711822598803ea070703c0068090344251103403901c0b402150b070042001004c0c0300340319489540080c01e00024011f000507000c1c009030300e15100c030740b00c0c502c6480c501c1000c0c18030b40003100102000030b00c100021401000e00b80000e8680114805c50200b400201203003468aa08059042c004280da80c41850800300000605010954001303040103030710046024654135900314850031904240e1840544405804042e9429140400160070458501c1180003c41c40c00b9964508694100d08001c030703400702001803201c83c1038a11b042d602c0d005113034007143c600c40d031030708031802c842c400f01d40c000014403640011a0101c1c481d01e6503030580300b20a507040c6940c1d080b040000c2c260074200c0e540e00c0080b4032490510380001e0403420940511a4900c0e8414000e04510038070080c058041c1000801d0b814112420f8400014142e400304000c0c00c40c41501e80b1210122041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 680180971 1250 680179721 680179739
    0x708090a080a030e032a090402040603140106050a090902090a0e0c060703020a0c060f08041709091e1f3c0939091703090301050a180803041515 63
    0x180f079655514208001c1b00d030710524100b88120f405101405c49280740240e4492000800074552a040603100700c082500000d0351801c150701030001d440e001c17a0002132881c0c0c3c5202030020b55800c3e5400039004142c4101003103030000b064110100da02c0816003515169190700700400c0c240e4210310801c1c2c0050340000e1003201031180811110740036102c0c038542008188405c0c00c019101c1100500014042402c0c80d840300840003581c1c0c1070711140003000781000801c1c101048a02d0926840d21100c150106090b03000c25074040f1808995908501a49101a1150710b823011401e00124a80c00c2d24042041208180300404401c3c49a80400c442542c103000001d030502d0316860441e814104011101800e50540f130760f03a800741c030403042090050790f00f24000745140410112420301032a40702d000d0107504c413041c0380038180d07011000e4410107030b09070001c01c1181c0e50307030460106a80c1c9c0507005000340400341c4a620085005a4015680f00c1d00540c085103800180d006000c0459500c1880c8440c1010060700074410b40c85 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 680182221 1250 680180971 680180983
    0x1020a03060504060b070b07140705060f010302130c02060a020f041e17032701110a05010c121b050708040f0803030f0604021201060305070c2406080307080708090a080a030e03 77
    0x1c05030500ba01b80b611581c2d600880c000e01034044070a0107142c0e19055849040401110950350b4020103551160400e409000340e903120a000c124403d1900c01040e07144000305106040a018459004182a403920704425000b0350107909240d0019800300408564116007102150076002c54200c400c103018541181c036a00c40c03e040094480a8104002b81c10030704460303503d4004501d03800e00c82d002180788a0300c0141d0f012640081000002d001c0e031400c0344203101e010340c07021600040c5078461054052418020100b20382c0e016900c956503164103c000d401c03c81c8148064440b070742c4140c1c080c910302a00c48080101c6184241e216040560000040200e11820b440f18290072400c151400d50500d80f4400d0455601032050003040d0400d5500e000294803244152039072102903400240406281c42c10752400301000e00032401000d100341c1000700000744102c000084403502604010340d14102041076881c00f050758442541541e21040520000c02c41c01024003000010910030740b14490958000c0c401c2c035051903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 680183471 1250 680182221 680182229
    0x3090a030f050315090c0910020d020606100801030b150603090c180609040605091212041703060d08030a11191805150715060f080f01020a120f060801020a0306050406 73
    0x803091042c00b07070148801c04130036118207080f24616007907a03405030440000d00400512a5006c1d03040714038424256000f0030303084442180c40c0e0030360301c2980d5980180908000c9900d6540001240f400042020482c889909038202c0c00070001c25800040303c10019009810079030304251582c200103482006032626201d91801c1f0050841044086d160800000d8040c5070700030300181c012500c0718001421141d050010315000006581056111031000030295004607040328211018600d100c0721496812800742600d02c145401002c45502c003401e0b982c0d04034280c0029242e048003030389920112002014010241c44440955a6108440034500500905038044c10840d001c041c40040420f1000313440d0320058a641e0a59050720326a1007405190054200340716603040e400080c6030400105101c0b903049101411909200b04940c0101241e45402e401c03072107040e800502003001d040286490901c1c5402c003c4920110f007000041c0749a07a2040c081c00d80e4419242c0100281e610101070001c0e140500c0f91030007074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 680184721 1250 680183471 680183477
    0x3021f03150b0a110a08040b09090f0f13030e060a0c030f1805010f05130b04080f0105070210180c030803010f0605070507060c080f0a210207110f0a0b03090a030f 71
    0x6618016840c101c43c41103802c00030030402c914000d000d90440c00c02c54012001d40c001e00303c2c0c1d69960fa4200354940c0d174100c2c24030740e4480c94014000c00c010146144515001e10041c2c1840c030f01c10303280c00980701d00100c0403039030841c00d12455101c043c0080e41e502e005028091340035110003a254400d40383c000c2c007008511820300d051102c03101e03071280340c0342c18050200181c1e04c00382011082d10520407025100d900070031144040450160301c002c208036100c1400f410841d000201107401c00034003500101d083e50340c2203c0e41e00042e4000e0860a01e01d8896401404007aa298070f03900d400c1211980b10130401c048c0341d41043e10291030020040108401000e0800010300e418039000b418540359035103c5884424910a05080040300b0860f0001d204004084844902042e41d596590300402c04000d400c85078142000000c1c1150900e100100395402c4c001ca03841d0729030101b10718020088403810007441010510800741c004d1601b4101040070400400218040c00c900ca00400491106180041c0408030240d504010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 680185971 1250 680184721 680184761
    0x370c1202131a01030f0b040e0106060801050306190b01050702040c09060f0c0203250f03060f060504111e1b0a140a0320030d0c0509130501081b030703021f03 69
    0x2408141d00e1501d110b2200c01d18003c10828010032018001d401c000d4125030340203140800e6426040415800201140c9403526550100d030b90310001c05031035441c22504c10307000210840c0d0295950131694400882d6840506000e82411082e4010a0071107075100040c10110701c400c00284000790304051100c001012510788500726015030342c04a030b240e158030840306203090100c11507603284818201c2170001030025034041300d134050303580e04100303002c0c103110503800c20620710380b05000c50182003c0c092100704801040c0310318500805803009540d0f0201a4400c3d111040041c41100c40c05815480b60055103040d450040002e24028248090b0a41c50042c0303001c0168469000c010000341c001c07059680303e00001c0e03444041c58540c3c0310a43d00314450101b111000a1278030074044862034202c0081c1c50382c000c05540800c0300d03001e91989081290020b011b662010350001c3d07400000c108181c420030f00080000b0702640d0b0150354075400b080b50341000c20540303498074508203541c046866040c421009580042c9000d900 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 680187221 1250 680185971 680185991
    0x2070c0e24100c060b0306091b01020610170106050909011e0b0108070c1a01030308011401021203011514040303050a021603020a0501141c050612370c120213 69
    0x100da203008140034814490301c448a002448020350099002c5c02015054030840c0c50000d110320b407104120328041400c00d40400209505501c0011a180720f050402c0301c5d8060142807050001106403030342143e500641d210080032682e611282152070142e01d488002050591000c0321021040340c0341c03512410301916281c40c034185030b0b03802001d00350401c402d4101648030010906081c3e900403644043d03081c80d54850304c000400c15034400f100038103c445d600023915130509503600490315400003040f05c035491181032005104140c0d0000c0f00b04144030160514118a91006100080c6500682e0040d8007103640851404c900c0c1e40c060200b030060064284030812602d0666001403203492481c010750b41080280c1403042102001c030360480d034a813801c2052400d0f50400d84030400d4042c01e0100c495500611141265001d03118000440d9014104219031001da0b026401d801900c1420b0302d01c0322040004083c81e804030100d04510030000140c04224a110b070080510f0041c4401a4070310400e40541c07038a4401300070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 680188471 1250 680187221 680187229
    0x1509020708090d140307050303010608090a0b150406260c011b0602211512070b03010b180a06051806070f061505180a0c020606010207090f02070c0e24 66
    0x90407106045a0040400348541030130303035241300e80a0ba9070341e091000190640138440f0002c0a14101c507003903519040702d60f84408a0a4692814590080c030480701e207004a000035408004100d00d4003009040064140d84d40c801e0700143c1d07105503102e20780c00f10410504200d24001801466100e000a0074092054030b10703980c80100b5201102000340c0401d070301164441540c8201d4400740c071412481660242541400d402032045410101c0d0180c4c441c4103080f0a18005410204c2d44030115001009034500703581c0b0748041d0420a50008010500421002d45030b022180d64103911580070700803540d41e06449002e0070042c01c00c2d00c8440c83c8900e1041034244403240002e0b0345014102c602c0341e0311200100d5901c01e403e2200b0140c034182d0700708640c04810401d018810b183c190300520b114045901060224100c601801ea032514000e5940d00d0041c0c0200000744101090740d001002c81c212845801883c103405512803450810f45600410300c41088102030010310002c2090300c00c1030589250904440c030000e00001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 680189721 1250 680188471 680188477
    0x111605060c0c1f09080d0b04052202040b130908030a0507090f05010315051003090302060a0614010513260d0f050405010e060c03031e0106030603020310050414070305011509020708 79
    0x5009411640844501c1c0c40b0702c3c0340c0201c00071903070141c0340c40d480c5e509030246800603000030b80800d40140d02d424005411000601c0031244860f0f4025620300206585809000c00b40007e40c82039504202d50514a504000c10303842a0003465018082c683c0d102d041c54003080f0182c442c050700260030401c1b00803007400092a21140c10f4100e070b100b400c0c0001d00c010444050404a05158405a4007420420104500b0343d0590080700040740719500b41c94466641010103001c654040c0035603681001510710f851825401500101102c407043c42841d0b040c103554540400c008101c1080005021a6804452103150010461315019480ca4141001c461083c0003008003e401030f48145410030080c0320b000f9400380c071550122001e05800c842030b01d65070324000c00d0405a202c40003010801e400100000050f92610a100700c0082d00e40c0280586002c1c0c40080d010400b600025105a50080115000e208c4000c0100000301c02548a5030020170741c41c00700f403c0c0842c4440039a2003400d403280100085400250480b01b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 680190971 1250 680189721 680189743
    0x604020a140604090c110d050a0e12060609040212060420030105090c0f0406031b0f080d020d12060e0f101409011e0317030405061b090112111605060c0c 67
    0x1c0010070950401048a55486d45126401c0501070203268150044e84440103051148481e107c0400108000c428050304500510041505802000201d401864440b603040d0300140014400150900651942814100259012154040d00e000c440000f402002800310075880700b10300800451a000036595101e48100e4401c5128500480350700901342d032143d00203030146420100300005001004290910808076002c3c121641c240c2040019a210002034000ca104500f68041c107098441000c0550b10200f001d910121055150107010580003640080b95208030cc0d1001c00d200c0508105103140c000007625044030000a800321040d074a15154005014115031030007024840c21070a003a05950703880401c3d00010510180c0081031408122824042d6001c1d50003181616865260030a0002d8a00b400500c0199920400e0124001c29030041d40c080c1000d400c03070301340403542440500800d0300d03642c0200038810340c1211014581040c80810020141c2c400f158440c0e0902d4512000e40c55070383c80d032441c1d02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 680192221 1250 680190971 680190989
    0x601050f0d030f02030d11090a1203052b021206150412110307080607051e03100e1f08010903020c0922172106010c0201050f2a0604020a140604 63
    0x80281c03d091003002121a07203007031101c08010b455540010b22440f60302924034544102e00400010541f442000e04104080d80d040e2a034601d80b00103803030f00403000d007255130b01c40113031494a925040c05001c0314002880c200c40301004000f40d500c1c204007080400b152044450858100c140000c0c48685c40400b410f5030116003141e66040b034450130350002480c041e407a4000c60242d014560501010700c2e00580500b05001060700c00e00d6031b0b00c1c003443d55002103000860701800020041c1004005211214440c02d42015407804401e561822a080e0100c880d60707290f00c4200075030356030780c2d09005140d4140311b182d420010480b150b0348603092084040446100301c0c1c503040d0582d404030f98400d04000341c00e216016501c1c2050002a2201100402605044584a0942241c0c2820320024000f0b40c41107190703800055058640c181008000300d425140c035000b100c07941800f03089010051341c1c00411080e00c1c2640d20320190060500c5d01d0070340705014413a43c90b64410302c03440350440071008090340c3e002d0941d010b41d41c0c40c1d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 680193471 1250 680192221 680192237
    0x100f0909060f020d0b0312070b18010207050708100b0f0d02150c0f0c011214041103030706090c15020703050303060f0d0b100303180f0e100b0414030601050f0d03 71
    0x2003004030080c80302c42c2e20140001d01c0040c0c0c40303418035596000020b03d00800c405030741d080806408103200910510000416107214240010b6102c030b030712046d49810740700304000182001542d41c0d4182c64507120f5084801140e00907030262440791a24001c00c0c00300c150a83c0e880702d00510321404a9000720b03003104000c0c03140145e64400c0d03041d540d58805441e0019041d42c210750260007201842034039150020841d600040c1582812101c0820f0b9000d08203d4551444566010707540d2343c0c59040205990380401c5a06010400134035000c6405409110742441c01884e2801d0b4091410120f00f004a002d20505415904400c2e8100045040482900d9001e00182da080d00b5032141c0c1000241e442201c890000c00d000d0090050102c502007003e09041928825100c250402d50000703990740c00c0603654880c91100416002c000c2c004244030000c8590440100e208000c031440d01e50310900f2186d08107400201d420400d5000c946c40b1498200302260060a0a0315000e404203203407004501c00701000d42300502440a40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 680194721 1250 680193471 680193473
    0x30703090c0e01140f011b03021212100e07080a050a06030206030705120f01122a170106050604241716080f060a060f05040305010f0b010206100f0909 66
    0x250000d0425a50090000075000d8444101e0064440c080c06803044144a100c021401410824010030944805071034840c12406c100703a0b81c1d104e1150b90032085046015800c00c860341d007074214000c0e0804c46800c003001120762619107014960403000351f00c03104082c139565007031140c480d4000041070742056118402142a503039502c50a00a400581e0000390010800410003440c1ea5021003d004601c2d034145d400401c3c0c0e1100701180c0c0b942c2c1030a01030440e58900c0c8491480c0000e48180c0404502100e03142c050300700c07810180e620118000554021070641d16004103a84021706c00380b28400113803008441090a050400168182980c0e1600f025000c04036140c4074004c049005103e4207040940c0d801d402009894030b030030041500074070140040c0208500030082180d0780d42c1d43c800c2034421040501404816841d00208940340002c100968003132003c100070200c0418030071300404940251000c804a258003100c00028070308100141076880844003060240500681040c00780101d580c00040410f01c4841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 680195971 1250 680194721 680194727
    0xa020102070b070504141e0f01030608010606080f0f15010e030c100e040c05031302010e01090b070305191d04200c0106090e030a02072c0405060919050c060307 70
    0x107840070241403a104041002481580180284165804240e2001480180302c05001032400d0b440c1c22554204030010b6031480f181000d0703040d941198014540031030300f50703512100c480c21180a0303008040020000820040782c040d0304c506183d040f255441c01105141740841d000e1b0008160a11010304014549091300070950302000050400040140f1481408a603c0000707001000a542c545001ea070800c2c0d1034040030b50146083e00d104121200c00f000068042e50300440386524096002418009030100c0800d4281560016181c007900c45d455856403591441c0e14402c444003c500b00c0300c20804555800c60807900c141c00349041070241a0b038042180c28085a81900340c480c0d1400c911203e400218500080060540180084542c4007104000c3c3c0e0444c11940c580300d10503111000d016900c041c40400200e4221007101030003142d40c03600c0070310901c101c0c6000e040c1031605481c181d910358441e8051204481d41030000c42188442e8990783c02c0d2140c5207581d07440c0c550003404011441510080000354200d40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 680197221 1250 680195971 680195977
    0x501050a0507060c0f0306050a03020607080702030f10050433050a0e0109110406050f01091202040f020f0d240911160506042d0b060f1009030506160e060a020102 71
    0x250143e410b0051605090008001c0350070a40b060700000e00341240007a07603080c0040c20001b40c0760003030021031802505032105c1d00b682d809488100c2c0c0610aa84101d4806e5005000c0c080a4400001300462582881d0822690180a008103d01842c00d80030501e102101e0700c0c1c44482e121306041001007643c1d611420140000c0007000300805495090541400c100400d11913414510b92048038204a8035440e01d05101084240c1e015407404a0a410300c28028004d07003181d50b02c1c40c0cbe44024800701d99525048200e07000e0340c000b104410800c4d5000305010180a55501410600300001d40080c4848800e031401d0700303000802880307650072495564107252194801c942c11150300d0340c0014106111180d4606d0036aaa17601e044034140c50001098500030500111082090804146c0c0120380c00c0c4541e81303859084050b00090b200e00d6201d10321241140c035039114001c8004500e221611400d94040c0b8500b0060704008000b0200c40301c2101c5400109009500602c42556940d01580c007552034055180c0c003a40288 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 680198471 1250 680197221 680197223
    0x10120c03050d0e0a0e01050108070516150203040605090c10050a0207050a0605031f060e042f0301050a0b130e13080301030c050109080d08040312021b01141f0501050a0507 75
    0x402100101d0b290907410100160f280401542d8280700c95a458488130b080d20000c2c0134440c0010034034000300344141c0c440c9020f0803a0401c62000c0314205001d80c1c0c3c4001c400792070000b10007442900842008103005607441140d600034112405403880e01c1100002507020361800703100c28207004000c00c40720b8905100300503071005008050801d00340d00ea120030b4007500c01c0c0c000301d5040a280c062903003013200d000c201c0c10000045070f000d030f110301a08514810804c8083d01d018044100c6600000c0d00042820380744482e1002114001c1e481c440c1c2c1d80d4104014444600c1180c7c00c0312105d035000b089001840310401380040101c8506a0b1041d0158541200f0a0050241140d018203540070200002c070034044094200002ca0703209032030b02c0e507181d9a509406a20b4501455450307004c07400b0940000d011a006400010640d85000c01c0146064540f96110024252092000c840b50799078400413800090556441c6400045c0f46129100342040041401c00314205405890304100d40883c0c0e40d041e650081d01076901070703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 680199721 1250 680198471 680198473
    0x1103070f0305030a0b0a1d0105010f0e04020322060b010806150f070614040c0807050f10030b0102030c0d030f0f05010f03080d0908030f040209060604061704020a12120e030610120c0305 81
    0x42c5680300c1b03548504011f070340d690148882c1e1f28400080c007907003d00015007081640b070b01c5250005c071040e010040290001090501c101518002d02129030b50f002a010600c0303886540001001f0300520001800d20704001e1845008100f890104040080c0201c10f4441001030a90350660325181481e0400c060142c446012036251094014003080140c030703004030020f0f50003490407a111140e07103034100704d0901c42205955411041c4a4480013040e440380e00020075581040c0126458102103c0d100e502e0200091183c100003907850700103070070040b440e006012131200c3c080c00074002541440400901d0181c1440014103074500007811000300c40e610380100840941000400761030789400c100342041010102c82c120f1160035410f001450901c0e00c041038409036490765440c0072080394070b20f4503903042c0c51003d4016a40108a42400106860f01c0724030351900c00d2248143d10502840a13a02600c0c0d02d05502000707200c0d1300a2030810611841c0842d0fa4000c9488814840e10b03081043e09240e202c104041d0005402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 680200971 1250 680199721 680199739
    0xc0a031502160c0e1b090402032503020a030b090103021c11090a090614071e20033609130204060b0a0e030105160e210703031103070f0305030a0b 64
    0x43c0007420054108443c00c0502c1811169284001c0001c080711400801c40d00c460709003c0300080c5d082035406141d1140d0b41048082048008031029242031056601c1000003980016010b503540398903005d042c070a0881511405415410750340020403800600285070010345504800d081030184440020981440c09404c0046904048012102419012a054070024201182e145d41210800301071441003205949054019080e04690520400004040c2e81044038000c0300c40014001c10020124032042c400c025503a80900070001c1065811500c51108000445403180c4070101105000c003180d0a070807650240290369044924481040d55107010707402c20b1901c02d000c03403018161801072505105545907400024151002c00d4242c2d10f0484101d43e03a000c0c941039030360311107000305103003942c20030300500d0796001e00c120714224242c01850010581c0e2950020408005064100c1464040d0300c0c503400c042d42ca003640f00e44441d4908203c014008082140000c0002c2d40840c60741c0c810300003200d000b828505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 680202221 1250 680200971 680200973
    0x2130e1f060804020a1a2a0105090a260d140601080a2f07051005100f06020303160212160b010f05090c03072f0f0c0a03150216 56
    0x990008000811000d11805400c0803401c1c50250422030301c5581d00810703d08449041041c046241842e0700c8038400a03503820300ca203001d50300d50940749460403040105841825140148510709413080944025500e4001002d80d4021440e12000d4540004421892400103100340e592510700d407044c03288065917245850b40c141035040303c0f4070b9058060002640c0303075031140c4c4134455510100c900784142c604c40080340038051921210908540107000c042001e442e400c1c4407164407100d04140043c1c4844015076503072004c100d5103270810041003025014039440f401c0840d06050f00690350344000340500404007803881c19540c81c40d1007003081d54803007003002c2903c540305d228044400c1c03401a06410111242c5030300500114942a040c904007007201c80080500b44179881d65040458150b101420361810000200c4ca0140c07000540c101d10200140304400d40c100744280603901d1410301c440000c5000240c1c00c40314805000d030760340070f91040549400040f000003c0301c207408603c0c020b00c9501840341e2440d0100281c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 680203471 1250 680202221 680202241
    0x3050901090f12050606010302040522060e010b0d05090c010f18171609180f0f02031506040515030c060a030e060f01061e0c0807020d020307031118010e0103020402130e 74
    0x1c281c07044d811581692504001501640500e0003081d4100f00c0b00c21407032014040400b44240c0141400031300140d103a442d640c82d0031009109821803c515900050041c1d0310030800d110b040e9111a00c80050040d29000c3c0b4002405d40100b161a0740401500e4850f683c107903803100002900814010a450801004410405488100d102d281542c4241c1c0d51000090021170790107000300f40c1c00424180e1030031500365a81e001c7d640d03c03506c00c1076400c0354030500810010780301000141190300d40000313034291501c5e0220400055500080c443c0008012480380c0c80c1e4962030018525103106800c582c05d03a181d0140103401c50082000c500711450902c41e040034842e42c0c0d0280e004250581e402035882410101091211361030529040000600140c007641280001c51568000750000324030003441c0058090143d00040c2c54425260020b480d2042003800a40e0b032803810304242340306201c00030a003803555072616400c400d28480512000e4051a00010701442c11000040c0c1000a00701c003c40300621424290410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 680204721 1250 680203471 680203499
    0xf0b0c1903120e030c06010608090313030506060f0105120601050f2107020d09150e01030b06030a0c0e100c11030309150d11160210050c0307030503092803050901090f 73
    0x8850701520f03040c81d200201a0200482d200e00380041300404041e4a003020031103032110000c0000c00340d17010510060040102c1d1008000095005030300602c03107400d1100400c084401c200d03460a050000c100400d03101210340d480800c2d8404401d00f8101c0d03c0d608080740c801020b01c07a982e140d00d5855016503240c41d20f0b900d4a106c090080d80c0e2503007260b00c00f0300c07452016100880940180a0042440c40c10104820f2184050324091401031602181440d031440104000340c10544403010710940f54401c0b0760b40355a0084030720911800071155001a03c0c50204098041d10640c3c0340900341703825400500c0d010303407130400c11584240b00150011041c07102d1444c80f02c0c5140c000c80390302242207040032132401501c8001e80564020010300f80d0a107408130080d40c200304903282e10303c41c00c60a2040c00c1c00003040120b0144080d081c0103010383c82d0983e0381e18012030150b0405070080c11034515007140660419541420351044c5d150950b141c01c1007071340c4035086001a20386038426888440054002e007404102d0400421403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 680205971 1250 680204721 680204747
    0x102a2307151404110a05040608010203151f0815060301060203040e0c0406081303030f020d0209131a130605130207050c01030506280801020c150a05010f0b0c1903 71
    0xa8901d407005481803140030b55950b55007440c60b40300800301040c0801c034400403039401c0060003801119900c0d510404141a9401a4000042a5070110820151110601030f0070b000410403201c0500503202c80040c45089027042d007080e01007080c8000081c2002c3c2121040c140130880c01084143c0f20b60b59090000d41d42e600c1b03809880d00500c02c140118010f000071005481c1980c4207a100c02c41c0320394410180321000072001c07405504058441e00f007800145568030041208081c1400d000d43d503920b0403400c5c440c8a44032545081d110302e2a140544030f0030580ba1100354007202045496181180340c1c401504013410340c130f80015a00c020380c48510703082c81c0ca4641c01004d0003480382c4140c400400300040107408072101100d6042d0040c91520000320442c9a0541c1c0012102c0011601140c0c103444c0d01e022800c80c5c00540c04103083d9401040a407202d02d800040c0f980c0c1c030403004030b401d106c60760400c03242240d41b200c141b15020031140c0109130190045018840504c20f950103000e01119480c1d030b400c00900c80c1e082450703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 680207221 1250 680205971 680205983
    0x201140d060b0c03130e04080f03040516060f0e0114030a0527030a09272c0a0515010b090f0112020a171303140304050a050717102a2307 60
    0x40001056007013040d86c10b20407500502464240341a40904071aa6030006100319441d00a181d070042c100c841c20841100900907a9403022106004c04030098403201607091024180100f5560303003645900401c0c100d96000044203000f051940794004075408081e0303003a1100441103200c030003802000d04c0010241241810070340d0341d10300c1c1a903152280000c00000641c405400c1c0c11880641281107195048140c0702c201070701c2a140c500103200020f4689a0088410007d950462070380101440b80070407850f00340c1d248003060007040d549421401c0c07050344151104c2c0d5015154802000d5810b80c01a1210550031401c200155916104040000d041c803811800310340e0301c0810071002c5524040c1107007140728920713410f0b00c0c2c131050026101d000980d150030050013212071b88103d00e10310700020000d011f194000c120a0b034080030000c1100075028140345110388620f040e02d1800e45000c0000d07801410010448e00800d0501d80150401d078021141103c01e8800130701c3c0b5070341840d200e4000000c104000c02c0143d009031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 680208471 1250 680207221 680207257
    0x18020d080327060a05151e031501050306220816030201141303030f02040f06050c010c0c030e120705031222140907050d1b020c0d0201140d060b0c03 65
    0x5038103807040b40300c2e02450000d03074009030008440c3c0c09160701041d080f08140d074100049030005030000350140382a0b04d8120300c140c010307103840c4180c0c141085a0580c0c802c11a403c46404d40c1800301081d40c4501c02004403103600b030040001c0403d1107011a880c00819084030415a03170f0b08094220f440c81491401045006619080c00d4a00c03503500c2051480c080c2c00c9100010814840540f0110042c009001035041e00c40e41c20000050070a5011100400910141e201d0030340720101c15010908460b8842c401d41c080c4a030b0000b1260000707510644a0f2181b000407905494000b000c40c17071051400e003072a002581c1500c6145004400c50034004c001c0d00d01d851114842040d407001103070140700450480e2144000c0d464850000d22111701d0055100e907031100307151a2842c140041d208900d42035403e0880e5009901e4114008218000d030306010007010944296071070498071055a00003041d601c4201c10008032080c0100e1036114110007038011034010030150744116210602510495142d500503100040340411803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 680209721 1250 680208471 680208511
    0x1b120206090d0e01200a0524011d04060209091005041d2107120c060c0302090112050a0b1f09061409010e1503100f230418020d0803 58
    0x308048461442da543c0030240c040e807030054031202e0074890b04a0080344188200304040d0810404401c2260051005005025a880000d00c0c00a101e4108140c0c8004020061140c03400c0c00664100c86140c201030031071160f5940c10f10800900400300d20030307804407404e02031250400e0241d00000a960302101c1c00c00946201031190100e15103d40c0300c07000c890300040c20021907010101c041141078034800a000380b80442668480380003032035140e050004a5100d50840d401d00c81d0502c50684140c080d401c0441c0b42542c484c001a00c0883c01c4141d80007015151b50008604400303d030400440c0401c00303442030003445414008019410400c144e03d00005400030b8002804074440ca480828445d9032024040c6003c10403001195603880e851143c0750808075200c1500c0008013444011403103110254402c1c28070380c0c1481c0810407540c0442e44413182c503403910240f84e00d0107030307210481403c03000c5c0032100040e108014143d500300d0100050720203540702100108000c140010003000b1846400382c41043e030316030b19130 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 680210971 1250 680209721 680209723
    0x60d0b010e0418080c1f0f06050603010b07020d052e0e0706050409021e0406030b0a0519090509100510150924090803160b01050402281b12020609 64
    0x40340c0d218090307a200865039034003c5004c0314002c00200d415402620b0b801840c1c0702e60340b01032401c441c0d40a044603a8418010039108031a02c183d001602003203451900c0d651401c005c001880c06214030184c400c4403010144401c0000410180000003035205500d012810115500f6480d0400c100b8546042410b11104803c2c20201180280a890168403003505103402e0520100c02500040821082c10300f007100302d403480c1190b52001d4001021150381c04203040038668240503440c072555002e54091740440c06840382c5090150031100130780340c1c4000b0001c1c450b6a140521031400100081030110507140100b401003410001c445201070b180303411f00c080d4414500d81f80403190400d251041200721042e961345490200300c1321603000b504440618011030316686402801733045520502c40c401d00320114807910020170104020082c01050111811407e00c101f0201c090444e420401000041c40b80402d04040d50500a40300d081d542511a2600480c0400c81d2410a002072703100781c0e2a2015100b02c400050344804 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 680212221 1250 680210971 680210981
    0x6030e0102090d120302071709031b060307030b041b0c0b0c0f12061f02071706090a1b1d0a050c0a09030201030c1106041b0807060c03050a0509060d0b010e04 69
    0x44041c09403c1030168603164040500c8240c01e6801c20150200f040c400422420301d012030492100380444c65854600104162034071804004020408166100d292050364442054940c406030340c1c1030104207000d660340040c00802c030b2460f5880b10320070440c00d116510f9611200741d01d511403040b682c05c0190385030b11451000c140505509481c4a480400001005110601d1683d80018020b0540c081f088031084e90400c41100c00741030280140e2010908124414141d2007080b40c800d003640103014141010380000780c0b5050074200c05401e006a014826124881a9105500911042ca07046c21610588003444e2040841074a62440340b0f428072004c220760010600803100d4004c40c944070000210719660055015001043c007031418000d40f80040391144005005c403a1141d4401c0c000c820100785d408152070000b011135042088203500c4514117200b01038100c9106880c40741c044c1044d94454404c04402c4034507104040501d600700e400410030209881403504070314843c1409888400381c40011310203200842d1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 680213471 1250 680212221 680212237
    0x3170304080306011b0f060507030c0f0e09100f03060c020705040b011211090301020a0e19080d230403050d08360a02090915060315070f020a050709020406030e0102 72
    0x1002c001046040d0f004440b035083d5482c0710080002c00c1685600c0b80000c2981c10101910002d84a0b01044212949441418035109c02c909044808000c11500149280c64245416001703501c0e002c0415817262010a0300e5005000b0704060704002c50b124603008000c4d01c0040401405031107a40c1d00400c05180c90f0003400031124045c1e68140e0b48560708450380700a802e0715035035000788420801901c3e226440a0005003540003154454030058000c0c0e50900c0358007210144403071840ca642900510a0f6038010591404000f00c0b40340c08005092540c80000c0011003a012030f1990900c0041c0001c20481c01003018140d000140e1100551540c0391000f40c1d08001c11031581071403c400e0107084002010789009180c50680005085941280999020400c01401507468064980c040c813018a08291549000c0703a0040007580582a0302c035003200b2180c14040040d00780c0341401184404074140310300c01c01c440a0700c182c20004450645903500000c80c001d503c28060400080d00b070200c01020070805008407075280c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 680214721 1250 680213471 680213483
    0x11040b0903070911043003030c0327050f012711061b010516121a0a09021c0c050d0b0d020a0902030a0b330c03040b04181811012703170304 61
    0xf80c06d03603604600500109145200741507070b80e08865042d0460941d02441054041143c41040300e15050292070001c07203030382c4003106a0500100400d42c014a5409007480c08404092075008101403800c00800e1890049190700203d0100c1da00003910218040c240d15440340384001c0000c0d40b24241d00098a414105010011445441c0380540d92103c40d4022401e0201007000f261040320714030001000354150f41e100801c00d50700440d00d19120503035035042d08140840e6603001c0001341c480d407030061300c1c501031a515032042940d203c000d9030f02515400d01e84103416500511184d142901c17807241000035001545c0d40312103180b8001040001e801c0c24004442c0c10b1440d080800e02c1c101691850440486460032220000728007400540ca40c80c40400140000c1d005030b01420340c54a04246154940702c1da02100c00c0c440508192105c1d0800070344080c0068950b8120298001c00300b120001a22140c0051a01488010301068030350340020741000303060242d0744180174007903000409402204140c08160b80c00341030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 680215827 1106 680214721 680214809
    0xd14030d110703030608060f0103110d0f0c15020c061b0a050d0906030507080f07080a11070506100e1608090705060d02091311040b090307091104 64
    0x5000c0c40402048a8500ba04440540342070603c005805010782e0748210306552640301c0c030b80c4141500f083740030541e082d81c1d2518580300700c1d4501c5500d5a2044503100380b11520701c00710342c00400756401007009042200680c840e8003000301c8001030002032312500b20340c0302c000350041c4948040d01401e0340f0707a407806520f03003107026058800c0105034500304080201004400c031996000c041e040603561402400e9540c7d0b580900b001010788404241d90918003007088000c0200010705240306803c40844200119521202c0900241d03040d5414890f01580503ca0300702076100e207810b00e9020403024110307080c1342d0741ca4000c00d006901545403040c8181c0c0000320f0310a80d0034207000501e4002e80c500c1e020429403e10380f100015a00803401203800c0148005a81c25156604011078800f6203a0200f04002507400741c050255954494030035166650031940050444c80c14007480c5121741110a020a15 = true := by decide +kernel

theorem cover : BRFrame.Cov 680035971 680215827 := by
  have h0 := BRFrame.cov_init 680035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 680035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 680035971 ≤ n) (h2 : n < 680215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
