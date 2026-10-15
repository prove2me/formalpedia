-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:11:48.738978+00:00
-- url     : https://prove2.me/submissions/ebf13972-81e0-4e1b-a97b-26216e3ab0c2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 774820143 ≤ n < 775000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 774821393 1250 774820143 774820147
    0x5030304020307150e040510080a0c05040f050f04110402070204140402090c0a200c03011d060f1014130c0e13111207030603020a09020403060e0c0312070303090209090d091703 77
    0x1170a000250000600707044c14500d50398000224168180f040b003c94502c900c020791b0f4005d0034281004100c50429113403001c0d1610740380030000d040300e070001074581098108442503085c00981c00010080d201c0d05a0082d00076081010b02d0440314040c5002c60b020b1032007201c0d2035103c0c0d51406a40d01890003442c0c800c074000380c480742e06400e1040c0d90328200000d501a0001703551002034000d004c130342580d4004001c220000454803284145a0040c0074150b0003403c0404941803509000740c600d6104202d41c001c80070724910021041002d582c03130881010326100a0300e07051041c00580d00000e0400310040c000a40542009540480307850703900d1140a141c007204400090038008150503001503120001d058006150f5203070008805692003da8980c0213042445000d642c1c2c0707003140b80a000b07a6030005c54020b136075482400200021342e00800d41000c0442461001072b101c100604084024010039a0701941107042c0005101d082400481c00f180c81026584800d2050b580d1090b04070b00e20b1041004002c125002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 774822643 1250 774821393 774821417
    0x4061202040c022d12040e040c0603110a030c0c0f0b01080d03050903031f0b0c01201c0216021503070f020303220204060b0c0a0c0b07030503040204020f070b01030503030402030715 79
    0x4c0d900500c1808844801250b5805681c0c02d00003403194070541044202d00700760350403c400c200d82116140040c0940d49000e0018010005100c2824014000584145a1035034900d045c41c9200d07060181126400071111601c106c084e08081541000c280210401801b5907c00440421701a006190044a21074011465552108100c00c10152659030260800601400004040e0741c01d01c003419a850400e40005182411602d0021500100c40180e49200743e040c005016802e07002d50841c459505a07200150f80c0306030907d124184880282e00084d44000a10721302501140c03805e000d144101c4840e00c61104012240c14243e0392400216a086240100c014200300746011118521030341c6440684041041d503114140c100b01034000c1c010403c000e40c820b01090f01071066524a8400a04135115910300e000c2c0705440003485d921005102078012600010755205121341002201c802a82205c81c4102030350310303850310740e85940c07040d1810380c464494400c0210740c0700404101424054402c0c4c541d0140844 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 774823893 1250 774822643 774822703
    0xf1103010b060d09032724200304080106060c150509100f02250201090609260c0909070603050c03100603150302030f0d1101050c0702010c1104061202040c02 69
    0x15201004030f0070810501071346400180c06070f03a0024841440489200140d040c09107c0d1585407200c1d0b0200d441d0089100fa451450340c116403951182070512070601003e0488034902882c6100c0c0e5407105400d986444000940d8903848820303501d000d8800e20348200700b1031100c05040281c81d016a10050903420101070040c10000d280d100304101400c2240c05070402210301182280410003501d8000048a90760b41101190703030260212016002c1c60400c403102d541071041c0c1040d919000c0301e091071000000c2c43c00c44260302d000c120246481c1402010740b4207528105600c5601c804452203044080307801d103004944241c90382e105803071241840c1c07418500905c0c90b00008801509003040403a12070540b182010016032010310a40f020311401e4401805049180c00009025030041c40c0c46070103991500c8140803c2c1070701c01c000c80c0c1e0003680910f09040c0d2204941040c0904501d603540141c1e00c10b18055000030340c000f2880d241c0c14405d00848040080170002d100690300c60b050140c0d11b50b14208840c011000b410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 774825143 1250 774823893 774823901
    0x301081203040c030b0a0b010f02060f0a1e020408030405120106050102030304020105090105130311010f180501050a1107090504120f08181f091209030b0c0a030212040f1103010b060d 80
    0xc1c020341910b402c0f0b980d00e8840810000c1c055400c0c00906448200c03c00095070040d40078200384240c1d1008080c0303850700ca0000e1402c06c101030010a00c0d41d89405801c1010701c80803903581e24203850703d0004c56a0750303910000703290b8aa02520899004543c0340505444c1c269044c4078042c03c646060b00510b10390b80d0383c8d6004594541c451040300d814424240400003802845903444009180b2880b80450401040c1002600d85107900c01103004200d8012000200c0c1c8140030f016074221102800d107142c035030062402c1905d60b0785106c15144518441c2020000300014240c101d180a01e00402404c2d40c0048005800c884030107959900c20080390b400c8020509200c0d0400018111492180c15a11007400302201034000b001035600304c0012540303803446c82d01800743d104891700700c40390320741000b540080c030716501c4036085040100540a000d8000c03c0040d005406078045a480d001107010b0118149410f252440500c00c100405a565110107a00100107003814800d484491400403d99400e1403504030b5401c000d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 774826393 1250 774825143 774825151
    0x40306050c160f060f06050a03110d1e0b13031d01110a0c17070f0603020721020f010606080601020309040b0a08031b010c1b020d0609050d03150b0301081203 69
    0x3100030803070200e6030b007040c5049070030b80d03407003003440e1085890340707007040c100351100704589040403480e201c4204402d51715849600308896201d0091103083d803038030b400140000403043d40a007180c011002d60880c004001c054543c5000e1060f1445801a291440d030286074421040f0000d003c103121510700161070701c0800184103064014582070100c0102e4201c0282002c5118000711454207099a092012042c501885142100d0740e000600c0907501c1c0201c40540240345104003001c0c1680024280e00f032040424142684016400f500d01540781d038403000130354409142189031415480c1103001301c0c110b0b100b06d0005005c1e00f4146d00031424030701da020402008125003080703d9406000500c00081184040c405001301d002c01e2180c00740000d180000c154255051340d60441d0800900d652040100c00d503c3c1c0142d031030b60343c040d02d12400480789407801c0002880501800381c5988030f004036843d081c40e0f050700003501500c00c1c0100400450790f0386680d46880d0200b0700034846507402c00d8644081031500c01c0050761744 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 774827643 1250 774826393 774826411
    0x7020127050a051605030f010c0c15020c0a0b01051c030206010513061802040f09020903150a0e0f010f0b0307030b06040207030210050703020904050609040f200301020d06030203060609070504030605 87
    0x66007420783c0c2e5642c64402c0c0107101500f1038907540340c1004640340900400c074201415100034071044825010007080d21310901401424242d40c907031000c00aa11540c140d803180b01e161811541c481c041c500380300d200c81000348121403069009074250344141d440702c606807400c0759158000344180d900f030038100b140c05114407990111980da6400002801142c00c40d000b80300c6242400c0c0141c0e641d0901c000c103001072005811031203a0500400610020b41c40c0010b5625104451280382c1d8065105d04101d01c010b08400c0f80c40d0f8880c4d02c501c40f281e0309240360642c4030400d662103072a403c210382403c10781030585550701c0348005440241c1e00e2000500b41c0c20141c005050b00c030301c280305031005498207150400c210b95007500c80c980020341c04102c68100b8206071180d1500540c0c21a0a022a850595248085d5000402d0001c00d5440b1015503440503141c20005800d9210004000f951926080900400101964030050f4464842d45d000714009050100b0807074010070982d03680380c0c40d150031901c13040c01404014107400d00e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 774828893 1250 774827643 774827653
    0x9090c03141501090504020f090103051b180f071b08030c2d0c070b0c0c01030f1e0212062202070f0210020102070309060801050a0612110c030a080702012705 69
    0x1907810b1240c4440b4040d01100c0c00c0052282881c0c01804802100038400c1400b8511800c01800414400108194800504131401600b42d1520020584558a1b84003420792105510240300c5c0030b00d00380c2e6900b0f101c0c110179580c4800c00011203824508514101501078030f01d11702040842c04002c5140000c11003082c0340074496040040c1d4000c2d02e15040352002d801c0100141c00716085881100c240301400050070140002d50601c035812245513103500c0c4414959050661701c095000c03d11103d0340002020606000806440031021100403000e0f50003581e0005400c400080021000d14110300e04500ca0305504d040940ca95240e00308034402075106c00340c1a601041c41040c54801a0703205030303030302c046243c090b4009a1108070328035010700302c00c0b6030b50000028499214014040d50325001010003c60322036281c070382c109019489444000b0040303260b0301054014001214814a00e00000030454030341a590307107240a58505504a0032142d80c41e8080d414503008042c100c00d444a141110391516000c1d1003036603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 774830143 1250 774828893 774828913
    0x91406040308040e01171b0f0121020a140f04230d0f20090604020a052812050c120406020c011a0315060312031b040303030b04050109090c0314 63
    0x2e668000da440310520038850750050195901d4101e2511004401c03400030100041015940c058400315900031750302035001e015140c00980e00ca44c08501c07084651080d044600c03008440d008010b984581801700100d900c0d40b49448201d11003004440e440359500716424201810201101e5140070b01044d400c6100141224090080d0b42d003240308454984500300e8051088164034000102c01e46040c003011000381c0c03c28031400c40791606400c0f1a442801158010303600c508014080e00c0c20300038414112101014200401881d22000b02102051502c40c0c0340d00c242422900009016158221044d440c4008140001e0b08000c40c090455a0810702c11a03000d82030803d1300000d01d0031500b01c0b0551014042c0070420b03950407810180704100130311480401aa0807403501c18080381c1e80304030b1213001d56494200000010300b40c040742001101ca100205510716030795035803420700602502d10036054601c524503000000403007848a2081c00b80481e409940144180c7c95915840440340d0003201c80c0b003239401035100c11 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 774831393 1250 774830143 774830153
    0x212040e0417121806040c170312010f0e0108121905040e1302040506040908030c13050a03061401051f0c110d0b010305010c0509011e020a08040303080603010506040c0914060403 78
    0x3c0d1103507021a9001100ea85016900b0442c500d5504880c0d83c40c40c0c01500900c40410130300d1041c0c0e4190f9009158101e00049414200ca00c1c40c0f04160180180c914928000b203000100702d9140340c00c9030030035002520f45903202c1001940b202c0d441020a41c01c0503040011728211440c0c0300403e4091442c5041c00c50402da0b81d51200034400e401103540116a456078002001140f03041e02c10190003d0051702d04002400c130950740c280340d41c0300181a01e890700070003046400c03085125541c0b0f0400b0b00000340c103c6100c00c0e070340d24042c005840c0690b480700700c04805500220755030a0200c40d8500740724041c90072100b6060014010f50f1824400101998a0b0410707140d40034050b00c407c051001c1c203910501c10034040350b145080490860f00101d0b541c0f0104442003041400603a408141c1290030708070011004e402602d511010707882c00e82500801400050041000014180c20098852182d10b0580007407015580d100100021580d1150146000ca82aa01c0600001040c0710304441006009000c662420f42c990301c279 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 774832643 1250 774831393 774831397
    0xb0315071b1712190c02030a0806150f070c060c02010507080315032e06050f060a03060e0c0309061605030c0c0118050102041a0c100f2a0e010212040e0417 68
    0x2426a0019250060211000750452203081381044040100075400020200a45a00c142e9594074100940c000104240b40e40300600c440d4001c6003030460710fa4408a882c070000d0550032030f11080d120b603018208005185030044202c900142e1341691224174000d52039440c94240d400c003600410861609210703091035074500b04000d0348410710410b0030b20462551044045003d1b6880210483e403039080580c100090703101e04031a00d6000f44100c41e0303180c4801005008500034082544442d10701d90380c84003400304408480c0011030040c0200c005480070fa50300c08044601610201d895540091020000902140140b002504065004a0010400822608100c0c00301c8a00b2803013682d0503540024100f14030064050b100300c41c0141c4854060070034010f00c0019032504400c0c02001c1080d902c0e12840b42c0500a00c1c0c0c0500d0709109015031007214600350311500b010300c1a0048509010411444c1e0412203036000143c1c6c5010080849402880c0c9402e0110014051741d0141046078103e001c414100c10320680400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 774833893 1250 774832643 774832657
    0xc0a03030f0f0c021e16090e1234050604021002150c0d0506010c0f061a0402210a02270a030807030e0a170604030e01090909060b0315071b17 62
    0x8010310410b0103400341402d1001c06140010110343c44006c214100d04c0e41039450720100c51742e410300040e0359400c42034500e05244003400fa04102c00000039401c0c0a1900e020074100c41c1d50300420001c9180450b10b54461100d40340c4c1107010b8643e078040d8000500600e4052000c07208000300d8070582c1c039140380300d64194038103550580d036904003110040381c0c1001a0150b4801e40d64418800d01c2c0a860500d0340740c40314190652001000761416845201d48210b800c40c2655200d0a40400350045558243d03c89001001869003c402e5035034040c80c5020a007003070041e000743e646403c0020074100d001c5d600f109548010307000a40c2080d4208030784220000108074074070007501126009446e12a8200402010449940741c260000c400403084038180030a41c01d0b000a201d503010354113080c00c004086a08005942c50f08003517214544503801c01c01300c00c04101864108aa020b002a001ca8904001240142c1009041140c64000082244024082c40d025110512408501455400300000280d001b401000d41c0036007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 774835143 1250 774833893 774833897
    0x40f080a050c0d021c21050a0201050105010918050a0603060e030705070f230a0b220909021f030f050a050702060a1116020a0b0d0507090b0c0a03030f0f0c 68
    0x40030000d1010078040d5501845040720400304401440e030001d10030f013510511024041c2c1000141004114800c507040134110309400366455469500e4900510540c00728800c03500550a1000001c2c0c030b54010269001914041c1131320900100d4111130881c000c02e0001c124613071582d00d60100101181203442102180540380c0007550750f82180341007440c54024540e11000109075105420407251000c0c40c0c192440c1703006c05c034542c00f02c1c4070444002028031700d00760801000c02200040e41d08001001d012140c241d4a06c182e441d08005e980e07114490221500d0350302c0603401c820305071100e104503580c1c2c826601c0d030b4002d24100060f0040c03203540d21104450045541d03924003940c40080c000f905404101c401e40c0010000c005100b07160f030100b402e500c140500d0726824441d5100c500024219070354030009001800031201d0407a1030348410446100644000c1d9400c40c00b16040880c045000f4203540102d8241d009a10010311413902103075002c038000e0400660b006100c65407000d90f16080c14840c0241c0210740425 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 774836393 1250 774835143 774835153
    0x409060509010f0302030a080304062003070f0509151c0627052e0317041401110601122d02040506010e012a0506010b1801111908040f08 60
    0x40814050036500c10f80080c2c0400c1084042003006030b5000034001c01c000d40c00105161a611a844d0910181100324116481440b8035a00300f181c40c40400003552242002c2d54a140044080c1c3e03030103940a01c2061030310394100e40b290714444214491200117240420b000401c4030030b60081490361008442464010800c08402219516120440d0301c000c102c0005514408007c18100303105542c10106401c01d002901080800b070a504440041e0211001181c011606210015580c0d4160074243d00c54020003c0c10041840c1060b440d51080c85651380003880d5200820f4a80d0030600f1042d040c094915003182c4001c600100071030008100c2c0001c101d14107031000906480401ca1041106441c001089581040250000980640e1344214905015409000c0001002030042c0e00812040d808031405070803407040400025200c80030700001e0a03511621500a9400a1000011039000508050b1804503030f01100400301201070711615200d205208400003403034140e483c43d08141119142e80a00d103aa001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 774837643 1250 774836393 774836399
    0xf010e010c0806010c060f180f02041b0c080906040b120702060f090a0303020c0c0901120b0604150902091305010602010b040f0e0607050a020708121b06061c08040308040906 76
    0x24000d1000c44078031801d003000ea03494000e000800c99410400003411650315400301440d100910ba20000e8501003030700c0c5494414020f41050220001899800c13030040340b400541d1101840c4031820120314207034503513404e0001c02d4a62035440041e0407400c02141d000008210002d064000d5000900100500450303c444074a0b1103800a0304180c4001c01c2030701d520301a0781c20400003034004100c2200480d81421b00584414000561500d04001034017103c1d007041d0050008a07040c0c401c0907291015505c11076920a05a50f50018881590002038403660802d56012081c04854002d8018200d404c5014081c400c0700c5508800200596a0a92040001d40d54420400d40c45040a004600641810801c180b00d48041d0611480e03071044000e050104104001c03540d0b0012510a01c1028020700c0800120f03a1802c90031030b01d0704000e40c0008103d02800a04620f0321003203510100d4098481c020041410b025808248890410050705c1882102c400b032003000040700081c8054003500240620000008010741 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 774838893 1250 774837643 774837671
    0x412060b04050702120c030702090a05040c060c030c02010e0102031c020c01060b39070303090e06031c08060604170d030e0609070303031104050d060b03011b0903140c030f01 76
    0x35010960a000307505203400c0254150f00000c03040c850080080b0302d50b581d4940d0460a5045000f035030030080d8041020303401d101c40c6060079000240204e0141010350511a9207120946032500f2400c0c1c0180810a601101c0001d58060b00c240300031030701c06005507481c021603170944c0d50440480c5000841459804039402c40500c0302486044003516182a507103241149482d03041e05004c0c00c030044e071004101c2d50241000100070103041c0f0710b0548a1281124081c0d0344900e0080d04040c0319001d03010884c61980c001034000c0c0307000124002115160a18030b0390b1070264020403203241000404a94121104020020302440851550080006200c01501d080c14800c0c0c00102541c2050b00c461445a100c1402e00c94821000b003562000c40b0751500300040c8000c130016480c100d500680d484a54052400850f940502c16550000e1041c180102d00030080c204000d44d865044141104191000481c1e0030801c0c80040d4207590041241e00b2080c04035421851420b00180c6403402d1103c1c0946e059444d210300c506808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 774840143 1250 774838893 774838901
    0x90d060f1a27091603060509060604050c03190e0708070f0b07030206010e0426131505070f06020d0606020a14030a0e1c0203070b0403170301030803060904060b0303041206 75
    0x40d01c00c80d61021024504041d01c0918441e004450b0b075101002008610070f0304040001c0040b44104074080d550040c2d881c01c00e40300401e4112401c858031f00464001400c2031034170340310f010310a00f07419401d03604588a81c7c0400c0d442c2418441c4404509a5034140000041801c0107507100424031140240007140c10102d4040d0800038940c8611000c5600f449102c00190700415010306458004030880c00560f1103091804034a540303032200da24911a07401d800840810345500170310131000c0081144414668032403034030344c07072080c20021034000890070b101d01d400240490340420045801040003500f00140300076510220758444c1d00c8007000d41e001034078580411002003109400c08800001460501c1a5400040d003801c0010228910440e641c0400911260314903520100ca0f54026044810341c0303032158a1001c07a0b034072501055034480d03020f0001d09a40159401264141d82e8000015401c40d00e44406000c04a0702c054070440d0965114441102152000c0000d44002c2455140800750005103042c054115 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 774841393 1250 774840143 774840191
    0xf0405010908010c05040e150d060506030c100e13090602040e011a0403021c0213060609050315150d150c0c060e0f0c06030c0d060306020d1b0c020402090d060f 70
    0x82d904144682c2e04e441e03003003402c1e18201c0e40000f84c541c0d03840d03942d1131101c1c1d041c0400204503076000c4508070304002801625400036108040c02d400f100c41c010043c0003040f5400030002220000551008100c84d414204040c1d292050040000c000c201000540c2d5248243d03041500b00000c80c00400c2c0041007046801c1400319002041c01c0724541c60103045130007044440c01160210700400c07103141c0345501107499081107074608401d2220100801600c0d003c000385107000301d20469201e031040c14403185441020701d100b180a446504c042e404c0c1d44420805120744001c0c4458191190292114005900c2000d80580c0900003050b5075458201d03044ca03d02102114130343c4030b141c0000c0d402140c1c20340582c08000703521070342c010381103e4040c0c4070b41c5e07a48040c030103901c0380340846070005007001800000c1140329000740029820020092111001030105019240050b000090004550854510250909078010200041c0203011458060121345941e420f03182241f0038541c2050b540c0215003c860713805460700080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 774842643 1250 774841393 774841409
    0x16030207202e051602040203130c0b0a0e120a080a020105010e0c0405010c062c030c0609060c0403030e0307150e1e0d151413120507080f09150f04050109 67
    0x401592121404942d0000b038907009000300081c44e106500786841d4011402540100305641c0ea2810f00c000840d07c40825904490381c0c11800e10204210300e80c0c0094031410003031a81d60310030300405801040340c0b488071809a01098001c40031810049843ea03002130619100940000c00d6a500d40b0300b0060503001c0042128540240521042c441a03034010030845120380c0000e004105040b00c0c14441901114660982412049a03071035140c03c0003010010f07008884050301581c0340d0b55583e18071a5140e6030100d03040c1e00c504004000600010f800740d64408500c24015040364a0291202d0030421b80c0c0a0360341303100001ca00062141001e0b860140d43d80c4c0c0c12036011030340c42141c100e4008081840340580c08401014002c0350000c409502c00b06500c02410032345c000f400c0c2c0300c0600f031401e1020340403c0030201c10384203000c0c02c0c41c4481c3e0150183c000c6a000e2a0701c03210b110303c0c1c03503120b0140499a030411a512a800034943c5145024411510050b0440380390310360901e40e03541d16000000d040e1400c0e0342c1c40656 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 774843893 1250 774842643 774842689
    0xd12240312110a08040302060306120303070c050c09011202220203010f091506080106140d111207030b0a05060d1515110c0603011208190e01030c0e091603020720 71
    0x40013520380c40640702180d5040d2440e60b00da4a5500c00109910070f10202c0003007610000c01007000840e40491611225405001a10041e03100203090001820742400340e2040318880302400b40c01400c0403141d40030850328240e4940e2200440881c5003080c0e0740b00f80d1044807800d10806042c4004015032007110f400701d044400598185140130000741c4180814800c802c1800011981410081c209001302c81c15403451300001c03c884124082071340919004005080c0e0714001d40000070b034005009118000760417400400c0443c0f1036281408020300b6a1140d51458201071b1160f11318403c00303c0d01851000175001116464408042c1e00700010400d10324101503443c0c541c00906804000d4071107400312410b45448a0010b0500601410100c10903ca070250208400d00a42803c551079984480064520107003640c007031002690303025040790340d00c0003035030310350307403060070040171500504441043c60701490560502604205190300c03804000310310500015001060404403074594903000580722a80982e82240103 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 774845143 1250 774843893 774843913
    0x150603150109150306020313060608120d0b0a17060421140a02031603030e101407200f0601031704030c03060b010c140c040e0d1224031211 61
    0x4054480184242c8080c5983d0b2500f81d2405007414030343e880030b5078108005555038180728121142090741084140c0d0306074030b00800424880b8000c2600344c6068229000c0c60308180d005220350008044040c40e165000c4c2074074000149030190000000c40048403900606940d2070a0300b00341c3c2c008041c024803504404000c0200e407414030380040d08450f00c48804192542c50307000302802a45584103c1c1109011640c40e1031801c402c1551503044041e080103050162242d80e0744000340c100946001007130620030345a807080050b03102403003500e400f4290b40e4203d003980c0501c901e242e03002c0d041c12241c06110a03190042e10040c824000c29001c511803141a001d00146050300d981c45222000b02c0c640001015a5114003d422207607102d940540c03412134000b402071405400c02512107a44510382d0bd10140111708013007841403a20400319200d08107080c02e40f43c0070704400142000100a140c00405881c00102d4040000c1c641c4142a0b8004082d41c4100104940054900e5000e090380c2a9081803c1c180c1d80314100b14 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 774846393 1250 774845143 774845173
    0x41208010614030903040b031303021b0d0f060b28050f01090302060f0c01110d0e2b11060708060a14030a03080c0c0133050a0b030601021e150603 64
    0x31142c40c41c00448590b100d0b2111825181076200b16401400311041c040240a0300b10402c11680c482148241c085440304d440c5408185044100c41c0001940201c0381c29014001c01c02403050120308070310505d40040c514408200081080e14580c2c0400d109880c0070361103543c41d594140224001c1d140c104c0d00c4014002400000800c1c0c0c1d03065010083c0070b400c021401200c100c6075041901e410705821002440540601c402d8070a207a04005a14140d941c00c01d80c4e6220041c5c40490114003040d114a5103992103010403448d0107010414800c43d10800c000c50031a554070303001c1448070324010940e5a4032010b66062407000c210803100c00f0382140000e0482a032008500c0e9900041e00348295a050529510680d611010020725000f204030403050b035402e03d103031000070304161010606840420481120001d8000b94181854211801055040001c034403081c0600d40741c0b040a154000014070495a00810164064508403980001c46606a201200444e10340800d1084651f002a09038000c0821041801741 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 774847643 1250 774846393 774846407
    0x1110a0b420303042102010815030d110a050a0818010215041e0203030a12180f0b0603070b0f0904061d07080619081005070c03051e070605010605030412080106 70
    0xa0708120030703104400c00601e5141401a40c0c01821040c038182c281c89608814640920001c12040b40020741040004608840c0d071072030211030610180c000c0540007a01d01c02035462800140701c010140c030880c40c4100004a040016417000f5104203a15522080c0d2884607500740105001a20b0554101204806040200000442e44983c00c0340c824200800d050003000c10260080d1806500750100144030345541d50840200350044590620401c01e01c203500301003400d04080c3c640011b00070075008011001040e01e504e0f10a4001c4802401c0d5000315035100c14013103c660010000b034500383ca0200e0710000c14542881000b004180703021800074212031250a01d0005400100580c040c4443c0d240440c880e5214400d4200c0c040380081d2003a861035458500b920780d5410102c070140212401c3c203000500c4c2602c11101a4200c070b0349500d4090410303c1c0c6084c0841c4c51480900340c0801881c00b4404503000c90040d0042a008240710341b0790680c0c0741094100072250310074440303081040c413025400401c6a1640070031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 774848893 1250 774847643 774847741
    0xa090c080f060d0b01060314060306060d06020c0304090203070f0207050405060d0204050714031905100e041203090c03060603031209110409020102010b0406060206070906080c0f070201110a0b 84
    0x101d000340a68407140000d0a801428001070300703c0d04024000300e20f00c1d8141d40864494100f80b181d0884654420040541e07610f800c440d40c03a04100c2007001607002039002d070042d04d80072080009076820247c80e1085242280c10403900344002a0030140c184402c039030140040000b5002c191400e000c1d502d462400f05149041040009000d036a55600048a2503c80d0101d680d8052015000580c0c0b41008040c08901c543c0000c65000c02603d0100440c8607015103040800c1210030820f14106513982c3c50320784020341d0121004140c14161154a1080041e0220350210095840382c60300046050560400901e0401c0c0c0710500d8000c00d1620300a82d0101e005061031881c4984111000b180c13000706440100d0162282c0c3c45810381040c241200400c0003a00130800754460b1000307a440681c200c0e40e842c4104c401400503079450550520410521580a03840070050016600604094038607280054210345460024241910b00000038814440500d10112070f4180f52401451006071100e8200d00090600d28100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 774850143 1250 774848893 774848911
    0x604150c081302121e12041a0a09080a080711010521061c050a0b070c080415260714040503030301150903050f033402010f0504081002090a090c08 64
    0x41c0400b0031590380e1403013040b40064003415624820f20b0884000030602001d132824005000381140c0d581d00c001102d0581b01207501c18042820a012968001c0794164040d0210314100300124001103900141040304482c42d611a00700c02e036a40b141401c003440c1122040303100394108441041916070860a450b840f6000303515010b04107605803186000208000c0807002020843c41c806600e81050107404184018224000d200d05540350341c84a100301d038229800100202016014002880f076154841e0505900081504128080d000d0b50030bd80e040880402c0c00e80300c8000c0d504010408405d0f44158425050201690a20b080c01d04000010b500c84c00140200000c020829074040d01051291a07001c00941d001800e840c3c1c10191018507035103e0b4400c00c1002c1510003d5403680032444a03905240c040202c9801a514821807203500454810f1982a040310820a050001044100003070003e031031f00b041c1c2c00b0f000503030b10138442c0c05202110180f9070007440c00d0b82c9800c402081880d0000c4005038064041 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 774851393 1250 774850143 774850171
    0xf0b0d05090c040e070e070207050105341121030d02090d1205041e0302100f0e1908060606030c0909040615030b2406091c140604150c08 60
    0x74140c0c0300e15108201c0716441d4418102250704145403808030311501a510708041d825110796900300146d83e9450188607580c0020743c1048045405140c04001103084030445007001690090307036540c003407190b49d201002d07100c034543c0c05110640740c504403003950b05490200c0504612814243d610302e0320780c000c410706a1401900019040080d83c0c40782010305070380d0b91084682c850b402e203040c801001600240110118480c1c445580d0103011180d0403807034112540213000c41c804007603201080b6542180d400c5100184034884980c4501691030040c1d030820702d0b03c0300300303201c01035481d054030f07140792141c040c1115024100405c00d02039681c82c50011030754a0344040d99201059111464500010700703407200c00142100ca0301310040f0820101a416038025100707c02191006070034a441c29180200e81c0c81c00582c4107504200044075410501e00c0341010403403880c81c0790340c43c0c00c1940340c04450f1000d410450aa03034200310104000c0040314140010403001e442d82c20000804100c502402e103240240c00b50a0303201c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 774852643 1250 774851393 774851401
    0x80306011116030c0807080309100f03021209010506041a0303070308040f0606152726010501030503070317100605030a021c052203080129220f0b0d05 66
    0x8204050300e9441c68120802ca50b250341e03030030100b81488080c02408480e0042c840b0024010f400001030f42c00004c4028025180d40d480d8000903031f1505c00e241c1c1034105041e000d124030069a208004040d101e00c40c10800402d46103406002c01044030123241c0c40e04104080c00044010302d44001056900e4554541800341c0c0d603840d11b051070072903000200002400c2c1800e0500100f4124481c0f5003150200c586501c800784d810108124582c40c04844811601050140032010400c090990340d44c95101100c510b001d001040e890b618290a42d84245c00c2500c1c20362002030301804069101c03580e080c0418000f5521651030804194010304910035110707401c02c00c44080040740448240394111061503000301802001201040f80e000064802142c2e59001300941041d40c1d45a00783d954403000c611b0703070b043c0d603064070716030a100008920b49001c010b510745c0c0c0906a070742c07911540481002407030a204d40301041d566406061001c2d04103000150409010054007040c03c100c0054408292211544040b00208080e55 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 774853893 1250 774852643 774852677
    0x71e0f08010b1803030c01021905030705071104110a0503011509030c091e05010608040b0601030203070e130204030c0b1806070209060f0301090b0705040303230301031e050a15050a0908030601 84
    0x105284941d4117000004181c8a40901540244000010000c0103501a000b914054500e400b003100e103600854010405000000e4558419040d41100103100040c0d0816225141c1c01c40e410110f6030400ac200000018054111694018400d00707200d80750201c00d00703095035103081241e8824800c8985282d1521030740250500441c003590f00f020081c4404000c0c81da9105402011100e040d6410369050a41034041040c65100c0d000302ea220f081e02d62900c0c3d1500740400180201211142505d00c0e20a03401e01010001440344400c1c00000d0150190042c0c40344181c13201461500100d00080d40b041908000041c01a20f035100701c99804041191016441c3c050000401d015017100c60f03008260b00f01200c00c00c4000c0e50000082c2c8250b0b03002f80d8643c10250f103505140402d00a0152a8444540c1c0900040002641200b80d140c400038070920180e08081c460303030364549040130b501c4003103e9282100500ea80d00d80c00504c583d641c04104c0c14811320003060a512503601c0b070702c0081c01c1d0764108100090305268400d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 774855143 1250 774853893 774853927
    0x4060902060f03060907022802010207050a090b030f0c0906041802090106050a020d0203041202060c0709020408030315010315050603150303070b06030c1504050402031905071e0f08010b 81
    0x30340140005680d500107159010840d031084890910481089010528541c07000480340b44010300403402c0c12040b070492412920002060404038118440d0b2000072516444081c0707840000d102490021451000c03900405080245151246450380c2c000303424003a1035907424032500c0c1c11102c10780380043c0c1600d00e10a100001012107401a400000202c00000c502c0e03881401000c040724107500382c032012541131100b00d07103910481c4204810444030b490000007503c1c109000302401d5040b401260035a40d030f5003e0383d001742d030020391100c000c5410110412400003411250410380e11030920342004501440c9030b0760405c1c08554000c0e1405000007100042c510302c524100c0b4810301e90002c00b22038070742c4450710304460b4100088808600a004998803050981080c50b491800d6586880b030746420f203824001803000070b40004010b4520f10011403101d0f03140035058031801e405180e940e80c0d041222811014288104840044248200709072007418806207548012418103484445010603510404200440d03041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 774856393 1250 774855143 774855161
    0x6030c030f0c021f02090612060d0c1520030a0c020307050d0b0a0e030a050316180e100b030105030c010c060b0a170106060525060908040603060314060105060703080406 74
    0x156141c0140300b10074a800040030300c200341061009200f0010414081002e07401038078840e940050042c00540f400c51034603080281e00c0700380640301c520b02402031740720707a141008568020707640040031309a07001003554040340c41c0c203401c4807031903010078400781c03205506d40d80c2c0c850380320700c171003000701c610606011550107101d000004c0200410000c0301d00141e00781050b1040003038030005c60b120303e8800fa01c10445404016207541c0e4030503464542c25035940000d52114202920020410420140002480303d40d0a01307001d00540551b21804806262020414109583e40e070480d40c407041c014001000329540000c0c035007907100b80c04c1c64201968441860200701406501100d1588903015150104a40b280400900942d921010092010660b96030050310180300e080200c00311b0004600034054030b210041d43c4c04c10518895040007400c42e50325151103050303401540110300029110f50f400c00c01e200307080004404000e04100038016551400c07002518900c50382c6401000c0c001c00c10001014002554000542 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 774857643 1250 774856393 774856421
    0x70e0a05030d120612030807080a18120201050711060115030204081b031212182d10060b0a26150108010b07032007090e010203011a0c0706030c03 64
    0x2d8005449020300503100d04200c10001c1881d10000240515800708020038603505a02c0d074200c9500c030a842103443d0ba40c018901998103844030b80e150f00b0b1010040840008a005078025440c040b04c00c10004c0c25500b0203040c200800c508400300d007150500c0417a0550440b00c0741c8a881c10a00310511054000e40a1544214998001c614481081442d850303100b1304803003070440641e005141c01c154100154040e40c800d103001651404005449a00041c404041c48044c0300111501882141480200d00319000380305031501050b6820b048042c08104910001d07035030490003c1c0256404c14050310703a64060400c8000070042d0b6240b0381035203e41c2c03401401c0040d4602042e14000383c40d101540e0314000504c840d00600151540c000081c10034594825501c115a0503542d0802c0e41c080b0000502c00360b210001a400b0704d0250810000c0d44280ca17114548034004510005a11796142000c901f6104054040016104000304030440190f500858000162a1181400140c04811507000c0700280010102c2d141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 774858893 1250 774857643 774857653
    0x10e01020309300a030506061605101503030507021c0f0f1b050f013605090a02160822030b090d0908031602151617030f070e0a0503 58
    0x1d80944041120705110100000369001441c544800d80c292250f201d04030f03d0005002c1c0070385150144260806900510000c000074148000342490162008400e14111030036031000004820403130f0f00c4d0103021401c1c280d000b44181d103140b840d14007901c0c40c41010b000034411080b0840003000c1c1102c0560000040d6041042070a0808551505203440143c0945c2503a401a140b840300d18030b180c5400b50441a2000544402c0030901c10304015071300380024644503c50f60314040c41503401000400c0d041e89404e0001c150529270540b8203c140000700c0d1020389119a100d00410007015100000030703d040c0301c00e038041c0b001c3d641c0c0c01484500340c43e090b010204500c4210050705002061200c1d40188070f010f51070300c8044c0d65001076034941c20f030380620092061400c107400600140d1001200301550100c880d0000c0c2640344089146080c1c41101c0d40000815112003000c2400c81d0248404207409440d07000309001c019107181024110136119140081000040190a0803e5100e50f11031040034002000d000d03003120 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 774860143 1250 774858893 774858901
    0x4060e0409080c01021902010506030c010f0e031513020f0a0308030712020f0a26010e070522060908060903070209180f0604060c0f080615033c010e1e0702010e010203 73
    0x250b03001c000006c000560070706002c1050307450302042c440c010349816140c162501c0011030068411a03d0303082c810f64580076200184402c5061003445d82c0c410800b403e01208140034510412000100203018070303000300c1404000f80001442e01c0200c85d000f45d251700b480d0042c3d4804a00c03034070103440385440c46c1080310b0011686440080d0842c0e0902640100003c41d1034948030800341d0042c84520074404c910480340323041701082441d0f00400003412903c0c1d4154010103500c4556000001403980340c2c0c000700000d4444142000b0160f4184403050700024480b01451820b0003940004200b0003000d410346220112410f0070200f44d8100304980303285244030a06580440c07506c0d0402200038100aa21840800e6045046001c0d03148a1568644200b50041c110b0400745c1c00c0c0040801345420080170041481140c841000d002039424180c03e00c44001c54520002e05501e10005514115060780102031000c4000d0500c400c0d10821940c0d00c92450103504010403e41d1030300012405080ca8201e40c0280f544000180 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 774861393 1250 774860143 774860167
    0x8040b0c03030a0501090e1002090f04091218080a02010e0103090203010c0305090f0c030303041e0503031009060506040848030607020c060d050402220f050c04060e0409080c0102 78
    0x2e103206015520040003c0c0c2e0f44e41d0080750070b6545180e800320305504040070241ca1408264040c0030b05050107841d000b8180154004a822540b501d00262101c4d60003090141131103a00581032240400c041000c07401d10351502d9000c540e59010b1140c0281400f0301070010f4030302039210760b021083c003d0300240244060420450040c00a110503a6040c19034010901c2c8001c2c09a400545d2001d90600030300154590ba55035100e1000040581e00b00c0201c0040e40300c4980040380d030030005103004100518410f401940f4040180003114903da2082c1c0c05101c2c280010007031902c0c00720b50002074808a400382201a1901c4c0c02540c450001001030710082088689910401c00401d00c0300801c6a109a0460b4800d44480000381c0e0b03111400c00c04598001d800b0083e5640c07600b007c1e000315070458805010607400300400380b40030034003100001010700003903900c1c024052030241c00d0095603008050114054a010308201b0000c009055410103640505c2e15501030130200a005000c51300120090002191070750004546 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 774862643 1250 774861393 774861397
    0x5131b0c05151f08061e1e0414010e0a15020a09150306050405061806061c090602071b060f0e0316062114181c020d0f03050103080406030908040b0c03 66
    0x9a680c14200f00040030440d00c2d0f0000d841c600480307038104020740074504482801c1072040014101c0701c200600310b0582020f002d500c504640690301c1010380c1064803c0301841c02e400c659102c01c591110358800c10301c900215901820b80341d03900c541a01c4c0980d480742c002a040e5015a107d138001c40f0000440451110050b0b031650048042c0d403000c41d4180140e4881200b0800d0234520401000280b41807a03011030980e10f0064000d22942c4041001021400320040101041323a417040c2040d00d5450b000202d45040058044d491504410003ca001c407440341410001001441078104074824006601d079482c4096500300001090008800300c80360308291502401403990740c0d515907401490780c0650300c8082c2000240201207120b04d0504c1c0c01c040a665690100c3c00b825581d2804080074014200d40e5413002c55610004900c840c2c00c0d0300181326501e86200028150f1524041100806140c10018400170300c0c0c000c11101103401910380428001102c0c00c00402922072540300f00c01180c0d00141400340c0a00c0800 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 774863893 1250 774862643 774862681
    0x26060f030c1f11010501140d020a08030d0212060402030f0402120a15020406020129040b0103021b07050906041401090903270e01050f0612040809041505131b0c0515 72
    0x7881c81024085400484d00360f038000c0c0168152200c0d0824480c500d410568010701c0100d00050001f1101556100d49504541c440050764a440ba00080c3ca80c00103d94054959080f51080c0d404510314588000c410794000009000240709100d280150b010f10301003004140001c03a0000c0c80340041c140c14a03040d030001d40c0b05114283c059400e002d94240204004402c034000c42203c181c0141109801300c2c2004024004c200c8241d041c190f00744003440c0d464908401f121038240324403008007400c905000801100c080000c01a601c07807400c2405841000c180a09080c0c11a513140c1e2021a481000f4034040c0c46a003040c01200140b4903c2480314000003024a5076101180d00040c1c50040e03c1c1d88680130b2050a010300c0d901c846d005881000044140c1203c2548294424002c1405034281003c100004041d80c100c0320b4541e040015800c4144a10f107400c4106521065840404102e500c003202d5034191481c214070b0009060050303c1288409000040c030440f0f6010380c00950804080c5001509061680d290740c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 774865143 1250 774863893 774863897
    0xb0a020c03280308040c1802120a200f0903030c07170309062205032e02070b160309020607061e140604020c0a050102040807030326060f030c1f 63
    0x800e282d0444012401c0ca0350300d0122a4210600d5901c03207032029210341902802c110b401a0410f640064124806c9034401014070450703101695422001c2e0034103800c100d000c1d0265109601d0000071070b100c07503041000e4014451042c02c000382c0300c048407200851540584005907801d80000118140700244c0451742d071090b210f0300c94406c5102600c60213510ba0340d000381c0304410b42141b81000100c04c00305510b0200349060002c410640e007101e86400100f41000c01c0304420b100e0001498864448a00701c03509081c09840c419441141084a603841e08490b17580301501d2051860b42503001c965000380700ba0040400300d500900740302d50b620010b142440c0201480c00b10304404001c145403114203480d03507000b01c03c000c455026200b06039841d8603080000a50190700b040645109881103140010000c0c0050070040c40c50b0009440707400d05d941400303002480c503d8a0243d21010312442c82c4d02e601858000780d0f803c41020b0380d8201c0a4808040407078500350034840101c0d17000c03c030404450840d2141d10103544e1104019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 774866393 1250 774865143 774865153
    0x3020907050a020d120e0f06161b0b311e030c0215070609150c021219301d0c0d0602041d0114010905030c190b0a020c03 53
    0x100c0300c1192203000c0c0041c2c1d940181c11103030503450002e1151480e000b921048141c00664400c00c500c4252070003105811004e05034000350100300d1700741c5921814641c200050708084c414150007280516141041510042443d134440f004545200c104002c100d0311160403a003208440c0c055401c0c40340c100c0c070704d90508607404a00302c0f0140c0b40010104000307140d07a56154603441101d1140354200080c0d00c1038a620341c3c42d04135082c001b40011900318090384030b42a000e80601411a240f80c11307003d0139640e8009044066501c03441c2c450715518484402c43d051106510342c1d100205151070300407140504c501d210f2684030980e4440410398000035984001c50541642e0007040782440c6040e40c541c6040f14150801004e0b00414854000fa041c00c40c0d50000a909c00c2c6401842c0c03540314411520340601000d9528a40e41600c0014042480500d11890210000342410003015141400180c1d035541804496806880c0001d00418080403010350354000e0b0510740a401d0b21003151540082d550811441c94034481e00c07034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 774867643 1250 774866393 774866401
    0x10110d0c0b460e0c1e010201020f0a05030a0b190e0a110c070e010801020f0904020711030102030a021309060b190504031a0103032c190b070309030209 66
    0x31404031034540c0e8450741e524160b42c2c8003220400612405242c0340c4030541c48071000c20221051603818a04810100311038030203890803400304800c0301c4125000c11550751002c03403103900720790b0f8900000c58210100d5044440c040348820040740a40541222010350550225100840300c0d00940558429150003400b00000c101d503200b0402201c50812404620508035807050003078189180710325910184030000800c503100c5100c0c0c003004507404507509000c3d5400151050042201c5c0c0e03103d440c011302ca000c0c000e600304101084103914a22800c04160300c5130794001280010040308002c901505d040040c0219180c1ca4400c2d035060182d48411925040f111030700d0310110721007840c0d21500f810759010314200c0c0d0414010300300c01c501107040d0100b02c2d010f00c441070000200140e407041035000340580c000500380b095451803801410707909401e0110004640c021403d480712950100c2c0311080920110303150400c0310411101c0c0c000b004400c2d0440541014000f45a10601d6044084001200d10954050380f003651 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 774868893 1250 774867643 774867647
    0x31f0909050d1e031122030309080a02100f1e08060f0d050714060d020307030b09070309050a081309020c0303160504031e0804120b0702160b16080910110d 68
    0x1003d546a401c1000c0d400302920307500740719a100c0c00480c0016514945030022118502460310680030b070a4600c0007080200b88105644001c00c0001440340c20000c01130a6000c0c0d000418515001d088903040002d511042030340a40324511034200c100b03113400b5400729400814802403890a04452280c01903000c245034507442d09005803d04501034200001c0c4c4101400d0090f264483c0000c42226644030905010322005000b0510065000b04682d031800a10559070f003050141d00c54000f41100d052529046051004c2480412075081455014420580c2c80e401b0760441c2c0743c440000d4010881c03e40c80030801d0b40a450000000b140200480d003104103500070041e104813503511445c04000d20b41c40b021214070710311001c2a1040c04000d44030b18000760400361503007040d2080c81d01c610001d5600400180c14800200d40601c200320703850700c84141d40a00301c5d05050404005200c1c200281400d00900038648050241400540d44212001040d5011440e58850020001007a4104e0644640541003e15100038 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 774870143 1250 774868893 774868907
    0x6050706052211010f140f0f1c0c020c0f030307060e03270a0b03092a09040b04022803030806040e070e0108070e07090b09120d050d0e01020717031f0909050d 69
    0x200c001c0d4110f03454000400c0c40c5107d903422842e8902d00e21042030211044542c5081005950b058101c000014484c0b049000240b40100d101e40c0140102e80c04020185c0d161004400c69000b582c00c006c02154504100030a2480c600c05e11003900010003525012412291002c0040a0404070032501084c4207511200079004034801070312184001d6220311003c5102c0d000000442c0000e00b0060b0703680882d4400306012944040c8111030481d030078401d00c4204411403800035000e107008490fa40b034040700801c50810a0030380d982c0c5400060203202c0d40c500000c00715940e94005140040806065981c2d0701d599070400e0b10303104020f00030314000b4000d595000c140a00c14000c1180b0803462962001e109501d000d00e480d060f80c0c0025000c070b8010f84010040c00e090102040b54070795104040e0344460351454414804411260840803414450b40108007080114503d820703c0c50720314800c400b0459a80e00c410076181c8880b40b000d82c00c1c1c036800024080000b03d840c140d511042c0f0782400384003584c058148080b0301316154 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 774871393 1250 774870143 774870167
    0x60e06030712170a0f030c0e22060b0d06030b0702010e07050f010201020c0601080607090501031b08060a15021605030a1a100b0c010603170406050706052211010f 71
    0x56401070104100c8604001d40d42482240a540056035020a4541c500314075885520700c24045080c117505102010382c1742c403a001d040c40c2c861500c022144588000180203e0119403070340c1480542e4030880054500c1035201c0303001001350000d00e60303584502409002c058556844162011a2801d0000701d0036070040c0140c2c81c0c20703010f00000d80b04490a00040046545020a4460440d9030034450208103900070001207011301300d031000a210900c0d00e800000c001310700a1704064101400c00c40041008c2498185c0d0070400329060a0000140d0740d05404105001301d10b47c8429101d5224405000f03005030007250000c000c4112103a00400c45459006050303442c80c3c40e10700103201890300c0b840d5004030382d05111090782140b01c0803d0f120308075aa0707108000c400d400062040007280d40d9402c0801c1001051512004003110300c036131590174549042d002074080d0140040240c00300e601c480c005501c01603000c013a03104500510081e007904034000d04019601c915040d03503482c0816a6000b404801500400140c680 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 774872643 1250 774871393 774871399
    0x60b0a0e01060521040b0f1b1903110f0405090f06010c0b04020a17070e1005011b050114040602030603060912091c020603091b0607151806060b07030201060e06 70
    0x141d180650488266000c6a104500b200032001402c54045841013018000d502a03134034018542002000040c41d030001920f49265102414016802865820281e038079010502000c15070304400306509801424044200e418640350000e5100b19071444e42e4054000d0383d0081e50710708100d07510108450080380c000d9541d01e010502c000400000641040300e440d0740705101038500070080da40c428800d40c00d130400700071000180e0000e84c010b104c9841b0140045602c41e88100699024620b4080080c1044101a0100390b0b05490203041e00f06018003500460b8946846502000051601e801c00000941054074198801d00860b4003080340c1810000712103823001851a90b0618006040341004a51828401c1c42040c243e15224488056520400518814402c44002d0040c0003803264201813641e02105039a44604010300c828000b00300300d101c2c3c92600c1117a511001034042074180c0310090b42d0505010040889003818000b0801c26025000b80040c20700c40c4d0001d001c903d4a170351224046610407200990 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 774873893 1250 774872643 774872669
    0x90b040e0f10050907020703050c18011205150703061404050702100e0f0d0807260103021338030307020d021918020301030209070f020714030304170109060b0a 70
    0x1007900c0501154210600c0400203803082d079510049899a030080f10aa4050f0304081c7c13003001402000e21a201d510001201e505440c004051035a1041c00703410300500000c401c2c0c811003202001420040ca90000d100440d10748030750b140c4040000c0190105004407000ca00951000d2041824503001d146e00411058028007105c0007820090741c01024035090a0710a80305050002103080304c1400b041507603185030b81e5134030814039110b00c0c0981044d07902d1203000c8440381d00030041440c0000d9040d6003415a0b9040302c0e000c980c02445114800a800d1942804c0442200c000401c46000c00102216203002405007030340380303403801e0181055180c2c01840c038040e422094030014500185009840d4180390b5030f400180100642e16040c600c220002010303c50035545034000014025403070440600350340400030789003803900015040c0c0000c1d11190503100c0d4482c990200107148170300f980c0a10680b000b038003e5102c50000c0149009036140604042c03a01518024541451240c46083c078000d50b00c295510041d440e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774875143 1250 774873893 774873901
    0x14030403080a020f16080a17040510021b0f0d02010e011e111e04030b101230030501150c0201050a080c040905040b040614090a030e130207050d090b040e 67
    0x20301942c010002601c2130348040100202c02c5110312403031402640985e17a80394845944002c041c000c0c101d00c0710b5900c00c61040c1000c010008400250303d0b1203070020340e5400f50f00c4481d612031500a900050703008036054010042c6000710500b0014111041854a40c02481104882c40e503140c00c850040240c031030f800003404282503111106410000c60005903448203481c0008021043c040b078100c0d00c07060000e0041c0080c1c10030510082d6903071150004140398412030547d1414904206074001860010441400c0c5103510044222064603001c00304035088100c0000507030307003000400400d82405904c2e880342c040100504c83d1441403989020660b410384600345440e4040b181954054401480200c0a500030032002c103403500180626406988034250034a180d0409243c82011b4415218220a500042c5010400c0c2154006030801007160503041c9509041c01c0d050205004410400c001d24281d400018004204440021480d40c0840655602c1441e16145d0000c080244180e00c20240c0300c20f6803502203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 774876393 1250 774875143 774875161
    0x302160b06190b04080d1806032408250501050f25110f0d020f040b030f03030906100b070203060a05060301020c250b031608061801080d1403040308 65
    0x341c0c025030010802c0c282c01c0c8420001032068100740e004103294100205080080c1082000a034410803003504200b0503c00468240921a0000380b15600401d0746880200c1c1c00312000e0b20851200c5031313400b844d4500c03003601c0b02c403201c0d0340f400b0b507030710040d020049601d10005407800d05034144241c1c0c0301651a14030303001c100e03074502c0001c3e04821800c43c41c200318820100501c40e4580700c4c100da540d1140e5a04810b5080e90020451040902800103000740000b0302c00200507a40c4c908000c2858004130350005001854902080c03600601c40c0403c1c40300c0c4400401d10031203201c00545140b0442e151070b40380b407840343c540306118410f01501c000290036900c90804a101910306820071075114401a00040c10002040111450118801601c00720b10f10700ca1000c010b0f050707402900d00054899480c07090301d10309200c0361107070300c08000c49203040c104000e00c001710b68940c0d81c0200c04d9445020469070a4103650311240d4942e1255280d007030034404100e4040f20b1910307040300b05090b64800c03a0103071200303440342d9204944 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 774877643 1250 774876393 774876413
    0x1404110904021b0610060305010b0c0a140f06010f0e01050d1e0204091a09010b010201060303090b03060406050d111f0206040b04080c0307030e0319020d030c0303020f0f070210030216 80
    0x3c003e10500a80240400c500400c1184d148159000000c98100510341000074044903810381025100c2c20081000e20985103000519000d407a5110340310520318150010000e05108080182d0001405800000154403410020301c1c015100d40511408059a03200c0400c0000d801e8000010203000c004a803c0108c00c8003e0340302d0b4402c500140c03000c09d504030680d490845c20980340b02c1c41c044070b90307580f000d01c10f1519007440703100d040e80000c0c00200000c0e401e640b40601141164412041036840000006070652130780d8002000404000d085c0010345c041c0f40c50a02d40042c0040080c1d406030455902e80510003002d404400100d4050340c015040c0d40c1c03100e465825904000a206030b50800c030400a82c90034001c01c02c000c04209000e580d4000c5660219030030513081a032201c1a056031100f00150180140c1e552003030f000c47c03569250900e404209918a01600a40115050b10024100100e82003100c980304e0b900400b610b5100f02c1c2c0c11180c0040c44031094049006006030440c01a01d9810001c2c00590340000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 774878893 1250 774877643 774877657
    0x103110406030b07020a200d020d080906070305041502060103030509090702010608060c04090b0306041a07030908070b041b08030301051302090406060903051501210204020d050403050301140411090402 88
    0x44003207522510b984490054034403c1d9044401039000f00842400c0c000d506240d0711858101e418241c004400003000900140b100c08400782c8103100305070b810b03420810708000716059040302900650710b076440d5050191084d0440e200300c0308807915452124041034070100c0c1440c16070754551147c50914080c0d8090081443c00103000030b0956603500030228003203000b00040e41c170031003000b0401c076900c0b410310800e9000c3e82c01d401c1d031840c026408070043c000001d0642c44409168050305545240369034960703000720080d002101c00a007602c480002c0c036000f80f008001ca0b240c03169016504506180d803070001601d042035110300c52139145400500050003245060660018a24840b000160034803091600140803500f880d4020004076842c02410020000e05015130040d440080b00c2440007903242c01110b90407008504405d000c4002d0280c1c1c031101315031742c6030b05503040c8800c118001c02441c5054500580260b1080c000c409550305c3e032003020308440c130b050b000700c403010f0007903400c02d908004403041404041c0d04001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 774880143 1250 774878893 774878899
    0x3031d0a060f0e1306050307060519050a1803030201020d051f030602130b0f030f0c0f090f1309030e09061c0213090f03030207020910030b060904050f1f0e0c09010311 73
    0xd10703070100c0ca82da035a5210700c1c4e000300e443d000180380e1314060401d032404e5002ea0101081c88010700440c244038a51100040c0345401900b002a5522084a02201c00c0000310714040b045801860740071040c10782c15405440e2805c080d80c41000b20340c07180c2d410003125034030300141603007048a01c1d601880010140c0e000741100c2902c507070303084403910303140e5201c102503070007258800000407404010010035480e8a4030158020500b1100710b8a0181c1200d80800c052140058042c01900b400c1d204460345e840f171100c01010010300003010044445907250080c07900a0101d0b60901c5401782c000414030901d400d90b1007581018020b024400260300560a01c44548488099282300a640d1060f0030302150103900c1901c0801d11075500140d03070328007038410042c0d081c0700a8144003600c0d0f07214005200080e02c20110325007040045903001344590f201d28000e0301d85440c090900850340130310740c2d0040c50b0440070340010f089030148040901441e10001c648a80d248480304681c3e07844841c400040012541003101480f000c0005 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 774881393 1250 774880143 774880157
    0x1b09011110020a0e04050f040c0e041e050c0108060102190b0619030b0129181207140a05060a1e09051f0e091b1c090b0103031d0a060f 59
    0x41c0382003040360041085040852415010b040c86403809100f8594040750741c020b801154106503d03400c0c0324040c2401040802c01c90702d000300d8140705050009030141145d044008060790003c4c50180e8407a19140701c0180810f1560700812000d41c0080780b81c0480404111010ba443c0e20103841d650500000500415080480c0c110f0300b062100041584102440c092440c2580c1940b6004003c081c3c00600041c40d1202c01ba0000c95541842600c802c03035032681049415203203e0100040001d00103074040310014201c0c480c400740001c0208400300f0321304d4490301c129140c41115903903c0911109104906907000014200d203505c441c0d204c201d5180c3c2c43d83e40601c0c5030400c02e841c0c13900e0102d8400594824101c1120329100d400200055100182d4442c140c805d4071211028140f540309c44d1100c1e103c180e44680319600c041111500d81000390000b05040441c03010600a003462410311901d280b0f07007800140c0025841c14403010080e4215060741d034400c1c0020b8068581c692600b442194001d0070061840200540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 774882643 1250 774881393 774881413
    0x40b0f1002070e130f080d14040b160216050405190203070306140102030c07060807030f11040614160813031406010603151223060a02030f1b090111 65
    0xc0ca500c10300d408041a00240302030b60030441c404660840080003041088141022a00011000094154a65808804103444007104a00d441c081d01170812013507001d061140800042c0800480c0b0b8a00900703550300e00c1503461500c210100d0f01e4901241001c0c3c4d03ca89100c0040000e402c19502ca250702c01e15401c1c00c1c0441c000b420540030160384c82621410006900d5410500002117030360081410464240000c5141c290810f04240d200c42052040c0340034084500d0000e140c0d240650440302d400240c0d41020400001201c450090b150000c1c002c220004518203982c030a454502c0048071002614202500391001c090790390704020754405500c51241080f100d200000141a40103401e0320401c00700c0140480798100407009080b2018400ced6101080381c00082000100c0300011030703401d200d4001480c8001c41001d448902e01030103980581521500c40e0b1350410174140c05d1980654040c030320310b868050a6403551251f4201c2e1012400301c0c00f28096080140c40800e40c068480e9114200000c0145c0310300d60f007 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 774883893 1250 774882643 774882649
    0x906070b0408070c141f0e0a08061e040b040b060d060603031d0a0b0a03050a180c0f050f010504050120061e0f220809100c020f041a040b0f 61
    0x400e5070304442548011401a041040303484060010340032502c03020240406000c0000d20f81e503891500c001c1c0da2100020b800c19014410381407201c00e6074000d45501c8640345d5800115969500071581d9000c41120740d40c01d145611158500329000b260401c010362060b407516140c00d10f0103072001d0f141503807000006401d80c002400d20300807840110b0098850020212115101c2d4280c0b00314100107500c1141040000d1219211080c280c604802880c50009010369648030880c0040c04021199007a690f5038640f107400b00052000740300190348102603c04045075403001804110140040f80502080007031009010551103511040080302e4000b840682d5001700060a60231700c01e007500d64542c1d00304080e8000208060303508510381c103d903071403051000c149441c00c2d010440e45000c41d01d40d0810601c0f0b500035400d0101100c291602c411009106040d240800480500b841d28008000ca0040400510420b0145860700c62a4811503049c4103618040c00c420080000a1012200455010340e400500c3d5601751 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 774885143 1250 774883893 774883913
    0x100515090a0b210f2a0d060807090e0a0f03051306021e16030f021206070207090e0c0d0201260a020d180c032009040f02011e080c090607 60
    0x4828400400d944841e00203c0c00385401010034102d42011000c0d050004c0403500c412070b41d0b4001940c00d454400c1c210403602e02928904105900c00031200085008403c0d02c4455100104070b0300207004440500b6521000750381a030783c1009020b00c04d031300645007080210340b540c08014203c620a2a00d070f403405e1040820310402c17082c00d030803200040c0e00c20000e40081d9102850284051000c0b44010082c810800030703c184590891b010080a065174005d07810115207601401c0300d01919650140da01078904413000031350300c004c644543c3c00c50b00d0800100d41d50300b44022414101c0b001c409000000c076a0000e4005613060840c1203100e1540039910111154030041c0c04030814012010b2000c0940d541580070106800c0d21480110041048003c55181e40007580412200e01141d40c4a01c51071030101c518402000300c1c1041c0642c4582241680c1e040008100340c01c245551040e200341c8030001c0106402c500307000fa0f11400180c0d00003091003100130544140b0805d01030180351174018800c0380b0301111950b4041c141 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 774886393 1250 774885143 774885149
    0x18191b0b0a02070f050103021602060f0f0d1b0c0506070c03020c131d1203010e0c070605010e07090f050a0b28080405010606030c0509040f060314070f0806100515090a 73
    0x40e04a4141030004e03000d440c0403c4001c082c2481c040d42000a000111400f00c40c155100034410b800000d500304c0c80d14408401e590141d070141d8410394403222600c3c00380010744180000004000303007002114040034020b41101a801d80c1007001452243c0c0c410200742d03a41e6a051a0940551051040e064020340e0f801c110451040d802401c04680c880240400c42e01450b0101d5250444d43c009100c00346550b0a1242035a04584410364541c0950f180c000040100784194080a4400c5040400100d14241e1080249015440710f5481d61001991242c07084402042801540c0c1d00648034581040b06c0b11150303014050054081c4810300004001486008000c0c280c1288080440d60b61410803080c4003080c81124002e03c15410309200c04d112000c0c00500350b01c80c810105229540d25440362201c1c0b00c5d60303800240a107510000601d81311510412540e41c406907441112100d400a0748041500d09022440d5401201c07900d82c0c1b40300b00e5081800700800000c4c1c0c0813401521045c207000141190303540003140401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 774887643 1250 774886393 774886397
    0x1407051603090509071124280501090903110c010e010e033c0114040305031f06050306120c060703300c1b1a060a0b1218191b0b0a 57
    0x40710b06c00c103009051109803008034000da83d41644440700480120800b0b9800f043c3d40404541d080e03c40e041286071072070803100701c00c3c2d20f900c1c020001c81c02c2070881c1e200b980018000d4544203800c0d104080842c0e60390310703038809160000f0b0303807062a00c01550091002c030a560f00f0007000d0740c1f99403d180d80800c8003500001070081040c14582c1c001c07030448140b032103d100004042e60081c042008030421448100340c0140c0000c080110004c00140800c0c1004102d58020922040b09090565600c00042281e0015035055105400d00074561135010300015000c0032026010b0007090400721b0a032002c0c0c0702441009c89156140b881ca4812440303001449186224450040c480020580211000200303070b0f581651203181004d242c4940341d00442e50203180402c898110900300c070107aa5032030001c10030b880703c4c0c0d03031041400c142c01144486c2c0401c0c58031134840c40b4800829516444a0356203080d00c4c0c0d0368050340701c0c28284041a071101008101000c00302112b00c01d40d084000180c0f03540303c119401503441400b80d000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 774888893 1250 774887643 774887657
    0x1005010e0c030103031d0a08030a090e0109060e0414030903060f0f070e300109030917010b01080406020c011e0903030b060f09060d0603020a1206140705160309050907 73
    0x4051500403465080754441c50402c0c115811545c01070603030303459a56580030b11030040b88180b0f01c5940d000c0e030030b9010b0f1180c0c90580740c40304000d04020740200e00c40d0103140b01c107100400001c105483c2c1446180c00f01d4020701c04200d6140ca440d02c0300348459402001e040064041000225141d84040bc255805514030007503e01983ca0002e122040b80c54001d0808010000d80c0b0840182587c2c03096036427120f07030f00c6065401c1c064a024941546100601c40004602c5508100c1d04400345a00100f41804494406035203072075200301c1d40c09803422a0112400c050220756040c2c04580032a14560280c0216a00c050000030700c0c10160b0070a0419440200c00883d040d51918400010190b00d401000302122080c0c40583c180707155443e84001d44d00506401d40d002d14404190b4040750b0080343c0240000f0354001d0400020561141f515141c1c2030850301e810f0b1036440c240500c600041000c20b8071640304907100c2d5038603410121700071030942c840181400b0036000c012440c10007040541c2c40121481c0100c041d034407000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 774890143 1250 774888893 774888899
    0x3050310030f0b040b10030c2112050403051209150f070501060905060102100c0f0f0201060e0408120f0f0613020c0f0303010f0503161a040801020a0905130e0a030e0111100501 77
    0x1c00148008183c0401c46c04842c904000154044022005503000000e0b8010142414010900e4800c005000509410022900188c90035005002801600d001f0000e8079904103681c041c54401d8444c60464a8201504c05168003050040c60042c01074010503880c030f2464082603813501401d60fa0140c01c01182c0325500d10602c0400d41e010842490004184030042c0f00122004002401a8003040703c0901444030000000c51100e00c02c0d0f1200d4042d201d4002000d1007820b0900b0105040c0c1c100606c03276422185c03480041007003010080300061044440034591101750362000c0520900032118440486555004e005014064201b40100c1c6060301450f0011a01c80d8035000700007107961059403045010382c10004452020001c2900d14600b690088080100151100d80302d0b8401c1c0d1040782c0c44180b40394808562440315982c0010003108a90080380c0d9070312a48881e40c801d004075614070380c1000e181d0380255054400a40134607203c1040030414184500620a1105070314249840f8079103480541f40e5400042c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 774891393 1250 774890143 774890153
    0x1203030411090a0515090601110106121a0108060105040c0512040b06131e0c0c080c010203040b060a080309041e0609020c10112712100b0102030c030703050310030f0b04 74
    0x610f51042c181d58041c05213003004480d4021201c215000903004905813000135105034061110880d0022410000f044010740e80c8010303244058401d2412918508034054124100c9005075002c0e059840b04805400035903e080104001082c0e084000c0d401d003d02444000e5074a40c103000b00500c0365001d25240350b11440c003103082244841c942101000781c0c41c40c5c44445009602201c082494101d0f041e500018040403645040da0703540c7e64403e004102010000d5401806481900a54020780c481c503009491a1520420409003550300c1c0595022503006001051207480d2940140508000e0380890312445045168400140c59040c2c001c94100358001034285620316080003641d0002c40521401c00070f004940400415030312070300c2c0b021071b1402e100780c4149103444041400b1004100004207030350040042030740701a0300c0f800c10300e4100d0b050502d044050038441d400071080712160300402c0007551a0a00036a400d50740e907040500111004014207030301000041c00340c0c0c4000d03183c5010380d4010490740303041d10301 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 774892643 1250 774891393 774891409
    0xa021b040e0a06090203010b040203090313060206071b060b0306010f1e0308090d2a080105090a170c01020702041a0907050f0403080703030213061e17151203030411 72
    0x8180158900241d5034000314000c10103204040e4041d00c003140220139800000d01401d9058102c40d44144008144030b14100c00000814080b02d00b0752592445903660030060b078490701e0448500c1c0c0492081040d141c403440d9980b00b00749006100301400144051400040303448c0003400d07003100000021000080c091400c1da403d26480c101880b0300020000d80c115518858940a400c1e2198040c5121380324180800040304c844429070036016201400ca515103496100010341c4610401e2069403030040411110800030558010094200d50b082c0c9180c8044039001c1002c1d8080c11001320700d55424011900165207038041c54403107070800801404510394103000c101d0f000c40064805824000704002b103200c0c0862840698040b241c0146c2e226484900f1410190f02a2040d000d0540c140e00c0019004a01c0c541c10900304603c1038040c808040d42840c04ea20b060740d042d0010544d0308982c0c207980000640d104c0f034040d1a03c0c000072020748004000341d40500814511b8205603000c95403080840004a10340c200705032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 774893893 1250 774892643 774892693
    0xf0206161202251203030e070803120117060f0411030c12010f061e0b0904020d050916090c021510150503070210060608040620131a032502120a02 64
    0x55140744040c41c0600024400710549001020b150300c6003101124101f05103c01c80041c2003007400d40380e545981005203060000309000d45044020f11240f501c448440000d07641e403080710071075040141900c45840c0c00c011a800745444c1c513030600c500145070340745072541040700d900c0201d10000468450400e81904013500c0d55a040806180c04440706800d000b124958130404a41c0e8840c0e280c0e55a240c004085006403188144d80f000a904040034000441c800240c0100201440c0c00808900342c2c035040105c05440b61601c074100141e12088036800a4803007090337070750b030015040d10018920940e00c1707031f03051139002c0c0780e00322500400c001004018069405100c00c17003a400300c41324100051030901c0c0b40030340110000703000588034559807901d1501402425003100b5942556a0105842c0c9191906401103002d0701c1c010b0b032801062211116101c401000140c901a500c5040c1da04510f048942000318a1124080403408501c5292203c19601c10710500078504a84a50301070300e03988800700c518005490b2100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 774895143 1250 774893893 774893953
    0x60314071a0a2f0a0b15040e120f0f0403080c010b01050301050a030605060a080d09140306071202030a0f020c03210c0f220e06120f0304090213050316030b0a0203040f0206161202 78
    0x1420381a02070b400868500c01380c580160480390ac1d06506082540d00d0b000c2c009201c000e20500180100602080e2406130111b00c01d860028069401c0e80d10044074540028441d00c0e40140c0c0140c4c00b070002030856040564400005042c031040da55071190210301d071040c075803070400c04511901010b2000e0b05c21119400301020b401d600412250409400c01400c1000007000710a1155002c8045464501640c10543c1d26080080c41552202a9503080d80d481e0b0f4021104c05d80d5124031040c1054040121600d10740c45152450951800c1194541c1c81102c01e40c0500741034221051f210300d002c01310030407176864800a45a82d10900e10240b50500901c1069000e40034010384aa2000b200440315520000032941900c8202501603280c60b10040c100c0781c001c4254120aa05010301001d00c1c2e0310620140f11201200e010b6801201180c40e0a10384000b24481954040d081d221410407400240c20702c02e0007005a00e240014042101189032039005035005001d10810060f0000d00c0440c00285e2401c029008154441c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 774896393 1250 774895143 774895151
    0xd1b0203120c07060902121e0c0f04020304030521150d150c0509030609060f011d0609070c0501150608070504080718060314071a0a2f0a0b1504 63
    0x45034101d4141d08010528031016030300003008000c00a064010002d0260b01818030344070000901c0e24a5180c03036649801c030b5814510407052030014240020b05e030100c3c501c0034010201d1400107409100280d44000d00503000c0c040708003d0030082c0004544490b4501c503480100102a04000340701c2000180b00c4a02248030300d44141c003400110303d425451803419445d0040c000750301a0000c0040d96207006075540c1d664140075500401003241c2012032194030420304515800510703a200c0005120240f44028140040d448d403c0025189040105080780c020403241012660110a40c0c2c0b001d094400ca00003909051296840800c015900b00e02c00740e4001042d410900d003800e0424980b255200b001d4401d11030801d00c1e40300f60b20030802c01507001c5005103800c80b84161031100c510354a11f17540c80341403050310f900512551325084200905011780d0205510b541e100e0144401840070414018500f0709540152400b4690030800c0b00c0d410410140d10521682044c3e500d07181441708024a811044166400340d810 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 774897643 1250 774896393 774896407
    0x9111c0203120f16050712140d0f051213210207060e030c040b12030a11070914181c0e040f02190c05190f021e0f060901030e030d1b0203 60
    0x40b0005403205015942c019004e14a02c60901503d41016a4043e810140e416694075051003003452991400d01c2c20103080b40e0300303107072800f10880e03903201d00958650000c5c1e8207100321500b100500500303540206502c1402c465903074850b268104c42c8400784c84001400f5009109038082143c050100400034586030406c05134540c0400003180e2030304d200401d0180700e80da40e1070b90039000780d8a441c01152040f032008110390311030340024000340c07402d48080061707012403285c154001600c211902400a104d0005081646182c8401d8203205200b054440001907a004490f80d803c02e1030118a00034064800b95951404000c03c01d0381030204680000012141d07160040149400840a0800d0211013110518100000642d00c2c1030003070a001c441c402c4481205117942214003400b034410221a041c0b07008a52030802140d01c04159046201001640c1e500b00c41c0c5046c1d50800ea00e0818050aa100750604001c075021030803402950030742e4441440c1c4150715590f02c02c0d051903010400340c6c1d0b1640c449640021480c044d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 774898893 1250 774897643 774897667
    0xf14100e37050102120a1401090b030318032104060e0307150f1e0c110102031602090601031e20040b030105040207080c01090b0405011b1209111c020312 67
    0xc000714610904114031007030507042160035411140d040340c0b042d07480e12090070441039034000f46c0410031070080d221020310004219841d2038400c26040b0000240194070740030050019603c10f00c1c1e0000032507454000d004000460890800c0511001c00e5454400d0740d51768103066020304005e604000d014020340c0440820300c503031a601ea49000282c8254100040781144c1e000d400c5403000000d03220b50300c1c001c8045182d0072003142c0000d40a060540700303c4202060000b403600499036401001d0004660715101c054500c0942080c0d03d01035001001131402158005917902841e07034010020540004c203683d83c092010313000304a05944032038400d2280c071071454585402c0104540e40010301900c0c0c2704a50000d0070500304080c20007101d15102c0c20100074000504c1c00d06180318910340403981500c3e55400c0c524012500105450140400070850311858003160400811130028452000c00700d80415511400d0700359a80c4600300001108410543c05100d262980705050500d02c1038142c030222040103105e9203800c19 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774900143 1250 774898893 774898963
    0x616050c060415090206120403031d060f1819020a08070e2202041407090b030c0403030509040b0a0b07060c02030406050405040b010e15040f0b0403020306040f14100e 73
    0x50f4220110001c42038004000400a0031510002580300100043e0444903210b00e1185d14861f074021388003000f2504d00c001054502c8000c80700705005c190486c50028807441c200034074054100d00480b01920b400c1001c0c0201c10700c1d0002d1000ca000c2030280340301140c400c40c40d0000346080540038075000344c00241d140c0710f409034203150081c0c941802851010546d1908039164400c1c1100c20b0380050043c000c131000c9049a070880f01095501c880054007101022608108001c22207000340d1542c400c5514152450300d08460a810508a070303039000e515151419801e55410541101800055843c0d5684000610341a0120f865017100700f0155042400104121038129003a1401c895080e600440d401c40032100403111450300560312a440045040d020b50f10314040f102910036282c2000d1060324054440420940741e005a01c002903060707102a0000380050068003a07101d0700c80c400d91650f84106140b10720581085480240140ca913582c0b400400342c880410007200301c800141d80101d11030f8040c0c00b18811656 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774901393 1250 774900143 774900151
    0x7031e1716021005070605070f1e05032e06020c0306100501090612020d0f0515090609150307030605010306020702130507090501260c130602191209090e0616050c06 72
    0x2072440f100b5951100d40900c0c00ca0f0102944090204507500e0150005009400c20968400005401c00300058002400000d100d0200100f034881c1800c40da030b0418072002c03210842259000b08200c04100d00c00e050189014034000d00000c4d0003801d6244203002c103252402200a002c1116a030200c8010800799810403007507170954000d03160000003c0d00300700c40340e800392040711142c002c40c1c0d01e0310021141171107407a80454000c00c03004c2c280114560b0b042c81006410302d0103a46181d4400c0e50607001c2941400341120103c2ca003030001d0191a400ea9903602c8210403201c090b8400d582e030382c0d0001004800c518216003420480314010508020341c0c01c0400004100345101e0044a060140d41542d61010341a1181c1c41103400014124129907841c24220004040d000b101c0d42d4880800c11810104040d400442c10005c42700100861243d140b8030354450140700444280580180000301e40c2c042000b08041c0180741c0d4090f0380c1e500418050900540c5131244044c008010002c000c8280901032542002240b040c1d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774902643 1250 774901393 774901399
    0x50a0227030c09160815060d0903140f031f0b0a0801030c0e0717060a0f06121a13020906040b07030c0c171218060c0a03030f02091c030207031e171602 66
    0x701c4d0f0f82c2c1c46c50100102e8142031100d070710100100f030000490083d504400c0410348079980d207003202444031600e18030601800d60b00100d40e46081c400038203406aa0901813005d0000341005840140c0e0f206140301e182d40c07024000800080148006206007c00c004030f40c802426107220022042c0fa007a50b0040058001d00c007010003848008c80400c52640d510581d40003d02080c050780150075a079480040c00741c0c482c0103440c0d60040d08184949459404c44250641e0451003c5d0881000c0401c40200c00700130350015660b141e01540901000c14a40360315409800d180f0312070788414444181c0c07810503003c030481c650b00400d00501031800c2000901000b00d01401c50b500034504c0c0d65216000c0701100601a209038181c503811001c00b00d4a146a00d80028400598900944040002054100c0e4000503841152070300c68000140d0140354060700d203c0d0b07840341141806441a100125129a5041c07002918070a008010340324071180c0500b40504201c0480c2c0c085007412006141402503500f031004c0528a50000e44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774903893 1250 774902643 774902657
    0x15061706010e040e1015050a18140c0c100603080d1104051e0108070306031109180a12030b01021f0230040b060121050a0227030c0916 59
    0x912640102c0410301803440090003401100d504254903966480305034281c00b52942000390360b504205d01c1c4000c581c15a000a480300c00803604102c2c005407400a490b82441034103030b40381104058220581c0b0805e0081d0741d8994074550310031120044c42c0c030704043c0c9028091100c1c0791400030400507a401c0211000fa20305550b02080e010b050080c108a24025680f211b5086121300c001c0111a031004400007106020980746c4904039154240101d0072581580801484900c0240d80d400a51501c140c0781075004006c11142d200c40c0084075003507810165113403811900800c10041d040d0809806000e0305003448000e20084c4040303040554443d010411200102a440e0f90020703002d814200d5400412120f50014140e0002001d540c5070603004403401128162a04880c00c00810340941c401c8480007030324200c10702c5c086c0d0f42501c0c0d003840e000205006420680890f03420885400c14040642c074401c6c1c80c452500020f8240c16200341458100300300c0c0c40205120303c10720f00800c880c852280107000c40d4160f00307283c034071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774905143 1250 774903893 774903901
    0x30f01140f030f030904060f030b0f06060721030c0f1d150703121512151e06150309050d0f03020906070813060e06070204090f0218070201150617 64
    0x601040c0c035a505141c02d8041c0041070340d15084004028880800140c8081114903075810149604003140e000090802c04144082a81561a407101030742012000b42002e103811610350f00c1e0760940c08030b640e1922008003c068031240090301846203d89212003418010a038030900301001704000c10001540d070390b0300b0070f48085800a03210740c03800401c10f00080306070079076820030307801d001c0e0070314401034005441a410241860b414003501902c1310220780060a0003852290b0543d0303184070344d2101c028414030603991802200010740301c00020300b0003500000c0001440604002c44010010b42c00c03070703940d0140760600715075400094001580d90348541c0c0c6480e00c0d00c0b0f03991084030210040c0c0f0030351141552200c0041040d1041c002800000c03c1113001d5808005940b80c0d0740c0300280d80780215003c460381d104c14180503000260509410050140c4d220300c40b0700c003001c1e801d070340002c0b10035051a04091030300c0104070421041c1d640900c242c4095452111446103190316021000b0322000b1060414411000c0040c041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774906393 1250 774905143 774905149
    0x1b041409090a05030a05040f05060702060904021e0406111b0109061d10030f0b09040b01050607081908040c06021614030f100e011104080c04020c0a0506160801050402030f0114 77
    0x102d2150382c0401580d9a42c00d60100080494100d400382c101d800305403600006141c584a41100c1040790f000d13005034206030f0b1b0401080003d40000680e40e070191a100100030b910700d21100104050029919100c4401410320301480c41c0007002c0c00054951404400181c895a070005100011101070385800f0386101210303619408100000d4140503040819101c0b00c04419030150004460422500010442e40c01800104680d684058801420b2000420014405420104001d03c106030040c4002460400c07403a20041c20348488020340000508184140010003c98040c0e18000b80454802071602c0685006002d802c4000c5205240d01081d03064100c07940350314240f0051650a84210136030796941d626401c64805412030382c11031511035203482c00c2c00602a50403410f40702070b10a28402480300721a58000d21000b584004e01035602842080f2075480050000c000580c4208448000c0300d42041481d90041c05440041e0009441603006000700100b6000c00c00344241194980c3c10801c080c2d5000c1004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774907643 1250 774906393 774906403
    0x902030a05010606050316051e3604151d04170307031d07061b030903230c18040201180b040801020405100f050d090c1d1b04140909 58
    0x300514550800400088064120019601c504040076502c04030045039030b002c80b20381c803420b201c0c6401c032211962125495007881c0c02a041a4104005e00c418801e040700c421803503d180340038960f4000384660298029810180500542c840c038500c40100e0003800c0850400005080c900340780701000c0c03a200040c045c4140450007004800041d502c2da503176800d210320001c0142c00030246101c05c0333580c80d1002da00120000191102100c40b01d5036007000140042010f01c11308048030505408010303604202001141c2e80c0219810023003401900c0903d00f408092440f0306140001c803d092107641c4002c01c21020900400c00b00303038401e45c246080690481c00c8050b2989100d01a08142190307a80820040307a9103c05500500560380105c5000c0c0040c0d20303c20084a090b5004168003000800034882c8504401140d000103104a203c1c040d8501042d407107580245204180301244030311340ca40c03002031192500200b21484d1088020603102c40c581070818034004802c46d410000140640f9144002031034030402880 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774908893 1250 774907643 774907663
    0xc060309080738060d06051f060504060908010c1d0a0915030b0c131a0708120f0a1a061e030f160c050d0302030a0f0c0203031009110409090203 63
    0xc0c0303000b0645841544400d45070300405251460040d040e00322401c0011001c015200f02401007440c0c00341d00d02c3d9625007021f808081c00303910082496802540c064180008401c0c0074004640c1d0342511a460030f08002d007942d01c65804084264980058501082c0d0b100803184e036010a121440d000d1514401c000c5180c00c02c066012035002c07403900d030910308140e03070b40c5296504aa0082051003401c0e00c91000100d030301e2003040d2552903040d600010810140211101190014000c1404039003060f103640c03070b01c28450f8840c00d02002e2082c014401c000650014081c0c1c4e5030028180700c0200282c025009150b121040e0005445104900100d200c292403c0400b04104c072070f81030500345680303900303016224080d488003d071a000011202d040c1c048401e02c1c07003800a2400d40b074000f0001c0a4130005190160f0080d80f0107070488440503103c200c0c403410f5054502030b006907406590700645c1d4901d40100950f038a804c1c1d030313045020842d080244c0004040c01150584042d107041e404000307403008007031000910b00b4001072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774910143 1250 774908893 774908903
    0x3c06030c12060906090f06050306040609032d09170706050c01090c0801090c0b03221403071a0a0e0c041d0d0809010b040606020a12020708030c0c100c0c0603090807 72
    0xb1004030f0883c500760842400c0310320714907041c0001003e8220640c192280d9000d100d0b0554403140c000b4020580381d421800820f4080d00788115220900394070307907184950702070381d010030600d08110290070341d588101e842c4000c01400120060078415030034450384900203841102d00300328020650210f6110298405020564000003031601caa640380e450602a2015003400c0d076017030300010000620117807000100c0e407049901c8180203440b49203010340e0341308d403200b148402d8403d120034140711040301104200074800c2074054201d4440e100718101442101c2c6d44014440c0e1035250030700c10414882c4100007100c0c1d040c0c0d1030880e00401c029050044a24445c40900500000d80c81541500715501b504180c115024482100080c80041500003e02055070b0303491143c00300680c00656003c0100344800c00080e0400b051b481911225a99551200e203035400c1419511140d03082802d41c0800381c604040c8040003c0680c0c2081800704d020354607404c03400121341c4601710074141c54051042c00c120101044aa11980c41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774911393 1250 774910143 774910151
    0x5030417011506050a320307270f030816050706051909050a03080304021302131409090303070c0503070804030b0609090601080c150904063c06030c12 66
    0x1800e1554041c003100c0740d6480c1d080016000c0420018411400c0350b03200c003280c1e117a0342420030441c802107011240312100002c0c404e80d40391b420b40400c9441c600a50180700156540008041600fa900d082e240740f07100010843e440e480300c00c101003041d508030001185d0b00b0001c0b103610b903102c00001d502200307242c120003880c074060303500c021610940220262a90036a8400f190588645290050b0b80702c8880b070003000e50041c841c1200300006a00d00c001154020b10240c0710504c8031042d14650401d0b82c0121251101c00307640910140140b00903203904000700c0d02c00303c030b40303030403609241401c3c2d40c036840003a1190041000194a4005004c010800c030365090380e00038055991160f490900c0348114009480c40c034819a04c02c404101254030002c1c1084c140c0d5155409011000310b00400c01c00e80c01c4074017103021031207071040c080c201380ba5079a40704640c000c20303004040341c4162440c2012000350300b1555150000b11620103400341e030f0b54982c1c4070319178083e64014100002d0b0b540c14040256004035412881030141414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774912643 1250 774911393 774911429
    0x5100e1c03021e2d0115030506070e030102070f12110a0303050a0e0a03020601090b18040606050418030219081b010b0102100b0f090612121c0b030a020d050304 70
    0xc00196010852000a0030b0b0306103186020503d900c03280894181e40990480e070786100070009521041080c2944200000100c0c2c010501c01065003d0144e801074034190000310070405002c3d0401200b00032040100c00845c41c0083c190348080c100e11145d43c025050140c840540643d8500411640b100360403540304039400c0b64280c0c075000713020b0318045030004403080c14600c102d041100000784114000341d15401610311a030030202c2c5031000b400395450969022400303092140c1b00c8204600518001c41c01504046562410b200034071040d542040700e00300c0000d2180851501007680031a80081000383d14540e4240300d0a40d0908800c14020b0480512440e135101c29466400c0c2c0301580030001f006401e80036600141c0c1c02441c9502140c5140da00030303801007940d5000c00c500785007000756181d00260041034284110700c0210202c2c940b074688092040d0130140025076000c810025044103450b00d14984040c0040141da0000c40d80741c0414201c000e000e0380805040c02c00b0440244223079800380201001c0f8010707141c9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774913893 1250 774912643 774912647
    0xa0c0b0c040f0b0304210311041701060f0f150c0b0f090c0a1409040507030602040f0311030105062107031209180507080103120210060f0e1005100e1c03 67
    0x311600c502c004281c40000001000607089080e20f00c590b4003e4241c501440c11484402801400d4100c14820150f598034900620178419001c4e1024003010103482c440c904100580b1030840303500360009840841800c200b0800607240100440c180c0c4c010340d01c03011420828401c04e940c00a4284001800c0011030b8040104210034404502e224090a1044502d200000818091407101f2070140340e0003ca09100f111055060050700150418410021106d0050b40d903240c02003241c01c10f4001070304c2100e109074200244040c480c3d0b988140d00040340208990b080c0580000c0300d0f800314450651410f010301c0d000389450369050004c24000c0d5000032010320300c042a400c000303140c03041c64003901c03062845415600e01f00c0c0c0c00f2031190502c1400076803600c80c00c071303400c503103c0c010a03606d404611421880740303148803025030040340075610027000c0c0c00074080c1c41107050041d0020341c04002420b0341d00d04000e140c0104070682e907081c4800081c0d621414080c12420034a000704651100355148003288846440c980800c240d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774915143 1250 774913893 774913897
    0x1062402030d600302060703051c0b0303040e040809090106020102030115021507050304052107030e0909150a06090e0309040c080403020c01050f0c0604121d13020a0c0b0c 75
    0x109400540e241021880e41d0211000c1051035140c420900c200d5101c0445012000d000383c211201860103c0d15250b40c03030707000034055400280c0850000b040400c0aa8900041050504070b001c2842c0040c02450048400301342d130f030700441c420030400010b450046014889410211128148054001200c2d907858101c0603001c2d520a00ca03083c0c2c01020150a0300d051403021680f0303220030701118030301955a20780d2700d42110740740c0002d44255954000d10302030010003520307c1c498107a060078503e040d640b0b0ba15181009042803080c10302c0a8011a4844100000f0750404140001c0800b00c00328240040c0cac40b440180c80007031803280c0006400078540b1515081604000002d0301c01c40004540a103d130408400b41211440401d0b0340080c090391003904180c1142d8051805091552000c4100509041c3c0c440c80251902c0c0d0262000d4803280c0e240003003008410f911080405e2294400c160140d0400d03000800700701d405085480e0006596404290049100c2c8140c041c5501680c00c03e030480d0007401e000640440d29 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774916393 1250 774915143 774915191
    0xb01030215130b071722060c0b18010209030a05150a0603120503060f1503090d05040609060c0515040c1d010b0909060301110a02070608060301062402030d 68
    0x404200418040461003001242c01c000800e12030041c6040c03500d52002001e401c400400c03640d05170300c28180f0600d808070201400c1c1010755071460700c01c9900401080d926000941d00034030708116071210f8030300100f50b07004075568000c0c1d01a02c0c0c40ba08007500c95440350081c080c0704116681070085071120402d1001c00103181e040c80d041e40c050b505280d155428464100d41032407100032719200481e801030140da070081001d190f10540c040d107440800c1200320009010010a220012110507020040c05402e007410007845880d5a01b82c1491880c0c5414168081d01a003518030505013003004960110b010081c0a02c00740c130341810020b0308007489003054600607100701000d02a4250103892108241818175910704050704a60282d250f0394503025071798003482401c2078001c0070990550749580c600c0c4c0c00c1501caa0024407010606078003400c4550308141740207029501c0940b420348aa03042c01003c2c051a08402d075000340c042d11301c0e03414107028000c00e41b09a0540c01814401c82c0847d150501061614940d18500081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774917643 1250 774916393 774916399
    0x203120f190510050f0a060e0d0311100203010e1e1303090f0e180114190b15030601030b090105030c0603041e030509121501090b010c2301390302160b010302 69
    0xc0d0081710030300c8815000391291100003942001c0c41c0c010360821041e0384550900030b140c042a6141511401e030302c1c00341c0191180c410b6035400401048140200c8141a403c00030200e00e1800503d61820300c0d41001c030003c3e1075240c01307501800310101050f000d003640c1c00040006c030cd2019110342d6545900c14041d42d00f00c0d052076061040001e00d0915030410301c14001340b1644041c0c0305030740b07460f800892444c10106409100da1a07a4070008844140d03106454070360307003000c4044010741d00d1900310001800d0b542400070301c5000e1284ac074018880f640e808a0900c18645068413941d480750307100e0800000904200b909015a202240160024582e10800602c844002078030319180314501d0310711680ea01c1940d86a02c2c40d0b40000f80c4e0040c44000119040b91001034014948002d4111898554109a1483c051629036400f072241b42c0310140b034002c1c02803406a040000e0a00010070320701d1101540d150200e59a80f000100f045144a10a8044c3d03064548001c0000404000c0b0b0341d281c0b40901c59410203001c1644 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774918893 1250 774917643 774917659
    0xa0203070f08071401141210080c01020c0402030604061a030603060f0f1311040f02030f070906020a1509080412110303270a171b010203120f19051005 66
    0x8030645001007203070840711214018012140303000c40720844072401c071800904000d900103c581c40c20b00b140010b405941c450b1203039030b065170a01d4940004600c0083d40203210315000800208156a0041612410100c040d503015a4070b94440e0000703030003000b180d04811005c0c1040d04070059860002806548108820f07030031a40140c58030f02c41002100b9003141c0000c02c90520300002044400304031046441c1034460028020303e80a014000f400340d409040340760307510b26400f004000c1c5030155240140d800000d1030811101c040d051440c000d458012a10010745042040c1c81e1194441c18240d1264441030f4200009a403626141c51a150103500c5000303056075081c1c446c030009421841d000c01141c400744240343d920b000c00048d4002c0c6450250060f44a00e5001d8030480b00012260801e580582e81390340444058400b401009005082600306030030038604541c000d0108000b43c0c8c107404095034109031141d054145d2644d8902219407414881c82c00c2c480003d041106020000d407113000d150b402d50f00100c0342d40c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774920143 1250 774918893 774918899
    0x30c080408030c0f0d1d1c080301180f06050102150910050112050c031b2701060c03110d0806060702031e01020a09080f1b0d06140103120516080d14090a020307 70
    0x3c42c0041b01c4d1040388101c81d004101e0f0740041c503003e81c003140306009640b01c03400040000c2d20b412215030800da011440f2500380d011504042d10030380c440e215040078184e8007040060b040000003981d501e009440d03909503540c0d800208400a40c01c00000100815892083c003c1b580c4407181e000180c02e40e12400c55807440b6002581141e86004680c0f00c0301c800310b1105407120801c080c000c1040c6165140e41031100184110001c4821505022080d03003c2c0c0217545401b52080d180b482e00410740d800161010b015500003442051665030b1058030203070031610403155291218558000a403c025243c015586100940030120000702c0042d000391180d2265a1070ba1503c1c40d6580005035202c04410703a00f440c4c3e0360050007040c0303000c907001c0056080100c4003410340300ea1004196101c608480c0c421f04240000b00c0540c00406c200710301d4150171100d5045518105052007400c003048140030411400c000e00440c1b001ca9845070484940d44280c140c0000b143c4ea842e40350501008940c6c565280c0030f03059019004000000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774921393 1250 774920143 774920147
    0x1b031a060a1b20040e120a0c0b01080a030206100b0708070c0513050105040605030a0201082e060507060606030908071103030d110d0f02070209070e060d020307050a02010b01020d0c030c080408030c0f0d 88
    0x551810442c09486c00700c2c11240000349603031050045500b40840c02220b41c0100c1c02c441c1b800d5000e03200075001000310310542c2c20044c1c54980002c4c1041005040b00d4420300c05001440f05540700e9a0340004a80d85070301051806c45070400c55504a141c000c115940302d5040c00901d0f8028a0403100c080c2c50400c00d00740c80c1e0007495141e21403610040d01003100c003408109481d90300c1c01c0c12307150306100442d040700c0c0c4541c1c60703400c850b003200940c80702c00090400305065080c00014450300c0020501424100852105955000a00c0c01004006400c100c848200352069071401d00446454a4034682d00b046030480f210043c2180c0c1c0c00050700c0c1507100c2d24050205032300c880103100b110040c82d0024017186855541c0081105c8a00b0355100c11900702030107110b01a001d0340b283c0065401005207807119038a85181c0c0380000c3c21500740c00341c4d01741198000c40304025141e0700480400c01260700b600d00007050312100e0800c00302c0c910465102c1c1040c0e20002444462101012400d40c81549002d015a044000800300c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774922643 1250 774921393 774921401
    0x14100b0a15050f0d14150a0312050c0f010510080714010c02060309010207021309120e011d0a0305030403032318090411030607031b031a060a1b2004 65
    0x110901c48400d0303010380e035590b805100039040704104401c803103103403a201141000640f0350b90180301c040d1078424418080603070070200038a108140107a40040e04286551a903100b002c110f1f1041c1001d000e000504c880d2805c600b88084644a21010021701581c1080f6034810211609403054201500032136001003240c036038941401e007141c04160f4230101c02c40290307020424540c0c0040e1500b10150b508212000040e200c1c6c1c003650010480100d40010600702c0b40c107040d110618110400302c2005441c0c1030b0703049030340e070003070b03440d0180003201ca09246ea034822610100b0800b002980015007030340700202e400010564800380056620305201400801c140c2403a9581000f4040c940403150407642468900f000350814040c1c2d640e12a0194400c1c00d11144540042414864180c6080c40001e0b11907121310343c008603000030056800b125140810014049055400321202c2212890f0b101d00030006503900000c2c4514000d01e1031010042d8483d0060382240f0301603000151401502201e00000c1550b84e1035864240305d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774923893 1250 774922643 774922649
    0x114030d170106030b18010321051612090f03120f020303070203040e04020f0409390306050c09090106080a1a0f090406020408030a0c061103011d070c14100b0a 70
    0x1064185908260341034018000b040c0f40c45030071070003000c02c1b1800d9003140e0308058002c40c0100401e8030001089000e000c10320300c035000d0140521404002440309444178445040c982c9030401029500850305410031601072410794003401d400c5128500c08800c4c0800c184403801d42c80801d884e50002e42a000e03805a071280400c40310200580c0041c80104a01c0306035840c41a4828401846000365050880014080b41d000481c140c0310000200e5004440c01c0304816200c10180550f6254100c508103000074a21901c83c41c04010040c680302c501154802c1e90060a441242c440100020700030b40e1141801041100300322400c1448a04201200c0c2c1d04040c10070070501c0300710f00a4844020a51719000b80884040e0151007212559820440051803860a1004c1c0c070207540165119207070103c7c40c0c02c0050644940c0d03440804204800c00042001020b24080541807054a80100c4030300c4c1d071444000e030345400e01ea481c060001c0100d20200d142c221030106549103929030051040000303034003807821f010803030b580c1d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774925143 1250 774923893 774923927
    0x6010602010915050433060b03151203090301020a0c031701051f0c021c03030f1a011d0301020d0c02061e15060c10060e180a0b06060c060114030d 64
    0x160b084140f40040303800207a44140180704890051a000400d4059441c2418003941a9105c42c1c0101e000e910080c02510002e250640c0d2190650600315040c90f024012800250300c5500d000130386c1d1401d4282030054a001c0d20b8010000c54842c41c1000c40580b02c0400040e044001801d0b01e0601141c00c403022509a042e940050004159058040d004498040d03800890100784010901039000680c2c60180e2000111072241c015180b140680c0340150554102d0058406914202410b2907041d5241c600b0381da441490034a400305400c00c92110050f00ca00324a000d0541650000901c08030317144d00d5411442019445034200d035000d5666032407009003400c00d900c0c0501a200c0d0f031001b14504003210303114441d00e10002400c40b40b500184001c01d03071a045209001b20f0043d510761004105e01d00801e00101c0c1e020a50341b20350624480032950054a9114072200140403101d00400310380507803280350130f440180000380d0072a0a29615040c1214101d00d080705202e11074031138586c0d0100c41604ca1620301d00c100c0041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774926393 1250 774925143 774925163
    0x403080403050a0c0b27030403020f090c070f0b010e070e01081512030417251a04050d050703050c060406022808030a0c020d0e0d02191214060106020109 67
    0x3a40c1c0031103441e801006088200b05546629074085010040c08a0092145002c0010501412415840e17855401560120f072500140301c10000f5854107286400f010108a804404903a100b2002d12403500845030b000d00080d21542c034250402042e244a64182c030744072440352a465a802034210b45a4000e1880c50303000608210114010f403c600d4910140c808004000c0010110305065031403841d08980d00c491205030325120156a140d40038411170460f01503a180b015501000044140c1702d0648034410090f555051001d812484030a01d0155405031030010414052008e140c2041c540d9520700303000c01e888034001c041102d100703840c0c98000c480840e41c0940107001c0c800349a540140c1c4540328510480d0007000001552070019010400952140080620010345e44940703010003131418690300140420310a681c3c1c0c4481440ea5210b800603282c0381c5c11101780e40805100440029441c0c00c1d9440031000183d00c41d60390741045010740990403405000412541640c1e03945d44200e090b600000d00180c881c03070107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774927643 1250 774926393 774926401
    0x3120204140d0203100c03150f120b0c07140d0215100311060d090b0f07092d05031002040e0606030f0f0a200a030e0c060f130504090308061206040308 66
    0x442c08a200d0502c0c0000d05a6100c00ca41400d0300056034a91680440041d0341d505580c2c4409218480310009003d081b49041002c40c20984018690080d41e180580b86502e2840059141180707401140c5620fa4080b000d0351801c0114446141d490701449407103c091300441c01d050500c51051a003044c4600390382c022512032240386031540d5521004280409800c007601f00b006602404a40c00ba1460f030074403401d44c2c0169490000b01003128035102174030140c104100c4450800245d10110160046d0f211100004109400c008500e01031500da50742c0700070307014000d1540381003020302c503540580200c40140c400c01d0070a584d2a4100003007444105c81c008003030a0010085824410865056648041c40420004014100e45503800444482c580c00403260b881c00200b403503031191f040c02115240c081000042640500400029160b4000c4030421003c6e44004590b03140d4030070080d5204002040b001d0810000f9180500b801024040c00b00c481501840c0441144520f103040004e4841c410358050341c1c0e551072611 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774928893 1250 774927643 774927649
    0x31603090320010b0618091506120705090d050f07050301140c070c0b0f0405010f082a040314030306011808060a09080d020c0604030305090d0203030a0e03040e04030c0312020414 78
    0x42d5032288076045650300c85040a45444003001488100126200d03c000c450203a02005080c02e13004010140c0300c00131075254070260b101e01040c0c0310b1728400048400c4560303903540400c4650340909030b40315610800c0388940900b842070108442e001d5440500503904550b0f00d84044c54245c801d2075030300c55141003550001428083d01c0300c01800703039944106c0c460380f00b0310758807000da1010381c000103c4039400e0000041d00300007561b000801e07860321040a042203400e900e07001c10584851208c40c1d003020b02030004840000030301c8043e007040710061940021a0001500305117040c60b541c2e0400c445503804a06452150b040304c0740c0541c4280201c44801004000c1a9911b14018019026205040b204150207000301004643e103400035068040c9200e00403e0b451505d405e000f003c2e0303600689604119004180710703030045035012040b42e43c415003010740031402201030002c103441c6211b141d0050100d404040309200400d640400440901402039950000d41c40c601c100150492145110b881d44402ca10f000c6040141 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774930143 1250 774928893 774928937
    0x1005030a0c0e27010b0f01091212020f01060f080c03030f0a0e1f020a0201090f0b0909061f081009050c0a11250f0f12140f0307080316030903 62
    0x4000310042a0500c903442003e0612a01401000015944402c4600b6542c1000a42036490003400d192031140503182241c5c103c03c4031540d4201521a10140f041010030500802c40e84419915800c000c00c9103c0d0381c1c0f0740b003051145803400343c1107280c0280309030219680703000010746004d6601848580d240c001883c0e800d45c2c000c10f540741d445400002c00a002070003203c12100b004010002034028140084183c4001081c070030a80d0404203d04081200600041303200c03106070740e450803042d00d1036807881e26050001002108110182d00c01d40b0024a0700d440001c0d40940640c1c024000d810101203211303102d04d00742003a1078003104c0b000c082c50014001160f100388151235414a0102d5002942c06080000e081d142d141a002d0f103038031001c11007110080002d034200019480040c13070322540c5003030380a041c04684003010241800c09800758260500c41c001c900d1040c002c1c00806038010040302d41d141541e18000d5072541040342c02c51040110400c4201001e8000d01801507816417580e1545905030100701c5c1c46a200d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774931393 1250 774930143 774930151
    0x15120a0c090e1801110913291201020c0a03080c3f01140a06020a120810091404020922020103021c021606051f050d020112090b1005030a0c0e 62
    0x109158071480f00f08070b9081c4a072007544d01c2c404000c00d60f500d1990050101400c06104500f00e0b8030324000802c07210504d110707010100300990700f45254a1a160b0400100e50384c07000040100a94800039040c000030310000342c420803584c440d07102d4010740d80d290622264a4007421801ea1040b041c820308950b18800c442c04001410f141000d1030030710680c486004c000c1030320f800360050a45008a102d00b070404d49040e000400003403060784000c14109941e41d40d80c565540e00311106c8002d00184a0110701f10b800305c0e281d00720141418240400c103810101503804046d103415107042c3c0c00340308d080d800f19000f0010010015038041044032010300486c4154011802035228001044141e820036541a1804013240010001101c01d030440341008482800c01c0780403190042c102c1c03682e407240500503c09004000710460126031049440d800c5602c0540010f13030703000e2000176a19194a14219409040240c090881805a17132003070038200c051b0f83c6036070505a075110103400103450042c494a041200c0d0440c80c900c4d50748 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774932643 1250 774931393 774931411
    0x15150806010507050d030e07090c020715090b030712050f0906041209050a0806061807080c0c160e0a1a130e07051c110d02061801030b15120a0c090e 65
    0xd002d8564403458103080e840e0b0000d00000351907c040008004c0100210301c060445003004000180000700042e58440c103502c18000c0c6030030204181c1c05103500030a05003006280203085142da83c035204400401ca0b94010040303100741e51400c404210100f6150328114840d4603108001e02080d2240d45480a0000418100d1000c10001c280c2c041000d4550010b400000c00c0c4890040a0b40d05166003048803c100c01000208103a040302c0403c0851070740248540e403c044104001d544d22103a104000c0d043c9091207000c0306900014100000f00d02c140048140d10070070045a041041503401020800c000105280310b9a000980700c01d160700c040d45075403182030020a00d0701110110360792003002c515002808102c4e408401c40084013a0140442801600f1814200325079405107071030700303500050302400348682c400e440b0004004500f100341d0003a80101502840144550051403860140780d2090b4844141026480900d50100d900ca43c203d0052401c21200c580302d1038800c038149052080c3c82800206060301c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774933893 1250 774932643 774932647
    0x50f0d06060b0a080618060607060917211b09210c1e010203040e040812040c0603240302090c040b0c010501060915080a05090a020301060b0d151508060105 68
    0x484030300c01d410091040c8000c4a031190701090000d0110580107000501481200c0f07554180c40095120555200008580d2581c5841350b9080040c01002c5080000300529210344185035280d0080e0098102258406e0001c600c0c070b00d9410346c0000210b81a0b402c3c620010342540c000800c081c1440c05000c603440c000e0110805480440e24090f4002008a030743c4600b9042008840d225040c0007800c980050956090b140d031500b2203000003940c0303111f941b1800031916002c80104007008291000c030343d400c82080440b81d0607400d00b8140028080e016100c0d0301d01091810100052500402038403841241582090703d03071141c03030340e0240114900d0082840c180c0600c1004040b8043e400340300980307400742d070103800041d0315814840003400000070707504081546070ba0744c41d04240c4650b0081e000d44d4480110786000c00c09407a0300c0000c41c544000300b00025419424920301207407000000001d4040000f004406000005441060003030208040c003500341180400194011035034000c02079290440010b1402034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774935143 1250 774933893 774933919
    0x30c23070b0a06030614010e01030201030f0b0d150501211502040e0c04030209180a032706020f0706030504080f0c0c0d060e070501110a02040b0303040914010e0c1201050f 75
    0x80c1c0140303021140d51182e1a900d03a824401e00006104070340d001005880000c54650400003440226441440002d04060315954070203140310b01a001060109809020b15031500c102e864042804a04502002070039480d0200003d0020002c0d0070840030108290200e00e02220301e42c50790b46142000041d003e1005d5000c00001400180e80d00c44540310301e035400540c0b900c035411441044000703000648103040388410007214180b00c40c4041180128603a150509817150101080040c44040c4512118030003c4070130440021016000b054008002c1c12441c261152542c07582c0040c0d00b01e031401e032006448030a052100aa20505000060203101c200c4002c45040e500071030001524201c50007002c9030201c0d2965000015884100002d00143c03500b42001840211090021035031000ca41002031301c1a5240c0d900b07400c05880c203000b00e5000d040050001c0c40042d681c605000745c0b0090038854131040303c0250b0005141d02e02150300b0313100b5080403498590900e9290a042041e90301a07406040d80c07102400c0c02c49 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774936393 1250 774935143 774935153
    0x1021b1c050f0d080a0b0d08040e1b03070509130509060112030e0312190c03050d150509070f090f0b0406030f0e0115050102150402030d050f0d060f050907030c2307 72
    0x50b540c42600f550714016030b80381440c0ca801c01d54000501d564007072129250100300062000003034a0950307111707800e0100785940b4610301c40c005030120013290480507030000c1800300c115442401440340741c0c010348030742c2c5080303062426440c100c1d44211524041900800018061001400c02e4aa0214020f2529683c0c9481d5580024201081021f4031458003400042d440d4000d082e603004040c0e90f81d0541003001c0c42a0b183e03100980710744078111308415625501d03055100d620b01c040c075011025003000b40480d29185840100a020030b0845641403001c60030713820700003c954034910701544c02c0d00c100c05415401d080c42c043c01600501081045650407585030215601483c1e024402c070000c01c1d40c020030100c5614901800a820400c50800c84030314036081d0002c100142e140000d080c03500f04c2a5140040d0303030b07010210300b00d44075020780040e0041c014105200020048008200032003138440407906042c040d29003400640c02c44180b0940d50003c900c9480da00f90003241d4141d420850303001c20840003807a111640c0e4803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774937643 1250 774936393 774936403
    0xc02060d0e0a0c080d02100b03150a1a100c02040207020a031b151103070f030203130b0d05060d1a0c160b190e071e0b04060503040201021b1c050f 64
    0x80000740d910001d0300c803041c40342990b14900285020006445429210207001752038507500001c84200b80c0d102c0c5029001a1400c1000d81509a030100001ca01e908060003d00050441e0445400a180c50090040000d14008a8845a811268a07100c1c40c11119a0038840a500281030680e0b02000071a8008042a84041c9400c00c0740c0711410141c1c602810011031500305d030040ca0251081040520000c2080080081154900d54011110000002d4035140880c914416580c522190030321000c0d00091900c0c1e103038040e1100888003034007070101d030351070506119500c000480003405503022482d4010f88600100c3c05a034200b90007983d00c3d840c100b40c008102020a101721000c07200802480e00300619a031526080401e840807060043c41540850b0441b603588101a0203002c0d60007842c50b2094041c6850b0807001c6005144100e00f0076111940c3d00c80142884d0411581680940900741e000704030b03070f5080000c1c1d5192420041c8038070480c55002c4500100c00b90b0344002207800388190003d030002c104003081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774938893 1250 774937643 774937661
    0x90405010506090a11091212040b040602070e070507020d05010f020f0703030b0603090604080f09100e0405072d03182d080a03050a15030b010603060e0112030c02060d 73
    0x800031816040c290140400700707400820f80100e5a2409000810311200ca108958119908030344c001130880344035490505007200c1c40700300c0503c0a0006000100c04080c10050f0040718a01d03005c0d2541a50b07039030301c1705421200403100d02c00000c804000000c0146084002ca00400740a0750000554800302c000c3e020490384a07507007a0b15102c9001c2180c10030158103002d0394030200c8080c0d03035290450070a05001955000094030062a4140101e188003040c0c00001c01e8400c0c401340181003061060207828060110044041a01c0c003d40c02c007000601094042c1e003000040c403111075083c1c1c1d20032940322440804010325040b1748007055201c0541c1c0555070700a40d2203a000717a00681f044031001040d03007460140d509414400d008416980d61001c0089000300c2c065410961460501051740c2da10241e0100040c80101c10414010ba08101c010081c000c10384a410705903041c9031001c01c1066164111444462024441c09007541e81070054000004c1c0b042c1000e409407440540b5150910318040c07540d00550b0b800e00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774940143 1250 774938893 774938903
    0xc06060b09120c10050918010e01180c0212090319050102121f0e281a01020a020d080702190311040b090105030c1020060618010b1b0307020904 63
    0xc00c00d41c901d854410300c215080d81e14980101105400c00b0041201030030402c1e90201031020201c3c4990440d00c030500d400b01c0c54010403240048942e101d0840c00b0a40c0c1c000c1c001c5d10403001c1150b10452840403075214640040320160010300390f0655a242e02c0c1d25640c4090f56039038150003081030300381c0400700780c55110701940e21980001d42c8648403210340804901c0020300c0d044001c10900840754114043c40716038400d4030707501c96106e5800d9881003000000030203a03014255001840c0d0f010342144035170380c0d805410341c0c0c2c1c2031040ca4034503035020310012a6150740d41000030b58021076000702030b400508118028911288058064203601071a10300c929070340c0c400c50b070060700c024202c060901e140b0310382480f0300c174100001142ca650180d41000c011a44d100c42e181c00507402071400c0f1070300c07a540c20f000e4901100c0b825500e00f04540b03107045d501400c5031105800c0d41d4140c02104086c1c00d2903c1c4480d000c541a050700c0c0441040d508048400f1000c1e40350340138551082920b1701041004401580340c2c40c110700d11441c025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774941393 1250 774940143 774940147
    0x7020c130f0f02040303172203120b010e13021605010e0706090b12160c06021605070504090b0f0411030105072f030a030e01020904051f0b16060c0c06060b 68
    0x1800a100581d0803100781916060300c1000b00f400001d4000b000320542c501c4241c20601103a1700c4040054090032030381c550004480000c110b00080542c0120171080c1c048000f40182f128076005001514034114401016912101c41d00310074800307040603400b03080c4140c1c000c0c8c9103908a0b0701540314682161003001040449030800c503014000503400c2000c3c5c20051180100492410780d402040305020003015000080c203800390100c00e10441e02c580300b824840c0341c0240c0115540c102040464000300040c0c1070441c0d150140b85d10006403440e05101e07620ba0b070361b0000c200b030034659508a4158010540208211600c5c01c00002200a5850034490207108461545031540c4c0e420864075846000e5242002d0182060210900c110b5207840101c1500c100291500300031413404805e00c12580680150b5442540240c42e103001c100d0b034041f0408568891101c5010242d5031140c440030581040d201e810402141501c0503250b110001d24158001000380c41c95191041c04400da60352440255840355205044080c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774942643 1250 774941393 774941411
    0x41802090708270a0816020a0b03011503051005010f050403050312010e0a021603030f0b030a0606170303090a080304060212071e090513090c031a04030e040b01080f07020c13 76
    0x1c190600d101c030081d4030018143d40040045269204034000c00141a000f000c14820410540400341340e24065005107420f54090b1a01d01005180e002481402818102242c02054841c000d02c2492700848032000c40c001c806e4188401910803a544000540401400b08030000100f102480a005092170003401d07141554502400c42c8201c034800b03064591454410480742c801020b2008403119100d900d4103001c2041c1050750071b010001c000382c8070307403607090701a4810040421140d58000e40a6a0140c00107140607060040e100e50380b800120340d05c0055600c402c0e000070101e0f01d088040c550152240324007524012428002070508001900c00d88041507064440822f00302640c0461080d8600c545810400306103401c001400c8030403446106020f0315541c16448003400241134212000e180c12103203110780e01c2c45500440c1c0c142c820441b800c0d00010f42c1e0406c0d007000361400c2d0061042d1464169102a02901c41d00c0041140d11000340418095105003507038028a516050704083c8800b0782c1290010707101c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774943893 1250 774942643 774942661
    0x31b0d0c02011d1b040e0a2d1208060d080403060e061f09021308010603080d0501081504031d0406080307030909110f0d09080d05010503100506030606041802090708 72
    0x44000351a01d0314070030001910f00800f001684a901500c8440002a410f4505010a0040ca00d20400c0c41d41070007804151800c3c051035030b500c4c0340000754000e10703200c0081c2c0d8107031003080f03800803200010031070000210034964252140b80d045400c0600140510110b542ca5622071507181d12540c421038000b9140c0c00301390303241c00f814072489903c00303034120702c0000d410450418040100c9844c0100307046180c0c0401c4002d1207140c220440c01c080e14141c0000c00100781c69041229841e0000360040b51201c2c1404008240d420f404030b514015104440c0c80302910b61240c0d0750035036440400756183c1f5001281c000000d86555268004c54004040040155990f14010300b801003a03241c250b08443c2c21103003013a40004021005a003254000c000c0d600001e510f40c120848504040d0a402a0103000100003040300701c080800f03035100070f048840031400c4840032100c04016034203403202190082d034550000c900044050806400550040c42e1070702d510a95440240c3c0040e14802c070589041c6d000402d118104a5a03075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774945143 1250 774943893 774943901
    0xf0e1f0f05221d0403020c0d0c050d0b160309051c03020d050a0605040c050c0a0807150f020d060909030804150605060c030a0e01110601270e010c1b02010503010b031b0d0c0201 77
    0x900b03d4402034900307241c01d850103590b80004051041c007882a141c0e803501400003510381030300502001000903a488503581800c0c803500c1000d45809590000c2c0306a00349a00780030744aa80340459100001d05540d451454007240103859210b00742c403d0507020880841c000304940b1809200310540c03900001d0300c038146414442281c0e0311a15580a00c9801c210345841a9400034030091101d40c01072120760f40f040103140002d2425050001ea180741400c0c0100b40180300390700d80140050007400036042041301e580305005009d651403544041c0c0820080c0700810041800f802c0700595003126500080f8030280d40300c021560581c0700045101507038002040c00001d1035441000401507c1003480e14004201c030305841c15407030305018070a91840c180c80c134088207100d4054040c81c00144c1c0400c01c00304000d0000000d01400703031100c0c690410020b0590500c9122840c0c1c21414050110b4040c0d40325800c5a003051415405580050554024081098440400100f620f0b004014601c80f00d10040382210402201900355 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774946393 1250 774945143 774945179
    0x309080a080403030b2e020a0507080a02090f040312110c070e06040e0c06030c071a0c0c07060f0e0f0319150b01022107061b0f0e1f0f0522 61
    0x90b03000ca190800d1a00070488118024060341c0094034103103030007000a91412300910350050a0f4061031000050020006c14802c0442c0d00030303620000b040d501c51a450180319400c4800a010445a0410a407819155440380002c0c05241d10440c0c81d02100c86180c5140c4489a801540102e4920041001c94201801480003512803880100700401111000904a0000070100c3d0f054080109d07940d0180304154a402c010310241c00384113191814244d48a07401603015002c501c103540704002000071300d140b1510b05c50a580e2403607981d5003400c68201c0100104040c004070a0750341881500310403000322010006c2d61404501c115050101458180a030a042d569290034050554004000c105900e501b01e21410880894945500f50303181c100d031404000401510305050303100640980303031180303c580041d1504a40140780d1541d07080c00300d643c003c10400044d0b01100e80e41c8410f80c001030300b841130f00415070704000d01c056007009818902c40e2140e000b0714854004095696100e5078200304900d06020041c4c0c060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774947643 1250 774946393 774946399
    0x230405010b0a120b010503040803100504050f06030c030f0c12030c030c1606030b0d30030506180103020f0d050715020c1201020304170310090f09030e03060f0411010309080a080403030b 81
    0xe1183c5684c0040c0c0503000080002d804240004002a403548259120f000503000c0184200306070700b040e480140b011002150864000e00ca100c0581c80181703000144800c000c805c3c50001c100c012071178000e10070702c001291000403181c402070150000c42d4405002801c1c100002d14020190043d0f0712454005003103196010704103141c0b400810744071507100c2e4030f00c6500c0140c00580c001034400c800044259860340080301c007030006000031b84a51800f94075800c52030041c502261f87c2280d282032109032841515080c440207500c015003211048442c2080800b20540a0055050316907503a628494088118507405410b001600080f85a40c440c2c507048000c400400300da18000c50031403400c0d13560020044540c21aa07800d0700004000205039501c00840a4041c1c15220000c1c4034150302c0c501c0070000340040c0d282c100c012503101011030030300b82400204c4038030031048408040344a40361a22650204600402ca045c10580c55044810200320f03050003d0100906541e184c50702d9180c071382001012619485d603501c1c4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774948893 1250 774947643 774947651
    0xa060807080112030c02060a0c062706050903090a0b070b0c04060e0114190504050907080f0403080a0b0d05300f0c0313030c030309060315230405010b0a12 68
    0x12403507011074180d05484410070b880301216030303600b02542c0002c081e0701c009501c040b002402210b100d51042080c498070344242400d01004826501c03001c1d442a803c215580702101803807100d00403844c1904555081b40407030090b40d241401e82804075403102802d8001002141002898000704900d41c080c4c21350100031988901c1c1043c2c24000000c00c0c903416101c4060400c0044c81442014801c14801c90b40b0114400f90300c400000d4070030002a0080d0407070300c0707503d1251920200160300580030310300b03a900c1100c1e00e40442c80aaa10759405840c0c230b800241203914004e99036080d040b4103071512000d202d001405940204002c0c6040300138003c405002d40c0c61185d000600000e0554008500820b4421001c1810340c000d884040c01d60382e80786107003c0d20103080d10000203400c0c00028444c1034450f81003035030700a50700d04a64a807108810303410b0310300381c41c1c018409016080e000c214885e40100c0e20131214580460884508800c3e80c00101504c00a0f017001c0003140c00042c00d540f085410140414007841d034904240 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774950143 1250 774948893 774948901
    0x130b092401230310090c0903051e0303060d0f05010507052a03030711030c0303163207291e040b04030305090f0111040306180b010b1e180a0608 63
    0xa02c014034600820b0650070ba011012841e03503610445154040c080a080411100100d10b03402407031008544030545250090320100910800494000303000024280e0003549140c82e0f20301030001541c00204291040d0f08503444034000110700f80a214007840c05d941d22542c580c00003400c04001c00d01185440b207000203044c4014241c1c41350200a4aa020405040ca00d89007030322600ca090070351040c4080841d0a000020030001d5416100d01d501d170759a0120341e2080a078031410100c070029101d60040d07001c0152007040310700e1340040020340107100180c4121068041840158013400d205070114101c035040420365000c0113a80000b90245513450780301d00c0c0c0841d8060174142c90300501040f001c6c0c0003504264541000071002c2200f005030140c044e00040c000c0000b4500c51162045c81e4000c0e00040310b0f000d0400c08c0a4000140c81144100582e800c090107050036481c0c0442180f21740e01100715030000350000844220780d07101c108081c2440241c000142c0b03000c00980d80801070180300c1a0010014000503000740 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774951393 1250 774950143 774950177
    0x150a0c022e0e0612100314120405040f0b060a0815220203100b04031407060e060a2304180f0c08070f0c121806030c020c130b092401 58
    0x8840008250501034108122070001c1071142c401c04038000d044130b04490a002c854041c10302140d00700c81c050421820601140280f2903141c12a55111600106041c8002d000300d00c0d195001301d43c805400c403400203640c007041000c6880c5812001d241d1021660382410042d0b1303d2907150042042020071124032015105240b00744c40c1107103007900d03070802599001c00061010a490840a0080d0440641d05034a680d580d1806074a000250303050020180034202e070015916002e8000e0440003100103203c00d040a010600c00c60f25012080340d0309152111100001d5002035005c4000d00c090411180305142c2c0d407a00e80590700c15140e6591103100c460340340250f0140750980c0b1201541d0002c403949401e48225404003c101d440d061407220151840c00040c200440c541e82108810300800018040c401d040c036a07942060b011180b02000410158105000109030741c030f4480300c070040c008a0715500007510441c0102103006440e003128020280b036202100a80c94911510a01825500902c1c08198000d0780c1451 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774952643 1250 774951393 774951469
    0x13020a2108031e040503070303150b0d0e0c120a03030b090f1f0305012a0809070b0d0f02040801020304051209030c010509010201020d1a181014150a0c02 67
    0x1500c1c1060100204a00040803402c02c41600141d00c01041036061a041c030710344030b9001240490200e450020008200103454809000711000900481c2c2482581d040140141c00c04518601c07144c058410501c06558540001d2a1401000401000c400e00c5500e006003c0300c04080c54544195403110030030107295040314103180e0004042c3c9451628070750b0701e40e5824039000c0a400003841c82d420402013625801405804409881480260802039502100d0035035182c1425a07906090703800c039440030711101350b003c002845201c0c8003010019030070751a038a6040c12a0400d4002c2c0c80c55940000510081c040100954503080b42105411031402c0740030800283c0d555045645d46040c4040802c1c8078905a0013035050317039003030030340720806100107040386509201150043c02d0300c5218869038184000c2403190569200e00c02c03282080102c404504141c0b0840021000003507160340301ca1010310f880d40b003400b400041c2036500c0c0c003500c0c1e15168a100f03104000d890244d080b810307010a0b0324500c601c0c0ea08110080 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774953893 1250 774952643 774952709
    0x50c10030e071521050a0b06070506040813050310060f050108013609050a0204110703050904090203160e070f2a0206090402210906040b1609030b13020a 67
    0x4040c946a941c0c5800546400030380000e680d120102c0fa00c403440c0b4200182d000315100d800c0301b41040100e812184200700b00e901132850050180d81c40400000d001030280002081070200d4043c58407401969080000c2c0340c51261880700501c2c135207a810801800c10890202c2d03000d88001d00303040c9060b60600c0244009074002e201801000441904418401c410112549010310800c80e0305020303450f1241419569030b011b50380102c0c0224a0003503400c1c01144030744243c40140ba4503940e5030349003c08807020000a4103180c00c1c01d984c94020b0540c0c1d80c40300000b40c0d007918014200501200341d5403130f0011010742040800d40e086004c2c4910501e4440000000d858603c8406030460510400f054050020490a00a040c1c42c0c2c0d401c1440000d0741c3d401c00e4560754154111884c000035810480d07032210009030301d40400b5100200a4801c80c07011648500c1c1d0b02d08540e61180302d43c94540c4459950f07450b6000860380540f0007444446051115501b982807504c004805003a43d403041d042c660b801e0450403c1d501d81650 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774955143 1250 774953893 774953909
    0x105060307030903120c0309021f090b0c24011d01050604090e0703021c05071a07030f0201150f0305060907030506060d0609080c16270c02010905060103050c10030e07 73
    0xd014501309800340340c40c1c4600d4080070804014450220380090002c3c240c40000ba4815070018100300b4030110410140d80d01c4807200c0da10b032044a0314255282c14030750050399211002e400fa00e0741851584040009008880301c0004401e0000c0d490714004045181b030102074130340b1a00c15040140400d441d1034040b28115031001200207500008000b0840c14070304217800095100b41510394804032800c2d409a8150400e010b04241d03411259158040d01148500d59100d0700101004d110ba0303800300740240460511007105000200340070450036990b00140450380c014000f0b10b94501c80500038030404004175075005d01d0240052444074150b450b5180e6402c0018520343c440d00d0704502c401c0820101d43c110003626603200b00c0003911142c40344525a02c40008080740c40000c10311690001c1ca100401a85424111503900004800b050f00b4102801900c4071502104c103542d251141000002c40421440d8000c40c0070724040c7c02000c404004000012482031000b00425041101960f01050049440c0e07040341c51003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774956393 1250 774955143 774955151
    0x60212010e0f0c070230030a172401140705030a11010509280218010503010b03032d1603030518010c0e1201150909030917060601030506060c0709090b0609010506030703 74
    0x4c4a00c1b85030218203e001000701004040c04100500c0001019010f180603940302c0030320071002c0000f052440901180d800c68200100c01c58124440b048040c002c44070841850200303a40c0140c48500e59032940038000c122003952001507050012540302c500140040c001800a2105080c604105075a442940c044004070102c91608607080505500c40c00501c03030b9000e407030384942202ca03d0140205001c01d100d928080d5003007006a4000789004001c036001e03028105e00903c0b040c6101c1d80005c1c2d041b10100840b0b12890300400551520b203480c21503a81d00d542c82940c000c5018a40a1080703411000c4002203080e60760304210b048903240ba04881d44542600007070741d106500035016811079002d01440e004440d842c650040000c602c1070456040310742294007984450604076034403225000d001c2200220030f03409410000100305290b12036007040790840002480e1034181514089440e0603c1e0190f4000c100c8603580e030a02c0e10070400c6242c1003e070311800131140c0304500c0d03243c40045100d034031004060900301656 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774957643 1250 774956393 774956419
    0x302060d0b03190303050a140705180a030818100509030a02061e04061e08010f0510180f0501110102070b19150b0901110705012307060212010e0f0c0702 67
    0x10403c8441d0402020b480c221070b42c04054140500200000d035143c07210309061805035411000940c400e00c1c02031a080d50b443d49007501e00c200788920200603400080d40301c41d00c0000000890b4840016100601c50715421a0086403258104105124411008003d1080500c01d03c806039030003180188a00c1d03019a02381e40d440000000c964001c5401c0d8905480061002c0340218585030312501041100102d809941c402076a40780007520070b90b20901ca081c5030044040c00c00d101d039052000d07900124001034203120301c240d00e030200003c100d02200d411800c201030441a0800856a0000304015484140e0000310701d00b00040c1c5608040300f200821850180b0692015415171b11b50a5001550500c0300707014030b0100e2a1603c00d011016401400028000b80000d40e0700c16000744042203140c11144140c4840d401c0d452044030340b501ca030080e688a200701c0b101c10302c0500e01180460000300300341f62081040207880e40c1440300744800b140c405403144c03508580410402041c0010303041141c4000f03804862013400131720 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774958893 1250 774957643 774957649
    0x13050c0409081605070810090b13262a06150a0e01081b03010513020f03030409020d0501050312040303051804061805090616050d0c1112071a010302060d0b 68
    0x30403480300c02c4040e00f280c1c4a80040c0040410450306468884040d1140e50141e48003800644071780303038405022004090007054541c40050303404040c8070b02c1114223072100d0b0400c031880c104a102240c4050181440064401e480304d040004288840b43d440d00328007402d66100324200d030307035810081c00b040c00000d1000c0c0e4044281c1c3c030740c1c1d8550014444043c0c4454030f580c4522003c0d8035110351030b080d0807401d0600c02c4140030303515041c00303401c0c807841d0100113500c8152540e4081000030500000002e406010400010500520600003020401c40c10740b4040740300c0d490481490320b005a00318040f03078000428001400001d51240440b0900078076400d107035a00074811400200140b54641c0040050a0606100102d020a50300840d205507004e0003602e030716076903242a46440c61885440080003400410800344105841c0d400500c075103909142181c0096080090b0314980b00d0481b60b10f50b04c1100c0440c0d21400c0042c04544a04c40390300c80501c51503623503d0359001c40c803603009035403218030816201c2044002c41d031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774960143 1250 774958893 774958897
    0x3211305031603030311030103050d120216050106030c05030102070c0b130504050a0c09090c232a0d03021603030f0f0f090b09030a0e27010308040e13050c040908 71
    0x10000a0580b500c2140000c1c110105000510040300441c0c1810040c9003811125010341c1d049941000c060003212812141c100e642d40302800d11640b44039030034803400c80d10a8120081f200282d1090b0000191a800c0d820124111030070b0f503000911aa0040082c1000a41a03484d80340031103038426200340c4c8900500c51800c51301d40f017030703048590000e15003802c1010051903904030000c00702190303c1d200001c6031104101015140c01103c0040805c421481c1140519841010a0110780031200941c0c2001500c2c600c034050310b110804212010401c0c180048007000051125160003121800c08503d05190b6800818900b501e0220260a2507910381003040740321019045103041050300c01003001407980c0252203c00a00001c841580c040d440c2c60700007555900e0000440d94070b02e400e40c0315515286200000c201a00441c0c8040e8501400481e44454070102503404682c040d6214000c1e46448070700741000640f0000005050025060848400c0c03400b01da4086820469104203540102c0c1c1038000303007000182c078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774961393 1250 774960143 774960149
    0x190320030f0c03032208100f0516020c010f27060807030203092805070603020d06050102031c0b060c120712210507141b24130201030b04051f05032113 66
    0x90048a01f1600681210740c001045840203410420080d00e0b4240121340003424010a000903a005800c007120940c0030f400700a16103d614030300055403495030800403900b0808841001412100c1040030f0100d1134000d80d0141d0b01016038030342103045242c0100241c0e5102c0180c4030300d048080b01215048072440000130028034080d0098102c0324443c1d581e8000230003e40c00508075600c0c492030102c01181c95032004c02143c0c0030640798490440145447c410f1640144003120140c0d5020700c00304030300a089607061242d012101103042c003031502c844c0c01e82090b44100e81c501d5184030800c02c404803125109550541240d6902007503c1d40000c550365107100698a01315000101200300c0c1011400d2452160300b5215070701420403410980b5841c19914103282588090a5440f1500404403000a0112101c2020421000f401454046124524035020808032201a203102038050441560041122482000d140040c801900240701b100c00052060741e000c03c0c07000510420b1139000811032a90307620781d4008005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774962643 1250 774961393 774961409
    0x10f120c0303140d1404020a1710020d021e0d0b1008040b0916080601081002040b07060b0f0913020f010815130b0604080f0601050609010509190320030f0c030322 71
    0x5e50807542c507507242c117010200d60480c8240c80c0301c07101050070030100212200565515006000e108002e0209a019410014224800f0759092044030a03880006440c440f4014241200f00e81c0c1d200c44003800010f0364500301c4406e004040310960a4030140e8071580140d405a0090001d0000d0785a0a603024140300740303c07041500c41d900d6410040f8580c140407e05078104c496003001c42e000050850100b501740c0c000c0780305200c440e0034103100c01c4000c251250001c080a0318010704204400f0710010005141c100203460100300c070784603590303294218107048000501300358007420090400d18104e801200c0d030115203a42d45001d05400c403d450320398941904103c02150000f407000fa00c541e240e180040c0c0e100103503925044c02d4441d0200005450500d81c045500315030069442600e009801750a21240f41d0200d4070700c0f1041e42c0401c0f4000082070b1441c203041000c19a5a07500081d1040180c2010314061213000d52480d07a40042c40c1050450350700000300e40c41550300805080111484000c4d600d1200c0d4a5409184 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774963893 1250 774962643 774962651
    0x10302031801020c01061809020f010c0302030403060606120b0d150e0c0909031201120f0311160b0a020f07050a1511030a0305010302040e03090102070911040518010f120c0303140d 79
    0x1405140c19002507050f41c6512501c40712031445a007d00080d00c1d40248080d401580b4010350052951041070003201c0075000c0c0c01268507069403a0b4a102c120b4005920000c001000401402c84401c154014054880d80c1264158500a17846d1581e6070411044450550100e5449a01c094440810300121b10ae86200034882e5081d45415400c607a00c0c0c0e48907034803090240d041d40c0000704141c010480c20490068100000500b1147d4556094400d61004d040b5602144940980c22034581c9041007014060000101040e0706c580c0300040107860306100103140d140c1030300410300610070b075100d002541040f1102075901c041001c4624400f0781d450f0202d0100369041e4000010080c007619096009107040703e2007074500300f1880c180381c1c405644a004042280780140c114400800224400d074000407404013042d0301461900e541d40340020b042040002d2030248a0b55440010030650b1120035047c401003118000003a510101c5584804480d030b05404000c051200041c2041c1c40709552206454840b200050100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774965143 1250 774963893 774963907
    0x1020106030c0b0a0e12030702060a030204051012050c1e09060f070605060913021c05120a1d030601180911060315030705040c0909050c0c010c080108010f0c080601030203180102 78
    0x22603000c004002e02240170b0074100545070400c0aa14445601c031030001e1801c0c0840ca90820066601142c1c07408200740c0c080c0004070703082c0c2e9294600c40c0000f109450344802e0f00c000401c0c84066903002401d14400040520202a510500518803c14180c030888120b40c0e584000000034105c2c040e0260045a02c100801c8040410401307510850080504550080c41552103801c100d035004002c8070000d4000350600c00071070300c0300d0304064018002c034880e0054400642c044151591240c01481000d000200311030030b0102d02555860020400ca401600980032660600c04c0c0400191400d0b13500707203201950340d055a41800782c0400001440074000b8401070340c2e030400c515895001010700380620310a0084903000111840c20303208411840c20395850300c600d0f0328507006441c802020000c00d0469600810856803c15103000e200d069030018040c0c407480c6280d41445c404600319810260248551440c0a0308040d065400c00300943e4800800d03c2d016940342d40e2900155983c00c030642c1c7d501019130020581c6 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774966393 1250 774965143 774965159
    0x70203210a02120f071112240112020d1211030d0e010b0d0c090b0d05010e0f12030c04032003150115090e07030902152209020c060601050901020106030c 67
    0x40503010300d00c0d400c0f580e5000700c20b9110302652080304601040081d040207140e00051055a1280482e80020203020b103a000e18403c050401120310240416600e440a401031004841003c89000d0710020741d1181140c5441d5001c600e810301c803548054a2440040d0b03860f8190f038031600e09601d03000480f106490301c4a180e150503c1c09042c03d400c0400303ca5003840c1009400381000d0360b031030700640e070000f06043c286407901204030028510700e065560002901204040072a00c00d0281c4500312006500601c00c020b10048441c0c100751c008501410b203a5010410700030204c0b110000d8500789d80d0040b10410820807421b1070440c80170031446550341c240c003405074403030740844440341214129003200390401038400110b4011161214580030f140400c40c110030200390801c4c07099020050b01407010307040541c4401508d03c584540d81203c42c0e01c00d000704844020320030340245007202d18001e002e0460154141560200c0081d00c800004058a04010010440035441c1e03200350003000c021900440145003d40c0c42e5459 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774967643 1250 774966393 774966397
    0x5040804030512031905070e040b060f032d070e1c2102120a021c0c0206130302100e03062422060f0e150f100f030507020c0f0607020321 60
    0xb0074985c0c60b007158810b200e03d00403030064078403c0c01540e403460007489a1204000040c41031b46580c94214009200c07080c5403c0c201c8000714090b00303c0384103a04c2e031304017100740440060000882980c840c00894050040e00380c3c00050403c000681116502541410780038000440d00c1c3d41030b0b015105e83d0b1100518415541c0e00050040c508140c0e9007030b15171040f03804004091903c00c0d860480c0040c1c0c03041c1100142000c80c450003400c2c01300703245002904400581c00003816034104040418158070403034410002c600e821100c1c0321081080d810320070055980c004c000394980100030700c00d003445910b0140f08440d181c0c402d0b08500210000812506a00c030340042c923414107010b018401400603103401800b140d10b6802401d0042101c040000440c5141d07030744807000070500c2082880541000208030762820a6444072118220091542e583e001c0e000d19448000702515070184c001400e45d002150880c05a4a4076080c03007803083c0e419501d8a90b10345a900c042498250102c02c20a904603140342c0c025000101000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774968893 1250 774967643 774967651
    0x102161103010b030712080f0d09140601090501060503040803090703060509031312020607030f02100f0e060711060601050711030307030c030807021501051e030111031b040510030504080403051203 86
    0xc10030803a0103000c0c1542c0c0e85e90f40c06448400c400074141500011603000007030102c1c1040c81c402c68100b100002d200000d5809103071040350b0310f860b40200389540300b5040080758010184500c003070146503d00440900284070107032000e00701082c00030002d2004d8008004c0680103691000c0304100303910700840c80a860350400030510083c0710410000003400104490180c1c001e58008014501e401c030540da056800c41c03400140c910550158888041c00c00d4100d1240030780d65807210303401140c0e0142844407181040c500038642da050202c0e02001524070003000a03129408002801c1543e661242802d115039103e41c42e180460b8075100002d680410550300103a5501c500788691285501500c0d200400c1e0f071201d404211300004030018030010001d5250040c5444001e80f05440040b410151803000309003076036218002104070320b20000610040003c035214040410305009001400c4c94202800118100001c2071240201900c88011400b8040c1880480c0d0065512400311107004400d9860140710350001c035 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774970143 1250 774968893 774968899
    0xa020412080d02121807171509070803030112110103021c050c040b1306030501050d05191a070206060f04020405010e0f0a080a050d020d0306150f05040801150512030c03071401021611 80
    0x7500011f0b44850040f056960a01d40e00081c20481480100080c00110010310100440c40f4034040011000c00c2071009501030a06004014050002403c201d460f0b200740e50015410140b0400502c401180344080140308aa0b20010109094666021820391402190041041d134200020300d41451060240083c003114a1900c040c8035030381e0703941d0810201c003d0207800030707120350450344d96164104420074000181c20701c590341c01e0300e00d40412400f079924880102c0310600503030f10000c14003400340b901a41e01164000300705c40552a183c01c040c0028060300c7c40c408028081c101000407880c4664818020707001400020701102c40c0000e41c1c2c106170703940d04418030282000d40158049072008900c00e00564040e1246802c03040c07001c9443c031200b12004803842c04840f0800505102c08202c00c1403c0c000d600d40c0d0b0b00c00401404202d410402001094a42d02000c034005034010000c590180401000b0341d5411504043c2c01003c1140c0c4000d41342c00784c40fa4100c0b0040d0700c140b28111200b000340340300c0002d14600d015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774971393 1250 774970143 774970153
    0x60b0d0902150403021c15020c03070201080903040b0a081b0f0d0b0904020d02121509151e130302071a0d0f09080f090d0204050c070b0a020412080d021218 68
    0x403095140c0b184103a00010b5081050350340488100300d407011860840078807a100c004618020408118100d8001c0015030b03c26800000e501c1c0e05669200384000d400c441c2e0103014614161821000c032090f07124407100c86041c049500000b44011040c10681c41c0c0150020940990b1504042c0003054a5848107441070480740c50f02ca4000503908004003828807403a4090940010603800d0f408100c00510710100360384540c0f24208001c40a00340c10007109020b043c81c00010b0682541480301d81c18208002000344004a030552003480350b21481400070741d0081c0902942903c1c845080c00c04030305050098009105550101c0b62902e20109020010031040c192000c04003c1504a003d009081c1c54100324050000a014002c21910a01e20402400e11280050100d51207100e90740c0810140c1d18104c0d0f441000c00e0010a20070144503011000030750001031004110300c7d06007407064100e07007840490000780c03c0c000b02080c80803018141c0d60444044540038280d07202146051420f80d03a01725400017002c8522300034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774972643 1250 774971393 774971419
    0x201350f010308070b04050a060f0e0f030903100b0102030d1a0f01170106050a05071a01081c0903030503180f06060103060602010b0f090a0605100305101a09090703060b0d0902 77
    0x1003a4980c1a00d81c480d00c0c040c6090310541300ca612100000d00262010b0041c03800041c0016554419120107500190000c1003802010040c242080c65901d00c40c40e50ba041082000c603543e501041c0500a82011940000c485000b20300403031a6019422030300f42c100d898503880b07001000c0040f0904605410817518803410240c0c2100460725406620124103140b0300c18401404184c0c0544040c3c484c528491030898200b02c00350f2101042c00e02d04a200b450b1070155800148080c0206124440902d402240c2512862120f0407004192100e20310001e0104540403002c02c0703a026002541083e00182c5000715035115030710b41c0600ea1143c000b6202b0601207440e04400290b03650040c0101010540005e01043c1038000c41402c0c007030303484c074010180111141e4034000440c0c603940e2154030741d22010782994001111b15042c004002810040e030007041c449400440070101002400701100c06450301954914031580710603909401500c015005090303502ca02040401100f61a070b444020280d00884680c084005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774973893 1250 774972643 774972661
    0x60a09081b100807141b0105071e03020f12011e0e07020d0c0c080102160b1003150209010c0501110c01061a07140a021005090310050f060d020135 64
    0x318115000141c08461540c8640916a025070102c100d040c09603c1600c5c01403000366030352140da04050a4174208149001e141424480c00b41c1c00b0840d41400c140c00541100a040c1021001c00b000040580000e02010421403101c25107110212084512100f96125404030303034043e4110503801d01e0507444500c00950074501b007518038000e90300f5030041d280051b240711044520303199000b801d40f08080708950019a8900900c01441011841003010325100042c2c5440110f0060141c00f640d8500d03909902030010440300940703001c111080c4800166103510000058a41d03445011b40070f8819464200c041c00c513080210010010080001c000300512522002100100100c2912071401c1a005120140016001070002055010840d08444c061141c50b400108580b21400020001074030100d024202c90504000702001000603e4007071080d031030000c443c4031700310100501961050720301d690000196401040c000310054460702c09101c00740d42e20b02d41c20b070f0304c580308650341d48500c8002c0300003030b42800b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774975143 1250 774973893 774973933
    0x90405090c061914040b131202031005040f1a090c06070f030813062a0c03081f09020c1506090127060b07200307050a031b05060a0908 59
    0x402d101e003005040c00600b000540420811002c4c05150325215001030110300180006040e2445e40310303600c014803501040321529a9121080c1c04598003403a0340140c1d8086000b10285151200003c0c19139910304013112450041840a0000d0001041040075014584e0280b4480c0a5102c2241c15191201c030600809200b120300180c04219002404000248142e0003180c0247c0c1c000c600c40d00807101a25060308441c00140207080076035610800092004500422585600050500d030b4581402910040c0844400504401d0854080d50085292001184944007e4a2014802c54035961101c8100382d45015058800d013076114403400181175850041161fa040c3c814507201c00c0c0004030001c400309002d00c0342d01902c041458484c4c401189140039440a4107515004000c270300102d0002070030011380900c40c907144034041e4101802c00d0140761103400d41d072402c4903800b80c1c03e0782181422007150b03294413809410003940300c0307400211074507160790040014003a9003170242950840c0c41d2243d03010082d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774976393 1250 774975143 774975163
    0x306090c030330090206190201200c150a1104030c090f0c0f050f07061b120b1014070b0408030a0b010509010e0906030c0a090e060a0203060f061e0d0209040509 70
    0x8034085840e219100c2c050f0350481d00f0b81c00e00c060015414221407003c200e213018142129a40180c2d541d00c0090700c008525900c26542c0ba20382c000c41460074075404243c0303844850303281600c18202b280b080401c1c01012294000d650a00a800b6115142d907102d2600104103a141e00c9080c80050410480400700802c0744501200002240c0318446003440108041d11150070155110300f84000030301000010a0316400f540c26034046035841e03158540a09a03010f0040100d1040110180c1c0c83c14111504503203802845001511040c100550501c4480e1003684543c440c0d401c00800818008090008000b0890082c40c00f8a003101d000f07108604403440111a2070007a11039490028035803040d004041d040181c2c08a401140140030340350200900c0700490725400c0070b50b10091407150f45120805500c0814041e032500110382c02015840e504040c00041c1e0708102074401680700b420b000448101501c421a101c84c070b0401d001e030a02ea00d611030540f040c0e00075008200754602807424000042c08030032000c503042c00c0c1c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774977643 1250 774976393 774976457
    0x5060120012f03011e030209011202011707020714041b02060402030714220219080907060305040c0e10080a0303020d051e01170f0a0609060e060106080c130306090c0303 74
    0x8581c41c0240200c003004030150340003032044103172030040702503240d01400c0c601070517504281c00e07804030031840018100d150034654903140c10680300511450903400b003914001c0703a4080f141d0100b10303e00003001800405840c0090310318001f0030b80005a0030754010411500c518022002e80c0c808076500c210179801900078080e41c0380c0c4030440180240e6000324a84804000c80f485940050416808a2043c00c0c140708130020500401c0360b040801c1058841009844041c00080ca01800742d0306044c3c0e20550500e106024410030106074100003034a400c0c2460740d0038001d010004c220384d140d24136070a01500075070100d05d00c10101402e0038009010100701c10740642020b03441c40c0d170005a982c40d0603282c40d45520045800c4d000b50281c0280746000e05402c2003494181e900074000020b568039142340560031901440e854031503940044004000058100820551002c1da0106041e0f036102c00d40310004c10034080c0c0d00f009000b18945890700060000003d0401c0560344603403280080d04040f180a0001d0740e8bc041d440c032403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774978893 1250 774977643 774977647
    0x10615020304060504060f0c02090f0f061c2319030f0e060a0c1509081305240304110909010906110c0706050c030405040615020c0d120305060120012f 66
    0x14410740c04007c1401c01c0f840d10854551442d800105030800c20707230311308500300000c0c02403281c1d112400f082581c21036011a030041a01c118541503445071300e039505024100100554081e86038603002c031101e2076805903440586203500f440c242c412405565a000907000101c007180180403041c007880c480707402d0307020040105040910209086403803075516901200c54010100312100810102c3c011080058403d4074401d0f180c1c00c62101e040c010582c1540800e00c5020001410900380344c40307c000040d1040300c5038640303039255510f04140b0002c404003550150040034141c03c000301c0b58010740c422044144220010f1218180160043c1070394040e00d2210314068121401c208280c1340500b0007030600c0c100c1c040580e810907960344c0c0040c08644240c0d00c01c000031460900d00c140c5141d4140070742e0300d00d800102d40c0c038000c03003404d07807188030080c4a90040c450a1566440100350141e010302845610044002e00034030b0b00324514200311f806041e4915614891044229603540034810034002c4854000305060707128 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774980143 1250 774978893 774978899
    0xa0c05010b030d1d041b020c01020f120301061d09040f05010c0e090606071523100605030103060c02010e0f0d170f070305270120030f010314010b0909010615020304060504 75
    0x84d03454a9001d8a080d8000d54070b5500c0c0640c10107580600300c03405400e40103003c0791400400060b05203195485000385c00c0c1c0005102084118a003000c2d079054809514201100c0d84c1c200b071031200d459040d0441154080c500a0030803041010020540100364440c2c0001d2118080184041e0f0b03000030303e01034055000012500182d003e0a043d07010b0725449010b01303411008401589030b15011100390003941060030410320502200480015112a040b0380c480a01c0c004552620b68000e100c1d00040c00001c041a07140e02d600c0041d42d200750403c5034200364407010348034442c4441d910503954480d840890300204860310701c4000716014048202d8400c0001409142070f40c0e0312144101e0043c00010003a51717075004d031000f0802c10214081d10315104000c2d1403000080c6129249900d484003035900c414001032500400402120107840c038401c50440390b0103e03009407036445c3d60500a01421415500d142c2000110302000440f00c07054001c541160306c58105880c04440400c3c04036100c0c410740c0552004203504100070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774981393 1250 774980143 774980177
    0xe090c0f040b09090703120516170c03161203140408070f050703030f0207090207050c040c02120f0310080303091e1e0d110c01230f0a0c05010b030d 65
    0x1805401034010000101c040355000058481a8182e51031050b5502c028003d00401096070818a045441d500b842c50406421042010500c4060403004007540c0340910403041c1c004841c801d96000500010580342c030f5140c525a42c044040c5180c0d0252038140d400920105214001d11440c80f00440100184010b030303445480b0f010729680f0082048983c42e1079101c034540410f03c20710800000d50300c20b981d080342028481400074544440c3c0d4008910483c410800000000d0b8005a2640341500a0f030b8041403004c3e50324070a85c103151070241b00f2030b05170b04002580c51005243c0c0d4011032040da0b1517200314502c1a2140d0b20703251759000c201e802c60940e5110480c1f01d450f104001c06e5a23011074060b60222030302c000745201e07520310b11204020602a198800101990059004141c981502400030014400d80070140c0008240501290702d81d41540000080d0b081a1440c45040311047c2080080d110381d1551006070042145001130030544055107800c00a0709645004203c51f0f080303140903561401d4002e548001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774982643 1250 774981393 774981409
    0x503030901030203040203030426240f040c2105010e06010b040e0c0903010c03020327070b0d1b0f020d08010e0a02090d0b040c150c05100902060408010e010203040303060e090c 77
    0x8140d90508c0705000000b068404140c5140503680100c0c2491007180c240c020061602801201d45020000106602c14081540d10181c60b8025124070703201034961600d0820490661580d040401c0401c07040c1c550108000542d1040100301f842080200305440d83c5418080c1c03074003002e00a2041150301084100481ba001d460021741015810f07500500d0700712000700203030840c1d020001c10404240c000c003c00500810b803050003444290713942c1c0c910030414044051301d5140c0b4024001c2c1d03030940802040e100f100071415804002d07075440500d5000e100b10a0a0340140410240c841e10000500c1003d4010000b180b00d590030718129109044500f0440c0ca0b09480c08010f904031094041e0030a440d0369501c2d01045480a40340e008501403c5140310301c038205000342d4101d03d1003199070710600c141090100b00154000604850006010f0070000c1d460f0307228800606144078a40c01a02d1a44c00c0000a241250041d802140514132a46040000b180d0b5041050103008003101c240a4a40180100707424070300700703404 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774983893 1250 774982643 774982651
    0x17090a0f08120a0609060527090f0a0f0b011a07020d1514010806071106130c12080c0601060c030f030507031104060309140a0209041202030f040801020c011103010503030901030203 79
    0x20207400e200008085200341001100e615910f241c0702c000070031a14280b4410b400181505946040304080250040f00c10584c03640b41040d0116800790005801c0c010130711240002c20403000a44000e44001d041c2520003048000058800e84034070710001444040564850005070704068201d414049141c08200c2c1c02c898140c1d080c2c03000148298400040d5202e48103114010103200700b40b80306035040c001e40c3c51a054009110b07809100d08403011044c000e40000340aa40328486550002e0320280610307080d403c140140c0d0003038400f0300755402c82c070040001030b0010780110002c0381b0464045a903600402c031000c159a4201402080550f915040c0241c0719070003580e80242c0c03604010959240383c00c600300c956445070b8000b00001c1d03035540c08030b42001000154815504c6520008066040c40e0381c000920a51000d00006c0c01c050148010450a60082c400d0f10211141541101d0f10707580e40304d0a0f0b81c00307980700c121118015403a01c019605040d00010aa9050342c00140046080241841c0190000d51000d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774985143 1250 774983893 774983903
    0x30912051501060c05063106060b1b010c17071215090b0f0f0a15021504060605012309010f03020d15180b01050a0c031205010308090117090a0f 63
    0x300d101d8407040780344a5850080c402980c40000c914020300340541402c0e4050002d54010510010908600400d2011041c0d218989001041c0c2403445240000052550b9800b00b076044d80042418882d448058098002002480000348a0f903000d00038112180c1500c04c00d000d941031080c0c1d01140006104504146421500c2070303000480c210700c0c4010f1440202140e02c060b820a4031143c100c046810b0186559039048000e40b42e496070f908800b000600c1b100c03c580190180310210445103101d8038400c000c0c0f00c2680060174855a000d04040c10554054000c42c0240c0e0b000c5910842c41e002e03d06420314009907a446040426401e0101c0300004444000c19142d0b808109902403103420084451480f40c10407040d0482514040e15240c0044146008202146070302d0452524509007a075917001412903003848903600d010031000880e4070b81582c00468004555107418517001c00401080307542c2004009900098840429000402d0307e50109407004981210b070b0b58110807054800900c4120082d88020700c60 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774986393 1250 774985143 774985153
    0xb090c0c100c0e12010c02031c09021504090c0810050913080f1e0a0f0e030c0307081e0a0c030602070303020d05040f03321303080c06010504150b030f0405100212060f0a0303091205 79
    0x140c2c00133170000c03181c0d2012410082c40000d04020880151090b5200700c000b50410b100940fa140007030440c810554420580281c80a01c00503039844251140e02100a03448036656440b4000e20380941c2c0541c100440030f0484a007084c41c0e0b0341541c5214803e940c0d042800b40c1e103058640400d44c070112307502085420790903090301c10440b41070a150341c14801c076405132200800400b400300c00c41303c504107522002c0d0000422908240120404a5201952a0243d982140001daa11180740c40e04400074840c0800d41c01e2480d10b82014401042924034502d0785483c0681d40e04a101851280009082000c8000d2191402c084007580050485030001400c0702c0c0c1c039800d840200f150340e29211840598844030010155400000040c80203250505c07611007841e040d841200080c0b4101113030410640b00150048003071150000008041080030441a42c20003054a015915030300a102d03040c2114006035012445000303c070052070450308206d951074003180c0e01340d65001c1d00e6520382880503070b02c40c100040a446901807 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774987643 1250 774986393 774986411
    0x1f0b0f01050403200a1706160801050108010b0c0c06070503270a18020d06080a030f03060311040b121204052d0d060212160201050a0b090c0c100c0e12010c02031c 71
    0x1641b0391020b821004a0080c00c024034129104a400403410110038050048010050101c0e0f60700c0341d105c03410745500550aa58410814005a141445051015a2000d00002c14100b0004044040c041f02020804100d10030b10310b581c244541d06020901c90f5801101d030310000c109220305242444480041c8070401841d207480c002020043e00c0d821341200708290b00c18510072040552040c0941041c3c00d652804004080c215501e184071007280d9a2640d100e079490707400d818090366481e94203808126412040300e1900d0055485440740750040e12503613108210128003541802103c03041e071000e580480c2284000e050011042044210313103603c09888459080c802c00c0416a810341c1428003d00074160120b652490403540203080d10342c000c0c0b490580c0b9041004201040d101c1500c0c032a00588090411741d180c440e80100311b4a445954001c1e200d00c2424207218468468011814540d01441900c1c41d42c42c014640e46449e003a81d55a0606000583c000c0151522002107075003d611110980080071490300a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774988893 1250 774987643 774987659
    0x50d090c09090804051203070f0f1406160e0a0524070b13020f030f060105060d021201090e1c0903060203060607140d0306090b030a060207051f0b0f01050403200a 71
    0x41e1003141200c000c03c0006080c0b2140c86c1815401c4c0300448900011131900281e5a280c45030040e85440080042c1d40c941c1c0d202d0200034034001015586810f840c1114102e1a0104100240711001720648001c122035005d686400d082105140041d44e002030403c44202d1304060102e40c0b000b141c0110590055400d100c580000782101102d07602030810f51031030710740100082c01084010740e030341d0700c0c0140f00764070680c3c0220342d448000c20b106044400c1195030039121103061184070040c1c826011310340d00d02042e040006c240b41032180e00040780345107070074101d4075400c2d916001d910354494002080400300e05c032003d0410000d0960b400641e40824060441c7c0d0420005607510084030004800222042c2c001d50346a40c190313a890f200302b000070240c00c8024010440c2480c082600c4a41d0410054003e903000960b40082c46420414007142254903540030300141c4034404082c00522504200382c2c40760008900079803180d07115805541c00d1300c2e0403146418031000019a154030010f130580003250004104803000640507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774990143 1250 774988893 774988901
    0x8130803070305030f010e011d090f0d1d042307020102040f08060f0c0421020301060302090103030513080102030f01120f1e050c040504050319110303250c03050d090c09 74
    0x28840c0e203d03540c4030700b0607031360312100703504160031030480151610f004004110f44488106916064141c0801c2c0175211004000d007401c8614009000901c81c0601d03e01c4480d92151310031911452202c202e000c0d64842c4000c21003616040000c84082c40f690040c104850310b05201416013100440c0001403034a0740e90610441c5021450b8800b0407941c014108106161a49451a42c2d0180c52100c078603242504040d1003243c081050070854404030008071403103045480c00d52007080a91f4004142030815a500d10f03004141d079000c442c11000200000500085461050003a80c2c0200fa5801410245a00700394418866a1700b80e48162125070310180703040d002c102c10030301800620b04032048803081e040e11800c00500d410b0b034058546020394580020003011079400b1050340c224450322540309140d181001d100300c0c2c0c0b0001500810400b030000100740000d15400715001262500700b0201854400c035020010780707110b02041d40260228200304600500c0d5001c6a000d100c44901c40c200038006107407140b203e46c040b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774991393 1250 774990143 774990157
    0x201060806041128090c020f1c031a060d1d03040e040f0213050705040603060f052121070c060305040f081b1905061006050d02090d060e01060e06030304030c0308130803 74
    0x1c00d51b80c40e1313800441d03581442407082c4225090f00420200000c01c4107400d2100e000f050305c0f410190780d103041c028408406074007180c01c4503000b44202e1315541450000c0c0700411080e0030b88215029000740c9050310102c04011341d1704903840d05d80c0303090440d610350300d45a03401004000101d0b403200440310251840070711841240c0c09a81d1560b100b1340c1741d60501601a08854080e0030110031104040b00800c1945d0300d00e401031010a4801c60465184140f4117075407841c2200c600c900e020704402a051419180d0080409000050301035047c0c1703080503503101801d904507a8284c40180940c0d58644101002c00d54100007400d0803030070799401d0400c080d41c10901c6802c002d4191a00d41c1100c0025101c40c060150030070a560b00900032120800e80740d4035000b03021307003a0705c100300800040c1c070303000b080d42030380d40d680c0c00e10500045400c107030180003804195070221300030300440c0078400381d511440340850700700d080c00825101525031045c00d011040e42540c59001c00f81e004240ea0207002d4118820108070a0300a1020b0142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774992643 1250 774991393 774991409
    0x8032a2a1f11071a0c0f0a050102090a0905041e14010e060f0708070f0c080702090f04060f02030108030a03021e0412050d022109030703021c030201060806041128 71
    0x400803030300c40c000302510644900341c00c540d40080b105000944040f4021191000c0d0188455511a0f007030710340505000c3e0f10400140721b4011f07040e0302414031006400030030420710105c030f00b400041d4031110940c0c21610140d8001e00b000008100700100312203615500702216004a00c4500c410440318501d60035105900d84400700c82d0008418842d1924200c81500e0304403007941004032952900130701c01000c1d01d01039030341d94041006440c00181480682e40c102e520b00c41d00500048598500396808403a00d45060700c0c101c41c01860100001d40502d03840c401e0780e042c0e0b444140654544480e00c401280039402682241400c1c20001d00c5003801041041c005000070030040c2c0c40f6085024040c1031041c140040c0035142c105541010304940101e0381e40000e4402c0c8844228503e076242d05e682400b04e4549402030304000d4101c407540d81c0c616640c0c085000c10920841c882d1f0b0007444840d458209040c0c40d01019280142260580d001c40e800394588120101040c60b0442c6004445c0d00e8070140f1352801c05d0b03569200d464 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774993893 1250 774992643 774992689
    0xb090f0a06020d14040509040201121e0603031106010b220f09330603020703030b0312250c0e1b030c090108070503190b0f04020408032a2a 61
    0x1000035040304040c013203d950701c0e056604091500d000301740b40e280004c000070304000454440407801480c56000440c04c10300040340d8508042c0502000300100124082030380840d80c4030b00c41d04520040065041d041c2c0b420540101e0820756104000f00c01403004030310454110300d403048003180072600d42040c100102064000481d00300c0503c03204030383c0c90070303402c000101458178103100d0404107040302e807071204481003850b0060b503d10032420b048004040d0303c41655458050f501c18143d02c40b90542c0604402c1c02c0c1c50448080b1010349011a0006801c1144004c0500400013410407030b0340420b6040380e52000c03000403a02d544554a040904540c0e0085840d0680c2c02c1000c16280b6032941d20014959001500d4140306155003001154402c895008203c810702c03164403801050078071748034501c1720f00030841c0146c415921507486402c3e9030340b2900480c2600504818100120306a070f04400c842c403c80260f044050455881400e420307660000d000c4241c40b0b460403a042c41d400f100d480703400700e2591508000c12070702 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774995143 1250 774993893 774993913
    0x5090a200a05090f0d0b0f0f0c0c0c10050c03040608100f080a151d01050a0e0606010c080309030403020d05010507080a0507020d0e0d0f050f21040b090f0a0602 70
    0xc40300001a400e04040a402400310440d00c60300501140d25011048640452041c40d1200252008800c040000e1040204009002c0c105803400b0056000c0c450400f845402980c43c40c1c0e00c0307012809802c02c03007041e0b0707403096984403035500386540007002d0402140f821a02d403a400c0f02a082c9546e11a0b40400005880303402000200481044400b01505484005d20183e80c43c240601e60b40347c90303150f0301a1101490502966102589070300030488840c0e0082500820320704642a14000d2208494038107009090061900d038825020811030b108420584515003000c109840300d80660f000107000541d81e200420012025070743d4400c40c45000c921410002c102403600305401841030f24003401c0f5440050801c81800025a00820303801c02c811890f20f07241518580c548002000b406c00d040019201e030f1808026941440b9021904464007030700c0c8411504a50042030442c80b214141c0482115000014442403100801301c40040941c2000200001c0344105104002072074030750a6846034015138003a01d103035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774996393 1250 774995143 774995171
    0x114010f0e0106200f0714030f0f12030703020418091a062b2913030816051b0f0123130311060403020705280e1005090a 53
    0x100007030500551407044551502201600002116203000c6601e80044485a21000100200ca450b1080030045414260355a0400000710264148040c00390085046180062a0015081c03e0140d8584010001100c000c0c09040352500040d20410425400300400200302801c200600301801d0341c810009965a214074140ba040c2800741080d55144000303008001c01d650751040034007d09020a843c12004048640142d204c04540701c0b8010a001c2c040d40d0001c1c03500846201819115400441031515911242002c3c0c03000100804018009505400003641d500e44409414148240c0d605056003403a0300758101c1070103201c40c840c1d41c0850340c6c045c02a0b00700d0040c090140105025500031041869110303895244808000100100c401c0400b1580c04020144207001b40a14000c4034802d4401c203003410b240094a861031071068030302c9594941e0030142e980782443c502d030049403000700b031802d4243e1a00d1400702510744000c0240c2d01c5000070000018007620b81c16000d81c0300c1c4605450001d4600d10f13650503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774997643 1250 774996393 774996419
    0x30702010e190815070e03060402010509040b04020301140406080318010320120f06100203090d0c031403040305071a0304060e1f020d0606030207020102060c1c1802330304020a08011401 81
    0x11031070800c41079203041c11b0b41d5180410159006502032034941da46005603000301e00038011200341103800a03c00000041c1845501c05450741401c4115814040e1640d104141541c0f030003500301e030500e40c041d040c504018035070182d4400c40314403044020815548070702c00d031031a029400c103054600302d2080c801d04200242109440d010344c49030084441c000c454100510081d940e0242044480c002c0e1110032201080c486419240c200440d0301c828000f51040c48095440e460350000d2104071780c181324251020401c054081c05d10b800b001031100300380d421695541c468501410941c00c800f0024042c51402c4034800c2282c0d42d286900c031a2084000d65200603000000e03089540f0741d8441410507206201d0303440142c2c2d0118810340c0298600701d506440e002450b9030700c045032490645444c2c84c07070301e0111031090212003441411500b034001c4070340318004664160b42200d4011541c0440700741069070000c880c80d21000c9005107402600280029220b940c840180350b00711840302d01c2c1c4d01002c0081c2e10041022440c0091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774998893 1250 774997643 774997651
    0x6020d05010e0c0a05030a1d0a0c09110d09020117070c03080f010506190302130e071704110114070b011202031911010e1f120f05010305030702010e190815 68
    0x11400034510f09892030307103140e0080795800c00c20040d000021501402c802c2d000001100241c4c504401241a00c02c6141c0c0c0d950040c0c5000c0310028002d0ba4002200c0f001881072464000d0740c1490303541b4200420200c04001d00300514228140401c004001c0b83c81004404400d21898050303c1d1158010410306015007100401808250040003d4005104544490007911360031000c820740716494481c0380340c3c16000380c01001ca1444803040300ca02c0015600326681d40441c0180c2c100c0c0c0f184000b1814030307c03902c040e00d4021280a8590300d030100603003005501c2a40002c2e1703114a07440c00325007800542d42e6200403044c82a82300c1e0356041d20301800c0300c0039403400748030903268500c03116540d0a4142c815512088914003c02840341400110404103d00751140340f02c00000c02100072800104908a00c0042e20b41c80070b0301010380416292115400c68040c1c644106070580350044020b41c00c00c0340550044600030001080c01340c00c0240000020300f00e101d0280400c0140941c071028044c46018203250032407a100c018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775000000 1107 774998893 774998909
    0xe040606030606060309110118050916090b0711010f1205090d0e030a0b0115051309020a0e2b050124050a0617010e040f020d06020d0501 60
    0x240d00c100252849858104079007500e41004030202c0312050390041141c00c580c803d05900d5030040c0c619200d01401c50f4114080e81c0c2d180c4021a87d007900984040c10b440a020307403400b0174039402c050380304090b2601e241c00c1030600d01a034a83c40428030301044242d05018032a808a50518440e11414410380085001030015041018100e9a00c0011104140004a821000c41c103685400b1420b07000c4135402400d044950790911185040c25501c3d003d1540600801300f00e40c201e8074be03000e0351110040c6160300c0b0050325000e4910000e402c00300c2180d4030320f2081500099000e040803219210350341000381c514101380c2030f00741032800340c0c0186203904070355904041e019001423401040ca441601a1101178400d11609aa681029101c2d60064294205402c030307180010f100748100010450f50042c090718010740142c446d42c000c100c0d10a412403090307501540000d40315010103058042c25004024074 = true := by decide +kernel

theorem cover : BRFrame.Cov 774820143 775000000 := by
  have h0 := BRFrame.cov_init 774820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 774820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 774820143 ≤ n) (h2 : n < 775000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
