-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:22.231023+00:00
-- url     : https://prove2.me/submissions/be764d54-1bbf-4de8-a651-6a13fabbc3c6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 735251798 ≤ n < 735431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 735253048 1250 735251798 735251813
    0x312110a0309051608030f07021804030f021009080a120f021b10200307030f021b06060909071802041e030b010f0503060711150403020708120f0301050609120613 71
    0xb103818100c04d0001c0310045c060320102205440c5401039000b4071300d0b1218100e00016050142c103810103002060400244002d06600026080c6800d04540840758000080d00c0d850302103c0c5103400c084c1100d481801081c2d1a144500d00d4003d14051001f07001c1120010b80340442c040f6844200c0401c105607014243c09071850061228102c424200002007040414a048808101212003240c540c2e860f07000000541841c000c0e44240d269402a110840d1501e02007045107218410002c10f1700030740e01c5808000b46061809600540c1306d01e500c080a801c40514244503000320244428008034a27503003c0c4400301c1d0018070f544d0b003c440080d00b44a2100c5140c99410948404541030b04a21504402e0550a0100c1e031000101d170354202c8018034081004c000c00c1d02519043c0350010015040c0c4004450500c028160b00194100c2540c9042c1c0540d07400040e00601102c4500c01e40c00b43d10410142440100043d150440c040c010800c8054000c00348030303841e1910759040000481b4200e2400020307042e04030034007080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 735254298 1250 735253048 735253063
    0x3120306010f021c03020a1748030702011d10050c0a05040b0706090b0a0902150711040e0f060907060315050d020d06020c01140405010b0a03020109030312110a030905 73
    0xba03001500c00801c01060800048084000250500da000100404120720880d0020124684900340e8105800d00000c80b40d08000d0b5040f42103402540f603411120314021000d140359070025039071100030203e030103900c890006802c000d105006555860702c1c10071004400ca40300f68280c850690282c284034030b05481000c02c0341d4010b0210036030340b0801d0014114007a001402c40d800e032003202081ca91540040d15084028252800006000381140070500c981701c15241c2004030b03524400c50325402c118101d440d5104081c011080f0240c070740561548800003c1c03c1650061507644010400d8801e544407e05440380790400c143d94014456000c003004004050341071141200c18010324082440c280d1030130001605040c4800400707403107450107483c941d080144682c103c510504d14003000340202043d2552000300120b0446040d6140e5007032941507075047c5000754a08040da68140c490320000d50541e03e0407685240c0301b51411500c9580c80c18820000d15580d00500685250741d503000c1140c55251400782d040005 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 735255548 1250 735254298 735254327
    0x1a2502191e080a051f0b041806050114011202031008010504080c0705090403121a030708070501090f0323010b03060114011e05041238090708100e0c0312030601 70
    0x143c99040000342d408100409a80d221881c2181461403041091005022100c034417548180740454500c000c1d1403e4101514041c0203060401c010ba03a601c4081100c50800c28060f40090b1040d101e90318582015405181c200300703180c91104030f46032105503203802c480c02900c1c15246d9140100d8640303618482005444080c201c02e03900502e4904081c3e501030060051203044040554680b9403201c1044104095103006e054001c04031100c141e40c03009642d131141024003c07180040c031039034800304180e00b0000d0110112640070180c4112210000e07507400862049241c0c86071555282c1c0c48842d801e0f03800f0070071070f40a00403403c45040c441181a00140015050081540c1c1c0342d007081c10184205070b0080c00380c80455010340a01020690340340f4080d8502d001620011104e1300121120b0704210aa02c503480e02103840002460b140e03921817050081e6501c8080c8aaa11541d0008500001d420100d42102c0c1115846100f03d4508410030400a0300306111081e203204426008410440290b034401c421000d03105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 735256798 1250 735255548 735255553
    0x9040809030613080d090f052a1c0605040503041205030a0e090402012010060b03010905060105120103170d0c020109020306060d0209060d030203040806101a2502191e08 74
    0x110b595445008600417001c0d510000e42d1b0340c0301d400c018440d050b640c0c141c500d90700c0300a4401c1180049007510f211880c0f4003100751002d542401450050812049582801290441808616403150b9541c03014020041c4200d0341400180400600001244050540e8511440195450300242040200178559a0114600c0340a25405000160b41c228021400c40400192242d130300380d0f610100c1e1031900c103540c5204608030389000000030320b81103842c0c09107051b142844003d203ea03403201001101c0a011311040300c0a81c040120041002030746801006d4038501d8010314076070a140ca189140c00444030410301440150751148042c0c070031803400b4008582d000d401110441d001c0541e40c0c001c60f4000100400041c0120311030204075040c54001c00c1078034000c011000c200e0328140340240c8415500c500307510600202200010b1003103182400c020a44441803203440c6d507600505902d414006981060a00580c1c211f80c004002c242e04500c0c07000301102411480c50b10300307204c031001003481032800c5d02c40d40412070703d8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 735258048 1250 735256798 735256831
    0x303080708070c12210b030c013006050a06020c04050a05010b040e0c09060a1e052119020a0c0c0e060a030807030513060804140715120b090408090306 66
    0x240c000f9110142c294003e960303070a01007080501035840483c1409141c0300d06214001c880c50364016a0003186000005400740d409001c2054010f503902203142401c076101340c00000c40340340203160150419075203c0c019179000c03a08640d03d401040e0f00003159080580180c1041c80325504504050203003940124140c9410401580340c40ca18000c2806540600c0301409090380200303100111030360945001d5800103180d10703900c4482040281643d03000c80c041704a580c1c600314071545c0a41c002e84c240c82d42e240404019440f0030003452107417140b0010080079040011481c0005c2c0b0201c09041c07000d0002140a9140c640c40000070f814002084522540a9201c1f200c8446c1040250388841c1140d000701c942c02100d894a4603c9443e003614140100100145c4036401c01c200007800c01c0d8056851070084e4050f06050260013981501140c03541c4541c0240034103a07041d510011011031140c42101801031580800103420500400018612001503034103aaa0800200e980c00861a047c442c0381d07000340c10300f130152900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 735259298 1250 735258048 735258061
    0x5070c0e0c04030b060d030219020f0a15110c0108040b130b010801021b0102130504110409021c0c080f180a08120406060e01060e06130b030f10063e06010b040303080708 74
    0x701d0034001c01183c20084040c500d00115100c8bd0407aa8030401e004010308040c5444000500c5c40e02da5020103000060940300c1c04499413800030607003803040801a9140211544d41ea1145104280c0c040c0c06860703c1a2000003041c00724a031100349901034425100056034401c00641c10030703080c54228510308900d034410802c0025000c091640f00c0300300d48040e240400c0151803d4202103090040d80e2100c400e1500010300f49442d00d078003185d4186c0c181c1e140001080791a0703008000b2103a045085540c045c010b0701c1a400701d230301c0300b00745110030001c158100c0444200c00c1c0f0030b98603c01c079900071034004130154090f10140410840075008500c003624002c90505015072411600400501410742d10600583d0300003000500840340c05044800380c82c4600c0039aa90b4180344040c941c0301c881c100c0d00303e42c040250010215010344034903920030040240c1e03180000301c50700404d2403500c88142d54030484506003c0c141c1c052008a8244142402440541065500c40740385090240898000421860170084c62030200400b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 735260548 1250 735259298 735259303
    0xf0513030b060402190302031905040b04020d020f0a0f05030f1501140102071a071b08030405011202040911030106020d0e010c030f030e1e1c0f05070c0e0c04030b060d0302 75
    0x803a500000c031a4203545030790300850024421140000c450f1020001070b800755a805800450190701c100c501c0b14410944088a8801c6480c241c50040020400401280251501850444140d03000a0070359002c1d0385031400144d0924002d42c444a9282500c070380c1081145400e1143c10440159807000d41440901c5080d284841003050040c0b03010b42030302d03800d2400345e43d100f08070010103002160450541035110011a0a95030810744040b00c003191114145c4101d4106422070b041101d03000303001035041c1030800c0010343e00810320707903400151503030300740b0002420b600240a20580a4400c05000d952541021070085c00c0c002e001709610284201c04013210400c5c2d0307100520318a55501407502008040c17412508030083d0000c5003812000b031040c401583c8052070342d039485c084600146030885a4080c40e8800e03524411940e1190000031601c141540b4860f075010b0801408050300c02d504000155450385010980d424054841030100100498188200318a861180d0340102003221180307110002942c00a5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 735261798 1250 735260548 735260587
    0x6090c0206043005030f0a0c0509041d061005031207051b040f0c11071a0301060c021c110109060e0a0312090819020a06050301031a0402011202030907060f05 69
    0x346015212801a01c00d282c20310f007120404500311020900c0c420092070014800d400917600b000740f0f00c4440e404180700f18a00d1188804214081c1c903078a00b05142441040700070103042512028601d0702c0c2440c14101081800210b2283c029214800500c074141070501d4a00088050303d981003420030013a00c404a04006106180090440ba0580c655003500b40406e000d49510b0116006042c10700604540c81500000b00000d0302c46c0040c01c9820b0b090740d40548071814080007159190902d400c1006110701403140081486050003d4003ea100c1605400991303440b0341c0d42041510140b86109030800f640d80c1c01044640280428602a121480000b0008140b00300c42d210085c5000c064109401c04580205003c00092052006841c90743e01e800203441c4980d0101142244038000e8504041403180c051000da90603070343c000014503805c011031803901030043d601030016410300c85400903c1d944202140025482940b458001c4c0114901d0950050400b02c0c510708110b0030b0102c01e0011840045c4950320b20f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 735263048 1250 735261798 735261803
    0x9050703050615192603070303090209070314010504050423031c0207030503240301180c06090b030a0c030213170c010e101206050303040609080d08010311090403171302010306090c020604 82
    0x20301541548005e110300d410b0349000c50403032074000411f0040c281034140d80070840b4a4000d40d042c3c034803a900c501049040714582c071702d07003482c003d20000140514145644625406449030a0039210380b401c0782c004441d00364511a540340d05500000e450200c2d5004161506880101c4c20000d6040454954026100d07000003007c0d4400d15429041000e08620501486d20391000702074000c1044690164912102080240003551000018400090114031408040040300ca01382902d5095440b010f20a1000d0030f0500c003985d0415400f480480280d00c0405090401803074408185c5124107001068107041941005426061000c41b0103001c1c800d07111041c8841200303600c2c1c54007003560f140580902e070040ca4560400303034251201040101e0710384d400c09a40c0c0b0a0b81c5041085802443c03e107102190302d41000d0000170301110010780c40a22070304041d03055982180c440c0c1050480c2003c010024800c200c802c540c00b00f6a41803030b0a00d01305550301803081e18060094190148042850313504003950398600503100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 735264298 1250 735263048 735263069
    0x10b0a03030302031906090603031103030f0112210e120703020f01030f020f1b0f0610030201030c110a2f0a03082505010209040c021c03020a030905070305061519 71
    0x91700c00c42554142540400f000581080502c1c0c5411419000303010381c3c0011004500d240c071110b4611080002030300d03c5543d6540e80003107181c7c00c000f402d40a0740c0341120b044070054040450b0301c8403218207156102124007155668a00d07000a50208020f8451825121000d50405003041c0b001d2385a19540e1000c80a0070b0030041200b00c00d40c240c2070700a01c07954032144e0040f0008120b40c004580403e1285507a02960320490b4404196488046e03200e40e4180c0e200ea81c000c181100420065000790407000d5100c0881c2008010311501081507030070300d102e0031001c4615126060482c6155050400010711a19040e280c1d01c0e40c4040400219203c000c0b00c2c040540b00100104d0741078000d00c1030105224482c004000103003070b0f41009141880c040e4200302d034414411401c00c0031b442c0c50300e0b00c00180816986004030301c1c2c0b001d080d03203200280d000707502a03a8004100b6450352404000314104021200055228000411181c6402c0c101400d442e4958800c0c84d00c120084400000f070620744500301c000755582ca021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 735265548 1250 735264298 735264301
    0xc140906090a09060521100b0103060509160201061502060a0b061c020c0705060309030304020d030908031b070611150a140405061005040c020729040e0108010e010b0a0303030203 78
    0x3518901801d02000c0d441402c074403020691451541025044890a03102c0b80c01c2d4020314001030b110203070124072003c21940200754254440805401144c0d101006050000310641c603072011900540c0c00709d840c2d080b0f82c030410305a0b0b2600c503030901c201401007216003154800c3c555008030094407100007812180d405500c500444e00b803603990300e044666100d5001584201c1100200c00640030b900001d0004a1901501c42c0005082c204841128450550301e40a0f43c5580e855500b00318250402520035010082c1c2d0000c04220040108010203d610001c14800c0004549121683c5401466040042005200f0805644450000a4030f003814441c1c60100d00781540d80c81640703001080044103c0c0c4030940b584041c8030520401150b02c501aa01600100d0700741d41d01c4030b0030721080d16074600c1e81000581c0000c00030080381845800504080d508840491034880c0551185800c64120350001d01ca5034503a03000422204000744224802c407031035113000b0303c0071071107144c0000c181000d9440f001e410300d42c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 735266798 1250 735265548 735265567
    0x120e0d080a020f04080a1b030b0a090f0611070b160c021e030a0602040524040521010228210b4204030809240c1501090c14 54
    0x70150f51100000800b521385656840788010b903542d01c20035054442d0b59044150b00303401c00341000c0b03000541c4d410481040072509c074040541c0c010520a00255400c03a1122548000500c05003c0d0304a2540d5401106440da0300c142020205018060001480514165005031607250091031144030250101c540c8500b0881c040094590900d44000c41030b418000c115a190420400c0c0d4003070302c2030703403802e481e002441407840403d11101c656150691600c4c48081c402003001e13142010841000c500300c09540100050b00b00011400c2e42c0200b451030703661004602e540350203184140040840600946040e55030440c03941c1001c186540d16800c1c4004031621014000929241d003841a180074080d203906d040c10054031190120024244403c8030014100ea001e4001e07051002015981034a07042070000d03141488100c01c011900c80005691050b09800a20443d41e42a0304005000b1200f010340251507146200f440803075000c04140c0020307150500d0100c0000c40a6407202103e8002d400084142d0341d20701c07260 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735268048 1250 735266798 735266801
    0xa14030d05010608011a0c101104080a061409061b0a0e0d1202070807031e02010c080c010903090b0c060708040c05030d02012405060706050a2307120e0d080a 69
    0x211410022982030200014000d41d011889034100c9106c6080798091140c0d80c2841c1a8500c01c41d215088268407074071030b2848804140d84010540c001400c50245410f0351005418245150740d02d040d64120744d1801051040d00c1c5011100da0b12064120140c030141c6010075400300030314104610504103080109150400728000c840e40c1c1c61840004040c0703401c0380618903104000f07003100c000600c0140500c100000d0352000000e0a182500e034030184940f0070480750f0f10450141651900c050b41000383c1c80507142d01145e20040240051f496400c008a480c0c845800c0213040038940e0b500c101d60381c2e50308102c09540f1020110325150072240d42e20340441075481e02e0418910000381e0b50007503a4140a420040040190158002080c9000c82ca0482001c4011500303050f5045107107224071500700c0420445800010140c0c1c0c001e65010f0981d9000185611001c0c0000d803610420710100c0d80b8254001c01800301641e0041004400c500c0402c0f0b0511104940980040e2205482d96611042c000070101040c81200719 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 735269298 1250 735268048 735268057
    0x3020d06030b0108060411220906200a11070501080c090a080f10110304050307031b1209050306060d0c120212100b01090b031b0703022a01110307050a1403 68
    0x80202002d865842c0d0b406103469410598003110b80352200030195105081900940348595140c441003203110407040803003400703000501c0c4101d8105580720100801c1c20121038014085100e050070076a103881038a0000703400c51042000211060b17000e0001004240c3e0b00922141d0702c2041e40a40c0c075210829100440d40110b0140c02a000321700582004120162001848055560b42001c0500c5101c1c2d010003402080d210907500a005a04104101e5000c64040d00c0385030101f4010300b059104074019515a003880380307000900d54000544454007000246810003000381c110b2002c0b6507505141c1041d699030f041a000c1803282150210a01c83c044083d0b5841300c49503440300708814250b03400c50310024603031801040c00810081c04607e100c1e202150000c01403040d01c3c401c010040c1d980c0100c0b48500718500c0ca6800000c0200e04512440f84c10654110642500c480d55110b400e0912203218541d03400541000094400704230079074002d0191130041480044e9111071181c02c0704008505d8001800400e08505c0f4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 735270548 1250 735269298 735269303
    0x5130b090109020316030905060610140703020106230f01120209040e0a021c1104091e030306081e070b0304030e03070e0417160221070801061a0306030d03020d0603 72
    0xd08000001c0302112a00150700c1182c03503055a80308403161715016411625104c802501c583c0c00000001c0c2181000360404d12246154100803419000080c503000056100c0f490490041c0d440380001c000040c12580f42a26038840c880711418442e0f54a40451012100e00c1c001504108015503050032a14450b8100c40305810090f109200941250480e20764840003258100d000324802641d90700904401d41001d41295848685194001c0c144c0c410840506803520080c2c030307140e050344440c42c51101c18111121040740b00f81c0b0b000c50568075046015061281c0d090004c00d10146107059100711204c0400d811050b40e509900b0b16032292100e0074112000700084480d142c05100701240420751403240d80c2c80d02d00c40c600c04e240351a00402d0f80d550390309290207403000b01501d07072600007282c00040c03901d030400c102c03045003844080c00e080441d100c0e040d1402006a11101299640e188c00740204007a001c00790694000082842e840c50601030040303951030401e40b20f134400f09640810b1141c221a0560007a00007540c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 735271798 1250 735270548 735270559
    0x703111306030605030c010302030c030a05040812190c08090706210603200d0c090c170115020705031c120b30070806010501030b0f090405070302011d0a05130b 70
    0x20707150000503004142e0350140c42c5c801d10034440e060405601c24002c41780318031089560182191110a56100a001c018004980300e5806000c210300e140301030a03205101c1d019011440c500c030000408020102c8440c007600900b00240e103000c1120701403000071910b045034040c0c580b481c65a0090602c180c032156007401c036010098103203500042805400441c160301040c45148503189801c051003040700100c41858002c169441448040122181715400060f100700d10b41800c400c0360005600e024a4940300341c011141e0300c103158414205403a0f040009001421083c0d00a1111820240c4850f014244400103101040b04100e02d1032020708064200c0f400700c10000c1c001d812106503c400002e40080c0c20308440075060380b6002d60110804000984030210760724603016240320390810004601401c00d10791919000b40781c0a01001150b2500810f1a108500490141000604500c00100309105028904c40c01081d81c030b02a60f45d554460f89072000316401140c1003070456500310a143c002d003500a11066209 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 735273048 1250 735271798 735271837
    0x2803030905030c010c09080c010905040903230d0b09150d0302030d1a011b15021303240c1107060c060609020a030e010b04110f07020607050615091e070311 68
    0x80f505404c5042412229220b200100d5294400c0c0383e518120400347e540010000c010070085410b142c0e02001a02e402072410103401101d5110301d003450250b44806580d4003e00040480030007840d441042c00460007155040514105030841b8004280000b903581d20491418441a003003600800880e04501e259000c14003900d940f846c0b5110400000403610b0340400c280d1031400910a030381441c00b01c1c11035840040250402d0510a95100a41201c20550380380e03c3d0451002c404101100802c071048850103038404c40625250358102c040e151903170b420a050120112901008180128200081d51041d2a1000741f116150a140c0d01800c0700358070441c20680300044039947e890f4903403c01d00603880140000d004820440003030000720703a160b01c218070040000f4403000d000c074070f4210014842c0600042180c0d040507081d8035070905000c010795100e6100c0b030704e40300d101e00c49080c4103203140c1d848100000c44514282d001c0c07a40c8007035000018213075010595203555900000c03100006850144a0605080811 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 735274298 1250 735273048 735273067
    0x80f04080d09030501050c0313060b0321040302190e04060b1503090a051c171509010b03040b010b0307050a0e03010905010501080c0114180d03021f021902280303090503 74
    0xe14003e000c1a9183d50901002401d01030b480c000f203d0203900001c1c4480e07441e070010345484004083c05428294980a00c02240310945000c1c6c0040c0c0703258124884480d6500d20b07620400100c55114001d949145c001001c082051050480e074a40d1b000e0782200d0041045103a14001a030180c074104c0c10100000c2001c07003400000ca0002504041d241c2c030a030112000142c288241020140e0030386018000a00c000104020450b482c00079290000c000c19080396004440c54001205905c090b00300c40f1a0b044048100801d00403640340560040030480f4a42c3c0c59070401400c000c04a02c100044242440551080c007011038070254090451590010001c01580d40c68a0304c1507160003881c20344500003400c0d010302000d12042042119500510081c103660303444004018408001c0070600154198015848400780000c43c010328101088044500160396000f10500010f5106c0840450811544112074101561400e00c01e044914500010070034507a109031700c1d0440240002045c000e00d01e002c041000c0a5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 735275548 1250 735274298 735274307
    0x80703091e09050a1416050408100507080a15050607030c050607030b0f03160e060324041a0709030b0910090f06050105220903140c0d030c030c0804080f04080d 70
    0x25141ca51000f071026403180811801560303406008a0010b0003103101140ea441c81030a01450301044509103d400c140d139540c0380c0c0d420461850b805416582d16102000031550b801804142d00030700b00c003410083c0d100d0140000600c04d113940112800f41c0701c00a400343c02d050140c0320391a2555440404c0744c0300f616200800402611035040d9032802004480c2c91114107180101e42d248541c2d106081942c0c02e103141c0004407500d0070015051503014001c0009801190b400c082078080c0f90316140c48006040d00305413070800c05a44000e000b001512001ca1f00744000e031580000180100c035004624000a41c640c003960758104001c19210006041c50400d590003000811207484031520300900040215a81e510184074a20607000216410010351114100c0d81c241c095210030350b028061b140040f01c00810b1400c0264581c40050b10b0740351544200880c5424507414000c44400f01650f15083c0001c1c040b4601c050b14000000d0401040600c3c00300e0380c01e18501d06082a41e0040004404540381071000032005030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 735276798 1250 735275548 735275609
    0x4080d120f181118040809010c08041205120309030d110f040e06120312220c0b090909120f07050c150c07090506090703202a010902030a08070309 64
    0x180c0c403043e1112000860314040c03000d00d001e01241010503031180e480b0b60750480c1c40c0e0700c0441c0050510103041182c001007441d901c00b0300042c04035841c00c2d400805903400c1551629039804e1110172556410000c0000384100031051302d1207601070301c5020642c86c0010500400030300901e4a51024802d0208000a5006070180d800d80503810a5031510720b000c1111018640b24403d809590f1a10b12804003c52003210079100c030407580b000700d00610900c20310701c0c0d940e50002c03008542c0700d16911080801e2401c80d502d4125002c640105180004150115170100501e6a601035140d404e2500300380031600e0703000d01405201002410b18010000101401e801d00140a40c2d00700c090720340031501c50001d01244042c174612400307005075001460040d9550711018101e026000d0380010281c054190556070f40c0c948601405424004818007444044290b11552440492015a42451140c0c106045034000d070302e01051004610303801c080403d981e06800d00342641c60442d140d201010002e122800c40400e4a1400c1104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 735278048 1250 735276798 735276803
    0x50703080a0530070f0507020a06110d0c0534080618070320120d030b030c0d152a0302120c03060f0609040603021504051504080d120f18 60
    0x4400a252002030700b2503e400400d2481e1540415011070207080c0980c401c040000f15500d001d81c5809455408035901c01080d0313101c0004900c00295842804409014400760303000da0346452010b421285d240c1070b03500c001c800c0c03500604515905c0b1800700d406441e03130002143d620004240d140c051343d80200c5581e4030350072112a00b2201417400080708040c1702140003801c690b00001c24180b40d04042c1c0d516400d0180841605900041014016240103010700c1540c2600da035580700002d00d801c0c107105050800040308007051146c1c8c00156901e00007a2801400780100d0100c0d140000c903840d550724012070414501503180744c168101803140503450345c980c00400c6603454000398690703140c84103c440a1140010b968569000045e103c03800780c00d040220282c19468802080451040d0ba6030300401c40303076140f00000c0e40000d02e00140c02d11540c100824038003980600b82a2440c540b13481d0a00180e120350b8084040c10030090480403142400c0c030702d40c018500600c041c9070104030340403603017403400b803507140380c8604 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 735279298 1250 735278048 735278077
    0x7050604021903080a031505030a0f060f0c05030415021201080a050d1706010e04060b04090f0510030f15140703020d060b180d0501020f070b10050306130b04050703080a05 75
    0x4080c1d4214140319504507544507504e50b080981103d41035000e04001c000850b0b44030800000010150783c100440660036004108003c41c035205030400c0390580c0c1059444000960400080c0d101c070507441400c99900c1070f04101d260b21305130b80800d40300d00a407041ca11502541500c0d1000800c4007400418030b0a2356034803520480b086042210b00075200e22540f403001e22004184c03440018229402245022907500009000245858544444164640094000c0d0315807560740c052049038104030b80700c1c06400c801070900d800c2c1c1e030915503a00e1288044898100074000184c0030750341150244c0c2ca81140400c480c13003401500c102e00d0300c818000c00035007020405c40ca03050304000001540700007402c00c8510640031418400b4070f5200c40014088500d000540465840d9801c105550580d40c26401500a151003504840d000d41819000041840c055800185c4070360840f10070700c241840b100d008010000c0c3d00401540b01a9686d09209040c880a9800030300b40c4800003a45400403a8840300511030816910079 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 735280548 1250 735279298 735279319
    0x15060f0e070216170109051b01110a1113020c0303010303270e2409010303051b0303070c0213200a09060c080a0513030c0e100905040c150509060705060402 68
    0x20704981d50700a2000040c03001200010038010140c440749644c2212103244008904100e469481c030341380140021407124018091a0070049030742c0e2001c2155090113180d001003408201a0300d4171060301014001e501d00c00c05070170300c0300c3c00780c0090340c7c041e590b4054545080daa16503959060103020362668043d080011544070b0b88908520211000f03036825112422408035090740c40c1c0345400c5043e00808030082c92120441d03d02800d5507961702455020354801d40e112034444c401d0401d000d03010300020b10107d409800610800465552281466040a404860000403d54400000402041c500c0103200b801e260600c03016858501c4d150060000000390395038602c20a507100821101c103200040010445c1000300980b054031403151020302014012007a040c80340a03600d6a581c0c80e40c80e072581c0100710f42e502c0e45042000500310b44103014001d00110105101c82d1402e65a01c030384107410b0b402200003151200000c01e0789903108000f5164030070806004190780d440d090610950350b0b00c048408a2140c5d881302c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 735281798 1250 735280548 735280561
    0x5040804060305092d0304090612021206011203030209130c0905090601050f07060f0b1002060406060f03051c05270a0503010b01050a03051306020d050f10060e0d15060f0e 75
    0x40c00c030600d40341701500032000310f8541c0c3c209988502a0b4080c1c0030b01e03100c14000172452241a1040c48000c1c0724043c22008d81c00c1c4e0510602541040814000c6d1494101100400128954100c201c441583c507240040c2d50711005400603ea00000700c10b40401d00f40b428180e246003d1b04210100103032601140c91070b0750b55895100454192282038001a9900301c1480180c001501c20f80152812402c1c0c4d1002180040c8442d003c141c88100143c070000060b4440c00500c8240003440c81010050107070681c0b620384075810b50711102d50b076001010714440c10f41e01c44461070a41030300c01e01c15500c01200190801e103081440341c00261000800ca140d80e0b101d00c01c0303410001610307d070501c29980141c2042e114641485445001680200310051101d040241c2d4401e240c800950240f00400e241845110006028180381ea9080d8200c84020482150062210385c00e020b0755401614242060004407100040711140e441e210705060480396034a1020760501102003035050007103e82d14181c602550200c003155a41c0f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 735283048 1250 735281798 735281803
    0x20f01050705040302010e0f03060420040b0609091005120c01080130030c02060a0309291602030f0708030714070f1101050c07060e03070f150c02010c060504080406030509 75
    0x7500c10303802107802000f041006500604182086080050102010b054040c001c00e0808104450848400b80c240c4101c00e00c40808141e001c00c10f04007650300300403040400e40800c041d4410a05464400c8204800003075142e000001d49801400020307114004e40c1030f603840c4041e9101404000907000c21801400820b8080d400451324407240103410b104c058071030502c0001800304040890035005c000d00310b50040702584503e0002e0851402942d0b0001c0c104000e41801c18050500f03180009030300c020300d20805000c02040b00044d820141d90740c000210070102036400d82c50b40c80340541055081d10041142c00900c840c00001c0c500c50941626440d08880c0000004443c600ca03e4000a010001492004020078000d00c121083da079410704119240c6070700210f03e68a481083c1e4800d10028640541800140c10705202d00c000519500800021aa041602d0f0b9001b20100c03061050811421002003415a0300c18042e001d074041d00b00408201d14141810000201d511600030000881d0a003400f003191480700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 735284298 1250 735283048 735283051
    0x130e0714040c081003060c0c0b0106081008010506011706120a150608121804140f041202030702182a090916021903050f0d1406040207052814010c020f0105 68
    0x141ca132420f00c510308541d10b4000402c1488038400c01c0218500226001903404800c090181c00c05071550102ca144c58059100c4284013504080c40d180d0500091003040d9802c004440301c03040da4076401c4851940c40b41c0116242160301030742d4280d00d204040c20f0700d0a00191a900c410103100588051090341c1e128181580d40700101c8690040c000010004090100010a00742400d110000c1c80400d0100b42c072007540f64000b2090f2212141d2000140c00c0c03004002d0310034140341201103140003031410010280c000031703010513002803100303405c0c43c4846c0040d8031070507081101c041174039803050602c01c8052141c070009241c1d080400b2081c011004140801c010340c0f840e8556002c0308a442d8000c001e03130003109608128400b0224000c0b41446004d000e1041c102c0c400350082c1c91006003030b4000242c01305080b0551002031030041c02d0180a580304110907404280045500603454260b90324940e100d4003075444100314000b44400141210000c2c1405000d03580b41900600700c607940c00d81c00c81d007000c549200034034202d950 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 735285548 1250 735284298 735284311
    0x1d0f120304030f05282a1d0a0606141e1b070b120a020c0f011a15031003020913020d0f030e120615040e010c050306120703030c02130e0714040c08 64
    0x1510040c000004100c1c5050205000010b00d80d00e00341b46000c00d040c4030769400c40c4c001c41604611059220880200d082d080b65104081e40401d0102ca45001005089003c04403440d041d103440004d98500d071101d12002d410f82d1440720800040d514940c9000401e000c0703085001030076660003503100000326540340c03c2c01c7e11804c03080005110b542c1e4a803480550000d621428809505010f040c000507007001c02072040c40001c200045246904104d00400c0002c40340031102c0341640d0540c1030041c81703e20b4114615035002c0c0c990641c3e0104103500d4007040c08208030900310000354041c1c2d5100301442000503100c94140c0451007a1a41c080c580000c6041142004540501074248d81c464030001e15213a0b0840e00a80100310003400000303400b06c4108500d801d4034000701d00368010640020502601d820191402c0303405010701406411aa41940da000705025854000a4030400c0c2c0002440c441c03240c2079102e40c14820340307030080b2036951b41d07a10180c0080c3d041d00c4c0c4030340c1c1c400c61606401e420094050503105104d00c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 735286798 1250 735285548 735285613
    0x50a23150604020d0b0a0b0c0d080c04060c02010c0605100303031802090a0510030206180a1d0c0d060512060405190320011116060b011d0f120304030f05 67
    0x340d030707442488000d4004902c4011402d89034070181d95035445054010025100142c0c1c5540c4e40c41ca0018102d181460042d50380341040b04140c1000300121501c011707a81540e003c0d140c1a001c200c913500048034035020050303015144134989800c0c421080c209401c0d1504591098078140104c40390100b84503825a507216002e034220207110005111700440e54001c0d03901c105001d041485054483d008624a41c100071242ca40d1481942016010b038a42070f6484401800544180101ea100c02c14810f410703601c01a101d01036189000c902c0260079100b90704440003078540034104490a00f51012a15074600090340c0039109400f80c1c4854a018201801383c030307142c20f60992194017001564800c44502802c2940071261255038a02e4500e00055015006054035a0364101d00040b4541c5030601c01d00300c4401041c0f0174180410345035003d40a0303482d482e0f090a001d03000c440081702c01c6c1402d03010030102005003880d4540e600001601000708001034207202d0065000c0d40c1218ec62400e484145200d07011511801c0b0800c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 735288048 1250 735286798 735286801
    0xa060b160b0f251e0e09010f0302280b0a033e030a140925061d0a180f0f0605011704030203040e13060e07140418050a2315 54
    0x21480460000034605403132a005003c0508668000d1448030101003031030009000d148070070650310340054058003420f40b04c01000185461030f40092160004400c10308240d4100b10704036808040002e075004001c000c04400310303560b41c000358030081c000d01795510090003140542a60710b07001018107410070501402d040310718040300906001100359400c000c00c410206921420500302d40d07030005002074082c40f00ca600400784140760030110380341c60120781c0310b04c0084504003c08100d403d42c00b07102d540c0c0c0c15075030340c240b45105140c0801087c8070340c2e170941000c00782000030b0000f005c1780300703403540043d10b0110700c0c007c10848810004428025034100388038050010340304218110f98403900310401c80d00280300f8011646460b07560406201c0382d40c02200c40301241e403255100c0001f030100c18003034054001c0d218805800f00c541070080b42c4400c064000300480c0110303901d401070741700e1840c0c0c010140051a00314088418220070b0345011002850440c4500c500c07540c25000040503078800041e240104001140c6160340c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 735289298 1250 735288048 735288091
    0x5180f03090114040504021909080610050411070507150909061406090a030f03080a050703090f03050a0203120c0c010b060309070909020a03021002010e0105070c020a0506030a060b160b0f 82
    0x2503d08241008001c504200800a0f071903490344014121841d111481043d58154070102500c1003101e588080303000c0e0003036401c22007455810007204c4140c0380c0850b40003079600e40c01038041d41c580c0100700c03005006120750745003c00c0700300050560040344e280c43d50314180003548490f1640c09440300b038400c110314000800701c040040d00d0104080c01d501c40024002c1c0c585555207450307d03100c1c06c4400200703074040f41010091040f5088107020701540504141810701c019020b955610b003082c2015240541001004070b0541d0240c0e00c280112170b0a5100510222141d007400e6001800f50350091025081540ca080b82c0c00005041000681c0e200c1c0803560301600400d490024240050290b1080880e48054102c0d8048016036440c1081c1c10368001ca80d000042018503e036a013401c44101800c44070030300510300074000041c0d40d650616400e4920954050b40c07039864054802c009003081c0d422440d028203000c01c1101664540c507900d44072041c012400c166542d11250107015071102c0554502d001d034010008c01c00913 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 735290548 1250 735289298 735289307
    0x16051e030d0507034212120e12010510060809061503100218040f1a1314090d12050c04060e010927051b072a030605180f030901 56
    0x1401030840c1804200b00b40640141002010002080c1030001001d40100c45d0791400030031310212200e480c00c0c11107161820900701c40c14400c560760004100462200003442194030030b0426800e5102c0c0a40304144900c044c5600724040c000c2102c0000c025844214002400fa100c0d41c245800b5850200c0a40800d0b121220303c1c03c4185001840c40b40c041c80b03500b809491210301c9100412901c0c0c5210600c10480461000b0001510701455100282e24148440e08070b030901640e50000103c84210344080300a060419410060400400c4c206d000c0440e002c2002400c290100715402c1441d90399690014052814582e00d08036001034543c1c41c403040003440705000f120301849006050040506004085990714004c00c40040d41d1600450b6a59842428142c3c51020354003c5a80256141408400307400481c602c5034058004d0b20380c0640705d00f002042c8070505500324160101c100b561002212000c42e02e0742010740c081c00d002e948400f105017811050440d00f02000c903510b0219602003020358a802213042c01140c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 735291798 1250 735290548 735290551
    0x90a2a090803030c0c0c04090c05190e07051c140c0702031f020901030f02040302030c09041b08060f090109020f060d0f090507030201270519050616051e030d05 70
    0x50900c048154007181d0560200081e500c5884110b9405590301c072050360075803c10742d6400c109401642800c141d6400514060141015100300b6101c4002104890181c0304800a540c0c1c00031800d0071100041c000c6060380440208000c1116401303014000c1c03421010502120401d42c0c41100344800c860200700c046001c1002003501a0004003154000844002100340303040010303861034031036070303000500e03545558160060601c16610300c0000c50a00b031450700800c0e260814400f42030f02c90204500010104031001425600000000700318443c0503441d1516655501c2e425166a1444d480100001c0c3e1061014000c3c0303265039901074994090b4404c00800c3c0081c1d82c2100c0d001c4c42816899980c0744404484510138009280e010344001e013003c614500000d071001000d00c44998640305205146910009440d41358001c9601c15510580c25000d041e40704149011250081940500000b91908011302d41c1060325403600e000d0019200d4109042034410f41c07c0c801c0341c8001e481c540003404441c0f40c1d108107a0020303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 735293048 1250 735291798 735291881
    0x50a03200d0806060d020a18091a060705120304030201090209010b03060d0201030c110d090306054012050309010c0f0c03260c03010306202514010b090a 67
    0x5d080c4854548250140e03040a050400000d144035400320700c08400740b03890320042500180c200410841c06030001c080f01d05e4545654011500002c031682086800c00980701d12141905145840f81841c0c44c000b40030303010016050344560059000440d400c4120003c0300d0141000a00c107101c0d065559005401a1629480c4c0c40107100b00401e140c8051a02032100d40b0600d490f075034038240103a045d85085011510045e207240001120080c0a5240c0811070502400098202c02185484082030f00d5100e1b060102c0070004090800024100700043d0b0808055805000180024803a400d80a48110b81c4140404950701c00900780d0007010001c2401616000c02d429000303058110b00800d0709020301030400054800d0180100000300410a0228911550141455500c596244c040d480b4800d21424001d2860406001218103080722030509003100320003065901c0005001c0c14500004020700038200d0340072150081c04164005001c0c503089100e00e8044040340c0354824405103500f48a10b184017200840f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 735294298 1250 735293048 735293059
    0x3311806080706020d080901090506070810030818040c03050f0a0207020310110a1107060c0308070215070207090b041e02030603100f09060c020f100b0d080403050a03200d0806 77
    0x4140c00d08144001e9010f000d8a400030704500d50200340084ca44040140a84201d9240c040e000b4001440407071101c2c0c1000c0c1529005a064441584c0c00700491040e0340700a0004600040402502a17210341e00d114503082150100300140604d8000d078181e0b0000c6172004004044480010301502c0b65074083e100e424000f40031100c0a04044120000721080983c900d07403141c00209414090fa948401c06404c000c140c0720140407114501403001d40700034440b0000074284000c110000301c040381b00b0040c000b14001214050f00d00c030f041c940c038044d40340c20450194490903030802984103141e00340783c09024441d04d0314107a1a21300117000c840f00c400a403c0a00b20396458000d00100300d500348039034040d4023507403c190700b4000f600548625103030b000c503512030700b070300043d50405034210710040c4021a0388040c0c00041140070985002080010703600c40c01d0004020154031002c00d021090081c002980c0d40e44601c6a1107a500840280f0a40805050003449180c0242d001103d0080e0080c0701d18000e0307030000405440b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 735295548 1250 735294298 735294311
    0x27060302030c0f0d02131215050613051003020a1406041206091a06030c0904030e01121e0203010e010f0302060703120f06120b0c031003020f06090d05033118 69
    0xf002900340c2c040e400200c030391a000b19a80071400441c1d440c50340109844050021a480a540d0b809140100136031007000050381c0e940001c5198503145800c0c0c03a40c00c80d10008000c540f1340450383c55004402408144c0c0038058a020104903a4000008103c0d607813801001181018982007151465200700d03441200d21944a01c6900006404582c60a11041200b00c403a1140d00e400c2e000d00d441d1130185016103116102140900c0b020ae07400c00552403c41c24280703004402501070394940800380c80d8090000e0260030426283c407105403002d44c0914161140c189240b40140d0380e810308440504018007001c3d40c415403c105410003e800303040c000215509152001c41d0000404034204104c8d04964000030014071514120010007100414880d4001c0945601d5411801c004490900032915800000e00480c01200140c64681d00e000503030350411002040211080c038945446a100c0d003044880f070180c030700e0700c2e0404243d907080140e9001c0703503070581d100c20b80382c040c41c0c6403030303550320341c03034a052120903984d8908 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 735296798 1250 735295548 735295567
    0xf06050a0b03060d080c0601080111071a060a0b0f091c03140c010b040f0e1606120b0102030702040c030204050102161203081f03050c010e0d05060c0a110105040506060127060302030c 80
    0x4000e002e006d0084001b40c810f661404103c1425205440140180840100450000204100c1c84c0f03800f402e0000300701c9001c2d0355525010034200b0340d85030080c0384030010220783c94400104a100030080d008059520400a8000850070070785001d61040090214015440c81c090011414000d014881c2d407102c0085459040c20001c2812122503001514903161203404c0e50f50404002c002d80c2494801c00b25803408410b14246008001901c8000c800324491f0f1158208407560380b0800903200d02d2034000b0303c1004900c1c1c04030310240c029030141c4292400f6001340411122244802c0800314115a104a040c4c3c2d03000040b0ba8003119054001400b94940324100d800780c4404000c2106180301442c401c000070448010590005403c2e40b080f60b08140c46041540c41d41c100040c004a034140c0c0080500149545840358014140c403854a4640d4510b055884d000800c81030000004045c1d000310700030f880368102546001041c040d0842c200c1c207079030b030b40300304048040000504c40e5008550114102d00c00324244116131 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 735298048 1250 735296798 735296813
    0x8030f04050603060d20041a0108070f0201111317030403030e09061c050a0c090c05040308130e10150f05070210021c030e0708030c0d030902010e04020a03020d0f06050a0b03060d 78
    0xc01c906d102140039210311130809218816514039144003075508008443c0009001150040c100030402c03075454007450030903000350051b4090707000c180130194079800251902c4031010014842c0703003000d448400c80da41c41d11102000f10790a49806950303281d03e0b9210003013401240c0310007401c100c0e081900c000d04180600c0310b4042c00d10f80da40c40b03100030f08010b4035141044440c401c0907400525080e4608449607231034541106c105d0f400c0320341c019002c645034040d40322003a0703038080254010710201ca400c1d410032007190007025804040d51010758960001800c00201210503201c0e01051f040441e8042200034058546031081d07181000d03c0d44110352850311070601c09028840824200c5000c01e40f41c40045181007014800b0101900226000f1428860050113899a070342010544030f051503070320000039003903903c104420b2a01800140c0300790342e12210344030000c00944c40345416070f80d2240b80c17902918540740640110b1007100c80c010109110b1a04001e0f14120b40c0d030020b44616031120440701204001a0746 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 735299298 1250 735298048 735298073
    0x20708070c0e07080601020c06040501120b0405071707030b060426010c03091e0201080420030a08070210090e071209120e10030507140304030c1a070908030f04050603060d 75
    0x1a402c1426003071180020386a090050451419500490f8a46559880b204151400c489091802c86440745110380a00d00501903600c440b44c000c1d04048c2042105500000ca81017040008a01d003c0035503644d0300c0881c1240d0f1820030555209404000030410342e064400000c1014503d150452030b4168009003441c21504210b100c070010a403a2032540701405140d14141c0081e030b05030208606080300310f500003021068024002004203000c000207803404882c0140c43c140100d005802c454200a1303e042c411540d400c04c0c001284038040c400301410250344900c883e40c0440749100700742566501c0b07000003a1203124202e51030314001d5030307600c98010118000303018504030352402c2d031500c0c07054050f228244000b0800c0740020005050a01090201d4a82d100f51000608480e0300c410b2a00d9490305d14046800c03103105180500302100309010106101804150700740a010143c9410000c01d0b550b001c80da890f4015407044004160702400704004904040c0008e6910090042122042070640c0c0e0314000090721 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 735300548 1250 735299298 735299309
    0x10906111e100c120e013e22150e0f01020309090c030702070515220b13080723040207031103040306140f160f18060825080a020708070c 60
    0x1000c026400100f19902c90140341131032002c000c1c000840032180741844032010f50800c41c60b87d812014451150014030302001e2001c001d401c005503558420003078201080400301c052200340a0001000545903180355a42c0c0b22281040c0c0b035400b8104003100c10404075251140c101c1d03041d07000c00c10481840340c2d1040c0e030a81c880c1e03910002554582c20300300301c0203180c4080c50700820702071200820011b148510000680c0c585403071b407501c1c80d221500111800508003010f0740c010800c1080100d856802035690311001c10544072002c048844440c0c0d11505a041c0344030010803400f150070230bd141d19407030781015001440c2c0d240c000e05110300340200c0103410070f01e03550256009403011a521a0304072408041c00000076041012580500d210341800501994140d00c096001c100f400910000c01c10308600400d448120b4075411190b08481c5d070b9685101505c030700011200c510618450b80444680400e00641c00042044a43d440400c1555040c25000080d400781e007040d11160f10500c888000034001c40e070078201911 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 735301798 1250 735300548 735300557
    0x609161b0302010f061e12020a030803070e031506060a1b020d03021c050306090604020306120102030109060e010803131e1503020d1508030306040c0c0506070806010906111e100c 78
    0xb000c0d40c402c9030032500035401005055410400b04506da14201c00b030803042c1e48810501003074082280c800510541e86ea588001c040440100422070741f0f517008618045c00745019019160030075144140040843c004442c0c1a5002a09101c00400244210f140f114003140100202004035901e80025422580000c000c40040c3e00032032500300080003440e03107101c0302d40460400500b142042c1000401002e40140194001c030b5000c0000b0708942d9900310600300000744080219036135611948200003600d01c1c0c0c0902380d4044100380002615a000004803014983c3c501c0500300c10a0804501002101c0a00040b4420b5444504085051515040b5081c404c41c3c40c2d441c01680c1d20009218003098034661001010502e034003210030080b5044c007200722540101c2c210340000d0301100c2e00c0015035070710428070740180c02807103110104402650040311284c0281401d81302c500c6a29502c0c0411140848c00d107004d03100700d030040c4500e82d0f0144000580911501050310660b00c032400c1d141c03200001c4943c108442c10004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 735303048 1250 735301798 735301811
    0x10c052203050f010c1107030309172a0312091008063d0f080604110c0303010b03011d1003023703230601030b0402041506180e0609161b030201 63
    0x40390403051b8140ca5100b90030181c4040d901c6d50300d001d0502c820921030005144c20001c0116038012080c850490700d01000c04001024140c900c3d00c41c280c030415404014040d1049c8520941202d804c24252600d90f0070044c0030104d100302c1c0b858100c402050140203160044049011580705c002036030000601e00e40d01d6403c0034160308440b50a045407000808594051080340e2840001080c0d0004446034000350544000c500441c07000d0103d0204e204903d01001540004400440c2c00790003a401503041b00c20005800e040f00c180640103110360642510101026180c4140800060408034031101c40300c8c0300c1003000030b45405020804106141a41060134401102d45d4042c02006100e190302c0c0401081142c41120702068200031581e500300c1070101508031541803001604558860700103404a2500061410b01c1550303544000d824242440510305101041000110701030a000d4103032403040c2d02c010814103141d00c604218500b1414170440020800c22030062004008103803a5610307104510036400000e05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 735304298 1250 735303048 735303071
    0x1a0a0e01110607030506060408010f020903010b04021c05130209011502060906191a04060605070308060301020a090306050a0f05011404060f060c020618151b010c052203050f01 77
    0x11221149118103228410050030240500000c60b40ea000c4218180010030342c40b03840020300c09014a51040e516582080452007003000c5a0b0003902081c40241e00174407404038807a0412040c0d00902ca4404007802c568901c0c00324a0950707807c41e58004e0070200390461101403940101d080100c0036003246100601c4a2240c4212a07410030400381d000039041e002d840c0301d040400111803d040e6400010714016107820303015940c9110402033000800b0014010019599604000391050700801d005030003140420002824605041c000c03182c10b0a12543d17103e59503821596514002d000151003c00820368868854200702c125100d99406080000101040400008100310688440d07802c00250190700c0070303082180607000400b42d0401a41100d6580c1c6410031010284c1c1d20320010344040fa84544407075000c1c40c000c107001c001030500c0243d000c0c0000020030301040341401e0311990a030600019008101ca514420203107500c0240d000e03480902c802e0301990f03a480312031070103001250b030b02d145943d00d8241510 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 735305548 1250 735304298 735304307
    0x40e06030d030c0e0f03070e04060b0907090b1215040501080601140a0e01060516170a120506030604020f13020f090a0618050103021e0a11010c03090c1503061a0a 71
    0x11041e589400d0161095030000182605100e0100c40c3c0079103e03000301d40a940e582800004068050100c0c0c043d00c0740382504190f00680029416503008008007804503003000c0c812942042a80e681c400c0b100d03d0040000132000e10248020000f40310060354000c000926a254000c480c000c00c0c00c0001403c00b94180740840302d9001000c4a118855880c0ca0b20401555401006541c11208c06041031138494100b40151700d40056145e03c01400f03030307020b40080c1440c45044000740c02e560718035030344052500e58410114400c441f03040c4c5130b6030f6040c3d21090024005182080b0f2551100901800c00403511035045d204406a8015040c40d410019020802c651982440c0e41c81c10002c080a00d082d4503501d004410003100700015000d82810960009401d222249820000e40314280078001d07403640d1143c00000041030441c4089042001d9400d04400c004498861b001e00c410140c2c024400c0e50501f850b0004210051240303204103010316403035075030002c1d141600000b0320290310301b00d501095541407441030090 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 735306798 1250 735305548 735305563
    0x1050114040515180604030f0c09060e0a0903051b0105010504150506030f0c120403180b131e1d0103050606040606050a05070303270b0c18061c02040e0603 68
    0x1445038081c40100032a40c1c9a494004102a406001542d03455540d80c1c019803960b102083e0310307048800000c3c00410090040082c0c0300ca1400f95040b200d405480d0740c204070a0720140d100381c0018060a00c0400c0c1c504515605c07100f20710f40700e401c2003483c017102c1080c1c030400c91441d140d0480181c5d541d00010071150a10f4040d5200c4100503045100c25a03081c880060414007001c1c02020140c0c0e4a4000603a0100301c580440c2c01c100c013403140451080c60f02c0c0ca002031005414021421102d002c03400d00058403074085060710b4071444212806403565082000b041d0410404e000f1190b01c1c07050604000441040410042d0746000c60115803624075070441c244030b032500c8400780942d4091882d100e8200007065001042c1c03800f1114034902a6603401d898102100980f030a201c001d0151000c06c0c66602803104035442e002d070790f03910176000c00d0440c3c3e80e170800560030b138080c06240d05002603e203204203030f441c60241c00030024014204042c90308006080111801c980068010b9058034121505000040c0390412031342 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 735308048 1250 735306798 735306827
    0xc0c0b010b0d0501080d08011a0418020304031115010b0903070b030c3007050304081908070f020604020607030f1206090c122901030204170d08070c12080c071a010501 73
    0x41c461b0a0001d0310041600b0b0051254144a0014003100d600740c92840040b50010321000c454400800360800c0408025841510203d005c603d004818280ca00c0c00421384030402050044403051580c81c00704100c005900c03004025a05000c0c0c4080418408000005140100c02102c6004d460382000800419400701d03640302c0c0d9404c0307071121401010415000000b50342c40062403900d0381d120340b11450820814003c0111701028598450301641105602c018060701c9030b4080e940d0029665500a016070b1205400e480c045d410200402221010034081d09109550f40303402d2500d40c115018500d107003012100c458000d00d110380d84030803a0f5805a6030220701d0fa691400c83c12010030156181c040407894000029481300f40008074a112260143e00a074140e800614141141500300807110361100e071141070344031044c03020680e982c010035030980c856080d10a1090f40f10305426081d42c42c01c3d509584c248070080c02e483d41e80c2820000d01e800074803803000311b400c14400074000038504e50500001400600700d44d1600d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 735309298 1250 735308048 735308053
    0x7060603111e0f04110703030f11070c050d0201020c0907020c01020d0f08270111071209080d0302071b080a05010501051e0f13020408100509010b0a090c0c0b010b0d050108 75
    0x20070b440000384000714106480b0884401400181c079401060103803645e030140480450010906000703050300358100040c018200c1c1c00c04c000708407280c8c01c0c1e15598000c0403800b90100b004524144240d081480802405900500465414400d071100142100c038040f1400b5006810010103520f9a5804204003900c60115040c4021604546e4400401c0c00a009140001d10315541c2180300100307180714426411410300000134041c4502c2e0410001c00c66003c240211080c42800700380351070b200e2041064405588561018140015900904801a400441051f41c0000a0706448440c075020308034448014041c1501030145111981001b41c01c44005a0009006a0400070403249440020980d042c20b142c003203d00c20084070341c401c0403400a500e2040220b6080e84009000300740e404000510251000000b5014041640d42100403030a0303884d0701075055008084408203000070b08050b044090340443c5898044004125511a412119020303880f20000080002e0104100d039018002c6030701400a0200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 735310548 1250 735309298 735309319
    0x105071d0a1d04140319090506030105090105090c0405030706080609070c051c02030c1006180908090f0d020d0c080d02030f031605040305070905010e0703050610030c03110706060311 80
    0xb140c02606124004030300100da8490000301004214060000407a08400032651540c41e9a00130800c8200940890f001103031068070001400d00c2d168003101d050b120040c101c800a640390205015655902900304042d6a10a00000c503082c0c0342040108010f01d03103540c0d5040c550500e44280220000c01030a02c1007004201e2010782c001c504002400c0e505501c0001a13102d0300940c0b00030403400c46c000c1045401d0640a00000e200c40c6450702d4010b00c081c0c409103a8054004c450b049440c804a8203000360041101509100c041034a145c80b181c07450103401d0140900c00100d0846e80002c0c0c5d03100c0504003c603102c90084800b0f002e0a0f42c2040b0076803c10105000540c41e115000307840c01003500000380000c8203425200f8001c50700910801c252001103621104a0700d56075110560080580000d00071003840d0002070300040d042d907102e40902401540040c0242c801401c00040490142c135500c0c464070b0038161202c0982400079503240c0109600ca0003200d0008205055140c0940e94820904086204028581 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 735311798 1250 735310548 735310559
    0x51201020304020a18021b0d09080f101505090f161b0b0a0b030a080a1206061b050102160f1118071b080a0305060307080d020a0f060e0105071d0a 64
    0x604003010b0360206000c8040d03440c0045e188002a2240340c02c43c0c4502643d40041200c186c20000f0070204640710b81d1074562481d611100d0705580d4060020001b0602d034406420010600f06540c01b07074040407050002500400e40307030804200c032084291051040ca41011042200d00c184500d00c4007100f0101e403810402e1400c10500a20001524100240140650401144031844141d00c8008076400180988062030602d04141c11141c2110703000c8030204000c9940c5031465000e0307100d108251000398458290854034110200c50303002e283c403c01c031420340d820401c4800b0701e100c484081c1200703440351a046910048514102500e90144941103004007640803400e41d484001050b0560312080903d003600d8075040342d0300300c259481420580070f050703c0703000201040810361541180f40300e008164211030219640d020004d51b1210301188582c016041007500c2400980000780c02403e5900940d0089000446100c1d55800c4680507034a406c00305052a0f41e60542095031a01d2020204044814000b0301d850315 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 735313048 1250 735311798 735311809
    0x6370905061b19030c050106050913142a03070f0609150909050403080609090606130b010c1b061209150f1404140c03060115030b0d14060105120102030402 68
    0x40c941108410192500600c068104490543d0001d92402c9040340c0310310b0700700509902d480303100c00c3d1030310b500348000800d203400d220040714007412003680707034403400c038010b0300d8020301c3c4001c01c540550203008621081a0000740c0e800882c107004007480f21044d5818288041600c0d0a600e83d001030b003070050000007007003407980003800c40089440041d045c484610450310f0495a100803600460285881c0c031003031000f81640116a08d10030700090f212002940c4908201a03922001216140e600080458041000039225003200315662018186101ca1040d1a921030040b01140100d04030014031310352082000682c4a01c511181d094505400c00458689031107506041604120040c04d50303864084110340c030388050748000c032480c9440d00100180d050a00d0072440070442ea040e210410b10892150034032501e8089607a5048071990039456906030458070054015000200705268084040051000441c600310813a05140084d9406482e296040c1810082c0d40c40100040d0000d6030320500800c00180c07101c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 735314298 1250 735313048 735313057
    0x1909060f0b0703030e1c170903090312090433150c03051303150b0108091506090c0403050d0509040f02090d20100e03010c02010b1e0637090506 63
    0x5213000704410b031610318650318000c18012100c1c4ca000c0c40c07080d225011640000340010343c509941148989844500b00d00399280100d42c1081e5040e0000310b00d03251612441c5c801052440c2c80504040b42e1b0300341c0502000c8180d010703140c26486421a039030b0501420482c40507690007034028942e41860f03049014600030003143ca40388004050000006048003d128611802002180d10401c8401c10300c040707426010285c86100c0c00f46000c2941e502c00315281040100d03240031780c0c1021140f06500e070355540c800c01003e042e014000900d030000804c070210201b601030003246448441c640b1000d40c2c0708406030074001141e83e28807080322a988103101414007540d640b50820040750700315030305040c04003c0d0f80c500ba070441d10290303815501550082044000940000031041d0070881240208603115014070140d003a01d2a41c003009a00c9840d0001c0720307004400d4440011745221014100301c0c10306801c00e030444c07110244504a40486140b5034030640e02411100d600d000e4076900b42c540000210f1501003c91a90b014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 735315548 1250 735314298 735314303
    0xe0f0312070c051c1407050309180105150d06080f03040602060114061b012c060606090904080c160f03050d0306060203041403030f041203110d090501030b010e1909060f0b07 76
    0x65103840d2a680c0304901c00d1741c3e8080c08002c010ba80740703028a070070f03a039030351002c12000d0040c00d0061301d0800d1003196011803030480c0d0f009031030340a0024440022172200da10900300c41e510f82e649c0b03c0c404642c4550410240381611410001541e5407824032138080d1405105901440030b0382d1101c0c191108036121841560300403105848212030020401c030141d4003412910044000900b00000740c550041c906420480402078210180d410302e88450003071000c5441001003540e00103041e14086400250032400501c081301c61541074402d00007010000d49a0707601c003944680b038007818a450520510109006492000e800740c113042003d549070040c003a45a0040303201700721042450b0b280d44005a1014400c4440442d20304e490281e4840d225140203c80b4841c8407000d800103104146048569080044c4400c1145419129110306900d4400114040e02107248190b0400006411030811600e03016510341c440100b802d0402030360b50402141c101100e510781d2285d0840800340741e0410031085d1881c00c0fa1003158 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 735316798 1250 735315548 735315583
    0x27051b0f0f2710090e0703030c08160c1805040f060c12020415080709080624031c0305070201020405090114010c0b0702011a0607030e0d05010e0f0312070c05 69
    0x11150700015480c0030111010071014100c89611502450321568410310641a4030700120485031161081d03011140d0b001814860307036024140c00d01c003190051404900240c818002e02e0325200294005000400341200e0803074070700320085410301004141c401145200a0540302c104114582900c848411070020368012301460f40d01c458504489119600400c821074031210255503403a510042d111a8105a03100700c030004480c8000305003070a200f400c21a04035400740740103003c107481c0d402c28004103130741c0c41a281c06c40d1072060024280546043c0000c03410380486a040c40884901620701401340c07000240580116403040000307200f0741d540e60f000c0a0564940c00a207802c0744420b4801070700c02c0c030017010300503001484110401080da58150420510548880303890002e01da00702c414401c031405205002000b0411071017851013241080615803900f9800f0354004103000464000660600c540418049070300d400004612400c6101522116000111031038680300c0b480054842d203032564481c800c044600f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 735318048 1250 735316798 735316819
    0x90903080606160b04020310140105091503030708090f0a030317060a21061410140d0809090619090911030607020d0807020a0611030103061b0503061327051b0f 70
    0x54800f04241e140300300500600704081c10078110142c12081d4240308061107339401400262040d4811050a03200072800ba0040d03040c12407036a01e81383c071a0070246030940c101200310719512481d651160541d0065010b42c40b07441c4075040780c58100800341c0008198a0003601a1881080200f46c4005005000c0710300314504140009207143c0308018011404104103040074803400d0095103103840010390111041390103101002c0c2c2c1c0280c10700500a00500c00900910401d208144c1141048101ca130741c4100b0081402c54070307040358250800e00d0100360300002c0c02c00d070b5a034042c10204151014072441c0d0b58012401401e03940340c00080295a81009910b4004110030440414072460003082228441c581c001340601243c20303c04181c5030340b50000d10045d609a030810010140c100000b4030224542541955003e141d039452006000c291410b4024002c40540c0d18107c80b004443d40359600441e5210280d00c084003c40c00f03003000d51400c18000703002d0300c1c2e07521b2558003802e650b0b40b10312446038580001e5a500740d90 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 735319298 1250 735318048 735318053
    0x607121b0f1d0405040b0906151c111e0a080312150d0803091f0b010905091305100c031104080307021e030615040606030c0503010b071b090903080606160b04 69
    0x1240704a6070300b2904503080009120812405043d00c51164078050121036055940040c5440a9807400d0b100540042c00c4469205225900703143c490b101178011440e1030f22302c0c4400b0002c2038030005031400055400000441f03840c0a071501580b207030000d144c280d008500f4000810f002e001070b1130018182c048819181b030034501e000e0325030141114455800594040c2c8901c0c0085800b0744403580c00d10000c801e1114203d00d0040e90f035042c4110200c0b0b40060759044201410081030000500c009800c01004401c4a240b810002e1030030020221130f070201040104094406400c041d098420b120701c14808018107000910200c030300001925409038044601142c0a4044e0080070401e019000d1555014002c82040150651203400c0b010155201642c080040f80c2d641d250460171240c03007984000003e402000100f09209211019115081c09184003c1d52017100a240000c1d08000d948505c20300c50321521444103054000391281e0340303c0c40c207880c03e40c6499108201409000340240000781101e03c43d1010906 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 735320548 1250 735319298 735319337
    0x1050f2802030901030b061611031603030e0307091b140d05151509010914120d0206100e01060c0f0321020c0f0c01050324030607121b0f 60
    0x24000e00c0c0c0c140925008084000d40300d41c4000718441c0481e040101100540c00e19400b2680c580b480180c042d03202ea026070341c031500290301c0c00c4006a80b40c411180c141c0b00c03070100d507810780d0000d503c42d031101e10440f02200141420b1039060340c000103401d40f07800d808030702d05080c9180c04014180185013002c110305020610750030354050750f005010003a141404006100c0d50b5044800404401140c1415401100c003070806903900c01c1a03410380c002a103809003006100303181404032400c1c5d03000a240104080110394480c1c9001c12001d50800140d1010040c040044a05550103026106881c88403140d98103012014142d0180000028108001c2d002d850050503c06c1d41c006042c40b101f8038482021030182c902201c080e40080021441c0c0d0f00541881148076080010044100f0f00c040e11401c1c11595801e1401c08000c141c42d42590485841c4140000a650103015092140c003503615000c03e044034210700c1c50212105001d601c0c00c0b4680d44007a034201d044d044140040d654074249030420240d8200140c044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 735321798 1250 735320548 735320587
    0x914010918030c4e020304060e01031404060623010c1424160207031109130c080303100815010905191104030501140114060304110316030b130201050f 66
    0x1d207400004d02c1e12601c500034909120030071040ca03900d240c2003c4600070420300070003200c92001d80541c0c020030007085100d00031240f0140c10f0805040005107890110080c3c22071900440d02240d00c140c0e039150920003c1041c1c00f4141e1014040304c00700901024000001e862500007201c0a0800581000c450041c16400c22a01e01d00c2d4040e0300100c4440d9061410051041000341c42d10701d5801113841110084a100260540c00c032a0043c10110110014500380320754034001419041e00b44001d028690081141d03030040c4401000c0b01c60003940c0d07038035004040032918445c80d00005100d41040e200036610303141310070301c00341550301641001035151581300c07581e2200031312003031600005420545810020f40c44600074200712030081c0000d0024419004492480042c24000e82d0348140150060b0705080c2000c0000c1c40d401803084401100c602030b010000782c64000020280100040030010a0040003a4000811340141480c0e041c00c403002034680c00a0400d00071030511007200c0c2c6012441000f5202c40761140c0c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 735323048 1250 735321798 735321833
    0x3040636150f05070e01170f180303101e0320063109020a09031707081215060901020c040f0b0d0c0303111906240914010918030c 57
    0x200700b9410104501d00c040d180484031400403c0300b0001d0200554020403540c80100c01c00c5045141940d62403226141c00700000e45a60082c1e030316107100f1011010100700660040007591450411503280800c800c940d02c1d070750020441c1d0300d008080100000303401c244105082400b040c01c000c3c02c401100d804501c4a01402d4105903480303004140c5c190b55503452103040101403440f1400070158903100c1c0e070b04206038402e42c0304580000b0040c60f4200003241700341040d1309200844007406464195641c41d83c4181d80c120380c0c0030b501c45d6282c82080c40300310051840013640f4031805071415410048140000707900c4100724001180119102d00303000c43c1909443c0c0c4907100c2d08030000c18a03c2410242d04000300c58000d82e020860101d0031141c1c0451501100242c900540d007048041c1584c1124a60703100005803c8400803070b0b401d01052520040440401d000401c00b0301000d131800910b00640c900c0c0d020710a441a40400c0241c0d00d48111850300e02500700081000325018103000a0702070305da2078000d485d000f009011 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 735324298 1250 735323048 735323051
    0x30f020925091d1501140f0a0f030e01090201021b120a080304020a170a06020c1f1505040902060708091302030403020c040606020606030d12060306110304063615 71
    0x60745002600305404100765481c1820940b016500120310405811054940421001c011102888a913104003400e201c441013000504c1c1c1040f20781c49100050f50095031100010400c40030100c07041a07454070a00f8000c3c0903210080c0940c501540010f500d402c64009400c110b081c00003541103927501d90100c0e10042e08225800c656045203c2e0802209035001070390224802c0c4201d0800003650140710070041505c0e400a0003516003040d040c0e071650000d60040300f0540c064020407188156038071922641d2a45c3d074a4403a8049080441e00030541d41064903900100d100c2c030300c0c0c850f1000c00b50319440162182c5541c040201560341c51484000b074052a440d0345012820f6000104100404d41c0c0401d40c60362404044d01d090040640b0340005907100ca00844003030350964031400780c078480b492007124000da5003071101070005001c03070302ca03102c0c04207880c160b60b0720400700e80001003400308103c194400c45909103115110070191034403910f0302000030485061058100441c06100c0018410712420100114544400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 735325548 1250 735324298 735324361
    0x30705070c0801091103030c120a0306350f0a080703030b090a02070501140603030a030c0e030307081314010c0308071b14010b040203070905010318050102040f1a04030f0209 76
    0x814003900305043c08403102407581d9170582c02e90800100780d5a910044801406100c9241e1207c200d6179000281d000c001c01d03481305000200c59403115040c25401c41102d020108450005000c071028244200c1c00c4201640403e248595042000c0380645186600915040c0c1c2c0d07440c03a0400310040c0401c8003c0a504c4601e90b03050144c050307800d0340100010303440303500280011401203d0041c05401c08444c600d4054104000c254001403107a402804801150f05168490341189400b2074607540012408603080d5600207101d51a82d01d800e0540340041250070303070486000c40c2070300000b0719080c018503009041c4148003000c5043c9034010302803480040000a85100781540787d017800c050503520403481340d40d40d502e03240c51140d40b424103000f124410384c05170b103d0f40402868a00110700034543c144a406910b500340b0100f1001070310a0000780000d100300c149c584412400c0c001076046a00c580d00008680705010001000040c0f80015548581034040725581c90350340c0d5200840c00c981d025840100420824190b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 735326798 1250 735325548 735325559
    0x409080c0a030e0109030c091e0e0c03160506120403020f01091218061b0c0e0f010f1d01090b06090307080708151302040902031f0506010f0503100b030705070c 70
    0x251046070601aa0f100d0701601112001034640341e0190002070711401001d02c060101c21307195040f01000e0045103819031084d0681d041607500700d07451120703050490340098011074110b19080001c8070032192900710010b6240d01d010300041d918450786802038145154040044d080c1030090141d00441c02c02c08000740444151490010200342901440d00b02003800446841404d104d0108034000f51480d0780c903071401940c10150841c1c144465000c044a507044d010402003558011220304900860410212a0369541400140480d02c500b6800c02401c49001c01c81741040041c44020b02d904503502100c00040071504100072401e9841460409505442402d100241312600012002d04403858242a07a25004044155481d4000d041d240002d12040800790f45000d85000e0b441006602d00c000d0807922000c40c039a46940e604403594213224019a502d00030021596044200035003ca01107140162440c034150300101004a160301650f0700e0614003100240d00f4078020001c442150b42c001e4070031100c0a0392003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 735328048 1250 735326798 735326803
    0x7080705190905100219082b060305060c0f090d0c0b220504020a05043c03121e0c14122701120513060e03190206011d04020409080c 58
    0x40c42007034090f1401306040d0308140d2012400d59080e00004610040881d01c0c1d4450003000d07001151510386c0d81072010320f80c40a000c107409140012100040c80425201c0c0f640c2041d5051541c010407640c2440420407442211000c482c00300d07038140c401241d0582214030503007404440c010103034200c03040225000030501d1041c400f4560f81c415011120300011142900c8005000507070041007800400318000b03000038850301e4204240700444560120140034608004001c040d9000c010304800887d8250524080c002e014440704d4082403201c40742000d21100500c01c02c0e0321020100042e0000410581292010401140c400c011220b491a84c08a541c42c07000707600c110031960f10030b04020f410560501c44007042a0a13460b00422218070503180c42c0c11540750540080c010384001003041c10307803481c00000c40e00020000e00c50010000008401941c8480d500c4030607941d81c4600207280c405560040c00100300c40b2451341e600b0801910110001c4c1d002c1d440e030b44042009025030100081003103101041628040700d00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 735329298 1250 735328048 735328067
    0x152b050f06040c02120d110c0703030c12050405010c060209032a0f100c1209080115030302060a060b040b1b0102040305061006080106080a0203090a021504050a08070e0708070519 78
    0x2124104201407000c10185c2c0d0740c90b98150b103080806002d01c4403d82d4080d0a81c080e002030052520380620300405820078505221058004030f0100380c4096604062154848070800b0400b2903003011441c0908010018000d400c40030b40080201ba00001c8045540c0c170144100b0049880701d40381c45c00401000e806010990710100000c1d8001c10191504070a1840c102101c490b181d0781c107841c2c82a413030195403982d500607442100e81400b4803040c480001060301d02441184408003405022500b418111301c1c0003030818401038021813807030307007410380074458041c000e002c48007202d8480344000d07078400c1d0640a1580e034240a10000d00c06502c0410b000081c0500414018800d5140d0002181403680720181138448007400c0c000e003c0043c20020015868141b04c1e802103400940617421200d035902c1300e5000800303031500081200204d200202c4c040080b820041c000314041c10340d40000d46045070070002c00d1021244003c0400c020840506c02140f41c0f5030090040307400c502100ea90046a803280d9a4003c2d100d070700f4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 735330548 1250 735329298 735329311
    0x3010320220e0102122a0703080f06030102031009020a090b0c0c10020a151a03011b020615030a020409020607080d020306130e3a08010311152b050f 65
    0x2d140440707111410610881c3d04440c181214000c05445444204994120031091024440c0191010400410f284405030003458481d95030781e071885c5400c40740003004c82c4020b080c85000368010b20a219019404c0604c5105803a03c8100c0140c4840c3c0c1c4000440b03040030b640e031081c20a40000a05622056804100c1c940d00c0001038801311440007042a00700d90703604a41c28098101e018107400c515003a40580c11400741d0003407035121a040b04440e0390001e802c40f8107140310007404103504100c0745c00d4180c042c006654003c03a00d00b1250858805100400d44480340720302c0081c410b55807252400b045517911000c3e01c00d180d400407111074942280c10300c03100c025481a01d02d5803145c0f51503544002c0200d01f501450080980c99000341480550040080902010722038134103260014007003070740126180c115008010301c10b090307503523001652440c01d2448240705207002c044d0007441880f8942c2c401080c2c0c8001c0b6129050000b03c038212582f40301100c101300c408080c1d02c00c2e4a2a0509080c0510f800381c6c10a4940a00c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 735331798 1250 735330548 735330551
    0x1503090809040f0b12190818061204060c11031e041710180206040b0304050c13140604020403170f0c060a0c0e2b0807060c020304080607030509030301032022 69
    0x640d51150507646038403c40c40e00005e1801c46c0c202d040000d0000b00500b0b00500c03105107a24601441c6400258650840a06c40c070080302803004000034410366004001e8175024600f0038400945903c0707001c0341c50f031195116100d40011415010b4003402c4509007118000c1c0001a404e04081b003561072220f4880c0103502d11460300e207081030b02c14102d5404030b110404059900a1169140a24110004101d50001441900c0da4062402012542d80f1403503403e01910221000c00a03c0201001403c0310310040070b85428001d620620040c40000c14103022011a80c0074680303450348801803c4c1c0d0040081c45682c0e2010260301400c01403110701c60306030300701103886d0029813a04d0020340350384014031110b05c80300414159070034207417001c20410011040e280040d15024003d9070b0700d40402600c40009664031045c20394016480050f0401c04400184511500000300340380500107400d003e2001c99581c0011302001d80310114a1801411140d2880744d00142c1e00400340c002c0708601412a02e5000040c3d0803a451200c09 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 735333048 1250 735331798 735331819
    0x7030b07020613030e0105070213051603050c04170f030a0306051f02121308070e071b03020606100504150305100b0408120c030f07080a02070509011503090809040f0b 73
    0xd001003506841030303c02c000c0c51407a100664808941028100507080e05200c010015030703001d030b29521b01490b40e0400b02d0340e0205140c20580380703460540b000c0b06901c1041501d00b106010301d0360100c1049504403101c5803500c441c0c504803100c8003030411070765502d81c0610b03200c00030740c035018540c06410503802c49400310351000c162204121028108240700100300016040b120300c14642d0382c24100500030300d03c10103492840b03580d00c030a403403458118184c00440301150840c04005c3c0c070740d0b48001400e8400f016913105917145e0b1015035003e0b40e078860180c03107180b040046012a0080d40d04c5201030710b0043c59100018a56448603410240c0205000c1c2c0710b0604e500c18103c400720300e0f0b00303031581102e04603040500140080c10203503055441d284c0003240c2900c16170008000d20002620588040d03d0320a018400c3c82c0e41d03603100c159000c1d180411980c0310034019210503004001c40b19501000e8503040d0403609000c107000e000761401040600c104061603070b1142c0350040810200a45a01a1142c05d20584003241d11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 735334298 1250 735333048 735333061
    0x180501150f063e061b0702180603010b04061d07031a13110301030b1005030a0c05010c1b0605070506090f0c0112092f0d1104020703020a05030c07030b 66
    0x81c03550700410020503182c034542d03d0608440041a06020b40d50034101c00003a80c914000000c0325440c0b070103a111680994184001034009160141c500e5240703040c007901c1c002e010743c00300e20000f022010b40c3c90000300500c0050510703142074000ea00e0080005104011f400c0d2070b101d081d00d03842052026610026241e0001582c0036019100b6009004044102d1150807003d0300c08010310740351584209410310784c80d0490051708d80b000d9009103000e944204070b90712040c034040840441c403040540c417030351007031b4080d06600000c1601d106502068400c207103441c2e42e120242d810103130082c145e900c1c0920301d080b00c01413000891640c13000151040c1407080c1c0a84d10191103009015907108800b4941210581112060a540b50300900c0d210003209001c540101310140741d81c03251400070055120f407200c0141c0c503920352004400c162072102d140c0c090449174100c0a045039152a041c030f4a045140d01e001c0c070b80c0020000b081c075008020002d00c69034440b049a036030300d0805800c15210075236480225000d54051021074007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 735335548 1250 735334298 735334319
    0xc030103060c2109030c230f0a030801140409050f10150e011203110d021b0105031b1303140d080105031906020f1207020d020f0705090f07020118050115 67
    0x1d000f0042c1c07803c00740001d0742440010083c46402c40407400c2c8520000c000001640181c410341e0002150381030103121031198000c00e070904ca42c0320311264041d0041c00255000039007020603141503464000c06111000c0301000418024442e5400180080c4030310a500c000403400058910030031000304105005042480e0a214603213009800b40d06803000380800103214800507621941d000d54001d2400241c01c1410907011400c1c12491195000160003520108c001880c40d680754954481c002e1a01070b1651420f04c487c01600100f442080c071100d00700240c2c543c03118641190140c0a9900b000c018100b20266012040c0d5070340c4c80450300404140c00c2000085c40380f40120340d203110b02603038400280070404241e98140c02503014010261010400303000e468501d8071040046c0c0e101d030b2442c1c0c008051309006c0c80e50181c0f80120070b8049000c41d500c41072040c0003588886c0c110b01d400ca0130304000c0d004603840b2080305a0240520140c1c008480543d0701e45c1d4424408150040c1c420030082040e404113017520380d0f41c80c90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 735336798 1250 735335548 735335567
    0x7110115140a140f030a30140d05071101020c06040c092d060f03052407091412060708040b01060c0209040b06030a050d050706050903090a23090c030103060c 69
    0x121030f41c001d03040b58103040c240b070004411a42d0006007a16006a9a82e580303407601041c0c154218110f20418105400b03103110070228901c140500c0c02d10121541c6400507040403031140c521140f445135103441c042040ca5018a04010900003080c000f90340314042e071020555519011141514214500d0f980000d81c0901440346a140d01e90036010700050103050300e04094459049245200e0159441d48006040880560340e42c002d103110760060074010034250009a41c1c0b20030381c2c6a1700f2154068a0900c0010b64002e240841100c207a420a0b056003a420f40c0000d482009141298002d40071702c40030041403a0744080380b1442603100d5040c030744540c0d03283d1000312000d601004000f90004c0b034850125001c10ba904030b1180c1c0c401c1c801801c0b5402d008090340c1c2d207801e01003a402008040340000c91030340204407450240941c000e076810700442c285490200010032644583c490301d0070403100104180c011000019020381100d401600007003860070640607041055109110a5800503d007c4107034601610590045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 735338048 1250 735336798 735336809
    0x10e0108340803210a20070305070812150f09130201030f0e0f1501030b0103081615020903010c0c0c05150c0106060e1002011509020307020106030203060c0706110a020a060507110115140a 82
    0x399031b0010000d5031301c40c1d69408a4815418043c0901c5030000292840b07004264030590011014100d0505c0c01101a000c680303250006d1060321050302428098035240d90550340b01c1c00f01e0820743c040b9802c031300050300100814042034400c68104190b16403130050016200664803022401c40c1d4a83c1106011750240344001c0c00300a015801c647c004001140444010b4812a0740042c143d112980b05903484208242d42c200350409043d801203401d900d2490284900001d141d45410041445803c5a480d00002c050070700a03a84260300c0c001070740b00705481c00d0080d680c4150840000300300302d5840e500040e1045c4c1148c0744080c0303d140c0c09480002202e2040c0100d1130781c141c44007442c5c2e001c0e074102541103010f0740000f48110215035a61b540000940e404100b003901810a03e62405e540310032600380315017507500082488895403c100520342038075600107007488129800003030000d120340350402c0490b034940c80c50111100940c20100051030100070300b040b8508880249540782110b64200040c04002c3d440b070b1060 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 735339298 1250 735338048 735338081
    0x5100c1107120c2732060f12070e07030b1809010f0209101101020f040b07110603010810090f21082d1e01030b010e0108340803210a 58
    0x40f81c1300c3c18221341205801030f0200e2840d002031410202c211010451038140b40c0070310304254051224505007960b03404d80f0004141c51140e5100d0003060441c1da65051882480c8000c102500003d120320f110354017032000f510009040640a08440c4d442017261b11064492206d82d510348005a80c0d034003003a2084940c4a07102402107040079401400c10341d42021030f402401c0c10782d5020000141c1c203035904070042001e04041d182561315051241070501c9201340444142e40252010030041c400840002001d05004242c40c1004c03a808010745030035294254a902d00800f04807030000c0c0221168041000030790304020a80d14901145c2d16528151080509003010200c0442070400101844070340f2050980e104003e041521610486d00c031003070426480980c001c0d5a050121801885100c003207002a07801803921700c000b400901035951180c100d240c10384070400303044600c901c0720542c9400e129412000400c110015252211081008004508000c0300c24200c0101d0003000201e1100c0907114200000401c40380c03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 735340548 1250 735339298 735339359
    0x302100501031a04060f11180f03030423040f02121608010909050102220806090a0206030f06300114010e01032a06020a02150705100c1107120c 63
    0x40a540f03100b02502c2581e455444080c100000f61807401509607101c5002c0c1440c1c0e070b401d04030029000d00c00804e281e00d8414206030901c1c01041d5030000580301500d02c4581c2143c0b2184510a803454058000c0b007840703400c41d04108841004800a90141080a1049541d10b102e030b500c888a603c080e00f04032009101003403401c801800401104da0000448504c2580018030748045881141900d0455224040b03050005810501450f4001d01c030960300714101d00000c1c5a0001c19034002000d034000203006c0004140c514000036843d6450003044c1c8188064002c80b440c0140000284480300203903460f07600511340c24842e0744503446a91705002c5040311a40752030103003182d08680d40c01c046a0980c030103000c0707011300030765400e850840042d10600c000e00c02c580003010070203000e2060100c102c12184101143c03103001d024400102e0800b1850164181640d400018820741c00e5406580081c1002c124040500c54050007055020a04079101c1d085405203904501d0940c0d108030700e007422110020401c9002a0b00030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 735341798 1250 735340548 735340583
    0x5060406020f160c260d05090f04020304060501140d0f080d060302060318060a0b100e031e0a050705064320040605030d051b0d050403030210050103 65
    0xd0207400742c4103032030b07410514018100ca1450003000040703600351030000030400d0030410407403414008444032500245a002600800d601e081d15844040b20300c0046c40310001c2d545100f0f80c1d920615916443c40200b086440f0b0030107081540c0200803d006414100380d1450b14441c151400c01001d400c0c2070f50240740005040d84036552411141c000c00154400705032582d00101c01644c503080a1031150b5000c01e246140c131144031100922b005409815040c8081c03410000c417030b6640390650072004122190415054040c51600800d24040c0c21300d400700b503008801d24400011034004a0650a494080d20403a8072807521070040005622641c100400003030743c949103140c54282084040c5010711428101c4a202440c000c00c014680d001548084540c110a0759841d18088201408440e1050060381d04001c400d050002080d41d406d074500c0c0f120144072000c2410220100450111900086913005a400c14a1150780152a41d0481e000071000750180c81c0c807130f01c903000d1070f0302c1041c0c100c0b0740042504403130b4503441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 735343048 1250 735341798 735341801
    0x141c03020f070b010e071b0309060c14030301090c0905030c012a0b0709051f05180d02040c05190c0503070210110703210206040b06090c1b150a0905060406 68
    0x1012035800c0042c001c42000c507400840d09402020250f00c08642464415002000d8071b580c904a0040203580801d1440841d44c01040c800c1510f50301c1c2410543e14906081c048802a00a05400c1a520000002240380480d9420510019100f030f2218011242c55204258840c1c4038400100e000400368480b02403c1c03643c603480a26145840c10742e0f8084007140f6103500d085d50408444650100303800c01070400c0300e414260300c11035202c00801030320038115101083c010064031400c018a05e00ea0510716081d4119030314105402d0455500500400c1166140e0314044c0c4590080040c40c00280142e541126019000303e5200c40c040f40e100000d0b515140e40f960070400307480c0702840e000017040a1a440410004410440040514000c04d52081c1c0c0c4032880c0b0003895a10052074101086401c418240000580081519604400103c8000322941e8645014216a005d21020a0100703140b80100c5031510740d0200c0d24080580780c04101582c960b485840241c00e0f20707003d40c0c0041c0940d001d0000a400302c0c04a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 735344298 1250 735343048 735343057
    0x10b031f150801050909010903140c0c13050a0b09042a03062d0e0c24030a0209010f050702090a0903110307060b091602070b031e13141c0302 62
    0x34222419898244101220300c8503051040401c2414005000034075002c1300403517206101100a100c1001c0740c0d903000340b071503185c8182d02c0c0e181ca4012844001e441e109010f0000c0d0003401500d113100303240d06c00880b14044d22085c0c82c454021403601c0c50174007a9080059159104582054030030401a074050100b00a11100c0d82c408050300f01501c0e00400003030494003400b8000c00044104125025901c00101c0c40c480c82800e90b80f01d910700d0070381c0d600341c450700c08140411858001c96a003030103094450444100306601c0207004441e114000204004002c1d56800341001000031382c3d40341942001c070b48c4191402d128500c03001c0c0d4840b030f21000140d0001040d030000c1158901c20700d0250704e4070030303c0c042051031038000a1044070743c9602c07000301c1055070900d40d031f8040d8000480c1015050a00d06108080c1d15075109001b8550301c513400100158040d8250103c00400c074604088800f000d2500c07010107401c0500e441c0007148c083d40b80c1411807a9505002500244030001c0420b08031510b5844081a00207602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 735345548 1250 735344298 735344341
    0x60206070c0c0b0d02070203010608030a120b0301060b070308090606010f05030412110106080f01050606090a05060a0c080711010f02010507020705010c11030a0b04030912030c061d1e1203010b03 85
    0x9100c00c0c0801c0010580024051144c0c19000258881e00148101425542032b41c128030810303030040c44000e580035030215034044146034000c00042d400042d200424050202a04084403104001a80c5010540c0c850fa14503c1811080b05132036035600d68000441d03800c11640440000030b04188003080114050074282140346c0b9250034440c0001c1a80c3c0405400d5070384070392158450b41c105110429074498203000d900d600650460b102c0b4908164100058a00395443c01820700a81c0003050104000340280107078030a107500100349584076040f40c500f0102213074001c10034074002128400d540b40510b005004140c09144140c014000b030354100001120600042c84c42aa5100c0c1403024603e240c1e1018070606141d10300a4507207201c90700d854100074200351160341c000f00322011010b070764402190b0311001e80014507901a8011a500160000c1d14041c510385106640d500d000d1040c804003010100e1010401b1512904252040a2211401d0217820b0100344a0860061000c2000514900342041008041030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 735346798 1250 735345548 735345563
    0x5120a06051f0c050a120e0d0203031602060706090c050112020702030c04052805101d040633061107030b043c050c090103030e0f06041a0d050f01060206070c 69
    0x503241e403685460174070440e0b4180d03a1842c0b240d9141513003550210700c400d1549420b84900142d000c20703a02007992441181d0709440c2110204000c1001c540d074010440c0d68481d0400000c1c400480581440882d0780d90314841c1d81c0c04244c26220520184c10240281c906554000740585540900c0005020107401c0c001d16513080450402c48070014103889240048842c01d00c08000140303450041400c580700c0b116504060301c148812410401103daa1040e042c1d840766000170042240d518103490014403480500d200292820075110b086010b4102a003100100e03030b003135034450340f010314071400b0b03140c135101c0034000034001c840b41d840000e002ca48640400c1c02e000700c40d41c41084401041c40d402000c9102c40006113002100072080300310600a0070850600c018804480001c22945140e070081c1c186400701d030005001c0c41d0345096201260b03032500281d5006000c01100801e201c080b440c081d408580c4030410b00d0128a161101295981c943d0310031050584416400421194462110655048031482030449094 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 735348048 1250 735346798 735346817
    0x15060c01020c0c010e09061306080d03051f0f1e0f030f030e0a2912160806040203071209060b030102030c1c0902220b221d030d0209120d05120a06051f 66
    0x700c00c10895482402f4560b5800186e9091082034040d11a1030003203402c1c0c017808001c80901034089005000012a013680e6008400a0611060505401c1466000702e10000d0040d00001c240721044242c0d00c102e078420350f5416044c918110400c102c0740858020962a50560200280004503a1620710301c01d083d8003003001e0411074a1046401407510484268164a10241041e8204d81c0c002003a00d40042046a0560551410301c0c0010b000314041d030f092016054075000c101e0240301250313101440040025000f035680780761641c900d500c65440035011008072416104051b0701c2c015503120300c1040c1d80c0d0060401420300d482005003041c40041038415064aa650320040d10680c3e80c3c0b4a0012800300e440c00c40300c0d107801100b03900400300c1d012030280503900e04400b002000d8101001c401c0350001d20804100580320400341000c00d10601c04a0301c100c805110303144c2103511880d005030143c075040840031506400c0c1d0761200c4c1481d0030f4407a50701c07c103a0808026001c01c40d141c13140440ca8414580a8036209840 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 735349298 1250 735348048 735348059
    0x140d0e040b1801090b0108090a12031a0a03030810050316032a090b21120d0609020309010603061104060c230a0b1801060602031215060c01020c0c010e09061306 70
    0x1e0b54000c1e80180072803983d80c0e0340078042d5604041c0b030356404841c20300984076400050300d4102008100414250805540701460402400e041415640e01607000d400300c940c01b40c40349005002c242080e0303034850001c94120000212481c0009052482d00084040003c201d0725580c1c841e0340c0e841c0d020b1343c070443d00e01040c1d100f14144d0b510103483e400100b6540c5c5000c40d0101114050100c00d1542550120100c10b0000326000c4c001c1e00024401c0851007415000ca680c0d080c0d00c490500100070540095000c2d50002051106860054001d401680e0280320300300030300b007000c020418580c0300d90301c40c0c080881d240b502414003059290f11040178481400d141400303941040e4840c2070510010001c11a01d650b909414400004c0d15010b054074000a480002c008040c00e101c8040e640b801042d1401c0d92005201000070324407001a1803c0c01c0001000e808161107000400300f59020350428041e501d45e900c1021400386140d8410701042c3c004003009080480c441e22120113100c0b8a0500e03c0d261502c040e00c45000090 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 735350548 1250 735349298 735349339
    0x31502190201140109020c06040b25020c090a020307020d03020717070f0606092007020a1d16020606010c020609011701060504050a0e160513050a060507140d0e040b 72
    0x40441540e03000280315003516416a0761030f07506070007113944d2078410b0160385500c500004580c3d81140e0861398071509681c8070150386c00d54520b000b02c040c2203034140483d00303810a600058500c2180074120352640035980c5410b9000124042110b49400580c0700d900d080d9215400381d80109085070081c041e24842c502c86680c42462544801d1045400a4070820010280b10383c1d0302c9620041c0c000302da014400080341400149024045008400304041d00151030001c40d81c840c480034008000840d514110b50381050000481c2c918120b810005100d80246440354803071000c00c0d42e5105480585a003c000010340e0284012500700000e12414048601843c140280c0884001402001266a030715034960414050115050450340802030b840d002d00e0034880b0403c42c1d14016142c03031009240980c2c9440360380350074101109480e4042604480ca2001c04034036103602000518041c1c9c080e408072021420320f0103150b940c49024660f80c1c030009500e403a03c0c20362468182c1200e8940c00c0e005210304a2402c045100b4038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 735351798 1250 735350548 735350587
    0x30610210c11012301050609010306050409080324010207060503041b08160801140a05041b1409071107230405240d0804120804090903020705011413031502 68
    0x80440c800ba0300741e401c4201c0034040d440140200a42030180003450315040d440519041c05417902c00d54001c9407190569210380e0007003004090040060006810f40d00303100c80c07194800c2d0340d040c95032452520004581001d101c2d440b0034500041e4000d0900c5072400100300c07921707000034008a0305042d201d032408001000980c001e5000e49121030260001b40710b0401c010394802d1182e4062003807a410715611401d004100b4a24951250340782e40c010600e5030b124070300780c400307010130010000d0806ca400c10701040c020b0b03203048695925001034901d400c0544823200141ca02d01010321220342d40d0341c05a1810b010f070344c18a00c030f4980400c81115010b441c8100050024040d24012201c0c201041c0040610003106065940816284ac005465001c50204c4c01d80307461507540705502a22201d07017010802c000401c04200c08807402070021810030856001c0a150094861250b442800c3c0090805445401d40c040c8201c212207408482d40007426110f4a5a40c900c5102c0c6840301c0340d0b00f0100d50038004810307210184014003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 735353048 1250 735351798 735351821
    0x40b0f030f060117071a0903031204060b010e04050c09130605100c0b1008070303030b011202300c070b040512120a0f0c0c02091506040b09130203061021 67
    0x102010741c1000740c6902680b0450444c10140c1d44900410410507200402405014204000880e41c03160b46002082c0756126126014148044003401c0000744907103036102151410b801d81c2c0b10748a0342c0042c0c04000588100b070710030b0a6210803c0203c54080d103420250038003203200d070060101c2c0b0150380c1c0300096201d0b0701404004020507405074103d400c12011211441d40070a100048a0340c0c10b060041d06d031b07a41c6060780401000c0c1540c9002d40c0c3c0680c2e01031024107101d004a41415580c0340c0030402c0c2c10748103d5240820610356518151054000902030b0300e85403160042401d100d00304001d50312100403014000d00305844034000c4a08200715010854010141c40e030402c035150034503040001c580307000c4450104d40074600c0c501d003038040724003940e006c002d003081c560b0101d5000b0410385034101c4c3c02604030001c035403041c1e000700005800200303911560090152110300700c074060306200001b40c2d040e040c1c0c03104071042d59224108800103200a405442d0030480c0048512140300c0c900780c0b101320301c0110b030109c4046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 735354298 1250 735353048 735353053
    0x120120702040e0105040b040308090a05060c0403120806030d120e06010603050f1303020d05071509030906020f1b10090909030c060509030705070b0d0209040204120b0c18040b0f030f 80
    0x300c00660501d030080300708035000c40000300203034a8036032105101100c0c094401070800c2103840c08a00351a0b01000403806150308002a5400313401c1410032403440390b20500c41180c140b84010380c0c0304400e034062007030107100e00c8028016181011088400325002d41d5010f0350400ca0a0f030b10184a49002d108014090103003189480000f141c6c14502d0500c041298002c002c64031048400c01c48000103070b804a030b4503d5043c8030b4101b164076402c1c5d601c0c2030540c0305000c450b8800c505180600e1003041c0345c2d00c01d18682c1160546e409540440c00241181a11030103c10f040c0360030801745901c2c40c426810310760f10811070342d20b2501d441c00c8034940b11720040003940c0078031b50b040d4001003100d803c4909000c80c6205030398210329001c0055207094104c0d038403252034001d9489810441c480102d0104005c11854045032222000200110365031a11207400580d10a5103035000e492240c801e10004400a11203400c80b5800303040320012440098480007008050040c0241c0c2e10b8001d182c54031841620b4408101c00400c16941401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 735355548 1250 735354298 735354307
    0x10e010606140f120a0b03190209010f0e0c090a03020603040b010f0f030201020d03091103071d060607020d060b0102030403150b01080604020306010f0e0604080f0f10020711012012 79
    0x6005041d040c03420780e1400c2c41c403410080d520314400b4039401c44080c070003a40003c0d545985e5202d041001041300950745038150060709a03074803640c40d0040741c8084030f0741700315140d50099885032200400050f05014500300842c0034808507803452118405001141d50041080c4101501c2c1c5d4040340080d001624103e41214000700180718184803200d20034041d01040600b00c0405141d40c000035905e100103243c10040c542da483d03501c001d228a8803242d16003814050101c0d40e180c1c0d9140841388107041c8100c2d999018452101c0400d48519002c1c08a50000ba001448980320f6081c2e61a1a0b00500342c5084050640c031003017000000280c0400e42c46005085060310015502d207145c800586514001044070f4426441041000740b20b83c0c00c0103910044c2c1c1d84c80d20300746040c0040d00002c2806e51080d504a00881e03c914142e40d1300c045030000da24200103607148159001d040c92855800b09a0042e10320040a40003804500c05071940308440391460302101030401d40800350030001e600d00300080f00c602c1d8841d035480081e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 735356798 1250 735355548 735355559
    0x6090628030b1005041206061502030a08180307030503071e1e0903020a1e0b0705071a0702030607080705220501020c0f03061302180108070e0a0203090d030c020f010e0106 75
    0xc0340b80180e003400c0d100d41007031180038000140944214001c1201e004400c0e00d01380c080c05940c2c1d2015024014504ca80d003020103a048000e0354070b0b00f140070705000251800c00040c2e9400c04000c20134100398200401141060b0741d96900b620650001444903042003c1d0409140703031040400d00e40c1452030a59101c80507034902415102e0102000e0703c0015042c890301000810050700d80442c2c01048400c41f80d40710b080030340903080d0114800404e40c455022444045501c1c0140000880d90604a4030840021a960051010b445801d802410340181d456040f03c8005880c10340102c070803903800010f610f0002d103003408006140344a810b040701d83d104c0d0354015802c103000d00c2d40c0400c40c2f8507544c0f0040b42d424030103005920000343d81e101d00900003400c0701148250030046403a4401418910412500d100d0f40d250f841c1e02d000b643d151918460003030b110048001290310b0000301d108882c0280c0345d00c0d000d00b4142405540607000f4141000c40c0c030086104410042e5400c0d007013071081820300150000045003440c41e00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 735358048 1250 735356798 735356801
    0x207260318030c0a060b0a03170c0f0a080307030506010903080304140105181e24100e090307120e0301061403010b011e03270f0b070504060c020609062803 68
    0xd00008140d50007082543c800420004200440030b030b100e1030208a45140030f010400011440c0d00062043c1c12640c00380c6a0300300e044010b080001c00034001c540002907140c00960b5078045c0d030340d00501815400c0000c583c54a00ca5005180e001c041230520106081e50b81d0ba81d8407903507008031401d0755140e15149400c01024002c0c0a030f641c100928910014190050740c0704640c9828000105154005106a01206110040c8405180720340003400041090380808680311102038110303983c1000304070855000c203428400c00f400030b014080c0040254103003022a034501e80c00d482051136544c2031084020041c4030a50b800d0250001801e0f5520007038030046098401d0509481050490324140038a401c5e04038000d20402000e07000020007498003080041020001100c40c0d0000e884849501c05507003c2c1d1410f02905039201841c4502c10b0320001041c0c3d8a0304800c480030b0145004000000d0541c2a83c880503181400c003a0220000090040307181400e1a95080c1405104001610111303024074505000346d50103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 735359298 1250 735358048 735358081
    0x1e031205120f2215060f0e0c0703080f090a060e0c0406050a030305190903050102191205040203030307120b0307080706020d02030414041802040f0203060a23010302072603 75
    0x6001059081d420481148410300304059580e80f02e05900854600a0041c2000741c02d00103144a042003189907260389060804109502502e0b8040c0d8111b000314080c065000c04464805402d0383d9242103d80310502000070300300024201c080780748103210f0180003180c0c06128002403030700240001c2050443d41418002a102c4547c003ca209070340b01c40d030410119400100702c45019518800300c816252800600380c900301010381002d806907102144209001e503004010308910740c031035100d50010300c5428100c407098440c21500250560024008a122240151400c401840c10644085081c00f031140200e4500400c5610403d520791020500308680d03501444004074045803840518501030030324802c3e1824001680203203015076600c4290b10501c110780751003468401e500820a0000007500c01031100690810b40e0b1151003101c01c001c000903000456400714510a104181c40b195400c01e010054009401090083e10802c195500b05040d40002d440c0350381740e40030308040301611fa046c849800c14a481c403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735360548 1250 735359298 735359311
    0xa023723181b0a08180115030b06030a15140f0f150607120f0e01020a1e020f0607080430021306081009140c0a1e03120512 54
    0x1042a894101515003007000d1001642001e201d11150712040e0320070096100d00c290b107004101e00802c0f00d10000b81c1c41024a406140340110359000c44550008503422241000d00030680202c3c0380702d0410000343d0a107403585d8020f000a003075442026483d01c525019528400400e10955500c0c4107400e0001c00703d51101c0e4001480c01032b09541e1785000d400d006a05d14001c0d21b810690a2889440d141c50b542c2c07101220741981e0b010355801d1100070344040c041c3c8912805954031001c64406440004503520008483d03c020341c01c0b03040c1001c6400c403244000044075880000b41d0700000700708580c205584410380200748451045c01165660317481c1c5000d5034659180091021078080346c031044020722100076031400c40503540444940c1e440c550729110310700c018403d90740450514010060703107003c4c88180c3c0d401000e500340110300d462480c802103003e444d1500c0c540c0c03040075400485400180072041112444c1b03d41c110b0b015034076805664903502d4071416481c5a420003400900002052038400c96000c51240d040380 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735361798 1250 735360548 735360599
    0x1201050103020d140a151b02240603010621050709090804150216080a0212010606050a08070203090604030b071d03030d0e030706050412020d020c01020a0237 69
    0x50542c1d0003e1041007441c03c0142100380d1181e1204aa903c003400100d00c0198003490f24841c41e00580d4080f409048910709400f40ea203082c85036560000d0000c5030344421380d01009946e0300e8299900214049e43c0001400740c0d030b0035658520b40890010000710b031002002c070301c00c003074000900b0482c03428900e400a40e4010f01c0c00142001e02c02000500c90300d09803810f944541000c00e07035074010340c00d0032450001c1e904400c004044d00d114001400040205914102900980350350f5640e1207001c2c046400e07130783c5511600c00011010414502402d10401c011604110244188c07840d2000703d0002070519045600180c5000c40e1900074010050382000d404c0b4164030317440e168110003403101d10000e038980c06030f12105100c0c9516201070740b010401c00c2c0112000300354030040401882c2080d0a0800703a00d42150740e40c1016201d4520640316075800003407e00c101d40b0059005141510480e03091000900801d141c0d100c800c4402d5184098071404401003038140c2c4441000c035034010307142162504001118280a03240340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735363048 1250 735361798 735361801
    0x1614011506180b03040821190203150405040213060602010501051c032109170a02060f0f13060e0d02010b010306050f0a09020c0c0d050d0e040b030a0327090209120105 73
    0x7a1808401d0011988800b1655891769164180040244941081c1c5c51220610880c4103240c0d04904410a001e07150045c174420b0701030052590b050403844141c1c0e01c841c608100f0040031045140c150031a41d403152000d00b40d1111000c00c8800390050b11030b07940148025035110320040c0445d05100e01024001d015240008240e0442ca072006003044801110540f48160035203c1003a20700721a8014400361fa501c845000c2c0000c0045d0140340082c0c000d004a400103000d1100030981580201750350340d0060803c0c241008079916510060a950500000201d4a264640d100548441401e02c6048509003d03600042806416032000404544154209600c00c400f45805002140c842d021000c00365058811700681c1c420381c1e10329403446c114400b01101d50214002105d001004004182103040d400c0b95262005001068010070040c0c0c1c08400d9141c1c0c050b8440d0843c400071034403401040719201c0d2909940161100e0300c694202212500b80c2154907020b80005000079103040a09202c0742c91142d04008100c0b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735364298 1250 735363048 735363077
    0x1404120215060d060e120a0306140105040510050903100f0510050a1503021c060b04031a07050f09120105090f100203090604170d060906210b06061614011506 69
    0x16a5000b00640100e95921600342c2c0c5c0d4804100c2c0b10500c00340c1030b12aa403a0a540700008014103994080e52400f40551042000309502a10075681601c00081490740244801d5800301c4140c0c005004856152003002040c00d0050b60521401e2041c1c14501c8010034140360402c2070111141d1690b100d90f025a00154041100c5241d2170f0306580403140b2890b001d60f036001c05010303070280c0116154018108514009000401003010002042180d00c01c8130b2040303411401c3e803418112108102e0319000418410020810140c030390200501203000000c0400e1070f01c040c08891942110f204507541c148680c03014000c592040c03001c01c50140100390b042c40c02e51851401da030000d929040081d00041c008211800d6060598020350199000351451420412520740d5810894010f8845403007407004040c2c8082405c010002d00038140110640c00c90050301090300c802e000e11210b5407203a000124961b0048030344900280c2c85816a100c609500e100210701d4803040c08541c400c50383c1c554481c5060041c082d0030300c800e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735365548 1250 735364298 735364309
    0x52508070815030a0c080c19060c1707141024061103040e161403060f06090d0605130507051002060a051008060a060305100902060409020904140412021506 68
    0x180100c001010460021408000c44c0c50600c0c006001850b03025900000f0802c1003000401058440044a60385d0400110603114401c480a6000e50000030720541c42c40e50109980600b121003084440d00000d11342010b5407903088500203080c595060315000680d410070303c404070703019058103004140d641c0031304c1c81040030804204100c10310404062200b1198a680c4802091042c0c41c0102840c0206801514000d00b400a6450141c840000443c401d94005403441500360181ca102c1d040141004402841810070041d0030b800207120190710844c0b81165500081e00750141500840c039102c00a4010401440d1040c00e10001ea00a140a00f003003004040e006540080c280740c12100f5400b00251070349032140c0144000c84590802b5000e8862803051014201c255030240301280d00070401d503007405801204c43d509884002d000a035100300140000d00034900c903940100303030701d00009000180e9010320a138400070554045405440491081242528494061202d5030b500303100c011340c28000d464904000759 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735366798 1250 735365548 735365551
    0xa06050105180612010e07030605071206031208040519050718090c12050a020a06120606020706022a151806031b070c030203120a1e0203160c090525080708 68
    0x4d103d92034034414010510b6003980a1b006c0191000c0035500066101c2c20408040c2c0415a030706800120105e20340000440d0701d10400e826a0b5200748020381c0410b1294040b112b080000d4401d030b40300d000b00e038a5200c0301102144081c80061141000d46400c9291000354000340d03620704840610a07081c8041c400005512600e140305072603070b010000c4842003071414a103161401962009401030070408000c41c0154022515011901c0c9144c014068291141e90803606c4082034880c05003d0783c0803903200c0540d0b01c0805139603444076842a2900190707106540c0024035545015548103241c103c0040c1102c032500349140d881000600035500c152031402c00301c03103510846004c105030004424000c1071000400c80304465140c02940c000301125191070003200c4005869214114100c0414450341005040365a00c60b400e041020701c0c3e8001c0d43c20510403d07443c516012030203c0031241c0001000010401540602c50140251314407448240200c408602c00141c0c03082e40e1866805110340802081141903009800702d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735368048 1250 735366798 735366811
    0xb03150c0a050d02031003020909010603050d050708190c02120f0604060e0c040c020105220803010621020c1608011503110a1a03070e0613141c03020a0605010518 71
    0x140d6490a440003111940a081d6102105134000018003141e00d000b01141e4066a00032035240030581c076040b0303103c2c3c201e03189031100505030381142e1101507849010344040c045c514081c4444501c0e0050601500301c2041421a941010440303501d0500290b042c990b902000b10201600101000444070f410a59240c000a0000701900d813180010941c01c1c906000041c01c00e500900f05100034140703020043d000c0d140490703288240203d0f454001c880c07401e0101d05078000c66080fa124038a141d0901c0303422940c0fa40d840340d9050841d1300c0c2c6140341b409007045100900c49441303000c01509a1519440101189001c907a02100280e030504001c070540214402c842da044950101c40f81c0b0901d42c102000c07400098182e40802038448882200000e9070400300d0046200710fa0340d03616400b9206a03c0c0821107140540340183ea00351a001d9018000004002c102c2d21958400410504040c10102e510f00c6109003003120890050304001641d204010382c134006c01c2c1c050001164582d0340c0f00c4100d0342c00c00e4010b4008007079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735369298 1250 735368048 735368071
    0x9070e18010e0724021023041a0a0c1d060909040506012603030a09030908011e140108030a030b041b110d0e0f1507140a03021213031407050604090f0b0315 68
    0x1503600824864800c420040340d00140d050724181c09c1c01d08404d004086129604215000040c07500c220b14401c0015010654603000701404034840580f510590507005681c0100c0304021208240d50b4103601d03203100724801c40c0105140c0d81054003082c0324400003045000da50664001540b0f0442001c41600c2d80714030b0802000814801c076040c00c60b80c65155902243c030035403902070118070741406a07004003a10006000d061140f1800c07140e4600240c8004d1013000c540e49c0040c488030100e14443d130032551003480000c01c00b1034141050682da1200c1140c1c0c11124020038940a00d4414101d8103000c00c1c440c8803c1800d20040c50403400000c100e01400602d0050301c00d24421001c54401c3c1043c201384d4828a800400c21500da80a0a07130080d80e0751321031403050300584989100741100e41418400c80c0c06264000c40018941451a9900346d039200d01210f82400c0d81c040c1c504080742039180c0202070070041080d982c0c045180e810f0402a44121030400340f540c3d00139000714050500a1211100d0540c002040f64607 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735370548 1250 735369298 735369311
    0x201090b070203010f150317040308070201080a020f0f0306012006010b0f040b0f040305060a020f040506160501050a0c030c140a210204031a06060309070e18010e07240210 75
    0x2801050f0920750804170516080125000d1824010035609a0707100300b00b104402c281c140e4515500340154480188000c40811200b80154894107049410403081c640144c240030440f241400c003500152802c0c120150003104029056034001108401442c0c100c1c0b4145504c5641000725803100ca05014100c0a120300003500c03100d444400d4100d034010051880b2641d120504040b202c522a4450b102c1600c49209800118a1b440f22501c00c95402d20203289540307181524000901030a074000c0b146402d080c1c4004010103010540c2170003194452000910f000544012003803000e4219501d4074040d008004000c07054407810100d01c0115400c006050504504400340c4007100c07070101c14820b10380c001c07490004c200001000324840c030140304d0440c014003c1c40103541d2401449014001101c004010303a002c42c104200a1500c1d4001c2d0341c101003071002c5e0807081c40c0c02440e00c1d070946283d0142c00d415588404020032048005d80c2c40c40c1e40400704000b00100c1e00044032402562507080c00307900c0c401c8903607494 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735371798 1250 735370548 735370553
    0xd201303060c1106130204050906070f0c0201050c0102030f01090c1d091b0705011523011202090604030506090f120a030506130e0d020c04021c0b0a050a08030301061b0201090b07 78
    0x10050900300d41c2c0f80101d851a141801554000515110040703000d20708020104079006804140f66100e0315140c1d0b10100382030300c0d1180c100c402081071581a418000d013003051400015080c0001c41c404c0040200c1c80e41ca55240c44040000c5610301d4100004010841342441842026030040b00d80145045030014069181c1d4409030681130310810307821030390b00000106ca00c2004010340202886102c0600c0e0080700c995598004040c0300902220309184000b01c2940c04200d40c080c580840901e18512001400d140413400410002d9010390000d440d1607101004010809108000701300b1124000c00250080041c00d40c001a09400b03180050000d140d00c13440080c0e81a160030f05508610444240280000c854204007103444100340c0c0130420050082c2048900141018000ca808450603507001641d58040720318060020902c05d0401a40101003d1000a040e0388400040740030388110b40c085c658039413609402400e480e140d15641d0300c2040c1c807008480b01603030300b0103030b407d045402001d4001e81da6075140c03 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735373048 1250 735371798 735371807
    0x1204021e0f0f0a090207350307031e062303070b071509060510091407020d1202070c0608100e0c03060d0f050d0e010905010c0507151101020d201303060c 67
    0x4e42100d40c425101140d88800d00410100003804a540d51090b503143c0d9040003000042c44000b000f10350140c0804101007551a442540848011324041d040c00405c94041d403050350954806501000c410b85c1c05074540401d58074100d070300c1c8a40c0740044004102d45441c204003d000f90040c610044c1c00d1411030180c00e1400c04072500440b0f82c15510240420082c07070320a1700060358101034018144ca0520f404141c1c1d140149a15105000308420b070010041c0c01c0c500b94049600c1c0f1041c01e44003080766001d00c409800111240540790180c0072a848218091030300c2c2c4014882903641d6400703050410b03400710602140030091001c5a0f08882c065910b1082020a42845050240c4118000f840f030300c60a09100d8003e58000d285c0a440d280036a1610342c0715949000444a011803d14050300e940c01440c01080101c0d03940c100c2e5011441c0c24140fa200e160f80b4001c0c40c50880e0440203d441609444000c0300d9407410840c903080010620f040000b90600c0c1c03041084299680d00cc0c0001010555079462900d82c45018 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735374298 1250 735373048 735373069
    0x1060f05040c12151503050636040804090c050708091003020f03181b0117070e0901030312060603090506070e1c051c0e030a0b06151204021e0f0f 64
    0x10380b0305004c1040e03810b0310540300c00401d00c02c0311450254000081440d602c41e004031400364100425140180004d41c0c50441191a0b07505c0c0d42081d42c407a03101440490100359800c0340300d14003c0c024581c540340b8010145080d6481e900086080000c1040020002044101030b600200c00558041c04084520303a420360092280040074080c0000210030400c00441d145081111a50101c041d03d206400d81928400e9131207495203218080780c12421080e00302c3c060084141d50201644c50300e12242c84200000c03c07003490782030708250005030180408450640c80d034002c031002800306140c00c102074001a02c0d00d680324080070740320400704030703160140104503a19000200924500710003807610401140c90f0ac5940c825179420507038503c4844e005600e421034001c1850f10400d000c060301a2030103909660f19284a814010701b40c66010004007902054242e43e44040c19075400030108903c03240c1040d004200701c6c455500040321030300310a624141002e807600b84040c25410016203010400742651800505000340f03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735375548 1250 735374298 735374327
    0x40e010b0c01061a120438071e0e0d1502070320070b030a14010e040b090607090b160602120105130501030c0e04060209120d090801060f05040c 63
    0x140000110300d0200c824001d00812484100800c00984d0751400a4607640c00d082d072000200009021408450003c021119409031069202e000401205800215860b5003180d0400c0c01e07090708203034030380485101c030306858118015040071a00c1c0c0c16059405120b841d49610a10304110a462268480b9210503184544c0d05a108260502c3d840041078401c009410195042e400558504c8151280400b6001c07481e00c90708144001e00388035401c1c41c0b1142c1c071030751000c0c000a40003660340e0540120701501e02403e60180c441685c0010843c1072a003080e841109001c6d102c01200e81100051141c2141c019500d001158514803d458030b910211008041204018002a000500004500740c05106507190581039420895840030100015002c803002c0700d0003404002c11780d4148850900c4001c2c0300c030a007940d00074403034040949402683d01c0417420005601c40b50300f445a02860a081d501030700911060041e1401c1d50080104619141c0c40a029200910419000e995640161010203104d0b8034076040404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735376798 1250 735375548 735375569
    0x30e1f0201051603060b0403110d060e060709090209031c05040b0403082a030f1b1b0907030209031b041b0908070e0106120506120d02010b121c120204 66
    0x20050940a03000e03040c200c442c2d00441d0811822440481d029101c2d4400f0740380300c441464142070469480a401d036603283e40a0350700c203a8500301c103400038455008008403001404094803113804d20399405040da2800d60414002c05005010045290700c00040308100c42c0b0448001c4403d050f9444400d0701d0030b10039900b10300d020110004e404000c0c4440c00f0010060b007200c42091040080101912200c4010300c0f00e80e100040d042003288420340019000504400700706d54640c19905148800d80b54600640c40d25200100038a44840700454507000d10305c9507000a0300d0509524281c2c0500001e0b0321480c609084c1020740b140d0090f0040107407035660102400d04c0036107525003e52040040c000d40594094402c61031076128820021800740c0a1401e6541201c40c0c1d0746900800d03030402d0601e4405808002c01c0107070845c503000c9030082c00b903000b0010131041d8503803a00001011070b4000c0074410341c86248014030341c2c00da0040140604e19034034164400b0600c071440c40c1610600c04200300d02400707403280740c3c00402d001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735378048 1250 735376798 735376849
    0xb1911190c1223030d18111f051e04030c030b06040603080a27230a0f0501180305011406040c030621140d0306080f060103050a030e 58
    0x2406032490350380303600c0e008040e1808865034a44880b82c0038440300c140180000700850368290204000b10a001c500d10780103040da810803890b06588000c4032025202c074000890b1886481c01440f140506401818000b516544000903200c05141c1076039010f103014404120340040c14040035041c0225405c0c1d11108000c680e9901c59403030600b541d890409000c182c035a8201740e804210301d445d00c2c0c800d0004a0307a020b0a0981444038441066450f0180d483c07001401758011041c600c8a1303044006d1003000303000041900c3c0385a40e1054640078600c0140240c0ea4014a0210411300000c6103c6800c2000c40c3c900b4a00244841c03203d8000c140c20308007540c03000b4425824200e55170801103929201078843e001c260b60030400005002d404034151021482034001070f800c101070700284141b00f04140708000d80a400c45400381c4440c40c1c880d6103804461441217000075542d820a02c010b000a200ca0403100445000401e200c1d411030b100c1d40d8a4007400310008060051310000030b00c882d1614001003203e40003001845488 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735379298 1250 735378048 735378073
    0xe06040b0d0b0324010e06031f0c0e041e050c0705070608070f020d14030c0c060f0103020f090c04060509040605030d032a090911090a030804050a0509010b1911 70
    0x1034105910514031900541500d21014000c802d030f06007a09100713030668401a440c12403c1031001c20040c2407650140104040c02d0744040e0004086110954252030003d241070200c0802007000e441c5060f064865820030800d6040030600010003481d500103004001443d07220b10030003004504c02e00e0002030080c0182c02001610540125203941300e1600b5131106142006441d00403a191100c4468002c08240091000392642440c08003030760340080c050298503e00300c2c220302d0103450010121412403070401c032100103008605100244444c14001924000000c3c24000854685030203603001c0d14042150204909050b40d69076041500105005810784030310603210324000b40640002940d11400702580d600242d5540c004111040c01c42120303941c0c29640600740541c4a01910960750880c0f0180e03002c0c48008001d80c1ca02920400543c883d6605d1607840b450300040c03002492056100d1481820480d00400408c003494080f103000709404040510390051800e815a0803240c0320112021a00c07400014064 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735380548 1250 735379298 735379301
    0xd0b06210a0c0905011416140f07060503010509071124060a061403130201050f0f030636041401151802310803160b090109050d050c1227010804120e06040b0d 69
    0xc00c1500c1070141d9501903125030f2f00740d90700e110038815960810841c500140b8194490a2074a26211030082910503507200c1040d84502c8020354500d002c26501440e0503c4801d24007940401c00400140c00c0002e8400d41c1e44090103010f010050140852005040072001107a1265080795180c00d082080d503174442c460f0b40b030f070100315420032107856000301d003c0504410384075035105209411502d00341c640ea204850160507100d040ea0003400c1140c0841d03403005c204070b259030300b8056490160b0f011420920360307500d410b083c868103640c1030f20340c492103a104001d0000c42140241c003541c401d0301c01c0360244021605009000002c40e4850380403a41500012a010480c1102802400d4460b0700900e0000b0f555214030917802c0c200d030010b100041c01c940c8081c41e040985c074028001f42000c1034419096403042010800781030301b1075109810702c01550302003044488400c40c5044030340030b42c01c4017885c00c1c620500d000c2c2e488508544084104d041404040320030303c0204d565500860b40540300000e40c15864150103140c940 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735381798 1250 735380548 735380563
    0x904240204091e110d090201030209060d0b01120c020a02120f010c0e030f1f1107060513060c030902090403032d1a090c0d0b06210a0c090501141614 65
    0xa200000070b0750302c041450640c044c08003416551191245030003000ea03604c000502e4854012414181c090005001c1c940d903000203850b8011200401003445160b4100050054809110105416181c0004002c0f202d80c00511001c489074145c514404c3c141307050300420b1500c0b12003c884080b543c01c040e0a05825540605a500d11003020b500b20344a050703000c5040e90f00c0d9203864540311204138411321440801c610a03009140f1b24024506050315004107500c94006944e000c03210340008fda0101800b00c100a003a00c2503000c40d5007180307010030541310143e0004000000252014080507103411030340c00500d025059100340502405c0001c120b140c1c448207040054095903601c954000c41250010ba103e0805943c0140704060400d40d09103040c038800b0140c0c1c01008104e612640100041c007840b640c81c806c8185043c00d040400b031161081d1f11b01410408181c40080031710300108400e8600c00c00550760002092490404140f0080f51030307500211042401d10220034002d06a0f01c0b4000f0f000101640126008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735383048 1250 735381798 735381821
    0x70f080d0606140c031903090f0602120109140703050603010e160e07080c0409020c030f030126030f1824040e09010c0f030906060e1017060402090424020409 69
    0x450f00000d408000074018081c40c58030b40411340003001020160400c2694114691169040002c2d090000b034840c01c04c041050740045422540c0054200c030280b95080300366004018240c5c041c0310955009103045202440680340c40240754450303000c030f011540c081d0000c0340b580404000710354082000b100002c12140c81807148464440c4a540403814051103945142d00c60101104210321b01403070a01190001c0d800000343c01c41500060000b0115a04900c00850003401c2c00b10800071004030200d01c4c01148510040260a5680100903d948544520040e9000c3e100c0070702801101d0780c8802e0202c3c6100c41d00f1070603c90200c1b015240075425030174102c00b400c1070724040c0b8180301c0c0d030760340700c04c0c40608031800c0d00c0f2580c0105400141450380300f84250000103030181700b05c00200d0400e550303030300b00324001405903044103031416002024004105030482074031001d00800000c020754105038021540b20f140180c0040c1c1800e0901c45100c1960b9011358002c5222950808115691075a03003007414024905c65107079 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735384298 1250 735383048 735383057
    0xf0112090f060c02070e0a062601020f04140112151202030111030a050709140901030609031b03110c061804111204080403060b0303030f0a1a190504060e0f0606070f080d0606 76
    0x49000030f41f040c8a10819505011588803120150151186080440000001203990200716200145070701d4400390005112504142140b00700c820009000101c03020904000141f62202c8200b032113202d20301d0b4004480e2800310780e01403c001400400d001d4440110090604a400000e00030846103030790003144124031a40e41c2c040043e0b2140c86003070000012700c0d14550305c02085401400894001c1d07000c120760b503109003020b607150344040000300d03000300a0b07000540208403452003800741c10b14240b21b044454507044a0951418000c494001803d690284084e4010f6a0b10f480300c0406100c2c000441d100300e00074000790300581c07030070307203002c40070340e402800212241410b20032020b0b07003030600100303903400b8405100441042d81c0c1c615211b24010626021200c0c10750440c0d00e910b64040c4c03a0900c002007602e04070105001c107242000284419100154010358400c1c0720401042404103603101c0c156003029044034210781e260541e0618103503a1411740b001030316680c80022900c180005951060013103c0e5203445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735385548 1250 735384298 735384301
    0x201030605030307030e01201e010e070b0f0a0507081c1416180f0b030906060a030c0b030c04030b090109020f1c06052d01060e0f0112090f060c02070e 66
    0x1d040e02d9000d1850000d000c2000c0710f42024156000d0700740c80001102305038495680b1104452194501007403480341d486030003141010408414800e0150600881388030340101071b4245020110300390381c8281c0709200fa100f28003013800070b49188907000b2514034541004410741c40318071265600004003d640803d6920034942020183c48442120540344500101100c4c3c84d00c101980c20240c4101c000e00c40c403c40191049400030407031101c0b41c24484c0141066440b400c1c0c4034640000c41c41e1800e01e0180c409031180c0d540c80c0701080010021030740002601c0720b503680c0c0307600c984400440400b18000c0750002041e880c0d41d078081060a040543c46020024000c4030700d00c440ba151802031003101d186407030464102030740d031381c02c0380010440c00d400440d0040481c3d007501c015000c500f403c04030200c1e904e4951a60042c2c0640040000e06c1d402205040b50a50480b21110100411000605825150140200b01c9038071001c4c0d003008e02841c80801c1040c141c0000040c0041d014885009403910064003c40210f10342000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735386798 1250 735385548 735385559
    0x2040819261801030c0504090b0a031e03021006121b09051608060a0f1203050906070c15020c030607201f14090c0603095b020a051b0a02010306 63
    0x505d00440074180c840503d05810119500d016010956066412010181c400800034400360801e90080c40f891818011050061038001c0c144200c50290000580c1001c00034480d0103182e1440c090440c0d070016250040e003092880b40891042c855001e032584514100030400c00090900300400945e2040ea9030030050b90307840c0c0402c40580f52038004c59003008088882848142414044102c01134080e040c12400c0c1450300c00064102d030b00c81c0c5000c842d80074070345108001c4481141d040480b10039490001d0089903d0000c0804d540b2800202040d040090703003140b0303190100d00d9141105a000c00c0800750350808031031180c1c5d041c0300741507070540801e158502220070940455000c030075400f1302101805041203132540010451a5040504440d2440c043c81002c0c40d000300c41c034408031143c41240744081101c07401d00e034503030502c00c90a140407624154080c010512180f1885406500351103004000580b1825180700880f454000c02d01d288a001149400190310303103000103004005540300f664140046900d82 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735388048 1250 735386798 735386801
    0x111090108090f120c010b0402070804050306010b0705030d20130f08030f040302060904110712021902030a061d0a0b1b07020121090602031602010b040204081926180103 74
    0x1500d6540c040d0300844d11391035428281c00e0040074409152000407407080c0e001781c00039003264010300b01110910800103080120703090511046004000c07118445007000f10945a55881c1d01c0388403052030500c0d07601c0d030002c40004a035220060b25802e9054903140c0342c05200424045000041c080c448010720f040200049205001040b1180324402e08442c508007882c6030b0900086400c2590403581c040c0c1c407564042c003e0001a4041d01c5820300030b03c080d6521078082d40019041c00850381729000000b07030f042c88100140e10001212010194003080c0001d0610141e01030321001c49903103800b48642d0283d94041c006100b0780c0c9522038090040c20b80d00080c201e403543d505002c9407055801c024082000e0784d05c2c00b401001842c0000c0120010140c000c5103081103070b51010100c1e40304407109070740142ea4000f6401c060380d09101e0281c0c2c613541524118500340c01c0002e00740d6144548298441407442020b910700420003036441c2c40c41e074204e070640e0b140f040103405c020b1012a074000c044140020624408054000e605ca07 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735389298 1250 735388048 735388063
    0x906140916051b0c09040c0905091b10030902041b1106010509010e070507050109080415030e06060409020117040c150504140d2a06140c120c0a05011109010809 70
    0x4030744400e850f11080d5907200324403a0704084407070480c1c0503456002c2c0c0e40d40c039102e082c14400c034401c4e80c094100c141084415011150090041840b81d80072000c4002003c08070340c1364200a9130202cbd8030043e80c802c017102c21000380c114920000c2d000340c20401c1c1c030300250404205448204032107481d142143c8a002107184d40d101024491540d10000e400300400c60b04202c02e4071680c000391070b49007251502c5244e40f03903d42510982e420440c0c0141001a00b040064501d071150214007a0720710b070502c002505011600c0d1b5400018140e1841940d032507030b100c0c0c1103a0003025003401081e07210340008071500d0113042c182da198040784509851008c0d01c41100e180c40744a4021102641e801c03150951050004409011200020300d4040b680754038260403d916400380d010b440d02040c4001c054bc0e0350581d05081c0001c0c1554400701c40e005502c801031141400049010a407070509100840100f0340750010000403900c0d2490402014049501c0d000c9070019010040b0001c0c562180b0a03290040962176030310b00c20341d031000c9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735390548 1250 735389298 735389341
    0x80601030e19030e13050c0d200304050a14030325021011120606030403092102091f0f0f030f060219022b08041b0b0408061009110a080901020409061409 67
    0xc003002100e030345003810780c0540201400e110400501070700346603155005910074bd0f010b8415511440c2c04400704264040c40000d002ca401c0c01460460604200c04103403080d01c0325440c1c400100028000d96000c1c400c02c42e860301209042002d0041118000307822145600c011030b20302c51040b607180084c0c4da6003002c1040b603009650550b07903003070f40305e141540ca08011000242809180c841404400c00942d07950140c030760190400d10586c504000011a0b465511405c55100b01c0c4041c1da80182000700c0701602d98031108890700f000180c00c04400e03600d482030007031050166501842c480c000b0190000d5500042d80404110b41640c031040b014580c0c19410150803001c404480010000030000d4006078400d400300c052085901103039035081c0c0d15550078010a0f0020b405c00640c0c1c1d03120500f00804440e500e0b822100408001004111501c8004604402d92161908a07002d2206942c041000903600354119030007030480607400c0041030740340d00c0e0a5120300b070704141461040503a40c000c0f031072980c80381180041424 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735391798 1250 735390548 735390571
    0x506090309180c07060f0b0f0f0d030e0307270b01080c030103020607150c2f0c090709050a091a042a0c0230010507080601030e19030e1305 61
    0x20100200b0159403038020500c1115580901160001407098003518000c150301280100702d0700341443c10300540c801100d4540d07100741c06a00d0156070300d4603120b1072a591150540f9080d02c150391010b0110b8a865001d44c0b003d902403102c00c100b00d10400f801403070340ca00c10000c04000c4c40745140102c01103034030050650740800d41c15402c000400040c5413860050010a21525040142203000310794101112061070350030020030311854080f01407185d50180a0040404c2c4c2135035818400c0c0f80003410340d50708000d1100b940150050030114888a000c4d8403040010000100810307101511501c0060103403000944c10020f2051034015113a4a00c0d2034020024994800714070000107441d44000d620012400070b5010f03041c410050501c90240c1c40d40c4043d0007030b4214a02c214035403108030100468460fa401201d010460b4945000d116499030311002242d001007007442c0100d40300d01d802544070305000400e0910a4022032210300e86041541086640744d603268104c40c4046c5c403071840c145440a69a0880d200400745 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735393048 1250 735391798 735391819
    0x602100504120c06140c0d11070807060e0f060405010b150a080a0f0b13050403080606040e0105010e01050d0c0c0318030f0b04050712060b0f0a050306040303111309090506090309 78
    0x1c0e11456211100b01d006240110b1710702c5140a41c030045002c192600003822000081145a0244600654000003604500545802100c3d12544564050301c0c00003072406840303800c600f20f640410060300c00411308440542d0200d003030038a031113802488170151442c00380007038220203640c1440160686844c6102c84e03c2e070400c0f0385d642c002040010728042e03042106569940140305801d0311100c20f4003420344c442c540001400e0a00c3d080184c20200010426889100704000501011901d280b1441c1114402e084c043e0380042c0050041e03646002d403d0b883c540c49032074a07142e440c003590311144d55070015001c1d80300ea000351041d210460507489098000135060641c02c2ca12080001c1403003510b19481401201910495a2100c12070a0a0070020105039076054569410084514001c0200c00e0801d40880e80c11105a24200209450355002007001e81455546e401c1c2424000400c002c413800c10b01944504100c05480c1c83c8060020119510309690303030b10078240002c45c0a00c0010444045100c000c0c4401d240e0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735394298 1250 735393048 735393083
    0x204061d270102041d102405091804120504150e0609031501060315030f03081509070f0311030c071203021c060905150622031a010602100504 62
    0x24a51105480807070025051a2008080400c0c03000c0d0026101d2480d030440624425401c0a941c110007410101c100f070042d0781e08100d01e0350303640ba001c2443c0224045120a580300d004050b80d41d405174807030260b006031104090303050a034440c03074005104038403501900301d030300c1400781d001c68150085020f00d601c24a808212060241d005040d40c03c0b00490040c12140381036020400709040a50055200700c01003114401880469007502601007100301e880f10407080a0302e540c80d1151628078003140030f0140300405001c5140c20544d030f074801101c424080d0020b0307041d050010004106004070800d080c00685000401300d04280644112030050901e800024105803203503c405295051030307030318241896401c12500054021441d41500d0340318144000103141854a00030100351034000340380c6404500580e030a290030759140c03401d07510214140b018040311101030050400729404690805400e10780c10600040c1c05007003407048941039680c664240c5a80c240201da06009903081510020248640d4000e4042c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735395548 1250 735394298 735394321
    0xf050601080601032403050304050a0812030402150d05040c080f0a0203151807080307020a050d0b010603051302130c020114070f0f210c08070c080d020318030a020a0204061d 76
    0x544c03000312105c2103d0a14403a8210101800740d80c0110303020f400104041050385000e2402d80001d01070030014000418998103145005c0c800200000e03c100b0039007607070201e07480410084d80c0000311240710070000c1b400c0c181070840c00c60000b40700b100c20314403403c4140c904000b400724000032100c0d0701070010503a620351942c1c0311042150040c80310399841c4100c0c0312114112000c0106400800d80c0d040616a1588180141704c0b8119035038024600649030032080d8000501c0e1000154115591440c0c0002c103a1600d420142040101a1010798000c415071104249041960301c51034518106400802c0428106001c1500d47c01d003c03501100032404002c605556617004902d071880c4034065103003046100060102c4140d0054040900220700e40c1c3e03461107007a0071500080881c5d001a0b9909000c1030400306036840c843d503841802050702d00580c01101041d0441c0c814010341c110041c801d01030366220429a1f00095940c6050b103002d030704c25400c01d4800501040a8840800c03aa05030034241c00d1613a8940c0039420 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735396798 1250 735395548 735395561
    0x3060504060e0a0f1a09030d090606080d03050604050a090302031605160b070201090608090718020702030d1101151d1503190b160917030409110c010f05060108060103 73
    0x1600540c0307520b001c41c40300c0014006110080d2003406074004141d0107041580c20407815900050030341d0907900034411841c80010640f1007440343e02c0c0020681201d286042c1000e016540c2c000c03038840c4600c452409040b5055008244110020741d010022a0350312030360402a10022840940541c200308058032404d21448101d4801034020811901c2032060400100601e00007030f4800c0048100109980085603440b060700300003002d603450840c0c4681004001180c91700b8891084801d4520240e6140c41e114003035030151406160010241d400c0b40c144440080d1030074115980f02c62003035203030088900b005034101c90704006a41d454180e590034140282e4500908110203403402c001403608030b9000034a550200b0502c030750504000300b06843e5803001c0c0341c9214220001b502001c2c502242141a003c000c1d4800c00034000c6641d40d0348840d035002d050368070081c01c600ca0b5401c401041400c00b100501c0d440c01a400800d07a01100c00002c002000c07140c1d0603041124000d80d95240000d0504000c600151311a40002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735398048 1250 735396798 735396803
    0xf24271c08160c0311010e010c020f011b050d02031c110f18090a0b0a0905042a080303070207150315150224010602060c0301030c0303080a020906070f0c06110703060504 74
    0xe512510240c0350010f403000d00780c0c0129400c0c02c20f500c4000565a05c224215010700c0e083c00c0c110060651a8002000071040001d207504000c1822035504010043d4209c0e604c41ca900301d01a90318440901d2002900c0b81c2c040000f4117000380010400030213500c414414001841c6460b41076a01f040b600c803284041941c8400c940e6200c140300c11614903010341e1000c91640c05051845000604000548284040d991155104580480c41c0c84100004644120813000e00f446011442c200708520401c8030704510043ca400500381440b000c4104007200703400040ca03006503134074035002c00102d0344003040840c190b590407424104d80c203002070810008100d40714614004440e550041d120483d204078080e440d40180e1980800d13400502800402c420342e01406039a42041c5e2070700d1114078543c15138903544517000c10749c400203080000820001c0c0071451194142e81450070028071460341c440751401c2c0b4041c0124500401e03640400c2d100300000b241402800c951111100540c0901070617440d41d03d40780024032004006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735399298 1250 735398048 735398077
    0xe0402060913050f09070b030a0f02040f0b0a140405063408070210020a03081f031401050f010b0408120d02090402030c0c010c02010b0f24271c08 64
    0x1c1d0920742c0ca10046207009038000e030740042d05180c24400d15500b200e01422201698000750001d0000f1a8004210fa9200048010101e80e0311030300d5210000a10466120303a11110034145c01080c00c0b40301500a060503503003642c4000803443c58032032440c00b91003030b4070a05a001c0001c000c51070b21460903051200d004040404000135201c1400c00308507200b034082c0c10854003601c0009907003045107440da4200f401072040d40300030080c082091b9005481d603a40a0400305031580540400318110004501400146038092085400c09203220a014080c10058603810501502c0d40c0000c5003c0c4181001e44048600240c020200015221040c0481d170b0310003185845402e40030031000210352658001580983c0304944040d5640e61a505042d08544600e02e5113003c59041020004030317079540005006400300210380081c101707285480b160840000d40110a42209030100390404440c28203007000c00068125007041001d00c903d002000b40b000080d98140c000000883c1c41d04000c5130903640035082c1b803420a901e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735400548 1250 735399298 735399307
    0x42106110d0e1203060102060708090109120e01021e0309040c090530030a1403070201020c1203150f03070b0c03130311042a0f020c1810060512010e040206 68
    0x88882035400402012403a50b1200051492000c007040350071000c00c88007011904508045000079120b1101809640400400c4408101c40d21001c1d4002941c040d40b00c1d071100c1a0402800c0003410f01011860111f002d07001e00480040000c8074410951051041080550720304080301c000c00c40108a020040002c000d040361010a9603100c00911122000358030310b810b840050b050303038040c0c0c26400300329099480c1d800500072807041c01c0e040900031454440402481e52a9a5803503000c0740280546401c58240e1320a00c031441400e004100300031070003130304840951145c1d0411078043c0407610001d2207800b80c059000c50002c008000c0caa101525094000c0c1054a25280402240c440344200036003040c1c0d00b24074218502c41c0075252620415103000c5208901c880e817079500a070201008403100c0d55040c140542190031040c2d25209000c80d164050000704401828200c02e052400c0071003080f14025410040500b0116520740604180c1c0c0206928a00c1d4a81c641c0c244440c2c4003c018000d041260090001e00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735401798 1250 735400548 735400571
    0x180a1202100e0307050609070e0a020f22050f27090f0a0510151401080601021207051f0506090a230a020c010c050f07021912120e06042106 61
    0x30b5250b24244140115202c0b1140c3c28924241407000c0c060451540c042d032401c005203c0380c2d80e189039000388030000040e00c0780b8524101c41d074940b10303000407048030605080508028203031401e2002c00f0744009540c2d444071961413409100d82c00b81d41a142c8e4a42448100c4040751031250112450f600c94095029074590035000f6014901d4020058001c03160354020b1007071030706480403500c01d014501e00780d4284840d00e28075040b2540c801e804000c82141c100800c107000074400e64000c00482502108503250325a0384c07022814029102c2403100300c1010b4004100d4030002c01c0e0012401540c0c0103040040c1010358649408002400501010b4030303000040e05281c03207161000c121001902c1c4103001107280545c0c0c40058141003802c40302171044a0301446424020003074203489440680342c903160b041c2d81003c181280f04032680101e4106600c500074490fa00084401001188200d180b4120341a881d01c94140001c801040f000740500c0c00348900b102c1e00d8113003000c110190701c42c980314114001c130800100e002141 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735403048 1250 735401798 735401801
    0x90b07050a140319090c090e030714010c09050907090f060215060d24140a02090f1f18030501061509090b03060411010507060903030b0a12050717071517180a120210 72
    0x1048c000d9190000b04d000030a01c946068284c40d0f00c0c3c0e8440007017142d50b02582015001e01c629025903030007a100c0100260b40f1900074814100a0000d4500f01d0340c3c100da940034000c1d03840c0b92481499445844c0c0320003240d01828108040c882d0151301c86c0001c0d14402590b88003a100a0800140b8101c003621611201280301e29049214000d9600c0d81c009656090240d0612104444060602d070040440800070180301584d505001c00d5011107140c0012840c0120354150140007c5800181441d46800b10001e0003003206014401c1240182d110584030958a0512400311000000100d03015003040d0000b41c0004c22422418403400014180710b803c01c02241c4950702202c807142001c43c0860781e02c80c44185140742000342c010043c05410b14010110140d660703150f44450b418440c1c8521b62028046100d450310060103604050102c2607201040311840e40303801040e440c004810700c200e8a4464000c50001f501c03100f900f120070034803078004122a62140d500d4070380c107800e002c0042b01140205c0d8a60030403030455 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735404298 1250 735403048 735403061
    0xc03040f171204120c0b19090c0b1b0715050a17130201020f160e07020a1a010504060f032a1a03010806070e0a03080904090b07050a140319090c09 64
    0x502c1d4404440345841e01e00a0061800d107810742d800c2c080701074a0103001514580080b6404002024800506a22000564041d10080070300410320110300c4004520300114001a0120350050410070402c81c10b40a032072074031039506001d0840403034800e01d4800b070300318002d40c01803040d1041c41c90320b21014040c44848690001094070a003841116140a1034255a03042240c4400c80c10104050900300c0c00c410b600c0400101240704503005001c21000050b1000e00a105444c00e0f01d4101c04e52054003160a00010031461090080a101310f144c00e1000c0381c0c00b003580d0700174402e50768030030303c1550355482d80c0c0d0651000444030030701415209940e00d40071504610150254101520110f02e0f60303143c2d41451980390800d240204200e04110083d803262a613555254501d404503500825000c0e99045200d01040244c0b50040e00074280003543e0090089150b4414001d040c1c2102d2540c0d03e62040c140983c03840d26510080c4ca02c1c000414041035481168521523000e131170381510070440b0b48c42071507913149440150380c01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735405548 1250 735404298 735404317
    0x705030910021005011a090904020406050301141b0405062502220b0d050c09190c0f020d09080309040b010e091302150301080304231807170c03040f17 66
    0x10f1414000c1800140030b403c0c0909150f007114042034010780815006400360000c00380c420280d202c0403e0941d05c03039a1000c0c019103000340083c401600c0c42802c0c40c0310743c0e0054501000304523150811034a40301d0100f050301c09a40e4003c21507840c0c1184140d0700580c00d8285151000c0404410072424010b90307980800300c203c0c4000848442c80801802c550108507485855800c9c002c10409104000143d00840c9911141b0805c4070301c1c0030182c80b280060103d4442d0b404540184515202c44101420340003220003a511560b5801c032a2800b039542401c641c1000c8921a11071580d10900102007180f60540211450380018580103007522520300c00620b07102c1040d104071011001440d600710550810320342d4204a140018180391555140c000c3ea103540740315601c6042d01d452410038280d0707001d0000c00c2d0303103e0202800402141803401070b04803141044405460314000720391110b0380d400904131400301d442d220300581078500b0b0540c2d50320f442d050148541d600049400d10340c0ca6428109032800315028000700030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735406798 1250 735405548 735405553
    0x11010e01110d030f0f050c090909101a0a0b16020405130c03120201200703120207080c0606041503051507020a080301080604020a060318112b021320070503091002 71
    0x3100354022401c0329417903d40c030703e5080e080100b002006550481251441d05080c1c4e60308290790b8503101454103015544107070507000703030404d514024500164210240117000480b020400159620f499501d07904c9007404806d182800c0d0080007005d4602507200c2035112086403141070045407180c0e50001c0b5000c0c071f41c004a403c110340c1c000040410390b09100301080c9190806002011a42c900004095401052401000c000360508003e0b03020700c09805a0304031541c800301040e150308c110002162154030884840f80958604a0020302d180040348501c1d0450341c00202a0500042d010404285200c3c000d00d15001d610664021100042035038000750b00034000707440503100500305481081562030701d542c4010f04160400495030543c40110700c00004c610741c0290810f68001204000ca540c0c2c1018060442c0c07c40120b05500e480440c00440140d2200e1080340c1d40780446078075114040845503952052080b083c820741440302a015000010012503015404990130440c3c00c070005612241081d88201c01038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735408048 1250 735406798 735406811
    0x110f0c060f130c09050603010b040c030c0822110f12160806010612020915030901090201030f020a08040f1a01030309060816230f0d0b030607020a11010e01110d03 71
    0x201c00300c0781194000550a06082400e1442d403107a59414203140a9071040e190b070340d008661603a40960101060788409801404161005e00c0007070001d10b2500101d801080e0500b00150121601942c100007104140343c200305450f8550f02d50b5011401c94440310b94109900907142041d517500c440414030035200c034900501031100b0504038506017842a0b40b041307040713901010061001c0398016000b00d0380b03828800303001a00e8090f610700103685002a0040c000e00381c0800014031080c6d00c1d040d0412a40340e4000c0e03d040c404c10104108041c208e210390940500001c07800c2e0003140005000100704180c0030300840e507150011050300500c5000401c00c0e40210b001c50f0381e00400f00f15054016030f955a21804240b040020080c0344140905445288548200c000b44d4040c2e0b10010310683c1c2c019200e102c501c0e83c2d1440d0301c1e08800c10101000303004400c002e903ca8466000040c010324070008500d6075090340000200400301e14000107440c00f00042c00d0050502004600c0d03201030040800145400600039900840e14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735409298 1250 735408048 735408061
    0x91503041505070507060513020a060f02190503090108101a03070809030a0206010b0f04030516080c150405010305040f020603090607030501060c021c06060b03041506050a050d06110f0c06 82
    0x665000602a00c007a500700001c00c00c00c590094160341400750000c10110307440d0b40d44120340710034480510b0003e511140c04880816001d0703000d803001d8020031842e0221424600215024040c1e60502e0b040249254001c00c09030700b0700d5118200440d041380600499854075616140f030500703074014154505083c2d1101008001ca800e900c501b101e608074a484005d186800803041009446503014014101c142600184241031102c48004070b400a681000c15200c200d13104110345505d941f500d200d00441841405000d809a242c040e02c9214107103000c8491798a09440c0034010740c00307094001e0094407802044047c01025071215070080d84500c000e02d0140c025450700b01c2000d0708944040e04808108001501d61600684510941c1010030940c05005803000b40145021805880e080d0481500140301106100070846640710110904101c00810b20181d615038080c008441c1c401c0c414641e20035005030321203011034807541c8000e00c48004c0206840c40d0416094000655901030b2510000ca90701c4002040b42 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735410548 1250 735409298 735409313
    0x20a081c1107061a0904050618030d0c0e030c1008070e0105070609030e04200a0813021020030f040501030b1503070e03010b100c0813150c0510062909150304 69
    0xb100c04c100c49109690525440d03142c1e4525004004903000808214003107182c84040054683c0074148040c203102c50641e41c5c2c4024001590007030b059000384078070130b62090b2030b103480c031110070323500040703a469030855500d0303001c2102e41000000c0341d541801410408540452400d0284007038007402a25680e01d1019080b041c8401c40340002c0d1040094043d80921040e08400f11045418405591030050025106c100c3d11240c0c03c08101c0000b5480301898010300d02403500060381c840d5070043c020051900d24507402d2400e842e0700c18191105c810000420090020313600a07440280b030058050320a011710b000c8601c4842603640140d403603601080140030401c0706880c09000311403400c4030507220000c0c29501c50401030100c0b641d02e030006125410102e820203001544403007400080031020b041d2180ba4083c03200141ca0300000c403800761580e001d0031802450682c100d00410b022528588141c849005002c0700c4103c42c40135003080114420020004030ac0325542e030840d034803580e2a4007140c40b913aa0805140030305 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735411798 1250 735410548 735410591
    0x80d1415010210090c0f150809010605010c030c0836030a05120f0d020406050a0306080105060310050a0e030c0c0a0614161a0a0f0606020a081c110706 66
    0x121000d10010312000e031a41d011030031a08850040b003000c60b81400d40d1070700480d0502c89404c001094172100c80c00003072550300109186030580c255190501940c4802d1203250980d0110700407940400c581e100b40d84000391040001031501c40c002d01c10b2900341030798803815000801a40100ca6002002c03540c244c0e2103500d1828520001d55801c40c014041035a607a550951514801d4103051190340000c20b18000c60300f0000c0c02c40c0d540c10081d2604640c1e40703407104401790080e00202018000079181810100307040005109450140f60028018042000011000006040000e0444024540f83c0b0307440d040f00901040500755660710640907201400c03008040c0002018154091020066500b1200b21610030322421114043c455130146c070703204c036410b050801c603a202000c41c5c03640010120302008004000c0da408401c0003030f8602c006000705a0741c1c0340e08980c2c58888020140100382e0070001142c40d40c211803094032040ca41001d01050b0301c480000c1000c80d80c1c03c85e120a59030384c2e8032001c0c56207540b00144000c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735413048 1250 735411798 735411811
    0x1b180f013509012304030509030708061e0f1302041506110d080615090a0b07030c170405180a1413060b0121090c03060e160b07050a02010c030507080d14 67
    0xc10000c120740302441000030130403800f445800a400c0c003040074180301d08200d605101c0050102c070b081c255603410b15581d800301160004607802c4100c80ca0001030a0340911a405144000c8024190b92150102842005080e074400c80e03205956000c541c0000c800c0411040061255480300e5002c0304460301803600b03085240a0309420000e4007800c209895454161400c030020030ba4000d642c90701d540e0000f00303094070002e80081c00038601c085800010943d021740380a4041d0303c02c9542000c1c07c0c401e405012100d000e540a2142c0c86001e2040022822005111f6154042c9204101041c00890074030700c010740b540c0940307403840c0d00850400c42e5002e201641c01044100e107401e180a4012415590110a40300c9421203600c410548640c0e5200034031000c4500d0344c018641250042002d0300f40ba18480d44d0755038021907602940c042d0403400090b10f0640c8020b4851490300103003e8208064103a00440b90803016580440c1444024449079011030520006040110180c820004803013907001c50900100c58021710a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735414298 1250 735413048 735413051
    0x7030605191d0915010b040302041b0e0621040f03080906010308030610030b0406090209040606030908090f0307090903020606040b0d0c03140c0d05061b180f01350901 73
    0xc0268441c070058440390b400000c0034840903a11502009420000134240080e5210b1304480007081c808070341001881144c1c0f08680130010a030301c0d8030002e01d2884d08901c042010a00041d105205420508014007103020021400b01142001d80c0c0c1c1d80304d086505640558400c15180700d44420590010760081d0403080220007000303250700d1640c0380c2211303200090249000312000d02600c0030203030080d000300040400080044c85401c1d228907004000350050021244500c2c100000011418024030600454642064030149403414903001c0c0200c032003030025040c0d01351091440001e840c048603c03c85844600c6907002c2c0c10503090010400c0140d80901c0600c520039001080b1944c0002c0c01d0060000c00c0f01c0c1e10181c8089201c4480301c07806c0c201000e0582c1150000301d4410b041c42002800300f01e46115024018010900c41c0110301950340030f0148130300c00d040007207130652403a00f14546101c201000c02c0c814542040400170010b0b203030303140811042d48180401098101d041e00004a2000d036948611807200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735415548 1250 735414298 735414349
    0xc030c25170f0f07110d11011d0d021c150603331a1309150b0307060c0f060e010212090616081302030706020706140f071e060507030605 60
    0x2c0b624150301c2401c2c500b80d0340c0c820001d00c03801000143c1c0544003a010005100385051071503070a01d401d8000c2504c46041c002040303255585141c08400907440c0d448030b00982154540c000c150f09011070581280e8194180e806003169003800075150329030401400740000d10104895140d89414203402d004140081211000701d4080c00c0103000406889452004001007c20030403c031040c051048404030074002d8102d030032070048110311b6407941c00940c84d40d8425040c4c0d1050b0078084400604884a00c07161543c1604884401c101c4103101e0050103240501401950300b90b05115a180f00484149000307040d002c0e5000f040c005034040788041001da02245005c0941424500300082e05400d40c80783c3c15030403c2c0b040b602d004c510300c80c0d03201c88040f58640d405030844198548610b0003075619000b61248400080280c000f0001000f034000640c1d0100c00600e92882c10400b01ea5240b811800700107040c4040301611036800310105646010380c0307024446a4400042d003e00744403d1150b58461a4240342529207941e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735416798 1250 735415548 735415567
    0x2011109100e1f030911090c040b0a03060909060b030606190b070302150c03060a081501271d0706080915041b0303081e0f0c030c2517 59
    0x4000c00c4404000d1a04158800c1c6503000519540b507290b40110f070010703141d0740b03c16403e034055200000070760180025083c2e44010b00c080000c1e1364800c0301d0f86d00f00710b2010f10082203803100c520060b00c501e590b0740c140800c50070384807c0d0003030855401c01d0058954503228403c10020381414081544c01c180151600548a0016140200c15511500c1008100e0400003500030a05200b40980074031001e09540c0501d00c0d0800951010881c0c005651a900c2214004800a0400c0c00001c0701010701881c003950190580c0b0303008134182c0c0b52001c21b2055201100f2044051042c108a128208406d5041102580140b00282841d0718146540c2c22540920440c0700a00002d0840003d003580100418202256166541e1a05d200d054104002920070320700c0c241008010140c00211252244107681c0700340c030324210890b03110f110241040d5280c217400c00c10040450a60580b4400955016550013100d91418003001035a158115605413089496130082400204002403040300091808550070410709055801 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735418048 1250 735416798 735416809
    0x901350f060f0f06090601050d0e03070809040b0919020a031410140f0310020906070c08060601031b0503070e03030c0703030806030708010c09060f0e1008090d08070c020603040804030c06020a0302011109 89
    0xe014035043c008c0200b4440b44405042c7c000021107041001540c0d141c1545291403401d80d00703c880e800d4800d6050108a17402030a00d008200d10a1204c012452810078107030a220000f940700c8401801011740310588a038481005140c00307401110355003001e2209a00c2e06440403031480441d007446120f003229070115601a43d000079100c25100380c0d05401a03440425200151040c0b06241004003400e0b5025000500b424011441c940720305000c0c0c90600c11f0300b04190a03444015003111a52021403c284081006070703200d812151f4410794050102e82c0703041100c0306076515010440d40101c000403c110104100c03414240046002007600038002d01068110050107409034000d40122010020410358201c240b2788922800b10004c83c0141c4900f00714003000d0401440c8140403546a01640301d125010204c05201d0441c0920595080d61009054070180c0c1c05c124455002506c00d0380c50074000d11002c0041071051003100010100e036001002d5040f880d25006c0d003503032186809001025000c0c002d802d002c0d01c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735419298 1250 735418048 735418051
    0x1602010c05090105130e040515130201080a05070311180a1205071e0510050a0f2f01090b0f0403180308040509090307051b0a050901350f060f0f0609 65
    0x13401e01c981c90b8507401040b050466400c3d4000d0300f070550a0010300c010311002003181c05c4c3c0307060803190000303440d52400021490190a03090084c005440340c0300041004a25600094128100d41780c0804d10304c003424040042500806805080070804114090440c032748881020000c124001c40007a03004140e031200c40d221842c0d88161800450300c80744804460800d4500b210141c00c0040458860f0410b9110041c01900070460303050105040040c22588203000d070504051500300e40403004030301c00800c00d00480380300c0c0088401d0200c0d920703003160703200003550368070340501c1030141e03089503002c03445d05050081c0281028030003102c0d194103030581440418050400c44040d50801d030b030034022039114000f015243d07108401024142d4019007416903844008105402c1c89100d085400003c200d8071a0f01300029120b0030700c0351400407905031019040d4400d00c51075002d08003081c800d0800050365145017441c01c01d450000d9901c1203800100c20010215035000642c0e40200704040f4010084c54500041400d4500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735420548 1250 735419298 735419317
    0x9040c081b0306041b0e070f0f0c05070315110408060621062a0a1206060e0127050a090203010e0703020304050a0f021504060216050d02030303012d030b1602010c05 72
    0x500305c41c20ba1301c403e07020300c03490003014079940401c480c0c80d00c0b150080c00d00882c846c2d40b500044203413100200701d91150312410a42504030f006482c5081c590340d65003e000c1200b40091010640b074140b000c002c0718403040540000c04401001d08000d140120800018001c0301c2003071102c80103040c00715860988005541c1da404138040110a0007141e1200350110076002007101c0f01c440c5c0000068120b0350b00d500c070882049c2c0240783c2005010b0389031140c81c21b8130140302c000c42c100d002420368000628852170302d00100609540d0807550385682c0c0e8a40004c01c880c4071140c0c0020680d00e800200400940440c60700c0745e503110989150841c00c5040960340c00b901c13045080809008018809005429507685600100c0d2241c02044219525540c814001c0e480381b01001015034680c0d201500081e070b500b0240c040d40c60480d4000c0140d45542e007018040e5040c0c02345415240c1c0d0302c0940846000400441c05030b03900103140034203040b403814070340103615070740d1030328001d01c2002164148112160300076003241c1550346464 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735421798 1250 735420548 735420563
    0x20424030219021b0f0d0b0a0603080a21020414010c031101061e0e011d18071d100302060405040b06160b0403110303011a1809040c081b030604 63
    0xa1008a01030302802a800d0385000c0e04042c2d01e0110364001854030a03451803a990180614040000c00c0103040301c1540007500700c0345a00c0100c1c0001c01c0300e8185039020481c6900040d140c0c0d280d0300ca80031a600a0041103011860300d038100c042d01102a0818101a61400302c15407500741450300e02d0310030008044682e810b0005482800041601500079860740700161002000169a186544c03142d000d404103203109007440c1880e002c2107880c1c410000c541a00d4a81c0310385d00211a001c1681da07501d440045c03034a000c00c8124490000c04201c04d008180090549074002c90000883c0a104290444060801c44040460b5002003005840700407e56003200d40440f00003648030800b50216032580304180303148810200b0030040208101c0b1000c925130245000759074100d001511068126601e200a000700380385034418140d1210b10110020082c01d000c7e0035520901e900d0961000864400182500d00305c44001e014070003070040700810490454400010028484050320010200752a108060001b414030b2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735423048 1250 735421798 735421859
    0x6020c06090f2806021501052205091c0314191e090b0606070b010b070c171e030f03040609020d0807080918220507050d03050403020a090204 62
    0x1982e0740511100c12010207403540c2d501d00318910805503403003500e020500c038003101d0f40b40200f025480044c030040500361000c9584140e0b4201010040403200c0709400008601c0c00c406180042e61303885c00741900602d2828018003890680800c2000c2c42c00e608071280341054601002500c000210704a1903401c071010800300106001c03510480c0010b027014140180d1003141c0448940401d0025500500c1c40310b0149800308515294a01048031a02c640c0c0d00141154540100601130155007500904805204500604d45684d54920140b0741c54226442c500e10307900f02005a00362500d40e00707852000420544003440c6019103030060f11440d804042d00c0a8455680c2c2c014070011501c0d6645401c03146a0010401c1c2c1d100d0140d0310f858240c0d03a0000305614003508802d00a4901c0c1012031160f05c0c0120203800360000c0200d00300c620002000504841a10103104c1c0da40005103a0f00e6a00311141e0300c80c0030b542c07902c0d683e90441c0144510300040e80e100b4525244100020002c00c000c01c0c8034084000034440406111 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735424298 1250 735423048 735423067
    0x3090d0e0105040f0806150108010f090f1d0c0a2718062414010507060c090509151509010503070507080909010b0309010518060c0703091203050c070801050106020c06 73
    0x1ea00480c4c020501c00010300801189115001688a01c625411220803203484060b2004550703414003845950440a4250018403240b096034101c806104100d0070009042042c60780045064003400b6401c00340764104c00403103006401c0444540024016101090f500300c0801741c810241c1d040005202d24400740d985000c8840c804e802d00070a06020303040310084c006100c4050504200c01c07608204598000b51500c1300141d0001409005501d10005031191420440d00e6103e610103001d00d202074808001030300c03501040994481022034059418559000b600b101594144100c800441c2141c400fa06401e110368146a07074004120307a400035031450f200307440b41454500383d640b6005405180782e100042c000041500340210300654460050070300288901c2d01c80c0007001c0307149014511032403a544c0040380050108411000240032840c400d01d0100031480e0b07112144401840013107011000100d00080b880d012074810411003000d0403801000300110b515110b8040c2d0f0702c00346492413a00550001c10039009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735425548 1250 735424298 735424307
    0x110d050307080304050f0d020111120408090d060506041416050c1204151b050a021e0d060515011806082205070305070b0f04050607020d080a0302130b03090d0e01 71
    0x44007640001c01d1512410f00d03203819900c8240242d00d1140c0783c414447e01c080028814050410407030885c80d4082e10702511b14404080c10301008100b40c03074640f000c00a0011a4480040c04248240207182c00103042c00c001c000c12060b01d04c1d40c4018482d40b0000c00031302501c0d41c0c000315001a0300900d4182195a58018803da034204040088e103c910102c1c08100000d00c0581c0c00c2c008100da80c403507680d00000d003100300003040c01d80b65034610181c0f40364070484030300f801401c041100001c1c04201400e8080d1004103040015100c40c88610212030705034881c01440b40c403001c940c164040c990304c2401c0499640c640003000c42072600030780c80b4180800500e01c003c0351071940d0158903603104a0b40301007606c2c0c145940d42480c40c1d40d007040f40300481e000d12840390009100301c9a030003a10441900d44080500e4589802c0410503503801086c0b041e80e1002204880900241418004007180c0c82207803409611014540c01c03086021125a010303c002000070820000041d60200702405806014180001071450900c0101c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735426798 1250 735425548 735425557
    0x10305181902220b1003020f09040906020c0322050306010e0c03130c0b1c020c0a03030b030c0a2303010207082a07080304031b03020d03080406021c09050105070804110d0503 76
    0x82c600c81c41070190f480302080d290010441c140b415180d01c50b12030900e1800300d0403031207048445031501c0f00034010854246170681001069030f00a800140c03d00308001c8450b0700b580e1080c500c1808400922800d00300c0c0b4640d1a6125004006c1100540308542c5400548041164010850082890000000307603c000c04890704040054004844c408015103400e40e0005c03984c05a80001c40c0810081d180846510480c003c46403c606c10728058030755103806540a038054001d030500345501d80035480d144c0406484003100f140c010101140078608a45110580b0f2802c003115614090182e401044100c0208001b10112090354400000010604200e08490040740b0303a030f0041860280a907082c0010390a1000003c2c00941c0c2c0503241107240301004400000a0a12500c4020f400c6401d059003a8003103030103840ca141d8040d0007020054030f05540805003204c4812034403001d0400603910140141449400d00c80c9035404036072414420a80e007001d803281036440d80c3c040e48540c072460020b8151010004184141c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735428048 1250 735426798 735426829
    0xf15160c03030e0f0306091b01052710030b0319080d0c02060603010b120a1211120a0f26062205011d0c030f10030206120105010305181902 61
    0x450301d440e0b2030014018003014000600c9400441a858100e00d400700b203940c0611307a484020728000d00c1c0201c10b1070703c000b54240c81034140309051040f030310349405150412200e00100920b00503034040d008100a204501c10a041080500d0200d40e02841c2e10001400200300f800800b204800c00543d291510052041c5803502090310b0a1510800c8010b40007d10380380520380c120002d0000400d100140410b40c000d969200190741c0c0050000320100341d02c0c1d55448010841031420400803454803003180d2400c1d1a80030f51010100e80002c10f050410381c86003203840d038400b9500d4804158040c143c0c41002200c4c802840149182500c80800d4050795901d02602d20b58241703420f80f02071707801040389140080401740705044114a960303800c42070440c02a0001d5100301e4194808e03a007182c8448131801c0040700020002c1c0a854031b80c01c408005607617000090000141462024001503041a000502780c0b02c0c060b0100218640621815103680d0002c591011600d0005100c5442c250242c000681c0090407241d90 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735429298 1250 735428048 735428063
    0x8030301060810080d030603150213050f0a080f0d0f08010e240d031107050319140114010902130608130f02031509160b09100e010c050601140306060f1516 68
    0x480c3c60484e099009001101c0c0901900000d01400603d0310040e4807815190703002c5072f00050414000d41c070300000c0d0560320303080c06003068603a035840e00f000303902d8035450303141c0e8003095400303248035025007923004c00001007461843c504000c0030351500c441036207503030782c042c00d10200340483d03044041403400e00c1400400c20202c0100a03080385915400c2c050080c212040e661401d0303026910b404a840c3c240059038142030b00c0d403080505900050398a4002450318030302420380ca2075403240710801e01c40700030100141c040c0405080042c1c1c0e4a1342814bc0044510090b8081e03000c1c08028410800b4a4074079284800c225504207002001c9150b2600c000380c144803013401515081211078051008881c40003a11520210406100c1050261601d084282c01c0c00313034044032980711100c601c1d00b00311180b04815480c080281030400001c1902e5642e00d040c10200240c010072000121524540094502003005a403c42429540d8690a1a030013011900280c01c40410301c05031503000803402005244c004800b58000e0b0881d86 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735430548 1250 735429298 735429313
    0x308041a150a08011107080c07030203030a0f030c140d0f0b04020f09120111030a09030302070b070f170906040602220b0403060501090b0d2a080106060206070206010803030106081008 80
    0x80c014401d6540c075a500484841002040d01803051040c454280c0d0700c17038191400e01001d5540c03c50a9804082c1d81d5026010300c0400100589003000505003104e0b80c2e403101c8408134207000e0010115107440e400b100400c1119003001450307224100450325032405100000c07902d41d95200e80d20025000c56240c45401500c001510280c1248500c043c01e080c2100b02c0e8044054000e00880c03c0c245d40505403e00800311080020170002c0290740d0011007040c3c4203040240c24081280c4074155444c1084a921001c00c4601102c3d040705640310480300c1c031126028801a0803420106100355640c50000e00c01440c40754005804e526500b107414116903078108480342000c102e80c5504603240d041d0020300c000c4501e5820200040b030400d40034040d1340e645600281c0b84804210141c1c0b1141c2c038440d0082102c001541012141c2040e81124a50326006060a44004580741c5e00d400310080c50501c0050044046400800052145543c0442280d044444a142405040d00d9040321614420000e17800400c0510030011f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735431654 1106 735430548 735430561
    0x4080706110a1218020d0b010f0504021204060b01020708100e2109010c11120102040312031112060102100615090906060504060518030601060c05010b0105040f030308041a 75
    0x5504443c0c610300d17174000c2041485a941c00303691603030b004070061044907403884441005010a4038214608942150307286818503000e400200000c0c0c550001001c140e1007000030303c0c0585001001c1c1d8498000780304002c0c0c0141546030a12100303000d15030329102222001c00364042c00c02c030076084543c41c00d03200c540111040840d24004480703143c1002d1000c00161240440c03100c42c0103080c400160380b5170640c202105101c3d0009460b004040c14803104403032a0b074140b0152030321602c5580791308081d51610801030342400c042028020f440361400e803000a80e2a072024440c1200b04070f81e00c1d40440942c4845d824801e8810a00540c40030920402c02080100e1140d40204440c500190203035600c14680000207050803001e900c1003000401c00aa03460a000c0280300785d036102c0740700342031040c9090b00e0099002c51394041e0344405018018014001028041000742c90144e045030700040106605c0c141 = true := by decide +kernel

theorem cover : BRFrame.Cov 735251798 735431654 := by
  have h0 := BRFrame.cov_init 735251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 735251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 735251798 ≤ n) (h2 : n < 735431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
