-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4994
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:23:56.749696+00:00
-- url     : https://prove2.me/submissions/4783fe44-ea39-4990-bfa3-0b6527479544

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 898021582 ≤ n < 898201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 898022832 1250 898021582 898021601
    0x61c061a031e0c090403051c180503030a20090d060603050d0c0c0605040b03160c05010609020c15070f1805060310030b070815130b060d0204050a080f0a030e0310 71
    0xc0c200ea001d03009000c04010f1080c440005980007400d40c00e00c0c2d24042d041d40900c0380c000b104403101c990307560b0710301c0d00700d810a02858000c1d0103002180c04983ca0215101d8001b01d80000b04940752030b684a11944640000340040360355501084d203402c81480c14428000f0361100107503803160f1500b0340000001c0c0b0800400c0d8500040b0390310160001014278040c01c0160140c1d00880c1040350600003404003d41c00021283c220644950728840113000c0801034880f11140b0310058455441c140000420540c2a00140030240c2c207102612106a08958011504c0c2c200f560400b0008003600f940003050b60241c1500030743c48441840320850303550f0380c0f40024841c1d4003ca500107611720442008008001070800312a4000380075003443c0c2000d141185070f03181c807401c540b41030a104a0000e00100c0302c1d00000c3d0701070100d03000050140c03a51444211040c40180d030081c45140d01800d03103440000342e0440049203418010b00b00c000600b21800480c2c80450f4440131440c1030395450302a070528074089000c9441540d481 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 898024082 1250 898022832 898022863
    0x314090a030909091109090309011d0a0b0706140f01183b010905010c081806161107090204140d110915122503030c080a09120305070506061c061a03 65
    0x2603680310b100060901303044d2f0114030002d4200d090544074550302c0e0307410217007034407419080d40f9124011828618060070f81c000e50401801d402c10f081c441e804519107200383c140d03441c3c003004200c6004021400c83c00c441d110b01c56084a903170484c9006254142c584501c1d580190340c002010846400700e841303282140c8000c1400c0781d550b0341d01c82e03224424640045445034007010f071211811602004003403032070722500c00814003964038003030000c2a0101030084042258081c4040200d8044c65142d2038841c00039801801071103400c19610750801107a1400701200d4010780c0e40103c0c00d0340300210410a007d0b40e06400b424030350f007141c40101d0303034909611034a207034400f1515400010807c4031030a100398540301160210540004070981d4044c80440d400a10041c900c7d0762080040381d03030f940110300841e500025500598841194003180038181503101d0040c1c26841c0c0550709076138403900c41d1002c00c8403036000c10000030012880c503000b400c041141903112414084240882d51041c680150000742403416102c400442c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 898025332 1250 898024082 898024087
    0x9090406020c030c0d0917032209060f1d0112060c09230f0405130803040c080d050c0d030204061407052b02010b0d050a23030a0314090a0309090911090903 68
    0x1400e59021b03180100034a0491050a41d1410317001d249510382c41048040260090b8034504c0c0e103047c1e190030a095004000e00d04080001035200c00c403052610302c0b1440340c0028141d600c3d00e0300c41300c1200c40350000e0483c0d0f81086c100ad5030b0300c0140d4401d070142484461f89014000c00351000100c40c43d00720703445000c0071035011307107070280150040800104601c8036442e20f008501c0e000420011141d10f0580411058201d1500c0d907c070ba40300d2602c00340c1d84040307800c0140d2600988040e200840d8000025000b400000d10a546800d100580b00310200d00892145100041d0b010103885291281040240065805602039624000e141440055001e00160160042d2110030a200866507828810484031050031a000d0402801700e4a9a80d42c1e0070340143c0103000000c6056042109d02880b14019900040c04030650341c9407400d0000c003400501c0502c044007101580760300041c070744500105c0c039040700c0c42d0325803501110075080010715401041802d4044914448648412180d607480170402885206201c0013142d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 898026582 1250 898025332 898025353
    0xd0210180b0318120318010209100509090711100e0c12070810090f420e0d23040902040305210f0901050d021b061b0a020309090406020c030c 62
    0x16124940381604000d40d00203081c14020301d12131508a94100c80c4058900351301000000481e80240b049040840d030240d10801010000c035000000b41c20051811103003078a082d900c80ca803d4074011050700c0c804c40281c20421858244c030072750f03a010392081e80410b000c6407207200c0c84070041211a80e589118403030719070009408100e001010032111175454000384d418402c055407607540904100600e540203104a07590b0800c200d00110700b01c64a4028410139420000448c04144501c901510360301030046d089003403180b40b4490250015031045401d146999001d410000c0c000711010101c1d201034008400da5003000006240125070018102950181000e0401c15008507510500d10f00250b0080019400501000714000d00c02c40c1590300310b107001c0c203109544001c5441c400000b81b10f00701590700000311840381244001c1002400c2031180710030740c2c2c0700c00858008030340c1a452030007900780e104010b0303008005c02c22141c102407180507000303849104054104000c18140c035040d03800c0100d01030a02d0b8040400c04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 898027832 1250 898026582 898026601
    0x1090507031e2004030602030402090f07021b01030e0f01020c07050a0303090b090103020405040e060603060a1e230424090206030f13060c0e0906030c0d0210180b03 72
    0x5400c9005400c0030020b1802c90503030008288011001000c0c1d10341d6801020f2180c00410b0114040480c4050312140e840d034491922000039002603506900681c42100041c03034480f000c2e001a802003440d6002005031040080b500d01e21002000c20709410191501841180d42c10208002280024030000140c1c96403142d110043c03500c049680302901c5043c800100b080840c1d04100442d003610b188402d0760780c1e10845c580058019219690019810914000700c80807941c9000c201d6034003460301203081d85e80300e4a07001071400646140e9840c60084100b01c055401c1e4000c2c850380300b001c040c0042d09080301542541158403038913010840c1d00351000340c0c00c0c002e940001c80850700c221440e84240b5104106100b01c58011501f10b0200406000a16101c00003081d442d82c800314035140210340c4a04184200d403100a0000c005100c4994010b0083e400480810554a40410784c000c81c4c0c24050315081d80c40400d6000c0040030001c0d144040c092001c10901d4140d0251403940c0c00e406890000f1800350740c2c1c103261511 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 898029082 1250 898027832 898027841
    0x90c0a030b1e130b06030a020a031a0f0613030506270d08010312120e07060f080f040303200d0903081f060513172103040c03080d1803080109 62
    0x140e41c4200e4022880b2000a001c80600c00e040385010f40e0003002045101909038000c1821100003580030380003100b0495a510f490700100b26001c40c541d014010900070507030903994110004051584898040c00035129400d2500c084c0820095204020410740c2c0d603034948600301001641d5042c4480ea14011110303000c40210324803440425004001c0152895900004144100c10300000300107481c010141751806100c0c20b0100345210b00810200b0514128901d440d5951085100b600c4c00302d110460040c000324003410500c0d01c501c107002800c003403550384c4c0d40e800c5005008206041160092a507a0040703950540c8015110f8000d25003000240c1c44070034200609000c03030090011a031155101c500c290841d155018040403554941442c43d11401254140b550441c903941002c1d6446280202c45010507a00203000300c84a82d0700c0c605010b040700721040c0302c01070784400c54018000c01c003440000c10020341560f0084c41490020440001d0070084400002200030210006400041e040401404588901d204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 898030332 1250 898029082 898029101
    0x302221214070305030d05061f020703110102010b0d060906021c0203010914091e07090e03040f150504030305130f03062c1902061e0a030b0603040827090c0a03 70
    0xb0145140b55580b003980d20320a2002e4000714589070030108405440340230400c1802c12021f1030388040340e04103590082da28801880103480c811100c6402d034602e940188108103e444000d0b014800da8000d5840d510041c0c1440c03071040740c440b0340c01c01c140907045212041d00351031030680150140e41ea514120004c03060f039140b12420305a0100310400d10041d610006504144582910001f80701401c441d85020305190042e800700710120b092072500c0801c1d0f0b8000c0010015502049028800284c0f52000415071007040100600854020401440030a00030710140600d02001c5069041d81601c0b018104c00d00380c82548201d40250301c80e030600f15006400424000034454070400400069045840c1980c0e0b40c00c0b01c100c1102060000703c03c1002d6464041c100c9050001d4002200340903214080c81c90079691181c590100041d00d0100c0c955224038025048074000c81e04030a00c00d08000407085103c03400002c050500309212502400032034240c0b80c18007400d00c40c3c000003c1030354480342d03c00005003d4941240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 898031582 1250 898030332 898030373
    0x909050c0a0c0209093c03040303051b0309030a06090b060f1323011e0e040308010e091903020d090905101a0d1407030f050601020a0303022212 63
    0x48010002076201d504800d84640444d80b402860f00d0701c6211608003615030740d81061034446003500b402c1b00c0107280e0010b00786001c81d07841c90a00000d800413494803030003107000050018404004401c051008160921100c4080d05d041c2c86c9003c01d004002840c0c60200f0030202e8082da2a0800c5034240301c0d00c400e205038029803e5411203c03d1030030f400080c0442613401c000c07540c1d01d81d0312801c4058803260b0b10603000724501071040e50045561242165282014100100c00101686842c04507820510700c000d01c3c041c940c940c0762003111340d003850404492004d00402c0621240300b0071440c6070003030261102c0780025074000d801034055807800c13080c01494540c00c0d03003002040034240801e00182124880340c2c1002c40d820034a40800b841079504035400507102d14115000759504044220039046044003000d4000c080c2900c04001e8503224003441010342e04122480e50258006020740e10119000e5001010480410300c216139101002800c1944150440d401c45100d484010159404108080503948080300182 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 898032832 1250 898031582 898031587
    0x4020f12250608042d0602030c090f030a05031213020315010501090f061e030b180106030b0109062f16050f030313060c050c04091407061e031a06030103030909050c 72
    0x2a2500444104017480104110041c0649901c019004403101c0003840da2025007550f581c24050000c140a8010702040c502c182440d11004240c0d141c0001e800f071b03e169111000c0c5041c40108404125100740c02450122040918245100182e5090142614040702104c8640301d55041c00c0005000e0021a004203402c84c40c28103050111a400803403000c0c200400800a07030315206006402c8000d413200e05401500034a00c01d0030042c1c003e01264009042e1030196504100c205031100044440c10040c0c49a0008900a0320300000c0d0304981600340c11104e0442407041c261301c080d0345001c40c545800103095241d510800d040c24449450100012000703044120000c5003448091800026050101d128000902c50203590200400005001c0c00003403030401001003007013a91030f040c0711401d4054484809401d025469001c11790758000c515000300307496040b01c1c2c070040160906041e0b000301188010210340c1c000d8110248100d41c1c4150080d07000e10b100b84e03603580300380c0c0c641142c0405807140944942c42d41c100c00d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 898034082 1250 898032832 898032841
    0x3090d0207080a20120d0305060109030b070f02011104080c1c170c0106120b061309080f070318080d0212040806071b0609200105090904020f12250608 66
    0x461000d11078104ca0150351880003201c0703409644c40041c4425410244003460300107010000320b4440f01c5186140c4081c480e9a90b010300445d454002c9000c01030103c12602c0201b901c0034801ca121340c0302803030540000910000003a0741a0324079006580402050341c010081071816007082060002201141c160100303071040c00b5903442440c1101903070100c19411010881c5405600c09411840c0149400d90040b0f00071100c0f400d040241b1841204e41c140100500d00d00741003820028842e005074603070014050307400c0c441c008020000b140d000c9901901006607240340c01d8090302043c2480001801c9403c020f1161204094002e801c0201c0813646d018520428041003000365000709041c3e500002500d00361080e00000d40f01840c0d240b1480001500e0715103880380c0841041107158443c03c5440c8584261003e807040003004440a02c0780113006904803100c5000321f03006040003c00c164410350010403045644040804051030490003800110422000b441c120480c0c1140382203500c060030762440e00043c01c2c60b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 898035332 1250 898034082 898034099
    0x80f070611031602011e030f0506030a0b01090c030608100903110a050c15120a0c020f0a0510050c12150a14010e010807091703091306030b040f020303041a03090d0207 73
    0x583d00300e03441c414454291040842e131042c0d804802d1240d1603402214081150391008004004441d02103440304d00d068049a01c40c40c000414051481d48074580240c44e03802c0c481001c0140c00c40d506808141910f07900081a02c841c1481010321007601c00c03000007084115824010302e8070a140800b101c03550415241d84020610105040c000312906a07803201c0d4035001c401c10343d06d0a216000c480380c0a0301c014020b04c08002d40c0c9030403482c03401c1c0082e0300700d80c410b1030007003805a141d030014440180341d5804507000002007482e5801855200d007090004600384284162140364800040711044030070440c16000300b13524a0010080d10140ca141c0c0c0d5100489526200081c4c12145000b01e81818481c0410020b81007603c00c4c200c0e02c02400d4101803045c009110303040d800c4c2e0380e9000044141d111300103000103081c3d41216442010101c2e07400c4039215900ba1555110041d02c4003004030141c1c4c06003c104404210554001900b8940b542980d1865a0324074021044c00c0c2003001010207202150071016041003401c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 898036582 1250 898035332 898035337
    0x203010803120606090a090b0111010e1e070321080a02070f030c0f170706051501050a120b04021c050603120a360f08160605030a020d06080f07061103 66
    0x410442e00e00d6600c0d00c855000a000e4001c0c00c070b0550f03006c00c004801142c4000250030100044030281c82e50039880004c20481400c0e01c04611980c1515805803a01c1d0581202005a00c18a0369595054910f01a2680c480a40384801221407000e0405120344030201151b1040b032580c1d200b0402c50b411070074140c0c60303a220100d04020306805402c001c0d901e0580b0090220b900c0003c903c443e40b010704116100f11021b0408010b400404051303036454507000005a0040c240388a4034031500303050307580c40d160000e441010b0754401c206d1300c641c42c000380d41c0d80e501c80040c2c2c0300c074401460003044091500098000845021041d600000c1c080380c0030350495903900180426031010b031a45000c00b0705080071101844c074a08084c0411000750102c9404402c030b89a84000d1080801e04159000109840d03001794640700c2059032101c44001c001d03904c1031804c508010551040020b141c200400c40d002524010281400400b69140303a00720401942008081c0880c002d42000208001c0c0090300b002891441c4644000303884c0d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 898037832 1250 898036582 898036597
    0x1a010b070c060c11030d11010b060711010813080301060305060f060c1e0a062306091003020405071103072f0f04020c0f0f01050901110301080a03200d0806030d030203010803 76
    0x444000c070303d0070032905560000040401030304490f06070000100003024607140081c00c0303605510f00711b0b01e820107080510848243c1b5420030050703490704602200446d40018010a92aa0840c02030f42205c00940d1a1006600078103075070760b000c00c0c1810700000b002050364198050b0340c0b0802c4100100500720101050b8071880300c0745450301000851108203020700340012000c0007000c5c9854a42e88482441c4001030380f0341200000601968555510740511154581c2600c80f69803109181c4c00802c014581074001d02e52040c154941002c01d090301d20042403543d0404802220b0040707585181e000c2010010711000303590300308a000b1100504852011400205041405902540e00001c80090025041001d102c803507021000321140e100884a07040e0090805a071118015424602c9103128002900e013564103842864000d00741c2441305690030348c1c6403c03200d8400c1d2029000c11003e180c21034001e0104040382101d41d1140b44072807034a4400c050030b0040c00341c986004e0520500040c0182d480000940c1c150 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 898039082 1250 898037832 898037837
    0x80115080403031b0203070c0b03130b0a090b180609121804020c0724050910030504060b031e161d0a0b0405010f051c020618010c0606031a010b070c06 66
    0xd03100c1d820b003100908071448054040ba2840014075003602d034000000d2801c0350140b00065200c0e6111004c0c41090302c01503540e0180714903000c0241c00451402901070b27070041e00e400c0d00052080034540d281a1013410440ea15010740c418403248030402c4c0801d2224644c002e9a05014102c00c41b0841c1c2c20501900a40743d8950891242c113480c1c940c40d13116503040710f02c100c030307040300b261800740d0f5130312480072268400021008c41c04001100c03820711500030401d40d4501c40000b001c0320043c10541004600801c802041940c51540f1403a0101c400e0320140205003541101020201d640d0082601042c500f440760080c69070800c110010030404440301c558483c0d4940c000c4c82410700980c8541c00c03e040545802d441c1c841e400351401000003074031a8001019402c0358070648022094000300d15811455510144010b50480320030801204280381a880d040c0800d101410450405207580d220f0303008443c1c0d02e410849640c1400daa540d5540c07034884c0301550040045270642c902d0306c07030b00350fa6211400429210311000e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 898040332 1250 898039082 898039097
    0x30603011d1e10060b07140a080301030605040f021003020a09270e0f03041409070807120203071407111503190216140706080a1a090a02090d050a0b07080115 69
    0x8802c44140032a0718103101d5082c091000e961110b0302d000d00e0741e00c0514100c5540c18420390380f640d202004124906c010360420300b0359045a107183c44180103000028422203070711903002e003031b10b00507a034134071001b01103100d81e5034010303201c800214000e082c50700c280d0050000740c28840301011102c2c100641d248020f035070b095800302d00c41e10f8500c0180c0c60458080c100000600000c00e011030f28140585020760700d280308484041c05921040d0003624007000a80e884800a8032850000768085095001036400040900e41040843c0343c0d840340c2640d64000d8001103940e40612400e103c0325260a0600703480808004045038618149001428205040c04034990a0141c01084140504641f1034140b00081e4124180c0c4600251501400343c40e000580550f201092508021031447c10a6100d540b0388200c1c2040d0030308000040d181040350341c400041440c00c5003602000300308002c4e21900f203505e43e0b861049009108003a0039141c4640c9076200185510308003d542001041117204000161880c3c1d51982491070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 898041582 1250 898040332 898040383
    0x90e16090c03020412050f1002190f020705030a1a0c0f03041e08070b090f010c0e040216062d09020d020907020703080c0705092a1b12030603011d 64
    0x38042c4c00f03198003c0100c01d5180c8185c80920101150b07603008006010217841804070881000c2c4100d0064991103103409111031400b0b484d00e4000e1100c00c0e041590b50040358046a03480700084d290600682017150440c1201010510610255060a1700300d17482a2507107003480c81d480b913009024000100f0151120110031001070003041c802c40c40d049140d800044903036075503401e800e0480c941d030001c2c1c0b64030050b03100350003c45056110601c190201080c06035502182c610003502040080c0d0001c1031159580d035080341c0c90600003241403003000040d449a11039003404c024020f41941600c1304c09442c0c1610582082050070040c1c0c0c8800d00f180c1c0c6564100c441d400d964880400c101e00d041d400e9080205038101c0041c90520b803a80c000342440880f0b074111144100da40d030f01c000c0740d0108402c450032424402e80407421021007100700409007654650b009810f0001c80418268a40350ac19582415a042c040c004140082d1341002e000b801b00c1134191100840c1c511880c107900c2030b5500452100d8541711100da0030201e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 898042832 1250 898041582 898041587
    0x70c0f060203070f0e010206060616031101150f06030629070b07090f1a070b06031002040e0109050117100509010b0901080d021c0206160509090907090e16090c 70
    0x4150440e0054000c6480740f81442c80a8071503e86012900041003140e075540480b50b00c0020b041c1d2281030007818080c24003080c00307040b072007010070303817000f102880202c0b0070b5078030307664001d104486d02402015058540d0b10f26050300210181d41507007000040500304034041c440b200c42840f0041c04c2100b002d1042c401c9020300385003024103024543e4014403410300503052200d05907011000901340c99400b101c40d0300d190707030303599038442e02800e1007103880602481072040c440400c440324459035201d040034090314040095020710078100da0140e0440d1810188000c0140020380300c80c440d00d8054210700e043c04403010459401c1e9507407011040d448114a0380c0740d000107105890b080d04412080040a4071920442d40c481d08815111100c102043c0300610504207440c450324502c40c03072091500300ba600580242d0700d9402c10b048990000f00d16000038001700b040792010544420750480d1055039080054860301d42008040d40a0314043c24809603d039118026a070081d01240070000111002c071a0000f86002881c0300a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 898044082 1250 898042832 898042853
    0x9031e021e0418050a080705150c030f220b0402060d1a100201140f07020a1a07030605030d1b0c0509160311040e15010c05030d1a0a05010503070c 64
    0x250091800c0e80d120014060240d40707040742480454042c80240b2501024040c41e0700c800d1005460385e40712100d46000710380c014005040f00d034010020755009203414031811800c0e00d800d41e103200824a0010401414803a488441504020020741560380d800e8150f80d85c0c4010910524080c0c02d0100d100041000c660311a000c07181806400309040c0002d40201c10407451401005d140301c7c0c084e0464182c5007090714410b126a041d815200d031b00340c10540d2503202620007001001440b04007580300b500703000b102107104032084114100c560441414580340200c4000c0170784049034003280c045d80c0807010a15546410130899080a002810355071450500c504004482a40b079034400341c0c000c20304000f4094802d50a00040c0d14107001520244013001c50040b000400d4401e6100c0c0a056100480109244007203c90703900402c3e04051600b4401040c5944031281180d1040e5019600036540c1c0e5440c007080144003107a0f20420310105c81c081c1d4418500f40000e0725904c402800802002802c034448010490060103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 898045332 1250 898044082 898044143
    0x9190f020703080912070803040303021e030114030f1c0912030c29010b0c2506020c0d0503030c09060403051b0f09040c060e01111f06150903 62
    0x148010220614860001e520902080e070000c3e54200020b12144030000305003001000c850b40e4180780c0880e5456460403600f001d8022020140c08200100d11490040c00c2541402c804a628541d254034001080da00300003090041d0340250000c0c0c1c0345001d01200800c1100240c9044250080c94001c080c104031110b40013a000207030a40c409090b03040a0541c800c03000820a0702c1500c4000c02010101c000300329a0410000385503003040911f0040c04010401409040a05000d008403000942c1c07104014050070108604d85075040c0314200c041110715410003c64071880c806a4151041415540702c1303940b00c2c4030007889601d1203480042c0b1132030a62a0101160004d641020a43c1c0d15641200c070244a0b021601481d60f200d84802c0b96160801d1400c207a0103400f071070780b202c66401d00e545814405c0c7c0d00c000c021540c1605001c3c07e806070410144c4140801e801000c0e1420103030030039148401e5003004030343c00f81c3c0003510908480100500840e401c100c21a080d203800403e2108040216100380f50b4101d034084 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 898046582 1250 898045332 898045381
    0xc14010b1c03080c13122d0309051e04050c090a06120b04110307120b0d03080618040b18070b040b130801020f040b0c150106020f010c020c0f09 63
    0x109681c15400100d4080d0391041c1c482e80d03039450702e600c3e203240c0e100040c0a10f0040982c0d01c1d000c2c040400603d488883c00e50303213840c86800340d002d56140002c03406c820380100c40c1000f05140082d890f030b2010140d0003019036002c3e0008854042e02049245903114094038007415060065a50340c0c08903a4403807001054440100000301f00801081c0c4454000344180841c4089078442820a1125000c518041c02000301d1091503862483c00c540c0c074200f048030440c1121100c4050346a5500100c1c025403262003c1d46103182c020340f80c1045c41e00740b0707009101350b5409642800c03d000070f04400707120008030740c40d15489e00090120301c810300161140c2c202078103120296200b054011000640090111034020240c68000701c617048203180c0e250b580708814203030700c10540c1540b2402000c020034031480c4d2045005d086a003070b4001c100e40400c00107a824200c01142070300b020015912407400f40d0743e0380000f40103a8060061500c05420100b40c46030124034035104020125129440620000d40810388041d521015003400a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 898047832 1250 898046582 898046599
    0x20f090705070b0105011b03050325020708060f0108030301030327030b0411040911041d0106060503330108091c0513090506060307031e0504210c02010c14010b 70
    0x503401038181d9014100c1202c14410101c00001d80350f00072000400c01e20f5804001290f8003046541c2121254001401c4007a0058006021380060186200300e0120103c40c3c0c005007041c5041195242c6003c174018400300c1c04601c208010f024210000c01980e04496150a00c05005080070408421118004c004085900791403040041403201c095031850080d0302403114010303441a5001480301f40c0713015040103000302600251210301810940d0100120104065524259890340c400460a50b003d50740700800040c004020b200469100d060f04c0300d40c2038016000b000078030030300120b84041114043c100340d05025400700050074511003840b2261246110205900703013121080f2000d4010303007000e400f0050306c0c085100c02040c001c1f00e038450740d4020000105841d0855a80002c118090644511800b0750038036060031640802d6401c0c060036014910800642c1c0441e141d2103001094a0030180d41c220400070760b00c0e00d000c0581d030032a0300500307015000540c84000c00303507031010341b0301500c00c1480031038000d41c18 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 898049082 1250 898047832 898047841
    0x309040509070b03040807020f010509092d040b0108060c041202010804021c030c0b07020f06040b06210303071e08060f03010b0a06030b040606090503060109150f060201090c0e0c070f020f09 83
    0x2818800d100b211120109c40343c2000454403401024019a0008500c80200d50004201071000b0102c1c0702c0d01203400061288020394042c440390179a000c98000d0540401840580814402d4a51010030b06002034102403030408200355981c01050007a06000c0d403400410250f454205c0c50b5102c80380841c010090580581c9401881c94012030819140c0d01c40d4000820000340c4041002003003054844c00401c0e15491f981c941484400d4003078800c030340c040e13000c140c00c4917106040c1010105001e004c0002d942c592030700030b4002e0003403d0140c10340704510b82c0040c4082040c542103080c090701300030140c405c480800f2950010900504203982410b521818851000076455819000340c1c1d98160b05917030070b1000310340d1604161344002090048540c1504600018803032800950300840101d410400414240c03907640340d0511034500c03580c00c000c005035150038a15080c445c4003642c24009100d05030856400740303041c0384000310030300811200170130020079620320009641d200852101c4804005000c080306041 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 898050332 1250 898049082 898049093
    0xc05040f0e04060f050c0403081602100906080109050103350c03130806090a032d0507300f021c030905190503120718030c1a030402030309040509070b0304 68
    0x1000c40701114070f58100213101d95019104d020b0607009010340d081c2c85080500755540d8182c643c1100758003594045541d456071026944003c20811a56030079100c448a15050120091490f90160004c0910a080000410026a00c82804850580302c2e1407045005075060010444407518040030786041400071403031213031415000c001407110f14000000c0b07070540c50381c0b140d0260b1070300c104a8058840d80c21003c0c0640110303000d03600d11820f24844038489001803000340400249400030584100c00684040341e0307002040000781445c0d0440e4142444500c440402440391202d40307500f200d9440400803090b0641caa902e00801c0100c4241300d030701c0001191684000e000400908100b1400c0d2071605c2200b446100848214501152868209c8003135403078102004200c08152002600400c02c00a42402e00484840c49480700f00103948120f01101100f8503182c0048400c03807000021800c904070400c10b0000699000044404200c2e066030042219641c401400c0d040c04038603400031501d100000104410041e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 898051582 1250 898050332 898050359
    0xb13090302070311280510090e0f1306050103060906240501300506041103040b0708150d060e06060a0605040e1807060e043b010f020a02030706061202030a060c05040f 73
    0x85e03090700c2d03000038147d0034101255010310f20711032000507916200104800119000096034003c1c42800c04d08a030004a69820049482c264030544400d40e842e00d03c0020011107004040c070201c0c40c20200345000440c072110203c4101075206a0b4140511a2607020f8000c04070344000030b54030b24407808000071710310f0030b2107140c003a04003101e800703200343d103032600003003884920005030303406260000700002d415603130b4040c26184030401038120340b5812007418100c450303581d508800074821481210041440c00c0d000214914222024204c184110348000301401643e81c0038003910112810000420608c0d00c0d0031132407940e41454070718201c0c914003a0080100301d843d04040d102c4003001c0240c070104800614062a102d031028202c03000481d0000c54040048a051148034116010000800028030440301000d40f408a03448140385001580020403601d0600003144a810003e109c2d044075108032160340c0c1d0002c0d842e155040f800074001562619103591682c404c00c00e81d4083c09007502000c550310345602e038502940 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 898052832 1250 898051582 898051589
    0x30e040c080426040b0c070f03050d0809030301080a06050414070f180513080a0908011802150c0d110f060703050411100e011d130b1309030207031128 66
    0x7080c990002559200d040c0c14030350006951158107820541090700c0008182e004407039401d1107100c2c2d8030f008a2300c0700800000c1401180b10700c0c0102000d80d0000804bc200007002440e0600c9a081030004004010740820b00000b05036010f1400645691146000d80843c1e005001440080c030031504045681c0461513000070070381c0c0c61282c19030b4131003120384000f00607280d00301c6001e40c01c04c2c8003c0c140c00c00143e001d006883e0841c00c9052803079006403100101d81c02c44801c0c8040c10011640c9188600c294104041d80c00da0440040c1e2086142201d1541000d58a05000c82d4a008120020140c2050482c3c10f100603403d440c0c000066074a2407c0001000300500320607107040d00c9080f01c2a000c10154175001c8424040c00c4a03a03160320704510f401c00019500f00090340035009040491400300d00081d0b803a202528115084080700140c0404103c040c050000908001c031000f552504040c8004a80c0004440c0210b0f9402144440c4068040c000700300b800d00c500154400e161820f903107400c6174041045086c400e6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 898054082 1250 898052832 898052843
    0x20303090f0c1f0c0b090303071b0f031404030606121208041110050c0a050a030f09030b0609060a0e0702010f15050105030408090303090303040816051509010309030e040c0804 77
    0xc40340311080191281180240303580d00020030f0f458200003115482045460020b9803d100500030b03142c1c0c44081d54080304403900386c45a0000070400114940200d1110181441a4141f00c0802c0155940e40302000c1e01100c05403c2c820031051995003000d44100700c5020315840041440060355030303030004c10030441c1040308803001a63b151110816074030503e841407180d40c200c0c1001002c1c51a110500c80c0403441d22502c0001c02c00d04001040f0f40000030031110720024450802450303800030301d050042031a071070365925208015000b0810004240d14000031504000c003200d03803424a4507828000380309012036600c00001c4039403840030880b050780c041d40a4407103081001e40c1801824000d8211082c40c0f0040d00444e400305a00348041004030301d481c4042c010928016045034604400a00003e1440c0c11a030300032101603200d070140aa02152106c2420b00800040d9098101640d8858240d131160151501e0f0324109035540295205040c030820123252469800f5008000d6504007000080059100303c5003540d5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 898055332 1250 898054082 898054093
    0x1503190602071e051e1006061e1e11150f1501030c0507030c02040905070b0408010c1b03081b031509090606030c1e090a05071209080a180801020a02030309 68
    0x281403010290f18010325501ca40038102004a40340209110102071000126900c25282100503c05851083c4009040c0d50784500001007120160b52070b002415441c2c02040140d0041411130f0240071310700004402101e800e04080502001c6100d40c98007007080d801c410303440c00303038800e014141c61030a541c10300448c1105e588440c6808084010b60696600c03195060005000b040b2501c00300344940514040c480c030091003c01c41040e1030319041d10740391441d00719007110000041d00300a0b800091040d105550420305041c07400002840380107809044441001e024410528005549850341c0751001c4011145400c102d612800c20501524081414001e014044d5103a1b2000c01c064500000300640315072001002400c0f0015a0740500081c40c50702184809403c1d180c640c1290b269503402c003c1403040340d19940004841c509035000030012000c601c1c149042c50714041c0300c2c07804114803a00300d84980d030316420082c000c040c800342110301c400300c6a40076031072951020950500c0650b02000644c0140008402c5a8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 898056582 1250 898055332 898055363
    0x30c21010312170c09040b03070e070219261201031b0e0118091707033f0e100912020607050f030109090f05011a091e150319060207 58
    0x20f42c980d0484400c61404602c1c0c90008941c40d203007400501003610090400b0908020040100340741c04007540004407484001d00c1082030030f6504011000c0c84003030b080440ba40c140382d04d4039814600780c0a82c110f81810f2000c10701010068080350f003200c000382a0100c50800945e52402d0106246c1011100c412414105a4000608843c154507150603124051444203c46100c4200c07140200741c0741d80c080b603400c10101040a61011104064511540640c80d20100e0f000b0f542c0f5100d82e9558a100f0340c00606d54a1049483c548030600740002039095a140d0001d800c1c514820140d240106000c6009005801c1c0a41402004140219040e541d09180c00320349854503601c4098a041c054a1080740d0090024070040001e140703280c0240d00c4590241d201680384614640300c003400e6504065001c4003141420103003855031304008a41c1740e030010b0070300c210580c068003101d4009800c12000c0c00609100301040040c110690307041c040d90b24110140300c0d000018000d1860140f000e500080c100b40c0343c5906240112 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 898057832 1250 898056582 898056587
    0x14071503020c03031306060515040806070c081206040b1903230a030f090905010b1812100b060c0102130801060803130909030e030f010209040f0c14030c21010312 71
    0x31500c124002024600315500c40107030b500e1341746800c90141c0d0f01c84d488010000c3ca43e2038003100b800d4090f843c80c1d01950f5541c240f503000e525000d030140048042010040c2d420000c01c048030140d0b604000c108d06296140d44451000034040c2148110b19a07122842c5003103100304030615009842164819151000101404a5003905e000b0300e0142041c0c40c0c0e007192000100003031081e2001c00400d26141000b510741512a0b03180011200c1c241c101480c00040000c018030441d200589038858814110f41c40042a101c90006580310010640c1c0020300d51f0302e51080aa0903a648000c0d40c0b241d4001d40001c43d15001c02c04150344407901c883c070411075070f03510701100800c030f83e54040112400d10040306080d415541c41c00f02e80c6401004c109800b9410807890740681e101c1540c0c103003c401c1d500004480007580314802c44003040b08480318609085c026a10f4080c4616211350000c4413643c4a40000b001907860356204031080e6841d218181c41c014075100640b803068010956105040c0c123036401100302a82c201d0100606 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 898059082 1250 898057832 898057837
    0x2070312051003170d1a01020f010903091802040816033e0301021b030409060501030605090c03040f141c03090506060f03100e0606180403120510031407150302 70
    0x2018002889030320500109102d410b071460013194208007035281c0001403d14508451050046208000b42000c80405a60f410000c12024031000c03002041007803150b541c0038280e10420320540c088d1090044081e501b115041d0305907401001182c2c140c4204020100c4182e5002c581c900003103564400c03140503a02844080034000300184252014141c511441812009210010707005a6034159020022140c45980c030414000c0310415500003152110b00f40040c0105480980d0841c81c101407822000f0042c554460480d15048901c2001d519900e80320740c28104600c524409018108140a010241c0704060001e03640000082541e00100e0356031035400d0490640350b6040340a895580200e0110f8040c1c5005814640940001021541c11072411070303041084d180410741015140d0401030401c0041d050a0242c01074034101c0c03001c0d10501c1d281a96021308000046515240055940d40c0090081c8011010070300c051900031114035041e400f4582042d41e910b0690045400e003003042d040103618580030780207 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 898060332 1250 898059082 898059091
    0x10213081e060a050a060b0a090807080c0d06020f1201030b0105010305010b091f05040801113114040902060f0a12020307140d02070804080615060717030402220207031205 75
    0x6042c40b610f0300c82e1030501608002d003410148603607485000918010080090440d191552142e02c001f03454034644038102403482d4080382e500d03044051651413a07a02d008600000715032084c0c2c0140c88468451000da51400360202c0502c1d08581d03c400070080c00401802239040304c0090383c0034010b03a80c0f5040c0480c1c09000705a0402c0e0816812113080c440d42e4280c10902545101c2803a040d414143d5800e005803e41e6400314290f4400b510021b0094125840c036010403000032008096a000b10350340030700111190080b845500041103c440c02070701e0558603a0407001e41c4640003000c00d900e454031554280110362105080c0000f18080301601c081c0070145000f5a03100e102e642e180c081d01c000d410101c90980d940000003c1c2e4a0681c200070039800210301801920240c10000020102c07403914140704014038406035030307541c440e810602074900000c8140f049011503000744400310b510b0303072941c0c0f020030b0302002502500320000c40a50b8a0060051496001c0c103a030500a0351800c40255580700c00e10116201902c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 898061582 1250 898060332 898060393
    0x19020a17010f140f180a0b0f0907092702070c1e150c1406090a02011709030f0a0c0210052709040212190803040209090c0906040b040e01021308 63
    0x15107003113450403980784c0c3c3ea0241c01a1603c40400451a800351707900f03108440340400241d80b009850403074100f46105000f840c0e030070754400c040c41c144294040d051400903c1400e6088009420012580c00f441d050b00e00d0107010100255210803841c13825607602050750080e00f40e0360120b0310080600300b440c590414111207440400414440462308101d0303403c035000c0c2068a0380400f0341402000a0810440644242a5034000d8640c811583c80018181c3c10300d10f24080c0c84009140901040140101c1150740c1d0707031000c00380241e6030110900c069880e0303840400c0296002c00d0207500f060720b00d1340040003450b00500122001e5881000d55803441c0801c243e05903100d80040b800d100040041c14102020000403e644007200c03c403503298481010184000b0004441c0040080300b404210300340440225006180c0b0310160800041440114400c1c641c0101264400e40d2101c503400003c2c0c549501c1174030b88080c40b4000790b50b20100440b00140700708031481441840d10074405000455801c07550360005268074034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 898062832 1250 898061582 898061609
    0x20106240c02150912010e0d02060c0405010e0f1e01030501050301090c0b03070302040e010b0405090601091401121506050304021e01050714070e1608010f0b1219020a17010f 76
    0x82e024000c404183e03042d0300c40200010480780b9000c1c0d4414164810550a020001c940101540211800c06a45104490541d80801c0a1240c0c1c54903131002c1e00c058440070710b0912200a0075000244c030420051103c00d402041e0342c400b0348880c030b20420f52003502c81c0e401c1c4c80a210590741c5005042c205c61282401914000d400c05041c07003500104e0008507040462441d02500b820345402004101e01020b078414100380324005010012401d04032000b6a0007802400c3c800c64842c076107803000350136601d00c010300744c1002041601d0f5030700d800c91a4440d200f010a02030f55506903540342c0101400c0c960060320268803c0796600455414140d1701494200d203c02e040c0c0d03e942c18012103569003200a60f03002d00d408020f000301d62000c620121000d900318440c54110900101944c07000d1000b0702842010f82059003009600c050078070064544008980f020301c6443c10b220020b80c0c40003881c2d90081100c006802c101800000d11031501c40d44000c41429800720b02040340c4803a44e031a0329070822040300d0f119060320701420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 898064082 1250 898062832 898062857
    0x80108070b180a0f030b010504200a02010e0304143303071211040306050f0403091205070905040b010608150928050403082413051305030a02010624 65
    0x481024040b8060303188240706007210300000003110301c01a9008604401110201001800001501e1600408e802c4d5801c00401d07121000c1d881d6100d42d02500101c00000011340000040d1007580f01c000c0c22000a004e594607140c031040f00004804118141a11412003104e4034041d01c400042c7c0380310b82403006141c601c1c00a12441780c4a00c20b0300010107110078880060403201c02e051080c0105901030888003411036895040d0300e4924100e807005449860002482801c010000e500a010034094904248088003282e0207031404502c0c100d520741094040743d003010107100800880c80f1899060302c500b9140c225055a540000c04010081d1856441d07000d201c06000c507201c802c814030b480c9842c0401034200e64120081c13250560549400380c9044000031030725410082081c83e22080407881550348009030b40444074890028060401d10514442c401b07980d000030400c06502482840b400300d43c0007050f0307615211001400f0f07000b44a244070380b050310540c2003190010144e90001c5004540080e0f264040c1c18a01d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 898065332 1250 898064082 898064099
    0xc0b18101406120a0f0602120106020a0c1406071406011401020d0f0c230a020a1a0913060e011206050a050105011b0507091e0b01020105010f091e02070b041208010807 73
    0x2070410582c1d55600070b0800803404181d0900c40c1c0300171036000ba040076a03a00054000c1c0b040954050b4406005c6401000e4000005050590310200f2280084c1110401c4d0740c3c2c000008446110b401e00040c0300741100b002000c3c1c00c0c00080341035412900040d08185d0980341180040e612400c88088813000920030460a9042c28000d040440c150342c01202e500c45184e030342c0351400401c66084144070070154006509001140350161509001d089600311003000506000d86d042c900e800b603085002d00c60752005107415415012135002d5001084c48021211407541e49207500000c00039400300c00e0f83c0d083d0400d800624806000e00803a4100c0320180d41d41c07640d0950307124580d0b403d5091000c044a0b14082d00300005054a5240900b540c0d000d0240c03990b03c04400014091000c4690342040700f419641004010400703200740c0c1400c2e004480d00e450001c140c40b520309100c4c114048200122031076442c0301051490a1111880e1040d206610445008000e2854500700f03031007103102482500c145500400302400303c002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 898066582 1250 898065332 898065349
    0xb041503060f111602092406160b01060906110312130f060507020c0a0f1a0a050d021818160c03030e100509061302030318010c0b18101406 61
    0x111220360000d0404210300c884a5035a12400d84c0420307103100ca000220641c60200c2c2c0b10ba0300038060904409080310f10020303402042d01030381806441074902140701403401c03829001501d00c0e650f106140d981c0560310786002806142090144100141c0c44200001003094004101c454504954030041c0c40c075620a002c40420f6071440104076000d0400306202e40016829000d41d0b0302407200e940141003028120b1083c0030644040d54003600d152020103404000040001001c2000c0e40e0407443c91750f650b00311188041da924490650742014003840011022401c0102501600001804076000da14401518403003004d002002d5644c3c04d8000c010081401c03d07603004004009559109040124040c41c0b0009010309000031800d0010340075480c2c3c0c0810075010742c107001072680300c50b40c031070080e1b000a52600820798a0044405d13507080c140c03503090140ca0580c00b480140c2c0c0155406100c010a0745000000000518807100303540308144107807065040604003a004160403001240600b20180d03480808024841 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 898067832 1250 898066582 898066601
    0x4030f03170403020d1b1707030c2012010506031e1204030f0b070f0f0315080a060e01050a060303142a0c0906120d030e031c0b040b04150306 62
    0x2407051490260030125040c9900c2980203030003030480d1002c18600a03000410800070b114002c0110f43c0010002001150028400c07500242600e031075104916068480741c441c0c940140c41108890f01850503e500c0e16400880301c0d40c00da40c031010b03030380a481c030690036200c0540706035a050304020312640109051400001900d8410812507101d114102619003440d40242c00030341d40c40d05550500c0043c4842000215001052494000b1a82c5924000146000b5400801c4020580c840b0030561081d84d85841440c050003495090303030150441490544c0080c210044410b41795405c0c0703800a000807881303100340402c403609a00c80c100c2042d00c070300038010586c1c80502141079941e51644c6101488603041c0b0341080300186c0c0c3e00200a504144010030401f61300080c9000e100b001c0c020380c07011580002080c1007402c10740303504000c103400d046601124114002c8010039140e003041e03081c0401100071280c10940005500741c408108025142060201b0f44111003280c0342105150001080002e51583c410400c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 898069082 1250 898067832 898067837
    0x8040c17070519050105030112050a060507020303091501050f040b04060801020406180e06213306030102090d0206071b030f060b031c111e010c120603020604030f03 72
    0x9900d80c00461401a80a500c09a46510000c000e0025007008400a61241c1010304004100ca16010008200348014050341c02c0016910355510200b050800480080c554001000e1005260400009540c1e0308200e40e5441d032841000c10510742007045031030343c40c142c0c5d8000d04035507a500103080c00d100c0501740c2c802c2603e8100e40e44100000d50800284090009410596038062009510644031a460506a00301e82c207018002018060f480c1d0302c030a805130b60710752a50054100303110f118044a052500c085c1c0795440c1b84011101c1000038010000f08101d921a003450740114507120001414200c0c000d81d220103030040f442c912020094a4040d008d0700400c0d204130300c0c2042c50000410b480b4840d803a69881120110b00c451179500c200155030080240e9204264000c02c42081407105140c24180d88560045c00d101d071392041603044200c184003a00080c0d00310001410306003c414000e0380240034000c20600010031310502c82c0f44015880c05001c0c01c40e5002030125040138116145c4940824004004a00303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 898070332 1250 898069082 898069103
    0xb120712030c0803070809070e0c04090b0301020705010c0e040f060326130f1403010203151c1b14030708030a0f111507020c010e0d060c17040501090c0e01060f0804 72
    0x10740b10383c01184a40b01940d40c1c000c0da07061800c3c849107800f5290700030344100c5050308100105400a80e0907078003150081c1c400407444c0421030340880d00a200b881000342040d428402d8243c2c0c1c2030307049141002400f1040e501000041c01409540c0101d60b03140c0402030174824564804481c11240042034200c421020200520b041250481042e20000641c070003541c16040800800c5841908019002040c500b54020762551400642c4407485a003010001031081c140c3e5441c41d0521000311104410959200b104100065000c41d0241c0c0c20300720714030a00d4078008071240344c02c005080101d5408100d419103130080d0304085013510203441c1390320b86102d10000c1141c0200d660101e00340c20082c05c06040040362030040d0341e0529110003030820307541c680440d040c0900c10806004544803034000001c0f950704500001030402a500c0225002c1c2d80d03040d42801580c450500380801e00c081035005080c03403445051041c900c0f0b40c0e0b891068031420b109100e0900410700c010010f1907414051000a640940306104141 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 898071582 1250 898070332 898070357
    0xf0109050a0e04060f0c0e040903050f130302030105070302040302101b211d0a0b03060307050d050d090801090c03021e0402192a030f030209150d0b12071203 69
    0x1c1600348036510a880000100c01840144031907880f842c6100103441c9018000110089405810307c410301f05070a004030741c1c0f1200c4006040c400c400340d0b60144d8401c861180e6a804000920b91a44000d01050384a5441d0501207421a4003c0c4212004c40e640680f01d0103110078403407400e440007151a405203101a01c1c5084290014804c002d441c1c0c2e00b00a8203100010040c4150b2009014511500c04100104014030101080340d9986003c03104540c204440b055072640c03000b011a0401040d070f4082504100084243c03800c03c6070116010f103044c80c00e03a0352101441e40d25580f59090711200035002d4032411004e00c00740090304103112400840c04510042519105052010404070780c01401e0901003460032240310504181d00610070000701c04042c0f40d00d500c0700c105400c01d90310301d03082003070050501005400040b0f0040c000d4042e1070001c20000d120741c60310541303540d480049038072690034020541e2903c220006680703000790030800403030b107400004c01007207080144c88101c10f108a8015014000ca004610 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 898072832 1250 898071582 898071589
    0x20310030203150f0106230a080a420b040303051b030405011707030b21240a181506091d151302030304080f1911010f1403040b040b1806060f010905 65
    0x2000308c13280982c0c4c1e00e00d030b918211441108480d05400d42203a0064403424000094100e06a945800d078684c100d43c00340d0081c413901450303440010307a2021420080c00f080002c241030304000640100c5461410340d01a908101c00416140d104a0184074080345001a4410b44440c00510b440d6029403030b402e000458401c5500022401e25aa00d110b10300102042c9900c11034490a0005489106000e030341c4074100414180101c10160000b880200c0032640c5112940541c01e640911441258111103038401c1801c548088002130040d5025041c0c500c0c2c200201104414504002548200d40c0d0b003001d442805010380c002d0240394005410f81082071b00c00001039000d60790a2000300000c0c80c2c01001440c8041a40e003990303040071072400c3e09440004d0196a8000072038145008005442c40900c0c0c41c1d001d1001d0500251107440c00030b602c201403c080801003004109405450724091030003140c40565079641e003078014640300300e0341da2031144542000e000702d07426003081141c52400c6c40d03050501c00708164580000c03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 898074082 1250 898072832 898072837
    0x15010906181202040632010e03190201140a0c030318030e150d1406030d030504150c18030b0601020f0c030304050f1c0b150619120e01020310030203150f010623 70
    0x1040040100c2e99410301d500d10006e84098030714602030800c14103c1e428640025140d6000541c2a1000100d40c7c19000c11603101d902c0f00945408002c0516440b85103210000300700103051801180428648183e01c0c0824440300351134400154503540e4640010445d00c107000b181100e07000c55440703c1406029028012040c0d014090088421042d080020f1800c141003500d0608280c0007001454031380b40920004c614000b258010040141c80c022802c141c400c803003203c1010080348043c0101002d01400310070000080403140c0140b10980c201d601005007510700c207441e11240d0182e10351560040004000500380403881070038110b00140111011202d032941078805414009049800a0841e420040012040c049580920b942a5607007420700d0942440d84446a02c40401c000c117000200a0096040e0792542118460542c1c031350003507440342072000c010542c898450004034443c1c00341e10007400c00d28000a81d4184140d1800401c1c400700c1e440c02c1025215801c14503c00e540300501c0c83e18400c00051b04400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 898075332 1250 898074082 898074119
    0x3020d0f1118040b210a210224160905040e010603020114040f030201050306040b100f021014070804050a0c03050a0209060f0f010521150109061812020406 68
    0x1c8141d59082d040000110721060050654400c914007108a00745403510007003100341a1040c03500d5020a03a04512403842d0000801c1300406080c0b68130408802c091000d40407088041c46902204c0f9903460604040808201d409402c00c4000d5403c4006050b200404810603034a0f540d9003001814680c4071750214040d100f40c40c03000321070360f03444507800c00465a204050b019010907020600d82010706000703409048020318070020b41080740100104085a4640c1d0240360040d60060400540f008400702c080d2000040d51030700310240c06078030400c00322400c3c6405217000100c40110350134500e035540c0c03a0690328050068400e071078520a502040c00040c0901910002840c003807002403900b100d480c0b04020209a00400341406001600d009400984a501c2c26540c81c02c0c007400d0060310b5050b00c0e0f40e8085440a14081c00b4038010030300041c0259041c0c6828134505414007a078621203c15180c841c00d0382c011002030940a075040c504842000340381c0600d031840d01c0d43e81c4018000300d0400d9a41401c1003041281c541c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 898076582 1250 898075332 898075361
    0x201030b042a090f0f090c0e06130807060507020a0302190b07080421080304030c17040b0702120102040e0c071722080c10030203040c0503060412091208030703020d0f 73
    0x541c118222a00f20390340d8402424000300035070300745081a80719810f000c0c1601c038401c210750f11403880c0d400c614050318218036510406001d150703c502ca07480c0034008545076403240078207a0092003000300305c0340e11074003c861400380c014000306640361a43d828002101d410384c002d24580d42441d81e0210b0388500a400500c0400d02801c0310688583c1004240450818004100000100d0f0000f0050000782c1010a0301e92140e01414981d41c000705504002000c0207207004140d0b07500c500010082085080d040140101034002d032501c5011941d454915402c0f0b1160380640000140d40c000054010700800000300302140c85a04542e003d01492450411141c2100d42c07101e0307140380d601d00c1e01d8403040822119a8010101d400003400c2d1104000c0101c5c00205204419400b01900080000c040c000c0c03c07407042c0010107024045540038542414500441140002e25200241101c0400111410000c513482c041c1c90701312030501e1941d200c6203402e400070350001c0361750186140c983da0310842c0402642f00320716449001c50b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 898077832 1250 898076582 898076651
    0x1413081809160807260612120408010b0a1406030a15060c15050408041401110a0620030708070503070e0301051801110c033c070c1202010c0201030b04 66
    0x80c2c00240030044028409400c01005078520322a03072820b241426a08542c8880c640c956448080209680d44544151500140315070a440303e501c981820003030003160301031341c0208810100d200400c038020352548124005d01c2018800700004c0c2c90802c0003141c2000d40c4000010fa80c20703080360300480607901903100d40040ba04012160b03040c003421100581504c440750404101c00c2ca05a9900c0026006034000d50111500c003c4c1c845071603034000c1108010741410740b42186c0034a140d924080020704101c0001c00750f16510b09046e042c00e042030b4401e0380c0c010010303070b2210102d656881a04a43c260001085841000400314851140b500c080c0328141c003c1c2030000030030103c0940d00441d036081d21410b17502c501c500d03002045111500d000c003000b512842000800b20149030944010f000074403010303942201006031011240100401c540d05c0040070315921900282601c50b48e58041099405500751011b404185011b419500642c803035489a840640c000708002010480c80002007050765070150040c03e641c884 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 898079082 1250 898077832 898077871
    0x7051209030d0e062412070e100f0303120b0f04021b0c030309090f0618090706030c0305040b040212120c01021b0f0d050a2c01031413081809 62
    0x10702403c12410b02110041c005414011602d8107081c040e1031000700030f140c0c180d10058050341d50a4603130030040b28040450380c3c0d494841e41c5c1700ca28018144c845030380b4035040d80d000040d4000138118410440e078064403103114482c0c4a0021030040c00720f41c080341d0380c003100c200a603590541d00c41c8046c00000311404103281d26420308074425890321900b8100244240d2042c00304e801c840d035400d5580c907408801600c1032517003a159040415203000340c582e0201d08103801402009584a00017511500710b07813140e501444517031440c28044d0100d80f0245ca003d030449103c82c0c0041c0140c03d20402030f0721211180700481e105030172007088540e542c1d0003400ca17500782a50001620f1180064079818151440c00385005440d01d101241c018030359900d1241c40610900038046a01c0b8550b84c003800388040a0b01c601d181000040d1450800219004801c2c041c0364003003850500e1042c001801c1c5140c091040c0090f147d903200501040d180c00465801c940d42103140451448011000e6440710080203003d0013200d510315000ea8507 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 898080332 1250 898079082 898079107
    0x6151107050402090d030e0d05060f04050d0c03090902090a0b03070207050415050913050f0d05030601110c010e06071b0308032a0706181b1701060b0f030705120903 72
    0x3030541c81203104034018803105000e6555031000380e2582d9814180620785500c92004146e45085518026100713001c0d40c401c1020000c140855107205a1062003500c401c903170440e60a80302d0082c4114040e000984a01050200d030a65078001c102c40c030001403806030480d54848560030170703910803590308005800018042080d800d26000d90001d40c0c8030a544c03014101c0c1404040351082200070400c1c02d19580044440c01800024440848200784907001e40700a4130304140040c0840d031041c0c84050000c0c6182c1482d011141c004181f94000c050b050f5242c480460301c1004011080c2c001d0380d002d80b03031b1821002e02000c20302c008104030002180718803a0b180c0c603407609181e0001c00c1c1c1c1002015a10b410101012000d1880c8414101e5034403661180002459071300d2290090501000078000800403001c2d00d0071380d40790382c90000150088600d8a41071209203500e88441e40d00313881440c0700b813100058061096816503001c0c280510346c082e0302480c016007081ca1101c0401c81c014030981e0134085581001580718103408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 898081582 1250 898080332 898080343
    0x30a14010b1302091e01120516080604020a0f050a050d1e0b030303010317030a0e03030702011e1a0d17130608010605040e1f1e080d1106010308030a061511 68
    0x20b0b030589045040001100106000840307142ea034068502c4600300d80d0f82d041e80200b400382003180d07800b0820005031515028210b40340c6a00000d800118070590001182d41c60329008441522400c2e603141d1061601c0d0a02c159029005800024180a414009103290a2070b07440384407800240c00402d0b800c0d68401b60110011180c0000c0e07098000e410130001440030411491001d00365050440d0080d9895850300c1d03c0ca0300502016049408900002042c000801c0c1c0c1504226117804140e50744221080da883d880204845d010302d070240d00d0740114008840d16240480c940c02180b8060b4181d075204c1004030304034014581c01040b4806060411810500485600c844043d014200c941082441e20341040103008401c0001000c000c01034040c010f1540d000e08086900030003d04148544540d05000105400411050b500880174540325014001d031455105580c45c0c1212400e0300e010342940e03400c40d00c40782002e50000340200786081d20f8120011f0240024a000320400c905c0e40e40e08509190b031041a6030500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 898082832 1250 898081582 898081609
    0x180c090316141906050309120f3a090609051903091a070f0c0803040b0432010c0348051917040902090909030a0903030e030a14010b 58
    0xc0f0300c0c03e00c82d600c08002441052042d03071110b0400640300e503104420a49003084198510140c1d403030205402c0356004060007d80004001e4142c25044910814a072004d03802c80886070b103510348030411850762401415840008064010301c80070825001940f00d4910f8082c1c3c0f200340651541d0a100c60400745a03010660700043c12955100d06803000c0038500f0800d550240540103001410700c015008104424050400001c2c11050709481d00c8a55620300310320b03142c02a02c030783c0201c8600d50120000501032460b080d0034500c00315001202520000c001140e250300301130307011400c2c40344000c0340640b00b1a03c003c858400341d080600c0c500360141030100310702c189207081c210040f80c04800b41c02f88000900100e0400280d1441e00444002206030341080c0c407070803071607000411140034002401b0501b480303a5001042c848100b44c41451098403001541030b40e9200342007000380000c1602205100084c40f031300801074808401030846183c1001521206401424030f002201c9a80d075820034404d0505100704548080e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 898084082 1250 898082832 898082839
    0x6090305150402091b07061103070e19030311030d090f0309050d0b0408030a020904090f0506010e04110415030204141602070e0c030a06031e06050a020702180c09031614 74
    0x40b41055400b0070b03800400649503442640d108111130182651072001c1c0d505640d0424414015030000c1e8160414a0340241c54600c005440a103000d42142080090001c2440f0a04001c021b039526580b0304480111a40c2500382d010b020405c00002609901d000d0b0304043c038007588444542140d249009011144503500090013001444080404102c40351103069010340c0000c006aa65900e0f490040024404c501003039502602d0542400140300e068a401c07041680701e001103c09607629410a810701a10464005142c40d02c100d032601c001e03080035040030f09800e20700100000b1481e240d60001c0c09681e29103d0039900f5205020400801419900303142000480a0019007800e03401d26010101184004007075641822000021420801c0907501030710085410032041781e100b00102e04050f079000e0084105030780c5a8241804502a500e440c0700b2500600d81c003d0249920050b000c48000f0030180c0200183d145410074040712040c2d031028403d58481040020b60854418204507085c0e00049011a20a01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 898085332 1250 898084082 898084123
    0x106051807021f0b2205070809030a030f020f0304110f010f320c06010e010f0f05040c0314090304030b01082811030703110906030115050402090a03020a06090305 71
    0x48003a008210b107440c0c45403400d05070308410003210941000d07042d21140113030404642ca9110310321711024034410018034030350703241446981c0744d0300000c075640305007501e000140e40c20410680550f64040d912403400d4541d412005410304071003107038400013508110350654080d807400300340d81124901110b40301480802401c01c9040c2c180109401003225000040000c0d520a18516100031109414181e0b80421420000603507290154801e1903180d20082c418403140841610000c590885c0c600c900d6001d45204040c1091090b10f0442000054202a0741c42c03400d259982c24280340c00c60345001030902c600034401c0210380e500c0c55490710300322009050348004180c0e0171102c0300500310055620800c52546050102003c100e400d030404541f010303c0d864400d949441005000030402841a4031200505012071311603002d40e484000340340c00d1701d030180e0110070141c04911080c800e6281680c042c01c04680b0140254402540340c0e800318036000e105400200126440020400402204014814651404003103120 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 898086582 1250 898085332 898085341
    0xf07060f0509060a0f020c010207050a030906030501030224090a080d090b0403020d08030c120f160804031215091d072c190903092d0e0604061701060518 67
    0x20344546001d01580c4c01280c50301541900d003e000e4060341d035040790000c000c540d039210300d1a0140c1e40d441c01c0d80c02140401c3e08600e00080c2580248120b0f0304980c1c01805141140f0940a5240031321480d118141c20100c0d0140056402ea840f1031101101510800d002000040e0700b814002e80004801e03440840d101c1c2042100b40016241c4582440305075a03c01c403200c0d1280c031160b006404500444100f01e11124090040007070b080d162204082c068403d4044881e40d01d0307500e2004a43e104021500038021030101e5201824042241d0310441c81640303123003d130743e15654507040d4220035980c003100350350402500060024095542400b2000c0140001009405182c100d0b0f801890104810751400014924000000344803007407503c41c100100701d401c0b1007005844082d00c0c0150040225000741241d0b0f440d0301d6003e910f1a041e103500000c0c8011551100a80d241ca80b030300381d07205400e00401464000341c03190400604105d040703101000b0024280c0010904500b800c1c00d1241c24007812960b880b03c825200d0621 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 898087832 1250 898086582 898086601
    0x50c0a0f14030a020a02360105101403070c1e0501020409110703140306040221071e0e09180607050c010c0f120c09080d230307090e1009020f07060f05 66
    0x81724681c1d041c0c0300e0751081a0302130781d050101c6001544001c1c164020a0803101043c100e00e00450694104448032001314081100898525400d1f802c4035a0b0030b0020008101014003420b44080603034460345041c001d101065016011b480c1440000b25903170384d004203040c4008400f0f401210360311502c601c0c005040103240e0302c0007003003208065030814588100101007040c9403210b80403541c55a0b11201241d4809854004403411032004407080c2000030b9106501820041d0303501070629000c0c00c1991454190002c040c02c100c60b032507000c0d203556499240c00710f407580c214800703004040c4151600e845a0340c9070301240c8400c03420741303103205900020030042d20340010441d0b40200d00c56032100b006020010f00d40841c414140c42916241e01700550074840ca03082d44121941c02400c0b01c00d0002001d5828240862049401c0d030705000684650001c141c050034203018146070b0780711aa603c410403900c0c00708450b0790394584604a80c054080111641e200040c51018040240240d800c120801c1c04100a185020107d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 898089082 1250 898087832 898087843
    0x10030e0c1c051b030d0807020312040f060f14150a05030a03020c0102120903030706020c2d07050a1404050712020703030506100c0c0b360906100801060e01050c0a0f14030a02 76
    0xc034400d1100704400707d03e0091003002520400c242511001c1024140790421000580c800c0340100e0300d280c2403c0c42500105800d010344291903451a15214458503070990100d8005034000c1c04c26041040c01c0d030000380c2660b081001d508094081d4014019511420000a0800210070880d60101d40104140800c40d00e002080790f06494000300010780322030741e080c65207040c00d03111403548034100d4141d03c1850050506550f03500e000440c100c1201c01d1036581d5820712a080d811442224601ca24040040b4901d0500342c01c040d900040e2858000101560101141c040380c018140990001c0ea640f020403009007002984040e40f11014100034500f07000c0c2c0c1d500d022400805001d808a00c65010445000801448101110382c1c0f00005c2c03072107414134941c801b9510078404020124460030200300403a9490910150444a5880d2507450740720713582c2401400c0d40c003001c41e907110904001041203440e014440504c0700c08101881090103001075021402c0450152040d901c008140c0c1d00100141c0e0a4035800190 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 898090332 1250 898089082 898089103
    0xd080d051012020105031e1e0709030f060506010504030b01090504050c010e030c040c05040f0b0d06060c0f0b060607020a08030702090603030310060e120f1c02030301030210030e0c1c051b03 83
    0x20082d6481d83d03884008103043d42240c007948038821f9820140035180d1422000520380d4002000399038482d03640c241044400001c81e22024042c80310900031480401c140d604200d510603418140145002c3e40c035582d0802c8650700364845402c20340d07a5010310082007802d100b10300c5015030910b49070441c1241c020009448100c032010191180769101e100c41800f6020f281a5801442c125864060301d41e5150f81001d0160f0102c080c1c000380310301d84070003c14041d00500c00d0003580f9410000ca030081c081d84d5030741d9212050000e094668130200c28801030006039240074607100544800406143c80b000a44140b0a6a9101804482c429041402041180010380003820308907495407500c1e10120000c00007080703034000e640c075900040d4090b00b10028070b14240000c45030102c0000f00c004800710460700d6000c07030b103900007804000c1d80009c4400350001c00e94840c6e04494244d01c0410182c40d5100c044e400011044440c400a10709400c540b004001d083c00018446d0f0756245110108151118400c400003d072600d18599 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 898091582 1250 898090332 898090337
    0x30060105091c060f020a0206090a0c062001060f14040605030607030207081c0902121c030b03010e0f16081c0513080d050403020a06031a010318020d080d0510120201 72
    0x103602c03160584a600000440a802c084200015001308400310061341c0302042d5000540b250502217283c0c4d1038001044002150400314032002103080400440b5030102100e6440c201c05000103564074100f00031b20544004002d41c05654500c185402e00340f0904412280380c0500c1540341440420450310007207002c0382c0c00085850010780d540d40a1030301c00418081c1403003000312601030904070f104402070740d80810541c600031289803200d0300c11341680a61314031071a89801d4130170303401003440d4441d1800385d00020704403803005001240e120300349840c183c980010180422199404020445009041c42420310050900803011703204002d000701c102d210303c0b0214184101005030010380310700390801e0200c2038009822810151050281c040c88000c00c1070704030380026807050912001c0042c07484e0003071281000007440c0b0041d60171112061b0005400a19180d41c90b0a5a46800b41002c4016554a544101742c1d6104800080c3c035030340380c130301000c1c1220002020251410500300c0305200303584c8442c0313038010201c1d0b092 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 898092832 1250 898091582 898091599
    0x1323070315290d0803040506060102070b0f09101b0312050603010e03070b0c13090b01081302010804020f0102010609060b040f0602070609090b03101e2403020409173006010509 77
    0x10000f092907402280000340080801109110803c0710225840740502070907404c0701d500340d48650b034804c007511607000458510803040080c03034141e007000004c0c4034140b241800e10481920181540d840452500d4404034000354484440c117400e816244550341d040301d8103800800c901818490120b0381ea100d202d00107040c0c1b84c060b1000540903901c00e812600b0800042c00d6402e02d007a900c599a401500a40c00c006001c5425000050110b4660400c2d54078580c1c1c059640c0c0c02152a81e8003402100805441100c0c119502d581020a039174803180240c074001c00d0b00c011f080c1c0d50749140001c180071052840d0041c0085410205003045125481240c89059440d0403400148400301700300000d00c2d104601c0c03882c510450800302d4129802108540f5016048440101446410703000795100400c1c0e0101030341411a180c4000c018805800e10350300c4513840c0ca206500254003050300d01c012503050f8110324094200c008000b1030400c0321201109209102c2400d0000c80308507410b0010010704a40640b10450b070041c20380 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 898094082 1250 898092832 898092911
    0xf041208090709111e04150815060a0c02091303020c030109030e0919092003010b01051c0212040b010501110106050105030712020d111902151323070315 67
    0x1890031030711410204a000c40b00307500500a04111130f00030784204c0c4010107e500862040a008880b29840f506c2541d01030381f000481001001140c0d04465046400c0006c900e051800586410136414092440c00d001280c19500d01d00d002071404809121042c0243d06118080000076048051440d500c0c0c0100d4110459954900035480c0b01038420940e11007140c00c00602c0c805018441d4101000300100154503180075010500303040c26100c842d440381d400514100700140240001e020511100310050002500e420380e0305803810600300e41901c0c01d031880009400104495a0040d890600c1100f040c17000344021441e1500103030035408010441000d00010100700398a856455044420311030025008000c1c5000e020540c0d505a0090b8440308075840c3d00204900c1100d000249a07810701040c03100e400019600e494841d06ea12101204c21900d00c03052130080340044e401003402c1d841e0703030341c4040003448183d1440c24950202c080309001c8486035071600c51880301400310190444106000030f4010f5014000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 898095332 1250 898094082 898094111
    0x903020a05070b3006060a052701030b03190f080403061a1c0c0b07051c050c1c0c03030e031902011b021504120509090f041208090709 59
    0xe08030030080c540d028000003c500184204090f080501950300d011a03039542c03441180c00d2082030500004801c0205100080e8245008001007145e8040e91a24070300309201803010010b484034140c0c11610200b0078000713070380e240c1d40e16118403103c01074110020700088002403860b040300c0d010400007070105003149100c40c0a12841c141140e0003550720010801c00c2400860100c040400007800541c400e40c02d10784491f15112403500f00300710458010030340400103494a5001c010960112000315002d000703142540c6500000041c03440402c000c952035882e5911a1002c10506040d1055540e40081c0304c98064103921580c8522031140c1543d05080c0002c0003410700221914600550a0b120b0032204900a41d110b01c0d9410f4122911048450100f9000d064900000382d0320382c0030607012510404140c20006010a01c0450050550300c42c0303041540c0346c0342925004c00c0c0070090407540d003403400c1e070040700344010443c0f041c8500000d0421407400342203600f001d00c82651900c11511400d4140750b204c1b4401d451441707 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 898096582 1250 898095332 898095343
    0xb040b06060f0a1214010e070f030524030a1205181c0b0a061512050a02030603030a14040302100e030f0606091f05030304090903020601060201091101081e01030c0f08150406090302 79
    0xe104007014546e42c1d440c000000407401c01c40c1c1074000942034a81e0809220b0282c080c66000b010440d8602c2e0070b040c10b420950041c15030410b100307039141c0b18003000070012844643c40c0803900001e03a0748082d541c45c803255445010840c11201c65000d00d8030341400001042030503014500041e4050154046a00c0d600500310141050390003c0445500c044001c1c50310a40101003800e400c41904400d01c581d070340b100c402e001280070869049800d03270001c100c0070418500c2641c103014201c01e00c1058505181e101d4020400c2061b082000501150b03680415022514040098a00c91800031009244600d000700104503510701c003500261a10304036584030300f0039160580c612400b41c103010f0203c0c2e445940d25080304014001e40072043d000750250701c0010811510601902c80e0046c1c000340d0000c10154000011542d0ba00001c0176402d502d030242c2351083e80760b1304a1b860503000398080e500c014400f03401c1440442503c0426400b60000350311242c1101307400040d042c2c03d00d40c0180c1100b00052148141d00b002d90804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 898097832 1250 898096582 898096601
    0xf100e28050906150103050906060105090a08150612061608130b0901050708090d350703060603230a090f170a02070b030c2706070b040b06060f0a12 65
    0x3a051030100704000c100000c82910801220100684100b0040f0054080f1842510036071241c0e001030380000c1d523075401000104407074400503004200480d0346400442c01c2003080c003c0a4844540d1f04203200d102d141000e01e01d040303801c0369409404103041c6100c030381911001c0340134218140b101038800161003c2e810010700e80c120740c020702c0d0321030349190140707480340201780413640c103400300340c0f00f0b400308040150010307803100004201e44071003048070790003101d85611401c40307400c4c1c4440c140d0800318400421800214240070f0021501c02184c01070a20201400391a5408400c000107a0700045101180b0308081009402904200d4001040702c00c5080105120f42c503a200508580c820028146014800d030f00140303070050301a070030b8a500720384401102d045880156410166000180040312903030400781c854000d289802030192030b00020200200c1c0c0d0980140c2c6060303404000c50402c01c81440007005c9511f5110004881c15840c11024071440241070285005070402c0042c40ca080004143c0c007903015080c00d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 898099082 1250 898097832 898097911
    0x9040606180b0a080106050313060903020f0f030f1e041a0409050601030c0e010e0102330a11070f060204050a03060e011a03030405040e0a08030c030f100e 68
    0x40e140c000c09880008030031869080907994a00c00100c104124042c1c03503070780d92155204082d9900e0000100d03400c1d00098400005107983e02805000500c503807140c80215407203074000d82841a80703030150908280702da610940c01c58100700654941e9000040803a103003401402010f14098403401d01260b5203008a07003088011001c071012084031100c003100170340101c81a40009008603035031180110700380c84668100402195017a000c40750198009c5d10f864012403c10b20441d582c0d081544490b4102d41d0301107420034072445c4a070700030300e07603612450344803584c8806010307010f000010036014580c2e2903201e0300001801080d000b51403030041003034540490300100b02c001c2216504584a041071802408000100145903103010044c21840890050703443c0340c0e1000a02940c01e15140070140302c00f520300603158a1013401034074a450001001c00e0080c1d4090900100b4041c0c03a41341228403058000e00c0500101c0a400c1910400c0004a40014160354840709003401401240c5400c1300b070402500040820008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 898100332 1250 898099082 898099091
    0x3010311040c03141f1d2e0302010e060d0c12060501080603070e07020f0a0302010c0305010801090c1404020409090503040512030c0a08091f0e01080703020708090d08070206030424020f120c0904 85
    0x8000b451a00c901a5144489102020000020700b1121005550301f2200c02c100e03c843c00c001540c040c552545040c80003404862030890580918001c0ba00c034614050f0200390340340150100d004040c8214400350600b0b0070320301074500b0400c2c0003031307510242c07407044814807113000380050401882804105070a940c180c0407607409102d00d29002c3d01078a40340800000103481c003800021032036014000d8800f80754101c1c003809004c900303000d5010000c100350310425401a40030000012156058807600400780d00a0010f5915603042000300701d1004500c0c240c810440c0d2090228081e165004511a618164090b03449a51443c0440101d4200340011141c481070b81444111400b50790342044040d4201d6400340ea07444180e0351401400d41c00c83c010880064004981070050643d2070070311102c1c05401a0082248a041210b15030020b01c481d031045608580d0112184a003400c481d40c00307490200b040c1d400c0c40f8154104131074020041711a01030015001030045084001c55402c101400484148460241c402c1c031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 898101582 1250 898100332 898100369
    0xc081902122e050f040b0109050a1d15150703030b0a060302120702030f1803121b010e030a0804060b0a05040213060e0d050706051c0203010311040c03141f 68
    0x51401140003030005001550b03405400d0000c0c1d03a000301d1064a030001c1101143c50142020711004100710b038020b6051024204003c10b940c0c2e41c224401c00148840b01c40b20345450a0705146074035100c8060006c090318440d0110140385036694410007640880001d80792902e9000d10b0408070301800c00e0418407038111010a00102d035240c0d0640050440d201180105081515003840c06ca1383c4c1e105064000c0c01d810028880d0134035201030341242280d28030700103007100d46034072001d551101c050340440d4049001b4580315030002c2068034280214410b00d01042c024600b44560004050b0103144000c00047c0401d5a461042d4480d644500c58200a0480600115203a070410030010044d480755008540106e54201e45030351403440c19205068045030b0190160454a15000040e02c1c990808a08003261301d0b150894540d980d41c0038800395000794024001c11141440100c180801c8522950815080508040388110028040398845810621000790054810502c0c192000c0803502500032651a01c40682c041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 898102832 1250 898101582 898101601
    0x9070c050a060c0c0b06090403020c060c0715090503070b03130f0f12090617011a310f05010809060106140c060108070510020601060e041505060c060f0a0c08190212 72
    0x30485130b4842c2030040d6058030b610f07040052180741120002c005034880c220a032011b05020010b411038041040840f4a45512100740082e0825209038100020340c504904100c036103401c2003a44000c080c042681803440c204010501d0030a0b0354105c001e0081c07407000c001c4404000000e407610400300c1d000302c10081c24400064004006412501c280070000303c4c901407046002c0705c1c0c011070038100e038050003036080394000709649600b50340c0042c4500c0c1a0655502040601003514428090b0704005044840da000f904003041c0c0744c18001c00b07400513030412180c0420015018030000b0721a040d29186d06000d902e800d40303c81244501d103c2c0c440b5900d82d0b4007074030700005002d81d000507110013500c900f01c810580144a6a2040365a80000d02c180c900080240c1480140b60500340e020050b0300c90f03102803586400d80c490000c540c45134031001040d500c1d41d00100801410785401140180c000c0040d40017840003042850b801480504054440510031040700c0c00c9074945295036044590340010041654000d140010b40c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 898104082 1250 898102832 898102847
    0x60708070812061003060608040605071b12080c0a0507170f0f070501050c090303040603051005040e03190e030c0f0d0209010315050709150c05070e0a0905120909070c050a060c 77
    0x39020303050303445100e813126010340620019201c03150743d540440d5a981c1c0322440a440050300e08814000104c081c1b00d40106c500c8001d000b024020b5071801e1140c203107142e0042c40444000c06020381c0c01000c1c80040109076011003103030720b0300350002c0c0c000300c02140c00451012107200b10807004a08050000f108490316003514050004640101c008001d40d507100400d29540d8860070030703542c0d850b0b0410001031107120300a9025039008600c00c181e1041142c4c554000c80d044403800000180c19500200d0300380e48158665104080c0741e402841c1035880700c2c4030f000101c0c0d5103034554035103a0f2103541018560080c54031044001008250014821401c40d40d490410a0040c41d1280c403450407079080100203503081c1d0090090760126450068031000d080580c074811210f0011804044900c0e014842001aa9820b520341550290195540c0028022503919000345001e410244049007400203100c5405182c0d101c0742d030740d0b038841d111742015918440c4924085c1d06004040900920291a00c2c4031100c00c60740c403030301 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 898105332 1250 898104082 898104091
    0xc0106051e030f0a03140d0216031e090f06110102071a010f06030501050307050d0525050112060815040f05030c030921070312030e07140315070806060708070812 71
    0x940d0f0840c189050304075120710b48408040e0215030306400d03c001101d2000020a140c1c2d90541d001170a0000740740078501800e0b18210280c0000f035040f45001e6088010702c440d03200c2c108032410403410745031a00000d030241001c0d0703108183c14420b40e4002800226429011500010743c049013072883c4801d5040c101b0f44541d400e0040c02c080f0360508801040c0c041c068071485040e50002002003032135500c1c00081090007040e001040f5007900603140311164100354151031801c40010301107030004290510b4001004804007080348200701d030400078100118500880c110201c185550104039035581d403821b1202558a0144000b400b6220020b2145240300d400b101070710041c541150541c1000c00c0c1da111084107008940080702c1c040d00320a4007000004c0c230030000500130315a2410045101e030214410075043c0f0341180e00889549000042e5400c0b1880c051000b0509a5111a48049036050860004000000040074640210000103a09003800000340a981c1c3c0264000c4a90369128902c444802c0d0000c030940b03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 898106582 1250 898105332 898105339
    0xf10060e010509070e271021020604290c030d060b0c0d03050411150301031506121104091e02010212251a040308091615050c0106051e 59
    0xc0041100d10b8101d04243c000d000954540740940d04000400c0b103c0213091903440031200000180054181204a901d8890b110b00010391044904d442c0300d01e2890415040c607100848030034107038240103a40300d005840a4803100e130700c1b8440f01074100201c03100c1100b02c030744001e0f407aa0300468415104c40e0004018001c8000400041c48440d0ba5440404c60714010261241d072260130010f811074400e44641d1009901a004003c860304411000f0046607050740c2100414820500020050051000b624617000f581160003900300442c40c60300e5900c101c041456a002800c10704400307000c10590381c40345c104240294002c85d041101ca6040c00d058181c0e19004030f8124054000c1c40151900c091805003a55030154070340e0b00800010fa83e908035100108000e080803a0003503100d0000e0035207070140000d42489a4881e807101031150a01c200114548034001c103004448071403284082c49241c421860100d100091402c21075191440401018003600e500e4000c16045603030502c4000d006485d860786540c4081055 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 898107832 1250 898106582 898106609
    0x22b0b040c0b0c16142116080705031504120c030311030a0501260d0c020604081921051b031611040f0501050d140a06020f041a120c09030f1006 63
    0x6042c0d0084a41e03856004950200d140342c2c16030318034080e001c0703000f00b960f801c0400d0340c1f800c4181c1043c0010059241e00180960b600c02c050900c80d40c1810040b400c211150b803444070400785015030720291844100b280e40010048401d840d5000c1600036000301c1e12180d03c0300c110310346a10b00030400d88000c003170903c118945690800988800d449040c01601481c0c0d03100400350004400c810015203c00b10b000c0c100b00d800160070400050004018041c0b01c1480300c20f41d400c58103041590a145d16441100000c0d130a031002c010741c18080c582d810000311104070001c02290500780000c0e00f807150840c0645180380309e8103e8101409001c0001c200070351000c0480403a402c02c80d00c1c40c600309a8049030000d00800d40c0010035800b4a1340031925440d4045801c0d5005001c542406005075254000c1c0c0c1c0058148140f003000109c3c00b80441d001030240c81c0041894001c00034104a0100ca041500c240060524640b51100041d11440b944040c00100c04000941080b500d01c480c00f034121100502c050b100ba0039180000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 898109082 1250 898107832 898107839
    0xc10140412260907090501030503040f150804020f0a030812071b051207171602040c03020307080a0b04060503030408060a060602010605180a0b090a09022b0b040c0b0c16 74
    0x6011040303428624000d200c410001c00503000700b0754140180c1059402c0c450807000103803654a5000e1103028600c11b0002d142c46601e4607000f864140c0c0c0d5500100c042520702c00404088662004905500c5030b011256a1180d102100c040380346140c15401c0646462000182000086880304a0b6030065200703640f4584e460b41c04051000c0c0c002c00114000300309070080390b24240f4002082d400380403186d0241728030a81c02030803078250301140d0313001c00c100c00c0309030401410070415403800c0d100e44005400c10381820b519628040074001c00740d26000b45081a4036659207031901d025221036106a01900c1c0c0170f0100ca98a585484002e079507110205d416030140707810148042a0b841c03042c0104000c549016041449031480e51104100d01900286003c0865036a140001140e50340e024400d40949150040059041c645005002c00074000b0400100881d12501d0741c0807004801d0343c031400c806074108400b6201c680740c51418105e48203050780504084000401d4046044d100419814403070321129001c411801e94 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 898110332 1250 898109082 898109087
    0xc0c020a06021b010e24090a0314070806042409080a210605181e0103030807110616050a0e0307030602041d0402012a020a0305011b09080307080c10140412 68
    0x21069082c1e60400030341461180101b00407107180c030080da582c1d14614109200700020500550041c2e000f55034288001128229042050000034060b201d45405402c0d070303144c29150312100401d25120940e201c0c41c4000450f405001c160f00446140e6440102a5629528032300010245404a0308140541e2040e00d101c4145448620030141205c401030f05800d050240100400400355004012071101807521a8261002c9440e0711428047d5121b5101d1898605091600030001e4620610042440c0c0c4580140030042c81c54101c40d4245000314a85542c0e01d86c10420110b8440e00e0441c0c0c1c494141c4121800802013044603000b400c15202d00c040f180b50190240c1902045403001910042e0100e000c17203141008031042001d03540904040c07001c0309151140f40d46d0110311503c00d030381d009407420f96680169986800c64144d151006c003c01d85491048181044011a100e204036800100326200005038003030300e140140203008803089408802c1080c070091040340303001242e00310750071111016002c400269172030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 898111582 1250 898110332 898110347
    0x5070f022202301347090606060c160f08300702041409010c11150604020c0c0a09020c120708030604050901110d020d0b0a0e07030c0c020a06021b01 65
    0x801001d4600b00f5484000301c04030418104103051714407200000ea40545043c0c0b480e0150034482900e804036016030841401c0007001c0c5031024016031050f00e01d0050158440c000070310340340c204e5401c60f1aa0342d940b0113a004c09142007900704170401e003405600000200c0001205001085030000030550301c885103080700550146503070780140c410080507804811f14506800001d0f02e40648040c1002405501002c0078203600c01c0203c8640001e0385d1103c002104c810750100c21200327100c9412001380748440c92040c4200e40180b0040005001d59800701d505052400c007007080c02c00c000c402801000e451030300c56031800c0c040e50108a9964480c4503444020a060f000e04049034050b9410894607400e5840e428100405018090f0561a40c0c0d9211340c2c001a141c50010004c0030748c200d009100503582d40c10480c0000c169040340881911405c0d45507030801c8080e4800009270343c03007d228580010011403035641076a4007a00c02d1006508500c82400120f60b403500000c6065004d01e062a0320220001c10340011981c03003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 898112832 1250 898111582 898111657
    0x50306091504020307030b0a050a0b060307020a0215071b030605010b040f17010e0706210b15031816090b0d02011409180c1c0b0105070f022202 63
    0x194000d00c54000c020746418203240d08244000c0c140c600242e42c039119443e019a013034030447c0c5000c0d034030014411140070300d102c1d203ca65001614082d007980380018011351107a4401001034091001c1d0a003001313414581c4400c031640b1651103e132032403030b04050300040400401a404215440c5103040b0000c50440b443d07006aa0803612045041c06055051410403144501000040c000c9903480b0000756203090001e0003420301515869031a080604022008a403000032420003001819142c40306802c100d4030b0b00001c0c04443c0041c100059502c0d10303100da0414a000e903e1411010500a030280b620404160403044000c58610740028885207000004100b01e80b20b04080c000d000c901001020801061100068041c8150041440c585600034840071130755040e0440707050403240310002d0010080007110300200945458410200440024040082d00300d01c03c40030090007440204100004664070207805994144141241c4000c0300321008500000c0d400c06081c45050048100d00080c0c1001a00340b0010f81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 898114082 1250 898112832 898112851
    0x7050306030d110606060706021c021c06080d030504021c030c02010f1b02090c121306060e040c05060904060b07050f0606101d0103110412030e09040b04060f0b1206010807050306 78
    0x3034890000308003981e0b0207c581104c80301d80074003014902d007806403039181c0e91440d500b00240e034032748280000200d42c511514018400c20300d024000d010001c400280c0042031200c41c180000c940d1985c3c00050101e40300e03a5042d661038185106403108156003c0c0140e95424400c4c6c03200031803140240000d031802c541000c03280c0081078050203000c0140c031701080100c2d040140c0f1040545002090b6044041d410000c40b121112096005c80c4c56040003a507101d180b00502840404e050541425034034200c1d145014428241305a1011032101003a030307a15480b0800818a0491040e6a01803a2506545580303e030901c42e2124050000000c207036003030a00c0280c0c80a42d8980e50030381210943e00c039807440c0c512000281d60400d40d0b109040ca0f98080d0000082000e8400745801001055603460000c1915921502c094000d07007490090000007002c4a19440e0000d5000c200824200d02107291702000b41201e90405520400d08501d42c042c0c0c0304045a514141c0d5580030548280c19250021b00d6030b240b6098498070315 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 898115332 1250 898114082 898114093
    0x7061d0d03081f0b0324130c170406090507050402091018050607030512060105090d060216020a0f032105031303050708030a050f180607030c031407050306030d11 71
    0x9204503403031580b0181c0030500c0f40c1d5281983e11410359207092a0840c01004000105110310006415102c10328128a00828501400184c0c00314400038080c880b0000e8548e26481c00d8940140108491b50045c03030090380d01500740c542410b14074064000d85000303403414041c410012441d03050500032503c91907005004124145ea030a00c1c122071140c2c010300f900921181000003c16907070380349401015402c0c02a038400740c651040d40200300d900034010b0041c5040c8041040903c0341c586441810000c2c00341c000d80010b1b143c140d1a814104e0600201710000d611400c0b0007008500d00300400c83c444280c2e40140c15009442c0c42800040320f0504011540d10b000c200140300080031980d07805d007510501e40c8a8503145042024654031030b255030700141c5641180329103400811003400c000e005075541c00035640081402c041d0914403030680f6807401034542420152111068810a40642c0055100890300700a00702c591401020007081ca810a1f11110312170300900300ca21440c14030901c15030380a0301c50603001d4075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 898116582 1250 898115332 898115359
    0x90f011103071b0309181121070207031110121b0e010914150409090602030601110c090114030f151e0108032a01020309070302030606010309051c09030c0807061d 71
    0x1c1b00784495441c00251540c0310f0020280c405809010318408141e810181f01580307011002c08140c4c005c10203021984510401c001262202c004490503100c1962882411180c22008442c801c0c0010004480300d070030301c0c1d80f10896244500d9100c000c0080c41d502e003488084020011200740c401449049070008400b4a01641c91030030000795106c1c8400444014509135481081c5001d40e20744240560314954044200911545c0260591850802c9000540004580340002504421041c0185201c4003c254107424075030f00d04225420640000d0411941403100580c2c40311281181102c0d40a801c035500c0320440340002507840014141d40c02e0101460420a5984908d501108074400681020840c030321900748252083c80214000c00e00907025040c66415401890f240c071002800a60403d417810800070003003080410b04842c0700d0340702c10400a848101c004e0459441042d0f4101510380403007100001000100040e030501202c0a40d2140001c161030300112800c4040d92885098001c9180305000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 898117832 1250 898116582 898116599
    0x31112030a0f06031704090b01030905031207020f030d1e020c07030303022203060e060f0c0403140c0a15021b0f2101060602010c1e17090f011103071b0309 68
    0x10b1826003001d400001c149a03a610744140481d603980c0300110203100010b0502c110b8040780946258030100303090034040340300d20380ea8045c0c0e01c0c8128182d585205075424041105140b0034420001802402800c49480700d070300720540700003440c40300303a03006100f004542c40d02c141900c18002d6911804611015101851554500f9030195001602403034050b08003401c841c110035042d0000740301441c044c810011b1441ca030a150f9074500a80607000c01c250301c0c0a0f0082000c0c0102030710449040e642c1c4445408130805842585078a8241c5585000d0303440988140c01081403559168440300001e11135089421161a0018a2010701e2000b01015040502d12404120310b0a0041400c420040450a603081c0f500c0461142c03400c4443d42c0d004000180d4444ca81e041c0000d40c0309400d0201e007800101880020007503000080c0115440078640203401c80441c00007400c00400303015410620f14007000a10041e01d441c40c091030654812100100802c00704203203901030f0312607401280c104681c5031302ca5248490030300501 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 898119082 1250 898117832 898117841
    0x30c0608040c05040501242c0a080f061017070e1911041a0c1c0c05060103051c0f12020c03091309021203070f230105070c031112030a 59
    0x50300c812400c500000740f181c40d41d21a1034001d110225440c00344050501e0f2052510650b18407460400c00d0b0b86451f401c0c00700d0213001c444c0300000a036600782145c00500d408500340e4180ba5002c01481c0c098030100c80030170308020603900d22a241040f04501c989480d41510305800c0c03c00d454600140c1d2000505000c00100000320540040303c0702c0583c3e01065107501c82c501035401000d01c410b1030000c08541008a602e4940d150b801d10000319010070304151041e40300c261f54801c0785444400800311014000c141c3e40c05040e01161558009095460a607101d061283e40e98030180d009440c001c1c0200c55840c50f0510808148800b07140c1a600c01d000381d8003505514010350880c0f09124914001000701e006181d40c2d124242014a620307032400700e101306141c01003103000264600d50b0031240d04104a42e80c006100c50362901141e6611060a20704c8180354160f07208000658060066298a071000340401039801882d06d900007442136951108101085c00e00a807215500c1c08142d074100c0f801c0c4049065424107810 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 898120332 1250 898119082 898119091
    0x1d010b030724110f0d0e0319060f11041d0f040b0f061c0b01051203091c0c09020d0e1213142b031803020f010305090f0102042d030c0608 60
    0x30540103012460a070503003410390b21464013186a01502a00042c00d402c48106c00484c0f10840260800d13000781c0c030b40414002014007005001c10b0340d41100b01180e046a6000300c0c0540707a160aa04d0720380c1e441b0b9110116110b14480708000c01100c4000088220032280b40003407046500c031b044240c141d102c5582c00070107850042c0c449640041c2c4090b00c040d4030071884a00020450045500070847d51510080c4940302840707001d104142e070030410545965440c0d110b040d40c541d000241600303844068506050a08007480c6d0880c1800364000142c0078911152030b0001540c620586050f035909640c02109608507104150303640441b01c81d01c4408220f8043d4000c0c0342d143c9240003404800c100b0002d4180c0fa060841003584441d500050400524107155004010300100741118417280402821742d00040c001c1c8030551a11410541c41e100090310f43c04082c07010301000c103030b180300943d2615125403040c4602c1c0c081c80091107244013030a200140103030810010104881d00905203c0355a030400c1012604128000c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 898121582 1250 898120332 898120337
    0x1b0c0311040b150d0b1f1b080a030c030b0a080c01030902121608150709122108070e0306100506033409060f0905040b010207091d010b030724 62
    0x38220203502c03800440e000000f81c0103549980d48803603400b440102c66201c81090300440e4200380383c20804080aa4059004585080c6111a03011030500c0300d00385115660014200000071130843c54858158000c1d42e0303034024580f014000c60860105000c5407425521038080690702c500001101035010b40d120303403015030010344444400c14030302281d24500780340160700c00e005605000d0100070226081c81010760001c0d00140141c068207140e00000c02c801401d000b45640075140e28079020400540c3c0d040d01d0300030522041802d8070034070f0400e0080d01900c000c4030030f6804102c041811502d6442c02007030151085000a0441d07a059040505108071078100504c102c80c041d44a03804c0080121500f00c44000c1d409a80c4c2c210349052031510300c0208003100302e40c041000d001800880b08060f03a08006c80000ba52003e590000b1110003160040f890001568441d6002c03032b180c5050800300219942010038001802c03002070240380341d01d400b4503030303140540d11a101c4041a103a140e04410404010640015074417803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 898122832 1250 898121582 898121591
    0xf0b090a0204060b131208091903300302070f0b060114030a090312090308040f03031d06041a010803161104060b09030f060105060703081e04050307031b0c031104 71
    0x3a404241110b4150304440c03d0024003045c02d81d201c94094aa00018080b2009000e00210784d550318a805401805c000f1441148441d10b0f10303812103040d001034801103400c18144002c89255510344400b070802e08044c03d030a03030244d250094200d03002c3d0003261000c40d8002c1120061181d02d48071001c1c44003000c0e005030b0401000300104050703498020b010318000c0c0b0441c000001d4440305440c000e051480100e1032650750906048803e40071903004038106921076002009411680034500d401c0b030080c10300d2800c428990b034090301050040200029214840e5224a18581c00ca81c0ca00c0b10a1120346024811451150304c02c208005075181c43c00c1400000350300c1007800740d40c20648500020192540c039080440000710104040c141d40c9010040909500303490b42c0680720075414000070030020b1003040300240c180599a000700d4000120b2085030414154061160a41800e20346400c0d0f0b2640d01c03580041c1c0000d664150100100418421030301d01c61a40290000b071381d68515500e1850076002521050303030083d030b0f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 898124082 1250 898122832 898122853
    0x5030a17040f0303050406080f010e0c0a0e092802040f06050c01020906181315090207030504090914061005031902030a0215040503010f0207080f400e040f0b09 70
    0xc2d04001030103140b10303490380c40d1503608200c00108401c41c01085440c0c801d00b004010400c090700d80291a0f000000e141d078203982c500070204190342400c1c038854165008030707003841000300c0002401582001d01e0844046103030070340604044007003a130080f80079802d00080b01c428108a41030092008011000c103060000d03040560200010f03400b07030006600c00440030b10821180015180c07502e407010164188160400c04c5640b015545240c058460040d00e98041d8002001c03024140904195001403d40803403e00c200212440c040440c403043c100f01c41700502c00c10010491440f00050850107036007001c0d0040c094030760b910350341c0080391400b9441660540101602c5a000d80c46d0413040703014041c800c51109641e00e00d04000d050846d005541d40f101c40c0d0380b060101c60005030b0858200e41d0811960f21415448a0b241e102002e80b659002d00a601240c1c80c0c503d90300303401501d8a40844500c1d40c10703e06005070650720041500b0346681220300070f00c80303402c003203407000002c203160700403500045040300704c034902d124 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 898125332 1250 898124082 898124099
    0x21090f030f0f07090b030f0a47130b04110111030c0105010f0b160209040501060b0a03090b1506030403031d0f0c0301050105030c09180109060c050c06070905030a1704 73
    0x10581014803d030001e10051110060b40c2c001d42c514060190010110001c000c10740c60344900d406100180b25050740510503075002174001c000b002128116500c007018008000d80da0240105010b2880c54103464100011880d18503400320f4402c007a00200c000010307030303616559119803e40d100241414031925a12a03102003200300b014007148445c5000000e56941400c1c0c3c1c02080d414180d22242c83e600c4200401c1070103014007107a017940554151901280c0351281d1030020f02405250304407024107400401c4689070594035410200c28540100c841c0c1303015480b515000110204040c4005030071680400c08134000905c00c1c0c0c0f14400d40c062071805014032150200043d0704101620100084550101e100c42110345000e10a44e401414101c00403e015082c1030041002c2c403800402e900c800c02020081031440c20350a402560f52294085010080c01c07400c0d01000e0540e80021442814070310440c0001110103000f51000402e4803c020003c104182403550343c0c8581503565071000080701c2007804001061803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 898126582 1250 898125332 898125343
    0x301090807060903230421080a0c060b060f0a0f09080f070501080a02091c06090203010c2105070509060d1d0106150203130605030a1503050f21090f030f 67
    0x500c600c10110300ca1a0509000300320080c21000c0350140600400b00c0c03040500f1700021034046682c160207101c3c0140d800a0100103980c0718220203014107600085c4012465405007104d06102d1141c2010480380e94048144138160046010b03480f22250100540801c96000e0081c60303130121501c2c609075200303c0d04e6192090408110060032085a800040284400d6802909007a801002c58804508181000740000c402400548405088007040002070b0b050100c250440005550064000d00840002100050246500710142074421216a100c2c1102603d503000b024068441941c6031400c08030340c042041200c0c2e100c4201e064005996100e820300070410100103540300d0300444c000150882c0f174030500d1038204032007111034411500100800c2405441c040702100a0300d003030b413800396144c0d035804100030003e02510601c28184c1d0000c0c2c0380001040310018611801c0b04000c001c0ea81c8444844028400116890309407200784c0b142400070884a0800c0d522003002d00100908a43c10b0754a41c0c5070080c1000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 898127832 1250 898126582 898126597
    0x6090a15021b030d031e090b0117210903070b03010f1d06031002030a021e03040212060c03073605130c05030a0b01090314030a02190b0403030f0213060504030c240302030603010908 79
    0x1c8c1252001000700c0c80f41c10400d01d00d455070004c003403c00d80042483c40406403a1310000b80e4000100441d2025058a003000000058100b90051507034075611141c484090641d036101c0c240080000140c3c40e45a51007121105000da90094002c2620b410003135520000380d0002064004c105a003480006107515410301400c040c4854100e805540e4101401805030245c00441c420302e40d503010109010b03104403410203e80e4403031207a180c00ca081210780c2c80440540c068030800e800520380c507000f6502c0f820700c407410b45004070340c2c0456914807564059078018083d40c2c11941400c01003076007440000e902da5440c0c0c2185071711240c1454000c034069200c1d911106003010340e800c184201d5002203804104290108180500001821294546500b07203a5446840c1e00c0c000b400142015210f440d4000d1031010307a01034604240c1000881400c817900e40350010f042e60054402600d0aa0003600001000c82440038a111407070005000b00c034011a083c3c1056010758009000f0707503015075854941c5404030b5010005805070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 898129082 1250 898127832 898127843
    0xf0c0504140603160305070306050a0806160e030d031e050c1e030c0d0c09150c05070506040f05090702030403080d060608060414070e06090a15021b030d031e09 70
    0x11036007003946908100c4410061203000d0481041800503a40010240007201202440d000c2035a0b9581c0c1c008074042c000d2548040e402a000d940e0100d884400410828801e100c2250100c2c464840703032008481e40301504000d640c06400045c80c00903203d00c40d4200c09079228900d854400d50500710304404080b18411501010400c01c0811132020054840c24042c43d501c00a01e40700b8110308220110385180e208a6040081590303132010400d598a006641620003403040b051000040c035414000034000d4400b500003140c0030301400d1404226071400343c00f80c406641d819480b0804482c200b2040c0a2220070151450040d44001e100000000e01c465005004080c0d54481c0820881c3c030b001406440031a02502c01071189041a5141003240d00b0700c410158481e13414500000c0d408210404201240b0881a40940103e482400861480c02e048030040c07034120180c0c00c5034601100c1402151000b0f5106564075410b811060040352524441c4e004991000554000295100d051001200c215610140102c0300e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 898130332 1250 898129082 898129087
    0x312090706091a030106081f03030203180a0e0408132d051e040c172706090601060e01031b0c0c090e0319170a0b0f0a0819060f0c05 58
    0x4503540720b10520024809212100c1c440703040c0f0941d1034001d00050103814100078404d8001440380d0301c1a141c1e1116241541e4640308c415841c3d04009481e50300013031a031600d040c1101010021340c2400c01e000412540008030841041d219981c3c0e518280d4040c1d022502c410342c000c84045034640906028410820a4800c1d01e20035400d108942c0c0422017141d8002c40c4030f407038200c41006a80900c4075240c002c080d012070f00043c8480ca619000d40300780901c044402001d00e103640400000418034548584650000040341c5922040d8440e1543e960310205c4030040d075900800f0040142502900100700c0f03282d070504012640800300d000c00d6140000b2680e12800003010b0a0101042c8051441c1d210080d000c04041803081400c4d00c80d15607501d2007a40c0d140e4030025910110241c14511510a0000c3c03100350306501000d42c101005d03003101034075a5000e04e611a250038180408035103031408243d0121620700d0040e228035074030044260103d08014401341d800c246c440d48681c800407118400c95038941c0301500d0303558 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 898131582 1250 898130332 898130339
    0x10090602192309060715021c02030103021206130b0604140408120106020d02190f0204050405061b030f010303030e070306020a030c0219080f1803070f0e0f060f1203120907 75
    0x5240245850282203442d0304010749010343d15020112040340e50443e00802032003014000034002840350203d00308070f1814017030704141400400e40003036040768000c64614a030b451450f180b0315210001514030a0505559101000c0080e001440c1140e100500030300c00101068408a400c1000b50300301c404031440180010307a6501c04400980070390140c07142d44010003151802c0c1c400a95a000203000008410303030310306a00c000b0052140e001000701580034209000d5802e040c03418540c0d4510030307210f01840b561f142525030326070035000c1c0036a44a1111003014104503460358800b41c00401030f40100300418055501e012011404d01c0c002400740c201555000107030340c22680c03802828450006181442c4030407010072900480c11200035101c042c503580980d00c0d40c90724a80103810001e40c2c2d0703084003a014050302c0700019042d54403040c000122507821010300c10700c0c1d881503031000034141e045802170303808280e5200380b40043c188400c05103600504d03d41200d2911186031034504200c0011101000c43d0381c407451060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 898132832 1250 898131582 898131617
    0x203010c08010f05130b0402070305070308010e0402300f1e060402030a0816050f010516080f010918051b01020c180a0504030c080705160b09031009060219 68
    0x403404900103103440e101550400e07440b00e05500c80b9120761445081ca52604000300a0140c0c025000144000c0085640385000c0c6009030458206031340c1a000303d000c01c1d0000821600d103c260f64841c2e50f00800f81c0c9202910013800c070000c83d0001d0a024910310801e0203a0005403402c100041c0d070406800000c0041513580d0020300c0000da1007a0591a1507000320003803000684000407608401c0707600041180d101c001103802a120440c81c090060418070410260098a540640c0700030702955110040caa8210516041510801c406590240c2010340740c0c03004104904650340b25040e414040d200401e1401d420340c862900c1d0042c8450385000b81e154071040000740c1d6030104150740c0600c000350b4402c8420546904642c026020007441d2038022519000003504262240000078140d07a40b141900c0d032685c0c03080c14000d44d0341c140e01c08008420000d07640c01141220800e0140d0310068001402802140c01503021000604031404044641a8080c4040c1d02000c506007104c1441031855602c08180b5164903101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 898134082 1250 898132832 898132841
    0x41508060906031902060702030c0a0902040609170c0415470403140a02090a05090d14040b0d0615080901050703050709050f0a2105070f08060423030a0c020301 70
    0x50b80301e44e008440344995034807081001e005041e0110744c415101c0b261030020a00741408205219440051030001040c2203901da8050020b4890b582d4902c5e68107030300c89500803058080c10145154070b40c00382d80c3d03401e01c902e01a00508443c001c02c03218501d4a030350b503d5401203e02d150010301d409080c500c40822076032004850450f0021400720b05005074015031540c1e025518491800080c215088038254540800c00420020303080340c0d80600610030b01e01d04880d044006000a80e010076860085042d40b0203000e104131000112070900900300d610f85441e001d000b8549074000032080384c8040e201c10000400c1c00e541d03800300d2988480d81d1034011076458080b000d1030840d0302c000d0241052500d48400c0c0424164003030810401d640043e10074020381040400000d0031700741c0ca03034480c07c880401321100c00d039a40398081c1141c1105208004036900c50762540307101402100c1302d0241c0300b00741e48001e00080101e04041c0d040b003d901e20140100c0d4100d06001c1c10b0504607400007052502041c4c00001480031801c09205 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 898135332 1250 898134082 898134091
    0x110a0e030609190f050c1e09280c0309020a17101a010507021309050106080c090411061e0f04031403070f0221160608010605040819080415080609 64
    0x78000d22295000502043ea06580300580400c0011a0903001c201080205801a29000389003c00d89100c01c1c240c0042c3c0c1c811141c4c51405048135001160380c10040307a42da10402c0101e0034081c4420249260440000e0080c682410101900c0c1d0718501d0240e1500303010300c0c000d494000c0340340c80d800100346202e91411081c0680743c903140e480c104a0b007918041080d0b45580f40070017440c00030390f500074500001e10140000085980134030b181c40c45110804c030b01584008121809c010554840b400c040080049680c0c007124098a40301e1000c5a881c001d10b8114010300c6840e2410700e43c40c1c140d80c0c4101c0c040030213420800000f0404d44000070140248010070126520201801e40214078003601a82d03524205d036102c02c0024010102e804c3d040242d040e050448181c44030142c0f04a40030b40356403001801091400b449800003044842c00007040b1a4030542c00c40d800e070303a0307172100501205504000d034030700d07410518400f40c0f4040418400400c880c4a14040e104441e0b43e1551008414104102001041e00000c1c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 898136582 1250 898135332 898135351
    0x100b0604060e0d080d140402011202090f090408210609010506190c031b2316060f121b0216080a061d011419090b040213110a0e0306 58
    0x881002110b50120310090854015105007207003108510381545203010340d04103030300b01030300344100c901c03250b003030307804054401c5000b6a10041200d4510320300108910038070024542012041c0c01e64400d60424182d900d420910a400031841c0000b4601000181c079144001c8030328003901c20b42401041c0c0b400c03030700031805014115806c9180000060000303002c1e070762401d00442031000c03c4000900b8035010314003600400c240007103240c500c000540381003403004405222901c0044884441036008200014003082c405034503503001da04c49030401f5403e030b8184150305502401c0102520011100560320301a0b00d092200303042004d0001101d01e04043d0408070003820140f480f40c40d0601c20048088005080c0d800d140d003058001520000065002000c0e039401040700c03040398213242c840003a0707910021800d48201c01d02c0300c0e06000e0100c0c004041090b140d00d00000f401101400001c103003d8613107903001c802d08415080b4002110003140c143e400701c540240b0700000100e03880072145800d0f03040074801b0950090000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 898137832 1250 898136582 898136587
    0x41715010f0b1909090f020702150f040b0c0a024b01050d110403300e0103020307020307020d0804082e020c0f16050a06050a0f08060f12100b06 63
    0xc0308a003541d005111000341058007040454400e18002c130301c40e501400704e0307660922420740354018050180d840170000300d0181c07041c2c01d040320110a522003902c6e01140358800140c42d140c40c00c00c1103c01500310510510321400b810101600596070100c5d01180100060440260805904905446090115412018692a201040e420b034110380d9a00048074000d003130281e101d8590241c08001440764503280c800c107800004001c401d0082d203031407254a14070b41c02003035501d100d40c207007a160304910070a00402c003081110b0150b8050b9030007074002e1584404540304030390900b40240c00155402155000a60384c4400015003404150307810301c200b0101c9001d0345201c01810401d41042c002c071740840070090310955400308101003514802d00100502078160710031100401c050113841c01014056101c0c0764441e10800301e000445500640030f071041c0000c0e130348411045c0b4803c06030658000d40000c0c043c99020003040507070f47c03842e600c1c1140c0b44829100207000740007010403041c1950440b000b48031107a100340820b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 898139082 1250 898137832 898137839
    0x30b0616061a010315061b0b19110a080a02072d05100c1403100b0f0903010614030a06050402060d02040605030a0c210c021c0e09010509060a030206090303041715010f 73
    0x1c08070a00c0803206985442c0c0c41e0700c40704010000107490b140c00c00404e4203540707a080c010140092270f034030100d81c02018010081500c00d8900c04203144170305c006602c0802c80da180010000c0c1d440340d000d81840d40c0104142c8100404145101342850045100c0280344680680b01006100e001c101768032070340000070020000351800000241418201d00900c6142480020021711070002d40e080d044d00404000441c0b5445580c03141641d421030b000441090301030741c42e201d8005a2001d07412168041d0040c0540a40400101d50f11803c001c0c2c24000c1042c0d820400420103060811154401040104029078480e80c507403c0445900064500340442002081032131150700909a0070910030035980c032000f100006040c140310800303a00340380c50249400032040e0391040100c078058001c9060030480804030740000c1c1070b030b0f00e4904010b807044055441a130049442081440103007000310041408034401000c803800d1950703c01c08000d070007800c40322601194014904170705c614580180c40718090311180340d5a1415608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 898140332 1250 898139082 898139111
    0x3050d080c0f040b0c0f030705060f130c09090303060b03070903060b03060108070e09150c0406170f0c0d0212010f031a06010e0f0d0b2d090d030b0616061a0103 70
    0x5500640240713078400290200305a104020410051666074196600d030205410408c0e12041c08440704020300c1c41d19400192034082d1020058101e65000803ca032000342409180802000c4200085091503030342c5002060000c18400a1445404190f40b0400c0c2d46055203031410556015800d02030082d80428010700825401140700c605884180620000c00d42c6d415244501d071108002c055079884c20301c0c03000d200c001c0503034800500580305507444014011080800c4442000822121010040300400c0030071080c0ea08000100b9400401c09030140c14a48550318440c00d0120a0b44921200786108a0400030000301800e00d050b200e080e038501100b149040e00018000a814000d5940f01d12064610b0340a182c0d10072040404080c3c20000707251092400009261001071140848168001a09007840c44503001c03030580e61041d01c001024000309412010290094092450900c0d80081d05102c0002e2031420030051a00950162101088480040d1150281038109440340b038109820004480807240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 898141582 1250 898140332 898140337
    0x40b06160803040f0f03030912260709030b0f0402030d0c05060606160b0711011a0f040527010911090105010c0b042108041b0e0f0c0d0603050d080c0f 66
    0xd801c141103a0780e83c2e07901e10708071038440c0c41d22000400c00414118040e0505502d0f6010160a510451100f40c210320700b800140d6110f0a0003505990741c0c0301c0c0000c0011080042d07400ba5070817801500b840e021907522a65201c0d010340c4120381840ea003030701010400042d03141c2048030f0000c000c0c541c20010521182601c5007600c43d2030007400c003405550005140c480d407082080105209030f82281e810300d00d0742030105000340f81c21000c04d0000040d42c20401041c0c4100e000c40d0a04588a000a00c4894580450700c1800050704000f00264011120106043c040104a0480c0080c882820300005100344081c903100000100c400c02c05400b404c003840050000c2d0b41c0110311060500d030800c01000c1103943e986464401044024040040d03110390100b880c46258004000078001c61003840d0f10401059000344441103816103214150075524000003141c0d4440050548582040032580245c0ca041890700c480400c4d20039650049459900400f900c40007242c2c046580742c0c002d404800514900300072041d00e0003460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 898142832 1250 898141582 898141627
    0x1809070914160509060705010b1206060a21050106030807140c0901060c1103030d1508030a050313050703020306071d0906060d0b060d1a011b0203150c12010f05040b06 73
    0x100c0c05540b031402e4030740540282d50040c00c004200e15500d90759407510754080d02011140c80c0c021101d07080e4601541501041c85482550301802c0c001103289404820341900001d622240e40c046146240b03200421400e024a5000c1e41c0a42d405580e01c0020380361501d00704091014051883c1c000c000c4862107907a800360790740d0440749a46440c1d174040209040c844448105031483c0c0f80c2c103200000346170f100d02005070021201a1200c40454a03e80c1d50390900c15100e20442c45580005841007000070101240320301061111400380c0101c9502903101e42c04245046000e4500d800420b480724401e10004c07200e406c07a0000900c0945038142c55090400200304140076403c411140180c80d910b15001a441c2c1c1e500350b404c0c540c111801407044051a24040b010081c14039841030000354000e4090125510242d170001180da4050000c00d01007611068482d0414005041510011000c100003000c4044207201c00c0d000e030458005811081c0e01d00400c03c011251810400c5020f14002d100f0198000404103810109 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 898144082 1250 898142832 898142851
    0x1b071805040b07050a2c03010c0201230405190501020304060509010e06010308221401140703050301150c050f0606090108070b0304120311070605060f1e010c02040b1809070914 77
    0x851400c0242a06c4040070b0881b00c407070000c86280d10000755601500c45058401d800c1c1c000b08018522a841203080c0e41c04030b14500324010f400e04481031840c0d5580c503560341c03150040082e40c0c070032800340c0b42c100c2020304602d005451036134000c01403209012061090350f402030314804c001c014510705c0240c09512800148405010075401007403e00c403140c040c0f4480f41c000000b218007650550344804000941004071400d00d400034800039000c070b0030718a003a011a402e13950945c07200750a41e8a00f01c91041d8940704290480300700412055003000042c4100840325024140001400903890006c00384808120164052801680800d8040002c04210b1040700d0b0007a03005a0103080c1841180010b601409174001c21450589000807100103016940d03005d1400b4580403588402c00c942e2090401c12100e03030b81c0343c3c120b50308003043e456005650b000f1380c2c6c05d012052003d40701080007110400000c000f075200040d21180380c01b121007045003064040c003101c0050f0481c200e0820174486290640b00c131f003030001081d03991f0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 898145332 1250 898144082 898144087
    0x90f071e050c0726010b01080411040f0624090b1b0a05060403020f100c090e0603010f050c0405090109020c151905010b0405190e150103021b071805040b0705 69
    0x304984660201e841000714001280d10305555010303203044c5044040a61000c4003c00514000a0801030042002c0180140d42c1c25100780c0316501e66140381c03811410742d00d6000750f0350800044c600c2c245005500007003040200c43d80740d50103500060313500780404840c598204034800c00180800f000c03220a546215205000d01400b416008260918190900c00301501c2845044104004c240d80041c000111142c02c3d000d4a00c410f001d45001c4050720702880354513010a1094005000e00000c40c4105a84801d00074004030340b90b8820601c107821039105032455040d42d04000303024400e5061448040c0e004002400d000c600d003c13600002070b6200c00040740d010482c20081004907806061002c1d081c071000203142410405540c2d0b03026001510b91182c481c0d180503030017a029990302d070030140c401002100d504c80f11600f101e0351080c1c003864601c51926400c03410725609102d00ca00c2600c1c511000c0c51403941d002e0041c1800381c142040c07080c5c41e1641e03124282d00c42e803c0c48200030004411600050b0485024100305d078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 898146582 1250 898145332 898145387
    0x110604030206151212070c060908070501082505041a1305040e151005101704080a050c030c070504051b07110402070f0f151a0d0302150a0b090f07 64
    0x181c511081d000c00680d14440c440e40006171140e81d800504203940300b44c5c444400d06a40d24003d682c03024503032041d441275410101003000194051643c041c1c3c01491040582d500040041e0300c1c044000420812400061002c10b0601000d8607104482d020415486180d80c10517035411200100318a82e030103158003998440341d01c008019410007128000c40c0c001c422804035498510b00c440d0310b0814901c54140f0071198014075900301c1c0d02400b41020200c426101440b5142e84948506000f54803090a5404100701005003180100041c0082c1001c00c140c9270192a40d185040c082009907100a840d4403005801c0c41112411404c0b510b00319510b1940c006d1100700308101c028000b400a0040d03d40107000c5800c0c1d100c07000d04001c0022a95003595204590218401207201c10348030440d9090088070540d600030b480f10001034640180480d13100c1d446441141d41c8545c581a030001c10540542c1c0810400b41c440070302095a15000c0050b0383d10a00390107182d0a06d00d030080c4020070b60851038200f030301d0352185030300b030755 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 898147832 1250 898146582 898146589
    0x90213030f03030e06010f0b16110a080327030d0f0c1a07110c06040306150b1b0106090b06031306200c0c0303030103030c032001050c090111060403020615 68
    0x8a0003940c005207108000c1c091420080d0203081c891610410300d014517000800c0d41c06076040e05000783c801c0700e1841400e104031612000000e12040d141622191000028920156103019074030000d13081203000ba684660100203524640c0b18070b115043c9814007503d8100384e04d5100003800d0040a8814a030506607100b03841c40c15079280300409000381441801c059801107440381070440d40c0c010010341e521110130b1503595040c030b40c440407501c842e650b01900401040011480d1030700b204e8124940361075074555296a81e00d0301985540107080003141810700025030700d03d2010a21407440280f4050509020000d00743d070020b00c040c80000c1c0007039a54400f18200340d00703122899200d0f0441310b1f00444254411400103003110b81c660031110f80485140318440103c45942400b02c20b484c1200e0345605c440c00c09040e160b4090314003528081a4000c20307030243c20700e000e4003c400d01a8501407410340c40820340d2440781100040141c88462864a01c41c0e000d0424000000d07030009034a907200e5000c4550b0700001c00180000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 898149082 1250 898147832 898147867
    0x50c1302040803190813020901090906140709031a0606030103031b140102040503010b060c070b0702451b09040f020c070e1602070e07110109030f1115010902 69
    0x74407540c480443c4581403035400202544c489011034a80300340c0d55880d910b843d83d400c0c880e03010007504901d103c0010400f0a4268200c20180d0f0f200703245c046200c043d502280c0c0c030725040490705c500c0000d040c0074040040c410540f1850400d00c454a01d007042d90328100020030602c3c80188002410000582e8a941407042003811130600e19a000d050790f089901c0c1e4546080c040d400502486101e540303450741c0c0158500d4114202c80c032141c40c0320090540d1502c3c0c10200611900003981c240d03044000d0f070340c501c41c10380c10883c044940c9501007629000c419001007000001d003902c41141e400d4100740a01480400e080c1c8100206803121440c0c4010f80e903002c042c012802515a45130501500c50000c5100000603d001c036a450a4400e140c4503904240c0d107138036511442d481282c00f40b40240e0800d080511104035401100c0760b1240036418083e03214440b030b0402d40e00315080c0010990000d611110402d4419612901050308030071880c00410340c101c20400603400501040c4954540b07142d002641451a0148411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 898150332 1250 898149082 898149089
    0x1060b21180c0d0611070506150a050a09020a0504051207060305130510091104021b06060a12110a150c030e010306210204150618051c140a05010204090b120604050c130204 75
    0x80e0b40300d1b6994a00035595a0003550343c080070aa1510703040a49040088102084541c02843c121080e850b28515800030b500c045054400c00400b00300208075500c450000d001c21a58110090000354a0007400608846024000b409101c1c20071a417000400c40004001b2000c0040405c00103902159192090865499803981e5810600200352030421031004114043c001c60000240ea146990300410014040041d010345005210458650be011079941c8907900c001d80006001c0104403501c40000342403150702c480010000880803444a410164032100c4079034614401c1c203052000038103145000c030381400e0160302c22084a081c03515480c25503a46810946c042000710032585201910348130020035041c0c16010008610103056400550350412480348014009402a6038081d12030a5442e00c408849080001c002d5104682e24880820000e2000304000c1110303540c0050254480e0081c0010a9242025203d413500081c1c02c0102081c80400d00f40c2c1c05107030441c0e581c0c0c44640b44000100017802540c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 898151582 1250 898150332 898150361
    0x90a080105090d021b0603190f1d0d0306080712061103150108010b0a0e060a020a052508060606070605100801050106021608031903020c01060b21180c0d06 68
    0x409022041401180b01c600f43c2110360300b80e61400b281c20030a03d10004d40003408540000c3d040000511a9010f4850001480d415030307000b09001d4400181c41c0c06440c0d08402c1c51032000b41ca03022640801004106c031030340042d801c0c1004c0c4040d13882c0100706504c410072031041400544080c0400f02c1001780c2603114512256000c00275036103e04103c3c2c8291840001541c0e0640842d4000002042d468044802e480305034000350354114582c143c8005100150f0401e010950552140c0c2e030780080013410900c00c3e071074141c110340303d00d0b03440c80000ca4014003e1503083e8401c07041500310206200c92600c924049944541d000074020980d038503400d800d0940c0707001039480010b41c0c1d482c10780040360740d69010034100f10030b0b085007082c11915511480172503281d21034184080030707982c41d80c19658105ea0294001e003603007241c0500001105551385010104a50191b2200b40c8100450040340043c102c82000d640c0d00404904440a02940c9000032590f4581d0101421482810144011000c1014036007181d1251007904 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 898152832 1250 898151582 898151591
    0xe0114031e01180c112e0504030f02010510050d0f0f050d020307060f020a170c0f371205040804120807030e01030b010507350d0501081501050402090a0801 68
    0x6107101c803800c06440c68583c60b00c50400450f80d021078407a5642a000341031940203011030044074500e00044031256004001c9101c072a60020100c91194841c1c90700c00ca0107903c0d400040700341590000d00310303640100420040c0c030303c0d81018005c54540d4049491165800400c804245e541c9040074024400c80040040c0144544200405c1c140e07408000b402c40c01c1c2c0304620907c405801e007640f400580c00344403050b0740001c2c0009943c070b040c80300b103180c4a074104441d200c8581c50301440c0000e123a041c0e0702c00189207014040d070030130050200350302031038190b80d0244181000121100d0144024100c40d0764220b024041a01c8402080074018080708803801020842603620f030900c41841c0c0b061443d00000701c15000328454001d0101954040c1c002e40046500594465141031003542d00d12005e110110f550340380d80005c0c1c15030381d080ca0201842024401000802c03031a03c55581d84503c10964030141c00124494000300b03801204400b4510209041d90412100075071100134020204a203580c0d6a4082c042039801c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 898154082 1250 898152832 898152839
    0x140a110c060a1e0503061e0f04150f05150a050c0c130f150308090d03050d05070206010312020c032d100b0f03030f16030c080a0914010e0114031e01 65
    0x10540d24011207001d1100303084100100026901c074017084030820303000300006203400d40c000181c841070441400d000385520741004900700418200c4103038007116a88a21290401d1041504014074000100b0301161486990003c884800d0154000d01030070740144000440e441242400038029618080d04c0a403660b114a44085040006001c161303a100c841c840c508491084500610160401920340000b075203407400603400280080c4400c841d00582c104003041c8621001400c1500030305000308680e40c000d0059504500704600059002c280c0202035502540c083c00003920041404e4114071000046d0407440c400340b00b2100588245d41c64202150301815508143c0102c0c2c42e4082d0841c900c040c0c03032005118040c581490340e60300c240d1400c5a41848240170310110000b2803081408194882e03c0c281c10380c002d1682d20610190040c1d031082c0041100e405046c1710858518046c00503581091074081020440c001c0042c061000004060201d03500000010b121022090103031501c54944221100e00d5695 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 898155332 1250 898154082 898154087
    0x40506061231050606090a060306050c09030d020d02060f040305070605130c06050a0c11030a02130212070c0b0415110c0c0f09070518010c0b040303050a0606140a110c060a 75
    0x26482d110004140503011038500c18030748440162080358040002c0840c0e454110411024403001013803c002c8649412003c0700160050007900d01910034509803907201c4c2c41d500304140c2400c0b110006003046600949014030000e83c0003400c1d41d00900c2c01c280c10916034a460408465520070643c0c0640b0300f03070420051042c94452403903003170f007941c0c006c0012911154403044111014070589040d000000c102d120540041104941003682444008048071401e50180e40071803031900172110600700c1c103036001c43c01c0300d0b40703000c0c580509600031040c0c500340501c072882e0756460b500c075440901f02800f000c0311000540c000ca0000d0340124030026100c00ca040d20350010301c401c50746e504400d00180b8042c0200401604007401e044d101c840c003c00341c98840c00c0c10883c03480d00018031007404014141c100310070349030360502041c078030500b0a0050b8060380e0040b566140c10001d501c01c0d610180d12810801521700028001c0042503415280b4030303509440d04080311070001d000b0740d18007407224444a80c44a000106806006d4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 898156582 1250 898155332 898155361
    0x50a0f110a06110706030e030409110a1403040c030b1f180e03030105010e280e090c030c06160c0807060c0525060e0121052a090405060612 61
    0x18048079030490080e1101d00803079040c0034a290001c40c0da0300c004014803546000350402e40a1000d51801c60f41000c0c0d40764400015034000e40280ac40c07088002841583e000d510103540e1031111004068586141002d0341d408651588a220140c800002100490b00030403002c403c60b070443c280c01d9a030514068440207040780411440d080441418034003c440c0440d1400402070380e040340ca058590300a007450130400d004500840c05280e1088000c030294820f0000d081011380e2000d041c03c2404a0075518000407003614081944203400d02c6540840d450070241c2e600c5104454102c2940300d005240c0728060b2074600510103ca41203001940200000401e44d00e038058a11880c0741e00403000c907400b006411440c441d14078810384041c0c0e100e00c001b038000d20045000c0d00701810075901c10315208209242c0651018064503c80360044100e680b1340c010b005800743d52080d8040d1612002105038100d442d1001d03040c10350b01c00e6000a500a0341c56000080042c3c3c3c9030020b460902e00c6001c2c86060720b203043d000e52500308 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 898157832 1250 898156582 898156613
    0x40813080f010c09030521070b0115260408090a03020607050105040615030c03061a040c020a17160b060a1e030611040b0706050603010608010e012c0a0609050a0f 71
    0x40d842d05000301c03c014407400e00c4104a9030004003920410f24040c01c521010b1005c2031010b1007c132030803c10354000446005017140242114189031041e030f03004c01001030144116000040203207800c1000841c10340d0320220010340065006101c80e80d684800d9000c16000c440903840a507100e800441c5520501c0f1040d0003091259100314800c0000e40e121605040c2150018000034199005290082c000680c4644c82141816005569004608000300015094038000070f40e640050304a041c0c1481041440503914210711182c103181030418400d10716680306c14030f0600c000303400388064a01092680e00c903400380750040c0c454080d241c624200c1c07042c20b4580e11260781c030080f00c0280c9003564000060300e04100356400d0754150780400380b800317055440e00e102801019041d99811355030f9210001e001d520900c98100058440b10022680030240604a404134100940400748001c80070b03464000c1c00340110301d440c400e550000c2c0000f54580355041640c1f4140f04210002c00c403034079800f90b45050110625190050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 898159082 1250 898157832 898157863
    0xe010c23060a0b0607050312040c050a03120305282f041404110904020c0c032e020c07050909100504080d20030126070b03190b030705040504081308 65
    0xc1101d40f406104e2244105640580960030520101d0000400c9070202c680003405828110400d58803200007400c800c0155200b01c407c1075140100c0e0042c280c15028186d4400840400707105600c204010306002ca1505040616410782c0d90001940f031a120b14100366800c000d0510240100340104422840c40d5000f8015100c20364080d00c41005c0c035241a0140040300300c1d000b00428100a8110180700213508000c0e000e001c91300511541d818244c404110005040352300010911142d400103442d00c0c69001001403140b40c181c0100403001c4000800aa520304a8005882100e00c6954901d90319052103078000451120034206014003042c0a1004042c044c070b02c0c0184010031004d40307003004a084801320207c030140c0301c0c5410300c01084204c148000c0c5c4858002c40114541c04400b20f002d2450400b180c1e9000b80880c0380010003849144d5040c3d0140c079a944005103c02c00c81e00d0008000290748030040d1003001d1066481c0c0700050200140042601e204d000c0f20400c940c00c0c1ea483d00111500c840d0301c101e65a18 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 898160332 1250 898159082 898159091
    0xc060e030f0309130506120a0501050a0f15060f022503020a05301e0102030103140303101a0c0f01050a1a09010b0703140a020c0901060f0e010c23060a 66
    0x1d04940101c115292030030010324520302503c1c1c018040c40070b48401420705a2210f4414054140c0e950117000403921035116900014043c50134070684801c480c0515600c03c2e00300c0c81e20000c41d101c0440001c428058800d50f05060042460243c030480c50005032800030b040140c00040c01c074512700e070418800000e80c2e1089400d80b4590707880e242441407500c004e040300e209041021401d021140c25403c1f01010501b110000e44007501440c8034180d01c50b4a042e0201d043c0d81e03500000400c00c0c0411180c20600b043d1070b803000b41d8a1400c040c0e80c101100301e034900130640b44507030454000f032850030b4080443d41d140001501f070b9080c178206004594002c12040316030320607144c20500c00000d802e4080d8580c03c140e00700144038644603420180200140c0d0082d81c0210240401c01c0c02c402030070703d841d502820b2885003aa008010501c2100c041c080c58600c183d014909014021009199541d0020307101800d4082c01c0c071307280c0c050300c2e21800c00315031401c0054030b0031405030180702c0110304281c0041140ca1140140706810311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 898161582 1250 898160332 898160353
    0xd061d04020102011d0a020d0303020c0706211130130b0609160309050307020402190e060f160c05040e030d0e0f0303070f090801020a030f15051e0406030c060e03 71
    0x141d6880c1885854055604090003440040c2303820814039500b01e019240c0107007032102081480e07203883c8494103d6804100d0003100b00380150f0074044c00c403121000d5120140025006410300b0780d007501444441d4604c8850110502400c10301040c17140301b400048907051070359810180443d4020102508041d6070b0110060000f540c6402e010b21118000d8510b45007803a1826074800b0110000d11040c14100c40600040120102590720b90000d0101c403100000c40c18000c3c1134180000d0311054a0200d55400307031005001066003c01d1400c155080901a0401c4264290303c034038004a603100549c000329413103480c10494100c000300c000043c00100210038410000c0c2101c15040ea9543c900d9020350440300d46c010000500103900c10007201c2c0c0d10050300d040c400c02c80c03a25520f6240c20398100c0c07030501c40029950807620440d00c0150041d09a00300b44007004000c4a0305180100b84096490942c0e5540c0c0c6040d10101c0c0c0c2207842c2d81e4407010041d50801034580b04251a40c8000348003554524145200e07200710400e80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 898162832 1250 898161582 898161611
    0x280c051521070e1e270403021f0605130504060b130b0307060203040f06030c120f151403070b0a05090a080105010f0e0903121003020402130509090a030509060d061d0402010201 77
    0x11403560b072508813605003450a8100700032840c001d466009107122942d07038105040762949008580035621039009000c4c044060040071451030704011448a07a541000010011030b182c3c0c0300b41d030400104a510110300c544d150f007400b0010300107410707040e50031652440072040b8810040e40008444c40045050381c140d16914030f0202d95034051030090500a41c964942002500d009074002c4846e030449003858480412800c80b0241150241141006080d848000038400681b202d040f6001070039013109000790031241d10011075554034042c054103101080024030081c10500810035102d071104000c1003801c0b40c1c1d0f25549064040e000038845c6100c2e6030440740f0301180c0e031121811105c1c0f10380c85040007581002804500c1c0310080720701038068842910075280110158646000600703c0303100012980706810b01d0101030007490003001308100380b40e41000340042e00080e03000301210015041126604d45074060a00880010302c03d56010380729009100c11302c0030b186041004d2031407141c4d000b40c008000d20710344d08866 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 898164082 1250 898162832 898162849
    0x24050705040302031b0d020306010b07060c030c1b05032b0b060a020d1412071e0219060b040e0a050a031404050a1206090501050108280c051521070e 65
    0x4d50540140c26984040e0001064081000340b008007040d43d0442550042401c1a000703130800c41070b51100290340b4003070200d2400742203d08055480e00b048140c0c0c40305c03001000290100b0200308101e1850070a41c2c1400f104109480100480e4082d2641091900407294520790070942e191000d1402c04c900004607140031000da0348041b1258000e0316850a4010041b07451103240c00640c1d510360010300480b16040140ca0341c40703200d41a1500c85001f44881d9041102e041e043c81e854200456004030000c440090074030940d00141640071101186411542001801410311a105004980310b14a42402401030001d2002c1c6da4a0181d1180c484c000900790f84210640b2550103001d80000060b0010010394265041240180b8002c5c2400610509643d4515003918000c1c2d0202c030b950781c42805108015019485521801c82c0000e03194001784c1d01d159519060a50325214251041c5032403c60000510424000c40c1c0b404100315003d2000c0c14209503c4921442c81590781500003407807202d0700741c43e60811851 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 898165332 1250 898164082 898164089
    0x90f060b04060c080a030e030d09050118080414010e191d151201090b040b1b03220f0b0907030314090d060f0e0f0601031a070504050f010302072405070504 68
    0x9511000283c142c03a0001c603548607400003410141c0d604418400e4460500191410003081d80012508090385d09100d4250b40320004410050140f80350b0150000d24810125001c0381e08202c024004038018800513a803d844004440da000000d620490b00a07500c0944e0351000d407014400414100c5548800d48004004200e68440c030980350703e000c1d802d1500e82445444000d03040c090004c00c040c25150342c0c4e003026030f4040e43e04890307040d10303c0e0a001071035070101c12681601000e83c0341581140780240150300b1440c0003080c0c260309048284d8544d014404041c010612040d0046000f04183c1403202c1d03e160389808511040d80003a03245400d00c20120740300e008a62240000414201005001d6140c01004200b43c44261141560f204150b996181d01802210000608200541038661550404034200224480c800b81c40070400c004004c031585d005401e036000c0d10000d40391102d01502800041c1c000b0311a0071000381040442b40204140c060b071500196801906000c02070026446054058070280503901 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 898166582 1250 898165332 898165337
    0xe0a06020c06161d04061205010b01090501030212040b060f0306040b070e011e141902060609090304080604031101060b0d0b1206130b0405030909010303020312011a030601121104090f060b0406 84
    0x380103071a001c0000c00903134040d0b000400000e141e83e599146489407840c072000840c0c1036510341c043c1c9402984c010495400a00003030805601d005005d40c200803007140010b0000389050703030a80200c0d18944076401d01c1221030102508840403400c01c1e00740321080000454003400001c40c00611864103500c901880210140e14488507034101e0f00c0c00302e00fa1000c0035860241c85020300c0601036441c070300842e03044480b244103041d00501000d00703003001444903100d80200803020300da0003004100041c240000344a03030b0007605440c0031340e642000c43c83d009001d40680e80c000848040c01081d01000000b5950102d12000c40c11241001190740500f81c0e10b0b1180c8046403607070f442011203c041c130007082c5c08141c1281d225101d40b003501c0c03a00100301e001400301c080030707041500180e00200d050010501c01c1030f000743c090041c14a912452041c40780002d01c0a03c001001c240c10086c000083c000b000b43c603030304039103c030202c8070740410340b22610365540000400020004980440c2071040015003010700b031b0700f10b0341131711010f9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 898167832 1250 898166582 898166597
    0x30305030f06152d03091c110109110f0306190209060f0a0305010e1807180f05041104150b0d020c0f010603080d0e1504150e0a06020c0616 61
    0x11140c1044040e000b0320041e00155070b86104842c4482c100c0003001e15503100302da034501c0a400c00d0b003a40300084001e0f81d0202d1188040040c003591900c0000d000729440c402d00f031304030440ca044c4d060443d12500c018031030210642c01d0004040c04c002e0300d820b074101130840a0ba600c0284000311420555203110540343c814052029885415911138680c00401c01e1603400341000740b8022440300303800300c50741c400341044001944e12030052001a885482c100c1d0825191046030310044851154035807903c4680c400d400c500c0320500082507a881c2c503a00300f02a0100d00580c10040f40c6002e00300603000e200c0c030040440c0701d01d18040124000c10250001882071303c002088032418200c1d1500e15400a500c00b0802d848140b00315950729240701c1c0c09001c0d00300658407400d403190301c40c0042544c420a440019407241d0994102103101c5500c04040e0a51a51194011000100340c0c015045420700818002c08000c900d80196109003040c020503400500d90540d4142c201c035066603e441e1882040800312600c0c0d000039010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 898169082 1250 898167832 898167841
    0x6050601030221060a05060d0c0206010605120705070f060c0e010e010315050f0d05030a18050f090f22110307060804020310020322120f0f0c020d060204150c05060105060403030503 79
    0xc0c1c83c0240d10803406820b029140f5280c4001071070a07040011f03550752494896840c00202541844518010301440c01d1941c2001c1c030300041400d0422008042500b0020007089840074410f90250b414100ca4002804018000c410940101440341c0403038101c2c0800c6154a084002d540300b0b01c80c1e18142d5210821001a1a013000c003004201441c2504640d80100040820000700c0c2c002c6c4001d0007400b003d0b8851540191060040c84041c022030780c4694441d10a0f5410f040180c0c940d9265160310010314220396045a0390700c00110007400041c1d003125002d0920380c0200c42040121582608541d2084007210b01c0e032595a4003c9648040c01c44000f90960032610540c41000c0050f0080c50304041180300702c50710301441003070300c4c14440000c450540b940341011442900b60341c6c10400c0b9945410103894000d800102e0a24060305c082c206180080c0904d4140004100b0700442e503050740c0c003030b10065842240114202c00001c20075800c05000b51010b0241b20000121303454070100300d408995150b20340e07908583d04c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 898170332 1250 898169082 898169137
    0x6080d080f06130f09120c0c15170a1d0c01080a050421020a0203010c050712080c09060c03090409080318030403030c03113a03090c0317070c0f03060506010302 70
    0x105075458030130f444c0c00c0b0312800106d030a2900c180b6407101e56107840a02055043c40303404070807954005070400c2070860701c40518a512140c411515040c00702021034a0701c0d1056002c00038061101004001603415855455800020030700c100d800c0c00903601d400441d2070b0443c1d200100e40055600a140e060a04400011054008003104820001c4c1c0103840481060b500800e003900c84040a031000210006295001c00c4042c01015400d0705007460180060701e000c4407123100d24441c00c0402885000007090b2044080c82c10001c40e2440c03d800f9100744910001c6142080b15034109658240000d006503820004000c400402d6400303c1c0e405a172106620388080e10140c4045102465820040c050341401c0901c0482d144501c3c541280d003254510950140c00612002d00d1350104040c0d000c040c2440c2c40070021a0300c0b80a084140c1c1e400801c2c040c0520300c40440008644140d035002810000c40d11800505130980751503800840340076400a1040f507030f6002c01101284903000d03820b460129546054040c420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 898171582 1250 898170332 898170341
    0x131803030915050a0f1118010e0406180608010e0f03030703050408040e1303020c040c020303010e090115140a06080c0706050606091507231002091306080d080f0613 72
    0x1400b0340000e414224641c9404016a03204454540d01541c03980c881c0000311200d4400d081c0500c0d8510301300c600346500003a9500001903080101410080c0140010805540b56480100146a04002d00890416070700d08200684801c0c455401c242d4a884041d43d80340c103000c101030010350052005140fa554804006400404000d0810345429000740030106940240d80c50b1940102d602c900040d60242035850000e03d17200c4c20300d0106021700d0074890110b07400c0381c00208ac0ea040d1100503600e065155102d140c2140141b06201081d80c00802981000580c4d40885c48256411201a00c4100a00e625808240c4009005440f045415941005154007280042c2d000503003100004003d5454689100c000481490006007401c4a00c407001955404001d80307035000d40c5d40360342100400402c00300303981c16664454080001c1240074540010718815142d456028001c29044640e4040000c183c903142c0c02a0341d0502c0040c840c1c0440c05410104038203207408541c1c207204460040c681006070070b01f1030a41e800340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 898172832 1250 898171582 898171601
    0x30e1510150306030f1b09020a050a030905190b0a0f111803101d071211090a09080a0801093b070e01030b04020109060804050316110301150513180303 66
    0x540c1c2d6010201c0051074200901d40114041e160948001c140342802114a43d81ba40c042000d6520412009021341d8002d400e69031407907518100000d8021040c00c0c01810201c01000406406800d500c0101c200712407610f4160050106481c10490441c080c00c2c0700d001c9a80d0360044401c0f4032803c2c84034200f000090700c3d1140320550094240c84180300c50f1083c100680d400c082e0081941c0d40d4410384004c034030400300145001042d00810316a164210740d00c1d60182c88032900083c41c002c0d17000b5400181084140c0c0c220030300442d8031181d80707540c2d0705075038100070400540ac2c01651109401c1130301e50160413242203030f000038011000c5500030b02900d10072a10032100400c01480c602c1e0380600310001582d07503011180309000307500450b0a80111710702840010b01d00001031f00103c00f4000c0e940140004104c0c00001d03900c0d5034030288100038a44000c0d04040c41070a00803010391780d0542c01c14103550300074078a181080040395410380c1c4c41c400929080c0d4503102034a00800c2048021607200d0000310210744290001c5104 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 898174082 1250 898172832 898172837
    0xb070303020c07080c0114190c050a0b0c070204140402010f30151a190908100f05150102030d0506041503050a02090c0f090108061f030e151015 63
    0x34000000c10450806810342d0080906405c001c0400d045940c0008409000010307191045160802c20080312054400241161040140c1041040c003001000c200035841560403d00c118807600c0c00c501a510a640040b030f040380100d00b8800f90728002d5800242c83d50080360705848035082d41504810884440a002901040551921440101c1582d4144180003582d4800038007007038180d0320114094402d42e1a0f40008041085040000000100344042c0c4401000801d0f4043c0c008a0f141c20840c0c24200395042004a8099140182407071b41041d4400b40c1100101c079070501150761007081001c1c880c501d0010490141e042041414551400d42e40000d1b40b040d0300500014520030b407904404440c2500f60030440e0a60700c1340d8228415840c0c4205e15543c0b0102081450303141c120304603c0d80d4107600900a4507410f005d59440864010b50392030b00c01c0424580f200f01c0400c15524012001001341c442602211810300034001540807440d2011505403140ea824040105214070b0034001d140c614460661401c01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 898175332 1250 898174082 898174087
    0x20f01120609230f010b032422060906180b0d0b0c130806100603181e020a050f2d03030414030d032d0e01021306270b07030302 56
    0x2c0a8401d071103408500352600201d000d0710007540884990455000e00701d00307a03d00e0004010400300140c0c5c0101c9901100800400e20010012081400b0005908003141d6215040003441c1203a001800c40001c0308900d0f00b2414071a86a541e1480c0742114420302616500c9403207060711102000003500035450086016081203220b0502d61101005440d098403030a001031000101c14021442c5070402c4000703070418201422540c140362001c13840e10941031080c0c5040c19181e02080707002407400503020a03c0ea41041082840c8070030f07032440120094070721108030310030741041d00040b406041513064404030000282400140908040c0c007035010703410014801c46078441c000f940400d240c8060015000810072892403000100d0f02200305420484001003c0d4105817800710409185448840300d0701041100741d1601858081d02c0a43d480070b0401420030200700c2d0300000d11141e03100541d100c148101d92696a40e0f10301c21320406400c60b0f071860364100d1031042401d0003c040c0000c244801c001c105040c400c2c00c0051 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 898176582 1250 898175332 898175339
    0xf051207120b10060e010f0f02011803020304150503010f030b040c151707050901142d0702030717071406070203060703200a08011205030c0a051b0d020f011206 70
    0x18500e4184100c2d1044040720500107440400d0004001414050400d003496800d941c00080051040007641c40801c5044210030201600070b51041101440ea035240070400c0c8454140070350780c0d5209100c1c549a8958180c47c965540d440b030400d0300e041c0e0f00c20b1840d83c400380e0f2440e01d440001100c0584191882d0960050001d414548080004bc0c05d804584910701c01501c41c10318070440450060541c0d0901508100d0045641c1c9d0060780d240c02034078426501500c4e810125072079841a040c810042004440055000c01c1d10759502c40681403140c402c6048454040e11101850011800c0141c04d1034181d02c00442030144280f191003802d80400060540f03801e1042e140c000920b458425074100d8086585c407902100c0c42101844400e40301c0100584039803901c110000d0082c41514140300da2055280316848100c00c000b420b00450311030724081d2044500b0604c05050454486c0180030142c01540107038824400701d400c24880355000c545d0002e04210340c078030380800155100741a04620043c5140d0303482011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 898177832 1250 898176582 898176599
    0x1303020f1501030506130503070b070e1005070501060b0a0c0b09011e020304050114330303120106030c020a0b041e0c0b070b0f010f031506030c0902220f051207 70
    0x440c01c428040700c440707225525608000f8181800948110b501d10580ea805e00c0c045a03000040382c0c40103a01c10300040c020790756814100c554040c00c1c3c071190f600c031202c10030001d1a0b6500c0809008140d005800822136591b0b5203c1d00c1c0703032501c24441806c010884800c4500003103141c50003a179600a1800001160381f080b4080443d410324000c40c0303102107103503010050005026003481948040384484003101c486007403400d8694049150303105800c2c2c84014002203520410810b81d8000c0d14110050304403600e03152006480f4614800c24012030000a150001001c002440060300b03400340c0d60014040c1865441d217880310031920301d1082544503165130a005000000b07911a0a420023071080c00f5241d910341c00e040c58400840030000e4015603110000a005110701d0750b5030020641140e51201480001105110004001d480d05500240c40b4807031085c00002c01c04a103400a10a40807d0081640380100c160100707200d10149010360041200b04080600c542d0034210000c241705c811140444082681d100c0b030a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 898179082 1250 898177832 898177843
    0xe01051012060e100305010c0905090c180904111804080d0b0f0a150906050c07060e1206070c0c09020304120f050d02030411010e03030a0203070308040c0e0403181d1303020f 76
    0xd18144c2c044a20200203200c13080c0311f150400d10040c0740520b012031030000014851600030302040312400000580b00c1615000b820143c00c103d0018002040341c0c0341c581800180302007502c5100740107229102c49261810146a4028031407030380114690309000c074a0310900f00401d01d9820391500400c0301c0c02045600d40d502042c1000a2840103803100f55015171000050011307105510160510005210060300180e0101d501c5040d2041454142d40124819000070303003500c01210076280e0360017008140205142d111204001c124040c0000c50b9005548030301001c1248070441c0c0142614690883d0240d4440c0f294409010442c0a4541141007503100906042280d00a54040f9158410402c809605507040001c40041d0b010071406903083c8405004040d489100b502c2009040004c0d2304001000c1142440d6900c010b000c2c1c148047c1e10b14502450b0151540e4200d14080103007251204c0006600130301c2c0500c4071051f480c010044003047c5c6407141038071040d903801c0c0c2c000c0301176000d20054011070036010440b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 898180332 1250 898179082 898179091
    0x1017060106030605040905030715060f08010506031c0806010f110304090e06060a0614031b12061201020406020c0d150e0615040c08060f04110c010e070e01051012060e 73
    0x280126524000d006001c43c0c1c6654041c0c3e01607801d240c080404100c020055134001131700300e44461040c0a14803102401441d040c0c1100c0b074514900b010101e0000e070150300c843e125090075400c454100008444140d542c05d950b032042c1d400910301900084155110703100110b0a12800c1c100f051555900d020004c1c110b400941080400640e04e08014000d8801044040d0304001c080d10380110b0b990410100070020030a100c1c4a480c51030b0700201050150008901d1001140c44503640140c6030f0303030b1828007507000882c1a251140308103103c10030710940c1c5030107208030341c12900c10350001c04003404454240403c4803050281500e070150f0081c5040307105001c6000f00d00440d4080b0003e0140381c5400e04403100500c5440000a000341d181098190a941d0809003450700907108a8401c2d4005009600040242c100d038041080c1107080400c10110f2420150030441160000405981c241511a82c906c40451070900c100c1d0340c84020407041649032402550045502800c0007800302d003c44c0c44417801c4001900944 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 898181582 1250 898180332 898180379
    0x924090b0c150f0c0703140705160305010b0a050a090f0b040606020a14031903050a0207020a060216081204030615090c0801150302132303060408120721020310 70
    0x428030b1410750302c000d19459010081400144850a00036110f03415401500b01c0202408200303d8070307082c200d10030400d4448856000040b600003d0010340c4001c442ca440d88030440f00c0f50f00f00145000a881d080e05520f09440c009080071204513b09484031001c2c042da8480c031100599620b0000c00e40b51114001c11020340400e80003411504421302c1e01c011038620740e8901c40c032640c0092200149144d604004614041751515010510761580b8461074024415008001e6000c040b40300f000a650b5008038a84009038186078500e8110b43e92419116203404030a86552107201c0c0800c810b05c006001e42c0d20480c1440b00d07400b0a01c50b11500e80d203580c822282103682501c003162500c00100104199034401d8845503140f4501076042c0325443c110042c045855000710f0b840400707000c14008081d40113090002201c1001002c4641c9828103007001049503110002e1050f80c1e9045000294016004a0142c804d84080d209400c0c5000502c6104000a41001e010440064982200003c8801006000803180503503032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 898182832 1250 898181582 898181593
    0x60d02041d06101d150c01090b011e050306040816050609070306050709030506060120030f0d060504020903070608130b0702030a080603120a05130b04081c0924090b0c 73
    0x2008201480741e1009000341045108401114508035468903030100ba2401d8176082e140c1c184e090031030305941c094443d00040640c17030580018180300c0181031070380c100c40c040c260180320390312400300341000e80c81c10340141c542552080d4042000281c5600003801049040c00140e14101003e03036445003031840c03d807503031000780e801a9401c0c03051051501c6041e40240560903c803203503902c0e56458584035940140300c24180f0900f8142c40e01200c1d00800c0d100d0120301200f05895664020a021400680083e0043e41680c0d140c404e020030681014400c40380000c40c02001410320920b801d01c120f508840092144561003280070000000407000c66086010342d5039078025540b180380c1070400030003103107008010a01ca0b512080c2d80c60003001e103040489844803000c1c80d0441e40c40281c0a2001c007040d442d5807045452000004000402030741c04103074820142d000000d080c0102d582c04104442000c500c2c000e101410034580d890709010081c90f030301070f2254031441c10309402d6280e0750100720b51203403c9100ba00b4441d0300708 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 898184082 1250 898182832 898182841
    0x1d0a030f0c0e06041b1d06030a0903090902070507150c120c150626030c06010b031b0a050d09020f0a061833201b0f030c060d02041d 58
    0x1220ba803507015070192010890308444c0740100f804044038150349030030710403004098400f041e640000070f40e0691020745100d41d0b078100080303450014000c041090307002030050f12000c902c0c95003d00803584800d802000074030f90a400e04640341c5c44a1070524011040c4501d000d00b5a00083c0f4443c0d0f806229505a04d90305d4030f00e5000d08001d40341c0c040b180b0031742c66600c4c40c101c800e010301c00144001e000500c8401c0007480034111142c0300513185100d142c07001c20492198100000d0904881070003188903024490306c21103407006100c8a10128011502114007150b0180701645084844c0da10142c40b1900082108803107800c03100c04504500b41e150820000580440789010300b2108c0254004020b11646009462814089207601d403115102038540c12043c00e018091a003c911030144c1400100b481d641980c494103180d8111036680924980d088030302e4801a41051441c9401042a91020340c0600603080c61580a03081085981c031203c100400d9643c00e010118402500514500013504955040e040707030f082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 898185332 1250 898184082 898184099
    0x5030907050f061303150f151a09031501050f060307080106050703120c09061416060b030313150e0f09040b090f01090305040f090923010216050c090c0a1d0a030f0c 72
    0x2000c0d03241010231b0901508101820720303c840141190140300101010343d43c2c103070022a8610513651690750522030300d4814502d1180502c0140d0481e40121604000c6030052002c1c400c09000c00c4904030b02007111400104041c034056402404e18910070318021070f410002d0300c42030381120031904411000400ca80700c03c3c854590440310681c40150000c3c8a18203003000203c421246036001c2d00300034001d54903600003c2e000d4504009458400343d016000301e60075910b490400e1140c0046100b00350000c0e510b4000300900342001500042c50200141690849036100c2d200c40000d110050400c540ca84a41c4440840d03101c400c0c0b00b001c1402d07200f507032104c0d40c491400100324044101070f000800403038500300006001400e400161a5004804c2101190070016840c09a0080c0586000c0040d81d540b560114803c001003c00d00048035402207400700c10944920185404034068442118081001c40001406421044840401c001e00080804000d183c4940d12040a002045001c440080138640c0070700c950107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 898186582 1250 898185332 898185341
    0x14040f021302250c0f15030b04020909180a0c0803040e09010b010509010f031e1d070b0d020714030f03190509031605010207230d05030907050f06130315 67
    0x100040700c15030504030780082d10020303039a0306914460094084030140c8100041c005002004065000200341c0717490b0f440ca501003000440040e0280000e00d08031400d16140b6041c403da80d01c414020700700d201383c1d43d101040382070b40030101858025503202d254062000109030044d240c002d010440007550710b071480d020004259010142802502e81d0402d481c011540c3d9001c001d0741d0310900b007440c020412481c1340c0710950007003803030000030121100f00b855500c01a0080340c221903642d5440380740c8113025909042d070b40d81d21803215005078404028200101000811a41c001e81280d070b000350000d64102d0002c14956185034002e201094400308007004200b20760710041100145560070880a1109207002020192030b4420844590003001c1401c801000744003003503040c0c5100c00e90050301c0c1114504268040145400300050883e04d61103001ea12030034040c0306609072805414001c00030000b00d82000b080101515507100b031290055001e00c11801c4c154501c0c036a4400031406401904c00142d07140f040e01050300d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 898187832 1250 898186582 898186609
    0xb0a060302041706090a03080712110702010e0d030906140f03192d110c25080703020d170c03070c23060d0506030c040908030619050d0308090114040f02 67
    0xc0c1c005004005d84000086840e5411503410324000d8810343c1c4510301590303008210044040b00a05d0f103440d086034064801d00900c00b0b24003d03215a010b001e64901005610481d000b401400945134400802c4124011000b6000111124964a05110302e88002c2e0700103420031143c41000407040105043e0030b90551140710310f04150710b141c03003450003125400da04001414025070303160b45941c2c40b6807504208608054a4a11031040e05407400800c0c07417411100c00c40a40d02140e070040d60380030000102102d001a810303080360f6020f096090581c283e40c071901201e520050301e00c3c1c180d180c2084043c2d9004401e01c010045684071300300c000451800c15030303d03040c503907081c800b40210014403110302c02035079456100b601d0040c040b1500c0800d40356924400302c1c0c2080b001001e000d41150801103013508010500b009580326010944104440d180702030340740c514808092243c980c0000756800b002c0c02192003550941d900c80483c0c0004039007101e0f211a20942070714115030030f039940c0503142c00c0c0d9030071407070f000c42c0c0350400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 898189082 1250 898187832 898187879
    0x91201020c03120f061206010e0a060e0415050702030a0210021e1605010c0e0915010c08031608061903020105070501061a030121030e100c050a06051012110609040b0a06030204 77
    0x200003490340e2692047c0601403221141c0c010000503d200045402c0000a01030711081c080460605103400c00308121100c850511260404000800142c40082501c20744000395004000039903820100304000e61141c0c0c580c0c0b02e101c8034480044180c8040b84010100c0000052155014660b40e08025085600c0c06100da401c009800300c1100303496407020000398210749040e100c2110030000b50010ba40300411020b0007081c000c40030082280c003d01170010407003509200e031100d1006940e0101003000d002d014010040c80b04484010620165104001130b1060910800c000581b03142c880070002e07100b03d0907005000c4940000401481004c0401140b041829442c00e05184409180e58001e00b01d169110b0711140103400a00e003240a031f0b482403082ca4010758101c82620b80c444014241400601403c90342c40d021a000d00d40c00042808002d0074016016030401e01800040c04000b040043c4c0c0ea1111402650007034803030186802e10390354002e80308002c3c90140c40050355030385042e010929404012404140c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 898190332 1250 898189082 898189099
    0x31902120c0c1c0c03050105101202060712090b070c0501090603050402151e1206040e0d1403070e120c0a0b040305211909031106070305091201020c03120f06 69
    0x110310600003002542c2080032107641c0c3c582c1e07010420f004054811900050240072540d54000240702040d4841c0c0e001e900d84c3d42c03500c40c2c190b485117024261204c1c413900081d0032100c1084124003142c2c0c0c07200d980d0b101c041c031858590205070f0344603c2400070303800100c0280e814910000c0100015030700851048014072a500342408246050b40002e505400c41c244111100b65000601d081d581d581d450050a00c9418281f0817515100f51204902c1c0c0c5070401c95103e8052458807402c1420800c0000d40216200c1c0688e40381e0003600680d0201a856410117854241405562028008030343c1c0c5030000080e02d41c10f1000280100740364003040045044031a40000074890b000c010605c0071410204204101d1940081140107100300d903081101c240c841c16411000c1c82c007a00703101c0d00c0d0b060743c444114400c80e03000c1d0721413a4504120780100441403080203002400f2038002c20410348a802c1a4030003648c1600f52000050911054408241c20740e031005c4002040d401001d402c0124007529560000e80102081d6203041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 898191582 1250 898190332 898190347
    0x2105030702120708071a0304021201110f0c010b0d08181c050a170f070f080f0f0d0b0301140109050915090c1c0210080a09021c150c0806010e040e03190212 68
    0x3280d510003d00301078020121452b036007011445c01d40018078048484142c0c2595034030705101e49100780d00000b200d41495402c0c5400200107160030441080304c40e8000d5126440c4c1014460450610216091403d4100401c4a5a41315007000169400344031401180a402c054049180c08629030313040700f00e03c0307004d0790040c01403001c7c0300300320400d6604c20780d44a211030f04039400506141455025613803036140350180000780103001001c010050702860910034814860b02e02076104041c243e9031084140d00c1c10050080c01001800c5050700840c3d004141802542c1c0400500341000060708012903195034507500c48141062075090503081580345003040c00000700314584540c001840310134003090100410581001140350090a90b10030711039164000c2c24000700325200400100c03807540c1140203445040450303145100c00e80f043d01038098400e03c55550700360903a030784000640340065a41070943d000b5075940b000100c51f2400300000cac86c039040c2000f009c6c00c0312004110000e20303240d101c1440c41c400340390611201 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 898192832 1250 898191582 898191629
    0x506060102070f0911090301051003260d0207061b05040f060801080303040308101502150106030218040c0e06120105030c0109031101230d05150307210503070212070807 74
    0x103c1c150307100c4040109011044c0300d818801401251405a03255107840700b07208400500c402101c003180d100b0040e0700d20b2140359036082c0101c00c400f00c0c00341081800c1000200c0407815a5030080420714401e1200050f50010b43d151080302d40070044040010075400076041c010f006000058000a10301b80c03030070124a605000601c1d490340000b03400102407094000114803c40601c484200103480c1440344094904e0400100954940740e014805a5141410001045442c40b038005c0701d9526400403569030002e4005800e01000b400c11104910401c03003007514840680e074650004001b141102107100d106541031000b05814100d160084a050040180c0108001003800303100c00b1615800b42003880c480c0c5954418006111105120b548070080300040f2812561400d0780424003a0984070030803241d00864009042e0741d61414003030304581e00f82800242d6015408a1150215140f02d034044c1c0c3d081c210b081c1e011580045031405800401c0d00585400d203c468000c02403d40208241203001401a81d1020003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 898194082 1250 898192832 898192859
    0xc1b0a120201020a020d0f08030c130605190804151d06070c02130908070602070302030d0c090605041e0308161202010c1e0c140a4b05060c07050606010207 68
    0x3401401906e10240503c20100c600005d015046501c441c0d407840c0c82015034580340d1002c0314070901c80f1160036005c81c0c0d5511410581c2c1030f04084214002e18080101000d5a4074031006204450980c0c0c8004000d005a5a0f4005e00400c00058180f60440c0540e06501e01d0074078000501c61030403c00480b140c000036941c0c540307a08e80aa54507c2001a800543d03040c80141485803410140099000140e0132081550000081410b03c202040c1002003046404d004c51308010103200b2000024002e000a1181329200414021200007008200e845183d0700c1e40c07045419088422101c00c4803807244000018000c441d60040d940c1050b0348020404500d070240c5c0900521036400d42c0c24010046d01a041c452140039a101000c00c68000c035001c0f00e00d0711404800741d07481121210842d418420030240d03810160880303000c022070301d6445060890f04000e810f0355016101005e0b8000750740056000c100000f1039018050917010381c40306085155280030a0030311a207401c1011f09003d0465001c0300d070400046441404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 898195332 1250 898194082 898194103
    0xd140f010b0a0309080a1106160f050f0d150302011b0c0902070218090606180c180d0b01060305010609052706030f01150e09071512020c1b0a12020102 66
    0x40098454040d030604500800214400500d441781c0002c07541d140582012101c244c01c1d1040b0704482e0540e0310b02c80b001d0390700c81960000b038000c21190b404504083d8044c80280103584500c400090504582d5000e0106803031003481c4040c250324056506009559100055007941c8090415139940403200395280080300c1000d10400780700710381c0810340408669580503071001c400c5200700c840c00076040284490742c94840650301d15200b500000009489180803800311840340c40707c1d03099142419048100807102d809020703a070aa108510452420015440c020920b01034411685d00181542c180b0700098141c5a07641c00140c480e10b050319084401c5e04c002c0120102c52007810031140041d0711102c003c80d180c030007645150045035003480345c074180c00c03843c079500d00e4200c505c070f1005280641c54044d0603a4941c00103010b50f56a944156035a030003e41d0180307058204100b100700c401840c140d5440b060034180003804440243c0c110942c3c001d2000c1c1d01c2e101c00440040c050b459030035580c501c501c2c0d0012307580c0c619885 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 898196582 1250 898195332 898195349
    0xb0f19030c1e0306020a141216030b0d12140c0601090f06050904170c03072a081b030a0c0611010c02030936181504020d060e07080709020d140f01 64
    0x2c0c0d4104080e1080441f2025241060701880c2c44001981645040306e008807490b0200125010440300340910038020440f00720006002040e854490b80c544d00010350b1212903040901c0441c488044070040ca2500411071344541c1000b8005030b5062131000f60030764400c034500e6142c0c1800c010080c0300d031395905100c031a00158081601c0102c80040500c0207810b005291068625010205541d828411341c201a8401c1415003851511350100b840f6050700c40c400140254407003617218810302d80301c00700b0b1000f00c0455850001c0803070303840c02c034540d03602203801d440b540242000412132108014002e400b401402c80da48441d0000c1c42c240001000801d81c41030f0784416960200d520508084000c05001c0512607644a0410300a0141d00d07000080460400d030004003801c03244603c43c0b40d00051140800a2170190341d005041110840e0f498580e00c020745061003041daa240200500010f00d40d008011550041901c4440583c81c0c0c16141e40e00383c11601c4040300e035060964100d080082e1a41803030407040c103440c10034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 898197832 1250 898196582 898196587
    0xb040608070e1c11090c0306010f140327011416120c03050f010902090307030206030a0f0507080a1d1c09080d050315031c030b0f19030c1e030602 64
    0x480c04440c045182d00070990401d0030b503609010940c02e01a03103000704034020040482c08401d500284945002c040391600f83c0c18a083c404180c1643c8601c42c200010062454103011003128034544d0b0740164015102540d40c41a1484014101c01c18408001c041c005440020409110700005134110b02e18000c105007500391207400e9130b841c624014504d500014009030b00410a51060120240060200740c841038150010380b00001007a100300c2c000c540050f50054042c2c40342d54615424801c468001400703000c0c00d5038940010802c038580c035202d0613200344407560322569035060500080c000c030303200b1703c0320b8074500d00c4003810031454801c00140e1207000d250b05014181103510f0300e1108581340c040c25002407105008542d280709146a01402850080510201072080300c804802099a106803481321000000c1c80040006002c2e400385c0e0002c0f11b00c0d0400f03440102e0700c010300d42c00900a0b900800014400796614403082c4240a60203a420024201108090720301840031120380c60000500d00c001001d0700e400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 898199082 1250 898197832 898197841
    0x1803090e061909020c19150b040f1b03051003020f0f04020f0f0c070b070302060a09020319210f0824120d0e010f0504030213180506100f0b040608 64
    0x180c4110302d01c00e42022140c002c030191141c1100000e54081240c0304114440c0c41840c0030110b8400402c640840e52002080d0a041d0245915038080d010408081f5407003035940300000000c00450080250520b0750480032030541c6d025502c081d00312803014258000f00d942807001880140c454a002004015040354030290000803100020064821154042810200480da405200c100100504210004038050307075482030b111044502c003030042c12000340042e44000301080398440141d215084071030018056800780104d450181c06851400d000880b0f62942d003448007014042c84401c0300321b4100a0b80f4210301800c880e03450052103400058105414100081e42407a402440c44004449080c0e018041e0b00300b00800107071080e00e070744022400304085103400d25184819032003407402080007000381c2c8940d4203280c15902880000074070061440c106c039964200d01900d40c101c0e07050003c500d0b07125030024421450039021030401010320717510010050a03141c005000d541445000c5d94103581c103d1070854156601c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898200332 1250 898199082 898199089
    0x12030612030408070e070215010b0c0a080a02160f05010c0b0c09090c0405041a0901060e01120504061d01053c01080609210712140d09061803090e06 65
    0x4400d03100c414520000800003200107010600b03908844180c2c4c2c40501d00d42e141c00b002e90301c41c01d04030313102180f4040c02001804a062404060088044088106c80c0e114030680e032100116807103104030364003507404004010f14104498280b000503101c44164425070b2464031002030141401c206008205062103000180038108040c107a0310b580768010008400c50400540c24110b0307030701c81e008550260f07040484c1d8803045010300900181405c4054854070050b807900c40b040341d111080003500c80c104115541341c2c08040c086406194003617030092200050303445400d01c12094180341840e045140380d05103000c0100c0841d02c0300c6510200d01000302c803610050313204483c1c18070400710281040094000301c00045912800011040e20884444044400b01001610b229108010004000501160070000440020084e440c0b86101c6407183c00c3c030404203401007040c0307000f54111034a42d40d40e00c0c0e45d40c2180e1060200c40d000300d506502d144003940c040100701d518014407800709030080b020003204110109800b902e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 898201438 1106 898200332 898200349
    0x10909140f150606120c040f15051e070803042d02030a0210031401120302010501050f0f0907110a03090306061e06031a0418030206010611120306 64
    0x2107400049030b48090000c000c2074229000707001140c4505400040207014200c0708100a454505040001c6150800b41e07222440d40c042406019800e680c01800325005040303100041e8000341341d01180f03c40701d885071810040071240c00000308028841403407400014618102c0007400070106445044520110b81c4802951541207a5a83c0006192848100340e90081c142000725a110a40d658000068026032000200c0f500418103202010b6080c42441d0160404803201d241d841c1403c2c0c00314440050420000d80075148400208080c0c41c040d11908000c0ca540c0400c480000f0000d24008043d00082e1204440c1e6606289021038100f0100748a62100362503d02c8010b1001d2404400710302030022481034100348090701040b510662214000c81c03011980710409207800451500c0d009161201c164425810000f014044403a0110b001c2041d020a1116001180e12501c5101c0040c1440 = true := by decide +kernel

theorem cover : BRFrame.Cov 898021582 898201438 := by
  have h0 := BRFrame.cov_init 898021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 898021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 898021582 ≤ n) (h2 : n < 898201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
