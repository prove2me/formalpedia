-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3060
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:32:40.827245+00:00
-- url     : https://prove2.me/submissions/b3e8724e-6c04-48b4-88b4-6f735eeb068d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 550179856 ≤ n < 550359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 550181106 1250 550179856 550179869
    0x902120106020c0d0b060607030513060819020a1209020f0616020307060c080304080c030d05090321100306020309012309070803070b04080c070f0b09010e09010e07230a0306 76
    0x4115800f02241000c00d507400c003164001c45ca00103903441e0343d8107116030381d030011105408000c81881240d03a442c9107086400004c000c0c5550340762540c02c081c156540d940761003204a820144c41001951509600301d149540680c2d08200002104102d500204444681140981e41d0103000000c086100416071403002034071a009404894103140c85134410380b0b41c10310342c4002603c02c103024030000300002c60510040c80078003140d4007031782c2c10030a05130502429140d09417040d1405401c0810f06e0b61300d0547e000c880d10902c481c051000340303c5d82802d5400328142c00079400044c002540001c002200e422007500950040c0001010141071605c0c210000d500301001503440c0c0d56140213144000070074881c00420398842c0e5030000220b5410703440700c0d0760b5105140c5c84081184928014504001004194240301d40001d118000d642aa111000c8000502554120004910460580380140280c4540b4000c065004005080c105103401c04443d02c501e842810750701041d40d02d500011074090840d410342002045581c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 550182356 1250 550181106 550181113
    0x40f0206040909200a0b0c0a0519050d02010510090e01110a0e3d1b0507140a0803040e100b031302040c050901020c01140c030d0e1e0d050304020a090212010602 70
    0x618407009600c40c02c00c0c035442c0e4000e0030380344280f017121b16450060101d280300000700c42840d02c5696406040c0700c003c40c903042e92001c503c1155014030805001031000b44415100030065440c2960311001c000e0110302a0204040e82d070755121280301da0035030007000e55804210600f9160f150300310005000010f0741c04150300550b040c5282c0e01c080d030307516112000086005080161450071014143d884004a580c9030020420500b00c50254500d20300342140e0050301a8002e0b007400d500f090030380031050b0f0000a409005e080c01724800c00c01450080b0179202914a18201900181c4900030640c80a4110742c20141c068180003061246c1185c405401e4000540b0170755081c40041064101074a0350700904c3e0300940540c02ca0b4101082c1036119015160100d008005541d05142039406140d185400080d04201100da5aa110720040c83c003c10425088034091441064030691140007181c451100100b240140400031000c10304540c1e4982c00000640380d060011501d40e090514901d101d1482842850003500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 550183606 1250 550182356 550182383
    0x30a06060e0117010501030506130203040f0b160c0f03200f0d090518040606080d02030d140415050709210c050a0f12060e01050711060106020a03080a05040f0206040909 74
    0x14000c2c4142c83c2000409224a0b149a20b0301d4019070191130000c0c40e880c2d000c03140c00e8914108284610207103000e1401218200402d51051038802d03d0345c40050b060041c800d004005200c107043e449081c0290050380083d003420322111500d0700303448400200041d02e00d1f20000c107a280c00e6034a000112505100c0c1d60307000b190a01c04090006841d1410b1074011a50040c20404100e444241d00071405604223124410005000e955240805d050041d41101440140c200080340ea030f901701240240c620084070851050240e0505907140002804651100030309140c42e0340020321600e0041e4506002080024840c00507104500314040703081c0b11004042301e600102c03070700208050034a03414480c00e640581000d18411403c00329902182e0420800482c1d680c1d07250202c0500d610401e000b094000d1200307407143e520942040f03511900f0040705822180c115480440d0000103e0307030050b01d00c3d401070300701040002c0760707211030409201d00c0c520014041e42110300043c00003003024176644510140d0340210395014004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 550184856 1250 550183606 550183609
    0x3020f0307090603033f020901090506030c090f0603010510110a050a0f1e080f090607170415050310060c140703080417030c03031f09060e0130120212030a06060e 71
    0x142003044244801800c140d03003c140b1b02049600030800030005042600c007039a0f60340001a0107600450350468411000714451581e418004070002c80a030b02103c03407604541c1000c0200300ca20340d450750b000d810011440c44243c2c0a607002c8c01141c04c4d80f0307000015214061094141040010b404e03460803614a000ea80c014600344020b50343e1a400380740c0c0700700c0305c80c5043d40c41e000070101e236044407020316800306041040800082c5500281c170b0140660b09581610766261034504c075107440c0e98001120601c4010020003040b000c0300300c0c610081d00c3c42418101e00851352800c21903188040b861801d40c0394818440007105000c8840081c00490300340f2030300301402d0703003001c901903449000d09182d130392055000340049815004404d0301c1c030226400800204100300d40c1d9000c000180c1b00c55070321400c900b80b011401030060000d0104c200000194100f1181640070380b42602c034000c10120381c40038001e04100081c03100102c1c824030003c650403200d0b458094030390a0a146042c02804507226110115000445407100b9 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 550186106 1250 550184856 550184927
    0x50604080a11190213020408060907030b06031506041e0e061008030c03032a120f10050f120102090301060314100e0312042102241003020f030709060303 67
    0x1030140c1d410903c0100d01d00ca41c2400310310210782c03101400e015000e1201040207002085814030030001c00d401000c0c000e03d5400c0c0000e80f000003a01881c026000f074030500004071030311500e59800500c00d0702d00048450200c6042d0b4070300c0510030a0864074034200040540458000140903004010804d0343d1401c0a41d1140781c20303030741d01c030300340d50040d941d0400d0001459414000000203580c3c000015292401e01900d9502c001507440085010007a2980700d0a1140d5002035000d0683d010318051002e10503103082900082e60100640d4000d4800c000860341c680601c00b080d016188a5040a0020f020040e00c2c0e1074960070190442c1e081c0b0030f0314400c50030000d050000324090309801d0390240003c3d6182011802071014035183c018000e42d4520b50404101c0c8515000d41140d41480741140c0c00b4000d400204d003030124108000704284110060500c0900408103d640d602c2001c4940c1182c401c880c040c03071000864200b551a80c00505145e15045002042c03581100b2501000120402e1034038003c008000412003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 550187356 1250 550186106 550186123
    0x50609010209012a050303010b040e09010b0a1203030603170d0b06180111031303080307021c0e13060b31060804020906011107060e0103060f0503060604050c0403050604080a11 77
    0x40440c0d22221a4042d00e890541e6902c08204a00240c43d24540717456142d503000fa0b100411b070200010342088444002c00c0415004a858802440401040c0000600710344050103007144210815083c101014041d81c4207000650303109035801c03c0700c05074156000d041d803c11002c2010752414a030030601d45281c0502100d0305842c040c01c0900e0195070b180300441b030181c12580f03104400d11040281c1ea610f502611300400065108000c03030756030f0303180407000282840c00d072038889400c001c1542c1112101c2c1e50448224014840148c2c5d501c070700700001e03020320409040726034056104260006400c55216508103c0080c440036200f5400d406c2c03202545408200004500c100e2001440a5010500602d441c541c46500608140341c07040e401401e0740a401d0034001c0590002d0040780f484a045d480650305402031100412040102845139450305020980320540146214803c0740d0b00e40000320030101000c1542c0145401a0881d42280f5140c50110b26a500107402600800e51840210010500000381d410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 550188606 1250 550187356 550187359
    0xe0c0d0b120714060f070b0408040911130602190b220c08070501090806070807050903061006020c040228050c030406080a050a0507050d15050d050a0221071406120112050609010209 79
    0x502d04041b585844042d01c50141c0210740303042042000050b14052805064103408450714110742d26160362600d180303820302c40e900c45000d54100c4420107002c101100d43c4500e030a60844038070296540d68414074130001c00070507003182c80c030340c1c400f20390b00c00b03220002a240c001e540c2e10a08030340007035468000551750b640c61407240d419168440710000f214180319612807a000b1010382406420505204e0001c0d040c28001c60b200c3c400c900640c2030801085a0400503099458020b0f601149007500d140c0100c4000382c0c849103641142d0b900b030001d1224080c0304c2c6007101c2201031268183c03601c941d11108004c00603d400c0d601c00c0b1009082001084e004881813180e54003d141c19140d15140c03001007990703200034043c13458074141140b10384880007031180c41d0341c4000089584280060004040300c1d10400851103201d610608a0303c0061203031045000001485605658a150600042960318000514603203d945005560111346200000f03203c843d58652200062007a02603465954031046000d00f00e00032003074180d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 550189856 1250 550188606 550188637
    0x5190f08121b01090b0405031306081e090a060e1e03041203210f090501110306091801020418050103060b090c03150607020603160f03060e0c0d0b12071406 68
    0x2c2c0d0b1800d2680180c01c4044100002080c1c4005684904c007509801312000d4a8070780001aa1810240109030600003511541c10074402c1401c0c00074104406800c421090380300f12450401151990b9420401d03407940c07030fa000c030040c0b014070240d05132aa1150380500c80e585010500d401c15054544012040d5815210f032900d80c85251406c68400b10b070481515225000c288048111159003a0a180211902100b241c007010482054501c4c0403400c5400c4c581c10288054030038400d01003d03580b600300881d0448aa1049a01d900703140000c0140281704603800030800d1500348140c1c90804086030001c9040342c1c000c42080212402480510480090840340d040c40d0b158200006403845000405050805902400300c03801c0070050307408130710a58800c0d1901200c8000c480400c990482c4d111241c0040c078030603444d0500c00745107030440f0003070002d4014106413811500072840a003024901d500111080100130500d403e418100054941c0f111080d008900700c100081d40038007000c0c1000c0b421100e9051408400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 550191106 1250 550189856 550189867
    0x90303030a0b190e150402040b030f0601020f010c0c0b06010305040302060c0c15010815060612011814040b0f090106050a1503091205030604060e06130f0605190f0812 73
    0x41e0006102084455a0200305070311240541c02100b580c6901903c1c42e0340066409003030600095070030080c400e40c294859401080144265030700d01050300c1d00b101d40395100b010207490b81070060341041901e40881ca681d61a1903241c5c2e80596000708c4211000f401031801f9400b40d00d03100c00440c02c1d68000c4030b014000d60320410100c1e0700d0720400b8004203141d44801080e07030203140d1103265001003442c1c01c1e032000034030798000d052001840c890800510307007007441203406620300840d0100d161080e8105101c1d10000c0f2040f400e040200c400150840755400c40c1c40990f08151703180900c0d218001d50b0703041e40c0311000c1501038000945045014401c4c8000d40c2c0c1c0c02464401c20311710f44140222818a240441c40c101a00c039281c9400181d180001e4144102c440d4031008d0f101c1c0351007024041100d1041d40034402c50040c800601140f510b6090342501c0b6450840c002103807000701441184060101540441d410481d2103090140a002c510240c006982d07841071102c2c0440c3c0e03104526592006035440c0507408403000c009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 550192356 1250 550191106 550191121
    0x40f120e0d0f0314070c05090601031b0c03121131031103100e0706030e0a02101d0909010e010513032111040b070203010c03060614210408090108090309030303 70
    0x24200300501c00d10380204d400c0100c510942c015005040100c0e00607a00741c5041c000b03441d0451a103030b03000f142032038104032054204851808010201d041203003400381941c400e030107052080d43d5890132100c1c071035400c1c03007201c0851a07000080e80c0501c1c5480c0324540b400040c400c10030007412060646107121440e003080a130440d1200f41a0b00c26122803164103100d010401c1300040d4581c02405c480301c2c0141c1c0a04501d62a0203406000e4940741100c00003c0d0304103032480c0c40140d61700f0010314142000341c90305010125884494440c1c0c00c1d042c01001d5484643c1008000400c281500f103082e008100f84002d002d6510341000f108491400d8500042c0890b410010102c1100e0542e1280c1000100117640800c8041c66200e4400c203d500503001160300c030303000080c0d1000b5400c09018984d841c2c0e03007904d01009802d1400800501102e128150914080300000b20959010b041e8003900300080012070052507541014031308490b171580725000d0b44d03001c140800c000440b68030011096036110540900039500c0d50360b5515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 550193606 1250 550192356 550192373
    0x14101805180a1d03180d050604060905070f08070e09010f05040b1522020c240406061401090302100504050415030c0e0f040308071403130302070515071203060e040f120e0d 75
    0x10a8110406d50010804610304011941c0035901481c40021142040c1c1010760512003140c03ca10000c1c200c105080142050002c0d0f0402151031940c0f0384040e58403100d40041c090054074401070411424079050109201c0c4071060240030b000f80500c52260b0616800500201320b00c2c09030108140f540c03001100e46c00f051180c0092000c200a08140d60b2980e40b00c0d94880100001401c01004102140042100300304440c46030070042c00042415456001c40000005c0c809490790100902039110b44ca2891050780c05007080c1c40107400d00030710521807414010341341c0c2d980196511096580c024040da0002d004444e082c4000c2c01500019941c907800d40e00c0d600c05540400c3c02800d00c6040080f80382d8403a0065000001440c020340d4009040c060442050600a1410456400903449400034440c41645036082c2d000302d0715496403000c1002c03208000d918040d00207121560045001e0484c8204210402520b404000c0c83ca03449010200181c41910400319041d450001809410400c0001b038200402c0c60300 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 550194856 1250 550193606 550193647
    0x30503040605100806010303050c060f160c1b14150406021506190602010b19060507060905010e031b06100b040e130818030714101805180a1d03 63
    0x2d05103c561560b40e0f071025417815409a2050b0b0014030049592030440d101886015003003849409600400d052001074040c0c6000e00000350b805014203000e00d002001009860f00f084041c501c1d0901551503510f00d5040040e8070401880c92290200516003d400103805046d2401c0d40c030b13542c0c0107082d140e1f10644692005034020b031400d540002510010440315030000103420152460307a002003400314514080c0300130001c2603440808810040d030018000c1d690702030252489144c03c40700c046503000c4581005030040071240c0d2002d2040c000052900000d80c9690000110280d80c00122401982c0d18142d400303000c0281d0042d48680c00c400c11003000320203011700d022604204044018404c2e031516030b036490705540c004101204596041030200d982442d007803042d034005020344124229060b45590006180110fa000340701e00b480008400c1004044280706044007500d005805120340030300c2d0b103803800f4008104076a20701c6158101020340320741c40c11260314403a000c44c140d802182001501c404010440d0800e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 550196106 1250 550194856 550194871
    0x131b142805040b030c1b012a09080d36030201031a090106090503010c0203090f0105072d0b1503070303110114010e010812070308070327050c0102010612030503040605 73
    0x1e000203d0710383d1a607002107000300c00301c1a0381c41c0d0320b860340c0789924502040d01103e4825640345c59008070041c860610009201000000000121204160203032207022154005c88958840c660000c078620f50004081014001488807140424074407140c503002c0241c0401d650000002c6203c0c0810042d4082d0b04002160240b0394481581d00c4141e1000c0382408409a21200000301031002c10481820284181c1c003400aa03480614a00b14040010035926440d040380581000400200030050016041c0d444038040d03107030400c0900c1d901540c10151408070315000c1c140c034003020304004160102ca500d14461a48034000d00544002459510705880200f00600100e19954071859044c040c50310390220306010b0003903140010350319410280694540181360780c10802c0d0040811018000c2600940007030761128442c0360205025165221a560101c0304030281001406541d0048007080300c08100c603414000c0a1b4000c11150b0f84d586a010086170007000c0c0980440d00420218011850641046601404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 550197356 1250 550196106 550196117
    0x106051c0f0308270d030c0f05030415060308030c0309010b0d050c040f020409060f080d020705011409010c140a2001120e1c1211040e06040506131b1428 67
    0x32240e01303045000d0000d6204060390b0800740e5421841e82e00b500ca60703144501c035450100c1c90b0350002200030b801444080c0c406401001d0028003080007a0058011801959000720f49503124200341d0031100180c0c01c1655510031035400c100844445044c07401020001c0e45c0c110006003918210881803100601103460034844880e0200404a45c0f0503080c01100010460301291480b40c618000e4014105142c9005003803c54004a80030071035613911903401190a4030751146295100729400051311415070700c2800400401c05541c85070b18240e000310701030810500407582c062240984544c1e06100e0409044060301003008003141c0c06854089a01041c9011017100c00c90b142c9041a80400b424004c00002610000d425a582c081e0143c400303004200d401005203c0d40e505081c20000002c003640d100404844c003850340c8400040044d6500141c5a05403d21020200311100540562240c0c03144900c070f440f00030540d2002d80f4111415840201e038169005035400c0381c1d90300320350a03441080004800c0308004001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 550198606 1250 550197356 550197391
    0x70803130203120c06010b0307020d210f02120702060127240305070603060308071103030d050a0507020d0e0f09071202030118050115081603021b0106051c0f0308 71
    0x31010440703800c00d19444107200d521340040382503103440c03d1416002402020014820b21034181d40002da4205880c1c86820411303102c500da081140328449070925680405800e24800401c1002d081e402041c6403901d02050700d500d03595204041e6541c3c1300070710030000d450313000d01202c004100e40c096a0610400f010000446d080803400c0708980302c41c0e800207404440c2e0140050403c1041000c000060003089242824400c045c0b4640307507a011409480b0000d86000d030280030700702c10340c0d90a00459031980c0f001c0b0b00c20410f504014000d60001d02040310802c002d88a420303801d0385824000d5602c0114201c0007840710f0400d80d4000306012a00501801e01418808100d85011810400e800514060506041c0d5190b240b084006c0f004281c54060b8071010f010302c00c1220b56114594080c50a990081d40c07042003940b0380e0400c5504500078410255034040003407510a00c05410380b810b400c440300710381c000c0b100324059240c080b20002d40404550740041c800c1d00c4000c083c1d00007070700820f19079a100400d091030919a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 550199856 1250 550198606 550198609
    0x100e0c0c030c060a05010806040807030507060b0306041208062b06090213090201031b0c03140904060b070501050604022706120103141c360608180a0201050708031302 73
    0x540016501100c0c82c0c0000f4100241d040d058480d840c01011140000c001c90f040a454035601e9110310074000d0f0410500103081000e0058070307003215600c0e140c00b030101c03461450281403481d890718408002c00005160080400c842d80b90040302c01020f541060f003221008900045180c140304e0582034111400303603e502c3d078400540d940662117001c1e6007030a03d000c0f640340180d02c00181211481c094100d1032540300104d0888459001e50300343c4003542c0c1400d2400c00d03840d0300e611a5005000b0b000500e80d00c00e00703080b00441c0d0900c0c41009030041c248250000d101c5c5449100c2040700340c3c082d1a12045201c0350724840382200900b0004664169480a44101d14001e04820201c41d003e0b400d070001d032490703081c040300d40c80448010414805200200c00201d806500d90201c000c024080350340f10100d4030703002500700c900109a0043c041910447c1c407040794610b5552000050818074041314000102070008210300072412000c118856040c2c0d050b5200c1e480c005159560b03140f00c1e000984012600a00f544824005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 550201106 1250 550199856 550199863
    0x4060c030501211412130b12070806010903050f0102130504020313081312060504020117040206160804090635151513020409110c07120212060a091a100e0c0c 69
    0x1c032884105c503030310002d00341d10014510700d40e1301014000504002e000c25040d0790078281030b080000351500da0b03080d44031140100d95031486600040c184e40100083c01207510415401080042e184200d503480c00c940d51000c0004038001110300c00c896803140c00901d00010a89001461810a0b1010040070280c580361940d91419000c6000c0f00c2043e5580d0030301055681101c20881d20341d40b0603450380b103d0710709a80400c1c51406145641d070b0191080e100703108200020b42c02900c3c05041c034003000f00140d640d50102002a5511098144460004001c0c3d05c80300e2014030003030021440c11840200840d4211080d00340e608140145219800722460001c4c90496031127103c07940c8126421040961594101700c1d2a1003204c40c00510040d0713513a030400201000040120b42d030300071034000b11807104000405001045050b2121181000d46006005c20080c0410f115071002c15618069400000c03504640b0034060b0f00f003030042d101d12405204180040100b844242c15140d0300800b008002424040380844a07840c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 550202356 1250 550201106 550201123
    0x1a0f03190311070b0a0e03061e0a02160503030105040b01050f070308060105091806011d09041511040e0709050d08031501090918020f041107061104051804060c0305012114 75
    0x240c010b0002001c200b0682d008040f01391030031003100075203082c0c00e0405a48421401c16000d0110b02718040c1c1c0083c0146045c0e50586000780c0c44441595100b00c100d19086840b82d02c24090148201d207401c0e054051540314200b503450b9411062515460010f46071000d86500384020030746410084200800d2039592100322144064a03c1c0b16000300490038036000140000d0302011f00180c50b403041d00040e001c0c0340d07120024190070a8101c0ba452460740d046000c928041c1403585048042044001000114514002c001038800c0025994071165162150108005941c040034064120207060002c00c1d82001b084440b031010107014104080d58035540d084901c1030b500d4440340c1e1050b00a60f20149001e40c2400c000f0282c0354141220200010180280314080c0c034090140041c001075a1200000300710100d071400c681c05810002c190910310815040340c520a9001181c3c07c45809081022140d00d0310300a00546040c3e0381e10701c0c0e101c3c00d104140c10a07031840d170b40c11490aa42e200c6400150083d000001e016010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 550203606 1250 550202356 550202369
    0x1005131d0a050708070c021935030304020a060e210304140604061e0c0c1403101b05070302010f0203150102210414040b040507031a0f0319031107 64
    0x118074500000d035201110700003003140c810301410900701324115510002000007030303504031003044000d0040300070405201350039084964003401440c01100040b0403001e030341000d150700d80f4030109828010028245c4038001550000d410018004051260301d00a032000880721030060014441d4a0000e008103c05907410041c00081d900001010b001078411100b040040c00802da59803440d261422a006245200b0360000d40000540086d1050003540300e0100c140b2840d402c10b04c3d2103034007500c034045032640380d007403a034090310900c0381e60800c20781c2d103083e40240000e51000211000320319800b0b0100703442c5507120103004c404556030b401704078412000c144051070103001d0140d00041100382c000f002900d4108211a1840c1c0d9601c40b0241d0240410f0b01c0c0c00702c9098900100803446820a0384000c03d02405044101c1a801801c10f41041051a0301d40c0c048030440d4050740614000001d4481400042c3d14030349180c07600340e007185c042d0341504040c1019031141e992080c07410000c0103000c960014201180340e045134 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 550204856 1250 550203606 550203659
    0xd0c030507111f2f030406050901120c020309090a091a130b150a1707050f040902120c130c20250305060c0a0203030a0b030f0a0c0e1005100513 63
    0x116400180c04e000d016103c540001c0a00940c104c40c50055502c0c0100e204550400c080041d19140c07503481503412101540445105000340d5540120180d100d4100b40141806018418002074644049004135000b09800c00814411001c40307c0c000100740c0801041088580921201c0c400098407502c5941d01c240d030161000e44406008004105410401d41c1c0b0040c2c0030244900780321000c402c0406c400f01150b004845c2428039020000205000d40754101029610101c0540843d00b003003404102c07005000021940d890300198031080100803500b40d10329820005505000b0481078030500c5034001c41440e94102214500341140141058006420400c1d2104252484080040181c10010385070082038100340709080c440e002600955a0100801c1985004d03142c01d040c3e540f94030b00303102090800130000b003a5811110142047d00421045104211840c20a8000507901c0d42c11141441c0503240010304070036071902d0003c0220f4954010320845807101d14628000195003603c860303910100d605404c0c01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 550206106 1250 550204856 550204877
    0xa0b0418020103151802130e091c022109011101110a030f0603080a090303080603030a1b150501270e1e120315090a06141011010e0a050d0c030507111f 66
    0xc144400b8050740700235050310740c14081c01403880022680d072402c0000c8002101d4903440c5032a0491520000000105425004a000b4602d107100032004054000f000c1e02d80082d0b901a045400d401c8484056544131042028020821102c2c4250002a100c0d02d4400c004581e06460b038071540c40960000a1080110303030078200400405401a0391240c1c0700304110003840c2071048031a000383c2406148100414401c07180c003c117004101600303074003075800f100918040006684807104080e0b90506a42d0540c040019445480c4c02d03410140181c40600084002400360581d8481000345511881c0304488003a001c0c504041c480740710714034082c41c4110a41d20b041c80081c0b010300c080c8181004080c21100045041510502082d550001c005902050590300700003040001281111100c490304680c110030350804811600d000400201030008501407000d40d940300040f40800d0b0f9070005100e0004001c510203024010106548003100c1c00712000143c14502d01550900c078107144d42601c00c1030180850b0104c0d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 550207356 1250 550206106 550206127
    0xc050f0606060a052208061e010f06050a03020c060a0e0f03042105070e070804020a0914070509030a050601030c030b0c0c0619060e0a15080123180303040b0a0b0418020103151802 78
    0x12208c010103800c81d0a0075254140003020180649501a6000b44072000520504082c46a4116072204a032002506d1060078a9020000a0800c4122509491048090207811031901004540446502446a1840c840040c1200f0703d81c400390841600c06008681c00040c1c90300d01d40f244076208002c20355850f6884d29051041140500d00d9400691082e40340030021000551840c0f1035031340140c0c1500304030f40c0f91010380340001e113044035102c4002d20780e0240c2030001003008280078800056130304c00c80703010700d06a48508500c055030144800d08030380b652050340422001c0b192240090045030004002040d6075450b101d020f000040103075445844079071794201e49046d400d0b0504e840006021000c0083c07000c05c03d601c040c10b405107901560b40c030800a401010412044d800109222400d07961016a034503440c00d030511550000e01110b0380c402160030400c0785403036854544150158144050003028040e190341d001180100100119441e40d00d0100102103003408481c9034820807840810001b59a6000940 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 550208606 1250 550207356 550207381
    0x305090a060c0305030a0f020f04060206060913030c0b06040f06060e010207090e0d05030915040b0403020c0a03020105030a051b040f03050c030a110d050309040c0c050f0606060a05220806 82
    0xa000c4810440d49051a000007548102140d810a201c44008200f40b1f0000322464000e201e220700c40b100810000038002189900801c0031445007a044a40703c507590f50344a545113490700660b400600040304104400001485071101c1c03070b00503502400000700004103c2200044900580003080850f140e090500784540e41080160082c00342039009215030b60800d10406c0c2d03552442c642c1001171000101c0003036a01c0204009058004031071043c0600c083c01e003800c1110440030103031019401401800400030f0541003410142d41117a5043e500c00380340d40c1c1d50f02180b6004050180120402030704452072140803205203c0034001408600700030346410317469864528901840c245e1143d0181d048540d40201144120300c50b9821580d0070358045114010710301d01541944640040d0583c031501d440709090603150b0100c0c2106c40a84180e0444130140c0d1986a6513554203811902076500090030440004a04d00c6140540305c40c248440c01600036126550349121a00110b07006406a0303480a13041041401954 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 550209856 1250 550208606 550208609
    0x203090a0e0412022e1b0512160906080a0b15041e14040b0d150b040c02010e060c0a0c020a080d03050705040b161109100f05030f031209070e040305090a 67
    0x1400240009200c20340c908042e0842c20303400c45079a1070305024a81800b00146c0210084040049030141e13008480240a011508070300c6205a1030308500000034100740300700d04030383d0040c8855140c80d990a490704004450180004101d009003503254074442c242500d44e100803c0c0b200718951400341e10f55003001601d5101c501c802c18401040c04034034030308101c00d01e1441d03040001c0f4a802e0f5004180d8400c02c1002c96545038500700024010b62410402500c1910954482079407940212407c1c00668071224040f4280c4554002450170754000d1008918040d00c400e00600d11207880307041c400e201c04400d0300040d4450440340d2016042d5000818120145a80751090301d620040e1800c0c018146800c08441c1e0882e4091f079801c010001c2000781c0484184446413891640c203400040001c0500c0c908001c600521102520405000c0e02c0003040c00f040c6450042207200c03c1c42c816030700a5040c80d005a500c81c0341c054000e0009000c60080c070001080c104c000f03951443c0b06a020752101c540c3c812103070092200344140c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 550211106 1250 550209856 550209893
    0x31506060816050705060c031e04201201020d14060a08030d09060f0203160e221e020a09060e0603010f09020a0216142d09070203090a0e04 61
    0x40400a1180c250031008254100002009107403040081e10070a40380d070b1082e100e020b4900c1c441c0104005201c1c1100c40114030540c0e94904007041d240044036551450344007910b00074050700740840c4402c04151800111a8521402030005c2a1b1618034000503003240d200144010b80c4644800521000b035542c1c020b0309804c02070649007403410918004200380c503409008001641592100080c0003404810b03000a007010340c08a00456480c1820040100042da0800c402408128200c41c0320741c207850200c0810141451082119500d07198141c0c212004040b0003260241c12a41204102982144c51010b0600e2040d0303900c070500c86030705048015042c1c0320751300c2090384151020001440052420b11004049800c06071016032501c4d105042030f400c2020f404030f001c213400342d010b4000409016141d42000a05401d446c4082108180381d82d07100070030004845481c1d0750018100c0c2d0300d01c0d0300b042103d80f41d0044061060300c0c2403660003000503c6440c250303400b11040d601c4110501007842411245010880d03c0d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 550212356 1250 550211106 550211111
    0x31704140a050d1202030403170910031406060a0203040b12010e0a1e05090a050a03050d0e030f161b0806040309080c0102060103021e04050c0a02070f0f0e04030314040506010315 78
    0xd0308000403c0000c41d110001c2000f043c1801034840c8600030001e44024640c82130b03460383d8826481040303400350f4002c440304030301c20f161508120300d045010380304281d90822021210711440d41c420050110642c401c200031021440304000c0021210700d040701400c491105103007588600d5140001480f40d80d6009450598114646404103007488200248104255030204003c0b8a5a540540c01070510000c140301070241d005141c0d0b044c0800d5481001051103c4994400f00b0001c0c9000201650381c0c0500c884140401104014441950a0100c603e1720494403c085062400d174005c041c0d119201580c0e444030015907c104140400c0541203007151000d08101c0008200c4500c10800003503507690107110290096010000080d041414003605019103034019105020b14204150760b0b0350a980400c50340b50040c0540240490150301c0303124a942100c42c0090f204040904102c4201861400a003048080c903980c3d003030303503151003105030b640310b1040340034002801d03456245050401010300c015582040451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 550213606 1250 550212356 550212359
    0xc030b030313030b0406060e13020a061404171614101b35070b13080a030e1f020307140309070e061c12021203100b090307031704140a 59
    0x460a0100110f0760000c18100c0b15440e181004001089540c12401891440f9000c10480009010200c0e02071417083d12401661590b40c54111030040c8040c83c007828800c0104400c1004468044c60054891300c3d14050320f84101c102a21440385603107e510107252a881c00f00012058a0503d41700c4283d410241010720580e5100b010192103003041c0100108180c44209112450a21700c940b8940b0999082112400324041c0c0030720700d05a500181c03000ca900307004c0c1d80005064010226501c43c00a503100d41d40074285811020154050710400d01c50344090300c20043e2640681c03c1c0c4a024038002020350344010b82c1c0382840c440003400c00250226041000408005000001000003192801c9540c200c02c05101610b170400051554000c1e40f049240034546d03d1f482c01c09000303440d08131180c0410706408440200300030305141c0c0b840340402c071400700e105440d60500f04815a01c3d84010129004020160b9001648035aa20702400701a0481c45072070b080e0100b0248401525120b0800c0704000403640c080304903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 550214856 1250 550213606 550213627
    0x3010e2b080601031a1c110f0d0f06090b13060509060403230d020c1c03110d09050a05060405100e0106080607051b030c0a1a0708040305090105070c08010c030b0303 72
    0x403030007034002c40c101591010206000c00350241c40b01c51104004160302c01c109441c090340b2582c42149501920110346c50f00c0382d0450341c5002810100840360103444441840c000b07840e000711007100030005491040e100c400b494009414242c44a108030304208074600c010002c0c1c00c0410403200010f101107640d604c044140030100303802c102420029144115202008010004410032a001c1c0c0c80c860f8100b070f400400d025243c944041108100320314441c0541030102446001141501e00c510780224141d40c08115050a0091315000002405d008104650480703d007562886d10303103001102c060b221078224101041c601d0056010f418102d0403040001c0c08014208464a611444003500ca0300c140180003600c41d480301a1a588140b002072442c007942d071217099042e94130361110f40b410320849150090510882d001e0034103004460107009640e5546841c0e503681d44d0141c6043e405108202c5c14400203100e030340009080564144058680d8400200300d02c808950b02800752507012100a01c41c1d0020300c400c2001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 550216106 1250 550214856 550214867
    0x17030a1415040509030d020708090316030c0b0f0c030a090e131709010e0604030602030103060b1f0806040e0709061d0903190306180203180d0219020f03010e2b 70
    0x582801c031000101c5488080c1e1300d51446c4210322040e20001d0011401200784641600584a0740c0419030644520071041d0100710141d40040c0001030403138003a000d00388140741e040c40144c81404034140e5414a85218108483c3c50f507001071329180009402004203018042400f03052075045080804030b00c00d21203880d92011061080300c0c01d241101140402c04c5003450380b007681119403040014150741c0d91140c890410201a41c000d02080d20b403541411a9902d282c00d0030b010072010380c030343c1c45040c0918060070401110480d40c06488540e02c0b50b05c170041841d40c070381d040c80b00000800c5940c00010f22589061002103503035442c0d0459910340301858080080b50440401142d056401915509104019801d0141c0080600d6001580301c0030000004000d01403c2d54003c0d401205c101c03880c0c6001c545034400700d036900e1404000d24030060300804001d10500084a54180c001440141002880200040030908461081d48011091f501002e0010f00a020a40c03010308030030202000080d06500d840006401c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 550217356 1250 550216106 550216141
    0x80304060c150605090f010317030601120203060a0918031e0c03140c010912031b0e010c0f0f0507050108130308070807030e152d0103140a17030a14 65
    0x71000102d405442c02404990164028010013003d81c1c83c40e040c0303640c0c54003000700d0034002107400b1001c20038107920a0607003505032403180704140e4410030b03200c59001034240a9040504400e400c4140b032500814060494040c000142d500c0000c01a0302d80541c3c10000e080494803501070a2442c0420107142203e64840c1c61b24124a400d4201280c1a400304030110025216150381032605e0f510b0300d40004104411210380500500b045c5e5420311a6050039840c01c82d40599200703120003c6204815520700650040b003010b0b440703602402c1e080030001c6d001d80fa11664003d401c40100d8031038200c41000c1c1300c03e40e000061160011140030080380f01341079075540074000740000b4091400f44544034000410442c42504209100d66102c070544d80c00003424100b104000c1c1e010303a1086045001c00702020b81030581002404070400386c0c003140b500c0d2a440e544948000e0302c940750b00d8040074040c5c9201d400100b0601d070914040240c9041c0712652720319060b0800d0341214034079030742d0602c000c00f264248980114104e94022 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 550218606 1250 550217356 550217363
    0x51302040213030b04050709110307021e1002130f1212030f11071b081b120a080f03070e0405010b120a0b120f06070206090d120612060f06080304060c 66
    0x42c2e4640300c0b54811003520465510042241103250208010820003081120031154a00b038140308120f070040d105400742c002240c2e4180103034413024203600710741114652a181d090400c4c0a441c0c0c4103084408040c01e03640f182a0710910803050f00020000189564080c0000742690b55103101ca40351103640e00b10f000f010213030340041050784076482641009896841403c0810707490382800d640c0d80d223916003501c1c20381c201c550b0f406803000200c20004000d8404181c0034090040e84c0c05100300e2507130190800c0b0188c0d920328515a098407840c01c255001614244c01071070710302d41d0841035903141d141030030000b41088010901c490140342494010814030004405580324401607030008035180c0d40c2c101e0020010030030441c10a03405000c0c000c91a6811401007a1090380b034404405840090b6503152040ea03460b40150f6034000c6660141c015805032501c103124500202a81d031001084280d40c0e10420110704003601c20598005580d0842c0009054051041c00c0c011706400020310b05052600b80043d1044904002c0034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 550219856 1250 550218606 550218611
    0x31b0810092c0c180403030b03011a0103091a0408032d0403080a14151306030309050d0507080709051609080c01050f120103140601080a171c050411100305130204 71
    0x400d000024401805110000f8100c4c0c882e00900082c24a4984001d590540210380340c000402ca5034201801030076003106580d08901200c052110044000b0000c10f241034a41c040081090350200340542c034214007440c0111030309512810a1940a0303d14200d00401c030b5001003011489401a001280c0944e5100d9010b041c00b0065566004800003e0060700c0c0c682c516600390710301007181511307204d000820400ca06a40c1d4105080700248000100c0340c10380400340115403034034410010780c0b500c540c111100c07510034420b4402c019500c044007031404040d508007a000e2900c460801000c0e088061440c000040546440d94015103040c00c269218010019891704104000034002100c0544e9812241c5407032100b12070100540e540d00380b030b184c64001801007070300c640910400025201000103440c414550030000301c410b0824030b031004820300d501070030951215010790740038004584094031450744200d000b62140c0d510f0000742401c10003405141d0018400f41860941406598102207040007901036054900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 550221106 1250 550219856 550219931
    0xe0c07021305061f0306091125140d021c031e02090109030203061306140c16060f09150e0f060105042703030e010b04140402010e01031b081009 63
    0x4124013054071460b10f4403210b680c000582501341d0581c04041101c0b00000104021101108443c2807840b41540011407540040041d00c4c01c4004244201400c51281c0200807503442e4080034581826034100c2c00700090780200380c2c0000142c078100c40f00b03d6215a07034a420405040c24000408429400c140c0d1800c00b25400300348200c840c1d000e036041d000995002811100e00d803070100070510040030701000c1102c04c11709055940102000303c2310410300840303440d152581800700180e40210080700214041d42e11940780c035040041c604407841400d5000340598503032071190210820601c151844680140c009600c02c07032224000c60008074256066580880d408070b428050b5403103107010114540c6280d03070b0350300014a029042540591040d09000c00303450091041481000030441110344400240c089001010001001584203264400c0c107044141000550001d4042100d00454104034081010541110a000105001403403080040c80050414082000c0d41142e449241d0390701907031500c00561000c2c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 550222356 1250 550221106 550221109
    0x60a0b102703150c0302090303030f0a020f07080a14040f05090907031a180c0904030503061318060605030d02070308070515071218030e10020304051002070e0c0702130506 75
    0x1810600408071280880415120b0070801d0a815441c50b01e010494504000c040860f030080c003c3e03500b07140004000e1821a80d40b00440003042c5001070410910707603406c0000360b00c80d0307045001410b1494050650142c54810300140502003001010000c00c001703038107210411002006940c0e4409030307041034550080d5910b8440d0707003516044154100a0041409100240841e500143c41603c2645070518211300c041c144180c40d62205114108190042119400030303003c6400740b002903030450000b07054044a01881c0246100300c2c4c3c00402d1501800c000b07010040705000240c080d440c0504001c0340600003000903008041c1d591111448004c10281c808610034041c0a002c2c0b12104107501031102d8054280750403030004115040f0004130003001481c05400c440303201103500c3e51002e49585612040303509003000b41042000400c19111b001144410000400c1948a01013240201c100700e4004041d000d0030020325510701c0700c00603e4400300e40001e22260001d0b03610795944a605032255003001805407101d10 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 550223606 1250 550222356 550222397
    0xc15030e0304031208010e0906070806120f030a1205060a030308130f0506010e160905130221250f0f11060916230f0315090c0102060a0b10 61
    0x1155112140400b103400424010760306030842010507030f0ba590000030382c1c81e0a2440c0c0c4080d42074035040e8450b84003c001030b0031140142038440d08510300500740311028582200340c070f20307043c1000c0c1c1041d07640d040070a40c5030407d038100500d242000c000700c41c2071105242c403002207007103055079110103003c0150041c00b10380b8011030a515803010640003440c00b14180c219040c5155590028410388001c3c4620310001681258602c000302d0a06050781d68564903586400104084144030513a202c81c603540c200441c84c4840700c07402e60031000820354186080a881c290f00702c81c80c803807400032000c0580d68841c408030700303450344c0403550315581100384c1030550f855078180d42c00b04c3e040807244022a0440c8a500c06000c0489000507a2045030941000100d5541d503c40405103400002c2c0542003609170340a00b05400c2924242d101c41598140c00390485405000c018080320840348180d83e1201141c00510b400c003000d583c18440300360f02200b885410710800082c1004610102c14401d80642001000025660b4040540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 550224856 1250 550223606 550223621
    0x402010c08030f060f0405010509040b0406110a020c1008010602100906020f030f0a20070b040809100513060c020a03020f041e0e0f0d081803090a06030204050117040c1503 75
    0x30042d01c0e80381c0140d8640b1501c00c10b036226482100c0750424031065240c1409054180d810140146105803595075a074004460007500465641d9165583c2c0c040031941c207400340106a6140e4000d0510381200c1090145a0081c50381607010400f01d800180b00c49600003d411941018180300050046001c0c00e0140003801190702250340394500005100d2119140c0c0300c10390041400c007004000c10119aa290f02c00b18400740d008210307812051114401040303010001b0380d4000d0190400c41e1034000600c0000f52140c40560303010001c1200850055180a41030240c5000f50032a801c0045a140041c1c0002e1034510062000074407132044d06403a10384a4403103400101c1d9004001e80c07a800e095641100120142003c072138503000611501c3d10020000302c000403980015846a00c0d220311035100c6002c1d05414401c243c040690a20040214071165100c0b074400c48010300103594010f07280c605043c0010444c078a0b030f0064402c1100d4840910010034664030303540c822211501050103041d480844181c0c05403096 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 550226106 1250 550224856 550224863
    0x121b090c19030912030c030e0105040215070201090e07020610080f03030402042a030501080c060f0a050c1c1e0201020910030e100603060603061b02060105010c0327090605270402010c 80
    0x4c1034051401e45070190070281400700641c0b0103102e41007050303c00e60300303d89040350701139030104d9504450704141100d03800400c00c0781d00600d420b4440395100d042803284203405594140040c0d026008114203001c1c513001d000054180b000280c010ac200b4000526a46d00000e0006441039030b032030440d4800700310161200c0402c0c0b01d40c501d410762140d4002c20060000c3c03000344102c180c40e00446803010600d103415400c0321030b0902a03c02d03d0b030901d000c0160031a89600511080c91f0076105106101c0d200000100c07010401d01d48541d0740c4200b45044256500c5e08014440e8100296030050058044a548200c0e0440c2030150914000030303154400081180f42040460f001c5400514000000c000e01040e50050f2082d40d004079800d10080c03030300c42800f2444841c2e0580400041e013041c001030200d584070b400000c6980703000b450032842050710702904001c0207016542d41c0346200709441d0100201411405410010001101c0242c0031000000702240030984141141c2848440340c4001011a030041140d0404142c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 550227356 1250 550226106 550226123
    0x12180f1f080103140a08030a020702060c030d0213060903031b11040905031206090c0403060b060f0d0203070908030406050a050d020d0905150f130f02040b121b090c190309 75
    0x8a14401508544080c001607400d10809840d44c3c8418a00250208519030f1000c3c0e540c1c556520341d0300c00d10007134000c2c84049074011801c1000f4101000e04001030711844401241c0180e03200c1d00005001d070805040d40c41002405010001040403c3d0410001c40c1b04100d04540c7d032140348000e241220030b044104002591291800c210b40d801c0c800000058400b1580d0a040104691a8001004445041141c0200074400104802d00019429802c089940312003d0641d40c201070400148601c15007084192a4032940d0120030402140d910844d02d4000f4003450001e94a000c1c24008014030b0341c4204024038050140010307501c400c55503030740e040b1f4602d207010030410040b040ca50301d00395482d41d031000c1c0318480414075036020400354040000030500170301904880200d0f2000341e99800403030f500184000c0e60b010340c2d9020405c480f52a03103011a112464a00090200f0310b007200c24081090154a06450150000c1d80130070420760301c5070048580c500e01d207191404031103403c860110050104408014013150707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 550228606 1250 550227356 550227409
    0x41805061003092d17040e061909021b010c0c15090212070801020a020f030a090e061c060b0307090e03121305030a030c09050d0201020714040f050c040812180f 70
    0x84881340034180341c0d100311341001c000780310800308100d98011400b5156a0401101c0444c195141c440000d8221040d100d4906c100d2079610035852080f03800080d0f18041c80700325003505103403048003842a140c00980c03605107a0a034a4094a80d0403201c0640c80070f5842c02c2d5543d0a600c400e554694080d0499565544101c83c0d005444840640c007070741050742d001c0054820300d2201001c11740d003c021f55140d40600e41d20700c00c1251a1818142c503400e4042d14064100d4190101403090507085010800c0c898010f89010407800b040d0303070038940782254036401415180e2911340064008a4084101c40361b002c1a0703200c20382c2c681c940d140007400341445110f0060851200084040400303425400400e402003003500c4040980e59100d080c00210124254000d0060300801720500504403107200c104c4100c24080c00020340b034404d10802c0021240260b0b1410600403010408018800003000314584003a0314100b42c60601111b0f054183c01d140c8000d0f85c1511030998101c0d1407015403100e000d00380c0c00c0c48803608000d2522 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 550229856 1250 550228606 550228673
    0x109050c150409110702030d0c0809012610050a0b1810020114250c08120a021c0f0c0c0210050a020c090708090c030d020c0f040b041104180506100309 66
    0x545c007012080340680034621000409074015641084440d4208060350700d402c422000454184580304c44100c1d0204c980c0e00481029001e4590b914400c01c079441510b180d0030305050410424203069401600181c02c02c01c0018070340f40003510402c00101081c1c1d08505c600008134030581c090a1100100c5500003040c2081107501064100001c0050071205516101c0b0b59108008030b45c80c07000c1040141600204200c1f020300213000d440c0300c69001c10421401801c0880703601ea000088880700d8883341346907480c0c040011010896100f6514104c0e42030620030720401066001c1800c034102d41c5560402d11401148040c134040c000d00c018a21040020984590362504044c0a00040c2040d00c0141d8540300e8450388600c0c43c240020070310103406581d002050403004400c20170112600c0701c0541500951550b4040e007a80e100c500400c8400c0c9050341c3c0958440f0300b849004819500301d40748060002e0705200c2030060b2900c0b00f603041c4d45203000510b07010030b04070020306007009920302c0000b1900c0c0e2403c0c022611300c0c0030b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 550231106 1250 550229856 550229891
    0x30c070c050f010e120a05190506060a06090509040f0602040e0f060114180f0909010c11160509041110050a0f05070c051908060112140109050c150409 66
    0x2140316000048400c0e480c0c00c2480703514842e02091502161540c0d030008504c0c44d06400c440c520700d0f00075080320700c102e08503030303a00381411402d4108a20b4a03900090507c2001020b00c42d40390321040540d10b00d05810f00e40301009001030054484c2601a01035880818144400644d5002c0095084030040d540c4640d2121810020502141c0381044000907101103142c030342c0b003000c500f00600d100c032014a046c4400001d41040c0d243c20820031552010030b017404561103444038501144241a03507000024640c3d04800040c2c070b40c0440f501e1071103040c1c220079400c621013100104c0c8e14059a070165000c1142c1d07685c5180280c2140b0b801a81160b21601200c01513074000c0d8020010804841940c2ea021003244401c0030035621406808401811401043d03030a200500f0300c4007541043d9041001a0034001d40d442d400036040000a810140100c2c070520340150901c07201000c00b00c0e281d00d00e1802002000380948603a522501084130301445104400381011244028070181d4015143c81c043c20084802c80e0b50ba15080f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 550232356 1250 550231106 550231117
    0x120c090406050904030815040f0e1605060408150601030f090c06020d09080604060e0a020d060b091b0d0b0a05030d02100605040c050a03050c120f0f09010209031b0a0506030c 76
    0x46142030020104141c2400180280140c1c0d042e1590300c1b0a4466000a407d00b04c24860040d820640c1c4458068640360a800781e4451180001c0142081d8550096464005062600544c2c005c0404000802070319a00040d8243d285102c924507002d00d8a42030012800760040301c2c1600c54440c207000b1003d040c01000200c441c01c40e42c4503002c450240b1484007040c2c0d0041c056100718040f80c2c001700c00003404108182c22a030300c0103840c842500d04c10f480607400106d0400402c40d090720b0003503171008521218200003d1140d0402000f0301c912050800c003420f00400e9200345e03c000b2582540b9103007440f1032074480e080d1001c00f500c001401da4070b443c54030010080d40d078802c0003803250303000d4101040080c860400f0b204140f02d04800341d40d160b00d40350961106501403c0b002e000a010510f00301f01c40030340103c0c4145030b980141403c1400281900704965080c0d03604202800852485c0d204000314080d9580c0080c1080c03446401c5014010709042020004809205941c00603410040c0002084041d0941da0001c04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 550233606 1250 550232356 550232359
    0x209010c121d0a080c130204030c0b031e1302120a02121510050105040b130527060a06081315110702011806080a020d090f05100b040506091605120c09 66
    0x82890b0010208900c052040c4610070040c0c10100d0007103480c0c10030318003c80c1042d0103950091703e06552692030000703100103036100300d510042c0441444102c40e0100c400e2400c9000d90380808070141003022804811154100c4000d00c030741c0c401e000c219040141440840c00c079540061410002c0b50800600d117881c6c040b031007001c40889401000042005075416008026100103a44550800e414415a1900ca50120201e44e00c81402c00b80700080e5566040840c1072181040c0da140e0b150a240300300c0d030030f000304000361005100b004000414058980d02071039103980181d0402071907150418a040001da90b840b100300d8480d00318140046c0208141810b401044068400e1740c9202602c11551004001e04556001e50400586503402060b6080803e030094058200d007000000b43c20384087d81c500f45070700c03814081110690044501080103080c14031a40303450400030782e81400030745820000184d0308a0000c3c08141d0510400001c0501c0342d21490555203031441820b04414941000649075103070760030171545503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 550234856 1250 550233606 550233647
    0x40c020f0a0b060f03190b06130603050109031403040b04031b150b120304060801060f03020f16060f0207030207090207030c02031501030204050a18031d10091e0503060a0209010c12 79
    0x600c07060171300090011050300e0800e00301c0114040d80d40c58103901c490181c203055002650a40d003082e9058035110300c10040d0b200c1c0c400041e80146600c0d016240c0d65140100c004220000c0c07003000007041c42c0301000c9501a6151038100621200d0003451440c0080080c4c020703007410400c68042480782029400741c1765012048800d290340940114210355a84641d00030800011a00001008024011038001080340c2150801504013071111710451440c0d0400d00c110407015000c2002102030100c030f4807896142050100080d4a000c0c40c07510041e694000c3e034485d06503881e0f40011000d041c0b6108030b04d094113030765000341651000e10b01c504040c00c2c1c100e0280808d0344030318a000049107510407a0f20412481044582c104e420300621904d0540340c0c6180c80c400d020010b007010801079142e0707440316100200c071007041d100c2c24041c6083c000e03035030700c07030002c1e5000300c1c110a848900c140300030340d400140c00c2d91103074803044003603a54500b00c0012664003c41e240300400400e1500b0303e000c0c24a81080c100c00781000c03a0081c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 550236106 1250 550234856 550234879
    0x304090501090504021c0c050904060b0f01020111041e0803030705031806060a05130e060709031115120c070b01090c08090715051803060a060f061d040c020f0a0b06 72
    0x250b8045880039200203601c01c1a10aa01d4503119074070364107105d031a010b0805000c003190f540c400b046808a048608680d81a07880f12030210034500a400308209403030038402002802c4403141458800c1c8201d010700381000c1900c40c041c480c260304800f4040003230078200381035a0f16402c0c28540900290816111802100314011180c0b19002d40000d415105260080420304e1062500041c030070b207920b0b619075203400b03262a09500392100000304502c1c1d0180f10741d50340e4519600e01d1400c21a0013501e4072035509201d40000c60b00440320400c410182c070000316030000c1c00c90944e00c518100c40f449101d100c3c00240350100c9040002242d20040d402040d0701c2d80551100c501568452888540300c9103c1e000d9000564014181c3c0c65116102d0b03809020f0b10b2449030340b071401407007402d00001d2601d6001c44155030850307240c2809005943d00402c4000040c5101e08245030b21070300b00c00c4404180c0c2c60400c0c4441c0190707a40d84000300418030802c190f84903c4111803c0d80d5042070241007180e40b010040310043d0141549c0c440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 550237356 1250 550236106 550236119
    0xf0f060509060f0c030d05040321060b04050f0105160501020706061502100e03070c0305070617160e0d06090b152202031b0a050d0c0302071a0405070b04080304090501 73
    0x726074481000070881890b01c008900206030981251004074001d100a0003144600e070054420030b4000d50098560f01d1001d8503500d107007001366000010003115a410250f0400000743c0440a4a00b6602e08440d595000c01b114030040b42d180c000d451204564078100c500204c240303c0306500511003140113090600034980c9a4951208501e00f12641400680c0324501e58142403e150780305d10160030001c0140d91030145641c41d46101d410050704162401d801202041003429003103110100030041c0d00c40008100d20707210116106004410a080c030503c0000d100c1c030b0440e035441420100c1e06a501080412005510b400c040b580f0000865012000340a16991401540b50401c2c2c1000d8011704114403110800c40e00c01c090002c0d400140c08045036219050301084452015006850390000582c0d4440d110108621010180d5034009801418035204010b11000700d00c4840701d5080302510000410400c0d10341e40703401d92030b20307813103130301401c80c0c02d03008980401c0034100440103000f180c01859082c8101e0f41c8801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 550238606 1250 550237356 550237367
    0xb0402360a1706070e100806040605040213140a030201091701110301060201090606141c111f121a04020a020709110403050105100608040b04030507020904032d0504140f0a0f0f06 78
    0x40c84544d0103078144940310380d82481f800038203502200280010650369a00c40114060f80c010b5410300e8a20010b00744240302406480b08a2064100201d0300910380c13610391303000078181c0d800500031801d1a16004007032491104003500030700c1014140704140c0365690394601c0b0090003094024400c45000d030070001e000a1101011603854060100140300c45000340301d594040b0100c070351000040b10158a1040040340d917603595000115140002086d0811b0041804002040080f02c402c0314180245400c0c01020013484501ca009034550003520010380c3d415952400341e1508485a008a0341d4174108940705d40000c0035078004e80100c0307118000038401034449440e4005400f005004020010300110000b0780850b142d400000d40107400380c10702c0f40c6801c02c42e070046074400c03000300d5080d80440c0544120750001c80d54602222481510100c0402110380240300c001c207548254861003041041020000100341c0d544c03081000c00d0b88000b0101c00c3c400d50340700542c0418044500c5925040000441c1c00a406401503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 550239856 1250 550238606 550238627
    0x12910030e0a0c060e12250308040602030912030a120207050c04050c04050109090e03070807020d060624020a030c060f180605010303020c030a05030d0207110409050a060b0402360a170607 82
    0xc5000d46014001c0443d0707503145e102a1f40f0401070100d920701c80000404d540800800c00f130a4141e001e5a9585180e40600038040c2002c3e4180e18540e1040040428065110710340c034045408140c00544d40d924181085031400c1e000c810741d640d000e0300c1c0c94140100e9061a20040040b104281c0703450072a6036868003160103c0b010810103c9098200300030748000202403600a0119034402003c4111040b042d85842003103400c5900030449610085442651040c1102a404a0390744148000d141050700c0d580c009084146651000340707656140c540c001e220701c00c02d802110704170001c0c40040680140c2400c2c05d4015020a01c0150094000c3e4802d4245034100803940c4412aa08240107618007819404008029130240c002130b41c05001440b1194607903035a9028080040d070060008040305055814a9011507800b0300f031301c81c403c51041200c0c100a9408814044444524050322a03a041140001d55003003000f6000030380d8003c180d01c101003400100721041c4034000e24901c04544040c0e480d4242560384a105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 550241106 1250 550239856 550239889
    0xe07050703081503070b040e0a150303120b03100237140c070b0313170301050a030b06060d0c02070602060f0708040b0604060302130b03012910030e0a0c060e 69
    0x342c0d0008001d070200c804801c2e00c0b000058100d400f0300359103101141c4145c201da044076000907080c2d01801100989402014117080c08528259240c80c95540c02925108140545101440d15071000850603038051100b020343d8501d5040035503855400002e2010140b130010b0b064580904026168015605460814150b13504c0984070303614160388114072501030341c20202c03040301d880c8640d88005c550020b0a00c003550041040401910302014071b403030b02064200d00420b8407441c103842407004201e940d88002c0c4480483e904518650b01c1d6458950219181d0312980d0281c80c510341c1400c2412060b80c1d400a108012602e06500f511f0841c4c582d00d190361440403007507070004001400e10700803e000c01c8180c81f041c0d410100081c80001c0da82d90383ea0115850b00302848107000c429a4450314100141030070702940060f68000d1403500011600700d5084081181c840f100e041c01506072183e2090281c2c0258017001d81c8a6000c0111210703240c0901d4240c906113214003441c400284a03181000317140c200072030540c102906 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 550242356 1250 550241106 550241117
    0x213060b1204110a1401030509010b22020c0307030c0506090a02061c0b030f0303011409061f12050405070f09090c050f0f0402072001140702190302040c090e07050703 73
    0x80300450401e03101e80c090801e4881d42c0390101407580c0c950360144000000c100050b000c1d68080d240000142c21904024008041c0ea410701c0061207096851402c5e000c821104032511081e40300c080d0034904028012501c059410b407000040c480d05040d0000034418009108400b20342c0e0035907440c28080d03103440d400702c0300a410181c00d0241c00205210301550074402a58414005415640603000907c1c248103030415040079000000103200c50300240100e1014400196541281030404a010440f050325000072051424500040090740ca0f210300080c0c80d0300c10920030140158285801c10b0f03910b803081c5102d080c05025940b000002c0001c2c950182c8d044546e0001541d041d42890041444103507802040702682c09201012038812640d0f40e4406054103502036801c4c52a605094009a894084803c82081c14002d00304d0300400b544085004a07098154195080f508001c4084030811807684940c0000794014203102803450895440801300045581403a2084550348615406071080d1280c0c90001d80040c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 550243606 1250 550242356 550242367
    0x418030206011a12070e01030f09110d1b0f0618050f040f18111908070b09061c050703050c030c12060d0203031b070603050f0601230c0a0213060b 64
    0x508070351401c80703d00d1030084480c6000c400c10581a1118411115a4041409490b401d111942d251040251403481c07414100b10198980d1250403206e2410510284034074812420744081216550100c8800c2c0034490404464949a20044500040700d010710700000350640c440e0b00101640002480840318042c28080215103100140006800f401c8a03600626489507e0710807000744d10350304848061301441c00d42c0400208801001000c884d4041000720308440704005100c0281c0c00b00b80311003200d81030280a951915050003080d0ba40c06000641694503806c2c440440f400007158124a20461681d5820011a0760303c20b190712071800152203440340400c0500450707c060441d10410f03500316400502e6002d0240082d40040d10b07541c00100c001100e0740b911b07007480715105001c0041c3c1c40600443d0a040c03140e807a05100801d81d4410080400f8104403811000054114a0045000c6200d0780118400da9660080c0141c40c2c3d40d1a1450049001710701c003c03e0070484042900c00c00c0d080d50341403040e081c9440c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 550244856 1250 550243606 550243619
    0xc0302010516120207210e03010b0306090c0616120903030e010903050c01030e010204030b13020901080604020f090619140312070b04021504080105040303061d07200f0f0a02041803020601 82
    0x3500b041c5c10803280c400c0007400384500e4015010b040151004075585441510941d10180340c04e60391001502c60081c4d0041091000844022807140c80001c426a000d90315245100340100d10417180d9a0050300b200810311a00340f001d60310800c00c809a0b4000e0300c6c0c07045140700c2000112142e00803440b02401c903800214801c0e10961094010b410840c100400250400e505e075191100e100c201076402c6004400200d6940c0214103110845078011300f202005003c4074641500450b40c1117000d9482c031407003200705000044196894601802050000308102e00f1130b142c6546204440070340001c00d8030310031700c54410703002c07243ca075410300302c4404942c020b824582c039403034076400d011b00105400b40f0241810402e0201181d666004d22843c1d10981c082da8012030110319001450000001210595081000030000c00c520150041000c0d03082c042d400c000303000ca212016840c0d50600200c148c40410500600801d04403468000a00c0a00c00d8000c031410001148190381c1950b40740310401c401005130308007100401c0307003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 550246106 1250 550244856 550244861
    0x9060f070f0311160b0f0c070b040309081605040e0f0307080d0b190905011a091e0d230a05070e13060903120b0a0f0506070c0f060c030201051612 64
    0xc1c03548034107001c6000d1072003070000c071070740e40040704103000f03603010549040148182140c0054000f002c1c80500398560502d400d02c00d03001d1058003005400b4000003404501018400c0004000801e02030054442101d0a00081410114503105052103a420200b81000d08a400f240402c4074802c00001035150141643d41c008954010441a200d05681c071985510540c442c21002440c42c0b10b82d11a01200e503081012030b00c102d61040c0c01084110341041c51461600d4074290450310506021904e001101000c9040c4c3d900054010840c59000140298120708000c4640030301d08059009140c00001019016a21aa03c1103041d01c042c0c61648881020006414810001c94002d4503c910440c102001d07504c3e0b9400790b4001e14001c400060030380006414480700c070b104441c6104000c44403100b64138a89406034201446d20700455200e1040020300f042006001042d4030000d042c0601e1103241c807550390101510300f56448009a0155082000090b90104000c141d0048006d8a0b1140d248068901e842c0400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 550247356 1250 550246106 550246127
    0x20c06180d02060406050c0706050717090a050604080721020a0e13050604080a0206070903080f09010905090a0b120102040e1b0c010f06060e010203190e150a0e0909060f07 75
    0x7080440004180d0140e00e8810040c4050402a11000e981d2801c01c2040b43c0b03004072070341c4100c041107014804c1c0342c001a0f0107071144569080489400d0340361001c10b03000500480240d88480e074080d40010380003441c9a004940340301100e176030490749061441492020000c00c0baa4620083d40030401e15001c1c0305241c04c00d44030300c0c0c0104852b02c2c00042c64029a9175549403030300c183d03416102c014021846000c0c0c03590411000b50310409038945004036500d16541c0d03000310b00510000c2e0740c01d442d0114200140b03034070949020000745002800d1107424140030000400814030200180c0c0100800452402510814000c841c101c4c0c5041e0740d996070390360356800c141b410030b0261029480d12000030460115041024011008400d00d802c0b0700044051520101400c0c10001c541103a056400501c10700b040381c0144c0a002d4903545203800e112401d24942400605007580c02c056407010040c0202d42d0040c0300340d200441c0a444030003035440403c1c0c4c1c0c0b10000115a01c0404441d04000100f03010002150240f003400e0898 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 550248606 1250 550247356 550247359
    0xc07030c0f05030403020f0d0c061110090f05060c0414040f0f090c08100e060109020a1e0512010509040f061d0d1716020d030b190321020c0618 63
    0x858100c981e2041c000742504941554182e001140610940c41c00c00749082c0c0075942118210000203075035580340c000e00f10034454601401030203c0c1421509009020400310310480c4078080240d00035a00d003c1e100c6600a031400d035003501c103d0000a0b0a00c1012040b00c042d10882c021320805045400b007080042d014680c0d03c000320a4481d200a0b0311241c40d0f00480e00524400c1c440c0b407511508008440d4907008006e002003519509211000604050109455041d100c1c0ca02025a607041c24180c00e5803055110032400510084190300c406a80d43d219010b0640901c054160000c0b59994070104103034404251000380030044502e81602c0000d000d50711003141c541d49450394541300644002e0341c2d810608039910100c040f408121164090020060469a00600c8002119954203603180001c1d0384c1c81001308030340145613442c910300c05076543d5018142e18420702c50400200c29916407512440144031710100e032880e420a210305020b001d00225005600c1c901c060310140c24071a503802001c080c01d8000d10b005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 550249856 1250 550248606 550248617
    0x50601020307240f0b2d0904050f01060605040b0421021306170d020a0206031003050102030a0605011d2d030105010b0c060906091504030e0901090c12140c0703 70
    0x180b003450800100754820260988028440c80c2603c007030315191450902c07107524200000e1034075030315200c1240c1d0420141d0411295104411101e24561a410507010790110600c2c00f004100000000c6610820030178400074024240e94203010b4400307000e603000381000c80d801480103111410040381030300d182861b851200300007901140c01140c1d1000c01720703030300022030350b00d580050003040c5c0044000950703440030600506030070b42c007074100a48403012600020311811002010550280400c6107000183d500800215903030308000d00108010202441142d0202d4010080902904003142410055940180c5850b440412800451950043c0d42141c08003040b003501c00401c0c6a00c003442054041c0400c00040343c4e4600380802594030b030000041c0102031035030001003001003400001c28410600b80c6039190b44030301343d10740d4030b0251000032606e240745401002c45400014040c20540204038000c4c441d80f030b0094076111a034951800d803210310007180040d052103030210306e030894120028251180a803410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 550251106 1250 550249856 550249867
    0x405100f0f05160f06051b07020603221208060f0330070803040f1719032a1e020c2d1504050a05040506031c091505071202030705030d0506010203 64
    0xd00300007801280003505c003a80e9030810070803006040382001c0c030b80340e0f0900c070000d0400c034035a800910301b44001030004042c5444020442e0480d030f040e00910107040d0b489200c3c0f8512800c0058000d043e070b142124080c2c4980e0b01505003502c50700f004903139840110340843c050350800124000b8180b254003014481202c182081001e14040340301707103024501851050070048010f10b4a03041a0280341c09182e41c07070001400070050840112030300070b000b00c4000611f0034085400148214080085480c1d03084152102042c48202c1e490103a02110408080b05e40e4481c10305602c10803001282e850b0305640c420f9400010036002941049100c0103d5080c1d1080170990103502c642d0701c00841d850b40071315002402520404101032050349043d20317418001e81010f903410461841d14900203039503180038000760020940542c0382240d95900c141c107400301804104420250580c0d03600b4004000da0b0111009803583c0c082885807044651002c0102c0d210581c20000a50808284244980081034098001415031204100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 550252356 1250 550251106 550251113
    0x20f01020c030909010503070506040311040f09060e060708090c12102f0304080f09030a0204020309030a0815010206040305310501020606040902090a0c0306030b0c0405100f0f0516 79
    0x1d1101d40a01005103031a041c1107018040c85a078183c215911a4003c5803042c0400d803564000e44c0d04503a0000c811540315068900070500400d2440c8107888820b00302800c600c14030115410510701e0801d402c3c1203818550350310104641c040c0043c1c0c0c031101c803600b00d0307203400740700e40341c03000b079034604c40203004251000701c6011801e0750304075080b00f4100c6503410030195200602151641c00c4072001040040424a945816503525010b071142d005501c00130100410250003e8030700b00091081f290707001c2c108564a0a0265096640750800c040c200b00180001e40060207402da00c052a140002042c2c00600c0c1c1074a5503901550349421503900890701078104001d425900d4181c80300000c040d0300d4100711200041c2000002820420b000b0188c5000b00d003010300007c01030311180c803c90f038801b001400c00035004000000c00c4018101c940d00103000b03040450140400b010442c4001c0048900480d000100c0407004a801c0e00d81ca00d0740d540301c50128203c0807144904a004034002c0403d00c901c820034603980e21103a074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 550253606 1250 550252356 550252361
    0x201031e0c080903041d131709040f202812110313060b030a0206070615060f0c03080714120106111f0902031f091e120c03020f01 57
    0x948020315a1103103808814180c000e812150818004805180f800d810040714905851003018031a8034031080c513001804040701d0324031100345c4d650310120036680507820010002d05a0010200c0302e11540c5810004002031095114040d8610009140d243c1c12400280b4401c09980020484080a1034101d20f00f4101702d2036100c981054507150f4480030b82c400c080031180d808440c0010071070130501b0b80c00c10520200c48841a00d040003642d1225022400b26001008242440300016000f50408404582e80c1c040040d141c219410b800300c003888001c5066529282255003000f10603110010070f07046007500b0b000c40c0c03041c2d80c840c0d8071a00500740401e45013528001c81115510124603807044a11850051100300d600801401c040900600100303144e8003400054540c0785902041c9901c142d6035100000110344042c84100c40d501600e05840308a01c056009010240c1541e05003100c0001741802c1c0301c0c5880c41c0640c0c107481c1d050b401c135864600310452240159803504d0708103401d40951103001c00b000000c22090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 550254856 1250 550253606 550253651
    0x11407031803150c09050f10050f0a0206011a03010b0301060804050c100f0f020610180f09051c0c031b051507020f06010807080604080a030e030412031706030613020103 74
    0x600f143c107040a07441001008603681c0707400078030402c40920f8040000e592200c90454105004441d4051b402d00300c0f520954452184aa01801e00080441e15140154022800604076419850b1002c8101d20104c5a0802c07480b09000c0d20400324001d10050206501c60303603030503034040e201d00c0480e020706240038000b55055490b5045c1074006510041c400a1440e8412184812594203000030020750400c81030f40704541d40c0700e0040d034207445005040040c0c598200d4011040480015104000540180c180a501c40d501a0010000c42d1540740406440d58800c88690740c540c0d802d552081d0040c010340d00000b4007016440300569192140b981d2803044400102250b600504468000300441006a000a030400c0030503804900305400180003001441004240c1552203a400344800d540c1d641d107810103400030103007401c6540d55840042000300315107040e65641d100b811f009031a24102410b000380d00c0c605034582101c4840e090b401050110303441229640c80044894030504000c1201d00c1c1d01d030351904811004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 550256106 1250 550254856 550254863
    0xd060b04090507031d060c0d1503111f0807030b011e03020309010f0e0c01110f0a0f03030b101403061c0b0105150a0c0b07090902072a05011407031803 66
    0x124003c1c0082c140c1c15124000d95118605d06200ca90341c00105119283e420080c007d402d4800d00042c05100d04400c1d5004440c98808800d110101548a00705126406070303d404a502900c1d0000603002c18410f202407200c0c042c6207660300c0c82c541c0c0d92200411409031210765241414066104200700748000081020381c1c141072a03a50044e26403401c4030030b40c2d09440d40301da6102c444a14005a1a01c1c2010104600c01c42400030300b0303c40c26002e2008500d48ca403006000c86d00c0118018189034100b01310100c03801381b800c81d00135130301404907400031400c08c004008208804800314414210019070050707817002450303200c13000418010480010020308a1540302d04c03a012141e031030061005000e1031400c01036038080741801091280c10403a04d9140030300b00c000f114401621212820f0300054804c0e21400a00c0b0240039181d00075134844900340303040c1c0700c42c0403000244030f4540c41d40300c02c880600d075a146814044a4050b95040e40d081c428a01c1801c9079400301d001901000a40c81110480111203500140111310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 550257356 1250 550256106 550256111
    0xc01050916050a03030c171b2d0303071206090903050d050907030f060504051c0320030c040902090307051008040b0705070803060f01180f1a0c120d060b0409 69
    0x7000100003000c2802a0000e61050083e11818000300340d00c11440d8017841e60160a51084022440c1840b0850113158020006200a904074011520300070801401a20a001260403004002c54850018095406040034980d1050002503c01d51003102d50300050210751000150068481c3d001805a8094840540115200040f4038030480200d00c20568480c180c03101400c074560031981e034041d85084000020781510380300c0e000305050100902c120b41000189041410000c510640054041c0c559000340e440c500030115450781400d00708404480c85541003101c05450b181c10441c1240c0207420a004032038040c8554000880c103500d07420303948441002c194070b8003011440c1502d002400c03c10010000d0040003000e1025800041414042d641c100070100c402e4108085c1e403c0048038001040340383c1805c00300034007000183c0010440703c10300942d51013a510740c0d0382d44100604034000d840791a902e0a02c03680102040c0361480700041c09080540d00e5000085500c43c1d544007902c42c0ba0b0425001504806d0b03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 550258606 1250 550257356 550257373
    0x10f0f09150f0909060b0301030201050c010209031e010518060a0e1e160611070605030403020c090f061003050906040f081c0b010f1e031a0909030403050d0c11060f0c010509 76
    0x281c00a80c03581c004c0441041c1400041c4c00d00340440f00a010600c0000e06008001c41d0280e000350003034058030001d0f64040c0c21500e0784d698000c0d44108405c80d8000b20b10081d40b800012440d00a0f8491020810045150081a5079110002c02c18010300305440400882d01801215940340d20360b490305140101e80090040800020420303040d50081542e91095061003a2912280c202d0403000c01c1881c1214020705025131280d5a500f000da080244071a2440e500200c00d00800030f2244d20510a503014007800da441032903110003108103804803482075400c00d0705a842040010002000032481006443c81425003a040c00011020101c550301d2642c084d9a40540b1000e020240c1c0d640312003e460360321607524200801010700001c00d42425240e90803c0d04061b11108007a11074804440f0700c18400c035014022029900d0030840b0562a80c000d800220343c2c500456203014000d41c0f0980045182d150845640000e980b6040e0030810558402c0c284003011070020b1098400c45542803042d10303c900c0e01c400c064030750304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 550259856 1250 550258606 550258637
    0x708060d08071a010e190207140604050a0309050303090924090a0606031109010c031d0604030c0305070e090312060120010b03060601051e0706182a05010f0f0915 71
    0x4050300f0076402e05400c88100110b1401c848030b06e0200e50711100740140d8503449400c0c00000e02e100390341440038611034a81403100b0440001000c4c3c401c90f000341e1317500304110303100c00c101500c0e07200341c14034164800c103010b000c076042490b04600c10b8140700c5080f03400c50040f030150011611440080b00c0701c91980364ad540081028039014062031074070034904034002d407401a810b000171b404000c103100d001c1e08024082c5030150f00d54500308000690400001c0c46540c541d0761317034500002000585e0100304d440d40150130300000c141815050f840e01031208540950f05107840104d000004000003001d85041108440154080d900d084035405841185a0004520384010006140c40c107100030303000d14104901003106854080b404582d01000d601c440c01c1c4255244040d062540181210b01d01d2a1010b0020340304050030002600131004082005506010310803610240101902c6400e1243d1404120b120080800a501c03508000c404003242e030034803200881d22030710000f0500100003116408180c9113450321412 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 550261106 1250 550259856 550259903
    0x10e01030b09190602030a091502130e0903040b0c251412100b18070807090b12010501030903120507050a030b040203060a260d021615080708060d0807 66
    0x20601000c01481c6a440351044060035203e00280540065804404185011001d4001c006003a820103880700102240c240080000e40c4850a00d0b001d4610446002036441c94006240303105450410145060070326080b0200e2942c0e01c6180540241d00812003248815001d100240c0c02e481c0303800007003803401410844c8841003d00110040c6129084031031022641d80d43c00915a196041c00400100e0440b0003440410718042c0e5040003071038400c180d00d040100399603202850520442aa40c0c035003e802e83d841d02c80c200b052150030b51020030301d0388580041c04954043d0704050000c2d0321070704e4150030f582401c024190850b40140c0d00000000c200140400200b40d1501454901d590101d40440c03130f6042100000c2c0301079a040c4640e030428038010b90303105030780880021080010341c03a034410f45d0308002d20800000c2d1900e008524000c4400d02051010031010648583c20281140945822486450713074401520310050081000e0740c011801480580000c80503c09440480c0c819014240c0021800300d21584 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 550262356 1250 550261106 550261111
    0x4050112090f1e0b040803160801030f08031b07050a0605010f080c040b0d02060301080715092610060b0315030f070311010507060c0203091807120216050105010e01030b 74
    0x103846040400720008542420040c1420035400480e80f180c0711541c0d9206004441e201c003016008002d200100410301084000952103641c88003c0c0092540d04441d042d42c071154280005003458064241110020300c001000719001543d5005140e41c403001d400003800e0725072059008641c1604000c81c2c1404002c428029507001d82200d41c501c010450400c4000c55540c5040c440280c4070303e0303d4a0703080f51251a0020107000035500901080c0c1d403580c41d1501070740d94009520130882660100b4240a8039281f00e004404160750300307086048454840d00f041e16200c1024940c101c07071913004229221440480d0313485803030300034803202180f191240f410b001f0320944081d030310002a02907000340404120030700300819880b00b03481e1310007128422500c6981c0100c50078010003000071310003460003140c1c1041c0c1e0f40000140c03030006021240102e01c0304400c450a61070134030988800c80403400303121100841c4001c0340c0103404001303c01189a00200100e444581c25600d082e488040c1d0b80508800600500000f41e2442d917 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 550263606 1250 550262356 550262387
    0xa050708030a1b0204060e1008060603030306060d0b210d0305100e040b0a020904020f04210c0b0a1e0804170703050904020f09040504061a120c01140f0708040501 71
    0x10304040400b5005440300c0e2100d5019a00043c01c010300d1011507072a40d02050103848420203410180c17601c070900340160b4811740a1505948550000a502454004120303807066a001e44a0f40c05d050322614403030050725031100c0c844c1d0310089080203450b451600b2445040111082c0b4000c2c090044020805012560003414000e100f201900046c04440c901150340d40d04503900626410890b52034055030310090040c180b00035806400040c280030b07503492010140c800d0b00e10507002d061110844441110400c1120400241020f0b40d100c1b00700004d10122001d070401031310b907045c001050700f200c4c4a0b800b20b02c8070300a00c1e0408240c1d56014030050001d9100c004600d050401a440e1400044c0d8030050b016018840156108940009080020020f090151446c1d040060024041802d2516203000a00740014110341c1d540040c0d060002c586ca0021180503400510002900f42c60540b500112a001502d8417505000c120400c241010a070109005201040c01226016203070307810000014140504e0b0132001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 550264856 1250 550263606 550263613
    0x80a03060602070b0406051c29011b0222090f1a0708150a0b0c0a140a080304020906030f0d0203034611040902040e09031e07020f0904050a050708 64
    0x6004804c010022030781507520718180035807244d501c46007116154107000040c0034542d042160100000800810003034428442400e1030b01110000c800440300c001c882c59014461201009986015003440181c542c1d803500c1d00030b4181c42c0c0281e6261001c0a5507110784046030030101c2a005c0000344080103ca00344caa200305800380449041c0204020440300c1c0240100380380b0200004500700301c0d130341d5266960007000303003d00850f2075040901f0307929120704008500f500d070034460300064072003034001086445c50950711400803419600c8640900c84d1824008200f150184074282c0c602c141b20b00204284a58021258011640c0740b4168586040364604100783d48000b0f02c6d1052140810344a00c22000d0f429945210601594046d80316080090515a03250203a9900c00041c00304003421070b0740090042c0d0301c1041017242c464846028107907030b81c030640c0c28545000c11890491101100608002d14507640000d2841354680d440c14001482884182c034112429804001083c042020500c001c400400d4440003a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 550266106 1250 550264856 550264859
    0x80a112103150919051005090103050d020601050105160b06040608070e011e03031403060102070b0c010e15010b0f0d0618050a0c09030302071715150913110d0602090d080a0306060207 80
    0x48412010340800c010103480e20341e00004c803030391b56140250004041c01807000c841c0d56524180b0540714202942c1200043c05240004100765020340100c0310043d144134a0081c0405641e118159903280207011141e0081c0c86080000f0642c10400c15007003d01440c02c241d81c60740d40f521840c102c0c5600140020b171002c160f90081040030035006203204c0803090030428034542d60703660000100c2c18000c040c3c21144902c4804a42d1695880c2c2c15442186071941c0001124041000807280c0c2002d54401d10074000c1807001001104441c2032940054600dd60f20200003041d29a25031088050f0f86d2119a4111f80595030343c807c02c1032007070590140c00c1215075107003040700141e030560718000c1d01c2c4c0352140510b100031030001d111020003403410001c24a090034444e0004c95641490001101404881c1c40a02c2c42840c561000c60182c0d00c90b0000c070b03100c0315403040e00d000210940b10148041894000825502554280140360994803040541d50200340b06000503590390400c0340b0064115206030300264110f5010520 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 550267356 1250 550266106 550266121
    0x10e06030d0516140715051306030e070305060f15040b15090303040f08060a0c0207150c1e0b060307090605011d0d0f050318010309080a1121031509 65
    0x141c022280105140071a5601c4414401000f41c5a50103401003481003d44010b02d504200840d601c025210300c0c550308000c1200d041c030222000e020f0001803c240d520904010403a2602030341c004480f03206028181c1d28076070b42e00d0300c60320304081d0100c0d100c0b0301c5401c3d030008000ca10070750ba07028415120b000311020010300b95440c001c00d9010544030702d00b1400c0c02c0000340a40d2160380400580e001070240e090b40503d4075449484442d00c0c1c2e503058038610011410400101d03421400844e20b04c05807015180500c2c142000c0c07070750495203040c1407142a29441400040340c2d6a0b800400d5000580c0d41c0649111160b9040c40c0c0203061501507aa4000c82e500c91a0548c140002c0c0e901c00322084010810004035a070a0510000040d10980d088a0041500250085c000c01704407000c401340c1030074219918a8403030180248015030644041c000000c00300801005403081c1c4502414041c1503004002c02122a04101c140c214050825604c426480612002c000c12498861440080b000c281c8255188080341c20400e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 550268606 1250 550267356 550267363
    0x8060310020424032403021008010e132909120426010e011e05090a0201080a1d19050606030a020604120f021f170c1b0709020a03060509010e0603 64
    0x1024048144182d030002000f030b2080e080501c040111207802c0031540312810b05800a119070303100032400b031024205015101030140b000141250390004040a40c5c1e91005d0340f54000e200e0100c01201e5906c0e10007074000258500c0e440c080f01c0c44c0b070140c803048024103000c50f8a030b28040030083c4080500004010a001e120035013041e81c1d45104a010503a0310018007505024003500032594260703010340c80c05040e6280c1a031031015a186e10030a00c0d10810003034403240007403074486e12800000303400724612002140800e19140d03c0b01110b03908540201c11000742c0d091a01d0b02b4000196010820075645050480921405000842e048401140101103074800d99000c191280101c0c800c24940b48841c28030001030040e1100c4882c0a00d81c000e02c10581c8144004165100c40919403009000a0300c60310008092000d030010790303005000c210140c0b03003000d03440c0d40c5030502500c0d503e200349201d015104001072a441d450020b01450f402e540c40c0810180e0520040c8101000146d0103264040d40c1d6100740314040d200403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 550269856 1250 550268606 550268639
    0x804050409080c060a0c1e0f0503060402120f070f02010e21040905040b010e0f1311010216081b0607030f35180d17070c0506010303080603100204 64
    0xd49000c00c600d03000e400d0034800c5000d079458820041c0520b5007005801d0940350b02ca107082282039114600e4910540f101c2c030101d00341042c83c3c2130104500e6002c5404150185000d1035208030010000b500c1c2903024800c1c1c1d14500b2007a2100040500a4414400416005200e1100101003440200700c0c020401200ca5515080c040342490306040482d1600d081e0200081100e020300040c8405000b2414280303041c14120009204404081c10017902041c1c4401c514000c40340200421841c4800400640e11804810000b00f626141944186004405e4917500e480f20000101500d034094450b04100012400b43c061113100c030244039010400c4a02c00003030f0469015603048080b4a071003010080340f0740200c02076145103006521310032059000c4401c0038240c3c1d0642442604129401610040c3c1402000d603103501e480f81300408200b42c0480c51780408114070000d64081e1551614800c40c5a03d030700c900f030801c0821707003082e40000c1d5501c0801c00582410800b5944c40030403440d0444c07405184c4250a40c43c00f981 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 550271106 1250 550269856 550269859
    0x612190b0f090901090c0b070204061d071404080706120b0d0f0807080d1131090b04060b031008010e0c0a15030f02180405010906120b0403020a150b010e030109080405 73
    0x4442c0402c1180c40c00354403002d072155000c01d214600c1d54a03102004105c1e000440224410b0f070a198010403940302c02100754003100042914a285074840b0502582c02d54014600040c00d00020301c400100c0010801241c0c2c020080c4d51900f801e110711400030031003556441d00040d401910300808c20301c001042075045c49011074200850b20380320300c013138038140b41c207807142e400200501030400c208240842ca801c2c004040d600c200d081e02e00a4007200b002d542e400c3c03070b5a12060200f00d10504000f04024503807500061001c51000b0710000307510b600c5060500e01034200742c0b40e40040780c44c15201442131074402d00c034000e000110b1310020700100c22044005041090705000350400030211418040c03030140250400004000c3c1400f055449803042403031900b0b500c0708801c459128030b09040000510700c0140c40340c0030a403a01510803a00403400d54a8030598110058411011446600204004601d084510701065480f007c00810803035580d400041042d00d80a00b842d00c203903d02050900000c030114101e6044440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 550272356 1250 550271106 550271119
    0xa0b0f03060121060329101802040b04030b190504150911100f030b040e1e190606090501080303090c040b0310060e0901050c0a090504051003020612190b0f 68
    0x40c44072160140120203142010f01c142032040100400c615040e1603600d0115031002c07140b0b0042424901100c00b6000c6c0c2d880c40c1c0542d0454002d104d41e00031035509000c8104100d10251609664403a0504554042e0380261001c2200c0801c3c0009646030b0110100400d02c04101844a4141a190742c0303648450f404564010658075000642004442a45044e9208004121b80d82c3ca8524a070007030481c01032030040400181c9001d45410482c40c041c1710348080201400c0c000c0501032148840003c00c8903100c4a02c0100d4818448519541d0b01c0c0c4018002050740304d1400410040c0c90300c4042c60a50b20117070846090b940062041048182001a0900c1a92003c950115a80c1864400f081c100070700000768800b014103240000c100501007060f02c1e40031f642004020482d640d100c042204480c0940c54812000501e00b0408020f13924061308119042842c54824261a6a0302da001800302c0e48640c070035038800c020900400c81031304088049000c10704035507182400703041288000a8030307050010080c07a12400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 550273606 1250 550272356 550272377
    0x18010b090114060306130e0f16060504050d0c0f0902120f060d0b0a06051009030b070c1203020c070f03052a0d02010818010203040c0810020a05030604020717030a06050a0b0f030601 79
    0x665030041c000c0d171aa680341b8108802e03684c030035859071595001710f03840760144580c002e81515080018002011542c1954130300d030030070f4200b4040010805628030107071500c0402140104003541070700c0780d100050200781801a030350130105c1013001680500400c542032108032030040200b00d4a448141a03940707581300e000707403c1607620600308000a20464100c2904102403240548031150061803680642c4e00540c03c200c160b85c0c600380120784011702c1c05c00050015040140c003095807406038000d0201c00e8840d40a56804d6078607034005070580003044c1e00640c0c1541c000e0541d003c46003658001080c1c10403c00e150141103250b904081107106280c0c1a0090400c50180c0004005252102c9070036140c0706024029540d909050410380c2864407540101030043c000c0e03503922001c03000c55100701c5440c65244d40351242140e030ba010070040207411140302540c5012200f00c03000226603038000194820b4109100c006a03c0f0304110901240c00f0140c0c000d0320001808012400e035405070003041c4d0b80d0101e0240382544041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 550274856 1250 550273606 550273609
    0x9020406030506190506030a110105070c03171911030a05070602160507050a060c0506070e0d0b01091a0d02030c0402030c040b0d06170a0c0e07020a0b18010b090114060306 75
    0x1403040da8806882030080c582800200d00700000e54403400c1655900511994513001304040c0c4034058901c0060140801e02e04003c21035010b403020b08146e5020300c51100701c1980c1d84d102c00760482c8405007200041d00c400a500c8403400305400c80c00c0800f00c4140343c17004100010201299491040d5a01d00e418000d01180308030030040160121080c503421085a82104000c901c0c01581d03410003801824030401c440003001c14840d00c2040e00000190300100100020b4a901308152400c80c8101c040a802562401c09100032911124038036000341104000007480c0508650317074003842e180d00034a407403042c1c09000c02140581c0c0c00140384090380408840050303503500d0780c001c0e040a600c00c51340501d800502c085203449048007103a02c620110b840814107501d68a070036100143e01d030f4807224001860740c141401c05008404a07112034a500c0040740c01110038000d1076440d4000b0701903003202c103001c1c3d03030004581d0108000f00a000d07600385d0120551f4002c0181d41445424400c0081e43301015006280100004015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 550276106 1250 550274856 550274861
    0x6041d061906090204090c02060c270f0405040f030306080d12020313050d110c151603050c03070c030512070b07030f06030206040b0a031d03041a0c01050f07020706050a0909090204 79
    0x60101030f41c1155a55500c044a5010384442d141081c00360041100150144803401c0c201d68001d0750801c0400c0d600021401440414600140c40903006840b02c80724544a854500c56140210300440714030031501c0d1589802800cbc0d034842d8003d00c0032a00310f000c00b190718039000980041c00782414440940c40c0d64500d000500c1c1035001e62000f03000c9200d1807801c080e40c0d5411018042416003014190f46090f1038080500c8914404914800705408042091411110f85848098100f910038034104c7e1030540e00c42c83c01c0b40740d81c004c001d040c0c5a401005c80c0c1001080710801c442020f4000700050b0300d040060303503152821038000c0206460249500c0c0d140748903421010f54800000303107600030101d90b02c076038859104082a81004c01c2140102c0c3c07400070040d040b03112a150750a2880c0c030301070007981341c6801d100107480c105522603031521585070140710300d1008503030038000d192048038404034a02c043e20b00003000070320302100c590052007071050801c0090300d0254032008003800d90703414013808201c1141c1172010900 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 550277356 1250 550276106 550276109
    0xd0207032f0c270106051b0105040309030305090102010f02192706200d11010513020f040b06040b19120606020714130507051809091b0d06020c030306041d061906 71
    0x20f02d00011400410f41035044005024a100742e150b82038600d84da03818480342212000c0d60081c02003003660000704006441440100004003040c030000c24020a030030281400d9803c810282c12560f015031002000c0d965001e00c0c949043c010709022010504590a0880605105030082e0000c014100c1c0700442214441d411440807090050100e075610514520000d01540030782c3c1840341c1c65402d040118543c0502c401d00f40314800c0d001440c0c40b122589600800004152030006c098000340700b48000254032045030b015143c0801c210308008014841d0307140040c03140510f282c84103d0b05140c00d070140266075000841c841596484124151124151400203041c1100c440416107002c1c1020200400305900c034019103503c010391040c5261000c4590200240810b0888030340b2035551046090f2515599101034100c146080540070451800340d41d110b240c285d074044005614194400000c0c000789061a10a0111804070117000040008501c0100307500c60901900034203e41107888004030404843ea0302c980d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 550278606 1250 550277356 550277419
    0x1a070f0803091608030703081f030219050103050708040506010303030b0d1b03020916080f15030601030515010b1c0e070801060f0e1006050a0f050d0207032f0c 70
    0x80d1680b4000300200d0380c0d540480c8210700301c400868000125044008207940035280d02d0389811805a0311120007a19007032600020590212070400000056114101d04a41400c1ca0744401900907003450005030540b2800f40036001001080000c201c0450b0021034240e054a03450319002c500e02d850100001e040c018540c80281c140b03c0c1c0d280300046220003c9103940c007100e1003501d0b40050f03661500398590303c0e08212000c3c0b81c0031452080004e910351014200e840d50080d00044d0310754130000901e012a280581c260412149580943c0403621420402c06110340106a100c803900e14007060501f00c00341a1104c01c6900701000d841d600b00c4450300c0c000f0b124007009400d041c0001c020050f075600c010500107003035109091009000c4404140f6106260b00081d095840c642c480c5450061113150865645105140c1c1008024090183c1d43c08020f05000034228140a945c0b1030703a4007a5185400500c2c02d0450780e950303058030764000411041610104e1034040a04040f2191900d9180c0d03002e411003003060500c1c00f213 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 550279856 1250 550278606 550278623
    0xc0c03160b0a090f0b0d050a0b0102031204050a0623010b04060c02190801020d09020f121203040602040b0a091706010e130501060b030c030709060201060b120903090a0308221a070f 79
    0x4a00c1004003c046c2804100c1032034140200d0f02c60704246011a000190428010b1300100940401409441d60707407074105116030102c0d059041c02e500d405e4100c035401c0a0542410702c00007464944660300d41e00070b1b4013410841d080c15292a1900a02030304102c1000340081c02131058204040010040540040041c010707c0c00a640d01e0241e0101e20303004047c1e80d80d0481c46000d203450400c41c82d0030544d83c0c0c40624164400100506420b200000c2d10581000340300300c60711602040302040e8011248050072042c00075443e0b04021500784060719881c000c40c0348515402d94000001040005074050001c0c0d00100101ea00031040300f40c81c1015030142c00c503a008004100000000d20001d1078854000f1403003a5144d40d20034114580b0707090200c0c241d0780c1c83c0c41400b42c2c9078000d01c408036007950650030f171a80010110b81228902010800400c1d10004594021b94400401050701545114002d4170005007518002d202d50500707080440726180c00160648540c010200820914200200c103062600040e4029521 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 550281106 1250 550279856 550279859
    0x10f03150216050c10110d05030414030d060e06030a0b06060f0417100b09190c0912152022121103010b040c080f0a1b050c0c03160b0a090f 61
    0x503513610b0301840d50482c001c944d11002c0880192150304103e107004a80c0029054504c92010101c555400c054000d651500d11107070885013071402003000384003403003a4a5000c50070030314000c04101210b40081065000e0b4201d144804002045882c1950344210700302c4641c0c0d280c619400c1900124010350300821115105070907100d410101c00981441307401da1410302800001d0303802040c80751410042d180459902503c0900c00d500f50b2072074200c10307004802c51900c80c0d030300b942d5200203d446102c880c0e41600c14500c55214041a011039000701842c0303101c07681c3c000001141c1c1e555120743e9032117000040c0411a00c50908100f00002c42e10b18400103191100303445c54418a07038182150403400600e119031013586000d000083e107007414005c84101c508645c9440300c0c19500d414009009400091907262002d07610940c1070000607040f10f0170740b031030b440640c0d81d182c5402d601d800140c90121b0400340075119038440d00507603140408010b0060241d40c04446150b4856081c19001c2c0c3e08004030303400a980752402001c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 550282356 1250 550281106 550281113
    0xc07150917070804050a090e07150c08030f040308060604050a030212030c1c020c0f1003020d0605151209340506041221080c1b03070b060306090303010f03150216 71
    0x142085e51000c40301000c00958850071003048507861208071031180c100c01800c0141d9040c41c450807114089030b04040703645c06510ba8030a02c0c1940121950703107160b4401c02c28003080c564003403111a4895001d4629500d06401c1c48000b0f1450b150b14403000b4030403a420b02c5006810324042c02079071020030250b01156070420001210207404403d68580500502c00d030001408149000f1501011010300038103642c00c2d2000e4010304501940c080003100516503101d00000a12f034441da50703005244651782c081c0584441c00419880d07081c04001e000402c5035404003880c80e00040e808400071b00a1000e0baa1002255800e03828805502d941c90360000b6484030b804100041c440086c20301001c40d003486440c503684814102100310044d01070301d61140c00094150000212005d04503001000396019030510031007810300043da03080c030716444014101c0b1865000d80034808541410001c40c1c0d0042e0f808009942190b050a01002005601e4880075141180140d0030741c1544c0c07020350403185801028901e4840ea0142c605 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 550283606 1250 550282356 550282373
    0x415320d091212050c160206120f10120206030a020a0c0506041101261609080601090b0301062702030a0912020109030f020c01091712130e0c0715091707 67
    0x1568400403403e000c560143c032401c14440d1520440907105018144804403011a1048145c060100c1e04548200316000380700802c01880c0b0b1141000404014452825100c07603440c1580640c00004210346804080006039640003d03030b0340c0140350b0f410058986220b05e0040711001170401d03000cec00d14090740082c40705104903012410024402030300c4905c2da03407403014618419080798541d400c050081400c00308029890300450049480c08900d0020149600d602516080200a0740b0407441907a80d030317410307030301d182428081c1c0c0000388004004000303041c0a0880c031001600349e035602c0348002d5074004001345007200b503035029000d000d4001d68030020700d200106010303000302103440d400c1d4040f861903013210560b2480001c0c43c000e50101a500e24407881c0c502840314a0001200340004058040c0c1010255400c2104020b0400894444c100e03031246413030b043c942d0b10fa4090141080c90604c00402020000c500d02282c00c092061070840009421002070500785c00c031251070010804142d0300010147c06002220 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 550284856 1250 550283606 550283633
    0x30b0717070906020d2d050403060c021606210207050604030e09070906050d020f0a021c0f05070209040507090f20090109031401020706110415320d09 66
    0x100110051529801c8080d56800c0d502c0c4201c400607400609014180c0c0c2c8991b10405000e001300c185442140c01c5801d144500d0b0004201c40000a030005ca4100240034042c0540380f86994280082c28031701c00301d11500060383c0d0040c0100405d01040d0340d00003490000850800c400003920a00c21074454500b8a03119484002c1a503040d0005100900084045d280200085000345010785a01c2c0307a55141200c2540c460701f1803005210351a6080c00202d4964800100500d07468003554050b1400420021020f0072a42104a5210402c14400c1a0805a07038001080780c0314950101daa5108550710761800034901800d941000d80310394103241d5a000861800e402104000d502c1c2c3c400c580c0450800c100380b45413402440052070000b40880701c10070110309903103298880901c00b0000945400c40c0d5458440035900c41c00409a04500d000078100446800742c20600074031540341c0307004030300c4c2c103822604805104c09000030224044030302c1c5550141c1c441d1880844100c140043e00500102466003014540260341 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 550286106 1250 550284856 550284887
    0x3010e0910050f041505060108070c050a0506040c0e010602150a11130b030108010c03050c090d0f0b07021c26090a02190e06030d09140a030803090601170a0b0c13030b07 74
    0x5060205501d800b6601070300740b003048180d4689e40c850703490180461301c2d6603900301d055030280190200340f000300707100b442881c2c4218050354040d27444516040d90b00ca50100d0580c0541c046420010710030b8440001e80080581049030f9410200d124040721090b0456803080e00c3c401244100c01c03500010b01940300c030010350304866210000304941c403403144003603040d11401ca84d0342c83c0c2d40c00108071445c0207142c2000304880e034a000b00b01000c082a410303039842100b000241d6090000d6031105080c0101042440c200300490341d4036180103080030085000003400041c020f166078541314171100014039030ba48108003041842d41c00509203900b14041d15000360070303d2401d00441d495003160340000b40003424005896100b6083e903070746940d03d252606000018bd407941c1e030181c0b035015a0a41c0000082000c0d0406180250f1840018000a500d0030440c0c1489510b00400e4008a4000c83c0441020480c04180b1682c00100e150450f81d03268078191031400c403c00d580d000100207210034070500140c160b00103c0c98080b01c25 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 550287356 1250 550286106 550286123
    0xb03010f09050304181805030705210706110d06090b1e06120403030f0911040501060e1011010e070816090203010b07060b040b0405011509050607050303010e0910050f04 74
    0x900e08100000d8412001000e402d40e88100410070038404c1d00844622088030300b1300c00148050b030041001103546079407a03084e10a607001040074018441e00b0f0109060801c030013035134442c01e54240305003030407580126040070380625603aaa41540c01c0d07020340e0881d9071242001d01c00700842c5450f17a51740d8000303004d030407400d0780151128802d0307882011140502c0081807074007c141d2810520000c41120300e039003000b4004c0701010f448414140b1802d03014003409003010f105032400c205400d0500240030403a20164040420441400c51820582c0c030340d4440300840700f0884c0340812020455403072460142100307103ca02c01728822184002010380340401c0e5010007460b110080003000344c1d11190340302640000c0c0a04401494200001d00000301c0950013044c1144008c0c101041c041501d9000904581c804da01019240854220b44981c090f0301036540d80180c20102c0d001e03030400000740c90309566400140100c120314040380000c40c40072007080101d070b001e04443c41800c1c0000c2c5051901c5410551094904588054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 550288606 1250 550287356 550287371
    0x70f030614010203030c13120b0a0f0615110f0d0807090608010807090e1f0c020f010207150e030412030306050a0501050703021c05071401020405011103040f030807060f0f0b0301 78
    0x50500803110701114140d00550031601c4d20b80c80440c00342c0c131504280041440b800030000394a40c06000384030826024811010141c50806505130640e0700902521242c20700d82401803000d0000c1012080c007101040c5040e4001e030002c8030381c0358600440c90104540e980309154403090311690101d402c5101d40c071181d5803060348035500d1354280c0f4088028013408410f030b0000c003000c4c81002501c0c0e0280c000000c59400f11400281101d5218450150003144044216101c040310301d8100d40402c803001e01c1050800086140412585640904c00c2903560351004558641e40b21151484003041940e000e410010044280111940340140042c40c261040a01801801400243da0341c015400d030b8402d10b801d500034000c020201d00303055070004041c0c036170072040c401e09200a034045000c03c9440b01c110030488d0001607456051000140150701c00e48500c4481c0c0c2c0c42004103102e800c0511628904590b40505410f0b10342c130b950b11300180505001d0080701101d034a080c0b2043c0c00d03160a50800c03a22048190000c00408 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 550289856 1250 550288606 550288619
    0xd060e010306051e01080c01030207170a0f020601061d0f041d010911062a01021b0601091104050d200d21142203050a050a14060709120c0509070f0306 66
    0x5801c02d1146d50712a070800c09562080354040d03002414036600c0760700000c80101c0000340740056600240c2e07a041c00180e214080c01d500c0ca4040100324050001030a150340b000051100110700c00403111255409018007688110060b00c60742c1000c980d0307148540c81d50b8218542402d81074001c0242e04000d6640080d2015003d415041c088102c07500c4542e04410f007410400800b0320782403000100001d25490f50350130400c0d035149010721f035071044c0c5048000703010f0091035140510100030ba8080c00f07840d036003060041104000070754a5001149170366900100852003000008000000610a1040180c001030200f08010820a0100c03070072564104060501d1000055200122618000710900900201c0c1c00c1144c030b0407100c0c5080b80009440c1d68001e015581580720755826041c86d0f4203e40c1101c450b48074400300801c20500c40225001031300d440000308a9450411401000b008562280d80c1d0300075150b0801c4e1080c801d850904201412003d03191598a04101000414801100c80d90740d00080c03810201003000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 550291106 1250 550289856 550289911
    0x918130614060f010309020a0f1503050a020c030405220911090708220c120305040f090207021005030414010903020d1710261507030b01030203070903080d060e01030605 74
    0x315406003d8880c3c04844400650082981c000705036030045c00b2a40c0042d0003070020342e081b0003602495058400f1030151550243c141d07140034000d4851517005125207002c550000045c0e404951041b5008145400700704200300c0c07840d0582404c404840d003040c501400780311110710a1044d110003560032100a0303444030402c441d080816a11881450301c45502038100400c441c0d4400030305400340c14100e42140c0e440c46005140c107450003044003c184046010001100c014010b1002099903140035072038820b0303070782c00989452001e00052043c01000300c00704080c020340000740c11240c0c8503c00200071041d008d0401075a99500c010481000400d03200f403800d070b504204940c0c140101440e1074494030031401d0624200310305120102d0038003040da401d1b80c0c0c3d00044600308136030b0400c411200201c460508050324000e0a44980803800c1d81032600400c00d103e0000c0e48401c050080b02d4000301c059403592025030189003d84541c5c0d01c00982d0f00100b000200510505078040d5001d8849001ca2503400c00a500083c5034 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 550292356 1250 550291106 550291111
    0x1090c05180a0b03010222030203070503150a0c05040315050901060501051c0c110a0c030203060c2502031e010b09060a0b07060c022107050f0105090c0103020918130614 74
    0x41d80700710502040d00b034000d5401604040a0050016051079180d01d042c21409444044842d12001c1810081096041c14480b13880540340c150050143e201c490030720fa154126028140c00b200d903503114a005500781c030030000d0f540a1136001d54061081d10b2841d0007003010384429620aa80c551a2003000181d03903004404440640c1c2c0480001000d00500105038001040c0c003940410038441d03803600300300e100942484000c2c1030341e1184103034440701400c60050625120380240007000c181c404105e407119101c210021603001900c50401c403001502d0700e1000c2402c01c1c107810608545411800c401000014064100200103c01030355410760355600c1e5010030002c8120392107601c54144003044190301003030103504010205240350040300c103010b80080040503514030144001b11401404182c2c0c0c0d00304401804a69100b0341c2981c020701031410003400c110345502c007511907181490b41c0000d0851154890b541034072000e03550140703040000d180044a10443c2c01c0408030849200380f8040450030740a070801007890 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 550293606 1250 550292356 550292389
    0xf05030a0b1504050f010603110a080f1806070504240512130b041112060402030d050901120507030501080d0207030807030309080d0c050a09060207050609010c2301090c05 75
    0x201203142512a485180700241a2016200c1c01441841c1691158040c590040089080180b034542c0350140c01011200001f018a02c010410011004034560009072103400541c4141c0203807071074035000c40c0e49006004541c40f6803803a008040c00c120606800c440900226410290014181d560405080700d0210500003140c001c41c000f408074204400141c0401c0c2c0d4014078080742604031920300c1c0c60722034011030304942c2182c1075103503c0c61151050400c00f15503c5640d507030200601c3d060401d9030010b501d07a420046d81000700000420541040c3e0f1294003d00c131b5004030f0920400290801c0d5030002e0140009020744007152165442c0b1401241c800545041129000341e0000c0c03c000d45550110098001c01c50155801c20081c07142c04403600322f511911104903480d466050340d402c014500030340b0201041e40500f041d50000f40c0c040001b61502d9040710504002441c04840101c1140b8082212020141e803a1280602d4240781494801c015444020030501030b15004094540d5401008000c003900c84200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 550294856 1250 550293606 550293613
    0x31e01150305071401120f0b181605031b0705071a070503030708130b0a06030201080a09030e0d03020109051204180b010203090d050304081b0a090b03030f0304060b06030a050405070f0503 82
    0x400071020080424541310300145400c464000d51440342c2d1090361140e4000007801581ca058400c01c03480c0403104070011180d184241c1c40340d40b0b44a0442103a01e014802c1000500800000103404e40707035940ca1096402c1d01031911540c50b0041e03424001d43d149198000d5180070002c9040ea08485162842a00c05143e4040d00442c510341d1082405c1351805c5003d0300300381c81c040b0500300304000030312880c0900c0d119014640000647e0ba241d80001040040080c00e1203124615010f090f501080d80a5100c0010150076100010008450b241c12401050380040c00b0380107010b04080d8003040a01c0030b00402c112600c400c802000e100040002c0e401300c4202078206400b41e8410861243d4a00346601d150100034015001e80c1d040030359400c2c0702c500780301004a5109152131124586a1285412030080c3c01a044030a0b0070842200564003207540c0e03209501e817801590390302200050402090360440302c50141d000d01020b840303041c84503240001d404140d404691901602802150f410000c40c0d40004031071004005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 550296106 1250 550294856 550294859
    0x30108060c0c0604120e060a03020d0c030e0a08090d0b01030b150301020a1706011206141212041e12121706090106030f0e010c09081b0a0e07030209031e0115030507 72
    0x54103010349517410680b081c040c030310810b0039007983d4000180441100a0300c000d640d9000991030303081200d031146071007800d242ca0202d04102c41803000a06480c070030f91008607103641d0b480d1040010311001541000504501c140d1700080200801907091a014000400c5107102041402d4101070a07405102c00b800b00241c036114042074214142c80b1059086101810003588003040c900040c4140d03403440e00321000089505124071003d0808001c3c6160840c6100d0203420464241e0004800c0c512403480341c0c0c140e001070140c03121000110310010750002d00c1c80810080180381301d85032065000000840400c00f00c1d5a0342d804055030920a010345124000c02000810a40e0030004264000d0103a001c42c0c884a03581c41c00e0420203034074244030f0300f402003582d42c4400e038902d86011000d40c031705001d140c229114084a514814440d445a2012105840003c06045583c0d5034485040303000b40640841250300d4403c4000c4c2d109460304107a40301d8820007909000f400008684168801c80252501c002411030b48841d00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 550297356 1250 550296106 550296113
    0x60717060d021c03180504050c09060913020d0c110303060306010603020c030408060103050703051c020c0d111309060b0f13090302070812190903080703140f0f030108060c0c0604 78
    0x361031480c82c8010303c000102c0e0001e52580422803000780d0110f020503110841c6100d03102c0d00610120040500f01d906100c1072418449a07136180c0200d1030141d0044402084109a90380e4080c0344480b03801c07041008544821a01d07541002803c600c9041d040415002030030031840d1039010048a1140d18050020002e0307900e0070004400039032015258000d00d003c18400030958800034495940218003a100825080c0d0560400f54141550304101540c13079448000f02c290f6450f004140d030f4205800441d107800c0b80c043d07079090403422200207105150344107451081520501c205940a0408203000704401c1002c40f4404051018420340b07006900d50118803110490300c80d0045402150b2114440c3c4103852203142d80350a0203103041c0707851275421103003c4003040d011900c050b103000c001a111441d182c107202c030501d142c40d0807016201e84000a0304000d020442c0c100c1c64410706040300d6050390b5240703045d50b960328006d03044441a0401e00554501d402840007003110300814000b0340b144007600328040e00c2c09407569034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 550298606 1250 550297356 550297369
    0xa030f0c0512040c170102090306060301020408060112020619031e0204120b0402180103120e030703020a26071202090f010509180c1503010510080c0a050a030605040c020f06071706 79
    0x42044038488601613000c0342a14105417001800740f498000540c5554604040508041000f44854020381c0705001c2002944400611113044421904403401e0211480c008104240720381450307904545840d1408201c4294164803c4901d0903001c071040aa2449400109003a807080d03100390107040c4a004103504c081141c107640e40b0f40162008004d81c4124902c2650b141442209900648032a048002000011608003180341c00620342200904585070441e070000718494420b00458036410b00c41e004841030501a02403002102c000181220107403940c55114540c40ca460001c1280120051004104500300c04519203060302c200402c450340d1070307580340d030f044643c03070318080b1083e0f911700c03454001540607180d000d012000a206c0b101c0c40c0e9035030341c10003040c400301000d12421070007080403c07810807105516482c1505d04242d0b0340e03d4003568600d8850800c9024240503002568001c2c0740c03002031039100f600054080d403440142d00a88100fa80e86000586070300340c030012070380c0019101034002604c51a064 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 550299856 1250 550298606 550298611
    0x25080607080114041503060f021b0f03070303052a0904060e0906010603020c07210210050313150b0a09050108060108060c0f0702150309010504020307170705100e150a030f0c0512 78
    0x2000c117036400c0c0d9903501c0b4442501d10800441c040c45500280042000c070450740f2160004030810b00911543c03404006d019a40d10500001a08260b0750328041596102c0050300e0b04514000d00a480c0709001306000640c0b003607440000041c0c0706074038000380011301d075040028082c40750000b4000740501d6864040305801a61050001d00740b54004e08501040d8918000285e4011080c00b82c54005e04890368810302000b01800e0245400303000c41072082084c01d0000410008049a216203490240b10200c003c142c040d006080c1543e5000d080008040f4800c0c095900c614100c89042084a070107903a50404a80c032200166429200840300300440d0a0f0084114000d02c2c00a10290407500503d60b03400640c03060350001e80704c10480d81d4440302404154039003084450b01078504106401440b000e110040c0382d890980d803003164000c1c42c0d50f1105101c41809009613290010014001509a00000f10720503450360001c031001021900c1d003000d030b01c80f406040c414502451300035294940740014000c20b03140c21a000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 550301106 1250 550299856 550299881
    0x80c010c0c0512070b0c0c031006120f0203011107050105090c0d02180c0d0e010e010b03160e13050118031403010b25050f15060405272508060708011404 67
    0x60040014215417810001c0c00444940d50183c4801200790080504140c140301c1d2111a40341444000d006a00b50030b801d40003460750200030100031140301d1010a0242c80d400142048100010407110203128042d0092031044418a050ba861840b405003000564840d08001a4000301c140c0400b8014a0140110307640042d003c801080c109207110130303540250b425028000c0c02a03511074064a5107202c0901620005000450103881c079095145420360580d086403003010f17480d044c804082081c0c821508101d04c849a000b0300203001c6061400c114502281d14030078110000b076081407844031070241c1c000c25a4140c0702050002464110407020500b080564485031002c0035003e40403000010787c0030031655071160700c607001030700422140002e0003498080050010f80140d06100410080e44040d07510392144c0c1c0c5046d0b0134a1049041c521080e45009400c2900c880d6100820301c141403003458a1a51000b01c0e800c000880d0280c3d0f84500d4111440d82d420310038015400205d0303440001d640381070303040311802015 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 550302356 1250 550301106 550301113
    0x10b130302010c1104060b0403051c08191506050918040503030420191a130905090a06050f0f090a020907111906050f1602150c0d1401080c010c0c0512 66
    0x1e8080000e8110f4105038030140c7e500c100090108104407090004854061641d610303a540d003031020102400881f002405521010001e50040c0c600c3c55803a44031814044510380300560258403014060800d6003c81032a0380b20701a03040ea54403c409691000c02c0c4a075070b100d400756046480d42e5480c01e07c119500548034105102658550a450f1501d0000101041820745480e903014a04441c07421410910344102c81000700c2003221400c181c4110b00d0324030459041d2903001401c0c0c0e030f60400013801c041190300c00400950419050148015091110602400b60036441d10f00c5a2140003949544441c5280000e400c00909000100303482d00480304003008101420030342e160002e10b0b03641101e41200d40c640442c0c200e42c0e16024018100069950b1a84c00200c2c1600c0880d06081924003954501c0c0b00340200107850460000640c601d03100c40c040c0d0307072032141c085420f0003401015650541c0040e000d0003006918420180240d02a611503000183d0054010369804103c5080c601404018601e101c0516002e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 550303606 1250 550302356 550302383
    0xa03031413050310240501050412050f0d1d0402180d021c030201140c04050306180703081b06060618010309020d0b01060c110103090c050904020102070806070f08010b130302010c 78
    0x450a106a41c5240e644d110300040100e802011030005401c04011403850110a40d81406140d0b040400c8400340c82640c1c00b203040c02030061a04074035060130448061180c0c000c0c40c80d905001604500d00310410303000c0140c4810700c110790b00148022405210b4100020040309410380b011800d03e1070715800101d0000c0c161100e5a6504492880b110300926402c40041c0e540d203460036410041a45201d0300030300448812072802d0719050000790b44070805004a4130003454031060724824041049200001c1d94440c80d03494030751004d00920032011403001d4003040c850180800188403803825504a03041090040d0401c4840100d100044008003803d40c0100d8014800c641c2c09404108210140350082c05148e5600d0b01884151400d080f41c00e0f07140e1010307414182000001c00000b450180d002c4241c03a019200e0003144d86e00d500040345083c000703500250780c0c3c1c0030f50030600542a6200001d002007003007a448180303150742e030752010045c14824149940807003804054144015071043c203104601d43d02450308140e005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 550304856 1250 550303606 550303609
    0x201050f06120a170c06180a02060c1501260705060a0c05010b0d051c0c050709090f060c081006110303060d03050408011112060301050f07050c011e0507030b0a0303141305 75
    0x341200d25014141c1c2d60101700001c03905420003c599010b0034040014031202c0081ca040360740daa200e01e10080c45030300082080e0244040810400d1005003c0540e0281e16582d154070300c940303141034003881e0701400c0c92510801442c0a00010401e049540181240e440c20361003003c102c90100454204540315503c0b0b1142c007071a5950441c2d84a0b02d507020fa405002071171113121044600803444002d070401d01a00c02941c0010039804140d00301154140440450080c00e5813805043c00344489000405561800700b1400c41c8503804420a4850703401581c282c00c0541e1104000e55030118010540d8080d94403c00020700a27040c410720349000c092081c01c0031420940c82d910004d081d1034104904c03002070000456451050024041e0694000506500070045420300d004c10400d0518000e10136400c0c0b110004100c04401d8095020a0030742007280d05400558001e00100d02c05000d042c0e41c41d074000784c10f06250509a24010100c00220307a41034545940b81044484809030982100d0a043c01d0301c1100007000455 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 550306106 1250 550304856 550304873
    0xc010809011e0c08130b010306050703020c0d080a050108030405090c0901090308040602030a08011a09010f05090d140d030e0613020d08070605060406090b030a03080a060906030309150201050f06120a 87
    0x1c0d5030400b402051040e924100140a4400103001d8400501060891404034401421241c10340307801610104032640e0382107080d0042d03ca55120a0524071600d0311604440794855600ca001d280d15110900842e66a0f50140d50b40340214040c41768020064000714803241018130081400389810705103150040e1740c0b52075024a6401c9907020760096003001500c00850f96021a4140c09082440144200d40c084a40c5005840c00350380007503818400080481b114403400389081c0d0700111002040000c0c0c0020b2458143c0b00000a07105d05031030347c0300d1804480030250290040301c00503018a402050b16076200019403010120601c0142d820400750100ca04c04109800e00170419240100d90114460030a4002d207c2150103981c040e2440a280801103121960042100b25015800d803030205000d45640800800812199106a84691901000008058201c1030340000c4860710b111170000600001816801d8942c200d5480442c0740404000a1052030a0380f0030303405884800c0c040b0b0300550396660704d0500c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 550307356 1250 550306106 550306151
    0x1309020415030c030b13110402130f08010c120903080f07170a05060108180d120f0c030e0d390507140f0f03060f04210c120806030c01080901 62
    0x2207400002e50240b0a00c00c008141c07a400082c0407000d51171191031b03901c0309006000c00d8580f048c030950300010181c2c00400c1c0401850090020801c0c83d02c2055074640c0300500800b021003c180114040c400c000c1c03140041841488000c0da05a00c0d1b0071696540c1e40700140d6080340060072482484605400d1070024115614000c0c411035000354001080e0810000152502100500800d00742c00f884130741140d40762011820081c1484a07080051000d042c072890400a004007030a079140c004d251900c1088e6980c0d00d500111074940c004030948101c020081c0040380c0050300c06550000c5040440300d25645120400701c0003682e015140c0c8403e0030f22000b50381740c40c18403441d680103000450724000d81540301d1400c3c400c00394007140101d90200340003c141001c40c5c0c0750301008046900c10400040004c041c00f501400d46120030000c2244006000b0001304090701c50400c8400544141c0b0200840e100f50500032001340e0f008900040041240703e481100459042200030081120795480d160324800031090305000e81c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 550308606 1250 550307356 550307363
    0x30c0c010207050321091005060301090f06020d050105090c18060c01020c0d1808150907082406090402011b03050d060e2a030121020604120209010b09130902041503 72
    0x50351030885c465a0140700e042c40140c0ca001030b0122040c0701c1803070740009800d00e840e01c8001000c51242c1da00c0002900502c9120400b0b0034408440d0001e00c10410f0301d500809141e1940c010401150340c07504180022994202c0b40d103050820f0030400780ca1000340b2419555203041004010526003a21685001d00b13a801c44418150598401d0099005c0d4503040148a9504800360307400b400c450f0300d01502141d803480180115480e0003da4004600c6e000d00070b0141e000070b004020200c6010090352040311003d44c101042c02603c6e0000c0b080402e007a40f03403105400740501c0e0142c0d078940b03006040040c4d071a60070150242c21014020100b004002c59141c0e03010b090002d009800040c1c01601e4071002c8103110700d03242503004442075044e06002c03652000080990f419903551907282240d2070000340350018003484012029500810104000444c80881d1000d02041c0c1c0c4250307045092a40c6e00c00c098015405090381d9a5400380d40101030004103e0f40d43c1c0800120740c0000c00102c1e03c0301d41d1040300d090307100b540d0b003080d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 550309856 1250 550308606 550308613
    0xf0306020910050f0d05090f010203090609071203080627010b0912070e190204031a15030a030905010e0d060501030f1202120a0c261801020c0a0308030c0c01020705 72
    0x107801e286400082d1518108450511600c0d19040000c0140140710354202000002d640700c0106c0d540c5841003000840049095001710f560f0700f003500b5416607845c400c07529000d40d07100d0007102140070021104c00420050303068540780b101d5260340b010440c003142d0b402030315540079038070742460200d100e002e11450f4000c00312000d1640d0b846211030188080c50640301750000c100c0d80403580402c40c070014510361a0340551090342d509240040581d030b840282c0318951014266451124505494a440081c4c0e680a032020203d40800105868203240d1903014640c00980840c440c40d000300115402413000c034042c04401000d50a00c2080c3d50b68940c200d0384203800542d05100000410000c0200880b050783c070320003017400181034940c00c074030207030316203214402200e020040100750034002c000f50b9030010018450103072018018100c00c10385030b044035013004c00ea411450f81400c541c0e01283d4000b00d2030300c81c0c03004054a00a5800c0c05c40d01d410105500c0a0f250100322102040074680d005001c0c4003520000f840364010307 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 550311106 1250 550309856 550309867
    0x110a02070b16020d0f20120a03080610020a021f0905150415030209030105041113060806060d020303070b0703090c0501050a080f060102011104030b0f0a0b0307030303150f030602 78
    0x3454405250001121100100400b1045051110024610550440701c2025030000c501d4001900d01c20504000e22050610081c0031130405000f90344c0001c82d42c1034031400d038020015511903a60b08060f21001d004564402c0100e1440e06120b46004a018014011641841d40540c0450510f21601c0d80000c541e8420202c085081d0303600c0000e8900130081183c2480f03203243d403d10100200d2049100d80303410740034800c2c0040286402030701518401e5900800802c030620382070902105c01d0340414030103480352845001d00f404400040c8582d50550302c40034004c003500c1e03035043c080c400e21041d101e60036680362109001800c0018150b42e41e151007105180d60200300c41c8290b160003000700400e034000c641486001d012220560303a1041006910101410740c10303000b61200c00048c1c2c01020402440c2c0702000e8002804010301142400c038030300070054110749141c690740b981140e0049840b41d44000b54542c00c01842000402c2c4a60000800354080b0545070f59116914210141d0807031887d801192130b240c01290 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 550312356 1250 550311106 550311127
    0x1a0f1f0203090405100b04060f170112020306060406290c01020c07091505090406151802090a0f0e07051c0207150b0a0e0a0c1101020703030e12070503040e0c07020411 73
    0x4c0d007604100302c0d445100b0401e007050300c801080c0c004c034000d00081000070002c00b8040c81c40b400590a09c50380b43c81000b0f005584030b0b001d4001c1075441d000160702074402c80011601601300744c800d02c81190b9401403541d1264460030200407032010b03c80036550300c0034000c0c00600c110010a1008000320004034009080e9503140003031500035540b414105140c1000783c40030400003600d03a004c400da80151300c0300000902000030b480d1080719251503000900f6405400c81c01180c0c55404d0341c02401d0648084a040c0d9a00f070342d9001004a0300383e035004030003410039580080340c5c445004601810719059240e81031040d85d0103210341c0701d040360001d1500340c5500c20601552a41810300d031086038440c2005403000c3c000d15040c078450110a0741c0151010308030340c1d5a03c43c860310285c80351151003400894140250354680d11810010041d214540211445005200300403080c2690242100c0000b075204000d942401d2620b0301e12820307204d0091482101c01002c110384001a902c5d81f02c0c01d60500b80c02154261603901005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 550313606 1250 550312356 550312361
    0x601090b0a170606010e061e0301050f0604080d0c0302031e0301030b1f060e1504090e060c040e2710141003050c0415051201020309010f1a0f1f02030904 67
    0xd01101400b810118020038048000c6407a59000600382440d07248240355402299061044440524242614040c00840e4600c0400190b040320380c2115441d0303002e40715108000c01031003a8840c0e4129540510450b0701d5140c0600540c29119020f4010b4070b04142113000307420000b0850303c5040e0101080000140104135100c004160400081c03020468001540d0340c0e60320401041d801400180441790900140a0f691409591500040c62420641700c4c0c2c3d9410780f04000d000340030302c141c91a011300341c00907810880020a56040350701e503007410f8056031205403075960081301301c580c601d0156031500304c02031040c002040900d07254070107400001881b1b0442c00c1c00d51354102e0003512140c001000501c0c1040440d00c00652001a07020071a00061171034400f2100c01c0407044e0540c00140c00486c2e1450b82c4a0403001940a1403190100708000d01150080c4144901246c10301076404228071021580d8041c0c90820700b40480030441e0142c10100c010041d181254105c0300b01c0c0f511800107074000144e1440c0b9044c0390 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 550314856 1250 550313606 550313609
    0x30301080601030615051c211d0103020f1e0d060b0307080601020610090e1c0908070603092102010b03030c010b011b050a0b1005060a030e1b150702030a050601090b0a 73
    0x250a04801350410b0001845110003841003640000d4501c840c1e001c0c4100100c01611482c0c42410907240f280040c0c0020b400612009c10b003040c01b410861078841154003a0080383c8500c8802d140c4149044046190821080c8183c242c2c556002414004143c4001581c0700d82d801800c80000604e0b00ea140032200108100300040c202d0781150014001c1c0014000c22100315000e803080c580b400300d00101d41ea11814500143c4032150400841030800c0b200b4000d8210803100c2c16203030010191000651580010703002e82d410190000c01200c102c070350254100c0102580c41801802e01d200220b40c42c0c03440800a851078010320183e04007650b5403155500070350781210480da0907104c44407010030740c0f4240e0f0b03c80c103031242c1215102030008802d020006420b40c0505442c040505402000f681e207a20303440d400100104030074060b82840b4800c0c48800668900460184520303950f00800c07d2058040451403101280c001d04812600361151144090004d4010f020060182c11071580c005035440d070010400141d141907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 550316106 1250 550314856 550314881
    0x3108120301090f0630060c090806150109090b0429030d03050105060304121403010f0f170c060f090a0b0a020d08040c140a05060c060a0509010e100b0a080303010806010306 75
    0x1c1c000e08100c00a000c07020f01030759a22880c0a8154a40b0410185c407220010385001041280f070410001c400e0341d006680c0c00c2c2038580104c1107400030364501c0f10001618420503035850210703111890400c88405076070010b411410020b0b2001c00c0c09183d84580f401c10400108801091160b01107600d01103040400060b542d640c2140340c01d0105516041c0442d142e444090005004030140d0542003030034500603100071b1010184040310325a2581c0d00c1c90802c0c100e0469000701c44018510384030002d07198001c000104142c50f6860083d180100340700040044603404100c211442000600c0600c0d030036503800c40114000c05c218802682c3e202c100000c02410040c5401410090195040c180804260140030301e00580301c40c3d0012444a61107030300003440c0d1488950090303a01003000101c50340680008504240100342c800b50601058a50750007540c01c0e40e541c1c82070f4207440d622207401072460044942000c010ba410140425040c940c5403a00181542e00c26006440c495004030010020411075200700036400d0741 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 550317356 1250 550316106 550316111
    0xf0c06031905071101271403040b07050c13050c0901031a030307150c03050c0403060209060f0c03070501060b210c0d020a020a0c091104091e0213060210023108120301090f 75
    0x500c03003980c1d0406e0408000240503e050b40d1031541c1041020412500501444034540b5110240b43c5407160340c1d82210f0150380e00511000d01d140080d880d40f8000d49016072030141c1d400b03061801220045005042c8074070407030f4404100803d611202d4130148001c00259028040c549441446c610403502030328038a1000300f0816217040e00304481500d6080070b607802ea030703030040303016a56644880c006581d80c025000b2900c2c3c0e510000403c103903040000001050a980b00f20000e019140da200107000e100e024481e402c20340e1600c00c0c050300544040c940c0440f5441500110130030b0501140c008000d089801890690780960301051954041c0000c071155100103101800d0240300001c1c0c40c014081041c0a188550000c0c0b9496118400b6000602e454103440d00780104c00071921442d0310100d1013511031680c4a00d10160040c05162031001a00d80201e58140100006003600d8008041e28001a8a2818002c40c00c5040075040805c10701014400c10b007020100b0001281c803541000b61000c120344040c000400e0051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 550318606 1250 550317356 550317401
    0x108090c090c1803010606050c10050103150e0a0b100602070906050d170d090507060e120a0f0f1203020d0e03161707080d1b020f0c06031905071101 65
    0x6540511055000124010154541055950010f004010010107a80c503500300b40021a02640c00805065803000d0309040320fa4071043c030050300d070881d0820b000242c030054080c9200310180600d50801c440309035100d01160001c90303080d1111050104e094582c01070b0502105000c1200581c1044654040d01d808a01003081c646440005510400d10041c014201c842501000254010000c1a42c80f0342d581210180304110003031400039140c1a480c098a40807520700048a401401c0401819201007001c034010644003445840d02c0101c0c0c890030310300300c840400782403034080022922241030040b000c00740c4001da01d68009241c21003d440364a0611501a40240114140c91076460343c0021102e030041c01014982c0e01d01d44e980d003a281b046140144c151800060b000b0144055688042c1208060100f010042a00310f40308a0701c0d00014540f01155038418240d03552149402c000a50308408001168012021880c0c010301c00d03918226108004032f240703d204032003488420f0040c4198181d03000540803200 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 550319856 1250 550318606 550318609
    0x10140a0335092d010c0c05130c020105070201020405210718060320010c0611190503150108060303040303032711100f020d0507020a050a0b0438180405070e0108090c 72
    0x14080007296040100200b801c00038400300c00b400c0e03400ba07d030190400c0c499000e0102201e003d06504402d00d0019840c2c440050000c620602c280c4080d603100501406e0740090081c01d0800c5051420b50509180c02001000038001c00d02c01844d00f0032640c2540e010444900d10b00f88124034942c003d01144201540030484249a0380c0961503004480e484200003c0320030020780348522600400d00b402c1041f03050742270a003641d01c0c3c0000c051489803001d0b23102c103090003c0e4800112441e0ba420750f80703960141d00c10301c001d0000034002d421004110314150000c8078002d1854072107a18950000c50107542416514411540d641800d954076425040d20b42003008520800d4a0001d5a6020b2004400c1c2049000708042d01103507250321380200104070007055141d9282c0c0700d100d10007059100c2d01c106c0c1104051200482d00500107075407000728082002550b414802c0c081d10800c0210350091034007030407402603895a582e09039a9445400d000c0e0210b81d4540e040f24100d24005012040098601740845d0f1080100c0c1100c3e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 550321106 1250 550319856 550319929
    0xc050301020a180501032c0f16080c040213060f020309060301151e02061f080a0804151407081b0a050c03011a0d08070213020a050310140a033509 64
    0xd500702021f00d04a04500140c0941450151208a412402504100024481b116800c9000d83c2c44540c19685845d061004110481c859440d07881d04a0f0040c035030811a40e800703038400395100701d010b00659142100040004401d40d0017600300d02a5a05c607a000c40c001d0652101d160350585221242e0b29004681e85a40a59540c20080000401003200c4004104003029016a18001d1284004a0b04100420b18210326660070071701070540c44462020ac0c0c0484075205e04d0340c901080d905041c94501e02019521149440c1e4041c1d4075000d0706454190700300068074410041c1441030b40c001e0002d4005203da01c400c1500f5030b410300f54080c54500d0035061404560342d4403440030706000d40c00140c5583d110344900c04124008110f480070030340c1c944042281030040750071400862040d4110781002c0042030f02e541d104035030008010381c9150413400c070361001d10010300b078000d4a800201000f241d60780d911440d840101c040c4500030b0382820368a18081205162810940a0442c59041d0502c48496034100c42070140f01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 550322356 1250 550321106 550321151
    0x10b120f06040f110a030e030301061d0409020618011b080f07030201090804060905010f0903080913060b040f0e10060503130c051203030403080f0907060c0c050301020a18050103 78
    0x40d40403140800c01ca40e541e50b0103d400e403c00102c0a120303640400040c840c86070803843d107039000310b41040c955080003100070085905880302603c41140c1044950710070040700742c03240351258116940d09204030240c2c1e5104041c0902c0e11b03884200e4454002980c00041001242e1076514801c40c40365162500099205001e59042028052056444419a0800301c1c050301f040e100c0540000c00005010036895407280c10f05054900c00e80b9112a51254060700720f07624003441c030020304040c009102c2d8005900d40b1420040502d904558041903007078842544c0000307988950301400340015002e604001c40b601a022143d40f100f004e0300a14100352407d40c0103083c0b440014242605010381415a00c20000c8060845002d040060b0503445000100d641956582d442074074107601142e0103000084001c001085032034403c2c11100007904c0411320348001958443c55042c07045618140340b14011945032030900c060075001c0c030b003603540500041120030b100060100359007269042504107602550b01050b080340245 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 550323606 1250 550322356 550322371
    0xb040213030b04230708010b060f040320040c0203091e06030103020621010303080403080a09020102070b2d1b0a050705060d0905070314161203080702030d23010b12 72
    0x2c1958880c5084400b420f01c4001100e0011010920b180c02c0d02000148035090303c00240007041304840d01020400c0501400344030084081c0204014000039425200051003142c401030746003429050000043c0a0700c2e11320b4102d10040e40f001c00e5440b090300c1c081c404060100c6001582c643c03010403810100305c0d28401400b019015420010322200300d80c410840010340f07110310703e07038802595859181c000d0a0200544064001031210750214080d0340b914443d04402c0f50b416002080c0d03041c5803240030101d175000a010080990a602c82001c924021100803c2038003442e104840c2e900c482c0c001401850717802000b80f110450388980040c000141e4006240b90a40d402245d01c5502d5004081820020b001800d4004109004444e000030070000302c0314400550030344440c140d0f01904c0701d80a446003034020321b1248008901c119036542c0003181c00350a0558119400c1d01c180c915004800c000942561841c86068241001a26680060b8800c002986001d07005142c080f030b260121804104020aa010f05a030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 550324856 1250 550323606 550323623
    0x9010e150c0d2c061e06180c090402070c06170f0a05060d050d030b090615030f2203090e10061d01030608100204050f06030f04140a0f0602030a0b04021303 68
    0x480640c5040350348002c003204000304007104002d0404600744c503020b00740c50950000480075510f4240d1094044841c0c4114000740c501c140f8180c403a4070001041801401c001611801008810003070303100e9000901c00180101d803c035410510b084801085078400f007a030341d0b210343e401c4800e0022a00c07901e06110380225106101042d2515114005640329040500081541c80b07003c3c2d600540c640c040c2c101100e503003022035508440c0c0d40e910060104502e03001e90160f10310303001000011100b401e10118030750804080c0001c10745410f50f00340d400485071403c90f829808074480e00c0013081082c8400c0c68142c0c0c0701c6c1c03410810300c03285898800c0103850202c24125040810780ca014404030580d1095020000402042045841405007100c10800a5000b4042d07107000303002d07072000000d1a08041341100c1c05114145906882e5940d19104d9400c0101c02c04e5030078445016001446000c02e00440d95402003138021800140e0324102181490102c5c0e0a0440b00ca0085006204ca0101409007030750040880e90080725a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 550326106 1250 550324856 550324871
    0x70308090313063c05180909101a0d0f03030f020415020c030105010302032503300306081f0b0618120c06040902160b09010e150c0d 58
    0xa40c0c01c0d40955103201185030042280000c006501002d0b0b0304a0000c0c2e000308405040300034480c15032060320682c01494584103440d5824449214200400d00152109050595508440c00041c00140180c8040e4480c5d4400c10305040079102c0c512948841d42292548101800c42d1100490b01800c40c0180140028803100602ea00b4140a90081c01c102002030300c00b1580c440d02c51400345080401440404014420307041c007036109060501c01d890503283c000f0024884a41c00c82c444940ca0b07402e0b4030300d0411044040d6070000000f003944d006200d940c0c000301031070500e40c051602a02030042a402d05e40c400c05040c807900708505000403a5400c0a028174400350340400c034600c95007801074151a002141c0060000407480501194508031081041c000c03140da12842036071030b0515503100b00c108550390f80000c041100f003200c0d00e02075000309003000024190011002e400d4a5011013540304540a180d01d94480d4045100c4400c181300005000040200704841420110160206030080351550036050703959220 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 550327356 1250 550326106 550326121
    0x1404020d020d0905160905150d1502040806040201140a080103080a0c05160510050a080a1e05040f05210708090102011404060219090303020309010e041e02040806010b03040503070308 80
    0x1202e05030111500184402c084a103800f942e610404842c0b1900200341c2000407607013540e00e0041900038803441800c584a00c2c01d50302001000c108140c42203a011000b03980110740041c090000c1c00051034408080e0000340760600001d05642a0304200d164844020070681c03d404e0382082d512819a0740010380251103152007801a207003d82500c4005d480307440f41032850302d000d05008000304103440d025202c16115005041c002c0d2141d00079003601d80b0201c0d01c0070300059070788076080d0b02c0712511030b44045072481340c03418203c000030403910161030a5451101428031032091004c201320792421000d040c840f480b446441c2c07101000240c011040300412541000070080d003941c0c03007500f010820302250012150141003916141009500c122100110340200307031480b810580c01151441c013120f4040d00954a0480c2c404011107200702d07102e0466501980e00e81d840c846043c19241c0c196034009109e41c005955605040200745400340503440914161410000c0100082002c000c1c1c49589505040c8980f95403107079503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 550328606 1250 550327356 550327361
    0x7020907031e060b03091c20010f0c050d200703030b0607050f0322060c0b07110d0f1d010903080705030c0a0c0e10380a0801050306101404020d 63
    0x1140842c000341400400b0070000c0c003410040d40508061400c48200e070000070326911241c5992803650000c00c01d180d2940140549000d444040d2401502c00011350f002c8031007010341152101e001000c0012000304124441c01c0407403040d0f003c40c0b0450400d080d01020203080301c0c0d0140c400c1c40340003030405071900c3c81400311740c03a40c1f029540105d90020a4031184440c1d60354283d500d4000e80a0342d1042d54010000d20105110102001d003602d80740d07582c0110384221511800300c140340141020080086441a1a0b805101800080544030095550b0060008400741c010300798585015001e045111004c2c4d85100303a82c00c040c241045903800520180c40c0c11071030420b42e007035005655100280e80180d603092010011040b4212040c1c4039120140d08441d1506d540c40500d1040501420b07070850110600500c2c1c041c0b0100c0b40e0607500c030154501d014900d044c002c80d49103d400c50901c4002240c51500103010354a001d0000e0b56112400703050710040c051812404004000c0d500d030005001d9a070000c2c28a11500c0c554 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 550329856 1250 550328606 550328651
    0x1e050c0705060703081905040c0b030402030a05010e0f0d030605100e0d0803010b070b010806090c06250b10150e06030a27020301051302030312100f0308120c0702090703 74
    0x5007a030f41c8801960a025081103030480381c4841d50420030030034004600c950720803035020755080b405d0f00074458101404d400c0c041c0d201400990749445100c94503000a0703001d000301c283c1400300701d020f4104038201901c498a84150706090b4403d050810f0703000d02140e02c500405004185042c5030100600300340002044415001e118040d02e8404000008100c54001c80b00810201e4840e40c940300780c41c1e83c0c480c5401d07200e14040d1003100d40c507000141280a14900213024102c1c0c68100810541e1800001c1d00c7c0000b910180c0504843c59481c01080240c0d03e8440020740c0011310319081c0540031080400350090100702a8201c15108682c08008203035070308540c2c2c2c0072400140d01c08000c103003041d81590381400602c070180404c900c69800d000000728005404404034021a40c042c0085003407000401e100000c404000b0025001c964040000103202c6040e81c444034010343c0110034003135a0303803501903c0d28981e02004061441c040402c01003440180c4400070313050361090480ca0005104107200200317800308001c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 550331106 1250 550329856 550329859
    0x2010c02090a060b0f0721020604020f040b030304080f010612081626070b010801060f030809130908180f0105271509030c041517010e0102040905161e050c0705 70
    0xc141030503217095410007840e03580d02861030944001c015051012118a581c80004016006140407400500700070001c0307940e15030001e1010a05841d06070102e40f458103d6800980d0603400355000c500420020322071f14001d41f041600f481c0c000c1c00c00e034954414611650f0080c40d440045020705109006150f02c445071008146141c4261402c003005400c43c40c0e400840c010349080c4c440c00000642e00700c05100b400111f40e8483c206c2d280301461a1a01c0c1d80c180c01101640750040c4028502c4c080a4009106500c1700e140b19031699900c80c0c001e891a951b8040c0c0e02c5504a0040307140b038019034402c0e07800c881a2801a88a541d00c01d55a04030322600704030402c0c403c1409034000d00d81c000d01e80c841010203409003003280030950403594010102000c000544d048843c4c0007035500c0da29170301803141e0080705806640c000d0034400089140305408002ca030890b48141d00c002403032540c0300c041c01034960380049580581c5050f490801003c2c0c0701408107c0550810040d1001440350000da20100c2e100d00381f1041004010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 550332356 1250 550331106 550331129
    0x80f15032b090e06040b01110304260303070c06090501090213060602010f05040213201303030801080102030f0a0510050a0e0702010506031209010c17130303030c050702010c02090a06 80
    0x36140c200c003000000101c4145100c100700920510501c180c26120803110242541c00003034694a00707010003407041c0d079041c504002050080c40ca41c81400c10041004088003210300d03044201122940415040403600d0400076001081404101c0b80d10440260100d034001000084580040c41e209004043c0300000a40025214140004895069000302d040303540b0f0360020300c034540c1c80200b00380481d6412a00258070904000c0c0d1110500880da00c16810610038050318103907461110207078001c0b5040314820350800481c5407014810168081d81807401803e8030340c029821030504402403c24803600505000a1540d11000264105441480781d001400050889006c254581d150f6402c4c1c10022180c10380550300b000702082d041d00300011511303080f40304031b44103a0810500740011101400080000e95088000f01c80700003905110800901c41c113072035240e102c0d805a00c0d520f0040c0c1901c8020b44018140031050081d000583d030000c44c0e00b2245541190308805990341d43c01501c0c010286070f00306040c50b88 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 550333606 1250 550332356 550332373
    0x30a02040e0a0942060e10031502270a050409060219020a0f0b0a111206010e0603091009140a0c0303021203041101110f032208060601080f1503 63
    0x182c3c400e552460040c01080c0414503075040d018680080d8592184841342c405503c031070707000c0444400c1c40640429000201d0755a5032000c415482c8a800d0700d10100504085a04108110003c1d05102c0e81c944584001d41c00c2040303d0100520350102e00841d041754016400190b409036131750050001c02740400074070070403081415043c150001e411101199041100c2240790b100410700001da0030062561008000000340c41035a680101600050308001000d500d540341b136000c02da030104c085c0242103205980f02c000381c94440001421145100940d9006680400c00e000300110089086e0b4082c40042c100030600001c1450a049414400d0b000550305c0d0254907034540c100040d01491504580c000e60803a458090070344101500f920040d100200b030034035001145d56440d4082d00c1402540c0f2030110903203d11714030f038030795050841e8003910700c020616404284040c130030070700b10711020007600015004004614040d00003901e801c901410600d055041c01c800108500760a644000382c090000d0169110070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 550334856 1250 550333606 550333621
    0x10150b0d1116021309023d030c0201050f04030905040b031002070c06110d0e041109130e0d1d0f130e0a02360a060308030906060411040317030a02040e 66
    0x6402540d0880c0704041c65513150300500494040c403020160010103110034641104c20425415090706014003036078000341c0081c22080b902c0318041074400e40701d89010030a482c07260310090842d0030007000746140c4800700042c000840e6000c2c9180c4e0039118161000140844840000782c90482c20320b20a040345800058040700f0445101142800c0340e145403512502e002c0302d507806c5901c0c1c2c282100200e0004985050b0300340d2901d4290815042903004607035461034403504002040a88822441800c030b01c94030303041e00300a040b00800401c0b008030441e151000d00320b91944c001d610640040ba40240c070510950000450503900ca12411074485140d41c42000a01414810b041e114809600c09038495010b5503400c1070a9616a032454411100d0004020b002000070011001800005042c400c1c00541d24640480010f820000450290701920b00070800d03494103004000c10344044081001d66010144001c000046440b0b0400650307490380c9107600e45a039500b1a61000034090340e4041ea030301440040511411 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 550336106 1250 550334856 550334887
    0x70e090709091101020106060903080706050408070212011a01020c010903080d02090a06030507030c0503090303070f0203160506060306010f1526070c0b0f0c04060c1406090d0210150b0d11 82
    0x3540c83c203800038000c0c9070b42e4034002d070b1316900540710240c180407007004070500242896001d01d500c00c0c8038a402508080d0103402083e0081c00e511003829083c0c1d96540318045243c5c0c040c080702030220007440200240b01040300003c00700340d26440000d0003800c0219104042400603010340d0708201c0041d0402c000d540c3d84542c001c010700b00030f85215020a151000c4a5212440b46046030311403c0b440b402589540c039410340c114ac003c3c4008031039000714003081c810080c40402d201e03400c00c2118001c40091a46003014010542400010380c007607126210441020082030490b2a14041284882d0802101d0315050180c44182c5034217141c480e201084c0c1d00c2c3c0c100221150410101c915890041000922540c0d03900c05603084224181e810030740c256802d1004100b01803007480700d0901c4d14031651068500d240d0301d003081880c6c464142d8000074039402040c1c0303080e03c0c1030381002407800c00c0d0404401445428480121240d1100080c0207684102d8400a0070021000d9541c10a4212203859081e66036603403943d8080941 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 550337356 1250 550336106 550336133
    0x509040506041b12061a0f03270106030b130c060809070b0d050108060a060501050904090311032107080609070f02210d060f08280605070f09090e070e09070909 70
    0x10311744500840e098005524890030040080140b40c41c2000c51144c0c08020b0b00002d0414420480610460168812052509c00c41e400403d00200301681540750012030311300010a4801c005840c1c022080c0170400c1507101d00111601400c1c401d101c0d895102c1e5990410b00642c00c441d165200c0080c0b00c3c411074140343e03c641d040322001000c0d21400e4440310000310994a01e8415a40040e005000c28040d5113070030b601c0844c4c03461181c00e0184041406060403410340d04000319014054500141200300780500780460395016089140c1b40405151240c001031315a80c01426010400c003104840b1040c0900030014005042203100b28a1400e0441c043c080d041ca03440718058032011410610b00117080c646015490050f5890003002d050111400050202a00061010420300c400c0c1501a0404110ba621400e4000d0201e50342d009102d000000340a0081c0207150b100201c428a01204001034000c041180f05c143c80d540401c98001c1c3d115114418078045843c4c10035405245041c29240422242031503449 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 550338606 1250 550337356 550337387
    0x50a020405090a20040f11030105100801120b061309060b0f2209020d020d050106061d0607030c032f0d111e03071a06041a010509040506041b 62
    0x42030b41d9894186580312818080000c0c085500942e20b01e95141c80c0c900e002c9010070024000145940c030703000300790301626403040703044100910010040c0490f04103200f4041420185040005031940346c000480c40d18100c2070400361104c140400400c0e8150351f0301c1c00e41a040c5160060500c0910510306103203000f40071002680b842000550b4440301c060820f410420143c8001260114920030803032518001380130846800ca0b841004400e5000050303607014807001c0300c03901031000000d071142000009031080c00980d248103081c40f030760030308001240e85400850310650741c1440d00c1c1242c02150301d001c0e034025840541c60b421084030700c00118120551600c03d0380d034074840e08040311102c1c4843c0000369602e103002810308006030086c0c0314111420f041c0707114000d00c4400c1201100d01e05201521150609681e908881c030740018104240400c0e450907000d10702c0454644404984c1c0c00d9050000a0441e1080200300d50003252100005a91582c0b10f500c01218010380c2c80d0910018403003c10300405031441c0307030b03000cae07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 550339856 1250 550338606 550338611
    0x303070f08100509150301050403080702010c2a030e040515040b0609090106180806013b01060e0a08030307050909180c060c100e0d23041509080604050a0204 69
    0x108000c5104030041d82c05162080d420901c524101800e2000305480100000d1900040c0448810305803800d20506101c0e50290307031802c070282042d64000b401c0d03c4003c0301701c03810061a40403d10142402c54400d0405903903940c0000c4030f1450320320b001c0d00d054424488a5900900c0c0008110982108100002402c40210390400c0700e8540c40d01006120300804800d10741040d0114018001280182611000943c5031010700d50f0b0381303546804051074110240c00500c641c180d0310400351446803850b06c01e00200351400b21900c180303168000c1c01c40c4c0143c205214078410020300c03092503841512a050704002404011007500c0c1c2d01d2400c11800703041517100302581b83c0620b55400005440302071404d00110501c02140c090013180c1003030010868140c220562072407084c0540e00440700030750703031900c180d01071802c905000e002038141ca488050840d105903807442081c10440000441c0d0400d86400300c40c1a038280f00b51440503482845411a42814550000076507445070b4002d10007031000002d0b01181003071003140c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 550341106 1250 550339856 550339877
    0xf0a210f240b0c03190f0e0d03020c040c1215030c0806090c150d0e060103021f080103020402130b181c12080711032a01090309030b1512030307 63
    0xd03100303402450581004018440e8414003294504030000e043c1148400c085a080c81c0000704524507840c0003000c000d0204034900c6144070025004a050715005604881c070880d503142070784000e526400c215000901c44c6544610103101b080c00b0301200141e4900440040280340360400007143e10b0007540c00141d031601c1c43c24000003190500082c010344100001e03809000403618617014803c0404030254200c1c0c14400621103c02908018030680c3c25200100c0018000c55142d401440140880341854075404400c404520070115004a44141160b50641c3e005030b440003502c83c0286c0c620603540203c178000a0018a020b0110011a40058524000c8985005c41c164855003d016690040b03c001c2904420211240303905000c0e10406602c098282000803800b4404030303285085601516030400301c0b03a5481802070203003d8500d440000c4c440400000c001c600041e0310007401580041c40024450a904000501d4104200d03504140000c00a004101c00c100341221060300ca400c01c440f0080000c4400703d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 550342356 1250 550341106 550341131
    0x3110306010b09060a050d0b120d0806010305070e0d02031507050d0b010203031009051f060c0c0806010806010314011e02041403010902060d0207030e1309050d140f0a210f 75
    0x100e51003d50010000c904d00a2808000d035682c0d0440007658402d540c0c0c2d5120a03101e502d50080b424600c02815018180c800942180580000030240c106410180b50404208405402030740c920b01c4118125000445400c16100183c0b518221f500160a41c0c1e90701c000384140d040c1c020b006400d4100c05184248104000c2d4001281d49000031214075181c580c203800c0030000e100c25544035580100d0002c0d010303411811407810450104910f60710010010750485020010300c40490031031800341c19030300080d040340e502d89500143d03100010700015040c4507610b80c00d030155a40950101c211003254840b042d40148080c0103010094000707106149400002d943c1d202024070b018480e881c10705600071700d10b904100724203500740000e4002000490900c13290071030240326643c40c082c922a4140c0450360110701c140640c600306003071800c1c0c02054001e10400e082d609400c03001d210182c60501480210040e25003001020846e0206880300004003420b450002450085170030340c20070f404903e102d0740140b114054544 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 550343606 1250 550342356 550342379
    0xe1b0a020616120606080105040b0303040b0906250b0109060e090a03051815070c150516060b09090106030606120515040c1706040605010603091203150f0311030601 72
    0x109290040e0031030000903140c9107060074082a1110b00c0d01e0f00c0b09a60900401050450f1040c0d0003039404103001600401051400d070080030740081040c0c0c09103003802c0c42d02c3ca5603120341c0a65024284151408100e40040e2924031005652600e078900829183e07101c5803c050b10406000e025055815003085008074400702a010510b02403a07840e8020001320390107841c200d5658000c4150001380700c0d800506611940d4804104010a1242e000c06681e9140c003072601da5401802a0f00c48190350950007a1a0411030300002030b14108a40c040240700c903c2c4151030090014020521815809507920084c0419400c05600081c2500e214040400c802515850310800c18094514014415804004480c0d400c2c007561080a41144c810041a4401a00c0f00480100e00700c40c1c040d007442e0795000030100028020540640e0340140b00c2400d0401a640c1c0c0b644813803052006428104c01410384420076201c0f44003107031668100401803802012038040e180c0c5008403101c44035500a41c41f0b84501000404e10120342d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 550344856 1250 550343606 550343617
    0x50a0f050f04030f0513080304090c0804030f0815060301082a0a0302121c0c030e180a050910021602030601140a1a0903010c050421050d0c02030109020a0e1b 69
    0x540d030300c003155210b5038121036046020080c00c4c1004020b105200803000e480e11300402801c0e100025588840c200170380a41251215035201c810041c0c807000b4032000c41c0c1c01084124038140340c2d01e0070385003944d1a500d14140c488a0440c4098008100200000d07134110302041c081e00e1003021b1460f20000e83c88400d000380c010341201030103e5112401345010001450010151500442200d042c2c0307500013070710351003e000722500200d40c201042141c034018042552140550f01e400303500315101c16881454801403510601e0040c54000b42e5542c0b034020820201003000794101035001c078001503580e0205416030b03060510b40c141040340a4810a800031480d2a54001d00640c80440945a07810b00380c500710718501c0c103050345c1600b0b501e40311041040d410307030f51002e0003281500300303a60300e500b5a1686008007510a00001e4480405240480203000c00000d2010403070302c0f81c0b11481d01d002185030416000290060041d540d00940c0b001c03940d040001c0c03503032101c05221702c91030280e940d201e0040a10510b041c0284282e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 550346106 1250 550344856 550344871
    0xc030b0603010b03100b0d120e090a1e020d0902090a0f11180d1a010f0f14010e010f0201020909010f030c050607121d030d180f031a0a0e03040603050a0f05 68
    0x12078030344020170b03000d6840031203481c40081444c65001c40d2600e0301c0e5280e811080803400014940e200c4030307006003403012916400200e0303181c0401840d00c9402c0b0170f030600380c0000003406d801341e0005640210b10380b00c0d8000040d03141c0c008111303260904101c2c2500c001002e980c90003e804d90709216103501c1c129a220107580c007415104225000d43c0304404204140541500f174210f400540618071000c5042d0245d410501074400c8001da00003107030034124502c4075080d19910204888008403c151306503603000065424207002800e004100340741c92030b010717406400703450800c40d0842c4400d0000100808694210300c1124050a2000480c546503424440d4a12900c2c801806d4858a58001411640b00303034401c5e4000d000c0c0c051030075100d000740790019051a8800381c00e500040c0c094080008040464514540100710300c00540303103110b1541d49c1d02f90203165131241e03516001c004007000800c0b0324413582012298001c44c1c4292a591500c40c00050300a003001c1d1080744001c0d01c0c4c400300c07070a8480a4421903028440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 550347356 1250 550346106 550346113
    0xa12030e0607021807080402130c02030706111603020a02040e0703020109170a06140f060a06210e0a0f030806040b09010b09040b060a020a0b24120304030b040c030b0603010b03 77
    0x1180d000303000081d440064100e800070010403000c41c2100c5001422402081c0d555116035840c14140100710f0b907000b0b12100034400c02d180403c0c06958607000803c45140b2075000b000840c40c2c004441000b8494040c1d00c184080d441142500300342019400b08000c105988220b508100c005804152950f454111740402408207417641d205101c095904e0f0042c49285200310122180190b46a440000782c8030740724600301803030364241c0900a469914041030350740100240c8451105034034048005081c0101c90442076010424a840c40411a0b2590412080d002881c000c4601c00c0e0458a8201203185044500b500011040d6000c2aa41c0c5400d001e07034841208001c1c11010300340d013041107268280d44200c00e80d0354440d5490586201c15142c940281c061802e0a070040c0c0341c541c074141400501c820005154070424108200021102cac200e015040e20104008da600d40540301d0070152803482c504c81c41d00003400c0c00845c601003108010400c00300c0e0060ba03105142e60300e081c0c1c81310b9042c54282c94614558951541 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 550348606 1250 550347356 550347377
    0x7021e03030c0a0c0c08010f05041a0c030a0b01261f060905040f09140705030f120d1d010e01060512150c0f0906030c041a16082a0106050a1203 63
    0x600c14030560034418000d0102171182c0d44d40b0080d85003101d400c1d0000d00d020b591150200801c2c00741c0001e0f0241083c8090b940c10480d40f13480380c2c48410f1032000030541d21545550314460003469204204d102c1d0703401c00581d0140c00741a4101144044403c048681413070141c1d140e85a140e845504082c1c01c0110351441d120041c4041c1000d080101504281e0340302108c02da6074180940c00b01d6545d044102d01100c1c0311015010f0301c0d0505003810700f40400e820f8812030a07031000d5589855002c0310402c07207041d0401600d000410502154a82c2d00d0311f5020b4038400110741c24030b483c800d04200e043d80f0000c100d0301e04031384a8140c0c1e060410410b4590140a80402010740040005003a00c0b80ea43d0040c165019040e2003030703107820780080000780660001c1d0360403040c101d00410705000540c33108602040f2010903194483c20b03d44160170800751501c11503401482894040b0716400103401d0407440071646007500b11034004420740d0003102c50003070808bc40703070b244a0001c0b20030004491074101500034401b038056441d07000c2103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 550349856 1250 550348606 550348627
    0xa0b01060c2411070f02040b030c0906040f0605031c031409100f150909111f0f0c0602040603091203050c12060f0405070c0611090d140a05010507021e03030c 69
    0x9401c203281c0e01c2e2503442d14030001c020340d02200140a081c0c03168008120910140c010311044400b10360504e40650300c58803003141150741d9096103550041c001c96002c141051054003030005030019906c820b401d03104030010074141c040c021120940c0010a65000c200700c4130a8100d044600c407094031400800e4010810003086040035401400705403440c030801040540d10060310580c1c03058242c0c4054201c81d43c608100b000c00907001513804a40c0780880305c00003103550103032020103001501ca808000b4440400c034013800d0030380a09031440c405a0000300071034456075194005009041a01c104803050120030395a58581c900920546008540c0c5120b070078200811951031f5402014007a0449a00a85800045555640394020fa034072416680d51850341074125481c0c080161942100d6051503044103004454140d2101e00c42d12406541050003126000c0d050707106541007403200c6001a045500340010800d00c6900001c8500c02d0b41e0a52a903070b2540410045510340b28041030701d030050941c004004a6030359 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 550351106 1250 550349856 550349903
    0x601050304110307060f02010f0c21140a05041101020d051909030c081e03040b0a0f0c021e0333040c0f090b0109060305060a030213110c0a0b01060c 65
    0x418030605071400b1030307609a80041d1520a05500010000c2d40d0303003400e00707103055080c00303080010501c0304001c1c850121142000f8003d440350303031010040404000c803039280c40300451b044803041150714103110940d8103104040402a0004543c140e5000317400d600a10441e520002e0f0100f00280315588036030403c404500f0b406070807018101c0d00010080e2441010010450b00b09000c0b00400b107010050200c0020086030700048048a0700c04501c0750024441001441600c104582a252a40c581003c544039045401c1c1c44180150b10041e4000e00c2c5004c0310000c2d01407081910550b00c0c01201211b0341c0c0081e20030703407072401902104900120781c801e488160b80155952030031034100707204041d42070f0f0707054440ea250b0a12a0032035002d100c84646403203c038181c03541c2007801d40000d8504c9150a00480c9041d0000c506a4010380c88000d0103003042c4841d07014400c01c941d002c103103420b940480c510391314210181d9103550746c41e001405071401302c80c5000000c0c4041c0510400c50f00c0680c481c510000c044d281445110a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 550352356 1250 550351106 550351111
    0x714070305093c150f07050105010e010308220b19031d1005270105060f0109080618010f02040902070204050c070f031803170307090f1a070203150408040806070c03050306010503 78
    0x40180300e042940e42c04c80c4d2000c016040480c0300d070303200d1610b42d111030902500b543c0c0181e01015405400d1001400441c5410301210290345502a5042003001004120f0302104066842000100b00100da1400803e01c42c001c118101000c50341c0505c21182503000049150b80245000f6046501003c0d07818004810b41d00065071200c4012420b0a40c040f14112940a54062506920060350b550b01041024075006100740003020003807070a4223000e801d000e40b044d510305000d084034a401000b5607030190084000d4204051250358150700303544481c0d03a0720061019410100c8101c0c42075040c030307002072408006002603131001c94003d6541d441c0c031061034078142e4901e046401d0b03544464110304404030220391f90146506490141820296036868200c0703008200300b079560401840d1240110003003019420300d00304030a1031040005056903400891001915190003940365075498542b076000c100920650341c000d041141c1c20001075900030760391600101d5846502c65070050200e4010710200d83c480d4171410181d41d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 550353606 1250 550352356 550352359
    0x111100e03041a0301170a030e01180504020a03022d0304080d060b031e0609070207060e0102030c0d09061202090a090504390807120204050714070305093c 68
    0xb40382c143ca5500307403050403001010002d0040380001c010030150001c1d040300d940c4942d00202074940380380c81e030703070000c0000202404039410800210042603440310800340007001010010800c554031151000080c1c007a4110521812101c8070303441040c0c26030f5100c00c11507c0290500c00810f80345560341d50f1105001c0c1c2142c107101e010160b5540340441c05058480c020742c0540744900503c030508a142c0807228640d00004c10750781c0104958414800c980f40c0024000d001c1d10003d06003026080c6107940100c0c5076002d486400750451048019a07418107400000d0141a03585955400c200e4800358030341c4c5416031051512054200286910800007007030a41d21054219204074400403a080105601b000f4081900442c400340c4281500d4070985900565100002404000080d01c45142b401c1007402e0000d40380345010340248d0322200001c600b24452038180915003a43c42c6040c3d00d0342c01904000742590040301240c0c2c0201c03501c0c0c0040c0310b1583e240c1a020003010500400f0048054241d040046244184c85840d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 550354856 1250 550353606 550353613
    0xc1c080301270608070504050112110906040b03100c0801080a080a0806041119110703050703060f0902032b030635191101050403021c2315060111100e 66
    0xc0c181c82c02d070280c01c0081212800802c4518103003420081224030690002800440103007121001417405042540b20400880c2c4685480d0703101d8011034081c010280c1040d0b41030081d480100c000c11132590008a441c0069a41d0110a0780c072211466910600b4443c00340101d0001d0085401c1c082c802d00c040340d4448000740c4086480d40c10290440c7c4507800110361b00600c07070113840c80d034501203900450706070f5030310401d10061480d80d146890315030b2181c0e6240009042207849403040e510410042e0802c0c14040d40c080c0844a110000e8101043c44004803c0c580c018142042c0014010078031901848080d42c0c1c2500b0722040c602c14000041c40c058010041c00c10070200d442c284622080c50900c0550b07100d01c5a030350030f0b111914507454000803a03c9042d0400e810700505101c03c0c00503072a04210201404001c40c0c0c2d0a10a42c81804e000e0300001c2c89142c20110f0b0f8295100d444120400402ca40d4076100c43d02040c03402d103031240c200640760080c003030801c05070650112103200d980720120303042082e19440303000c00c0c2c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 550356106 1250 550354856 550354919
    0x5070c0f02131a01110316060f110406080f15010807181802250f0b18060106120f1a01211a01020708010902060706020d020d09050c1c080301 62
    0x6900540c2c0b260400b6103da0005503000e1612960030200407400d00950714051031920302c052000d54041695840054000da60702d0304001450011903020b1052040c0c05900310741c40b40e03075410f40100441021204521081580b42c0032030b2401d101b50300c2044010b00e058403240d0440e960f5120480360600e9020301c4415078040d0120004102034550301c208480f0400742000750b52195404001c42c000b5021500103003105a1200451000c01d0f81f031300e10301c070b05194810035070305042c0c039441101107003059451001030f1140100000021459004841c41c1000b203c005001c1c0b0400140c1000c0c0c42c01c46004c5031001100c401020034140d221743c80745004031340a45104854001c10a2081c00c00421100041818600c02410f007120710401c0d81c0420952009005040084c040b0182036404142da5008040e0001e000c00d0700070407a00d88506d02501134900e000c5072080100001030903801c01e40d64550f100e60286018409113048180140003100420100c140c00088061840e407038400b032075032140c200b0b0b0070b54400304e60a4843e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 550357356 1250 550356106 550356139
    0x4113050a140615060c120c03070512030a052d0901020d05040f1b12060f0908031015020d0c140106080d03050411010302090f04090302210c010f05070c0f02 68
    0x203034072291503141c00a0900d80fa180b2400a0002e07803406215104181c1032004811070f40c00001c0408911000c060300581b02c030004415280b850007041401000750141d12041c804105481e000b85110f8004014240703d06d84034102010140a41d0940010f01d83e03201d90703000d103650344400b05800d411042c1c001c0014605221880140c045800596040b02c2c0381c0b0000d00200305000c07049012202d6140d503860021402e506c0c0c407405c04444015000c2c02025252039842d40041d0f01410790001d41681d402c0031109547e80303011442076490070998007801041980510344035685070310006e06514503d2094443c1801c1400a4031011090001c4241d07240d200d40d00e510b00407070300321000d1101d40c0c0003054a0300c0200701030809141683d0760040300d100e194105032050201c03030019681e2010500c4250400e0f070740014501c2c0d1900f412810a490b048610041c807015000d0940d02040b10401450442c1800c0000c0010042c0c1c81e82540c19036000b42e4025002601d2001100c1c0030848001003a8901803000701580c070f88580000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 550358606 1250 550357356 550357373
    0x60109080d0503040b09060601200106030c0e04120e0a05010c080f0406020d080f0f0103150b090c09040b040203060603012102090a0615080402090c0f0d4113050a 71
    0x2801c1c1400034501206100800c000080d4442d001a01040604064902400020300c0502e13144440e0540c01400840b1142d844000c2d4891400386820070003e0004c00d8940d00c00030501902500e0880b00c00c80941c2d02c40040600c034054102e107051000b010300460a2401004449a0b48076107130580d00590100507000c25201010001c0008107040d8020b400a8509094040c1841c10010001c003002e02c1498104280c14040300030700740c15242c1c40b080300c1e0b401e06071001020340100380707640030740b5000389100041c80f0320462504060102c212044a06006045620092000b680411740714613402200510060000912810340880030000d080c51141104503e600004cae403000c0d00303591820354503035544014003210301901c802070781034001820025014101580414032001c0014a0f0b014010004650000b033f210030395040340c004440f190004d212004141c0e00103c1d61540b100151031a1014003c403003549401c2d17400b00f03108001c900b40c210358083d68410369820311024003203a04803424000c030200c1800007070001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 550359712 1106 550358606 550358623
    0x10b031009020d0b030106030b10060504050d03032706140a1a040b030c03030c06070f02161202012d110a2003120706050703050612100506010908 64
    0x10143ca800a12040c60350030703403650900000000340900303917071814002d542d2518000340c80c0f40d80d04da003038500780f02c0d612070f80b41c0080c0781009a201290003640700d09881c2e2101e044a0003404202d40000100c000d04040403500c1a60302c82e409841440040542c81d8095595402007040d0b0700d0081c400308810b140014903510a035100c02212580e503d0a1000da02c940720003900f180c0d02d4400345000f03030782c40d8101181d41d07070000742d940346010910074400604108280c002c022001c170100d042c10b1203049540d0703105e2410b174140300300d0510348240d08910517406044949006040c0799020380144009040c2c1a0480700315003213038001c0c0c0200b804030f040a50604609018104a00c911850580c007082c10184039030300742d000e000f5000c50b00009000e0240c00151080d0032036a020400350b994081005001c003111800d081d0254040ca00c081002ca0103607011700d0b00100c0c14104805083da41d503001d03501d0880d07003 = true := by decide +kernel

theorem cover : BRFrame.Cov 550179856 550359712 := by
  have h0 := BRFrame.cov_init 550179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 550179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 550179856 ≤ n) (h2 : n < 550359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
