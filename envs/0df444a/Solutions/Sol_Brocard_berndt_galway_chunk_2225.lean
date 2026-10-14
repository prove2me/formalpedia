-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2225
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:08.266763+00:00
-- url     : https://prove2.me/submissions/70fea664-32e8-4d1e-ac0c-294118ee727a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400000000 ≤ n < 400179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400001250 1250 400000000 400000009
    0x10908030d02130b0c01050106020c0a0e011e08030a0c03021006140f0316140901050406120f0510060b0a1713080c0c04090b2202090a15090606090311 66
    0x124810448150410400540060526001080d0500c2c50f1a8628107040d0ba410716210740758045100c06049954500050201641c140034207000600201d40705054982001642c0704c2c03030001803013121107000380c01c10094020b80f0344d031681000400c604815241c8a000b50f000140400d5460030045005000d000003024240c03a0521032b940030f44091030158280400000c044c00b003904241102154140f00d01005d8019240c0d52608120242140d10b036281a4030100200388807502c001a08018407460400740b0901c6101e4080b0702c5985940e4200400d0003101c41c50382001801c11443d061f40080030b500703059000ca00a1a000c00501e06c7e0750b52a030700c0b50303c4408a040302c801c0404003540c80326a1005400031b42404200c458018198102e0181b0603111240358940004007206c0704240c0c100d94801400c01000010500840100d40c4810340d004200b041e41020360005094a000802610805541c5c0850711103d4240f803070031a019002c540301c00c01915442d240060030704240d51200719190b02c000c14074038065051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400002500 1250 400001250 400001267
    0xa12080709180905010905030307020c01030f09030507080d06030f08031f08030a0c02041e0905070e190e010b10080121080409091e0b07030c0f091401090e2401 70
    0x102202a48001c142d50108402501d8141e01c1540c107517490b500b405021820900003135016051540040200450380800034080e02d0560b1101a101817a2811a5012a41000031201034a0303200b0192980c410689c4000e10080c2001e80010b486c40043c04003010400c840200210f0048121407000c4c0100d401c0040b06011501e4603025001060b0000c5c40003815046c042d40d0054055440100003199200c1030701146d144e0345645080040b07465445845400c18800d0a122010140042c07280702c4101d1f28042440050070a400b03184030a0712175880180100100e020351022040080090900000b900442c0c070040201c0828000d115984146a44102c1800303020105a90340c158000c2025003803910707000f0f850006000e20882a50f1084441c04001c4410300300c1d001510700320f0300c60a2074440f07a0414010040807114510060001c5c41090100020601e410059041c100c0b4440c0e074200c100310f500e450040f074200e40d0941c00385181d01215411b0012480c41004290107c00d001941501d0028020004490310380 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400003750 1250 400002500 400002509
    0x7060e03070c05100302040801050c04030c050d0309121401051e071d060c010204120602120604060308030a0b030f0d03020c1902090a050714120a05060109050a05010503090a02030a12080709 83
    0x190012410015800d000074104c40807001800c006082c5070351031005034203550f8100c071108000d030b40c0081c0900401525640d00f2000d0302081d9030f5041100c1e11541c000d8070030030f824000e0701e40462901c40c1050810100013044880320321100001d014a09182034404042c50130304604802e805600c42c00511031901c140407401c0c40f181c132010101d140301c01c681c0901845611081000109540801011580f501c442d41d07801c041c0d5110709401a0f40c1c203e42c41644200f0080a42074500c01d0381040000c10100d100340f4143e0313400889045001582e409218000b0f0b2424803e04d15550641c0140f4000c0342c400d60f0164042c000200340f8600359a01d801c50050883d80041382c00340000d42c01100310780810070380241c9900441e030011250401d01c00303888104501401c1c6810000705040e99400000400107882d02c140102c0b03400c0002030800880e15814840083c0d6018101d01840d410414040300140840008000b01d41c040c5402400b40c40111409003041000030510744603200215030004c010400280c401d80c20b040440c0d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400005000 1250 400003750 400003763
    0x20307020d030221010e0106030f0b0a03411b030d080a110301091a0a1809151104050a1202030613080c06150406060203070503030f06180c07060e0307 66
    0x42464040c182c1c02074000302034001c00306918400755500c6100007080c05001e0008840540385940c0741000041c25242580c050304610350030036807200a00d84904c040c04065a61066402007609601c9414000d141103a250b611803a0300d00041204000c091001d80e9954007519005403600c407a011251148091825220690168001490080900c0c418041c081d00035694440100e150000c18241c006990001c1e08007019507603480c1072030214400041c0307201004030b4042d1030082e9503031b20f00007840c012000d9409441031801d03143e01c03800c03040140900003034903070024031030003000404c0800f452881320350024043e00e4001c0c5e10b0003c0101d0058020350080c0c00f020b40c028000c0202e80c0e981142d038004008581002c50700e070b1406002c105181501805510b210300640091651407075240300402080c0c605c0355022000399001046001d0100300003004aa9210920520002d01038807200086407194915400044c0c81c4c1007001c00b4400c0344400d900092460500450042c00b54401e154039041c3c0700d108540c40103101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400006250 1250 400005000 400005013
    0xa1b02060a030e10021c05061f08090f100902030c0303030435072d030203070b06010509120601030b10151422081606081305010b040c020c011202030702 67
    0x1507200b50040e08010442c0404d542024001c88002d8041c2d800c05da20741080c6825105100500d4800391003101c0d445032003220441d80090071000343c0c180010340303072004004000d41d102c005640d074441002407550340c04030401200c20840508070813034000c02e4980c9080303202e40600040040189400002e8a002d150801903560030320b103000d038402e202c000700034098034241100c400040b2410300c2c5d02400340c94030a00958421400c80011200c0000d0410020000840d54a15482140100e0340c00401e540415a00c18000788141c0c403204010394039400b071700440700d40c4180c51a07001d205404c03000c2603103812248141c6021203603072103080eaa13100004507401050700e01020080050720140c400e50510a0010901e8001840c1100704045d170144c940c2c410b2a01410f0144c1420100080502080110480021424401303111810003400900c200c2002d8441041840200304e14420321030b0a600c00311703400e0401041048800740345080691141449854a030110352606200001c00ca018007c40c0e10031078442d1b01400301c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400007500 1250 400006250 400006267
    0xf0f0605090301150303120b040218240c160902030403050901030519060b040f052b110301020711040f1a0d140f1e1b010f030e060c0a1b0206 62
    0x1440e411180140d54103649a80c644113404090b840c00d5030146029541d54840b50503041500d1003500e203441d01c1d40f4003442c4100703c244180552158424165107084034540000840503100d101480a80c54075020700c3c0a0006085040200002c0c1c803540400302003410440c403e5454039504100d0104031390140114104000412096119921055002d05102d6003a20303003c0344441218200c65642e001120720540000b001d0148002910901e0014401160140d64090000c0428031018221841110f1110581120a010420002c001080084015000319140ca41a04180132100705c00345201d406103103018410030340034166016010301817016030075600000c4e65a4040c8480340039080c0c01526601d01c08103400c20198405e1182010907500e0000401105050050342c511410308405003852a038044c0c030740710300e0145059049801c0d070502401d20440c180070308103050380079041100c070395115801100e041103005207802014080c810030a55450388030240f5505500442080b040d00650301c0b2206008065 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400008750 1250 400007500 400007507
    0x506010507022206081b0402040f0306020c1504030905211213051903020a050607050601030204020d1d0d0809011103010b0711060706050105090a05060607020f012303100f0f06 77
    0x12000f10b40700700d450358418000507001181c0c120703000001380d80c200740302400d0000000c0f4510303030794280d0840d011403a00740350864200640380340c0e100080c080c0346c01240380074a5020a120b0341032801408603120318540380c1890000c1c51031460780903140c80f680044102405560601182400764644940107181080951149003c01c1e0081e03428084c494121440c0070a003030316000185035113a154042c1c2422081e046104210383d12045810460140c00d003070000307401040001545a0449070107540050340c54803030b02e45040103840803046074100b07042d0369070f5188000342001402440c0110035698001e03154584903861401e0384c184003025100e2900610062000c0d021b86030050501900c9001e41120441c1e108001ca5030b203800500040d20081c1d600c000401881c201080081d901000f00c04040009190000000d8114007071103001900070048030080c240583d004412841d03801070308400182d018001d071040210154800c548681079101c1c440c20014028541c440e80d6010b840ca112888020203043c00e1088 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400010000 1250 400008750 400008769
    0x90c0e0109110a1d0a1707030c1703070b0903040b19170702100b03030c0706080a0506180403050307180909110609010c020904211116030507090b030102130806070210050601050702 79
    0x661007200100300043c6c0240340214603041d001c40c0409044250b14604180c408606594090070401c100140c005407030b24000f1089600560380078000c004d8a443e004c00d11880d41c003a41e04201d42c071444c00108000c0f8445e003007007001042070351382e038800d0103900c89844010f440404c2a2940c0700036030b00469140201030841d800c03c9030080401f804032303401c010340c1e041c895150110340e511900100301d604060006500541c09034a503c580e007138802c1084440303510380780d0740032010040000c0c0c03c1080c04800300f001c00348100a42038280e052070300b48250482d101c106a00c028215000700325171301402a181842181800f04c242c0303e10f140161503144002d0140d400b44520400b0092007202e0f0340e400a5140c0d0002040e14000f10844007450b43c455100c80c140043d0546000030380034140c25042070005007040040c2001846134140d03007103184040384030010200440c0c0607000d40c65105441c8030402c5400f194010000540394400d900c03603400c5403210000c4234000340441d001910f082c0c1c000b40e0200421030140c02d100a04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400011250 1250 400010000 400010057
    0xc08190509030307060b090106020f031b0118150c03050108061518040309030311011e150308040311010905271e13030f0e0d060f090c0e0109110a 64
    0x103803501d000e8400080c00c5500082e8201e03041603503848404400d0401da0b620602400f8540000e0100c1c80d90151415568020703030704a52000c150356880c4808041c0c0a400a2070303002410590304204903281e01d400d8200c0500b14110342c4034a0b28080d0030703c031a0340c80b90040c0d90403281e404001c1c4c040d6440b2880041c40b644802350f01e8a030016200a00215407055a101081c0f0070b038041d81d1042c0c9090706501d4000d000c0500c0100c0a1020303814501c00c510883c10000c0c0462880800040c0040c0c020100329000030708481d5070380007403c821404100001800640c01031038403064000daa030700324850345400401603070301e02001c1007092a100d400f2800d000f040c145407983e03030405078180c007104541901e4003000d40c2c0c9020844500c1080c9400902a40405400502d009400c0045050604840d107280002c1450302c0c120040140040751101c0e030640c50241e0b036500522803140c00200f558143da4032050340122000086c0304010b0442e01c0d09400245003206d12041c1c0d81c44441075562414000b280012221050421100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400012500 1250 400011250 400011257
    0xb0d030921150c0309021c05120f030f07140d020c07080106031e080d06080d14031b160605090f07080c0904060b03122a0d050a0c030306051518010c0819 67
    0x17480c0503a685075001907949040c4401190120070907d0200e040604218164810031020301c50050000780c00011b403903002030401c00041141d038401401b140e0480f54440160040c150009920f11030032203e400070074525010f14200d5070b9040d92002075501300c0d4194400a81451000c0240c07181000340152000388060184070050709100c2c1804ca40002c9407000c0d802014540c1c04005440072042e000b541c0042e0600543e0403007802e6280c111322082c10307084445011480a00300040c1014020b10290049013400e4004a04000b940b0708510025a00c80f488200111507200341f11b800100e85000298007010008090a504600d485664410024040c0076a01e250706000e0f005160307101199440c00740c100c3c040380380d141900703a807000c00100801c12451200040d094005004450340395402c8130884050941c6032504910044140c1011001403084e9003209600111946050445412000c003420a002c5102549840e05907260010f41348085500c40003042c0340400e005003481c0040c2c2e082400041000ca04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400013750 1250 400012500 400012511
    0x703050c160603060819150c0c050102130e1305070605090112051014180f0601020a050f070e070f021c0c06050c0705010605151c0b0d030921150c03 65
    0x40c50064070712030b085040020384d581820001c400c1d0030003500710746884110729140021025200c909402c40008050500143c0301c010140304a0311660f420079800381c100000319103c091030003004090415900c1144a14007a08010502c880e092001454042d0780c00401030038028030305403003680c80c0d821240d692414011041c0050380781c19141c0c0942c51254941c41e040074912400d0064155940c1c3c8900d40c0309004201c4c8045100140101098150b00f082c0500340c0c0500a5440c000104c0c0780034050b2a008210340114900e41c00300d01c4001903e40c003076a4507134400b1140f95803003c50803034040c2010754030000103902c44440241421544140000501000d103084102e0620507154101510b1050310f00414100c0000360480c24800e0a100355406001e04071080000b81d090907002030424005c1680d1003990343d4414060b000d1684181d440020350303500c06030130207007202c07400d080180102c4000e100303460782a2001c0821800301c0c40c90441101c0d580d94010a5030f000c00c0100705181005120300e03041e820903d580d44 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400015000 1250 400013750 400013773
    0x20f120c0409230c041a090a09020f0d050102091f0f111204140f0d02060d2a0e040606031e0203151903050d020d05030612010b04020d06030605010b0f0703050c 70
    0xc5107405000843e040040520101801c1484200e5801c1c44400350b0441d00c101d003000300c0341e40303400300c1542107408500045000606800043c0380d6810202c401e9a0100110184804000064025000c10a0308a41c0001c1d00d05e121034a038102581d0640941c000222031030303010142140a120101090500f260840b080305500040800135584150010303d00708500325401d070f4442c03510420510b54000207940c907504e0003040f9404a8450300032800c0710289991901400c615410407130b0780c0588a46169150b12100c0441074034080d080d8034440140303074003d50500d100411918081c0c0152001200c00010b00c05400e00503181640c000c1d00050f1450b842a0750076044c02e0100d5070b030880740b80314810b100d0352007103421460352410b1498a0f04204074042590000004044902c2d048020703664485000c0c1c60024150440d40606030040c4022445142c3c85440031500203242a00c5901c00821360f40304131410031490340c913001c90f510103005100c84c40c0fa50f00c00c10403564000070710542c0944201c09802084800500c40f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400016250 1250 400015000 400015043
    0xc0302100507030b0a05031b0111030d0f0506011205040b070309060b0a03050312070801060c030e011814040b0f06160519031e030c0e120a060501030f020f120c0409 72
    0xa542800c0020384400304c0008900d04a0740c24001000304400031b01c3d0b418941c0080c2d0000d0851607814a06101e00443e800740602350038030449004804411040050381c00c090034000003000151907090010b0080c045409601195220b160b001d0344e0400e15100c416620040214041c01c1009011282203803a1a0322140c140c807075641d06005184201e0146803101034860940b0345585c0020400404c0140c0791004114940e00103401411150701854204003d002100058801c1200c1580041e030300b2035481c00000c0c1c0c1010b0391080702000c0008440a002d4803500302c08218100c0529103069a002c10304202c90003a12101c280b6a01400c0d20600c00c0d162803d5400d044461a0345c6002015800f00d56503081f803241001c004150034a8032400303802c04000100902e6001011402c40410b1140203503100c3c500414503803420413030001007550080c414002ca6031603141c10042040d60310380032800784025101d10045032030028213580445e10000000c011415a8204000142c03180d080d0030b40c0c2c162607144840300e14454 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400017500 1250 400016250 400016261
    0x10309050609030d0b010c32030c010f110f0d0b040e10050603060601090305031207030f020f071502122a18181b0c1903080108010614100c030210 64
    0x12580c014588071071507040c400b0142d644400703465041207070515690380011403034080300c050700082003901c2c180340a4913123509081d010002020002c078070020034070b0303200741c98150011040c43c02048821302984183c60a440e02a02824458842c120700a000b0403c2c82112540a074a5151000344007140d020040224181800c1403260030025103500c4000700403c6007020000550054402c1c41c07c022000c0c07450311111344a02580380440a1a02c07041c01080009210340c008941000c14640b0456544001080f0101c6540c0008800c131940004031402c028101498401c2d00e2403440b51041c5445182e540c550300c2c3c24907280c1c0c130340d01e4500e00c01d01c0410b00441000000151045440c1a0b0310b02250b00d2000e4104602c41034540503010380c40118108004902001d26000d01007035002c802215201c101d00e44002c0e003082c8a10901f00e401a03072a441c0034050641c8000024102c0c1c01c08002001926221080c1200550903003c1c01034200d0100c1c54403010141c811060b180c1e40b980079105843d803140c0f580c8a24025240c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400018750 1250 400017500 400017511
    0xc0d080c070b16090f0f170106050a18050f09030301050d080f041701052412121219050709030b06210106080c0609031011040306020304200303160803060103090506 72
    0x18240b041c583e445580140b00b02c0050301d0210302c048509841d00a00354100e8400d030083d403688088142d8040310f0200250803141c0640030080c00c0e80f8000d615152052103e030141d11401e9520b50a0401061040302c566600f20b0081d0300c504051450361b801c0c9014440b498900d6001142c943c2020030045400c40340c0c00000d480502904098001031013000078034242912806000c1798118052859404041c94041c107160409040580303617030f03246002140001d8101b0741224081c00e440540024401144098162001e00c03508101016100342ca0f42801c982048840c1115075001103840054203101007954680740640c801001400004d042070a9207c0300244042c928541c1e41c2c0340c1d11044244810070742402148003003203050316924141078003075000a50b903503640d000103541266500d5050306260400b90495000d10380002065589080c80d06e00300c3d07140000740103a48070400e080c00d00401d1900d4044102c5852040b0300c140c0c00030250890715008030640c00540010306140d5960114030000d5014030440d480380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400020000 1250 400018750 400018771
    0x9090627070504030c050f0307092004030506040311061e041e0f020906040218040b1f0c170a0f181505090f010c0213020c0a021c020f04020c0d080c070b 67
    0x8610b1440c00c0c5138101c40503042031f449240d00158402e02d58030006614002c94800e400041105a0700640300d048041c0c0307568140c50ba5102c00200442441400034510303000750b1007556017550120108001725207a03001a2a52100c1d035400356214101c0c0c542e410304280d04180600719481401060640d040202100020112000c02d030b003046090540c6400d0304c030035611401c20344040d0303c0c01c07680e44420080880c0050350039100f1551680e20340f600740c442d01d90250b607076003000c9102102c1e141c840801400980c4c06800860341a01692240591446098282c48500c540342e1100b181c0540700480c207842142510403107001405a1440000e140c2c00d000507030100c54415602c4281d91583c2c40d6060101d0b46244241d101d06120a090710200142c072658803825400b000c0c41c0c40140c40d00e0302400c586040181d240000f940c080802900c0312041103042e030428006034801c0710f40000c100c0d21681400705a0103840b113036400c560851080310442c41d004d0041240e0100e0300c24541c0b8680740aa07550701c0e2102030151400e0402 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400021250 1250 400020000 400020007
    0x405040b180606010507060221190606030b060327030f0a030b0307050a05090c041a03090c0103090c1a070210050a0801060504080a110f0901090b01021002090906270705 74
    0x80150401c0c00012000340d1006444140350140029115203d400320080c40070358006042209480107000921440c261088004840d08006030607004041900340d800509601e05140011114045d104061080c0406061141182e89000300070240200070781c0d124913050240c01400210360000d100070328107119209403940d100c801300c800007801c888629031064002d92000751f042c08584e032582107110071141d0403200c50050360f480802c107213050b00443d032002c0240c00c00c45030606007041000700514481e00300c041c101c1d90301c020800700440070b40c0d81520024108000b10301042c44011401002181190310000c10301349001003560106050f0001d010340d0200080010450340140d0360710180081c010255460074905003414500d4094513160050700040124a81c0c44007004a0b450341d00d65101100c0d0010003c1130a903039511024805030140c000c0003030041c00303940004a4101f205100780d17000c9410180102400350b40702814406c400400c4000400c461002c800b04100f03061842c40d89a129040c51b50b41c8a48 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400022500 1250 400021250 400021261
    0x1030201020a06111209010516020f43210b04020f03030702060309030d0c140f0a09031505100611031207020c060c0a03020c040218101412041a0c0a030e0c0405040b 72
    0x1213000b00380702c140c110742102145030186c00b80019858401600728618040140c0c0c0d0b14000c0d0310b41c840c40c0e4030201c1c038041081c02014ce0342c40c10b44210300c2210040b9044040c184129003407030181c0f04c2030400007030283c6098000702d409810082401007604c0c0d0040c0440703203090740035000945035400071240c05030260704c0021204016050340c0100d40b507a1082d41400024071104180b0294140682d1448041600c400301c4c905e11028882c501d01d10041d0b0b0448000c0140340560412032002d448111a103110070b01503101300080d554812a00040c2c80b4107100302460a0460494201010f104041e00b618118800c1d05580b221700c1c0d440d03030010880310318120007c4c42020124603029041c601c6590f8007a21851061088103040e1000c03d20040f1707034042c1203c01081484060701c1c103540801100c1e03e4080064004502152841300703401c40c0a02490140c5014207141c4d0807005481500103084910141d4400d060001141c0e83d40240c00c103481e82c2030041c00380c034100101000030800310f0b40115400d5810140d42020700c031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400023750 1250 400022500 400022521
    0x1715120712121b06020309010603080f0a030507050901020d030f0209041d010509160611150a0b150403022b0204090c0504051006020d0e01020a06061511030301030201020a061112090105 81
    0x50b440101d505000918051101c40e1407041040303181d000e1324070742d000400180880c0b000e44c044005554810b00c0a0303140d42c80c410b12014290028030604000c44c3c54070020074092070007141580c0c00b481c0140e0003000d555441d110124050000c1488000100740c0921488003595200e02440350301d12500451a5158011a600c603800d6038130240404440d074002c040c0e8540b400781c6004a61064520505014507001013040200d85080c030000c001c400035054003824020040895040f2212410046170905201000c0d031410024074800d91100a51040403116901c2c0d04c40013418450201c0b65000c07018400007003558021030103890300c01d44111004418800300b8441480c05200c5c5c01e4200d40300881c008150360800c20041c1d9245501c21840091020403025415140e100700550309215506c484103001c4217940d8890108516101507040c808107402c82c10080d08034400209070b03070499070140c0c01444a000d10352250001401801c0008118010401039041d854603403004890140380c4400c000920b5117821804c20 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400025000 1250 400023750 400023773
    0xe04050109021f080f180f0c01020d02071d0702071215051e04060b0312130e0c0c030d09150e0601030b0c07050601150905090c040e071715120712 64
    0x80b20010fa01c0300c0c48a541a03000390702ea5401600000d4020281d281c1407402484603e8000224040e44640540400c0b60040032078070703035000b2a0070380803184141840c04069888804a01403083c00d00c81e00a01c0c5405849640340007900460a030043d2042ca5444003141c00c4040ba5000e001c2c1c5459694240440003400315218160b403040100c40b1420710690014100c442d900b001800250240746c591403829410f513401c0c003407224400c8184001642c1d0780d69600702c40e200726015104110340c0200040002c0c00ca00380000071a1551445038019610740a2402c00c48801006030724010b81c1c91405003864102088684d204040190324003038000d0129600d1884c0048240400500c0300c19100001e11640700060310000380107048d200240c540c02d1020743c6000c4102c6200017143e21240e4000019030500124000324070007401510707e9060f00748075660f2594029204d0f03d40100220703022803803031000142c0c51080a440b2122404004241184d0740c0c6020010b50314100a0340c101095800c5505412810008201c060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400026250 1250 400025000 400025029
    0xa060504021909050f150f010309020a0b0c0106030203060603030c0a120909060e0f010501030605030c04051b070f0b06010f09060503041502030a020a090e04082502090406020a11010501050f190e0405010902 90
    0xb2620030046d0a0081000c01251040840c18140c9503031819003156a00e600722009801011030031030304d551030744400780d0107002d26210580c02800343d000412410709000c011200c003005202d0003415104121758502030952907400b0b04c0710400009250128580c0190700484004102c415040364542c102140903250702c0c0c0044c0d005906040c98140e003005642c501240000d039080d81100c0000c0c4959030a1010140d04820000815020000051040c100240340fa00071000f20301944078501c007540c40303200550720b8075071100380040400c0e40a4003c101c00c52080b0300455000d2b21548400040c1c41130303205010140c0e00107035440740c14160042803401c1c40a91103d0380c0d0005100204007050541094ac64001640c1314400d4504e24106010b2112103041c0404210f1807040d07a030203010041240340900f441b0000350060385040c000144d503248240c0013071005005050603a00e00401034009000d0726000c00105082000701290303188880c0c0400541d1070300c440c401274400c038020130010600e440c4600c104403084841c083d4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400027500 1250 400026250 400026271
    0xb040519080403020405090c0109090b0303090d060c12021c0c18030b090c064f030611030601020c0108061c0507031b0b0f0a09080d031a01110a060504021909050f 71
    0x1107102303141c0c0d01c002014111b46202070000b03203040e44980800e0841c410b014207079801018a0304000b0400c00107600000110000f40c0d15000c80e0380050f0850003c0e0b221310f2089141d0304007003d010403440034060b480031900c0d90190400c000714444c1500c4044912a03d5441a030350305440c5002c0214020341805130708074498044400501e03000c4400d0b078031583d001e006c1d002c0711a41d90345c0203545a460905200c203206100d0080d902011030803251804020322031068002240c4050900307440a650a0040007130382d0241d001600504140b10451004603a11040280407a5000210500441d881c40e02c800e80c01d4007a40c0188042c103501030035400d00b80d0135003003a41000c1c205001c90300420050001864259500301460700511640c070050702c80c08440b840e40c0d980107415940100140c1810780c94040c3c4c011207a0340b0610806441003100c00b401582c4041c4d04d041d503945550842da8084000070740c0c5510a81d402032005000711546e0151240e0741c00c5980755030300320488180d075400501c030240a10f808150b6007c05000e2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400028750 1250 400027500 400027513
    0xd050909040f0c0b070503030603240a050403091e080f030301030b0408210f07030b06090d08070c1d100e04030507030827031e0906070b04051908040302040509 70
    0x240400ca11640003072000d01850301c0c0d05a50010400c802d5484001080641c40c49611003503903051403034503a1f00613907182c0c0c400e02c00d03007a6032024040d14070540950401d40003020017456540024450142500400450800079203c10100b440d00003000c0900e80070104000203114241001c0409180002ca01103502540e8024001040060108204598402d0b40143d441d6122488080d5100300d0747c00d03810410b01c0704640b4a00708812129610950b511541c00c80d94180041510f450500440f445074040460301301c0c1c000c0c1c055201181d003040042c05421f1050640180b4203079140d2060b071041d2144512451000c5429040c842824001a144000f030a030030108030810307040c01e5801070240e1060500060030b020316034000800800d000c001c000b810100b942c0e04020711311a01082943c0f29884040325898140c2c010700c10005240069007942c0510780c0150400b445c221003900e480d810220001c1c0b00700c0e5031744504080c1c1035403c043c0c2c211079410700c2d10481d4615261421881000107407040100000351952011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400030000 1250 400028750 400028767
    0x60705030f0a020309040906090b0a05010807090216020604090c110706020d030b0613150237050307050d0507020a060f08060f2809061e2709050f0d05 66
    0x2004803100707032612892140e42c0303400c502d0080e4214050a1411644649040d072079005201083d000398074160310a46169000b0780d00c82c22207100f210001e024501c0035901400d0706000080080d4000d01340410035019210302500942d000608a500c59040001d000c0d48a81c10060500e802c9500b025080150f50007804140d810050000d641314800d024010415444a0042c0240e80b00c000880329460310a0f60341c000e0054440c2101031200c0e041c901e20708014800c00409006060194454049445480e00c440b08000c1c2001c0701e00d948044240d1082d661030008002041c006401000524031003036044d241c80e0b44500150042061009040d48a00140803958030180f499a6004602552091084641803000e04031040495011103400402c0c1d00d11640c500803000c0034115040400d021501c4100051224545801301c2007010b0080034640c20107030304880800e106c01c1000d003c2c03a100740020101c0b000c01418a0100710020745074203d03001d450640000ca103154800c0740c03d00c201c00303038154103040407868041c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400031250 1250 400030000 400030003
    0x11240d05040201050702040e010b120106060818030408060a060f060309030f140c010204090b0405100612020a030b0604090207031404120602070f0212070905060d0201080406020a030b150703020c060705 88
    0x2190560129a661900003504582c019400d4914181c0c010340100200c080803072a031380c024002d9a00d001d01c2098415030480c06000c050240320181d40309565952590b4489034664100103c000c40d0401881c0002c0c04007140e40003041100324440d03c1c640501080440c94601c9880b60588140c119404050404460301e006c280c2000042540b085286461382c2c45940000710390009008a0207a00803c2d400001c001038032138856000502c1e0410300315403c00c5540ca407808000c600175007134070890011494840030f5695071000755000d09000e140604010072100038103030000b4002e9006804c164003441d40820140d0516500c14075151114a80300c41c050b1401e801d1844d84211940e01d01401400c507900010403404022601f100c0c559126409007800720040d070081402500d56201d4003400c0c000d0b034500030000b000352412155988000e40c040c3c494038103584460711428081e40c000c0503610140741c1c80340e9500c0300588500e0140b400044104441d0f40e105d0043d898001e08000d02c5103483d40c802d01050094001041c0e0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400032500 1250 400031250 400031257
    0x130503133305090f030d0c1407032a050a0f0303020f0c01140d020f040608181c0807171f0b040308091c0c09090b06060a2703020d1124 59
    0xa0400d030f03481c0c1805000082c8510400c00e4483d4050195407861415150015461540c242c440d0300905d9101d01d949101950340e00603440040c154501601510041c0303901d0141c00d8150400010000e61596100c50100e03a1881180d409983d0b0b030740c007204042080c55818044040b9a01c0b8075405440d00b00e0600c0c00003044050b203d80001032070240018a50103040c0c0aa045034800504c884010341c49950720301028000703202c00c51307200c0070000d00307840c4140f90400c0115840c1d07000507110740032107546000150100c41c070290041c101c0d070a20a0003100b4000d10640e020b1568410010000c4891040048800180c0d40041c140e01c42c000b6a942030005100041e500030989403c92000e1f20180c00f21018800e4180007076505201c06032202c110020041441c27101e03a00300b8100c00b40507429055198440e00207001c190320560305071031700040701c401100c2410441e5800c0001c840405000302c9107029100e40014004410084e0112690006084050341714240403d07580301907640d441109040c984e4001d9905080e11 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400033750 1250 400032500 400032599
    0x7030c020108070306180b041b0c0813050405190b0f0f0904170310060221090907090801020a0207050913020a0e0a020d0e060604140910020313050313 66
    0x140000203050b1510942c80600142051080c6c0025403504640200041c40300080343c600075130800e0021107070425039110003c11060580d0756101944029140c041968021043d44160003502e0fa00c000350607540d80c0140343c012400010a00300540b502c0c1d02000454101c50425030188451501ca11115a14149414521041038800c61102d0395145030004004000e0402010340e1480441404a844d171401419801c0c0e408039021a0480c07040e88002c0c8558a52a404240b03a030b030001c2089086508215000681040241c105418100d4035041c0075030076a00031902100069103c8075007000070785401d00d440381e0401d00006402c0e8100100e600030070356401c080e005104600c038038640800c1c0c40d05c2c0180c3c1265240c0e0740341c1c0c004000c1303040b101c68865111329064400c20b00c030700d0404500d0258554609035103409a640d2200070604584400c0c0da0501a420003065070300c000c00100040000301d6001d0000f0031180389401442c99005007001c001d0001c002901090f01002ca810002e20080204003c086032143d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400035000 1250 400033750 400033757
    0x23010605071104060512030c0d02070e1314060703020d06050405060102030316090308030703060303030b030f07050f010c02130519051501110c120105090706020a051209062106130207030c0201 84
    0x14100c1c4000c03c025011644c4925040031896003014421030001c00900034918541041d200460420700089a072030303200d4002e141008135228081004088000b004806080c400c0c200c03840504e601501c05410031000300e80580101303400240ca0807190000c0c0c400c5102a00701200c0401c59401c146000070369a00000b0700102483e44a9a41440401d00400c03000e801140d00500d010740d41d140c80c52005028100d00d101c21000729050213401402e0f482c1c042075100d01d04008100034902c40d481d200400c840110030000d00c0b41400b405040b002c2c0544c8508011303040400310320b100070540741081001c4014a1110b100b00d40c03103084c580002c0c492007158030080c800c00481c003441d00c080740408204901d4207000700840d910340e1100d01342d00b54104600c07064001a01c90040c0340b098444180c0c1c3e52100b2f98450122010092449c0c01c44450030f00800e4211000e02094440a03118500344030401c000b40100b5a0040f00004107005540d041104034544000d503242680ca02c50b42c15420711459540241c5058600840241071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400036250 1250 400035000 400035023
    0xc01060605120a05041a01181406011e1b0503131a070b0a110a020d0207080a2d05240705070b0a0e0f0a0f0b010608010b04060e01050904050a2301060507 67
    0x1488051324280081e46c00d0169410403950b5a00244880da49980540d4001c00d400c1c40c03083e0387c1d0303800c85d039040b248500300c180c480d16022805015034440c074403020b00d81c40007440540408c0c04008420002c0000e080c1c0d20910045a030b401d50401e010079030200310740c880042c4140c0c4041c255203802c80c91040c1c2d1007003a4840862242c6441d00c0304407002078001007840707456100c00450348040242d40080c3c401c503640115002d5621841e00d403e00c16454200c4c206007e8000f042985070704002e4580f00b00c24000348000ca44000c141510a55559030900307080c1c8005030b00042041c0004007108107001d811301c0e0040c44600302149008001e6580d101d94810003400e401c81143e907134109030746070314003808150500d5030080e094808501c81071800701445810b034030040d604019036500108409020390302550583c0d141109041c10149404021100001144c502c94104101403100c0000c43d120303805071501603000c4440c08510809004901c203802c1105e507004580c803c0b500d0700104510b0303801100300c0eaa4141c01126800c030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400037500 1250 400036250 400036253
    0x503100b0f0d0b25050a1101090c03201906390302060c0a17041b14090702010b1e21010501080d0c0201140c01150b0c01060605120a0504 60
    0x719400103201d030011840d407459410410008000f1340300705514042203d405400d2004664041807411503400829410080c2010703441c041c903110000025080000300e5082100d581c2c481d0324400c0b40d4421101a400104001815002d5080710070b8134190684440b01300d0f52920030508030142c20361040c00180702c09a014190f5500f40c1102176007440b140c0345c141e05080c6181d90700400c5a0a41071400b60014003680001c40c51080704c4804503410086190350b0550030b20107110104040d148040c00850745880c6201b40780c2403001088014800402c0041c4039a12891840e000f0702c018044020101801c591405059800b07690325100500e400644041181d03856400c030710003189007081941c0780d00e03c01c280014a5840c080b081504400c3c1601e8583e01521940d0024000907200e0304032800e0000d0104100c000005c41e4080000064900440108000b1513224060030b020118180e0340c0c0c100c0c94091a00281d801202402401400001d000a1810750303d000c10140074000700700c03406419400b0341c984401c007040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400038750 1250 400037500 400037509
    0x90e0c0301060309081909060e0913060509150a0504020405090c090106030e0a17040302010320030a020d0212040309030210022406030102070218040c090606020c090a0615020f0105100503100b 84
    0x240c4142e4241d2003011b4180400e1006420700c1280d1280b08005001408012017600f004050745014008010b0642e0300180a0740d520700c081d10000f401c00c143c4d4464a80301c82c210328a0a0006070180400c4400080c6604090041c00260b9000404044030340c5e109601c50082a00c480c0c1040d41140c000e41b500003860002d10101a0420f41000070150180d079020b41403aa20303801c03c100800c12240300341c81c1002084140208105181c16116440300041014400a003480310a90000d28100303044543c0145000c1540500054940007070344c0c03d90025080d81824021800c2040c0c61202e6904d95000405903070f600380c40500101c5400c66900112440d00d076001c602036480035015100c010b6402840500c0d00701004581003041007088405403041051030800240e1404184075090a44644d036001e880b02c1e0910005201d1a50409070501101c0c0707546541c0055034085c000701d070000d00c00300740d40a040010541c2240900703646024000703540421055200304080e5800107201c002c1d41c021241c0108001c0c2c0407d0018 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400040000 1250 400038750 400038757
    0x120212010b0607060e0d0f050a12020906030f0609010603050903161401020403151b0503010b0a120515010e06210406110f070213060b0f0904060902040305030901090e0c030106030908 80
    0x81d0b0300180c0c00303c1c200013000542c0d001510150740400450349a451140030444001520708072000108400300f0204031201e10601000035901d1540070003501e0144608085a1950700440c3c1c4c0d03200200200b818461185020b03245ea034010704903450144400e0030002c11407902c80c425503d0480015003070110b1581001a802400c01e00e0407611002191181c1e602e09044203191001010307141c40e545030200d0f20b01c0d05a02ca03a110380050500d982c601d8156800c224a080c01d03a0301075002e500038028012081d02c2404454003d0b01d102e8200410307820020f907260750024152089100003c3d03c5900f0502c22111449031040d014000802c1c5c1148540f11500e0794204800104040748030110844000034840d1002c00e1f50100901a0780c0c0709403510b010a003200004201152000e005d266a00501000b024103c1041000501141c100042001a0240d681e40d484001c0b82c2c001e0380104c5040c0c1000c956891030790b801440c080010324036000c072107180e0b00d85107480d0081448140a01d8040c035541d140610240301484007903 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400041250 1250 400040000 400040021
    0x80601302a050301020f070219060c0303050a0e01090510060b07202b02130c0e0402090a050d110906060406021f0603020d030c12020c0303072907080405070e0112021201 74
    0xc46d95036200e1a02d441d840d920400090340241107013248500f840000c069440f0840c0d1040e590108403180c01e0303804401800015021111140d00c4440002c4c1e60300e828454201c003a8883c0300145160122014580c055401da82e001c2c40200c1000d01903a0003040349140d801040c220398401d0705040c405038800250007440081201d03141040e00072980d03c122a01d49034001c0d01c550003107600301200344100c0c40a0040e1001000300f00c0014404501c1c1103501e04040e00500f601040040c105001c40e40c8030000b0a00d80c3e01d0340002135070805100125a111b40c2409492981c001109468070781c81c003424042d010f9610546403511450f41c001c4070281c0b82a004c8907a00580c0996402010151824841c2c203004214451150040c0c4840d4202d40c14090000e000140c000c8140e0f0b005000344d4141020364444645402144510b448040501030480350200c4082c0f07400b6111302c10684924416003418181070349080b034190080010022000018080555560111f42016604582c02c004800308a41000d02401c08241c8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400042500 1250 400041250 400041253
    0x504030f0602040e240f0a05220507020c0d0f0f060c02010f0509011803050702060f1606111c180816030e090705040605070507080601302a0503 63
    0x1010080007002e400030011074800810801d01c07601c40d1103265000300041c4001c04c41408980c3c0f021422410f00c840e4005440070300501100020341c0d5040458540f0603000c2480e9501c5454000c0811508114401c0d00d801901070b00c002c0c0302d0041c040000c2030341515441c402402644940b0362074004c11000c068280e0856500100a21400003e510301074082c084080c03400b010241800b000030b5211005100f40b10740c3c804154990032040440c2e4506603900c0d405294141e8210364108086c69482c0c00500040403101d070300ea2003032440c0e0b40c00b50034071000300c90054082c101e5081c000c200c41c69200c410a0010310a84032140000a8103250840b8903141c4c030411380300f0052044802050f50030045074040c0925140394001d4844640584402e400c009000001f220b0b01c4011500911040c004c1a100f0005040c199100794112030880c4d0b2141c1d01545845003d80c8042090742e046030380c0b801151a1941c210f041c0c03081e440c082c81130860055035000e18694071800f40840341c0d900e50b400401c96114003881c820080c0390140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400043750 1250 400042500 400042523
    0x280b0c1b12030f070809030301061407020303070b040203071203021506030109020d030e0a0b0f0a0f020703050f060610031401140a030c260303010e161115070f020d0c020402030403050403 82
    0x16890640d401c100ca1000e140d9000350f002903405030041458030f02c52088800514690380c24800142c801900780e190300700301d262080c0050801078804000401c2100c1c000d0f0b00900140c90b181c4101031508a1681190411080d10014500002c0e00020100c100b244078854901b0141d803848042801014450350180d4803a540c1071180d010b040d0060240b40c494101540c0741c00382d8a440e41c10844641c49035400c01d10080c6000c0110741c41c0c0500c00c0341403602100540c4107070b56081d0360f00e4440d00c2c03801714821100281d43c0c100078180022468881c1c290246648941801d02c40b0341c0504920401100051283e00c08100a006000c50150340760031501c1c0141d40d0020886e000c11742c0700c0d000ca4151001c0344a150920401c03d00202a0018002069a0480d022440764040f19964410100000e1a00505050901020400d05140400305000d60b000b03101ca41c025401a907e03014600030000036030940d0302000d54110003050b150300b40e1300c5814000100e170141c0340981d4030344a03880c04039881cbc032440d030002d1f00e411aa00e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400045000 1250 400043750 400043773
    0x506250504031e2405010f0f090c110d09050103150303080f09030c010f1a06030613090c0b04060c0201080a1116050f010c0f0809010501051309020a0b0309280b0c1b 72
    0xb014804c1070708460342c0c10003040e07881b140d1031003d540c4203000710b803011001c40d00b0030096911180c020b442940346078a0030b8115030390b680010f90725100c0108080c60100c0c036103100a11441d41d0600c40d00b94560058801348800e00c0c41c43e10f0180503d80081c005800750080a00000c90b8820100111000e28100200800c40146e02610003030007008901320b00e001c01d01c0803c282ea04140b4140040d2805900c0080c0f00526508a01410030003c0503103030030444a40c4080940020780c0020a00548000c00f81034403183d600c90480c5c07000401c10100100221801440c116540c0010003500094600200c040300c03040b109030725a41030291800340b0706005150f1175800c18035414101340d0300a0004980706200d0300d51014540300d42c0005802c1e24404d00881f5080b150b1162200500c4919403c007441d030a0000c1d00e4483c0c00340c2c603004011010780c0f003116040120b0b4400d507401400c0f40f01024160301c0681ea04210300c102d10b1607694500b411410701802c0c0c280802030105449281304c014812001000c19864115107600001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400046250 1250 400045000 400045043
    0x40b010e090a050d171e06010f0905040f022a07060509010c05060c04030b0c04051e0d1b0810050103020f0622080a0327031202030f04030506250504031e 67
    0x1a808140305c40e00d51030f0301146289000c00c2e03501840c000309000449080c0e4480c00111889041c403e405070400c42d00150014284d180d620444004003251580541d4400750f448003114141c0c140c8403018282200307118496070954010948000303803201807506c0b035900e9034408012542502d440301e0103032050003003909120f050b502c800020812648100c00945076075540940b00200c07801684501500980000381c110310443d60000303800c5080310010303ca0704a07601e9503164209020904040c0741600d0034044c2c41400b403042c040040301144000d81c401445a50b0566000c030341545c1c09200510700039100455401282200d04400001c0c03140300008400c03000d03603141c4c8800d580e8000c0200c02c2e4049442c00c039503041d844d00740150f500e4002c01a0703000300b0141072a40d0307520009810303070215a404500003400362100003074030240100011340c011001001681458801c2c03c2080c00c0c480301500042c182c0000100340b16401000f682d0880380c001452100d20310702d5040e83c4918600b0100300514260b2441000d2200203138 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400047500 1250 400046250 400046267
    0x61a0405030f030a02120307121d0c0a050d080304060615030212060901080a021e060a020708010f09030c0b15040f0f05010503060907030b0a090c030308150108040b010e090a050d 78
    0x4101e040b07030701000040c0c51150303e9228041c83d80e001600044014490f0072900700c011600103016140846da8080903102c810304403181c658480700c00401003082e07851909810000382c80c00c508111b4924500c40d24210001d149004400c9008150b0b12012000030140301301c41d40110020420307040c0300c0c0e8140c000c0c0302005000f54882003101004c0c010305008100c542c2821694603050b140a2802031500706455020401420702c40e03200107011203d061990304181e15050b011b0070241350340d40c00410340142051041401e50b4101482c0c012105c1c44c0c400c3d03103800320754800f5003d00b0250304070303547d8105030700c07a0f4050340440764445007510742040c03c0501c010788200300b5500030b0303034074040e202401c00041e600c803020591520390a54400780c180e07000d07070410300108004a41e001d412503030401c400540d001c510356132900b0782d55160b0f00940200c2e0440c01040070001c0080d50b000b160fa8000d290040441c07800e903640901501060180008405507880015030803201000031400e0f85400c9422500c40e0500040010040007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400048750 1250 400047500 400047509
    0x40e04030f030e0d0e06131a0c070b030603070b070c090903080a14190b120d020703260d02070302032206020c01022b0512040501200903060103080d061a04 68
    0x2d1402d41d010210b1140410020300c0b560300f659030442145d10240070415207402149126901d494083c00002d800d440d01c0299502c4401c03c48540d94951407001491410112254024009410100100f03d1582d501041313100c16074007000f43e825201c00140c10240300a800c6900240c681074075202d41c50062503013103400140b1405054000b4085086d400040c03404100c07003a942d00d054020300074600d42000705150446000480003400100c100200e00182070710f040d41c030481138809138000030410703c1805800001050300c00344000c0e00048907548607490000d144100310060502030360104070300b02010301c04e00403910b41c12014241c8441359840180e0480c50f40d0b01134462000540300301d0700711401d10350000c18100b400310f0101c83c0445403e9110301c0850341c501501c405100420500f085034002e45640e0f9002d59008901480c00080c14a0003c40c002ea0a5503c40c01c035444080c000703010140844d540010f50358103581e40149143d403500ca0702c0304082c026000e1900700d03c4c0d1301151000ca04403400200300160003200d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400050000 1250 400048750 400048757
    0x2a17010f150507051e0c030105010b0705010b0d080703030c03110309070e0604060302061b0309090a0609180b07110106050607030809070f050a030f050a0204050a0c020601150504090908040e04030f 86
    0x1d5000c40094900740715140c0010302981201e12103082d400340d0010140da0b00c01030b032070907155400d11040000303003140c10076042070300442d070046040024080240308074904102c058131031280d001002d448000c00d030700504100a04040e103614812803040d100e90021115140c40b10400394890030003080c00ea403500c04502918201a41450008548d49410301a20701225006000c0e503240c6808102001000c21400302014224802007200034915152001c4052203415042000a0142d04000405098070403600c0807003844400c2030500c60104919080307860b0040300604100c0000c0c466101c0703107070140040e0b078840c640c026404251b140505801001d258460344002e0140e40e2610784607000b580916803240500c5030480d48480d410300000e4419001c0c20703d110301803412503200211950000e030603148119041851319072030307814044403140c0402005015050402001142c0181d40704018241c1c00380380309040c4030a4450350401d052012840c01c88000d03041d0440401060b01d09818007034480100c0000e0035001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400051250 1250 400050000 400050029
    0x60c02030d24030f020a0b07240b010f051308030309070f240c051009081207030c020c0114190206010807080f060412181502010f2a17010f 61
    0xc01c6980940b00e11038585200c01d481541036489803030407810000c4040740c202c1c04504000c60400414800380a00f14407940d140010b090140f104036078040b440d10710550a89023003880703548080c1c0e0480e07401c40c1c6561462804d9511981d0340a6500780120fa03544c80408540000070512a07001404a84001920085c1c90298a11642e030251130928140d042110241100155404100c42c0e100e8011750641901810481e44040c50180b01170003100c2c11000d08940040c0c000441001e512080d00602e50b1010050404105500a1004c041d40300e80940d201d2034104860b0994012a514a100940c0e03000240034403080400c045080000c2e640703180a0041c1e100911030000002405031001801e12407908105010b000252220360f02c04904110103422030060000001201006817148055803000703051100305c42002d955410310203801c68820203840800c03181005140d11340880414520200c20600000e04809404002000c0307503100202c1541b10840c5500710300001c1c0b40c4500c40403c00c10703a00380d0783c4103444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400052500 1250 400051250 400051271
    0x10110a0908060f01090903170a060627090c0c0803150906060a0207090b01110a030f080c07020a1505070b0703090506010b28050f070c0e010510021b0a03060c02030d 72
    0x1d44501c01c6903e03945a00f03444005005e50078964214005040c8a4108103401030782d600005019003030200c0f080f20f6190703503c803400c014003580302d4030b242c030704485800602c0c182203c4840d254100404034000c01245da5220640c1441c141d1040301c0c00c51507181c07c0b981080c0c603401e0808880c18408103032107030329124140110100d41c1c10f240c05001c607186620180c0040442031300c0d00400d030010b058aa649581030001c4415101c409002c2841884481c1d07100ea6074440c40504000e5002c0c02c038400c00780c1710040880c000d0041c0c000507281c0c181d9820548116a09040448021210880e5544221040140900700c68000d011945406800c824602d6101e00103445541e038035204005440c1c003500c101402c01b4480300c401048490030003280813103001080e1821a20340702d590041e80c24036900c0300c4401c43c0c82e145128001c000c2541c848000078058402120380d80c2d4402c1c900e00000b075451041207015020b03040780300059401e5a682003440b0009584c0044140040d00002802275241e801503d01c0d03141032400c2645c9002c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400053750 1250 400052500 400052503
    0x106020d0203071b0e010303080a15180f0b0d05030304061107020d0b09100e10060f0602060613060806070504031e0209220618021002010e0303010302090910110a0908 73
    0x329200a40e40158100395040d201c2088058804110b01c0d8129006031021404503050030301c26000e140a40c0351480c050410840780700403074010800342405820004010302054100070f00f005209488184d01040c9455403860300c000800303040c54031903400600c00281800f0081c0100140d48602c1c001d030b004000c50106805082818458140d00960244120300d140002540a041081e00305103480216000101d018180500303d03010b80000d02039550098000885000481c01810040c1c003d400b2881d43c41440c0100c044d41d5100040d00c4280b01c1d418844110965081a602c00f03802007070700c0350860b40a030424a1010f071660b8881d010075113400440c100d041425045005640c401c0c594007400c054074580e5041170a405d442c0240c0080c4084040041213900407074228080e1000015042c803603403e41c2d465610400880c041286c50900541e41000760120700c031200071040c0c0e41180c1e0159181107080d910920090700301a00c24010806603840d00064400226410000d80b003922102e464850740d803034803803404a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400055000 1250 400053750 400053763
    0x1d030304170d08010f270c05040510020a08041a21040209060d020a0b0c0a0507090c020f0a0b0f040f120c06050604060803030c070206120106020c090a02030708060f011e030e06010602 80
    0x200303602400396901b04034001d900140e249001c00502e9001444c08200c25400c000c2d140c40c0c0f0f0580e03000400201e000d00c006c0c03a08091541c156a6140010300e00c08845685104c494042ca214105041c08100d11040c0c4031601d44040301d54200c1350071a5440d0525a4100c0f5a034017820a8030244e00480e4140b002031423900300380c0d040143c41a00201150315483c50246032403000d0740100820107090085101600000c6c0f02040200c0c05000e89580c0440d5000b044140240340c12080c072002c040641c490340c844000320386482001138100c0c0680c2d1102c0604d81c0c80e4140208000e402080061090941060603650276600c1840050316a00c206c106009603184c040070841920071502801d00160400c20110b100405444001c0020b107101504c0182009014844813001c0c003404d034040340158111858400c528680700c100c055001c03528a50850640c10001070042110350010001d83c0140c410455144683e8003400d0156480040d108001d01602170b525001070181c0001a00c07100d0600c104000882c0007800464031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400056250 1250 400055000 400055009
    0x80c01030b13090305040915051311301608071409011d0306040c083901180803091504030203061315090305031509010b0a1d030304170d0801 62
    0x40521080410321940003c0000000440c1408410030001a4040c1caa00441088074020301505036a03e140c00144500082c550b00700001c914984050030000c58441401d55107036460018030140252600903a8440030501c120303500020310514010402040000d644074108072096544070030f256154200b0550f00c0400c0c003d800f400c030b14818050003032254410b100c4945140202200440741013070080100c0d05042d81a5404d440e00036000b60709014101041060310580c0c420380c007043c0074401441243c101017014851503014601c40b18008803c20b03078844c4015200404102807941c0f9120b03074880201c3d9482d404500914040c015158184e189400d10105450840c4d0b00a001740c801941d0b007488000b84100d0301d0700c045400803a406001e01210742c41b84500c45055129458096072800c020324030508050046802c03034840d200f400018041c0a203581c0585007402c000b424003880d80c039022440e404d5085204030f503460f01480089000030b001c10313001040d90030440d040401c1e10b941c0e03500c001c41120300200c01d005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400057500 1250 400056250 400056259
    0x31c0615020610150903060e2401031716060623010201060b120403021504030906320c2404020a06050406140d0204030228080d0206061905030307030504080c01030b 72
    0x1410010192201c0703e41c03404801300c1c40c1501030282c890380c81304112820740d8032941c02070f440000c096000710174007005140012400307180394003a5851641d41303052140d10b035120f003c01c0b16404a20010340c000c04026540c14564801d0081c0406504c0743c3c0450a01800e030740c11a8012584e82c1d080321102d50042c0301c3d0034262259680031915003810100d9540d04410080c104404610070030805161000083c172101d400ba5210355a042c01340d070310300900200200c0540404c221902207002040c503d0f0b203507800c18403500c4d06a0b0000103458940903030840b8200300e04801990009400100c1440071160345c4400248200cfc400c0341c500c10b06503141c1004071740c0c0c2c0c0101d0241401150b10403081100c00511070024000c3d04010f24405450151242c0c0440d8030550103611032003000f082080d280c001c5c1804c4070141000f400400006010746600084001d40d42c001c045d200c01e005000720807044a0040c9001c4840c0c0140001404980e5940150b150090850384603215154940c081d4009030349080d07210b07000da0a004e4500a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400058750 1250 400057500 400057531
    0x30b1c1103011b17071b0602030a05060604080a0609030e1e030607020c0d0f02061e0c2a0f030a08040e04050607020114010b0a0e040f0e10050c040b0c031c06150206 72
    0x40d013a03180c9001516000038040a0380c8031004042262000e000c041d1722800e0056182d08045072000c0030340341e024050501c03130b4005010600c014040026003802e040d0f0452804502415903007801d4950700c6c1c2c0c0708a042c1c0c211405912030500301c2040f00c9920851401a02186c034103070380b04502240c0303824402140c56400300b101c5d80d1510201d07807605070703c8141d14001890780d850301941070740f0352400102282c8007150b020f9011907100041070060024805580c0038030a440c043c0e49001031802101801d410f001d61040c0c051605440d82501e0400c40b0060b201c1d40441c0b0b43d035440e5240d000000048004075011a03040c890400024003092040c0030f20071020083c4a84240c0a900700400c01907190400c58102003001416103002408de5188d010311008034002c24400504101c249510030300704038120b4098042ca078241401d1002c81d41c8082c0498040301c009205950b2141d4080031010306520425040c6008041100003180700881e8540c8981c00322072000060000a0725007903826a260142154000c1d00300d004a03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400060000 1250 400058750 400058777
    0x30402060415020118140c04050910020703030e010e010212090d0503040b330102010f14070509060d05271b0405060406050d0501020a0e0613030201030b1c1103011b 72
    0x3904040c030044803800040b4181011803c05c010072032000300c003510341c0701203035a1841c0604028400c1600141c1d064400384104c0c03500e60308440c1c3d00d0314688c42c2000900d9000900b0400d1610a41c41a071006c0e501c107009000e241899442d06010390440072418000207507000209014080000300c0d01c3c8000300d60340300d160031350307131541c0b180031944c40000c02d9018000da80054030300400380c24280c180107540c0510f0f029000c074182e80000908441c0c1c00c691340c10405190824011410349003000c2d0721b07032104480c034015a0790178044020030800e0048038040281e150404c82400000c5036030b14004001d0201c42100507060607003940400340e46d02c145d0040296203100c6200c9000f201d0038590000c59011201520116600c0cbe07581020075184040007000755103595000c03452501059101c03000d228007110440c2d090381407040e4013000c0c00303100c07641d440000d05065690701c1c8010a0b488000342d194851030300080803544260f2038100341c54107400f41c40080740f09500e490018016004100c180b50038001c41681c0d82480c00520 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400061250 1250 400060000 400060019
    0x32d0f0601140309010615030b0a030803040501110307050c12030c1e0c150402040605030d141804060b0d0b0604180b0a03020411070b011d04030e0d0210030606020606060304020604 79
    0x20380214100004801c02e140c0607407086004500495602000040c2c551500940007c3d403192103001c0810036040c030190020a0343c450040e41e0950f6040240d00d503503600c4a19001c2c0c0180720301c0d20403542d46e550110400441b640c00c580500380ea19003580990b50640f40550f41224a84411544c80101c07050600091943e501c0e6000c0b2454031415a000d62440c1000e00c0300c2003840c3c00b203094005001c4400b1141000118145401620020b283c00e078020030304508020b40207000802040d8200b80700f0304000c168280201503101c2039060f50500078004000e25602c5001c134131910740c001080c0707203601801c01c50384a0f690305006044804a50100440401e07408014403a40c7c040c0443c4070f111980b08243d20b00100150352144203020f18600c0414074a5512510b81c0781c022400d42050340700e40e40c13900c1003111060340c08004244040d8082d5041c43c043c0c04101c0488001900c0a071400c1c0080d401100800c894600640c143c0d0084d0180d0340302d5021a102c0d80c2d101800c101c0c0601c01154002d400c04820b02c81007101c10380 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400062500 1250 400061250 400061281
    0x182c04031d010c1e06140a091509020a060f02030702040c121407080c130306060914090615120a0c081b040218060c0a080c0c010f0305040515060109030203030f032d 72
    0x851480446c1404000403003540c0340c1c4c8240c3c1c2e00004250340e5a545400c000c0011454490b000d00300505104060640d00000c00300f61880c4101c10900501014501e00e40c0d00c01e2040740e42465000b4800c0000d03144d401001400084240c0c100401c5514006545010310b80004209100d0305240d41d5547c0da80e9078440700310815411401602c2d85081542d0000720001c0d400307019180150007418000030380350456112044102202170120394a5401c441b040c040700304a0030ba682c00ba034003c01d640c64202e0211888031140382041c02603000c0d105903241200482c0212011607180088650007045030182c000013400c2008a228110106004030f410054100c002d00b000400761800503030100aa400c0d204081d02c640d0741e0303584280d121f000c19400400d180740c41981c204225007400074080c03070108420314165071026600c021641e079100c010a60b000000d445684911103a101555014040e0381d2107000035003106603581c1082e40c0c1c1840706817032550980400c1b5004c0c40710001c0803940b0300400701c2c0d607160518011003422 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400063750 1250 400062500 400062503
    0xe061906030c150311040605070f0f02030105040b090609010b1c050705030703140d0f052d070f0210020307030917010b040204061707182c04031d010c1e 67
    0x68940c2000800719020818401c000e062159108104000701c4000801301c54000b68150580942030009020280e03003d07055031a01c5901110444900e6010709000d20f200662481c000d40c1903092208201c00c002c11620b2460050f0400400c940d02603c036064800e09035800d101005401201d03000e034110212078400202c420150044041e600101d0b21340300428100001a0401d407540b103400f002c0907804460400050032040c0262404903440c15200070001e180c2d2141c00421402041590340340d07458144e8484480c0e07000000c24481d20347d174030110b00d8584a5409049402d9226048a1204d1001e417400481194a803940c159241c25082e400c2c20048070698040403010200c03590f84041c920003e4903584010b001502442c0c850041400090340140381144c00145403000300022f40b201002d25021218070a420350300384210380e90030446265500d00e01c0002102c0e80c6031402003040240404e154021450003541d03026a22015503180d021401500d04055002c401028107030100300030400032550803803d0807a00d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400065000 1250 400063750 400063801
    0x1505030a06080a1406010b0a051903060f1715091c0311070803090c040b0f13020702090a020307020f0a03200c0a030c050f032a0a091505090601030e06 66
    0x191200c0340c242c60f0080140c0200ca00c0320030700b42943c148203020000e10340144415059180382912a45006003d8000c46080d5050920700792103001e840ca000307070800300140007582402038069503240300b821320007a62001c16a001b40a50b004043c44d582c1d403045954440e40a50340201104040242240500d01d000540f200070555101032010000d021800101292405000c0050302c904081c44d1160400001d0440c140c41751349000d00400561312103007545da41c690b4003110300c0040e55240b0030f110b002030310944e00300079803040c0c101081014000690303011313600440c0140c1c00ca030640005080030954507000c52302c02902148412000310243c000100398a0004000c0100b500c1c2c05c101080003217004226103800850384000ca02c101488282010300100b2900c2c8402c0300184012448011410702d10141840308001044075020040b00c55221001040000d204445003000500240d4511040d415924011b1510807040d14010450940c032038050781031000803800c0a03000c02d458401080a4200d240341c03031f56030b03071 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400066250 1250 400065000 400065011
    0x1d10060c02061201090507030b01020607020a020405150a030807050114040816020105090d030809011b0c0813080f0f060a0209061204020f33040b0a03020f070b0c21011505030a 77
    0x803060900c1c2060090208000100da5407c11080140944150340c500b0380c11544140100140b241c0d00048104450760107590001352038840300f52500c0030482d1005d182d6002416001c0c00004c10448000a0205601403c000c11409006201d1441c2c1101d00b603a0143c80380c581440601c140000204e01307071080c03610504080d80750800c420082101c0008a0740d041d00407078203140c01c21080034428040c150446000c10203442000450007005001d84145041c0070744030000c003181525021030484080c1e405022004202d44442c0d900012032940c03401c00120211182c040c0a01180480300180203880015800500041c2441020008003030085401441aa4031441c0b40803400f11503254200104140e0030103100c03040c4204080120701c07004601440095141c2c0e4001c010403c011418101910f04038241494050fa84016900d50f54082d0f00800c103002d004e1210010600188070341800040c020f051400f150303942c00d841c0e00e0364446a00d20007440792440c1d20b801700c0c000d80041d900c150b00642e800f084a00d4000703403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400067500 1250 400066250 400066267
    0xd0204090b060a05010203091c05070f270c05120405070b03130b090316020d110a060f02060901060b0301150309050303010e040b1303091a1c02041d10060c0206 70
    0x10340da00200103603a1600341d1401c0c00b44038140010390700050070b02800154607041c81100803c0c400700b0000e540c159108000d0410b0400c000c0c0c140f11850090209280000101d07846150344000c502034844076140380042c004200840f80c0e0705004511490103991900c90904024840c01d0305240e500400c100c07100d010b89000030540a840c1401746005400d1a0a001d041001e2032800000d8814003408541c95680144901454002191410000f080d8103444005403400391785014021050b0301c0031003645c0841500c0d000f040256106c000015145c0150f0b003207540301d84860041d1401c03203006003c0c00ca0202010401030004204000407000c0403103003443e001850614035103a80d803c6804c00e07008881980c01da1014001805110030486400c414140e410600302d114540c1c02a1811409219042d950f800762074041007100c10345425590a24002080080000c00641c0d0800003036015008040da0110814a1816100c1c035410820388540113091b08008042c0c10008251811400c0e40800c0341e101004021611 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400068750 1250 400067500 400067509
    0x50c01060308092b020d02010909090312060e040b010620030414040c170708060111010507020d090f03030909020f130801050105040b06031522090803060901090501051e0d02 76
    0x14001c600490400b0707162100103040212800c8900854600403c1c030070006102908440642402c031541110900b03060041840180d4000c0030035071080754100d2a08105209150308403600041403a404101000740ca61039180d080131044080c0e401810000040005100240c05845110300c0f01c5042185040c900004014445c07960307000360400c0c1b40400d001c030042c0c08030381040d01174200ea4110a0811002044000031441180d00c801010141009048808282c499003d1989410305800600c000e100c3c514000740e01035507810075402c0800014503043d40c00601ea0310f9a110f080c040d2549607a5055000345050301300c2010750803880811840b141c0400c4004003501003001100000d0000f40c0000c00d0b55031424042100320b40b07000030341c1070103a0360800800c102d15404401345d00c1c1c45034088680c2001b001c030590301d18101d88000a10000c00b01d18080020040c4418440030b144140c80884007003e05a80350f42d142d0042d68070a05c0740640188080d0000075600c100b21064034030481c005000ca09001f0080e40018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400070000 1250 400068750 400068761
    0x50319090b0406030f0629030c04120807050607020309030705120312040c0905310309031203020c011803090b07210804110a06050a0c02041107080316090308090907050c01 75
    0x100400c0e510880820158100e0003030704010700f05d20304604001c0389108148403031f0f405075002c25504c080e4000002a0040411410b540141408089030000d001c1546400740c101c0c0d1150303400341c0340c82c450480060007042c4001f0868881640103005020300c00c0c502018024950082003e004050000f032111410f5104040342d140e20030b50103a4621071856281c2480282150400f80907100c41400c034900814100303060302c0c4004d81c800907010381c10306806000d0400311484002600002d1030340c0019098905004e0341038018050100035440200304101d81c1c0c10000d44082520b240007404580301ca00f04010000b0b01801500805025003806c848048802202c04285141c00c0048404520594180014000180e10301d480042c0c041d04c03070009541c241480a4400d0161203000410015031080200441d01c854100e4030420350a0300071181c0340c400c14a42030140360000c85011610fa080740c1205041c80e44031701001070440c1e4200d0881850014000d00b80010900b005140c2414403804110380b00d00e041091103507 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400071250 1250 400070000 400070009
    0x100c0206061203040302150a0e0a0e1f05030a1410020c0106030c0e0f0612100207120e0d0b0a0504030306030b0717070905090109020d0603021009031a04050319090b04 73
    0x90800341c07070801d00b0401d04048000003403503140d005100038001615240106000b208101408544410342c11200300c40842e0080005500300c48030660020b42c500004070000c4c01840181c008800f0074005001501500134644590740c0d2540c030072007080300854020703904902c06601e03070030a40e40350403000010001030303a120780703130340d00d59a0342d92602001403101403c3c5103006010714419a42c81410120700f410340003100a0140b40c03291800048440c01a82c003044200b100b100d61490947d100c040c54202001d0078146181c408012030001d41c080340c1c013803804040c4c0d01081c60781310048804540b5804106070040000030300403410705513210804400310b84ca00652a10030661990b4806090300d601c03d902804800180c040014081781754001d000651740c131201c060640e40c6407000183c45182d04c0c24484050b110b268000703900255184945441d459004c4120020749002740c000003031a4201c9100441500b03421500540960828086c81118640d440040d0400c10075a18001d004d1540710b554054081e071150b40b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400072500 1250 400071250 400071253
    0xa0e0105030606060a020a030e06190e03060a090c1a0f070f052514060d1b02012306010806040f0204060c0c0f0602070b0304080c03040b3612100c02 65
    0x400207807404215007540950300380c9826007000c0541d20040d50314103070400001c040c0f1407404c40403907150329220705031240e9610102c420a00d02e02185801780040c10b4500c0c00fa4001d000308030000c0c407011802e004202009512001c0c00841510b407800e001c1d640841c490114540b414101300d11102c06000502074060316000701e00740e40070040c1d5032074080d02d030440c0120b484415030048092021703000741d001c00d0b0034102c0c0d03448a41c142c01e01d07280d4000903107148034201107004850b1a041d8452010003003155a16492404d5800800c40d00380e0820200c15004017603006079952281d4400007a0580d48500ca201d900300b80c028001151540d0080400002d036045600311200081d56602041c0a00058149220080207407900c10900c1d40d04007000251200c108d401208900703000000801c1c1004659000c4909a40620003a2600c4645072502400c15500258020b071103201070708003843c081c60981449007d02880d182514062004000510170306c1000f00401c04014000c0b03005108a950750383c010304058980590 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400073750 1250 400072500 400072529
    0x7081605150a3b120301060c020310110f0a0e0a0b0a18080604020607150908030403030f0b010f030b0a0801230f041a2710050702030c030f0c0c0a 64
    0x24410b100700c881c0300080e00000c4101801048104003548001812141051420801c04100340409840e140b550300c0c0613900f0440000001801e1039101640c0d140e0140300701d0940b0090203c2d85c0c4000180e80002410020380c8400b001180780c11881d0f43d0060222a540d41840861241d5000c0010711903d8103500030741c42e038140090082c01c22580101c500c1100c03140034100b070503c41e007800c10320343e039030b010003003009000c0ea000050f008140311030341065a4418020741d6082c0628807091800b40390300d400503a0101c2c0400d00b820b40b030380030300d000c140a10f041c40041a903482d203d903000460110701800400c2c6250b5000307024a5000f01d95518207000300c41d0a200c2c3d00140010498140c054109400340060081c20f00318052400d01001408110081d203035422011010195602d59051850350150b03070403c01c030011440071044c900d04c01008100c624503000c0d010803c000c10394a42d1401da0312032088556004441c0c004000808405281308040e240c4100324408840c20181c022011034501541c581102c1540100407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400075000 1250 400073750 400073761
    0x3020405180d090605030c130302090403050a0305060603040201020d0f03020d020c0303061305040f03120605060c10050a060f17342102040506031f0204080f060c0708160515 76
    0x100503a000100b428036108803800d14124005045001c050a10b20608000060810b581c004004890380a0360b0014418900c40c10180f401420650040c1c0c0300c030000c241084001031180c82c00f001502c1c442e03078040c0c001c0c24440c1c01a0004440018141d010a0140342c0c0c01d201491001e1503c1c4090044188440b000719600e041510420940c9820280d000303030b02c2800c00041000180e05020004500ca40c10300b0300030280000d540c408400740a16411181e0450340104800d61081c0c00040c165424000d03140701006141c580e00031000a50b281e44c001d00921030303004c42c420882c0700011101d0340401c1c4a1801520640700d081c1c20112200c0032002c0ba41c0c49040390b021801e88201048220a00040c051017246048216001c078501e02e002d819210082d11032540c0b6000107082d80c030305001c450270202c1180e000c0302d820400324007040002d42081c00707400c07042e20600300640420f6070001601070280282c0319160b810488a41e507411155484a00e15001d108841800741c00025001c100d0b840403038852000000451404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400076250 1250 400075000 400075003
    0x605311103070305030417030702090a090303050a06140609060d0908030f2809021305250305041104020304030c0f0c0e0a09020a150221031b1c150302040518 69
    0x1080c800d01e210ba000301e0000c2000500000444044507002e22140300389005080603070b4114010340030043d4100f036485080010b09100c035403000300d056109032410001501c07099042c20403184035004030340800d00c810024554525240b80601a071020040c8001d03e13005580e4402c50a44540c05403c86041a02106010341c2e1280781007540c3d4040d1403000c0001e46c4007a41c6100d4000000710210060080343d90f000040d0554032600329500380c85c90014000e00103828040907400700b0700310495240c04802c0a03007000b60901440303405218062030b040300940d2060f0300038070101310080d800540b0841c00d11140224900000300600401e2190324000c120b144880b901e001046009164020100d48030280303040500740060f60f5001041058441101d406d00402c0b41001d0164500311660b004265100c070700700c00800380c61840b0001903102d0780312f20b0410302a6280384c901c05101400341c1d2a507485884000507014480f080c00742e0101043c046000d4840c112141da940101c0d00310b900544010760050080404a40410350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400077500 1250 400076250 400076273
    0x10927172701020d32210103050f030a05040e06030c10030b0f04110715180606030606050121181718030718020d110415030c0318060531 60
    0x3802d040a00a4582220f03026081c2880c401700d07020f030b100460303040303001ca18809410366590b0302c2c6080d08010b44084180d000d0011075024401191140f080520079001c0d000d002c07090710150740341c03034aa0b20b0030300e4181580c03a400b041d00107040399018421111000800e42d218002c1103015074907502c00042a840003010f0210f100000461240901e05000d40002055040d204603a5050b030011200044202086030b41406481c054840c941a07502540b20300d41030140300d511000469204000c20003205680c0c00c0107480d500c01d140c002000c024019503142c0200400c43e044000e800b401852030a00701612507a441540350514503403808000804108900301000e50300d14145110012002860800c0c903064960031a0b001651041e0017240d00440d0128964200703030441139041890b6400076443d00e0711240c403005c052550844500010f82820540f4130700c0c0d8081d1040c40101c00d43c40c4107020004209803a004060000030b09290050f0b0600f12026a002d0086511200d9840b445040b46001d03060038100b5178032800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400078750 1250 400077500 400077523
    0x706060816090c03090204050126010c020606060c070b3105061617030a090b010608010b1818160f0302030f0609100305010207080301092717270102 65
    0x500c01551540700c041d0070740760700007264800c0c0703000304070488024000c9000d000443c03402504241044008101d0501e205181d0522013404240c5101c1500403101d19400d81e29000050400741c0c003d0030219049013080c0008041d6981c050317007118940c0d65102c04515103680203005840c2d1500c1e2f86100c841c561198415100c044603d1051410304440c209000218148580400328410b06041a40c080401440450300c042080d1040705a42e01d0b8904882d00002602e0170301800c85110b10300d0070011450364040c0480030705035604a442070741001c0403144c3d20095004502415940802d02068843d01400d20420f6107204041c900740b070522201901202404007074103000c1900505006000b0000790a052082c83e0f9403161007210040c03095120404010314101da160809080e075400000e0344410b009050300214100c0b51074030703420816a41c200782c012455401601c0e440c095034104440b90310104038032041d540e160710b05a060141c601500c0b5488800a6240038480c03040a45441380c8020141d0307014442e5042c40d1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400080000 1250 400078750 400078753
    0xc1703180a05101a040e01051509100608040606410f150c060f01030b01120201081b09120604020f090f04031b06140f010f060906050d09021507060608 66
    0x40100b50340d001d8464080c41c0b4515445691003081003a0301c0707001c3c4210b20340080054020001c0000c0ea420301400b801d4101c80c5800d4525144001d181d8600f491744d8003a106240920104d0482ca080a200301c4110101801c141c0303e2941b104400304000c5607544101c40b0b452690585003902012140719100c40c0d195154640e40c80000e1821052050f44600f0341c240c00005040328605440003106105164502601e400341a030b80c8500c01c01c0140c0c8001c0440e40a0680c0c2c05104042500d030390713034440e40001c0c020303154000380021025400304240d1416030780d89401610030203034001e080502c2c2e040410341c034030040d4140c0a4150b008100340025810424075020b0144070a842c5000949007600d94010060300203000101001404114100d10103152007862205d198002c109201d4044800c86010401314107540c0250b10040ea1400041c03440c80e110710800440c5c071140c403450406481e205003078486410819562000755110700900d00140c1c0d0b689034030f0b1030996407105443d4951250f030801d08100d4081c0c0d08070b03000b503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400081250 1250 400080000 400080013
    0xa11031305060904020d2c060c0a0806030106170d09050402030705040303050a0203160f02010e040b1c0809041103100b0a08060906040e0a030f26070e010c170318 71
    0x42030300c903034190203550741a01e005a540c80e00c080810024811441c00b400caa51400382c0300218921108800032950303224100c0e41c40481407020356940c403400c0c1980c0c0e200501d101006945039035030058089590055005000140d100d503aaa21758040d80025440c01c40290404010021029000300048002e000203490450442c584624060030b1441030b400058140240495901c000c58400c1084400d0942401c00c80c0c11600c8051a080e1705520800b00100c1c082100c45c4c5015142d4103083c1301d01e80301c4c1c2900030043d80c80d140d282141c521041c00c4101041d940080104008001900e80d8011a1440411682a99924542210030000c42c51180e00503e07078009040001c541560740c040301e000e4004000300c1c0c88c2d1034503071a0100040c0080c0781002c03400070325000351154441410307045500300b5515905a02d03200318141500003101c803004280d0090001034020071001c0b6104911a280020321860181000b001c40c054544620317401d54003040b000c01c03041200000b0400880e00d1050380103804c10704c00e07000b00007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400082500 1250 400081250 400081267
    0xa0f0207050f0d1704090c0306050d020904060b060f0f07050d0f080c310f050402040b031b070b040b1609140111100c09141807030e03120c0a1103 64
    0x60750002d58030318812900d1035a120300b80b00c60090714424441024110596903aa03800b081000703850032800352401700c0d150050004207414496400700d030003a80100b64913411341d200e664090042403502011030300818103004640d030702240c0e200281405a0316040d219100c440700d250a914104811105104210150400c03541d466040221030b5002040710030310a459000c10609440c90b00396407044101095080502c0c6901e60071801054403c0e0303004005130194454444061000383c0c071a92250016140e030800018070b0b0295820905030350400c0614545140c11442e4941204a040031390707007510a008000c00740b102d203092220140b50904030a00b00b1200b214900b04032040c4401010307100c941406512681100d40449c240402501c1100d9620100b0080c070f150080140307800d60501400000402081c2c5511581c40c01c003881c94824903600601003847d83e07030404114007400099540c2e41c86448140074002d51030300d902c2c1c00c05116210401000352515140e1100030140e0f803100946008982080040c0366 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400083750 1250 400082500 400082509
    0xb0903100c05070b070c12051b03130b03040f0b0f180a11041503021e09060a0b03041b091109010225060c050a0506090a0c060e0a060c06150602030a0f020705 69
    0x5490310b403c0004c031021540c48040a48052102207002450b9003074085500b0151500308014061850219061016500031011707642d680b4466240c25082e801c10071401080002044002158403602c112400303406c0b08030650340c5038941101543d03c9500c100c011400c2060480c0030311029445840c12074000c00a03103140e43c032104031501460744a0303030003143c0702c03000340d180d402032022140011940030b440c1000746e81c0c140b100100d0604401000318851540e11011504a240c9100f216040e00e4000400c54a580c50f01d946084120300b052412080903060600000381855030352040043d000f002d5240c03259a600c101000900300382c030301e4000d0600f1160050403a0440c4039801510020356038039050108041003141071080c174003000800000d110b44681d4040240050010400600161082d03c4610324261161020340f89402003045241c0c1110300602c0c1008518421200325901c2c070700030280069204070038100544600481d4020340d001d42e100151198001c0c0d882030b00345100d07550910240601504250004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400085000 1250 400083750 400083757
    0xc011d031c0e01140406020315060903030f1c0207050309040f140c0d2414030607021b010c060510050108010b0903100e0c0a14043905090a0b0903100c05 67
    0x260306141e4407000d0540303942c4250f002102d4072890703c0ca0000319103040c0c98104082c8d4821103048846000c075882c03002e980c0c146207044e203424407002006981000308042d01d0113419000000312600070ba41651101294000910003801000c1c0540044c0d0382d039903581d0081c0010b40340c3e8000d40310955480c0400c1c80681c0660304d507205403c003c5006515540382600d1110402a00071000c0c2440111f4498400d05802008070381d000c13089509550103403a05440c0e040c101510750400300d51910168228075292600644500c10300c0d2603985050404807105180d0751038050840748112554a20070a502009100d40e60b0080395880c014480056091311303081c910008643c45003d10116608855101c4134070002015051181070708580000d012281215610754281d80c0d03445498003d03034022442c1c0f144c004810905201808220304005070040011a5490b003c080c2c5103405007680d41c100030007800030b01c1940d81e0700581500280007007140c140e100c08118080500340381c2c00070141d00440d440c05100541c1280c2200a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400086250 1250 400085000 400085047
    0x714031b0102010b0406080f010c030e0307110a0e07030b12010c0914040204050d030504140a151110020c1f1802090a0608011103040308070804020109050d03020f030c011d03 76
    0x4003422810303458010303400f41410f00c01040d402428008040b401c80000107443d9031004049009120806041c501a012944165120b050342e82040003d58086581c1c20000100c03a20080e00500d0003541c0e40076020a0341609407850781c0040c0d210104415589000481280ca42650b44008c0000519005024010725000e2040002ea0a1861810517940d9510740c1030360000c0502a104130300000c1245001451755106025405504420425045240c01c0c0841400161103002c085540d066650303410958440d85640f0050045200f015841c60002005001922040c0c01c0e180081100c24a14241701c4d08490b01c070100d02c0000b520b014440300d46155041d07442c038071990301601c04008989408894201402060300082c2c881e60900100d0f100003207110b00214820790007a5510b10301a02c17514821207021405481c00390026220074024402e6150820078006214402d00444110314101070f09503045412541d07150320123940d1040400a011398101c1081404060300021b1480d28540f00402008200203004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400087500 1250 400086250 400086283
    0x1b0f0f0717031606090201082409040212011a010f020114010504020306010912080a110c090a0b03010902090c0903011116060b122e09020108060909011b050c071403 72
    0x8054030312181c18412181150400c3c0c005181590850a04134060700b020841240000c11100008131034240180301d0b140c8140d884009010104144e00400901c0400513100340e034001031454014011983c240f00303c4843c4000109902101c4240c0703000500048100b40009007964100032245000c41a00307890141511070880d801626900c4c0c02004a444001c0740d000500e50044074030002080c0000344014010401940d41c1d203010311281c0c444c541fa180c00c4440d01d410f400c0b00c1c0c0080894280d1000360820703000944060000242010580c000440d500410751740616049000583c2c0704090070207000703e50146e0001103400740341504400c21044142d00c1c0750030103001c4580d0381c02d460241c0d58620800403101d11115040f2140302d441041c500104400745401d40d8094580314440409a110500480c440e450b0141c68105465460780103000d00501c6c0101050305c0e0307559070814025030794492000d428603040c0341d50303a80ba216032001120700d1800036540c02c0b4460044c07600c0d58414050340c1c00140050001c01184 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400088750 1250 400087500 400087529
    0xa020406050609090105120a120203030a150303021b13020d05090d05091509010203190509041409030412020307030b010e04110f0603041407090c0c060506060a0516171b0f0f07 77
    0x1807900d040102d1618002d04100300d2201025549c2d038000082d41c05400e004000300902143c1080329122a40188002070141e000400710341444040c5100307400702280b000c2c00d42c0f0381402c1d00a103040300300e0344407180f80140700741d980040c850840e104121104a0100a0402d146000900c1e8005201a000c644116002500000d44480203034824429203c1c001003c008007a040081031700007404982002c903845001da403400d818407890740140414140994208000340d4541410a0903507143d46e2048801031303030540b1403060000002401341c40e42034000c00c881706035246142460f05d40400c0b06c40c00c07801090302c550142d058408045d03171600202c0c0d0300954080c202d10101400061980d0030040380398030090340d252401e0040580c45030060380c80b01105200d804e0070012540c81a0402550f8021490408000341007404883c50140c00750007404031441c011007608880603008483c100c015401908405074642040300e840f2021b50080003842c00c183e200c007020348070f55004000704e156195000e105851700c800004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400090000 1250 400088750 400088779
    0x80d092306032e21170f160804180c2109020306041112210a050c0a060f0e0604021008070c0218100e13030c0c05040203090a020406050609090105 64
    0x888141c0d0400f03000c2d5207410f0b000072056075103e0100c500c80c41e40614208400c0842d0300004c0d2001c032203030961048110501e610001c4400d1001e4100388907403503220604205281d8004003180031013042522590115550f02e007020307c1d02d4859500740034043c2d0070381d052103040d80c181900544400b01e80321a107603228051507841c0c5c01d600042c146042000c3d416006800500080c4851010301004150003540c1d084402d0100d583c02550b02c15825007002e00141950014400c0d41c000c1f00c00600241e0118a003441c1800716156405040121505041b180d01e07944460941c01403605003d502201407061000d030081d8a81500490a241c0d0400d40f40e40c00c0211101c00140990b00980c1440c0c0a5070b0007030071121f46201e40c18508035025038280c41d404c8072141101c1001801000a2241ca803240f501c42c5c8802007000d440340e400f030b1807a42850008481c2840c4110001c641612a880618810501a0000c121000a0b401480f0466a103a0070150280800b080a041d07151a400c0002e030454401380c0c0c00343d4140406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400091250 1250 400090000 400090021
    0x6080a0c0e07051c09060e03040f0e040204110f0304110a05180402120f0a0c05030604030504030b09100e010b0108060109060c2904121b0f060203100f080d09230603 72
    0x180c40e0b1000c5003040e082000000e400180d4070042c5e8007403042c241004006401505544d89018900c180700b4640710120b824001d0a88640c002d40e08035101401c041005107141e24104116003201007011420300f004400c10060150074441000742c24010340e10f078400103042c000401e040d10301080901c260048214086002c54031220301520504d00c10500b50307200d03113990441c4940c85190050054072002140c403801b1440b07280204826010700c0d8903456242c9490b24581c2d54118402c40100381c8080c41c007900505a078840c10a001c2c2103801600321000050000a0b83c0c005030007243c001c3c01150400003401c005201d855048000c021080d50801140c40310000700b41034582d4600440c1c3c01d44240c002d007001c103000030020b035025003ca03409455215034002c05e003450b803298002407640c00c0103400e00511303030b0055001c1016540103603081098420076500340764680c0c2c0a0140c1d0f02c3d055000110f6980712400740c000c02c0350711000103c080c1070f4021000c0325185801034030000003070b19050018403c103000070105840015 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400092500 1250 400091250 400091257
    0x40e130320010c030b03150417091809010f0509101109031e060c070209040201121404030207140f100f051c0c031404020108070f02030c060a06060306080a0c0e0705 72
    0x4803512079412070808001000d010300381040301c85001c00d0410403513210310300d0003045d42811804d0784a10341c1c4481e906d40c0c03180c5090814080c80383e900d41400304001580c60311500a03441c101d4604100c2600309050501150382103c5c080488031512070329140511407400e170081803500b055800d10002140e4500582d04950480c1315440300386a161003902042c00042c418065030103c4041c00609480c03c0390f9404540c80c81a20131941d0007580304040100050041d8041c01e2a040000c0b0300110000f41c2400b484001482e240c0203a8081d001b40c1d12001c010442031000e807495040d22030017a1124000d41000002240101088445240030f00c407401c0003400b07100307104809075035002110025094801d0200850f9200800c14818400002030506035880740c44c0342c0d14405036004642c10b0b0348824150f1b8540d002164020220411101140820000803241708020030145014500c1b00400240706c0b03140c40c41c081d045800c0d1358030400840d004205c00c0c070701240c004a0f40d1002c841005a410081e41c1d28104110303410320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400093750 1250 400092500 400092527
    0x60e04150303050f120906061c03020a020616020d240c050306040f020c0a080a090f0e0f09010e1b0a15120c09091406030d0519030f0905061e0705040e1303 68
    0x7601704020800c240002c07003e021349002d80b08011030030000b05180101c0c006140c0c001e00580d010607423440050401000400a482c80d603100400f001a80741d0004900c2c200c800c00c15280c0803034041040031a80070b030540b04103091a03203880c1002040c44891000e031080c040103000ba84a01d40d61000080d011003560115880400000203489220305113140c8000705411042980e0000b0b000e650002c01c00742d031000c402c1c00035900c503c1b540340065030b076000380f0300e502d0140101002040d5407541c407000d203480d50400c51040d5041250801465604000b0240700205101d40d0180460f280d403210080070881e00100b444c0c0818002100102d6200c0c50745005030303900308442d4010240d00780303461050088030866200da17600030f40c4203e064686181e5640b008591034014549100c584405040c1d0100c4440d00950080c828804d82010100741502c941d125941440000c45142c0e070240301404411141d6888909220b0340520075003445030a00c0c0c1080c0014041803c018011405107840300e82102c140b500984440507020f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400095000 1250 400093750 400093777
    0x605030a0b040308091f0213081b040e150610020109020306040f0b0a05061c050a0c1e0b0f1603050705011506030c031112190f06060e04150303050f 65
    0x10503186054854044216401d0300020b84003408103140e540c0200d0304150b01c040041481d18505c019a11000080d8000b0b4540c044101c01032400140000040c8400b0180c00a0b141143c1302d800e0324501031105076221b01d049501ca40d040099141010100100700c260004070543c0c0f5591441020b403c141d00524903100065414031421003040208444801d030fa2646522890b085102030315080c2c4640709075001a81c242d544400c8803840003039240b07801070342d11900038024000c8420781790160702c6a0820024581111240c2403440221502c0103402c4400d00e4001c2c102c40c4111403030040b01d40700700c40e9940150b408440c40b914038000000c1c00d06100e202030380c0519070403038002c00005249100110118410f0300c92140407e0410440d55107142c0244508515601c0b1184418503140c0710346801010b0440027800c8c005114034108400d0111070b540e10601c8917601614400160740c1d410200040d01075201959010b01c00c90a028401605610340350b404011280e16080481e11841710868000c103501450740c680300d02 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400096250 1250 400095000 400095013
    0x51009050f0a080304230d03051b0f040f08070308031906051306231305060105070f03030c031802100c140f0a02090106090e0114190801050f0c0319090501060503 71
    0x502143c2d200441c041c038850032044800b5840064000c0c0c0f00c94158072081d11603084a0114041103020390400b0703500403010340c0c015089c43c0c00c8856100d807a8101c80410642c0c17810104017400400441110003000d081135600400c080d603d150b039040714030300c4000c015915440507550a0789244542e40c01c404080c0070004c003108060b0034011003c3e0028401d522441104205034403608031000a042030088821201130582038502070398020300c00150238013820260401c40104100004982c0da0401c1c1c3d60031030b01c03e680c0490500440c41c8000d080c1d4030402c03040101c4c942c641c07580100580d907208500f00b1008007070901c114941074a041071070245450743c0074440c8501404158542201010503400c0d480d900c2185e8403e00d80e600d0b1841102c030403071240200b549500d0f00b01c0040c030002e10112230060100c140107003580303c05182585103402403402c1e41e000d0a02603444034140301c8140034424507180c4c0101e01004090443c42c180707400000514501c080d50150560f00c41c00c0500344802900280d01078680034084540c03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400097500 1250 400096250 400096253
    0x90b040f1404050d1d190f0b03010e0106090609090e0a08041206061d010509090c0d060b09130308130213060605071b0e06060306120706230403051009050f0a 69
    0x101c21003154101d8040c0240180308000500440240341ea01d5818000300510084110500103413050a014030050420113a20002c0c10380d24000300720019005402c0b500d9140d524198864070480c6060300110144201c050052103107a62105420301102c0c41800c01082c45011500020708096810001604440c000a800728100003540503103e10b85116000401c961940d07041030700042d1003100b00c038070082465100100b100d468009489034001b00b010782505c102e0075815001800d403c501203c204c031041d032136079200401450010140c3c0d50100007028030820310440e96a0060445800501810040c58040603150954403440e4054a07604405141040096115034000d44142c2011104542c4100f803880c2e40d4080b00d00000c8000c0071503040880000140d2121410003021341c200901403904010340303c1d91420300307a00400c010001004c6a480310150340b10445180e600b00600d000708800d05040030401040010b07000036010010349000100080c4103880b600d060750034258482c1c0c3c0388145101d400140d00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400098750 1250 400097500 400097531
    0x30a0e06090d09121a180a03090303080c09030d11010e030d0e0705120c2202130806011d310303050f06040612030f02160324020c0304090b040f 63
    0x100b684001d07480e10f01c480b5984a240007902c100180f4003d007036043d0b05814554403212034201d039401008000d02c0915034105018904c0c42e24a4544050300001c044400030402c0c90b400ca02002e41044404040358a09022080801d507a18140f011001c20802c0e0b290030031070504420b5000420301c00440d07050340c0da65441c0c0a000c0c1c0203840f200c0f00002075401401c1c800903891a2042584480d03800c0300d80070b080310100400401c003442c8041098507000c980b82d61528114405580b0080010410707580f9010802c90034540c01510b0840b050b08402c84004082120a803180c1c003503600e19901000c00fa40d804208911080085e01402a00c9035501c500c9540d420724500301609a0030551043d0034075440d4006c030360385040400c400e588283c030411414001c4258080b011900c59407144515194600464106026006480e42c80880e0340e481a42c10004403003c204201c0484140c031250f1103252801942400091290541c691081d48109640140c0d031b011940c00c40d071a560030070300c6150500042000650346086245 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400100000 1250 400098750 400098763
    0xc0f0d1712060f0103450b011e0315020c01020f07140f0606010210051503030403052a1e041d0d0e0303040303091203020a12030504050f0a080301121e06020a09060207060c0305030a0e0609 82
    0x4162440201c102142744030912010904480d000903418020708030301d010728002980043d802440c1035400300404400c03820a20001c1050030301c60004012a01118608103043c02000e648900d0160031100500034183c1c0e0004289104a2080c000003c42d5164a00240d500c92207040c6095018007000c50000103201c8045214000385120101c0140c480a261412018099a03001100c2d402310401c1c524008030110040d958180641c09080000e249402800e01c11001800b022500381c944e00034042040078550080b040305213054260300441c1480d0540c0d401901d40403540c005c80c503001d0881c0301601c0a02d442080299a0990030600031403400b800c11000802814007100c0a442e144070701108030381614000142421002d800c916040c0c1143d003040480540b903038041c0e000740c0c0e284294400c40300c0780750350b01400c1c1c45c100380c0715520040e80c61001003800340818046900020540d008034000f04111074000340351112031581450080c2d80ea503544840840149207016825010344030302400c0003a40030001480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 400101250 1250 400100000 400100009
    0xa0204051314030702100302160c080d2601290309010b0901120b010b0d0e0303100f271d0a03090e090c0f0d1712060f0103450b01 57
    0x55004100410b0461640e07407060b1140250403622140170100680e00caa030290942141061702030030030103600d46641644042035004031025030003800440407056040410100d06c0f03407020030720551001800c1c0140f100c1100520564400303101c22014901c0c1035030111540652206868002503ca080c0440c0300da0082010380040d41c050501c940011a042a40301d038010443c503400008180142e090400404441d006450380d90105038980444401c940c0052024511601401c01403081c02d0745081d04844503500f45510074404c0c0301030f40c480040d1034000c24403204096504101c0104560001c0851482c103031000005960040c010f00801e10105030b801200c410445a1198141e901c50700c42c480d01e1625800050340c56a4021040340402c90541003000300042001d0003680e040c290760380903d04040859005003039042c210290041040100d20701a0700605c4210740c00c0c40d0820100c1042000b02c207400b0700084200f802c00d248100d02002140e400f01c0c2644580c00084a00444a070044c0340280407104280603 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 400102500 1250 400101250 400101263
    0xf0c07050f120316030203090d0605090105010501110d0507080f040909050f06090d140d0212090f070f171c0509030c100f051e0a110d02160b0c0a02040513 68
    0x1d01403082d18002190095065070403003e5460b1600d0b03100c642e9500d42108000f1410345c041480441502d81c0c40d5000c022800d405454003040c10319018448034211101600600c1c10b00c074488107041a40013000446454426041c14450355a405608151645010300030709402208000600820081d240c1d030030428100e40705100b1280300794988018a17444a404480700c40039607006000b10507040e8130070100203401d03160f07c0c034070039181c10b440d01c00c2901031740d0210f203840c4404a414014090364800030071800340d110b0002c0c809001e0305400e1041882c0cac0222203204050080e4402c40724070141038002d001c81c107090707181d0312400909440b0005000c0e0041c0c000d000c43c00e109028000a8580f1400c00f0341d909008804d071aa2000e02c440381e845015190b58024080c850404094a000ca6000002d000010300c160b8440341c80c0c1201000701e40d03061500e4411a50380850231500940c5071002c405020410f072005407694a0321041e280c1c06404601450225000400381d405070800091040e40300c03c04900381c1401e400303101c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 400103750 1250 400102500 400102519
    0xa092907060207120e0319020612090604030f110d030f15081032100807030807060e150402061b0106090603050d080702100f0e0f0706081503150406020f0c0705 70
    0x480965003c0c07841781402e901508411804a0007981100040c0c12240c40203048030305240000985c3c00101804880e04402c0c0e07406003003800309140d00903014070340340030746480c0680b0032101084610341c58281c0d00d1010070900d5100d2a410000b550a9004000e40c0054940446580c035614542e05580d40010311000d40d200385006070b4000030100c041c0280b42e10360324440250040039141c1000c0c4000d100f005003d0b112290301d0200120f02e001003880030340300a46c000c003001510368440b400c1003000c0301c1c8084000211a4000500c845076209200440d0794002d40480d14140c0b11454040c0c0c045050422282d4030006501c1e080003c5902c200c150300c81415a40900c0440d14221040082600c040ca01611110050380c001c40500b6040110394101d19906115640b001c104d015119800c54901040c0d40f61641030b079004a5001d0000300d0384a43c20070744c00300566105940100e40580480e4a0307242c0d40401c0c0f000c0c102c858000030184081c40c0c0454400c214034102d80c40d5601c00a141090316a00d80d030007803d2107800d508 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 400105000 1250 400103750 400103783
    0xe011a0a06020601051905100509010e060306030c090c2203050106060201020705060a020c07090903030c5a17010506031012020a0801020a020f120a092907060207 71
    0x14900c010395255400400712a4284810002e05104108019600c455030b0000410701e031b01e07107800c1c200d030129a68a80c142c4800c042000581108040420300303000c0c000a104028003030741c0018815009010035100ea03100358507010004402482240b00b0300c520003900501840c90070343c180d010001228001d000803ca0a40c803264103c0c04e034822254050606c0e1301c8800450710303000180d4020b080b100144012141c19aa03100c0c0c4401c2541c07800541034004c03c1d0b5652400c1049034105100b50b001c2d140d440d8003207500c02001081e01414440b43c200c10609103040050240c0c07040d0040c2e800c02d107440d0502c00161010307148504018811001c010035452130b808400c1c000909810400141c0f0700031110032180510351402c00d07008008590040c070080c1d074401030038076002800f50b000303200901844190f9800f6207229840094407a24000104640d280d001d0130801030440b550790b02060310070a654540f040b0356540300500860303018252080c1d0f0306500c448800140030f42081456030040c09031501ca80360305a11039001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 400106250 1250 400105000 400105009
    0x1209031703090c120c04180209090c03120a0c020d0c03051e070302130b090c03332115011a0702100302030a0f020c030c0106120c05010c150e011a 64
    0x94900071441d83c0402c0c00d407111840c0100315010500c8085003100c1601010030005000d03108070512900c2d21851000e092400e604208400c0c9900400080052084000e18404650754440401c030b21302d101039010400c01c480701d20030908004d0440c1c00519420010045043c00c00340400944812100f61003840295005212600c0007000450803102c00341100d14a19002d000310f00c045a071034056266a103075240c04603a1703125400d80340204c034200700168607454090034603c09a0f015a40724144400c0040f0028081c1881c502ca4100c0d04034292108d00b1381c00303000031039031002004065100340d0303d004e07102c150f000d400b0403030400034100c440c081c10240f0f0004c090080000c0c0c5204d0310341c0103500b004542c5100c03840b044c0a600195040844803600040d5480c4148030b40080345c0242c207a801e400d800c000349001d4450424003440c809011520315060384034a0b50b0780d500745803000798460b20b4180250500c0c110140328011b03a40d0006044240018403200b1650001240204a00d5908103041c48c030300e55010446003031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 400107500 1250 400106250 400106257
    0x9060c0f020712080d09060f09050106080c0310020d06030c091b0305071211040906080c0307080d0507240509030a0f091211060f0f0406030b0103020319090f12090317 73
    0x881541c40f10302ca20343c5803c4500d030b101a5000401d540c869150030b000030502d20802504a43c55400060707002c480d45001c03802d6841d50f0384517120310713400090500d103117950101d8002d100c1a0403210050780c9140e0018600d002c0c241a50019118600b900300c00141c0c011203030058403c480f0240f920400309004002c00380d044131016204840080c019a401c801c0240c4203601c80d0071150b8004405070b0070565110542816650184c200c4403003030b080032030b4540c1c003070500b0000c56001c1c140c28005401c24045104008010307008001c03020b00800d040180d50900c0c91316480d00d40007440d01d10706041c410741c81d0400380240e9a40c4100b0a03100000c2e02d8500003402d01d07226034207440c141c840a00908142003a203444004a110a03621a10b030320200c1042902c1c9541d038420000e0170444800c42480f074940d0310b0701d04048d04a4404507192410b02d030040003040381108505021011003c95035000060386901420a041460902d40c80202a588448110b0410344d8120604504680c85041c00743c003491580761084100c4d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 400108750 1250 400107500 400107509
    0x309050409030503010627140909030c2122051306060e0f18100f0902090117070c0c09022703030307140c0a0c050f0612011e0909060c0f0207 62
    0x8006000500515114508018051152a0441c50700f0025000c5100060314964232080c400c6800d2a12041d41d07040c00e1002c20351000c02000a0360038480c840f98610b4441d01800c081d2481e40145800f400400030b1480f090750041c4410580c03520881c8c3c40c039070404031110418003030305128241c00000c13000d07a62054000c00058401603a941c0e800600c0200504c2210700c698501d89038443e406401614100202c160b11520548040c2101280c452400f8188a40851240c00855426004215003000c99802520500c503c90810171b41104c65601c100c0e0444002d04120001403005090300760010340040c00341c01400c0f030090011240809010c004204580e040624103c246d05030b0810310000742d0443c016200c1e400c1c8a010815464034042d0003d10046c1002181300c801c03600700c01c0350300f024401c50a20018207550090160384592034500840d52840c22200144900e03482146001e164a006c0c2009150301070007070911078000c1c0840a09403400e10094500115018009003030f00303c00500701c41c070001d24142242d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 400110000 1250 400108750 400108757
    0x3031704121101090b04050d08100e0c0307030b0303131401020d0c12030b10020f0c090c1209120f03090607081603090302031603031a0907020c0919020c03030103030905040903 77
    0x1d0410090603a42120744a1114503295a10180340c004584007920441c4110f11a00c05080780701e000d0380c8094074070070010306404241a4540b000388582003190701d150380c10410007411240c880d615a002240a001c021103c0358150201140342903034000c8924565003503810742e1365180c1050101400480c0d49500601d0b03058000303034012448002090b861a04203020071002e25000c2100c1141e08013180840207882c0c2c82c0701c010b9201c8448036a402c40148029500010201e0b90340c040d50600c40c01940c0207004050001694401100109103011000c2002101d4018549a06506c0c0c0da011428185190021a54490240104000203280d944aa5039042c4541030b1055104a10000007070110300500c42c00d00200d080d0f220400520607410070401040350030301c1c841d680c01f060040ad000b040740c3c3c02540b0000c0d01c6000d1a01c0308103100415401150844038040150b41024855940c040314a8201e04020f03040d0410510000b0405032104010000794180ea010341c480504c85a580e5042c0022180c46403c0640003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 400111250 1250 400110000 400110023
    0x227160329060c0604080d0608010c08041b08060705130b0c07270203010f080f0d120c0e0909070608070207030201020a151e1a0102010612020d0f051603031704 70
    0x50403429052a20300301c0340a86003608103524007600b0707440d1550540301640c4000c004101e440c41c6c2901da000700005040740000034403103041c00c00400740000308040c3c00101545121100d00422414a0740514020480441101d800303007484000542950b0100001d5220700f107160502142d00c01d00d100403507000740d0754030004011461408026000c0c000380e4112100501000c40c0310407003414290b00156020784505c400d414107252600742160301e400b17284140a060703030b04202c02011842c1d0700144451059042c500703000c03480381c2c080072045440300e0380100050344c000d40c0c035070500c4001040001c0c002c00352580c2d1340b80d8840303a466041059a9444462100a0040c0d12a105200001d612205010b8504950900102c1c1c1c2c007000d03610140021017011116018199280c41c0e01c038200c10b6401141a40300e9081c0020080b4504110002990300ac5801c4003a000706031600611007004690302041d06210340102c140c8000841140b06200030840c64481580042d03100400c50704501c00f540520780c001c56000540340310 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 400112500 1250 400111250 400111301
    0x50114040b1207091e060902090109140a15030f09060606020f06040f17040503191e08030103021512281109012a0602070c0e010501050a05030402271603 67
    0x303061450311740580300301c120b01116030030b14013801401c02902c1845000351f160340208000520300320541e8410701c2d0055a1181c400c0c2d682e240c580c4200705480b241442c04a011500041c1038000d04403040700341d11350742d1506081c0e10a010140d4007142c10380310954261820080a509501c0e035450017610702414000b040720b5140b001075140c010368100c490001d12000c0c1001d9941340002d0514400c010143c150b480b0201c0003100f00401d000c1007500c0c1c02c100101c00b08504940391a10038181c0014000240075602004258910800f0341c0705842e2a05030f0004560306602e05005038002055424030710749184068400054a82c944602501c82c408040140b03a504203100d80d8011600010340c804070000f0307107007030f0036101c90b82c100c240b03544d0700c01213000b200c01517035900035803520b8110300c0829481107181c0c0307080e01c0060120741c3c0d200c005c8507d10007076850880d03202d03200c2c0c2c00003c00e40c1c0300954018900c0040880c80380d9542c5e4060040b80e20602c1c800c1b80d1400740004120042d4181d48000c55004001c0308000250b11 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 400113750 1250 400112500 400112519
    0x5150306180f1501030621050c01030501080a03080c070206192a02091009060609080c0a0803070b04210e0111010c140a090e0f240d081b01050114040b1207 68
    0x818148145170103d8440d40e41c0401302413456010389144100c00c00e010f0031070148041040301241d204403c2c60200107541c9400e00d459280c0d4a201d6000301040100c6011446c1129040300f0b0310780154000306015500c040038107800341082c00074640030020410610034184d010000c4100b0358246038100855002e07030404c079401c1100d103410091400c881c2e80180040443c103441d251280f1406441c0c1d9495070700c10b00d0705104035a440c00300200b0002d072069002580900401034048180e17a40c0356442134620b8464bc41d2032034203207825600c018601d0303000c2e017841600b110f002754070000b1525040c200303807102c01800c0100d0000500341c81d4400d0610007c1210700f0101402a0079040043c52810154501384007026150608082080416511503408402c00c405000f41c92400140b558103203049540c50f030780c00b0140035020480001c0d400c40054a410000b007070400310036031000b81907030f0f4010500008100039a11115060640616052044c0c00f80e40f90120010003428010548080b114202009007401441e000450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 400115000 1250 400113750 400113781
    0xc090506010512070e150705070e0612010e01060905370b0d06051f080c0d061404060c03110405180403170903091003141b0405150306180f 61
    0x110304002c420003641c20640104140e03580905042e54071041c1a200e401c04100448601e998041c00b0503604001c61400161300051220868814060002840d40e4032400195000e00c185411007455092003140130f0b4480065012405407010860204190784031060202400901c0d04015001c9180d0305043d6183d00001c6800a00701c440c00520104044007031401041010740c51200c1281c00b280c588081c482c04038200d0f4a040e10034658800c841807070900c1c1c1903050f903944107102c0318203002e86a01a01c8400344003041c2c20000341d030318010300c000144d414030f49000c200074003a840140000a141851503804000c44608480440b000180b406000400104c16803003d0100a0011814000c46001b90851500d07100c2c2410300c0303401500040e585640c0c5c00310a0005559030103020104241c45e00f88040d22b0754150740b16507904618460007888010002c00c500007918840c40d0056039121040b4007c205191f05a00006c41c17081000b40d031400a040d03203105046405c218181c50f580b218201c40c2c0700064600c0714035141c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 400116250 1250 400115000 400115011
    0x3061202010e0424030c0e010b090907030506032a0a0b1801032c030d0c1b08090118090b030f01060e0606070609060207300e040f021c020705060708040c0905 69
    0x5140c2130b0051407036111030070391207541700b02c0f0303880400c0700d080003030a04d403000309401841c6d0395003518504041d03100040c0880c00300800741000e06a45902081d50750301c0401c548203100e00c65030100600c80b6003080034000400300f14400a449030052040c04201c0c0c58101e000d450300488041e201040c144903500054029181e24145a5102d42402d030480d5032000c18401e22014201c02c1d00e0146a44460f06100e00c01a5213000c940b02060000321010b407039101200c0c4400b0841c550304900c54903160904070004079602c50008243c07221014403410040381040055001c810203050881c1243c50343c0166540203130a07282213100e810400442000000d6642c188170b402003411510540d40040c0038151030b5111012600301901c00d070f031003a0201c85d071518400100c036600a55108200c07205036428807500001040c1030700303102e032a500964651518412907079164060310340f403054900008200c6207008000d0402504422011f840c548111000305960b00d000350394a0380601e410141114420303082a520f800580305c040d00303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 400117500 1250 400116250 400116281
    0x40b012d05070f1101080a0b03060112061b0207080c1905040c12110403020109170c040b040b040e0f010c09080a11061603080f0a02090105030f0a0e030a0f03061202010e04 75
    0x440c100080b81691501182c5104d1208070121180c0080010403444004000500240c80c00005c1c008c01da40020700141142e80140003412003207a94648240a040500240425010096501c10341c15802243d150b0075075103641c080350320842600e42040b84981f81d29031100001c044403001440b2506040d0000100d03400710f414003201036000c94020000319a034424021070044400b003001d20441d83d102402c8070080002000c00b10100102100ea00c0d03d904183d54003510442d543ca5854005840f01e402809522000070000c01005100e850061344130084909002040d52800205034206805a02d9440c00c0d01c00e00c00040c115240ca594580d1a0b031614000d480d50b1009090220060342141c038a4051000e910980c0d0301100b5041801e95048072101c040c1140c02a03600500184c5013a0f6403000903a5440500829101041d480b51620710340180300e004014101404005130340c0d0005500030340000400a05035504021a1387c0d211001203510140c00d400030300080021301003004600e041d40180041005580 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 400118750 1250 400117500 400117507
    0x9050405091207060c0f0f120f180305090f0603130f031404090b12011a01050304060b0a081606032a140d06030314040b03060d141209040b012d05 64
    0x4088441c030f400050b01264601c0d00c404503031310204d60010806c0c00009141c1421220140000c501628a0a03100340f062003c43c0e8541c8c856000b40750640010112102c04505c0d00c0c072103a40c0c0e043c014040e40c0902c803410b000b2000145440c8050804c40101c0e03103da40f09000c0c4042200d12590791511000b6107080075010081e651894905841d8044018001031580f0b490000b940c1c0790160a1085452200003c0406a40350041c40348200c3c10351035124420610920f802c554035665460014003c02e1004050b82d0825010b00010031b00315400160600a401a4008556916035414040303099903844450305449502c05041d25684c241d14107a441040105420441601002850b50385074540080c0d4040c40219140d4808005060300801802517400d0a1903001e8a464240300d1003035568400980703081d003c0d2044000c110700303201002040301c502c3c0010317800791014078601801d22201038101100051045240c4605612507601500f803080e05005020f08000c18144100100301055a100e40101e00340007040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 400120000 1250 400118750 400118773
    0x313060203240a030c06030b03030d0507091d090a150902181008210a0203040807030c14030f15130c08030705060c0a0c02090a02040e090105060102060603030702010905040509 77
    0x6001a40c8507048004001c8454030021110030410782c80e807088107005040c1d00a0500c0803a119062600a854560a01140c0318181c000032034594400c48200521461820082c0110164460a200102c511821f40e906600b1240401c48401c00026920001513510a0200c0710010b6502d842c000b00d4207521320400905525240c011409004e8180700c10585900ba40c020007140c16111504003020b4110180140a080d50031800301c1c2d20002484000b4000d41c0021520342c45140c42081100c000c1d20081c01a11440c0340d907450105680c0030b9070300542003451098010a680c078140015031710038622241c0300a000d22203000040b2003020602821140320b80852800c0707000898000040e120003042c21070011503460300c0307a080079410000f003d01010350721003041008030850344d8410380d0641059011903404440f40c445480e00b500a00c074030f40c003014030300d4a21001c0050b001c0065104510987c0e003038084d945c10b0341c2c50030101600c9204456009010503901702c824405030400c0e500c07013540462100110346804582d07 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 400121250 1250 400120000 400120013
    0xc090c0c01091a07170c03060303040f12060b04050603100e010f020f0c0705010f020a12050d0504051b09191d01110c0c0306070804030813081308010612080406050313 73
    0x90020a49040311103d02c805085000b0a0203d98000d0031450b044520301800c86140e4082c10300609010010070020000c2012940e0600486004140300c032802e54141e03a071041103084201d400c2c002070b0b800300d1401c228030f603d0382001c2c02440c0c0303d500000c010302412050746203040000d080c4401041845d6580e80c04c0652088001d00c002d000300500b9492003615603e10022031850000540c03c01d078104000070035480490750b000100e1000d5203030b0044602c080c90b040003008031910b02542a00c0312180b41000240030074007001040861090a0359138503001a008102c05018120703c050780c2024010006039002401c9440e6075114042d04030042310b10b5826069172070300d65400c0d21110490b281c560400041caa419054007005100c9050000382c0180203d450700301c1e4090482d041c01400981400040e90005560f51a480c1d010081254000340c0746854a00c4050b1512400c40c4500550019610340800800e0b804007807000039640d1540440075030b2500742065403c6030142c1025007a444446816450f4000082e003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 400122500 1250 400121250 400121261
    0x7150318061e050109090305030402100201150303051b010624050c060f010e010f05030d081e040516080307050309100c1a15040506331207140c0c090c0c01 68
    0xc05001e800c00060b0191400300b00c6070182d001c684e10070315181610b000240c001040e41c1c0d11540407100e0915050f00d25500b039000d0f1034241c6403140b80c03408801c000f2007007681080107409904507400d5003600103440060882d088a4240c0659451a03540038050100044484222490005030385000742c10300000c4501c1c00c1c80c149090b2000c3d140904150014400b24148031040c070b0043c82081c0f10003007001c0c40c2c5004070b9140c02c080d2104204120010000400401104078184400b0380106664003451800f424540c1e01d4000c9080b030003070241004000013400d40c074000261041541c010015500c6c2090b031508106611001165950600518402040c041005843e01c40c04e203440c0041d090307040380761003555241060101c11038180701300d2400c014084241c0340d492803a0707150000c544810b00c0c556500090755416061a43c12200e918100180c030f083c8603d883c1060902640c06612a48541a035907240b28003140940031800100740d00600e5415180c0c60030f51500368100c040014070910b00344042e0105400d41e003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 400123750 1250 400122500 400122521
    0x938390f0a11010f080705130509160801140f1e0a0305010c09061d09042303070521030f060f040906090b07080108070302041a090403090e07020715031806 68
    0x10010074040e814400158078079550003900740b070314480c1d09510803405480b1201c05060307001001404204842044d402d000241d001c3c00005060301c0c51440e00d590700303400000d205403c001c005a03072a400040d200c4200c68140c81e03a10b1008000b20304800b00322044c07210307202c6003030400408548401500384442e11b802c0c804a000d1805a800840c81003040580903014000c96802a82001a4402c6081c540d2020304420181300104540c07185054645003083d100e115403505030114440760825000100c00340000042130424803d006844940070560700036041c10380401244846a0020000038281180020f1866800800141088034100b0b01c0c1c070101e001c81c0c10a20084910642d103507010014080203116560b401170507032030b03c0b02156040910440d2591001e1100074020782c0c80f010741c0080c0d92039040000a848070302070301116151803d400c004101d1001c911405003441c0130500410718080c80460b461041c1d036030160036070005c6142801c08a00402d115070b110b603094089a0408000074425000b20031049 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 400125000 1250 400123750 400123753
    0xf0f0c0906090b0316031a1005040503101103040b0907031a0106080a05010b19020c041506081303090302010806010509130c09060e0a12030938390f 65
    0xe0704181015060326400d420040d074071042031081107121105100e420000c0302d40340c5004201c5480180300c0b144102c003002c50543d03008c1d480d881c09681850748803000c4c10880308210100c0310b041d6856881c050440c1d08030850860a414104005030110702100c40042d0040260750840b54181c0c0c2c0c07a20740c1c01104203e034030603880c0400814010094150310a841940000340d001040119501d062002c900600c51404040b400e1a24500c0304001140207100500743c50700081c006001a21b030318100c1d405111802c9c0562000329006002190180d101c9240d904030b0941e15440340001241140c0040d5540c2e2002040141008020032148005884070703449011280003507240450039510b5040c014080c0ca000750040c608000840400882c2580c80f005000d003201c1c4508c0030a40a2401410304031040360301900000440380402110443c1e00c160842c50800c1c0b00100c202040a0f40c44440c0d0340c109a205184003250f182c2c0440300c02e48031344040043e035884400c0122684907004000c448440703003481203500c9618002e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 400126250 1250 400125000 400125017
    0xc1308060405011a090603060414011d070602010e0d0e090606280e100903080c01020f0f180904020609040c1b0b090d02010c02150406090204020f13080d09090f0f0c 72
    0x241180b001e040344c1164011140c0c0c0746140740140c04240d40e523000030070107880e208056005103011038082d4419945000d44114204001040da0354007a0759001c82c0c031503d0010b620300640c402d0706030004141204401581d94070300b070a803040542008900c0c0b801170007035544203004103d142007103d01c04c024510020b440c140c03510590140698060001c10b04290300901821240106018036a4020004025283c1c040c0d10ba9441d840c0039252a40240203030200b42c00019000a14000b14004541c042c0c4448070f42c03618040303101048142486120301083c3c400a401c907500f80700c0e844661401d504828100780591620030013546c0021460207041c0103e1005403080b003007081c10700281240078030404101440c503000074002c003040faa00c02565100d44041c0010102d86400110702003081b650070981d4010b4000700305640b40c8000495201035a401400205030642d011a00012214004a5000704442c460b440d1102441d01e08050345012380380e5504180070f80c580d51800c0490301c01013480380a98100907a80d40290 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 400127500 1250 400126250 400126271
    0xc150715061e0b030603150411030a1a01060518060c10230108062a0d020301060e03060711060703091109010602070302131b0c060e070612061a030c130806040501 71
    0x20b4804158000c012084820030821090703450004e87d100a80c03503510780c0107030b455491382000040c203440d100249900d801f0b810728020a120200c0c2000106518841141084d6607940c0fa00717807501d208503005440d03414414603e034051883c01350041d2551600b8038040c0c8924560200143c401c8465403a505500d015121035150294a1003820480c00740035510014800350400000002070b086902d20401070818144c120307080303c9448101074419152038400203540300d50f101c84002d4105c5203144501404ae00c94940012542c0707108050349204503484a0140810783c807412411809807020351000d0703c0c10035480d19200d00302e03212020b0050007030105e540a001460f055204101d00c0050348900b804680c1d0034506212640e80391044824503481260038a010285c0c910b00d00341e4080c200c1600d0150700c6000324500040d802c1c3d040581d594525401f228100545a01c90f00c810343d00300d031080c000303180c04103003070001424030814240204881d804400340108055a01d980840c40e007801102c0413146a510f0390001d21 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 400128750 1250 400127500 400127549
    0x10f0b0a201f0203040b130804170309040c050a080f092a09070921021c1101080106090609120201021c121109030a020f040216030512090c15071506 65
    0x65480b1152500390700c2c50400d070722a811803107405800300c1e44000c2400114010080c0d41e0040310028261001c500200e80c000608840e140e0304000c0f00c55000320b080500600180e0310420840d80d002d4143d468803030b02e68441410f01f6100e0b000041134100103224200051748c1007403810354940110b80340034100320040418030003071046240b0301420440611440d0f00051001c0c1000700c0e600003481d0f19554406004401038000950340301c40080c0502c070f003045072029074003c0c440c0c41c0140f04180701080e02c4081c00340c0d036111011a141122481035900051140f141400501008003485e1000c42c01403045901550a00c0300b004161043c0014003070215082607002c001c410118043c2c2d090010400610a08284190001c252600c0019400038400d4014070031010550b6240c1d07041c3c0b07a11804400c180032814010b442d0151442d4005c48000c010301d03040e00b000031150400007a9220304204040d24114207001024846140354014407811110690300030007103d0581c880d40300340c800518003c010400e6401c2c8454981 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 400130000 1250 400128750 400128793
    0xa0e15131401020105010303270905010306050402040b01050307050a0c080706050f100b16021011031902100504020f1203070501020f0726180607050303040b160206010f0b0a20 77
    0x280c156410400100082074000b24006000da1b000f524204007010489c0030300108114a8108580a81c44d1400210900c1140d0b8003140c032a91080c1c03020032999411400550722400201e40311400a0010000e14140034800c0d6910500c6500c07a01019040c00401e65807030041c0ca04c21604004211fa2020402031b00c01c1000520500802601400e00d15043d10010940c003280313032202c4064003035058400c202c049903100b5a0020741400d482d405503030b154085092424544119030060000511070440c0d4000c5500d554810280603e900414650110345441c080c000e040c441020401d02600003440117402041013030005103840c50503ea004d0b8ad4682280c580120548001c02001c01c000400d0b0307444a54007110f040031580c8a1018000802e00841d0560004a0a201e040c50041043c00007006100c1000031202c801c074042c1131042c0d1100f1100c9520003049903104024800e1019241d200300c020003100d0101801446ca0b84114500804540e10816015182909003940e42c2c440d5030051040300010315074420f84 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 400131250 1250 400130000 400130039
    0x1060b030f0423030d11070c03030f02010b0406051c020111060109090209090d120f0e0102040b040303090e07090302093c0705160206160c060503010e060d080a0e1513 73
    0x885070715883e006a500e0140709503002d0400d0762503800b071611203840e0060b64081d80e44004000b01107501d80c80d0003000350550703140b03000241d0700f800000315081c41c003800b40f10180d52000c2c1c4800d90110341080c802002ca10403803000c2e810b02c42c0c2500070012041b800d0060301c4c0a094211310224840c6410700c18000c07010002400c0c2e004603003143c00300044856120a50102003a000c1001054040045410a000b0119440b41800c0b0350b02c0002c00062081d0031601034011203009445500034195103804c012140c19084078030b40c00241c480300040c4010718100040301e80080c11a0310481c4002800011003046046c024a100c000b140c3d5141e01d020b110705454107255100c03c252501c3d6040600c2c0c14004100d401ca4014000c1c49103001050905910581416030340303043d0341040c00b11840d01d581d210040d006500c20300400d650001c0c01c40c0060303004d0030a088500412503004c0405854035407100b8044132607441007075985500008a031780d440340d00b50722140640075107128200303110341281c6408019503080d03450458 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 400132500 1250 400131250 400131293
    0x102070b07030507110112092117040f0f02060d020d0b040b030d05031f2702040302090c0706060512010b0405010815040807060b040f0c020105072f01060b030f04 71
    0x840041e6000c000d03611351541c0842e805c1c10212040c00140c42010040400c411003901e090b405005000d4007600040d0040c4240400c2101716080030021110394030300c0c00d0124208841e1101060000300501c00f001d6a0f14014800101c0c0c150030ba50018806602420121803803a0b004280f03072070306030444d20841b001200225001c1064074000c070301098880070301000e00c20a108021000800804d1201503014116075804104100780d51980940782e00c456038040484552488050b6072101c1030054400c88007600e800400060780d80c0d41e51100103000f80e00c11402214035503205e0320002020349904203010305214081e0004644950322505220444005a10283c00c07a840307003804d60401002c1c2e403c02c1c7c1c0c016411142a568a009505004001d000e0b04240315400034944000b40e00b00c501c2940c402c44000c0d40d9503000340300c0c1e034540c02d100300d079103c4001124a61844a2402000311218030007250480e4a581c540007040450b551540418990412600c42c1200b14990007000104425605d8044081c8115103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 400133750 1250 400132500 400132507
    0x1111605192d1a090f070b12070c020d051b061e090a0f0e0a0515010f050a1812020f0a14010c0c0e0406060905060409022b0b01030b060102070b 63
    0x4458a0a4002444460400d10102042c40341c140075210610b80c0016000690000244190200f41c06650703012120b40010380214201040c08483c0401d01d2401c550b840310219082076803d0881811881e005130103003013400f000c40356140068803950750300c0f03902d00e02800c090040c14510311041c40c000b8a0f00000315109090410264186090400c0300d1004103041e00f0301d023034407442240c01249441802d81c000340d054620741c010004032510803100e42441f45000c1c1006001a440350105c500984c021107542602059a02162003030070340c460b402501410031203117044220071425414000741c1d940036030441840200d2041100095090480094256020654140c0f48031803800c050a905080c41015081c100045c0000d4002030082ca10740704005066001d0b600c10260919247c0304005103034600c1240c5821342450006003203840c15104100d9104d80241c01005194607820031450802d440700c030b010944a00e0184000c0c0880c0034000e040380a98880c0c405180c580c241500064a8401c035a40320102140042 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 400135000 1250 400133750 400133753
    0x30d11010b0f06270603040b06011209020f0909011104090605030c060a0f0e031c020109030807020c0d02091b0f07050709090c23150d06240f020111160519 68
    0xf6821541c4040b4a0750f0840d0300c0041c3c1901d078006000100d1010369014034044103010900c14400c4d0013a0044800344ca4030300440b0914010282a1140a44007a5000b01c0d044464403141c03c1c00007069a21913003103400081c05030a800c018901c40e8001d600800c02a070307030b03521050250341070030020000c0548040f2420340c200b543c480c000614100d006624081082042c200ca10060389080003000c5000ca00403580038000081840028001c203440101074001401d180301060109001198200e500c0001038411071203c00d4070740901c03103e594058120144001c1000c1660724a4812402a0008001c074101240d80e4101e507007403c81c505100ba070881c0d4010b52400d0071a00010359074420240c200d4205050001807101502c00a9012525802030250850b4000b42480380c264220310003860300c49150101080059120440c4100c0b03030b40150390141000d5a416440d003038050241202a100060a00c00806d43d41208890f020150f0484020850440802101c0c07034101718046c0510513190300c02a403c0c1e02c2d800d809 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 400136250 1250 400135000 400135009
    0x4061509150905011a0a0c0b0103030f1206050603010b161a04020a080607020c040b040f05070504090c05030405030901180b04060c14010b1302090a1d2a0301060e0a0302030d11010b0f 80
    0x403074174503810b00c000613120888602982500d25666005072690303803150b96a0038090800c0c88110308840001d007007030280700100c3c1c01c45d1045206403440a0a03e42c1581e003401e20580e202d5000f009099100e210041d100c00000303400040840d0301045280e07082c141410180b040c84128540c40d0820f8105030091400c012800303500158900403100b08440102ea0300074102c0100340140000320402c0c4203642018100b05a80d40c2060081c8105c035800703141085041d950240c1101c5a00042d5002081c0307030801c0000089540c0708003d001c05142c0f80c4050b02500c2039491040d6081540303d40c0c4014040b81148040340705000c0c2c0054151a600c031410028001a135941d800260a9025010803640165010aa1034015112214640060110254107500d4480611000800e194080781d0a00c681144104030042e50f005518038a0340301e24159800c40c1c151390800905030345100400d01500e0b0018561100000980d82c200002c00054040c2c0c1c07245103208011010039403c2d240c04a01c95070094a209214030a035454 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 400137500 1250 400136250 400136279
    0x503040302121b011b020c03010204030c030b15030f0a0323030403031104050d030e030d020c3a1a100501120f1b050408150103020604030204050406150915090501 71
    0xb1100b56840d030380c0c2404140a000034602000c0710b40d4941c030b0202150f041d06a802d010605940c215000c03504002c04640405081c1e01c9540401894820026000c10001d00e402c900c00740c1280811014001821844000c00d00d41080d22469003465800f000002007415040b404584030070481c1e050401c2880e1000b09514410b1101030f0000302056030b135500c1d00140761038a609a4020344001040c04007102d00c6428000c10003052054407920a001d06c0c512114103500001c1c00441e901d8020304403001e03412001c903c420324151501d4501e4804444405002c1014001c507422403d801d100705c03018400c031b0780c603020340d140201001001020420340095090010703a81100f0508080d104005001c2140c0c001c3c40340709800303002e104503c800c00c941460403240c1c005410038040e10035502000100c8061000307541030200d04c94401c4c40040d4019a08200a10140c02e0907000700b540180601000700e40098001000d0780c8517445648000d15207903541444110080e180800d41c00141150f07001440954141044031a280302e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 400138750 1250 400137500 400137523
    0x609060f0a050a17010e0309031c0c0b0a05150411030613180302241006050a0c02120105070306060201092013050106050301090c0201150302130e010204031a06010503040302 76
    0x300318484004041d50740007400700c003800001d00042c0da030380d503100c0307298a82c0c8948280301100d95080003048101c004002041d5044418014020b26511101399110b84c0d4030107002c0c14800402412001c000007040c01c21000501810344440005114a07200d00290958420061103d21503030a10700f414111303280100640c0d410120031600d50f2802210b143d41d100080080d4031402e526406481e0842c03003030503004522003072044034001211100399000c07214040d241f03404984c01c3c40b000032008030034045c8078414401784c0b407508407908013141011220740020390700c00c403181409465a9101c5080191080d810b018845c01010180024080e00869995101c0c8164600c00c0604a44841c801802e0a40e6500050344c6000071301d111042115507112140244245d109000d8420340741d040080507800c0c248144950009030181e0529441803504550821a01781030515402c4800c546503484455106402c0c80140b0044d4805d1900550907045501c000903900e2005000c40c0c10703c10f0600401000c29004a035600a85 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 400140000 1250 400138750 400138759
    0x70806130b010c2a08060406140f04030507110306090705030106150918060b0a030b03120f03042003030c0309030706030615030c051204030f1101021c090606080f060103140105060906 80
    0x104c20489812004801c403122486903032007204d40000c0c5090001c035105002e00d0103010103000d01e8112202d80083e140302640c0980704c00c902c1600040201c0d04c954054110b00b40b103885410741225980e80001e1804500b911001000d0f040a40b041101d86001d100e101c00a01c0c4c0300049210540840001030300107040d0307100306081041421902c034624149644880080c01406564a81391144290014000d14201d8140c501030f01c10241c07103103541300740079042d0f0300c000211400052440d5034554a44102104000078103021004400c001c01e019602840541218003035030340290303202d0300058101441c1c0f0165510030002e01d40b6080b000c0c004540504000d540d14841e130704011481d260b801c0c000f1034280c850301241e0a1400c00305000d0000300340d44a4035000080c0040d640e400700c50006090514200c3c42100300810000700007201c403c0c81510180c108500d0326000b8800010341a0b038865a0740c2c20100c4551085a264010f48014003c10040312100c101806148000704401e18205010882403031010f400a80304 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 400141250 1250 400140000 400140023
    0xf0507030309080c030f120903031513140a09052a010c0c0302040f060302210601171606020706080702010603110f0402070f060204050102121603081905070806130b010c 74
    0x244a43c000803141802c010200301c80e568000400c240030290425070440e01c0140b44000401e82c42e070400070549000e6040c111110310303420304040c02c000c01c0c0000c4035072010500742c594120001c070600070b100aa115052000c8046100019490709605014050ba041d664540c0702103001c02c0740902c10034040340ea400d000e00b0300b00544000c03410701c1486640d040c0c1c0001d500c01c1c102404d45003070382295080070b0200ca00c280c42c1070f00c0798541e010b01001009000381d1400310039403041d4010000307186480705440d150041401610710441e0900c8030303c1030301045038001c2c1c400359114a10420200da48004980e0384045603100800156080d40c0c0c0c0e200341c0c840318000032071140e0f410340454174199a0726411101e0081d404201c078600301c000c91902c40701940281c82080d001d4040d11000c8403e10303d24408441c0c51614a2001080080b5030303035019140c001c80506000c0340f00500d094414194002d91180d80d000e01001c1d21060118649034041049460401e81168801d9003030040d01c0c00541d800c15020780450f54000f070030684 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 400142500 1250 400141250 400141253
    0xe030a020115033504030807030801060318260c0303040b070207081f0e100905070501110c060f090d0302010608121227031c0f020705070b0a030b09040b0708070f0507030309 76
    0x4c0b00c0030840064296104005400400c002981c401000c49610a031074010540c2e0f42e0b0a000d40841c0d103050420503400400035440d500140d0945440d08140e00202071a1420310042410f00000da00101100c0321141d00000512052000b14112203910012500c01812a5424001d60b1a151003280c03100807000c440d02003884000c440b4680003007002403c0380044400030044605204007074585000151003d004100002c1040d51051b1030a294413050034009105c9000e0010520170a03a00405600c0c100810a1042c2e802030355480c112150b25a02a5001003065400c020060342040100c030800d880149040000464070694010001c0d07006481103034070a480c441020f040d541810031202855650b0100003944024044000c201034400a0a17007402c0103101c40300d0a00780c00b241700340d00c40684641d200c0c2000300035000159000f00401c0105241c0071900031850400300d00780c2041580c0031202d280c80d442c10440c4451340000080d604c400e0074034101031f05981e9800050841d10031402d01404050321030a0850 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 400143750 1250 400142500 400142573
    0x20d03033908010512030f0f040504051905010b0703120b0a0902030c120c040308034302010b01020106050109120c15030b100206070905041a03010e030a02011503 71
    0x84950705803a418011a006000d0700c4800710070340d07511000402d60920001c14a41041040e80450385101c1000318504101409001030640058280c21601a402c20021072103844038020280541c210150714212060603982d000241d60050300400060034052101401080d40000584080e401d40a00056003400c0c0320b01003107100d0704c160449002d03540000240071802024000403c0800b0703c510601103991103001d4440080e01c524807000e4146042807000c01d04080c410300000c0781d080303509020404200c60000540021200181400801130f451b4264812040c0c0c083c080c60200280034030080141606040019059160a025003ca45030b1a41810010003003950340300405001300d1743c0f4406001244050081c041c1640e0381d0481d01a001d00b1403010b1400d4000580300e40904030f80d0311082c001c1070800040c80001e200008140c00d41c10107004052102d51028030130b01c082e000000c805544d43c1c01003107402a095400c05003100c030304d00c01b04810410104100400800001540034006084203070100c1071103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 400145000 1250 400143750 400143791
    0xb160b060112150f0b040b0a0e0111010c180e04020306010323010504110109050a0605041203140c010501050a0f140f030307051b010f03063c0605030609010b07020d0303 74
    0xc0801514010043d0380d501084020002200c0701403030105810b645540d41d0980324011442210500801400203e11703035409108282e42c00101854005070340d01a0325655429240c0f0700402c100422224000311411082c400034450140101d01014803280c00c05d176010070769460381440f01030255a0110b5000328441c041045115911400300024840b50500c2c0c00d0850100c12608201c41c0411401d4800040c2da0425540304800c940b1152500e03414503113400c05502141240794021400c109a40e44801e4403884014090803070b000b0040000503175581400300707011000d18550050070306075072078101c10003160303480b01005c282c6010261481501074034070320042072441c007403410010b12074002c15400c04c401c01e606099403e003080c403d03a02c2c0c032039603020315500303a04848250003081c3e0550035032498600450304800c21400b2003010742c031030040c1c20011858103050b1558150020300000e03100009000c40b505d441c55085005d0860440e4207071411180f0b42c001401050016001000c1c07540396107103401c41c510140181e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 400146250 1250 400145000 400145027
    0x16170427020423040e01050906070807122c07140103090c030c12060b0d0309050d0f05030c0318040e03071707060606030b0907210905010209060403050114010b160b0601 74
    0x3d000040f00c03500041201d140c0000390303805280360401e44d4602c0740050141c2d0380100f480c0d0f0054449900d85000445140c0b000810b41000d015402e1140c0320b40c00f003a0300ca560180005207141d8181506059141d50408111040c0085030341d00c0144180011004040240d590103c00d00300007071011850714001042090652020f461040b14550004003050b0008030f500c4058410082044400306c10010000d025000c07080150018545142c144800e080101c41921094019411340350720702041d40e610740c03440e4012000000690800f08d2064910070805c00304022040040340c050006065103000941d50b4000d0b0700e405481054182b80f401c02c80c80c14071703080301c5a043d008a41071100035143d880103800740c821001401e004a03d20400190164454010850082c01000315070174464420281840503081140303068520355402c0003010301642d200f60050004502c5170b4004903640e0704040e8141040c1d141648040c0ea10329007003005d46d90300e1311040100140c43d0350002c01e0303100948420004903020b01c5080c12 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 400147500 1250 400146250 400146269
    0x6010801090f0f020f09090a021804020a021501231e010f05040e010902030f2d071106011d01060207121509061a1005090d110409020303161704270204 66
    0x541c0490050880d004060720041030307c2c00340c09915656614000c9101da81404003905509503c260746524083c0c0042416001501c1241c0094a81414043c4030180c203910084a40f09100c0b80001c40c041080f07a43c0704d25030005c540f00040034401c05074041004200d205242d04200e81d0300c00b000b0f8041d0040003610090800e4200c003858540c0c59036070f600300945c000d41702070345040c251400041c4a19414030300368a4480030200800cc4808068010b003903140d030054000000c2c4000314210040750741c41041401c1c028800104981d54401030300603c43c2100b034040e0000300c02c54101e003109101c08010b62611013040d56000740b1049076800780100740b50040107400310091440f420521040b0b1051856a80442d90321f10449100d00c01802c441003d032010304c40d582c40b2503040301d9058034000108126a070402c002d210301500105080f855680024119401440f002c07120308035001c020402d00800e4a032017000c2560110b03066107403a041c0100001d82e1440c0c069a01c403036500322a11100c51206039019200207205a60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 400148750 1250 400147500 400147507
    0x7080303040c051e0d06050a02160c03060507020c0a0b0310150206061002030406090e061201110a1b230c040216021203030723090d03030507031406010801090f0f02 72
    0x160040a81090348607181c130448041c00860715a200310301481800b40c0005082d17007001407282eaa100c02a01c070060030069841d07800d0040203071058800d00d8100c0013603c15100758040714214506501103500180c8401e04552000301c0b02da046403114407800c01602c02e031003150b646950758144044000d41e003a80040d2610b00c0600e00c000201d90700003400c1c3c0c0c0605000c5600e50300394243e8000803a035900407841520005081d0a004000703110307107116900d4000c500640740c0341000d00c035010364a09540f0103601124841c40e00090300c0250980c0442c81070060b1080c02c150301c0c40080301e61141043c00000407060404002c0a412442034210700b00940c004501015200390b499000d15101000400c440d05c0d01a4010100801c00d040c0106010003120302c203213100c1d01c03821512804510303070489102042401109401c020031011034640d0b2a24446a80319200340c1e4041202e150841000301603035030312100161101190313400d0104607070f00581004e0540c0c03281c0900103006441c2038541405014240b82c40f020031440007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 400150000 1250 400148750 400148753
    0xf061c020d05010512011b0c0501020d061409090105040302030702010f0e0a0e061504150e01020f070f090c020604050a0b090c280605041404020f04091e0c181202030708030304 77
    0x2604098100c2d501140c1d002c1c0c0c4143d20301c1000d0301f42c603580010284203a90307640315003140ea401184000013090080c0001801c0030b905074110070031076074030703030044092820f10184040e094500000080da00103045002844241051742c0d020b9a240a115002414021100265150780344503880303119111400074100c100199507100d0b1648401401d40f1454019980c4c42080d5035881401c800f140c0441d2850708040014030740c440c60494a8900b241103050442c000d03000703108000001000303854054500c80b50401c1c40d65203496000710071039a01411040654000d9000c000201d01c003c6246488a50040c070149440c1d554801040e007444c40c0a440560303c0310040800e40c2c2e0200c0c0000002c07038038880b521544003101d500c40c401610607000b60301c01c81912071151b5000440030300703054001d000c400807004a4035041907220b00040d010b031025448a00c0d0481d000c510a51000402406030100080c1c3e241002c11403642e1800b184000010b060003403546180386448071104540b0300300540c4000707001c0182500e840342440d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 400151250 1250 400150000 400150027
    0x304030309020112050414060901020703020c0f210309010207140d1b17061e09032b0203040501020c01052d09100507050301170724020106030519020a12020f061c02 72
    0x20f1f084400074407c040000b907100700144221030340b81c2e8168004102203504101004034000ca4a012aa0840101512040b2000715021030502100c01d07007000d96162080c10303000902e0911141e2010b06882c1491400070003c0d00d81180c3d400c0380b260441d01d5810440425040d04442650fa503000301240805040f1050071f00902264450003042501503080c040c58001607040b03440c0900707454500954008010101960b0440c840d405140d20b1025200322054402c0c3c1381c3c00d0120380084405aa10365000101c2443c040000e2145560009404940110f12111940c66440e4501c00100e124020420300000c2000710008002402845600e40002d00140c0707440200207041d60403e20910004041822001003110700118030782042e102500110941c000c2000c468442a00882681d002555030f05d079404004241b0501c24604480381070031203803021042710b2060081041440d4000325252640d003903545c005955548c0c030440702c0c800450f442c94032400181c0826400000c145400042e01d4800078520726a600c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 400152500 1250 400151250 400151273
    0xc09090f1e020a0b09090c0a11070617180d030c02010b06180a08010c0c030e18040303060807050f030c04230112060501120b0106081504060f0f06021203040303090201120504 76
    0x42503030302d450740d15907641c131101050262401884d4400c03200800100354006040140143c14807a02d010882044282c44450a00b5102c0c0c0107540091003208c034902c591700003200c810341c210781001c42008000c050340440d980c44240000c0c03520109500c03184c1144c0294801d4200c540105001804d0f66583c20740c0a800445810244250074040c40c0c00440004400406119144ca0503155480c1d5080c000b98030354040310070103001c3c48140c3c2d00401c0260380380e40c0007400c4417065108a110f40c900058240c200007a0510301700342c41d0301842c03003026040c040300356944003c203041440d2001a60046490382d0703070021030034100307584501120328001240c3c000610152441100ca04030b5000d0f8030104500d988804100044126410380a4808a009001040900e129120541e8000028400d00e110030103c0400141520503a6000480d6818905030502800200c103c3d41c02c01044503000a109507401c81020341d01c40d0000410107400d0554407103640040da4018420300f824102c1084082000385002d2802491041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 400153750 1250 400152500 400152503
    0x2c0301141918030e0d020a080a0b15041505060c030c061006080601050301030321060519030605010806010302030607050919080109060c030b032a060c0601031106070c09090f1e 77
    0x40c10b1a144400c95041d40c0e001840003500742d55244060101e030814082c0b64081c0080482c5c103e100b44000041440041c428038094a102e0542c030754040c01c103c05480303501c0303005c826207601c19440d2603811900540c90500450455500f621219140ca0a2440150641c080c0c2840203ca40c007411003000700176054454104281c2d400c580b0782d10440e444680044604e030200740170080209602c10055124920900090981109070540200704591954046114000404014107041448050500410907140201809440c00d44001d004943c5160000382d9903403400340104050200010b032409243d150792810441c00b032019158904a2955107159074001c0c040000709850302483c0100400d07035903100e07008401100c44018024a00204502c1000c1008990360020401e44808001c001011b0303202c0070064441100100003030502d5625604203002d00d240440740a9201c1d4004022010004d484020b05100f41c4441c0d19000840c00120318020310710140004014024445155242c0c07000d01201d80d10b03880c1503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 400155000 1250 400153750 400153801
    0x90f03020f06010f0e0112050f1608060f060303072a0f06080a0b060a1202070c120218090312180f010501050a0906050306060904081905030f072c030114 67
    0x10f07a6600300c0e8200401850040c01c4907045000010007243c0500544100b0103400f48055508403000030309003d10700101000e0300604203e40050400c034600080c0041c86c0e00202118400440b49000d40010b40c0fa40308200004000c541d60380c1e1181e645402034081c10107100e030801c0b0240c05e11a02c441e9203065403101d500c0b074480001c680c02c00082800c041405504003844001c2c040904101d00a4800e40d160103a8032074504001e5401d1004a02041e111443d100040c0400c80c031501911245006000418030700000520248100e02d05105a0b00000800ca4402144458100406482c2c9880040c052402c04200f182c2ca4810180440301c018019400039049900c2110511403581c0e4170401401954aa403040d43d904d9001b403000500241070030502c09500510031794080c0e141450450311882000c000400400c0050f4004c410400211010305450760000c0d1241440c00c1e4210401401c458141e00c800312144034840303414a04422501e094010a24040d041d100102151604540b0081d049107805a50201c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 400156250 1250 400155000 400155013
    0x30d050a060501030b0f06031f0b040e070206010e041e020603180f0f100b01020313030b040201080a0905030d110c0a03080603060c03010f090506010203070c141302040b040504090204090f03020f 85
    0x140d44c064801c4039a181000340815054030031103420400c4c103810007441d000403031003005000785140a500602c1c102801023907600340c1d1600e00309182010315080c004c01c00790070f5500c07060040c45046290b000b0981d11640c40404109007480c1c10a00a83c0c40201280094005c0c00110601180c5070115294401210849045071340000241c1203842d6181c01d41039090404d41c1004a148130641c40f5904001c24510040c012649004800013804c032800c14240e0050703420007904410b00c030856901050550304030404482c1841031400369102d0903164800c50f00348540c0207645040c65112440214156011540030070300359030280e05141030291051a0480ba03980c031a001c0d140c0020416004541a241a0354150300c00340c01d000d051580c0d9034010103014084c641544014029840040d404000b1480600f43c0c02d00070304550f0080c441440a00c0840e80c007603030042c0c3c1c010701042c0301d001115410749049500c1201d0102c1d4101d0b650001c00c000301259800a40b02041c10380610b818035030001a000001c61608044491 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 400157500 1250 400156250 400156259
    0x9040f020412020637020d030203040309050622090c090b0309190305120106050c100c080703090314030c04210b04030e01030f140702010c030e0a0b1305030d050a06 72
    0x8030300c0340d4040e03406036040d460b000101509010340900f105214404148002c04c0307650105502c8200c10a007003220204c1c1c90824a515284e0501c1030240074a6142025811800c1981d80500f5800c0036011b83d5002d401d000c81c00407201c004010300030b002e641b281040c00400c1d584070309440d40580324a4030780c200400c800c198002045804e0100310782c4a10303000d00290480e060860551001e100728042c0c15020484103110f03031107648444602c00d900a01054850540c1c070f0402c26459404c1071000a01c4401c1640750002131405140c11203682980040c0600d00091003150381d250a4031003c0707424603640300031700307000c001c200344148103a00600a2f9100c003407268981000601e48500a00c82c0840000c002400e0300c400304000038010781061004100504000c0b0385200c40c41c0000701165580740040b1a41d00e040030906c4843c0340c080c4241d903010b011515060040107001d0210700c2c0e89140c100e01c01850071600305c00141088072603201180d012680320041c2d9541e004183c2c400409000160359881045142500019 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 400158750 1250 400157500 400157531
    0x1815210f070b12060d140a03031d0d0806061b0606090c0f09131803030914010218061e0c010207021804050a0201030905071a0301030605010618380904 66
    0x70708a440141d03074a442c0801d4074000c0c0150b00d1015040941085035543c1340740028814240c02c1d00e00b8146180148071400441c200101034a03000d1404003500d410103450143d4480340400e2081d400e40f6941848030094407941d0100d0b96a219080c4480701864910580c0383e5450340103c1d0040c0100c5003200c3c82001a11982d200389040c0c03060003d403041d00882084000028140014050210b0b91400700010303101c02c0340d5a503a190000c0c2401c00310f0009595052041c108080b103109525440c014900840c1040320040700c1802d910034107003100388526000304a80020b44491080c02c0b403031050301c881032612903004030060380c040d41000304200d10541d500100c1e0700e0128010ba41d000e1085410100801c0c4404440c3c0064004000911094455001f8200b010032405050300d0404411035442d0710342962589581800700c100d0782c040e0042c804114146428804000d280003110083d00c440c106548500c4441590010301c000c3d8120702011001d500300000c85a0043d0f210103884031038420b50741403224a01506204 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 400160000 1250 400158750 400158763
    0x1e0c111507060c0207180e070b0306030c0103111303030906020705010509061210050a12051209010c0b0705070605010e01081c02101104050409060504030f020604021815210f 76
    0xd00c0c0060040c0003520110385142c0205010360003e006986281c1d86411454644000c1a180f510b05503440d00c41c45118180c040044000a101c00d590319421811301c40c00294039249070443d5181059198110201110407405c102d40600e01e020407180141a5a49405480451648103103402750062100000343c65008204440d05450020310755468184040ca074240316000c0900400ea400071050400305594584040c88405007c0056455124041500d05180303015580c012642d01000180800311190b40c0112010f02c5044c1c0c00604c034015a40c0d1000708039124018042c020b0801c0d41001c00014801c203200d8a072905035000f040a8a83c00ca4141140c210103d295510316001a800b012001801e9079260344455401101001240d00d044d5440c0006000e407086e010090340c4081c2d443c0203101c109500043e613004501c6560024201902d01900011105104001d84034944100c03040000c2800012b428040d40c00314008010710405140008080c50096510800300500e02c00c580b4031103030306600082d41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 400161250 1250 400160000 400160029
    0xd05040b04090203070c0f060e12040812030405120403120e1012050a0908030405010501050f1008130614070906080c0c0604021908031c060509070e010f1e0c11 70
    0x11030724103490100c0080c0290700c01018441006502d1500d80d00184407420101ca03003a00070680410740d980c01c1448682040c40d080000001e0110402003088240d030040781c91050440303402c441c3c1c3c1e02ca80d80d03403c00c9810a4042410300c54031020014000c81005001c21540040d90305540e04c010200c4003c0301840040b41e24103400101040c3c1d058850138100d20b46401507540030100000204c4c104803c3d0750361810715003060b14125511394607000140b182c0d041c0050400c40400084481000742c0340e07000809042c0c480003501b01000c5e206912118001d100c85a08422002d9074140f0250001d4034003404000e11480b00d44c05801c0c005002500401c84e01150042070351240540d0101409070b81c1c999600300000c804c240409040080c0c0055400070315120b050018001455031850400b03040184101e03032000f1103625404c840d10484450003031003015075011055219032a000e00f000341060342505810b0f501340084a0321005480d0903081c0007641181d03c0030490744400c1c461404039000303210035810054118a950b24 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 400162500 1250 400161250 400161269
    0xe0a0209151e031504050601050f07050c041109011704030e060403061e05090c19080105090303041511030a0905070302040c0c020a050a0602030306061b0627010911060a11010c0903050d0504 83
    0x11040802e05d841d622017500000305040c42c5c2d152900c240680d0701d040d00408015207480e08039100d600102d08150203150b44407030160b214186450705210001e4075001210500445010f1604001410117020300700f44403015000034030040e180c581e02e00c0c1000c0a00030100717210b01e501e4601280d84084200c0e5014031030040702e244011b06200d00d00c600c14040342031210300070114000209140010040001e10480d4000d0f8060000745a81e454182844078800501640d4580d00c0c07490b141c045000c3c2c2520406880e0484400200800e40450608245d450710349241c0020b9805442d1010342039030030f42c22070001d0315511300c280d035038580c6107a4550401518540074818800960800c01c0040d5103882c3c1580202088514013004040d0078a16404c250b24285040743e144840ca0903035200000c0041381c0e56444009202e00341c1c024400c402c82552164900340c0041e0889002e4980801d01c548414025640624502e4444008120b4072040c3c110080111031240300c190b940b400f6100b24a14241d10030821101503c0d001607 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 400163750 1250 400162500 400162531
    0x3081c05010b0412050312070314010b030c03070807052701110106080a081605120912030903070b0a0509030604060515030a0b0c0307110a0b0907080708070e0a0209151e03 75
    0x42d0a1304071210300b801103410380020840781e2400280c0400c0a13029440c107540c000748001c6603080d0307000d8007101a000500c0da10000d008000000495900300c80c0e0103d41c03890700c101a91280711040c1c0349070049111000c00c0340b01803802d54190085030f040700000040d09076100310f100c1000c2c00b8040e0032504c0b5809502290b41200008101040200c801403114468680e6420351a01d440d46a26081039101e1003180c4da04400091960540e1400e4061403040114000146151001c82c10002c0c1ea94125807180900f0000085071511175203014605884145002405490305072800c3d26180c001064201c4107490100603600c552001400d0020b0400c80c40c6030f100f40c42ea50551200c000c20810717904010004000c206d081c418175502c20800f8407a030b103242c600c2005a2445070802c40211414003040d60414659540405010002c423640050240304451103100d03101015201e880c16440039105003216642c1001e03241400c2070100040b5070080c00a1440c83e140340ca024454130354031b1074a6100640d2040d03002450301 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 400165000 1250 400163750 400163759
    0x61a010f081f08060708060f0105030106080609060301061805061c020a030308100b070b040b07020c0310020d06080a2001030b28031707020423070503180703081c05010b04 75
    0x1407000b0301c501d0609100c104402995241c603540380200c02c4882100040c285020320103079040c000039010300803000b420540c0c10741d8145000100030000c0244100e01c0b44170300c000440c2c0d050b01c080d03001d84090280300001c039011150125105028003401e44125008400784280c2090070074040c3d403600c039a11360050020200178516241103529400140c51205100501c0d500010241c14410003480501c0c49080d040f1043d103014140f140d0b1704000146505c040d50410982c12940e0f68001c1151400c00024190042e12000c40d85001d20041c00203400c41072040c81410350040601100d883c200d50040701c1e9140c3c16041d5641d4500440698802c0c04900303400800c803015010700321250740c600e181102212501e800d482030b40c0c0d0302c2d80c015041e445071180988110008211040d410039020706402c04088080c3c440c4011207640b51070110303c1c0000e21f6070b0100710011011400c40c41c1c500301194080d110b0b00d41207608154a034240798000f80e0004100d01101c3d8000c040e130080411072405110b04a4240051150605150 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 400166250 1250 400165000 400165021
    0x3050d050703030b0a0f050f09060a170307022107210f051c05040503070905090618070e01080102120a0902010c0803060303070209040f110d050604022704061a010f08 73
    0x288004400340760b102d081c03030780c600d07203034107031801e00030000684245d80c0c01d842d1100307000d10324002c8c500b080d0141c5048000c101041d25451441d03021640030441680000800c082914110b00806030001d40c04547c1c90050343c3d961091002011140864034203440c5003d540c0c6500000080c00700401c9a270040b2445050004241c1102040f882c2078018021390700e004a014624040d01d524502d140804100003080511203801c0820900c80549004079003000f40d401c09103001559000018190005000d28400e4403a101b4030500c0100c00800380c1c0310042d0081d586501469010f9041090380c0141401d248000075003001e5079005d4650f404c1e4041c3c5990f000c1c0d40640d19401e420f40e1000f003c0941500c000c101c0540180c82c1e40c4000b5200764010040c0001c0f2003603034074050680041c1842a00c3c840c205000b0080007185010541c1d54000f030341203540c4480010300710300b44e00c050400d140c500900c3d9082c031000c01041c01050340003010000420a0007502449102006480351144402c05100042c3e0300000103611020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 400167500 1250 400166250 400166257
    0xe010e071a070f1e082a01020c030f07050102040e0c030a0c0e18151e03010b0d08190c0618030915090e090307020a060233060108040204090804091a060403050d05 71
    0x728200c0030082c401c1c2d94907055245c2c1e02501a82e000f841035906d00c02d010781d00c00042d00303109085900c005d5103440040041207030303240124080010380400008082040260941c1201c0040a81e074114404074070300000c0c0200d998000729070b8031080c20b0174150209160fa00c01c2c02e082036450002048000403000c00b800150148400428004405000120504261362907150445010503461034100d00d504618050500307440c00b0341c0e84280078407022464000000c0f0494240c03185e0484003009513843d035126060454030100c101d08090702a40c506580c00d46000d00b1440348007103050003a110a844c80c0c0d90f5035482c00c540555062682d0000c3c0d01c690050101d007000c20000381c0c0008018040b242440581d40000d082004c50750300180250740018170304510740318011000c0e045012000d60b000000b05604141556900c1c005103140c0c104540d140003e0110340e01c1c0d81c840300f0807a03008010706840d41d49070420b50700100528030b240700c1010308141e907603034941ca0a0011501502c2e0710001404405d05e400b5002d842c10b40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 400168750 1250 400167500 400167533
    0xf0902030603150c0c1006050603010317070b0f0618010302011b0203011d0d09060507050a08070312060e090c03010b1e060403050102070b0711010209010e01120e010e071a070f 77
    0xb402010000c002030320703c01038011060100010303603400301111140e19104404645015041c1486810041e41d6545400d90f03044940220183c440000d040d81080c03a0f80c0b180c808004c00c10286001070241290320b8a4000b4841c20065032407111003004809a040303140d000344070083c0045c04070f603c016040d04503642031200d003501c05000828098400c0707030140ba101d503074500c4040b075581c00a0100500d02d548030000b0070040c011400d1032440c06025031516030300d85036801b10103001e0a03070000b030210416110b810301e40c10b058060013040003025102c3e90b80f00346020050756100d819211b188032045a03464103103c0c4950001008103041c0186612084240528090381c0c5a00e6000d02d0510000000ca0005e000401e003481c4940d4024005141c074610142c090311a8068154544c1e1041c072044880c2c1c3d070050190800b110090800031041540c4841c03000140042c4400c524140d401c00510144200300002d0100070b5402e1a6003000f50000d0180002125010f44003001d0038001c008806030010850201c83c425940 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 400170000 1250 400168750 400168753
    0x10519180803030f061011031912020c0f06071b0b0a0902130204030c12080a110313180f090b0103080906090406030b07020c0a151b14100b03070f0902030603 69
    0x765a44041d81c2181c0003102c1c184412070b000320030000f9a160403441840207800700d0034448480a80381418a540b40650304015608151003422020040d000345100860100f81c040150344d20300b080442c182d107501038a030030304e1104d110b5500452400c038002c20030301210070002400760403040c100b611154205c0001a0960300c0c915a100818000b40e121204040d0054517103000151b130b102d1840c584040031010359400118960b003100314200c0040e100d03200300c40b40c569040c030300300d4040e81580b56200d040d403003031303020170680060aa0710018050a0001c40040c0c0d06025000410441c0b1200240d0416548000c5004119880020050000441c42e501400f038040d0007400441c144000b000109003101c02641090b074000e825681002a451fa0400a0030032500c0309a8a180d06149090310103e081101e081004080c0894210741c5803c3d00d00c0000706d01d0b90b0a40191141d410102c030074102c0794440492591196000e82000b1030564141400103043c011541078901c404541450411200001d42005d80460740c103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 400171250 1250 400170000 400170047
    0x1b1c03271a040c080f01060b0d09300801091107080d0f050a05010e090109050d030b06161b060302251b060905130516050304050a0c06031505010519 65
    0x5002103801441c0c0b08910420301c5501d8281016421442c002640c000c8481c1030381840e0040c0125005001900d4a0300322000000c20750390301030300d84044a40d5100072004000e5039460070309440c10000d6420314592004940790014140d032244244820b4174180340c15072515150400c41c90001a61090081000000803100081c40924480a0805584051301c1d1841080c0c1c41e440184003a80314100040c2d040000342e4000c00841480b560b42d00d444d640c044a0b0703002072699071003000d003c80e1190320894103004890401050010801e143c1500120301303605500c4000510340034040781440c028800c03645a440b0380c2c6026258683c442c11040c00066103550215000d07880154005a044d941d07610000141100c3c1c0c80d4600100e0400b01401404020300004174207407404e080501440107100b4221b0700d1094842e25100e55a955103003071181c83c10b4410320008000c004494400624141d16034000340c840e159040344907500e01c1c0c0d504011103050080d90803c0000041181102d1780c51400ba4413060100484001d00c800c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 400172500 1250 400171250 400171283
    0x50c03040b0c0307030807020c090114010c0501020c0313290d020d1e050a02160b070203070b01030302070612060303020303160e2808030c03030c0a03021b1c0327 71
    0x40e4002e00081040c9900118403107040580018200b9800b441502c000c0201ca80e03400002444400103200c0c05140d44140280d42c0315a0b44100c04001e80c0039040303002556110b00d94880b081c0c0da644491a0060030300c16051001c1603400b070440d401c2944030344120719000303c20b2081c1e00c1d007440d41d40181d031510455582040f50712060051401426036a8240c2d00d0b0074141d100b0101d4100301580d80082021007002e10400000e060000070401000c81a9041084e1040f03996074414182e02d14415150b0142c181c9001200000405030300044401c1079030b030f03c1d035108080715910600c7c1c1001d5485c2804000e0250b001440021310300301e101240b0442083c21860801c40c00c404160205613002412054000038149060242d03105a590840c0f0800402c0314030015031034245041401c41c0c4030700014001c1e0840f5800001d881c0000c44c82a01541c9103101101c2c194030080342910b856a41d149004895018900c803050050f0100c980070344201202034000c2107600300040240245c0707481201c485941211a4000620680c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 400173750 1250 400172500 400172519
    0xf0e0a050d050105091513110d02060318010c0e0f04051f0906231005180301020301090204031103062a0408030409022a070302040522031d0f030d050c0304 68
    0x30078002c800008039810700daa16603040c90080703200d505814041100f4094003103418940210f6a0390070203404514507040c1340c00241d00b0358001d500070b036004101009000d80c440c08041c0407002e15030140f0082204c910300702c07401c0e01c80380c181c04000355100c6c005810f81007140c1499088294090f80c94000c21071092406100700b01c902e841500100c20655484500340b00b4008220b00b8401039000507024400e210404c900090008154040a90100b01d0081080d490b20212054600c290f520010029503d9684849505000b50400d11045d00d940610f00701d0180c0504000c0b80440c00b07001102000c4420b1131034035640d02c0a501c61044c030901035040c20800001d0b406028400f0f0400b42c02030071005680c480400070490018a0158070149107142c010b50543d484010001e5641c007140e0f8160381c0402c01c0e07501c0114003030403a0745014084101300c9038000c2180426071f200035150540d241c80c010510b04455544280403040e10320402d050b400d64071001031000110701441c094500d811075441242d00e40f40c1ca4a5148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 400175000 1250 400173750 400173769
    0xa030f09062003060a0b0c03041d04020f0f09180c030102070c0311012c01050f0a02010906050907050d0230030a080f160c0323180a05010f0e0a05 64
    0x59415955440310b400d14020000034200b01d82c000005501d055092080015100300802d104154214200050a18402c0f40c00e1080d240182071300e50b800c400c0003411130b0142e402003000300c8040f803044080c0c900d03280380d915101c40d41c1800d51101401d0a00c0329070301e050000c3c41c0c4c0300420010012600c102c40001e0b0041c0d82c03d0000f0030000d4820310440109900d1031400006500d10182d0075410312110103121000310004444070792891a2001064410780c4007940142c034584154030038088551000100c0c4c003103094054200d107508520440c400c0046070b035405c0710591a410035005a9a110005128010261801d00c46104000030a4050041809041039a0428505c92180f18207540c0e000490301c18050780d004181c899010f240604035494600c0c00d03803944050110134003800c0c0d00344400342c03408409042c4650b0000000d07450099620031281c0c0c40300152102600490184801103004c21031001d518107244214000729041a100e489001c1001c03074043c3c55080c104080250481000b00c0001003903520414813 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 400176250 1250 400175000 400175003
    0x60a1205010b040506060313061e020307050c101104060e120105091b040c0903030f12050702030c1e0604020904110405040b0a050702010507090510030e030309030a0207090b090c0a030f09 82
    0x5001c00c0440b0900c015658020010b5101d8042841008801200e4200004505a00c003400041d014a02e6800c256030302460201d079100a40b0100c1040400e58210004012007117542c0200c6030892103200c92071060b201e0b9500780c954500d400780800c111890041d0b0450074521030081032403880e581c01080d420300b110340c121001502e9074040407507000361004d1020348250940c0b0039a030034070580c203a40c1070180080300c2c00e01c802804c10000d021002c50b4a407086100d48009084180180b2081c1400040251349400c907010310300b03480c010b1661991600718942003c0c00c904080750050324a0303540d01d03001c100034a00005e000345c40e5941c62518101e8550f64a204151080c0d00c55600c11200341092441310b022640c000b05018107680c03428042c04460354101d8603d204403903048545403407a01032008201c000d00007221400149210120512844803004005051880d81c51b9084500255444e00754409645120460503013101e15800400d101d070034500300508201e40c02d8240403540c107000030fa8840071921038800 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 400177500 1250 400176250 400176253
    0xe151b19030c02130506060a0e0f0a0807060e0916140d1514030c0a0902030c0c0f210415030902152b06060e0609041104030305130e01030503070b060a1205 68
    0x82603411843e101882c46004d081951040065203404004130399144070303010000d018030032181400800ca94807100c1003804100050544140c1ca9038075a500f84c0d4503500b5020350702c04a040c0340b4030841d060070311740701892042011101621241c3d412680940d450310701c0341101101d40c0c0041040804034071403806980007512008501c504280d203001209010600d2408000744280c00c18005c480d1103580720602c1c1001c0d901807060060396521490502c140f180f14071420507130300b806840042c810642c0c0100c1c0d440c5182e01d03951482200c6c5601210385548520403800791500c540c8151290500140c860350044c0d1610348003901c030804410400320201042e1b080141c18100b844902031060808103078200100c02078005040042c000c1d82d0501d50060b0005450ba054140542400300d900185c0f075459130010b140180494100540c0c2e00c0e02d90800030b00f035038070100c158501400050000200e42d650900054105c17a00a4090760400e442035462902d400303005800c1d036a01881c0c8280c041610240c648035000d01030310450 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 400178750 1250 400177500 400177517
    0x40608060108010b0909241306170102040609150c0c12020a080f0a06020f120408130806041104020703120507091806062007180203070e151b1903 64
    0x6000400c00c200c16046013042e084240400c0e42c4640320f20b5000c0d500b140b211100440c1d8091003002d041c04540b01e00c0421070340000f4881d0b40311004041540510b00307581c040b1091255505014005034241d11840c0305000004013900001c00004003029400f00240c1281d03c1c24413045a05612a403500980da034110a040c06e00e840c1c07a010452900481800041820b40c024002200700740d41040c1e226125480080c00701a00007414002c07103045a412074241c05410020032006042034100980f40f9044644180e80500000303d0114107032900080a51045074040c080018842902040c40042e4000010450500c0490860281c00101d40d0051900c02c0701c856454145e210f15156a1010360b420003400b0700a518a4058180040c42e8409503403402c24680c41462024180e10200003490440a40d020400304500f4a0640854060540041d4094529031703640d41c079080310240820440508a060a0645030710800001c7d210b0350760f80000c90320045401040c0c4000422400d180d01c1f0400e892101240080c0194 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400179856 1106 400178750 400178761
    0x30e060a15050301050a0b150711010c0510050408031b0c0c061b030d0212180a031b150204080d05041401030b040b042c0a0b0624040608 60
    0x24008105900d44072030404020440c107014540704071855223200e65420703001c0003910703d01500012015241038484005680d00214804111a83d00412030400401d00b4644541482a801031103070a51f82d180901e4038403000c0a982858440300c01050000c1105004002500002d55000b0b0760110f5541300081c1041020320398218491000b4840002c1481c84007415030003905c84003078214003021590b280c10341081907110482c00d00202a60240180c0030119204501c968055101c10308100c000325180d840b11404955500001044280c002604104c0908100302e4651401c4e10342c034181d410141000508110b0841004d107250406480f02d00000b0180e6440d8061035600d00020410003a41550301c00030b41040340624004003480303811454a61b045d10003c07030516086030344004035000c6940c2e00e00c20800c1c46001505036a100340c00d48180803182500400041000d04190344644030b141c58407 = true := by decide +kernel

theorem cover : BRFrame.Cov 400000000 400179856 := by
  have h0 := BRFrame.cov_init 400000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400000000 ≤ n) (h2 : n < 400179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
